#!/usr/bin/env python3
"""Differential checks of decoded ownership and registry decisions.
Run after building Heavy.Ownership: python3 -I scripts/heavy_ownership_test.py.
The active Python scheduler is the oracle; no real processes are signalled.
"""

import itertools
import json
import math
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from heavy_test import heavy

ROOT = Path(__file__).resolve().parent.parent


def decoded_report(raw):
    """Wire decoding only, independent of heavy.read_report. Ownership and
    freshness stay undecided. This is the existing adapter boundary, not a
    claim that malformed wire records can be given directly to the kernel.
    """
    if not isinstance(raw, dict):
        return None
    r = dict(raw)
    stamp = r.get("updated_monotonic")
    try:
        valid_time = type(stamp) in (int, float) and math.isfinite(stamp)
    except OverflowError:
        valid_time = False
    m = r.get("monitor")
    if m is not None:
        if not isinstance(m, dict) or not (
                type(m.get("pid")) is int and m["pid"] > 0
                and type(m.get("start")) is int and m["start"] >= 0
                and isinstance(m.get("namespace"), str)):
            return None
    if not (r.get("version") == 3 and isinstance(r.get("job_id"), str)
            and re.fullmatch("[0-9a-f]{32}", r["job_id"])
            and type(r.get("order")) is int and type(r.get("rss_kb")) is int
            and valid_time):
        return None
    # Negative RSS and nonpositive order are representable: the kernel must
    # reject them itself, even though the production decoder rejects them too.
    # Kernel observations have exactly these three keys. Extra report fields
    # cannot match that whole dictionary; retain the report for the freshness
    # fallback, but decode its unrepresentable monitor identity as absent.
    if m is not None and set(m) != {"pid", "start", "namespace"}:
        m = None
    r["monitor"] = m
    return r


def transport(case):
    r = decoded_report(case["report"])
    # The status adapter extracts only the terminal protocol token. Diagnostic
    # numeric PIDs never enter the Lean observations.
    token = re.search(r"\[heavy-job=([0-9a-f]{32})\]\s*$", case["status"])
    now, ttl = case["now"], heavy.REPORT_STALE_SECONDS
    # Preserve exact binary time ratios at both freshness endpoints.
    times = [now, ttl] + ([r["updated_monotonic"]] if r else [])
    scale = max(t.as_integer_ratio()[1] for t in times)

    def ticks(t):
        a, b = t.as_integer_ratio()
        return a * (scale // b)

    if r:
        r["updated_monotonic"] = ticks(r["updated_monotonic"])
    return dict(kind="lease", report=r, status_job=token[1] if token else "",
                observed=case["observed"], legacy_rss=case["legacy_rss"],
                locked=case["locked"], cap=case["cap"], now=ticks(now), ttl=ticks(ttl))


def python_lease(case, path):
    path.write_text(json.dumps(case["report"]))
    r = heavy.read_report(path)
    token = heavy.slot_job_id(case["status"])
    compatible = r is not None and heavy.report_current(r, token, case["observed"], case["now"])
    if not case["locked"]:
        return [compatible, False, 0, 0]
    if compatible:
        row = dict(r, fresh=0 <= case["now"] - r["updated_monotonic"] <= heavy.REPORT_STALE_SECONDS,
                   legacy=False, legacy_rss_kb=None, slot="slot0")
    else:
        row = dict(job_id=None, order=None, rss_kb=None, fresh=False, legacy=True,
                   legacy_rss_kb=case["legacy_rss"], slot="slot0")
    # One isolated lease is enough to compare per-lease charges; summing these
    # would incorrectly repeat the shared forecast for unknown legacy holders.
    with mock.patch.object(heavy, "jobs", return_value=[row]):
        admission = heavy.heavy_rss_kb(cap=case["cap"])
    measured, _ = heavy.memory_victim([row], 10 ** 100)
    return [compatible, True, admission, measured]


class Retried(Exception):
    pass


def python_registry(available, now, deadline, requested, state):
    """Stop the real acquisition loop at its first retry, without sleeping.
    Check the decision and mask from Python itself, not a restated predicate.
    """
    mask = set()
    deferred = False

    def sigmask(how, value):
        nonlocal mask
        previous = mask.copy()
        mask = set(value) if how == signal.SIG_SETMASK else mask | set(value)
        return previous

    def sleep(_):
        raise Retried

    acquired = retry = timed_out = False
    with mock.patch.object(heavy.time, "monotonic",
                           side_effect=[deadline - heavy.REGISTRY_WAIT_SECONDS, now]), \
         mock.patch.object(heavy.time, "sleep", side_effect=sleep), \
         mock.patch.object(heavy.fcntl, "flock", side_effect=None if available else BlockingIOError), \
         mock.patch.object(heavy.signal, "pthread_sigmask", side_effect=sigmask):
        try:
            with heavy.registry(state):
                acquired = True
                deferred = requested and signal.SIGTERM in mask
        except Retried:
            retry = True
        except heavy.RegistryBusy:
            timed_out = True
    assert not mask, "registry did not restore signal mask"
    return [acquired, retry, timed_out, deferred]


def main():
    # Synthetic identities and times derived from the ownership regressions;
    # no production PID, job identity, namespace or path is recorded here.
    fixed = [json.loads(line) for line in (ROOT / "test/heavy/ownership.jsonl").read_text().splitlines()]
    cases = fixed.copy()
    # Cross product of lock state, observations, legacy readings, time and cap;
    # namespace disagreement must override freshness on every branch.
    base = fixed[0]
    m = base["observed"]
    for locked, observed, rss, now, cap in itertools.product(
            (False, True), (None, m, dict(m, namespace="pid:[200]"), dict(m, start=21)),
            (None, -1, 0, 33), (99, 100, 110, 111), (0, 1, 80, 81)):
        cases.append(dict(base, locked=locked, observed=observed, legacy_rss=rss, now=now, cap=cap))
    for now in (99.99999999999999, 100.00000000000001, 109.99999999999999, 110.00000000000001):
        cases.append(dict(base, now=now, observed=None))
    for stamp in (float("nan"), float("inf"), -float("inf"), 10 ** 1000):
        cases.append(dict(base, report=dict(base["report"], updated_monotonic=stamp)))
    for now in (100.125, 110.125, 110.12500000000001):
        cases.append(dict(base, now=now, observed=None,
                          report=dict(base["report"], updated_monotonic=100.125)))
    inputs, expected = [], []
    with tempfile.TemporaryDirectory() as state:
        path = Path(state) / "report.json"
        for case in cases:
            expected.append(python_lease(case, path))
            inputs.append(transport(case))
        # Non-finite and malformed JSON never reach the typed kernel.
        for text in ('{"updated_monotonic": NaN}', '{"partial":', 'null'):
            path.write_text(text)
            assert heavy.read_report(path) is None
        for available, now, requested in itertools.product((False, True), (99, 100, 101), (False, True)):
            inputs.append(dict(kind="registry", available=available, now=now, deadline=100,
                               held=available, requested=requested))
            expected.append(python_registry(available, now, 100, requested, state))
    run = subprocess.run(["lake", "env", "lean", "--run", "scripts/heavy_ownership_test.lean"],
                         cwd=ROOT, input="".join(json.dumps(j) + "\n" for j in inputs),
                         text=True, capture_output=True, timeout=120)
    assert run.returncode == 0, run.stdout + run.stderr
    actual = [json.loads(line) for line in run.stdout.splitlines()]
    assert len(actual) == len(expected), (len(actual), len(expected))
    for i, (got, want) in enumerate(zip(actual, expected)):
        assert got == want, (i, got, want, inputs[i])
    print(f"{len(cases)} Lean/Python ownership cases and 12 registry attempts agree "
          f"({len(fixed)} sanitized fixtures)")


if __name__ == "__main__":
    main()
