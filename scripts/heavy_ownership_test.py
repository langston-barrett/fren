#!/usr/bin/env python3
"""Differential checks of decoded ownership and registry decisions.
Run after building Heavy.Ownership: python3 -I scripts/heavy_ownership_test.py.
The active Python scheduler is the oracle; no real processes are signalled.
"""

from fractions import Fraction
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


def reference_arithmetic(a, b, *, add=False):
    """Independent round-to-binary64 oracle using Fraction's rounding.
    Python converts mixed operands to binary64 before doing arithmetic;
    int/int operations instead stay exact. Nonfinite results are classified
    explicitly. Signed zero does not affect any decision in this port.
    """
    if type(a) is int and type(b) is int:
        return a + b if add else a - b
    a = float(Fraction(a)) if type(a) is int else a
    b = float(Fraction(b)) if type(b) is int else b
    if math.isnan(a) or math.isnan(b):
        return math.nan
    if not math.isfinite(a) or not math.isfinite(b):
        if not add:
            b = -b
        if math.isinf(a) and math.isinf(b) and (a > 0) != (b > 0):
            return math.nan
        return a if math.isinf(a) else b
    exact = Fraction.from_float(a)
    exact = exact + Fraction.from_float(b) if add else exact - Fraction.from_float(b)
    try:
        return float(exact)
    except OverflowError:
        return math.inf if exact > 0 else -math.inf


def arithmetic(a, b, *, add=False):
    """The actual adapter operation, checked independently at each use."""
    value = a + b if add else a - b
    reference = reference_arithmetic(a, b, add=add)
    assert value == reference or (math.isnan(value) and math.isnan(reference)), (a, b, value, reference)
    return value


def numeric_span(value, ttl=heavy.REPORT_STALE_SECONDS):
    """Transport the arithmetic RESULT exactly, never a freshness decision.
    The common positive scale preserves comparisons with the finite TTL.
    Fraction independently decodes every emitted finite span and TTL.
    """
    finite = type(value) is int or math.isfinite(value)
    scale = max(ttl.as_integer_ratio()[1], value.as_integer_ratio()[1] if finite else 1)
    a, b = ttl.as_integer_ratio()
    ttl_ticks = a * (scale // b)
    assert Fraction(ttl_ticks, scale) == Fraction(ttl)
    if finite:
        a, b = value.as_integer_ratio()
        span = dict(kind="finite", ticks=a * (scale // b))
        assert Fraction(span["ticks"], scale) == Fraction(value)
    else:
        span = dict(kind="notANumber" if math.isnan(value) else
                    "positiveInfinity" if value > 0 else "negativeInfinity")
    return span, ttl_ticks


def transport(case):
    r = decoded_report(case["report"])
    # The status adapter extracts only the terminal protocol token. Diagnostic
    # numeric PIDs never enter the Lean observations.
    token = re.search(r"\[heavy-job=([0-9a-f]{32})\]\s*$", case["status"])
    elapsed = arithmetic(case["now"], r.pop("updated_monotonic")) if r else 0
    span, ttl = numeric_span(elapsed)
    return dict(kind="lease", report=r, status_job=token[1] if token else "",
                observed=case["observed"], legacy_rss=case["legacy_rss"],
                locked=case["locked"], cap=case["cap"], span=span, ttl=ttl)


def conversion_case(value):
    span, ttl = numeric_span(value)
    finite = span["kind"] == "finite"
    ticks = span.get("ticks")
    updated = -ticks if finite else 1
    deadline = ticks if finite else (-1 if span["kind"] == "negativeInfinity" else 1)
    # These numeric-span properties are independent of the Lean decoder and
    # the full Python lease oracle. Comparisons use the unscaled result too.
    expected = [updated, deadline, 0 <= value <= heavy.REPORT_STALE_SECONDS, value <= 0]
    return dict(kind="conversion", span=span, ttl=ttl), expected


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


def python_registry(available, now, started, requested, state):
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
                           side_effect=[started, now]), \
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


def python_group(subreaper, leader, wait, probe):
    # Drive the real reap_child and group_gone, mocking only OS observations.
    child = mock.Mock(pid=123, returncode=0 if leader else None,
                      heavy_subreaper=subreaper)
    observation = ChildProcessError() if wait == "exhausted" else (0, 0, None)
    outcome = {"missing": ProcessLookupError(), "present": None,
               "denied": PermissionError()}[probe]
    with mock.patch.object(heavy.os, "getpid", return_value=42), \
         mock.patch.object(heavy.os, "wait4", side_effect=observation if isinstance(observation, Exception)
                           else None, return_value=observation), \
         mock.patch.object(heavy.os, "killpg", side_effect=outcome) as kill:
        result = heavy.group_gone(123, lambda: heavy.reap_child(child, {}), subreaper)
        # Collection failure must prevent even the group probe.
        if not leader or (subreaper and wait == "pending"):
            kill.assert_not_called()
        else:
            kill.assert_called_once_with(123, 0)
        return result


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
    # Adjacent representable timestamps around freshness and future boundaries,
    # cancellation ties, mixed int/float conversion and overflowed differences.
    for now in (0.0, 8.0, 16.0, 100.0, 2.0 ** 53, -16.0, 1e-308):
        for center in (now, now - heavy.REPORT_STALE_SECONDS):
            below, above = math.nextafter(center, -math.inf), math.nextafter(center, math.inf)
            for stamp in (math.nextafter(below, -math.inf), below, center,
                          above, math.nextafter(above, math.inf)):
                for observed in (None, m, dict(m, namespace="pid:[200]")):
                    cases.append(dict(base, now=now, observed=observed,
                                      report=dict(base["report"], updated_monotonic=stamp)))
    for now, stamp in ((2 ** 53 + 9, float(2 ** 53 - 2)),
                       (2 ** 53 + 9, 2 ** 53 - 2), (1e308, -1e308), (-1e308, 1e308),
                       (math.nan, 0.0), (math.inf, 0.0), (-math.inf, 0.0)):
        for observed in (None, m):
            cases.append(dict(base, now=now, observed=observed,
                              report=dict(base["report"], updated_monotonic=stamp)))
    inputs, expected = [], []
    group_count = 0
    for subreaper, leader, wait, probe in itertools.product(
            (False, True), (False, True), ("pending", "exhausted"),
            ("missing", "present", "denied")):
        inputs.append(dict(kind="group", subreaper=subreaper, leader=leader,
                           wait=wait, probe=probe))
        expected.append(python_group(subreaper, leader, wait, probe))
        group_count += 1
    # PID 1 can discover a newly adopted group child after the first reap.
    # A failed second reap must stop before the probe even if it would be missing.
    with mock.patch.object(heavy.os, "getpid", return_value=1), \
         mock.patch.object(heavy.os, "waitid", return_value=mock.Mock(si_pid=124)), \
         mock.patch.object(heavy.os, "getpgid", return_value=123), \
         mock.patch.object(heavy.os, "killpg") as kill:
        assert not heavy.group_gone(123, mock.Mock(side_effect=[True, False]), True)
        kill.assert_not_called()
    # Rows are the actual selector's inputs, after jobs has verified a report.
    # Stale verified owners retain their measurements; freshness and PID are
    # deliberately absent from this selector's input.
    victim_cases = [json.loads(line) for line in
                    (ROOT / "test/heavy/victim.jsonl").read_text().splitlines()]
    for case in victim_cases:
        rows, cap = case["rows"], case["cap"]
        result = heavy.memory_victim(rows, cap)
        assert list(result) == case["expected"], case
        inputs.append(dict(kind="victim", rows=rows, cap=cap))
        expected.append(list(result))
    # Exercise all optional/invalid field combinations and both permutations.
    generated_start = len(inputs)
    for job, order, rss, legacy in itertools.product(
            (None, "a"), (None, -1, 0, 1, 2 ** 100),
            (None, -1, 0, 1, 2 ** 100), (None, -1, 0, 1, 2 ** 100)):
        row = dict(job_id=job, order=order, rss_kb=rss, legacy_rss_kb=legacy)
        other = dict(job_id="b", order=1, rss_kb=1, legacy_rss_kb=None)
        for rows in ([row, other], [other, row]):
            for cap in (0, 1, 2 ** 100):
                inputs.append(dict(kind="victim", rows=rows, cap=cap))
                expected.append(list(heavy.memory_victim(rows, cap)))
    generated_count = len(inputs) - generated_start
    registry_count = 0
    with tempfile.TemporaryDirectory() as state:
        path = Path(state) / "report.json"
        for case in cases:
            expected.append(python_lease(case, path))
            if case["name"] in ("rounded_ttl_unobserved", "rounded_ttl_verified"):
                assert expected[-1] == [True, True, 40, 40], (case, expected[-1])
            inputs.append(transport(case))
        # Nonfinite timestamps and malformed JSON are rejected by the wire decoder.
        for text in ('{"updated_monotonic": NaN}', '{"partial":', 'null'):
            path.write_text(text)
            assert heavy.read_report(path) is None
        # Deadline allocation is rounded once, then each remaining duration is
        # rounded separately. Do not reconstruct the start by subtracting wait.
        clocks = [(99.8, now) for now in (99, 100, 101)]
        for started in (0.0, 1.0, 16.0, 2.0 ** 53, -16.0, 1e308, -1e308):
            deadline = arithmetic(started, heavy.REGISTRY_WAIT_SECONDS, add=True)
            clocks.extend((started, now) for now in
                          (math.nextafter(deadline, -math.inf), deadline,
                           math.nextafter(deadline, math.inf)))
        clocks.extend((start, now) for start, now in
                      ((math.inf, math.inf), (-math.inf, 0.0), (0.0, -math.inf),
                       (0.0, math.nan), (math.nan, 0.0), (1e308, -1e308), (-1e308, 1e308)))
        for (started, now), available, requested in itertools.product(clocks, (False, True), (False, True)):
            deadline = arithmetic(started, heavy.REGISTRY_WAIT_SECONDS, add=True)
            remaining = arithmetic(deadline, now)
            span, _ = numeric_span(remaining)
            inputs.append(dict(kind="registry", available=available, span=span,
                               held=available, requested=requested))
            expected.append(python_registry(available, now, started, requested, state))
            registry_count += 1
    # Exercise the actual Std normalizers independently of report decoding.
    values = [-math.inf, math.inf, math.nan, -1, 0, 1, 10, 11]
    for center in (0.0, 10.0, -10.0):
        values.extend((math.nextafter(center, -math.inf), center, math.nextafter(center, math.inf)))
    for now, stamp in ((16.0, 5.999999999999999), (2 ** 53 + 9, float(2 ** 53 - 2)),
                       (2 ** 53 + 9, 2 ** 53 - 2), (1e308, -1e308), (-1e308, 1e308)):
        values.append(arithmetic(now, stamp))
    for value in values:
        inp, want = conversion_case(value)
        inputs.append(inp)
        expected.append(want)
    run = subprocess.run(["lake", "env", "lean", "--run", "scripts/heavy_ownership_test.lean"],
                         cwd=ROOT, input="".join(json.dumps(j) + "\n" for j in inputs),
                         text=True, capture_output=True, timeout=120)
    assert run.returncode == 0, run.stdout + run.stderr
    actual = [json.loads(line) for line in run.stdout.splitlines()]
    assert len(actual) == len(expected), (len(actual), len(expected))
    for i, (got, want) in enumerate(zip(actual, expected)):
        assert got == want, (i, got, want, inputs[i])
    print(f"{len(cases)} Lean/Python ownership cases and {registry_count} registry attempts agree "
          f"({len(fixed)} sanitized fixtures); {len(values)} numeric conversion cases agree")
    print(f"{group_count} group completion comparisons agree")
    print(f"{len(victim_cases)} victim fixtures and {generated_count} generated comparisons agree")


if __name__ == "__main__":
    main()
