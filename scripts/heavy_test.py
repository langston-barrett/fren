#!/usr/bin/env python3
"""Tests of `scripts/heavy`: parsing, settings, admission and telemetry.
They use scratch state directories, injected load and tiny Python jobs.

    python3 -I scripts/heavy_test.py
"""

import contextlib
import importlib.machinery
import importlib.util
import io
import json
import os
import signal
import subprocess
import sys
import tempfile
from unittest import mock

# Loading `heavy` must leave no `__pycache__` in the checkout.
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.realpath(__file__))


def load_heavy():
    path = os.path.join(HERE, "heavy")
    loader = importlib.machinery.SourceFileLoader("heavy", path)
    spec = importlib.util.spec_from_loader("heavy", loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


heavy = load_heavy()
GB = 1024 * 1024  # KB


def raises(f, kind):
    try:
        f()
    except kind:
        return True
    return False


def test_parse_args():
    p = heavy.parse_args
    assert p(["lake", "build", "--wfail"]) == (False, ["lake", "build", "--wfail"])
    assert p(["--offline", "fuzz", "--offline"]) == (True, ["fuzz", "--offline"])
    assert p(["--", "--offline"]) == (False, ["--offline"])
    assert p(["--offline", "--", "-x"]) == (True, ["-x"])
    for bad in ([], ["--offline"], ["--"], ["--bogus", "ls"], ["-h"]):
        assert raises(lambda: p(bad), heavy.UsageError), bad


def test_missing_command():
    with tempfile.TemporaryDirectory() as state:
        # The only slot is held, and a load gate would also prevent admission.
        # A missing bare executable must fail before checking either limit.
        with open(os.path.join(state, "slot0"), "w+") as held:
            held.write("occupied\n")
            held.flush()
            heavy.fcntl.flock(held, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr), \
                 mock.patch.object(heavy, "heavy_rss_kb", side_effect=AssertionError("admission checked")), \
                 mock.patch.object(heavy.time, "sleep", side_effect=AssertionError("waited")):
                code = heavy.main(["heavy-test-no-such-executable-768"], state,
                                  {"HEAVY_SLOTS": "1", "HEAVY_MAX_LOAD": "0.01"},
                                  lambda: 100)
            assert code == 127 and "command not found" in stderr.getvalue()
            held.seek(0)
            assert held.read() == "occupied\n"
        assert not os.path.exists(os.path.join(state, "log.jsonl"))


def test_recheck_wait_message():
    class Waiting(Exception):
        pass

    with tempfile.TemporaryDirectory() as state:
        loads = iter([0, 9])  # Initially admitted; load rises before the locked recheck.
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), \
             mock.patch.object(heavy, "heavy_rss_kb", return_value=0), \
             mock.patch.object(heavy.time, "sleep", side_effect=Waiting):
            assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                          {"HEAVY_SLOTS": "1", "HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "8"},
                          lambda: next(loads)), Waiting)
        assert "waiting for memory or load" in stderr.getvalue()
        assert "slots busy" not in stderr.getvalue()
        assert not os.path.exists(os.path.join(state, "log.jsonl"))
        with open(os.path.join(state, "slot0")) as slot:
            heavy.fcntl.flock(slot, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)


def test_physical_memory():
    meminfo = "MemFree:  1000 kB\nMemTotal:       32864960 kB\nSwapTotal: 0 kB\n"
    assert heavy.meminfo_kb(meminfo) == 32864960
    assert raises(lambda: heavy.meminfo_kb("MemFree: 1 kB\n"), ValueError)
    assert heavy.memsize_kb("17179869184\n") == 16 * GB
    with tempfile.NamedTemporaryFile("w", suffix="meminfo") as f:
        f.write(meminfo)
        f.flush()
        assert heavy.physical_memory_kb("Linux", f.name) == 32864960
    assert raises(lambda: heavy.physical_memory_kb("Plan9"), ValueError)


def test_overrides():
    physical = lambda: 20 * GB
    with tempfile.TemporaryDirectory() as state:
        warnings = []
        cap = lambda env: heavy.mem_cap_kb(env, state, physical, warnings.append)
        slots = lambda env: heavy.slot_count(env, state, warnings.append)

        # The defaults: 80% of physical memory, and 2 slots.
        assert cap({}) == 16 * GB
        assert slots({}) == 2

        # A file overrides the default, and is re-read on every call.
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("6\n")
        with open(os.path.join(state, "slots"), "w") as f:
            f.write("3\n")
        assert cap({}) == 6 * GB
        assert slots({}) == 3
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("2.5")
        assert cap({}) == int(2.5 * GB)

        # The environment variable overrides the file.
        assert cap({"HEAVY_MEM_GB": "4"}) == 4 * GB
        assert slots({"HEAVY_SLOTS": "1"}) == 1

        # An empty or invalid setting falls through to the next.
        assert cap({"HEAVY_MEM_GB": ""}) == int(2.5 * GB)
        assert cap({"HEAVY_MEM_GB": "lots"}) == int(2.5 * GB)
        assert cap({"HEAVY_MEM_GB": "-1"}) == int(2.5 * GB)
        assert slots({"HEAVY_SLOTS": "0"}) == 3  # 0 slots would never start a job
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("")
        assert cap({}) == 16 * GB
        assert cap({"HEAVY_MEM_GB": "nan"}) == 16 * GB
        assert cap({"HEAVY_MEM_GB": "inf"}) == 16 * GB
        assert cap({"HEAVY_MEM_GB": "1e400"}) == 16 * GB
        os.remove(os.path.join(state, "slots"))
        assert slots({"HEAVY_SLOTS": "x"}) == 2
        assert slots({"HEAVY_SLOTS": "0"}) == 2

        # A setting that is set but rejected is reported, once for each value.
        del warnings[:]
        cap({"HEAVY_MEM_GB": "-7"})
        cap({"HEAVY_MEM_GB": "-7"})
        assert len(warnings) == 1 and "HEAVY_MEM_GB='-7'" in warnings[0], warnings
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("14GB\n")
        assert cap({}) == 16 * GB
        assert len(warnings) == 2 and "'14GB'" in warnings[1], warnings
        # An empty file, like an unset variable, is not reported.
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("\n")
        assert cap({}) == 16 * GB and len(warnings) == 2, warnings

        # The default reads the physical memory only when nothing overrides it.
        ignore = lambda m: None

        def unreadable():
            raise AssertionError("read the physical memory")
        assert heavy.mem_cap_kb({"HEAVY_MEM_GB": "1"}, state, unreadable,
                                ignore) == GB


def test_offline_command():
    ok = lambda c: True
    no = lambda c: False
    seen = []
    assert heavy.offline_command(["fuzz", "-n", "3"], "Linux", lambda c: seen.append(c) or True) \
        == ["unshare", "-rn", "--", "fuzz", "-n", "3"]
    assert seen == [["unshare", "-rn", "--", "true"]]
    mac = heavy.offline_command(["fuzz"], "Darwin", ok)
    assert mac == ["sandbox-exec", "-p", heavy.MACOS_OFFLINE_PROFILE, "fuzz"]
    assert "(deny network*)" in heavy.MACOS_OFFLINE_PROFILE
    assert "mDNSResponder" in heavy.MACOS_OFFLINE_PROFILE
    # Where it cannot cut the network, it refuses rather than run online.
    for system in ("Linux", "Darwin"):
        assert raises(lambda: heavy.offline_command(["fuzz"], system, no), RuntimeError)
    assert raises(lambda: heavy.offline_command(["fuzz"], "Plan9", ok), RuntimeError)


def test_load_admission():
    with tempfile.TemporaryDirectory() as state:
        warnings = []
        limit = lambda env: heavy.max_load(env, state, warnings.append)
        assert limit({}) is None  # Off by default, including on this machine.
        path = os.path.join(state, "max_load")
        with open(path, "w") as f:
            f.write("8")
        assert limit({}) == 8
        assert limit({"HEAVY_MAX_LOAD": "6.5"}) == 6.5
        assert limit({"HEAVY_MAX_LOAD": "off"}) is None
        for value in ("", "nan", "inf", "0", "-2", "bad"):
            assert limit({"HEAVY_MAX_LOAD": value}) == 8
        with open(path, "w") as f:
            f.write("9")
        assert limit({}) == 9  # Re-read while waiting.

    def unreadable():
        raise AssertionError("read load with the policy off, or after its grace period")

    admit = heavy.can_start
    assert admit(0, 60, 100, None, unreadable)
    assert admit(0, 60, 100, 8, lambda: 7.99)
    assert not admit(0, 60, 100, 8, lambda: 8)
    assert not admit(599.99, 0, 100, 8, lambda: 65)
    assert admit(600, 0, 100, 8, unreadable)
    assert not admit(6000, 61, 100, 8, unreadable)  # Never waive memory.
    assert admit(0, 0, 100, 8, lambda: None)  # Missing OS load fails open.


def tiny_job(state, command, overrides=None):
    # Invoke main in a fresh process, with no real load or shared state.
    code = ("import runpy,sys; h=runpy.run_path(sys.argv[1]); "
            "sys.exit(h['main'](sys.argv[3:], state=sys.argv[2], load_reader=lambda: 0.5))")
    environ = dict(os.environ, HEAVY_SLOTS="1", HEAVY_MEM_GB="1", HEAVY_MAX_LOAD="off")
    environ.pop("HEAVY_LOG", None)
    environ.update(overrides or {})
    return subprocess.run([sys.executable, "-I", "-B", "-c", code,
                           os.path.join(HERE, "heavy"), state] + command,
                          env=environ, capture_output=True, text=True, timeout=30)


def test_job_log():
    readings = iter([3, None, 9])
    record = {"load_samples": []}
    read = lambda: next(readings)
    last = heavy.sample_load(record, read, 0)
    assert heavy.sample_load(record, read, 29.99, last) == 0
    last = heavy.sample_load(record, read, 30, last)
    assert heavy.sample_load(record, read, 59.99, last) == 30
    heavy.sample_load(record, read, 60, last)
    assert record["load_samples"] == [3, 9]
    with tempfile.TemporaryDirectory() as state:
        command = [sys.executable, "-c", "raise SystemExit(7)",
                   os.path.join(state, "x" * 300), "--seed", "42", "last-kind"]
        result = tiny_job(state, command)
        assert result.returncode == 7, result.stderr
        with open(os.path.join(state, "log.jsonl")) as f:
            rows = [json.loads(line) for line in f]
        assert len(rows) == 1
        row = rows[0]
        assert row["exit_status"] == 7
        assert row["enqueued_at"] <= row["started_at"] <= row["ended_at"]
        assert row["wait_seconds"] >= 0 and row["run_seconds"] > 0
        assert row["peak_rss_kb"] > 0  # Even a job shorter than a sampling tick.
        assert row["load_samples"] == [0.5]
        assert row["load_mean"] == row["load_max"] == 0.5
        assert row["max_load"] == "off" and row["slots"] == 1
        assert row["job_kind"] == heavy.job_kind(command) and "last-kind" in row["job_kind"]
        assert len(row["command"]) == 240 and row["command"].endswith("...")
        assert row["worktree"] == os.getcwd()
        assert "SystemExit(7)" in row["command"]
        # A failed append cannot turn a successful or failed command into another status.
        for status in (0, 9):
            result = tiny_job(state, [sys.executable, "-c", f"raise SystemExit({status})"],
                              {"HEAVY_LOG": state})  # Opening a directory fails.
            assert result.returncode == status, result.stderr
        result = tiny_job(state, [os.path.join(state, "does-not-exist")])
        assert result.returncode == 127, result.stderr
        result = tiny_job(state, [sys.executable, "-c",
                                 "import os,signal; os.kill(os.getpid(),signal.SIGTERM)"])
        assert result.returncode == 143, result.stderr
        # Memory eviction still returns 137 and logs the peak and that status.
        result = tiny_job(state, [sys.executable, "-c", "import time; time.sleep(10)"],
                          {"HEAVY_MEM_GB": "0.000001"})
        assert result.returncode == 137, result.stderr
        with open(os.path.join(state, "log.jsonl")) as f:
            rows = [json.loads(line) for line in f]
        assert [r["exit_status"] for r in rows] == [7, 127, 143, 137]
        assert rows[-1]["peak_rss_kb"] > 0
        result = tiny_job(state, ["--stats", "1"])
        assert result.returncode == 0, result.stderr
        assert json.loads(result.stdout)["jobs"] == 4
        for args in (["--stats", "0"], ["--stats", "nan"], ["--stats", "1", "2"]):
            assert tiny_job(state, args).returncode == 2
        for args in (["--alternate"], ["--alternate", "0", "8"],
                     ["--alternate", "60", "nan"], ["--alternate", "60", "8", "x"]):
            assert tiny_job(state, args).returncode == 2


def test_admission_snapshot():
    with tempfile.TemporaryDirectory() as state:
        path = os.path.join(state, "max_load")
        with open(path, "w") as f:
            f.write("8")

        def load():
            # Simulate a flip between the initial check and the slot lock.
            with open(path, "w") as f:
                f.write("6")
            return 0.5

        previous = {s: signal.getsignal(s) for s in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
        try:
            assert heavy.main([sys.executable, "-c", "pass"], state,
                              {"HEAVY_SLOTS": "1", "HEAVY_MEM_GB": "1"}, load) == 0
        finally:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
        with open(os.path.join(state, "log.jsonl")) as f:
            row = json.loads(f.read())
        assert row["max_load"] == 6 and row["slots"] == 1


def test_job_kinds():
    kind = heavy.job_kind
    assert kind(["/tmp/pr1/fren_fuzz_frontends", "--seed", "123", "--count", "10",
                 "--out", "/tmp/out1"]) == kind(
        ["/tmp/pr2/fren_fuzz_frontends", "--seed=0xABC", "--count=3000", "--out=/tmp/out2"])
    assert kind(["lake", "env", ".lake/build/bin/fren_test", "--job", "ui", "a.fren"]) == kind(
        ["/usr/bin/lake", "env", "/tmp/ci7/fren_test", "--job", "ui", "test/ui/b.fren"])
    assert kind(["fren_test", "--job", "ui"]) != kind(["fren_test", "--job", "printing"])
    assert kind(["lake", "build", "Reqs.Testing"]) != kind(["lake", "build", "Reqs.Lint"])
    assert kind(["fren_test", "--job", "mutation", "0", "3", "8"]) == kind(
        ["fren_test", "--job", "mutation", "1", "7", "16"])
    assert kind(["python3", "-B", "scripts/fuzz.py", "--count", "1"]) == kind(
        ["/usr/bin/python3", "-B", "/tmp/tree8/scripts/fuzz.py", "--count", "3000"])
    assert kind(["python3", "scripts/a.py"]) != kind(["python3", "scripts/b.py"])


def test_stats_and_appends():
    with tempfile.TemporaryDirectory() as state:
        assert heavy.stats(1, state, {}, now=10000)["jobs"] == 0
        record = {"started_at": 9900, "ended_at": 10000, "wait_seconds": 10, "run_seconds": 20,
                  "load_samples": [6, 8], "max_load": "off", "slots": 2,
                  "job_kind": "lake test", "exit_status": 0}
        heavy.append_log(record, state, {})
        heavy.append_log(dict(record, started_at=6390, ended_at=6400,
                              wait_seconds=0, run_seconds=10), state, {})
        heavy.append_log(dict(record, started_at=6389, ended_at=6399), state, {})  # Outside the window.
        heavy.append_log(dict(record, ended_at=10001), state, {})
        for bad in ({"slots": True}, {"max_load": True}, {"load_samples": [False]},
                    {"exit_status": "0"}, {"run_seconds": float("inf")}, {"started_at": None}):
            # Bypass append_log's finite-number validation to test a damaged log.
            with open(os.path.join(state, "log.jsonl"), "a") as f:
                f.write(json.dumps(dict(record, **bad)) + "\n")
        with open(os.path.join(state, "log.jsonl"), "a") as f:
            f.write('null\n[]\n{}\n{"wait_seconds": NaN}\n{"partial":')
        summary = heavy.stats(1, state, {}, now=10000)
        assert summary["jobs"] == 2 and summary["jobs_per_hour"] == 2
        assert summary["wait_seconds"]["p50"] == 5
        assert summary["run_seconds"]["p50"] == 15
        assert summary["latency_seconds"]["p50"] == 20
        assert summary["mean_load"] == 7
        assert summary["policies"][0]["jobs_per_hour"] is None  # No exposure log to guess from.
        assert heavy.percentiles([10])["p99"] == 10
        # Forced short writes from concurrent processes must not interleave records.
        path = os.path.join(state, "concurrent.jsonl")
        code = ("import os,runpy,sys; h=runpy.run_path(sys.argv[1]); "
                "write=os.write; os.write=lambda fd,data: write(fd,data[:7]); "
                "[h['append_log']({'writer':sys.argv[2]}, environ={'HEAVY_LOG':sys.argv[3]}) "
                "for _ in range(20)]")
        writers = [subprocess.Popen([sys.executable, "-I", "-B", "-c", code,
                                    os.path.join(HERE, "heavy"), str(i), path]) for i in range(4)]
        assert all(p.wait(timeout=10) == 0 for p in writers)
        with open(path) as f:
            rows = [json.loads(line) for line in f]
        assert len(rows) == 80
        assert all(sum(r["writer"] == str(i) for r in rows) == 20 for i in range(4))


def test_short_appends():
    with tempfile.TemporaryDirectory() as state:
        record = {"command": "lake test", "load_samples": [1.5, 2.5]}
        write = os.write

        def short_write(fd, data):
            return write(fd, data[:3])

        with mock.patch.object(heavy.os, "write", side_effect=short_write):
            heavy.append_log(record, state, {})
        path = os.path.join(state, "log.jsonl")
        with open(path) as f:
            assert [json.loads(line) for line in f] == [record]
        # A zero-byte write is a non-fatal logging failure, not an infinite retry.
        with mock.patch.object(heavy.os, "write", side_effect=[0, AssertionError("retried no progress")]):
            heavy.append_log({"ignored": True}, state, {})
        with open(path) as f:
            heavy.fcntl.flock(f, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
        heavy.append_log({"next": True}, state, {})
        with open(path) as f:
            assert [json.loads(line) for line in f] == [record, {"next": True}]


def test_policy_comparison():
    with tempfile.TemporaryDirectory() as state:
        # The first flip predates the window. Count its clipped interval,
        # including idle time, not the span from first to last job.
        for at, load in ((1000, 99), (6000, "off"), (9000, 8), (14400, "off"), (15000, 99)):
            heavy.append_log({"event": "policy", "at": at, "max_load": load, "slots": 2}, state, {})

        def job(load, kind, run, slots=2, status=0, ended=10000):
            heavy.append_log({"event": "job", "max_load": load, "slots": slots,
                              "job_kind": kind, "started_at": ended - 1,
                              "ended_at": ended, "exit_status": status,
                              "wait_seconds": 2, "run_seconds": run,
                              "load_samples": [8 if load == "off" else 4]}, state, {})

        # Work mix reverses: raw medians suggest a regression. One kind
        # runs four times faster and the other is unchanged, so their
        # equal-weight geometric ratio is 0.5 regardless of frequencies.
        for _ in range(9):
            job("off", "fast", 1, ended=8000)
            job(8, "slow", 100)
        job("off", "slow", 100, ended=8000)
        job(8, "fast", 0.25, ended=14400)  # Completion crosses the flip; admission still wins.
        job(8, "fast", 0.001, status=1)
        job(8, "only-on", 300)
        for _ in range(12):
            job("off", "fast", 1000000, slots=3)  # Never pool different slot counts.
        job("off", "fast", 1000, ended=7199)  # Outside the window.
        summary = heavy.stats(2, state, {}, now=14400)
        policies = {(p["max_load"], p["slots"]): p for p in summary["policies"]}
        off, on = policies[("off", 2)], policies[(8, 2)]
        assert off["observed_hours"] == 0.5 and on["observed_hours"] == 1.5
        assert off["jobs_per_hour"] == 20 and on["jobs_per_hour"] == 8
        assert off["rate_jobs"] == 10 and on["rate_jobs"] == 12
        assert off["mean_load"] == 8 and on["mean_load"] == 4
        assert off["run_seconds"]["p50"] == 1 and on["run_seconds"]["p50"] == 100
        assert on["matched_kinds"] == 2 and on["normalized_run_ratio_vs_off"] == 0.5
        assert off["matched_kinds"] == 0 and off["normalized_run_ratio_vs_off"] is None
        assert on["failed_jobs"] == 1
        assert policies[("off", 3)]["jobs_per_hour"] is None
        fast = {p["max_load"]: p for p in summary["by_kind"]["fast"] if p["slots"] == 2}
        assert fast[8]["run_ratio_vs_off"] == 0.25 and fast[8]["successful_jobs"] == 1
        assert summary["by_kind"]["only-on"][0]["run_ratio_vs_off"] is None
        assert (99, 2) not in policies


def test_partial_policy_coverage():
    with tempfile.TemporaryDirectory() as state:
        # The window begins at 7200, but the controller does not start until 10800.
        for at, load in ((10800, 8), (12600, "off")):
            heavy.append_log({"event": "policy", "at": at, "max_load": load, "slots": 2}, state, {})
        records = [
            ("off", 8000, 9000),    # Completion before the first flip.
            ("off", 10700, 11000),  # Admission before the first flip, completion after it.
            ("off", 7000, 7300),    # Admission outside the requested window.
            ("off", 11000, 11100),  # Admission under an override, not the logged policy.
            ("off", 12600, 12700),  # Exactly the boundary, included only in off.
            ("off", 13000, 13100),
            (8, 10800, 10900),      # Exactly the first flip, included in on.
            (8, 12599, 12700),      # Retains admission policy across a flip.
            (8, 12600, 12700),      # At the off boundary, excluded from on's rate.
        ]
        for load, began, ended in records:
            heavy.append_log({"event": "job", "max_load": load, "slots": 2,
                              "started_at": began, "ended_at": ended, "exit_status": 0,
                              "job_kind": "lake test", "wait_seconds": 0, "run_seconds": 10,
                              "load_samples": []}, state, {})
        summary = heavy.stats(2, state, {}, now=14400)
        policies = {p["max_load"]: p for p in summary["policies"]}
        assert summary["jobs"] == 9  # Raw counts and timing summaries retain every completion.
        assert policies["off"]["jobs"] == 6 and policies[8]["jobs"] == 3
        for policy in policies.values():
            assert policy["observed_hours"] == 0.5
            assert policy["rate_jobs"] == 2 and policy["jobs_per_hour"] == 4


def test_alternate():
    with tempfile.TemporaryDirectory() as state:
        clock = [1000]
        seen = []

        def sleep(seconds):
            assert seconds == 60
            seen.append(heavy.max_load({}, state))
            if len(seen) == 1:
                # A second controller must neither flip nor clean up the
                # first one's setting when it fails to acquire the lock.
                assert raises(lambda: heavy.alternate(1, 99, state, {}), RuntimeError)
                assert heavy.max_load({}, state) == 8
            clock[0] += seconds
            if len(seen) == 4:
                raise KeyboardInterrupt

        assert raises(lambda: heavy.alternate(1, 8, state, {}, sleep, lambda: clock[0]),
                      KeyboardInterrupt)
        assert seen == [8, None, 8, None]
        assert not os.path.exists(os.path.join(state, "max_load"))
        with open(os.path.join(state, "log.jsonl")) as f:
            flips = [json.loads(line) for line in f]
        assert [r["max_load"] for r in flips] == [8, "off", 8, "off", "off"]
        assert [r["at"] for r in flips] == [1000, 1060, 1120, 1180, 1240]
        assert all(r["event"] == "policy" and r["slots"] == 2 for r in flips)
        summary = heavy.stats(1, state, {}, now=1240)
        assert all(p["observed_hours"] == 120 / 3600 for p in summary["policies"])
        assert all(p["jobs_per_hour"] == 0 for p in summary["policies"])


def main():
    tests = [test_parse_args, test_missing_command, test_recheck_wait_message,
             test_physical_memory, test_overrides, test_offline_command,
             test_load_admission, test_job_log, test_admission_snapshot, test_job_kinds,
             test_stats_and_appends, test_short_appends, test_policy_comparison,
             test_partial_policy_coverage, test_alternate]
    for t in tests:
        t()
    print(f"heavy: {len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
