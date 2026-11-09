#!/usr/bin/env python3
"""Tests of `scripts/heavy`: parsing, settings, admission and telemetry.
They use scratch state directories, injected load and tiny Python jobs.

    python3 -I scripts/heavy_test.py
"""

import contextlib
import ctypes
import importlib.machinery
import importlib.util
import io
import json
import math
import os
import signal
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
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

    # A slot-count change during acquisition is a retry, not slot exhaustion.
    with tempfile.TemporaryDirectory() as state, open(os.path.join(state, "slot0"), "a+") as held:
        heavy.fcntl.flock(held, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), \
             mock.patch.object(heavy, "slot_count", side_effect=[2, 2, 1]), \
             mock.patch.object(heavy, "heavy_rss_kb", return_value=0), \
             mock.patch.object(heavy.time, "sleep", side_effect=Waiting), \
             mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
            assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                {"HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "off"}), Waiting)
        assert stderr.getvalue() == f"heavy: slot count changed, retrying (see {state})\n"


def test_reservation_wait_message():
    # fren-covers: testing::heavy_wait_message
    class Waiting(Exception):
        pass

    environ = {"HEAVY_SLOTS": "2", "HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "off"}
    for recheck in (False, True):
        cases = [([{"slot": "slot1", "rss_kb": 1, "fresh": False}], "stale or future-dated report"),
                 ([{"slot": "slot1", "rss_kb": None, "fresh": False,
                    "legacy": True, "legacy_rss_kb": 2 * GB}], f"legacy RSS: {2 * GB} KB"),
                 ([{"slot": "slot1", "rss_kb": None, "fresh": False, "legacy": True},
                   {"slot": "slot2", "rss_kb": GB // 5, "fresh": True}],
                  f"shared legacy forecast: {GB // 2} KB")]
        for rows, reason in cases:
            with tempfile.TemporaryDirectory() as state:
                readings = [[], rows] if recheck else [rows]
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr), \
                     mock.patch.object(heavy, "jobs", side_effect=readings), \
                     mock.patch.object(heavy.time, "sleep", side_effect=Waiting), \
                     mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
                    assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                                                     environ, lambda: 0), Waiting)
                assert f"slot1 ({reason})" in stderr.getvalue()
                assert "resume stopped monitors or reduce running memory" in stderr.getvalue()
                assert "slots busy" not in stderr.getvalue()

        # A forecast below the memory threshold must not name memory as the
        # cause when load alone blocks, at either admission check.
        with tempfile.TemporaryDirectory() as state:
            rows = [{"slot": "slot1", "rss_kb": None, "fresh": False, "legacy": True}]
            readings = [[], rows] if recheck else [rows]
            loads = iter([0, 100] if recheck else [100])
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr), \
                 mock.patch.object(heavy, "jobs", side_effect=readings), \
                 mock.patch.object(heavy.time, "sleep", side_effect=Waiting), \
                 mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
                assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                    dict(environ, HEAVY_MAX_LOAD="1"), lambda: next(loads)), Waiting)
            assert stderr.getvalue() == f"heavy: waiting for memory or load (see {state})\n"

    # A prior generic load warning must not hide a later reservation warning.
    with tempfile.TemporaryDirectory() as state:
        stderr = io.StringIO()
        rows = [{"slot": "slot0", "rss_kb": None, "fresh": False,
                 "legacy": True, "legacy_rss_kb": 2 * GB}]
        with contextlib.redirect_stderr(stderr), \
             mock.patch.object(heavy, "jobs", side_effect=[[], rows]), \
             mock.patch.object(heavy.time, "sleep", side_effect=[None, Waiting]), \
             mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
            assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                          dict(environ, HEAVY_MAX_LOAD="1"), lambda: 100), Waiting)
        assert "waiting for memory or load" in stderr.getvalue()
        assert f"slot0 (legacy RSS: {2 * GB} KB)" in stderr.getvalue()


def test_registry_wait_messages():
    # fren-covers: testing::heavy_registry, testing::heavy_wait_message
    class Waiting(Exception):
        pass

    for stage in ("read", "claim", "recheck"):
        with tempfile.TemporaryDirectory() as state, contextlib.ExitStack() as stack:
            stderr = io.StringIO()
            stack.enter_context(contextlib.redirect_stderr(stderr))
            stack.enter_context(mock.patch.object(heavy.time, "sleep", side_effect=Waiting))
            run = stack.enter_context(mock.patch.object(heavy, "run"))
            readings = [heavy.RegistryBusy()] if stage == "read" else [0, heavy.RegistryBusy()]
            if stage == "claim":
                stack.enter_context(mock.patch.object(heavy, "registry", side_effect=heavy.RegistryBusy))
                readings = [0]
            stack.enter_context(mock.patch.object(heavy, "heavy_rss_kb", side_effect=readings))
            assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                {"HEAVY_SLOTS": "1", "HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "off"}), Waiting)
            run.assert_not_called()
            assert stderr.getvalue() == f"heavy: waiting for registry lock (see {state})\n"
            if stage != "read":
                with open(os.path.join(state, "slot0"), "a+") as slot:
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


def tiny_job(state, command, overrides=None, timeout=30):
    # Invoke main in a fresh process, with no real load or shared state.
    code = ("import runpy,sys; h=runpy.run_path(sys.argv[1]); "
            "sys.exit(h['main'](sys.argv[3:], state=sys.argv[2], load_reader=lambda: 0.5))")
    environ = dict(os.environ, HEAVY_SLOTS="1", HEAVY_MEM_GB="1", HEAVY_MAX_LOAD="off")
    environ.pop("HEAVY_LOG", None)
    environ.pop("FREN_JOB_KIND", None)
    environ.update(overrides or {})
    return subprocess.run([sys.executable, "-I", "-B", "-c", code,
                           os.path.join(HERE, "heavy"), state] + command,
                          env=environ, capture_output=True, text=True, timeout=timeout)


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
        assert row["cpu_user_seconds"] >= 0 and row["cpu_system_seconds"] >= 0
        assert row["cpu_seconds"] == row["cpu_user_seconds"] + row["cpu_system_seconds"]
        assert row["cpu_parallelism"] == row["cpu_seconds"] / row["run_seconds"]
        assert row["max_load"] == "off" and row["slots"] == 1
        assert row["enqueued_max_load"] == "off" and row["enqueued_slots"] == 1
        assert row["wait_policy_changed"] is False
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
        assert rows[1]["cpu_seconds"] == rows[1]["cpu_parallelism"] == 0  # No child ran.
        for row in rows:
            assert row["cpu_seconds"] >= 0 and row["cpu_parallelism"] >= 0
            if row["cpu_busy_samples"]:
                assert 0 <= row["cpu_busy_mean"] <= row["cpu_busy_max"] <= 1
            else:
                assert row["cpu_busy_mean"] is row["cpu_busy_max"] is None
        result = tiny_job(state, ["--stats", "1"])
        assert result.returncode == 0, result.stderr
        assert json.loads(result.stdout)["jobs"] == 4
        for args in (["--stats", "0"], ["--stats", "nan"], ["--stats", "1", "2"]):
            assert tiny_job(state, args).returncode == 2
        for args in (["--alternate"], ["--alternate", "0", "8"],
                     ["--alternate", "60", "nan"], ["--alternate", "60", "8", "x"]):
            assert tiny_job(state, args).returncode == 2


def proc_line(pid=123, name="lean", group=7, user=10, system=20, start=100, state="R", parent=1, pages=3):
    fields = ["0"] * 50
    for i, value in ((0, state), (1, parent), (2, group), (11, user), (12, system),
                     (13, 99999), (14, 88888), (19, start), (21, pages)):
        fields[i] = str(value)
    return f"{pid} ({name}) " + " ".join(fields)


def slot_monitor(state, slot):
    """The kernel identity available to verification on this filesystem."""
    release = heavy.re.match(r"(\d+)\.(\d+)", heavy.platform.release())
    if (heavy.platform.system() != "Linux" or release is None
            or tuple(map(int, release.groups())) < (4, 9)):
        return None
    try:
        st = os.stat(os.path.join(state, slot))
        key = (os.major(st.st_dev), os.minor(st.st_dev), st.st_ino)
        pid = heavy.flock_owners().get(key)
        return heavy.monitor_identity(pid) if pid is not None else None
    except (OSError, ValueError, IndexError, StopIteration):
        return None


def child_stopped(pid):
    # waitid uses our child PID namespace, unlike /proc/<local-pid>/stat.
    # WNOWAIT keeps the stop event available for a later confirmation.
    event = os.waitid(os.P_PID, pid, os.WSTOPPED | os.WEXITED | os.WNOHANG | os.WNOWAIT)
    return event is not None and event.si_code == os.CLD_STOPPED and event.si_status == signal.SIGSTOP


def await_stopped(child):
    deadline = heavy.time.monotonic() + 15
    while not child_stopped(child.pid):
        assert child.poll() is None, "child exited before acknowledging SIGSTOP"
        assert heavy.time.monotonic() < deadline, "child did not acknowledge SIGSTOP"
        heavy.time.sleep(0.01)


def test_slot_identity():
    # fren-covers: testing::heavy_lease, testing::heavy_memory_victim
    with tempfile.TemporaryDirectory() as state, mock.patch.object(heavy.time, "monotonic", return_value=100):
        first = open(os.path.join(state, "slot0"), "a+")
        second = open(os.path.join(state, "slot1"), "a+")
        try:
            with heavy.registry(state):
                assert heavy.claim_slot(first, "slot0", state, {"enqueued_at": 10})
                assert heavy.claim_slot(second, "slot1", state, {"enqueued_at": 10})
            # Different namespaces can have the same numeric PID. Neither
            # liveness, accounting nor eviction may resolve those foreign IDs.
            first.heavy_job.update(local_pgid=5, pid_namespace="pid:[100]")
            second.heavy_job.update(local_pgid=5, pid_namespace="pid:[200]")
            heavy.publish_memory(first, 40, state)
            heavy.publish_memory(second, 30, state)
            with mock.patch.object(heavy, "group_rss_kb", side_effect=AssertionError("foreign PID lookup")):
                assert heavy.heavy_rss_kb(state) == 70
                total, victim = heavy.memory_victim(heavy.jobs(state), 60)
            assert total == 70 and victim == second.heavy_job["job_id"]
            assert first.heavy_job["job_id"] != second.heavy_job["job_id"]
            assert first.heavy_job["order"] < second.heavy_job["order"]
            assert heavy.memory_victim(heavy.jobs(state), 70) == (70, None)
            # A stale live report retains a charge in both verification modes.
            stale = dict(first.heavy_job, updated_monotonic=heavy.time.monotonic() - heavy.REPORT_STALE_SECONDS - 1)
            with heavy.registry(state):
                heavy.atomic_state(heavy.report_path(state, "slot0"), stale)
            verified = slot_monitor(state, "slot0") == first.heavy_job["monitor"] and first.heavy_job["monitor"] is not None
            rows = {r["slot"]: r for r in heavy.jobs(state)}
            assert rows["slot0"]["legacy"] == (not verified)
            assert rows["slot0"]["rss_kb"] == (40 if verified else None)
            assert rows["slot0"]["fresh"] is False
            expected_total = 70 if verified else 30
            assert heavy.heavy_rss_kb(state, 80) == (110 if verified else 70)
            assert heavy.memory_victim(list(rows.values()), 80) == (expected_total, None)
            # Wall-clock changes cannot turn reservations into eviction evidence.
            with mock.patch.object(heavy.time, "time", return_value=-1000000):
                assert heavy.memory_victim(heavy.jobs(state), 80) == (expected_total, None)
            heavy.publish_memory(first, 40, state)
            saved = dict(second.heavy_job)
            heavy.release_slot(second, state)
            # A dead lease's stale metadata is ignored, including after PID reuse.
            heavy.atomic_state(heavy.report_path(state, "slot1"), saved)
            assert heavy.heavy_rss_kb(state) == 40
            second = open(os.path.join(state, "slot1"), "a+")
            with heavy.registry(state):
                assert heavy.claim_slot(second, "slot1", state, {"enqueued_at": 9})
            assert second.heavy_job["job_id"] != saved["job_id"]
            assert second.heavy_job["order"] > saved["order"]  # No wall-clock or PID ordering.
            assert heavy.heavy_rss_kb(state) == 40
        finally:
            if not first.closed:
                heavy.release_slot(first, state)
            if not second.closed:
                heavy.release_slot(second, state)
        with open(os.path.join(state, "slot0"), "a+") as legacy:
            heavy.fcntl.flock(legacy, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
            assert heavy.jobs(state)[0]["legacy"]  # Empty does not mean unheld.
            assert heavy.heavy_rss_kb(state, 80) == 40
            legacy.write("5 10 foreign-job\n")
            legacy.flush()
            assert heavy.heavy_rss_kb(state, 80) == 40  # Never resolve this foreign PID.
        assert heavy.jobs(state) == []


def test_proc_namespace_translation():
    # fren-covers: testing::heavy_lease
    with tempfile.TemporaryDirectory() as proc:
        for pid in ("self", "1", "6", "901", "902", "903"):
            os.mkdir(os.path.join(proc, pid))
        for pid, ns in (("self", "pid:[inner]"), ("1", "pid:[outer]")):
            os.mkdir(os.path.join(proc, pid, "ns"))
            os.symlink(ns, os.path.join(proc, pid, "ns", "pid"))
        for pid, text, ids in (
                ("self", proc_line(pid=900, group=900), "900 5"),
                ("6", proc_line(pid=6, group=6, parent=999), "6"),
                ("901", proc_line(pid=901, group=901, parent=900), "901 6"),
                ("902", proc_line(pid=902, group=902, parent=999), "902 6"),
                ("903", proc_line(pid=903, group=903, parent=900), "903 7")):
            with open(os.path.join(proc, pid, "stat"), "w") as f:
                f.write(text)
            with open(os.path.join(proc, pid, "status"), "w") as f:
                f.write(f"NSpid:\t{ids}\n")
        with mock.patch.object(heavy.os, "getpid", return_value=5):
            assert heavy.visible_group(6, proc, "Linux") == 901
        # Equal numeric caller PIDs are insufficient in an ancestor procfs view.
        with open(os.path.join(proc, "self", "status"), "w") as f:
            f.write("NSpid:\t900 900\n")
        with mock.patch.object(heavy.os, "getpid", return_value=900):
            assert heavy.visible_group(6, proc, "Linux") == 901
        # On a host NSpid has one entry. Neither root's namespace symlink
        # nor a scan of unrelated processes is needed for the fast path.
        with open(os.path.join(proc, "self", "status"), "w") as f:
            f.write("NSpid:\t900\n")
        with open(os.path.join(proc, "6", "stat"), "w") as f:
            f.write(proc_line(pid=6, group=6, parent=900))
        with mock.patch.object(heavy.os, "getpid", return_value=900), \
             mock.patch.object(heavy.os, "readlink", side_effect=PermissionError()), \
             mock.patch.object(heavy.os, "listdir", side_effect=AssertionError("host scan")):
            assert heavy.visible_group(6, proc, "Linux") == 6


def test_memory_victim():
    # fren-covers: testing::heavy_memory_victim, testing::heavy_owned_signal
    older = {"job_id": "old", "order": 1, "rss_kb": 60}
    newer = {"job_id": "new", "order": 2, "rss_kb": 20}
    for leases in ([older, newer], [newer, older]):
        assert heavy.memory_victim(leases, 80) == (80, None)
        assert heavy.memory_victim(leases, 79) == (80, "new")
    assert heavy.memory_victim([], 1) == (0, None)
    stale = dict(newer, fresh=False)
    assert heavy.memory_victim([older, stale], 80) == (80, None)
    assert heavy.memory_victim([older, stale], 79) == (80, "new")
    missing = dict(newer, rss_kb=None)
    assert heavy.memory_victim([older, missing], 1) == (60, "old")
    legacy = {"job_id": None, "order": None, "rss_kb": None}
    assert heavy.memory_victim([legacy], 1) == (0, None)
    for leases in ([older, legacy, newer], [newer, legacy, older]):
        assert heavy.memory_victim(leases, 1) == (80, "new")
    measured = dict(legacy, legacy=True, legacy_rss_kb=30)
    assert heavy.memory_victim([newer, measured], 49) == (50, "new")
    assert heavy.memory_victim([newer, measured], 50) == (50, None)
    assert heavy.memory_victim([measured], 1) == (30, None)  # Never target a legacy owner.
    assert heavy.memory_victim([newer, dict(measured, legacy_rss_kb=-30)], 19) == (20, "new")
    assert heavy.memory_victim([older, dict(newer, order=0, rss_kb=100)], 79) == (60, None)
    assert heavy.memory_victim([older, dict(newer, rss_kb=-100)], 59) == (60, "old")


def test_legacy_reservations():
    # fren-covers: testing::heavy_legacy_lease, testing::heavy_memory_victim
    with tempfile.TemporaryDirectory() as state:
        for cap in range(5, 101):
            share = heavy.legacy_reservation(cap)
            assert 0 < share and 5 * share <= 3 * cap
            assert heavy.can_start(0, share, cap, None)
            for observed in (None, -1, 0, 1, cap, 2 * cap):
                charged = heavy.legacy_reservation(cap, observed)
                assert charged == (observed if observed is not None and observed >= 0 else share)
                if observed is not None and 5 * observed > 3 * cap:
                    assert not heavy.can_start(0, charged, cap, None)
            for count in range(1, 9):
                rows = [{"slot": f"slot{i}", "legacy": True, "legacy_rss_kb": None,
                         "rss_kb": None, "fresh": False} for i in range(count)]
                with mock.patch.object(heavy, "jobs", return_value=rows):
                    assert heavy.heavy_rss_kb(state, cap) == share
        unknown = {"slot": "slot0", "legacy": True, "legacy_rss_kb": None,
                   "rss_kb": None, "fresh": False}
        known = dict(unknown, slot="slot1", legacy_rss_kb=10)
        with mock.patch.object(heavy, "jobs", return_value=[unknown, known]):
            assert heavy.heavy_rss_kb(state, 100) == 60
            assert heavy.can_start(0, heavy.heavy_rss_kb(state, 100), 100, None)
        with mock.patch.object(heavy, "jobs", return_value=[unknown, dict(known, legacy_rss_kb=11)]):
            assert not heavy.can_start(0, heavy.heavy_rss_kb(state, 100), 100, None)
    assert heavy.legacy_reservation(100, 0) == 0  # Verified zero differs from unknown.
    assert heavy.legacy_reservation(0) == 1


def test_report_owner():
    # fren-covers: testing::heavy_report_owner
    monitor = {"pid": 5, "start": 20, "namespace": "pid:[100]"}
    report = {"job_id": "job", "updated_monotonic": 100, "monitor": monitor}
    for now in (99, 100, 100 + heavy.REPORT_STALE_SECONDS,
                101 + heavy.REPORT_STALE_SECONDS):
        fresh = 0 <= now - 100 <= heavy.REPORT_STALE_SECONDS
        assert heavy.report_current(report, "job", None, now) == fresh
        assert heavy.report_current(report, "job", monitor, now)
        for key, value in (("pid", 6), ("start", 21), ("namespace", "pid:[200]")):
            assert not heavy.report_current(report, "job", dict(monitor, **{key: value}), now)
        assert not heavy.report_current(report, "other", monitor, now)


def test_legacy_proc_readings():
    # fren-covers: testing::heavy_legacy_lease
    with tempfile.TemporaryDirectory() as proc, mock.patch.object(heavy.platform, "release", return_value="6.0"):
        key = (0, 47, 32388)
        text = ("3: FLOCK ADVISORY WRITE 900 00:2f:32388 0 EOF\n"
                "4: -> FLOCK ADVISORY WRITE 901 00:2f:32388 0 EOF\n"
                "5: OFDLCK ADVISORY WRITE -1 00:2f:32389 0 EOF\n"
                "6: FLOCK ADVISORY READ 901 00:2f:32390 0 EOF\n")
        with open(os.path.join(proc, "locks"), "w") as f:
            f.write(text)
        for pid, parent, group, pages in ((900, 1, 800, 2), (901, 900, 901, 10),
                                         (902, 901, 901, 20), (5, 999, 5, 10000)):
            os.mkdir(os.path.join(proc, str(pid)))
            with open(os.path.join(proc, str(pid), "stat"), "w") as f:
                f.write(proc_line(pid=pid, parent=parent, group=group, pages=pages))
        assert heavy.flock_owners(proc) == {key: 900}
        with open(os.path.join(proc, "900", "status"), "w") as f:
            f.write("Name:\tlegacy\n")
        assert raises(lambda: heavy.monitor_identity(900, proc), ValueError)
        lease = {"lock_key": key, "legacy": True, "legacy_rss_kb": None}
        heavy.legacy_readings([lease], proc, "Linux")
        assert lease["legacy_rss_kb"] == 30 * os.sysconf("SC_PAGE_SIZE") // 1024
        # A foreign numeric PID in a status file has no role in this lookup:
        # the very large unrelated group 5 must never count as the job.
        changed = {"lock_key": key, "legacy": True, "legacy_rss_kb": None}
        with mock.patch.object(heavy, "flock_owners", side_effect=[{key: 900}, {key: 5}]):
            heavy.legacy_readings([changed], proc, "Linux")
        assert changed["legacy_rss_kb"] is None
        hidden = {"lock_key": key, "legacy": True, "legacy_rss_kb": None}
        with mock.patch.object(heavy, "flock_owners", return_value={}):
            heavy.legacy_readings([hidden], proc, "Linux")
        assert hidden["legacy_rss_kb"] is None
        old_kernel = {"lock_key": key, "legacy": True, "legacy_rss_kb": None}
        with mock.patch.object(heavy.platform, "release", return_value="4.8"), \
             mock.patch.object(heavy, "flock_owners", side_effect=AssertionError("unqualified PID view")):
            heavy.legacy_readings([old_kernel], proc, "Linux")
        assert old_kernel["legacy_rss_kb"] is None
        calls = []
        def reused_pid(view):
            calls.append(True)
            if len(calls) == 2:
                with open(os.path.join(proc, "900", "stat"), "w") as f:
                    f.write(proc_line(pid=900, group=800, start=101))
            return {key: 900}
        reused = {"lock_key": key, "legacy": True, "legacy_rss_kb": None}
        with mock.patch.object(heavy, "flock_owners", side_effect=reused_pid):
            heavy.legacy_readings([reused], proc, "Linux")
        assert reused["legacy_rss_kb"] is None


def test_legacy_report_reuse():
    # fren-covers: testing::heavy_lease, testing::heavy_legacy_lease, testing::heavy_memory_victim
    with tempfile.TemporaryDirectory() as state:
        slot = open(os.path.join(state, "slot0"), "a+")
        with heavy.registry(state):
            assert heavy.claim_slot(slot, "slot0", state, {"enqueued_at": 0})
        heavy.publish_memory(slot, 1000, state)
        saved = dict(slot.heavy_job)
        heavy.release_slot(slot, state)
        heavy.atomic_state(heavy.report_path(state, "slot0"), dict(saved, monitor=[]))
        assert heavy.read_report(heavy.report_path(state, "slot0")) is None
        heavy.atomic_state(heavy.report_path(state, "slot0"), saved)
        with open(os.path.join(state, "slot0"), "w+") as legacy:
            heavy.fcntl.flock(legacy, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
            legacy.write("5 10 foreign-job\n")
            legacy.flush()
            row = heavy.jobs(state)[0]
            assert row["legacy"] and row["job_id"] is None and row["rss_kb"] is None
            assert heavy.heavy_rss_kb(state, 100) == 50
            assert heavy.memory_victim([row], 1) == (0, None)
            # A status token for another owner cannot authenticate the report.
            legacy.seek(0)
            legacy.truncate()
            legacy.write("0 0 [heavy-job=" + "0" * 32 + "]\n")
            legacy.flush()
            row = heavy.jobs(state)[0]
            assert row["legacy"] and row["rss_kb"] is None
            assert heavy.heavy_rss_kb(state, 100) == 50
        if heavy.platform.system() == "Linux":
            # A different legacy owner can stop before overwriting the status.
            # Visible kernel ownership rejects an inherited token immediately;
            # without it, only freshness can distinguish the old report.
            with open(os.path.join(state, "slot0"), "w") as f:
                f.write(f"0 0 [heavy-job={saved['job_id']}]\n")
            ready = os.path.join(state, "ready")
            code = ("import fcntl,pathlib,sys,time; f=open(sys.argv[1],'a+'); "
                    "fcntl.flock(f,fcntl.LOCK_EX); pathlib.Path(sys.argv[2]).touch(); time.sleep(30)")
            owner = subprocess.Popen([sys.executable, "-I", "-B", "-c", code,
                                      os.path.join(state, "slot0"), ready])
            try:
                deadline = heavy.time.monotonic() + 5
                while not os.path.exists(ready) and owner.poll() is None and heavy.time.monotonic() < deadline:
                    heavy.time.sleep(0.01)
                assert os.path.exists(ready) and owner.poll() is None
                verified = slot_monitor(state, "slot0") is not None
                stamp = heavy.time.monotonic()
                heavy.atomic_state(heavy.report_path(state, "slot0"), dict(saved, updated_monotonic=stamp))
                with mock.patch.object(heavy.time, "monotonic", return_value=stamp):
                    row = heavy.jobs(state)[0]
                    assert row["legacy"] == verified
                    assert row["rss_kb"] == (None if verified else 1000)
                    assert heavy.heavy_rss_kb(state, 100) == (50 if verified else 1000)
                # Both modes reject unverified metadata once it expires.
                heavy.atomic_state(heavy.report_path(state, "slot0"),
                    dict(saved, updated_monotonic=stamp - heavy.REPORT_STALE_SECONDS - 1))
                row = heavy.jobs(state)[0]
                assert row["legacy"] and row["rss_kb"] is None
                assert heavy.heavy_rss_kb(state, 100) == 50
            finally:
                owner.terminate()
                owner.wait(timeout=5)


def test_legacy_coexistence():
    # fren-covers: testing::heavy_legacy_lease, testing::heavy_lease
    # Unknown legacy memory remains charged, but a free slot can admit new work.
    for slots in (2, 4):
        with tempfile.TemporaryDirectory() as state, contextlib.ExitStack() as stack:
            for index in range(slots - 1):
                legacy = stack.enter_context(open(os.path.join(state, f"slot{index}"), "w+"))
                heavy.fcntl.flock(legacy, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
                legacy.write("5 10 foreign-job\n")
                legacy.flush()
            cap = int(0.5 * GB)
            assert heavy.heavy_rss_kb(state, cap) == cap // 2
            result = tiny_job(state, [sys.executable, "-c", "pass"],
                              {"HEAVY_SLOTS": str(slots), "HEAVY_MEM_GB": "0.5"}, timeout=10)
            assert result.returncode == 0, result.stderr
            rows = heavy.jobs(state)
            assert len(rows) == slots - 1 and all(row["legacy"] for row in rows)
            # The memory forecast alone cannot admit a job with no free slot.
            occupied = stack.enter_context(open(os.path.join(state, f"slot{slots - 1}"), "w+"))
            heavy.fcntl.flock(occupied, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
            class Waiting(Exception):
                pass
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr), \
                 mock.patch.object(heavy.time, "sleep", side_effect=Waiting) as sleep, \
                 mock.patch.object(heavy, "run", side_effect=AssertionError("admitted without a free slot")) as run:
                assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                    {"HEAVY_SLOTS": str(slots), "HEAVY_MEM_GB": "0.5", "HEAVY_MAX_LOAD": "off"}), Waiting)
                run.assert_not_called()
                sleep.assert_called_once_with(2)
            assert stderr.getvalue() == f"heavy: all {slots} slots busy, waiting (see {state})\n"
    if heavy.platform.system() != "Linux":
        return
    with tempfile.TemporaryDirectory() as state:
        ready, stop = os.path.join(state, "ready"), os.path.join(state, "stop")
        owner = """
import fcntl, os, pathlib, subprocess, sys, time
with open(os.path.join(sys.argv[1], 'slot0'), 'w+') as slot:
    fcntl.flock(slot, fcntl.LOCK_EX)
    worker = subprocess.Popen([sys.executable, '-c',
        "import pathlib,sys,time; memory=bytearray(4*1024*1024); pathlib.Path(sys.argv[1]).touch(); time.sleep(30)",
        sys.argv[2]], start_new_session=True)
    slot.write(f'{worker.pid} {time.time()} legacy-job\\n'); slot.flush()
    try:
        while not pathlib.Path(sys.argv[3]).exists(): time.sleep(0.01)
    finally:
        worker.terminate(); worker.wait(timeout=5)
"""
        legacy = subprocess.Popen([sys.executable, "-I", "-B", "-c", owner, state, ready, stop])
        try:
            deadline = heavy.time.monotonic() + 10
            while not os.path.exists(ready) and legacy.poll() is None and heavy.time.monotonic() < deadline:
                heavy.time.sleep(0.01)
            assert os.path.exists(ready) and legacy.poll() is None
            row = heavy.jobs(state)[0]
            assert row["legacy"]
            if row["legacy_rss_kb"] is not None:
                assert row["legacy_rss_kb"] >= 4 * 1024
            cap = int(0.5 * GB)
            assert 5 * heavy.heavy_rss_kb(state, cap) <= 3 * cap
            result = tiny_job(state, [sys.executable, "-c", "pass"],
                              {"HEAVY_SLOTS": "2", "HEAVY_MEM_GB": "0.5"}, timeout=10)
            assert result.returncode == 0 and legacy.poll() is None, result.stderr
        finally:
            with open(stop, "w") as f:
                f.write("stop")
            legacy.wait(timeout=10)


def test_group_completion():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal
    for reaped in (False, True):
        for exists in (False, True):
            effect = None if exists else ProcessLookupError()
            with mock.patch.object(heavy.os, "killpg", side_effect=effect) as probe:
                assert heavy.group_gone(5, lambda: reaped) == (reaped and not exists)
                assert probe.call_count == int(reaped)
                if probe.called:
                    probe.assert_called_once_with(5, 0)
    with mock.patch.object(heavy.os, "killpg", side_effect=PermissionError()):
        assert not heavy.group_gone(5, lambda: True)
    with mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()) as probe:
        assert not heavy.group_gone(5, lambda: False, True)
        probe.assert_not_called()
        assert heavy.group_gone(5, lambda: True, True)
        heavy.kill_group(5, lambda: True, True)
        assert probe.call_args_list == [mock.call(5, 0)] * 2
    with mock.patch.object(heavy.os, "killpg") as probe:
        assert not heavy.group_gone(5, lambda: True, True)
        probe.assert_called_once_with(5, 0)
    with mock.patch.object(heavy.os, "killpg", side_effect=PermissionError()):
        assert not heavy.group_gone(5, lambda: True, True)


def test_namespace_init_reaping():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal, testing::heavy_init_reap
    for subreaper in (False, True):
        peek = SimpleNamespace(si_pid=7)
        with mock.patch.object(heavy.os, "getpid", return_value=1), \
             mock.patch.object(heavy.os, "waitid", side_effect=[peek, None]) as peek_wait, \
             mock.patch.object(heavy.os, "getpgid", return_value=9), \
             mock.patch.object(heavy.os, "waitpid", return_value=(7, 0)) as wait, \
             mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()) as probe:
            assert not heavy.group_gone(5, lambda: False, subreaper)
            peek_wait.assert_not_called()  # Collect group usage before init cleanup.
            assert heavy.group_gone(5, lambda: True, subreaper)
            assert peek_wait.call_args_list == [mock.call(
                os.P_ALL, 0, os.WEXITED | os.WNOHANG | os.WNOWAIT)] * 2
            wait.assert_called_once_with(7, os.WNOHANG)
            probe.assert_called_once_with(5, 0)
    # Adoption can race the successful group reap: preserve the new member's
    # wait4 usage instead of consuming it through the init's waitpid path.
    rss = 10 * 1024 if heavy.platform.system() == "Darwin" else 10
    usage = SimpleNamespace(ru_utime=2.5, ru_stime=1.25, ru_maxrss=rss, ru_nivcsw=3)
    child = SimpleNamespace(pid=5, returncode=7, heavy_subreaper=True)
    record = {"peak_rss_kb": 0}
    with mock.patch.object(heavy.os, "getpid", return_value=1), \
         mock.patch.object(heavy.os, "waitid", side_effect=[SimpleNamespace(si_pid=7), None]), \
         mock.patch.object(heavy.os, "getpgid", return_value=5), \
         mock.patch.object(heavy.os, "wait4", side_effect=[ChildProcessError(), (7, 0, usage), ChildProcessError()]) as wait4, \
         mock.patch.object(heavy.os, "waitpid", side_effect=AssertionError("lost group usage")), \
         mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()):
        assert heavy.group_gone(5, lambda: heavy.reap_child(child, record), True)
        assert wait4.call_args_list == [mock.call(-5, os.WNOHANG)] * 3
        assert record["_cpu_usage"] == (2.5, 1.25, 10, 3)
        assert child.returncode == 7
    # A live adopted child outside the group never turns init cleanup into
    # a blocking wait or keeps the job's own group alive.
    with mock.patch.object(heavy.os, "getpid", return_value=1), \
         mock.patch.object(heavy.os, "waitid", return_value=None) as peek, \
         mock.patch.object(heavy.os, "waitpid", side_effect=AssertionError("waited for live orphan")), \
         mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()):
        assert heavy.group_gone(5, lambda: True, True)
        peek.assert_called_once_with(os.P_ALL, 0, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    with mock.patch.object(heavy.os, "getpid", return_value=1), \
         mock.patch.object(heavy.os, "waitid", side_effect=ChildProcessError()), \
         mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()):
        assert heavy.group_gone(5, lambda: True, True)
    with mock.patch.object(heavy.os, "getpid", return_value=2), \
         mock.patch.object(heavy.os, "waitid") as wait, \
         mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()):
        assert heavy.group_gone(5, lambda: True, True)
        wait.assert_not_called()


def test_namespace_init_workers():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal, testing::heavy_init_reap
    for subreaper in (False, True):
        namespace_init_workers(subreaper)


def namespace_init_workers(subreaper):
    if heavy.platform.system() != "Linux":
        return
    prefix = ["unshare", "--user", "--map-root-user", "--pid", "--fork", "--kill-child=KILL", "--"]
    try:
        probe = subprocess.run(prefix + ["true"], capture_output=True, timeout=10)
        supported = probe.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        supported = False
    if not supported:
        assert os.environ.get("HEAVY_REQUIRE_PIDNS_TEST") != "1", "PID namespace init integration is required"
        print("heavy: skipped PID namespace init integration (kernel/container forbids unshare)")
        return
    with tempfile.TemporaryDirectory() as state:
        ready = os.path.join(state, "worker")
        reaped = os.path.join(state, "reaped")
        worker = ("import os,pathlib,sys,time; memory=bytearray(48*1024*1024); "
                  "pathlib.Path(sys.argv[1]).write_text(str(os.getpid())); time.sleep(60)")
        outside = os.path.join(state, "outside")
        orphan = ("import os,pathlib,sys; pathlib.Path(sys.argv[1]).write_text(str(os.getpid()))")
        leader = ("import os,subprocess,sys,time; "
                  f"outside_child=subprocess.Popen([sys.executable,'-c',{orphan!r},{outside!r}], start_new_session=True); "
                  "os.waitid(os.P_PID,outside_child.pid,os.WEXITED|os.WNOWAIT); "
                  f"subprocess.Popen([sys.executable,'-c',{worker!r},{ready!r}]); time.sleep(60)")
        launcher = """
import contextlib, os, pathlib, runpy, sys
assert os.getpid() == 1
h = runpy.run_path(sys.argv[1])
if sys.argv[5] == 'fallback':
    h['main'].__globals__['child_subreaper'] = contextlib.contextmanager(lambda: iter([False]))
waitpid, wait4 = os.waitpid, os.wait4
def record_result(result):
    if result[0] > 0:
        with open(sys.argv[4], 'a') as f:
            f.write(str(result[0]) + '\\n')
    return result
os.waitpid = lambda pid, flags: record_result(waitpid(pid, flags))
os.wait4 = lambda pid, flags: record_result(wait4(pid, flags))
sys.exit(h['main']([sys.executable, '-c', sys.argv[3]], state=sys.argv[2], load_reader=lambda: 0))
"""
        env = dict(os.environ, HEAVY_SLOTS="1", HEAVY_MEM_GB="0.04", HEAVY_MAX_LOAD="off")
        env.pop("HEAVY_LOG", None)
        child = subprocess.Popen(prefix + [sys.executable, "-I", "-B", "-c", launcher,
            os.path.join(HERE, "heavy"), state, leader, reaped, "default" if subreaper else "fallback"], env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = heavy.time.monotonic() + 10
            while not os.path.exists(ready) and child.poll() is None and heavy.time.monotonic() < deadline:
                heavy.time.sleep(0.01)
            assert os.path.exists(ready), child.communicate(timeout=10)
            # Reaping must be observed, independently of machine speed.
            out, err = child.communicate(timeout=30)
            assert child.returncode == 137 and "heavy: killed" in err, (out, err)
            assert os.path.exists(reaped), "namespace init did not reap its adopted worker"
            with open(outside) as f:
                outside_pid = f.read()
            with open(reaped) as f:
                reaped_pids = f.read().splitlines()
            assert outside_pid in reaped_pids, "namespace init left its outside-group orphan zombie"
            with open(ready) as f:
                worker_pid = f.read()
            assert worker_pid in reaped_pids, "namespace init did not reap its same-group worker"
            with open(os.path.join(state, "log.jsonl")) as f:
                logged = [json.loads(line) for line in f]
            assert logged[-1]["cpu_scope"] == ("process_group" if subreaper else "waited_tree")
            print(f"heavy: PID namespace init reaped outside-group orphan (subreaper={subreaper})")
        finally:
            if child.poll() is None:
                child.terminate()
            child.communicate(timeout=15)


@contextlib.contextmanager
def adopt_workers():
    """The harness reaps its orphaned worker, independently of heavy's mode."""
    libc = ctypes.CDLL(None)
    previous = ctypes.c_int()
    assert libc.prctl(37, ctypes.byref(previous), 0, 0, 0) == 0
    assert libc.prctl(36, 1, 0, 0, 0) == 0
    try:
        yield True
    finally:
        assert libc.prctl(36, previous.value, 0, 0, 0) == 0


def test_fallback_escalation():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal
    if heavy.platform.system() != "Linux":
        return
    # The harness adopts/reaps the orphan, as a working init would. The
    # heavy instance under test reaps only its leader; the harness must
    # not reap that leader on its behalf.
    with adopt_workers() as enabled, tempfile.TemporaryDirectory() as state:
        assert enabled
        ready = os.path.join(state, "worker")
        worker = ("import os,pathlib,signal,sys,time; "
                  "signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                  "pathlib.Path(sys.argv[1]+'.tmp').write_text(str(os.getpid())); "
                  "os.replace(sys.argv[1]+'.tmp',sys.argv[1]); "
                  "memory=bytearray(48*1024*1024); time.sleep(60)")
        leader = ("import subprocess,sys,time; "
                  f"subprocess.Popen([sys.executable,'-c',{worker!r},{ready!r}], "
                  "stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); time.sleep(60)")
        launcher = ("import contextlib,runpy,sys; h=runpy.run_path(sys.argv[1]); "
                    "h['main'].__globals__['child_subreaper']=contextlib.contextmanager(lambda:iter([False])); "
                    "sys.exit(h['main'](sys.argv[3:],state=sys.argv[2],load_reader=lambda:0))")
        env = dict(os.environ, HEAVY_SLOTS="1", HEAVY_MEM_GB="0.04", HEAVY_MAX_LOAD="off")
        env.pop("HEAVY_LOG", None)
        child = subprocess.Popen([sys.executable, "-I", "-B", "-c", launcher,
                                  os.path.join(HERE, "heavy"), state, sys.executable, "-c", leader],
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        pid, reaper = None, None
        status = []
        stop = threading.Event()
        def reap_worker():
            while not stop.is_set():
                try:
                    found, code = os.waitpid(pid, os.WNOHANG)
                    if found:
                        status.append(code)
                        return
                except ChildProcessError:
                    pass  # The leader has not exited/reparented the worker yet.
                stop.wait(0.02)
        try:
            deadline = heavy.time.monotonic() + 15
            while not os.path.exists(ready) and child.poll() is None and heavy.time.monotonic() < deadline:
                heavy.time.sleep(0.02)
            assert os.path.exists(ready), child.communicate(timeout=15)
            with open(ready) as f:
                pid = int(f.read())
            reaper = threading.Thread(target=reap_worker, daemon=True)
            reaper.start()
            out, err = child.communicate(timeout=20)
            reaper.join(timeout=15)
            assert child.returncode == 137, (out, err)
            assert status and os.waitstatus_to_exitcode(status[0]) == -signal.SIGKILL
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                pass
            else:
                raise AssertionError("worker survived fallback group termination")
            with open(os.path.join(state, "log.jsonl")) as f:
                assert json.loads(f.read())["exit_status"] == 137
        finally:
            if pid is not None and not status:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            if child.poll() is None:
                child.terminate()
            child.communicate(timeout=15)
            if reaper:
                reaper.join(timeout=5)
            stop.set()


def test_no_signal_after_reap():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal
    with mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()) as probe:
        heavy.kill_group(5, lambda: True)
        probe.assert_called_once_with(5, 0)


def test_status_failure_cleanup():
    # fren-covers: testing::heavy_owned_signal
    cases = [(True, "cannot maintain shared memory accounting"),
             (False, "cannot publish the command's slot status")]
    for registered, message in cases:
        with tempfile.TemporaryDirectory() as state, tempfile.TemporaryFile(mode="w+") as slot:
            record = {"started_at": 0, "peak_rss_kb": 0, "load_samples": []}
            if registered:
                slot.heavy_job = {"job_id": "job"}
            stderr = io.StringIO()
            with mock.patch.object(heavy.subprocess, "Popen", return_value=mock.Mock(pid=42, returncode=None)), \
                 mock.patch.object(heavy, "visible_group", return_value=42), \
                 mock.patch.object(heavy, "write_status", side_effect=OSError("disk full")), \
                 mock.patch.object(heavy, "group_rss_kb", return_value={42: 1}), \
                 mock.patch.object(heavy, "mem_cap_kb", return_value=100), \
                 mock.patch.object(heavy, "reap_child", return_value=False) as reap, \
                 mock.patch.object(heavy, "kill_group") as kill, \
                 contextlib.redirect_stderr(stderr):
                assert heavy.run_command(slot, ["tiny"], "tiny", record, state, {}, lambda: 0) == 125
                assert stderr.getvalue() == f"heavy: {message}: disk full\n"
                kill.assert_called_once()
                assert kill.call_args.args[0] == 42 and reap.call_args.args[-1] == 0


def test_pid_namespace_jobs():
    # fren-covers: testing::heavy_lease, testing::heavy_memory_victim, testing::heavy_owned_signal
    if heavy.platform.system() != "Linux":
        return
    base = ["unshare", "--user", "--map-root-user", "--pid", "--fork", "--kill-child=KILL"]
    variants = [base + ["--mount-proc", "--"], base + ["--"]]
    supported = []
    for prefix in variants:
        try:
            probe = subprocess.run(prefix + ["true"], capture_output=True, text=True, timeout=10)
            if probe.returncode == 0:
                supported.append(prefix)
        except (OSError, subprocess.TimeoutExpired):
            pass
    if not supported:
        if os.environ.get("HEAVY_REQUIRE_PIDNS_TEST") == "1":
            raise AssertionError("PID namespace integration is required but unshare is unavailable")
        print("heavy: skipped PID namespace integration (kernel/container forbids unshare)")
        return
    for prefix in supported:
        with tempfile.TemporaryDirectory() as state:
            ready = [os.path.join(state, f"ready{i}") for i in range(2)]
            stop = os.path.join(state, "stop")
            worker = ("import pathlib,sys,time; memory=bytearray(int(sys.argv[3])*1024*1024); "
                      "pathlib.Path(sys.argv[1]).write_text('ready'); "
                      "exec('while not pathlib.Path(sys.argv[2]).exists(): time.sleep(0.05)')")
            launcher = ("import runpy,sys; h=runpy.run_path(sys.argv[1]); "
                        "sys.exit(h['main']([sys.executable,'-c',sys.argv[3],*sys.argv[4:]], "
                        "state=sys.argv[2],load_reader=lambda:0))")
            env = dict(os.environ, HEAVY_SLOTS="2", HEAVY_MEM_GB="0.1", HEAVY_MAX_LOAD="off")
            env.pop("HEAVY_LOG", None)
            children = []
            def launch(index, size):
                p = subprocess.Popen(prefix + [sys.executable, "-I", "-B", "-c", launcher,
                                     os.path.join(HERE, "heavy"), state, worker,
                                     ready[index], stop, str(size)], env=env,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, start_new_session=True)
                children.append(p)
                return p
            def await_report():
                deadline = heavy.time.monotonic() + 20
                while heavy.time.monotonic() < deadline:
                    reports = heavy.jobs(state)
                    if (os.path.exists(ready[0]) and reports
                            and all(j["rss_kb"] is not None for j in reports)
                            and heavy.heavy_rss_kb(state) >= 32 * 1024):
                        return reports
                    if children[0].poll() is not None:
                        out, err = children[0].communicate()
                        raise AssertionError(f"namespace job exited early: {out}\n{err}")
                    heavy.time.sleep(0.05)
                raise AssertionError("namespaced job did not publish its memory")
            try:
                oldest = launch(0, 32)
                reports = await_report()
                assert len(reports) == 1 and reports[0]["pid_namespace"] != heavy.pid_namespace()
                newest = launch(1, 64)
                out, err = newest.communicate(timeout=30)
                assert newest.returncode == 137, f"{prefix}: {out}\n{err}"
                assert "over the" in err and oldest.poll() is None
                with open(os.path.join(state, "log.jsonl")) as f:
                    row = [json.loads(line) for line in f][-1]
                assert row["exit_status"] == 137 and row["peak_rss_kb"] < 0.1 * GB
                assert row["job_id"] != reports[0]["job_id"]
                assert row["pid_namespace"] != reports[0]["pid_namespace"]
                assert row["admission_order"] > reports[0]["order"]
                with open(stop, "w") as f:
                    f.write("stop")
                out, err = oldest.communicate(timeout=20)
                assert oldest.returncode == 0, f"{prefix}: {out}\n{err}"
                assert heavy.jobs(state) == []
            finally:
                for p in children:
                    if p.poll() is None:
                        os.killpg(p.pid, signal.SIGKILL)
                    p.communicate(timeout=10)
        print("heavy: PID namespace integration passed " + ("with matching procfs" if "--mount-proc" in prefix
                                                            else "with ancestor procfs"))


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
        assert row["enqueued_max_load"] == 8 and row["wait_policy_changed"] is True


def test_policy_flip_while_waiting():
    with tempfile.TemporaryDirectory() as state:
        clock = [1000]
        environ = {"HEAVY_SLOTS": "1", "HEAVY_MEM_GB": "1"}
        completed = []

        def flip(value):
            heavy.flip_policy(value, state, environ, clock=lambda: clock[0])

        def release(seconds):
            assert seconds == 5 and not completed
            clock[0] += seconds
            flip("off")
            clock[0] += 5

        def finish(f, command, shown, record, state, environ, load_reader):
            assert record["max_load"] == "off" and record["slots"] == 1
            if not completed:
                # The policy can flip again during execution; billing must
                # still use the snapshot taken when the job was admitted.
                assert record["started_at"] == 1010 and record["wait_seconds"] == 10
                clock[0] += 5
                flip(8)
            else:
                clock[0] += 1
            completed.append(True)
            return 0

        flip(8)
        with mock.patch.object(heavy.time, "time", side_effect=lambda: clock[0]), \
             mock.patch.object(heavy.time, "monotonic", side_effect=lambda: clock[0]), \
             mock.patch.object(heavy.time, "sleep", side_effect=release), \
             mock.patch.object(heavy, "heavy_rss_kb", return_value=0), \
             mock.patch.object(heavy, "run_command", side_effect=finish), \
             contextlib.redirect_stderr(io.StringIO()):
            assert heavy.main([sys.executable, "-c", "pass"], state, environ, lambda: 100) == 0
            clock[0] = 1020
            flip("off")
            assert heavy.main([sys.executable, "-c", "pass"], state, environ, lambda: 0) == 0

        with open(os.path.join(state, "log.jsonl")) as f:
            records = [row for line in f if (row := json.loads(line))["event"] == "job"]
        waiting, steady = records
        assert waiting["enqueued_max_load"] == 8 and waiting["max_load"] == "off"
        assert waiting["wait_policy_changed"] is True
        assert steady["enqueued_max_load"] == steady["max_load"] == "off"
        assert steady["wait_policy_changed"] is False
        summary = heavy.stats(1, state, {}, now=1025)
        policies = {p["max_load"]: p for p in summary["policies"]}
        off = policies["off"]
        assert off["jobs"] == 2 and off["wait_jobs"] == off["rate_jobs"] == 1
        assert off["wait_seconds"]["p99"] == 0 and off["latency_seconds"]["p99"] == 1
        assert math.isclose(off["observed_hours"], 15 / 3600)
        assert math.isclose(off["jobs_per_hour"], 240)
        assert summary["rate_jobs"] == 1 and math.isclose(summary["observed_hours"], 25 / 3600)
        assert len(summary["excluded_waits"]) == 1
        excluded = summary["excluded_waits"][0]
        assert excluded["reason"] == "policy_changed_while_waiting"
        assert excluded["max_load"] == "off" and excluded["enqueued_max_load"] == 8


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
        empty = heavy.stats(1, state, {}, now=10000)
        assert empty["jobs"] == 0 and empty["observed_hours"] == 0
        assert empty["rate_jobs"] == 0 and empty["jobs_per_hour"] is None
        record = {"started_at": 9900, "ended_at": 10000, "wait_seconds": 10, "run_seconds": 20,
                  "load_samples": [6, 8], "max_load": "off", "slots": 2,
                  "job_kind": "lake test", "exit_status": 0}
        heavy.append_log(record, state, {})
        heavy.append_log(dict(record, started_at=6390, ended_at=6400,
                              wait_seconds=0, run_seconds=10), state, {})
        heavy.append_log(dict(record, started_at=6389, ended_at=6399), state, {})  # Outside the window.
        heavy.append_log(dict(record, ended_at=10001), state, {})
        for bad in ({"slots": True}, {"max_load": True}, {"load_samples": [False]},
                    {"exit_status": "0"}, {"run_seconds": float("inf")}, {"started_at": None},
                    {"enqueued_at": float("nan")}, {"wait_policy_changed": "false"},
                    {"enqueued_max_load": float("nan"), "enqueued_slots": 2},
                    {"command": []}, {"worktree": 42}):
            # Bypass append_log's finite-number validation to test a damaged log.
            with open(os.path.join(state, "log.jsonl"), "a") as f:
                f.write(json.dumps(dict(record, **bad)) + "\n")
        with open(os.path.join(state, "log.jsonl"), "a") as f:
            f.write('null\n[]\n{}\n{"wait_seconds": NaN}\n{"partial":')
        summary = heavy.stats(1, state, {}, now=10000)
        assert summary["jobs"] == 2 and summary["hours"] == 1
        assert summary["observed_hours"] == 0 and summary["rate_jobs"] == 0
        assert summary["jobs_per_hour"] is None  # No logged exposure at either level.
        assert summary["wait_seconds"]["p50"] == 5
        assert summary["run_seconds"]["p50"] == 15
        assert summary["latency_seconds"]["p50"] == 20
        assert summary["mean_load"] == 7
        assert summary["policies"][0]["jobs_per_hour"] is None  # No exposure log to guess from.
        assert summary["policies"][0]["wait_jobs"] == 0
        assert len(summary["excluded_waits"]) == 2
        assert all(r["reason"] == "wait_policy_unknown" for r in summary["excluded_waits"])
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
        with open(path, "rb") as f:
            before = f.read()

        def partial_then_error(fd, data):
            if os.fstat(fd).st_size == len(before):
                return write(fd, data[:5])
            raise OSError("disk full")

        with mock.patch.object(heavy.os, "write", side_effect=partial_then_error):
            heavy.append_log({"damaged": True}, state, {})
        with open(path, "rb") as f:
            assert f.read() == before  # Keep earlier records, remove the failed append.
        heavy.append_log({"after_error": True}, state, {})
        with open(path) as f:
            assert [json.loads(line) for line in f] == [record, {"next": True}, {"after_error": True}]


def test_policy_comparison():
    with tempfile.TemporaryDirectory() as state:
        # The first flip predates the window. Count its clipped interval,
        # including idle time, not the span from first to last job.
        for at, load in ((1000, 99), (6000, "off"), (9000, 8), (14400, "off"), (15000, 99)):
            heavy.append_log({"event": "policy", "at": at, "max_load": load, "slots": 2}, state, {})

        def job(load, kind, run, slots=2, status=0, ended=10000):
            heavy.append_log({"event": "job", "max_load": load, "slots": slots,
                              "enqueued_max_load": load, "enqueued_slots": slots,
                              "wait_policy_changed": False, "enqueued_at": ended - 3,
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
        assert summary["hours"] == 2 and summary["observed_hours"] == 2
        assert summary["rate_jobs"] == 22 and summary["jobs_per_hour"] == 11
        policies = {(p["max_load"], p["slots"]): p for p in summary["policies"]}
        off, on = policies[("off", 2)], policies[(8, 2)]
        assert off["observed_hours"] == 0.5 and on["observed_hours"] == 1.5
        assert off["jobs_per_hour"] == 20 and on["jobs_per_hour"] == 8
        assert off["rate_jobs"] == 10 and on["rate_jobs"] == 12
        assert off["mean_load"] == 8 and on["mean_load"] == 4
        assert off["run_seconds"]["p50"] == 1 and on["run_seconds"]["p50"] == 100
        assert on["matched_kinds"] == 2 and math.isclose(on["normalized_run_ratio_vs_off"], 0.5)
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
                              "enqueued_max_load": load, "enqueued_slots": 2,
                              "wait_policy_changed": False, "enqueued_at": began,
                              "started_at": began, "ended_at": ended, "exit_status": 0,
                              "job_kind": "lake test", "wait_seconds": 0, "run_seconds": 10,
                              "load_samples": []}, state, {})
        summary = heavy.stats(2, state, {}, now=14400)
        policies = {p["max_load"]: p for p in summary["policies"]}
        assert summary["jobs"] == 9  # Raw counts and timing summaries retain every completion.
        assert summary["hours"] == 2 and summary["observed_hours"] == 1
        assert summary["rate_jobs"] == 4 and summary["jobs_per_hour"] == 4
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


def test_alternate_hangup():
    with tempfile.TemporaryDirectory() as state:
        alternate = heavy.alternate
        flip = heavy.flip_policy
        signals = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        cleaning = []

        def cleanup(value, state, environ, clock):
            if value == "off":
                # Deliver more signals before the file has been removed or
                # the final off record written. None may interrupt cleanup.
                assert heavy.max_load({}, state) == 8
                for sig in signals:
                    signal.raise_signal(sig)
                cleaning.append(True)
            flip(value, state, environ, clock)

        def hangup(seconds):
            assert seconds == 60 and heavy.max_load({}, state) == 8
            signal.raise_signal(signal.SIGHUP)
            raise AssertionError("SIGHUP did not stop the controller")

        def controlled(minutes, value, state, environ):
            alternate(minutes, value, state, environ, sleep=hangup)

        def unexpected(sig, frame):
            # Fail safely instead of terminating the test driver if the
            # controller forgets to replace the inherited signal handlers.
            raise AssertionError("controller did not handle signal")

        previous = {sig: signal.signal(sig, unexpected) for sig in signals}
        try:
            with mock.patch.object(heavy, "alternate", side_effect=controlled), \
                 mock.patch.object(heavy, "flip_policy", side_effect=cleanup):
                assert heavy.main(["--alternate", "1", "8"], state, {}) == 0
            assert all(signal.getsignal(sig) is unexpected for sig in signals)
        finally:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
        assert cleaning == [True]
        assert not os.path.exists(os.path.join(state, "max_load"))
        with open(os.path.join(state, "log.jsonl")) as f:
            flips = [json.loads(line) for line in f]
        assert [r["max_load"] for r in flips] == [8, "off"]


def test_alternate_ignored_hangup():
    with tempfile.TemporaryDirectory() as state:
        alternate = heavy.alternate
        seen = []

        def sleep(seconds):
            seen.append(heavy.max_load({}, state))
            assert signal.getsignal(signal.SIGHUP) is signal.SIG_IGN
            signal.raise_signal(signal.SIGHUP)
            if len(seen) == 2:
                raise KeyboardInterrupt

        def controlled(minutes, value, state, environ):
            alternate(minutes, value, state, environ, sleep=sleep)

        previous = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        try:
            with mock.patch.object(heavy, "alternate", side_effect=controlled):
                assert heavy.main(["--alternate", "1", "8"], state, {}) == 0
            assert signal.getsignal(signal.SIGHUP) is signal.SIG_IGN
        finally:
            signal.signal(signal.SIGHUP, previous)
        assert seen == [8, None]  # The hang-up did not end the on block early.
        assert not os.path.exists(os.path.join(state, "max_load"))
        with open(os.path.join(state, "log.jsonl")) as f:
            assert [json.loads(line)["max_load"] for line in f] == [8, "off", "off"]


def test_registry_signals_and_release():
    # fren-covers: testing::heavy_registry, testing::heavy_lease
    with tempfile.TemporaryDirectory() as state:
        signals = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        delivered = []

        def handler(sig, frame):
            # A handler must run only after the registry is unlocked.
            with open(os.path.join(state, "registry.lock")) as lock:
                heavy.fcntl.flock(lock, heavy.fcntl.LOCK_EX | heavy.fcntl.LOCK_NB)
            delivered.append(sig)

        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, ())
        previous = {sig: signal.signal(sig, handler) for sig in signals}
        try:
            signal.pthread_sigmask(signal.SIG_UNBLOCK, signals)
            for fail in (False, True):
                try:
                    with heavy.registry(state):
                        mask = signal.pthread_sigmask(signal.SIG_BLOCK, ())
                        assert set(signals) <= mask
                        for sig in signals:
                            signal.raise_signal(sig)
                        assert not delivered
                        if fail:
                            raise ValueError("critical section failed")
                except ValueError:
                    assert fail
                assert set(delivered) == set(signals)
                delivered.clear()
                assert not (set(signals) & signal.pthread_sigmask(signal.SIG_BLOCK, ()))
        finally:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)

        slot = open(os.path.join(state, "slot0"), "a+")
        with heavy.registry(state):
            assert heavy.claim_slot(slot, "slot0", state, {"enqueued_at": 0})
        registry = heavy.registry
        observations = []

        @contextlib.contextmanager
        def observe_release(state):
            try:
                with registry(state):
                    yield
            finally:
                # This is exactly the old gap between registry unlock and close.
                with mock.patch.object(heavy, "registry", registry):
                    observations.append((slot.closed, heavy.jobs(state)))

        with mock.patch.object(heavy, "registry", side_effect=observe_release):
            heavy.release_slot(slot, state)
        assert observations == [(True, [])]
        for operation in ("unlink", "truncate"):
            slot = open(os.path.join(state, "slot0"), "a+")
            with registry(state):
                assert heavy.claim_slot(slot, "slot0", state, {"enqueued_at": 0})
            observations.clear()
            target = heavy.os if operation == "unlink" else slot
            with mock.patch.object(heavy, "registry", side_effect=observe_release), \
                 mock.patch.object(target, operation, side_effect=OSError("cleanup failed")):
                heavy.release_slot(slot, state)
            assert observations == [(True, [])]


def test_own_cap_with_other_victim():
    # fren-covers: testing::heavy_owned_signal
    cases = [("older", 101, 101, "its process group uses"),
             ("older", 101, 0, "its process group uses"),  # Shared snapshot is below the cap.
             ("newer", 1, 101, "heavy jobs last reported")]
    for own, rss, reported, reason in cases:
        with tempfile.TemporaryDirectory() as state, tempfile.TemporaryFile(mode="w+") as slot:
            slot.heavy_job = {"job_id": own}
            rows = [{"job_id": "older", "order": 1, "rss_kb": reported},
                    {"job_id": "newer", "order": 2, "rss_kb": 1, "fresh": False}]
            record = {"started_at": 0, "peak_rss_kb": 0, "load_samples": []}
            stderr = io.StringIO()
            with mock.patch.object(heavy.subprocess, "Popen", return_value=mock.Mock(pid=42, returncode=None)), \
                 mock.patch.object(heavy, "visible_group", return_value=42), \
                 mock.patch.object(heavy, "group_rss_kb", return_value={42: rss}), \
                 mock.patch.object(heavy, "publish_memory"), \
                 mock.patch.object(heavy, "jobs", return_value=rows), \
                 mock.patch.object(heavy, "mem_cap_kb", return_value=100), \
                 mock.patch.object(heavy, "reap_child", return_value=False), \
                 mock.patch.object(heavy, "kill_group") as kill, \
                 contextlib.redirect_stderr(stderr):
                assert heavy.run_command(slot, ["tiny"], "tiny", record, state, {}, lambda: 0) == 137
                assert stderr.getvalue().startswith(f"heavy: killed `tiny`: {reason} ")
                assert ("its process group uses" in stderr.getvalue()) == (rss > 100)
                assert ("heavy jobs last reported" in stderr.getvalue()) == (rss <= 100)
                assert kill.call_count == 1


def registry_timeout_paths(state):
    # Run in a separate process so the harness can time out a regression
    # even if one of these calls accidentally uses a blocking flock again.
    before = signal.pthread_sigmask(signal.SIG_BLOCK, ())
    assert raises(lambda: heavy.jobs(state), heavy.RegistryBusy)
    assert raises(lambda: heavy.heavy_rss_kb(state, 100), heavy.RegistryBusy)
    slot = open(os.path.join(state, "slot1"), "a+")
    try:
        slot.heavy_job = {"rss_kb": 0}
        slot.heavy_slot = "slot1"
        assert raises(lambda: heavy.publish_memory(slot, 1, state), heavy.RegistryBusy)
        heavy.release_slot(slot, state)
        assert slot.closed
    finally:
        slot.close()
    # A race after admission's first reading also waits on timeout.
    sleep = heavy.time.sleep

    def admission_sleep(seconds):
        if seconds >= 1:
            raise RuntimeError("admission waited")
        sleep(seconds)

    env = {"HEAVY_SLOTS": "2", "HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "off"}
    with mock.patch.object(heavy, "heavy_rss_kb", return_value=0), \
         mock.patch.object(heavy.time, "sleep", side_effect=admission_sleep), \
         mock.patch.object(heavy, "run", side_effect=AssertionError("admitted without registry")), \
         contextlib.redirect_stderr(io.StringIO()):
        assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state, env), RuntimeError)
    assert signal.pthread_sigmask(signal.SIG_BLOCK, ()) == before


def test_stopped_registry_holder():
    # fren-covers: testing::heavy_registry, testing::heavy_lease, testing::heavy_owned_signal
    if heavy.platform.system() != "Linux":
        return
    with tempfile.TemporaryDirectory() as state:
        ready = os.path.join(state, "monitor-ready")
        go = os.path.join(state, "go")
        locked = os.path.join(state, "locked")
        launcher = """
import pathlib, runpy, sys, time
h = runpy.run_path(sys.argv[1])
publish = h['publish_memory']
def pause(f, rss, state):
    pathlib.Path(sys.argv[3]).touch()
    deadline = time.monotonic() + 15
    while not pathlib.Path(sys.argv[4]).exists():
        if time.monotonic() >= deadline:
            raise ValueError('harness did not release monitor')
        time.sleep(0.01)
    return publish(f, rss, state)
h['run_command'].__globals__['publish_memory'] = pause
sys.exit(h['main']([sys.executable, '-c', 'import time; memory=bytearray(16*1024*1024); time.sleep(30)'],
    state=sys.argv[2], load_reader=lambda: 0))
"""
        holder_code = """
import os, pathlib, runpy, signal, sys
h = runpy.run_path(sys.argv[1])
with h['registry'](sys.argv[2]):
    pathlib.Path(sys.argv[3]).touch()
    os.kill(os.getpid(), signal.SIGSTOP)
"""
        env = dict(os.environ, HEAVY_SLOTS="2", HEAVY_MEM_GB="0.01", HEAVY_MAX_LOAD="off")
        env.pop("HEAVY_LOG", None)
        monitor = subprocess.Popen([sys.executable, "-I", "-B", "-c", launcher,
            os.path.join(HERE, "heavy"), state, ready, go], env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        holder = None

        def await_file(path, child):
            deadline = heavy.time.monotonic() + 10
            while not os.path.exists(path) and child.poll() is None and heavy.time.monotonic() < deadline:
                heavy.time.sleep(0.01)
            assert os.path.exists(path) and child.poll() is None

        try:
            await_file(ready, monitor)
            holder = subprocess.Popen([sys.executable, "-I", "-B", "-c", holder_code,
                os.path.join(HERE, "heavy"), state, locked])
            await_file(locked, holder)
            await_stopped(holder)
            # All registry entry points must return or raise within a deadline.
            probe = "import runpy,sys; h=runpy.run_path(sys.argv[1]); h['registry_timeout_paths'](sys.argv[2])"
            result = subprocess.run([sys.executable, "-I", "-B", "-c", probe,
                os.path.join(HERE, "heavy_test.py"), state], capture_output=True, text=True, timeout=5)
            assert result.returncode == 0, (result.stdout, result.stderr)
            with open(go, "w") as f:
                f.write("go")
            out, err = monitor.communicate(timeout=5)
            assert monitor.returncode == 137, (out, err)
            assert "heavy: killed" in err
            # The stopped holder remains stopped throughout that decision.
            assert child_stopped(holder.pid)
        finally:
            if holder is not None and holder.poll() is None:
                os.kill(holder.pid, signal.SIGCONT)
                holder.wait(timeout=5)
            with open(go, "w") as f:
                f.write("go")
            if monitor.poll() is None:
                monitor.terminate()
            monitor.communicate(timeout=15)


def test_report_clock():
    # fren-covers: testing::heavy_lease, testing::heavy_memory_victim
    with tempfile.TemporaryDirectory() as state:
        slot = open(os.path.join(state, "slot0"), "a+")
        try:
            with heavy.registry(state):
                assert heavy.claim_slot(slot, "slot0", state, {"enqueued_at": 0})
            heavy.publish_memory(slot, 40, state)
            verified = slot_monitor(state, "slot0") is not None
            stamp = slot.heavy_job["updated_monotonic"]
            with mock.patch.object(heavy.time, "time", return_value=10**12), \
                 mock.patch.object(heavy.time, "monotonic", return_value=stamp + 1):
                assert heavy.jobs(state)[0]["fresh"]
                assert heavy.heavy_rss_kb(state, 80) == 40
            for now in (stamp - 1, stamp + heavy.REPORT_STALE_SECONDS + 1):
                with mock.patch.object(heavy.time, "monotonic", return_value=now):
                    row = heavy.jobs(state)[0]
                    assert not row["fresh"]
                    assert row["legacy"] == (not verified)
                    if row.get("legacy"):
                        # Without visible kernel ownership, stale status cannot
                        # distinguish a stopped monitor from a legacy successor.
                        assert row["rss_kb"] is None
                        assert heavy.heavy_rss_kb(state, 80) == 40
                        assert heavy.memory_victim([row], 80) == (0, None)
                    else:
                        assert row["rss_kb"] == 40
                        assert heavy.heavy_rss_kb(state, 80) == 80
                        assert heavy.memory_victim([row], 80) == (40, None)
        finally:
            heavy.release_slot(slot, state)


def test_stopped_owner():
    # fren-covers: testing::heavy_lease, testing::heavy_memory_victim, testing::heavy_owned_signal
    if heavy.platform.system() != "Linux":
        return
    with tempfile.TemporaryDirectory() as state:
        stop = os.path.join(state, "stop")
        ready = [os.path.join(state, f"ready{i}") for i in range(2)]
        worker = ("import pathlib,sys,time; memory=bytearray(4*1024*1024); "
                  "pathlib.Path(sys.argv[1]).write_text('ready'); "
                  "exec('while not pathlib.Path(sys.argv[2]).exists(): time.sleep(0.05)')")
        launcher = ("import runpy,sys; h=runpy.run_path(sys.argv[1]); "
                    "sys.exit(h['main']([sys.executable,'-c',sys.argv[3],*sys.argv[4:]], "
                    "state=sys.argv[2],load_reader=lambda:0))")
        env = dict(os.environ, HEAVY_SLOTS="2", HEAVY_MEM_GB="0.5", HEAVY_MAX_LOAD="off")
        env.pop("HEAVY_LOG", None)
        children = []
        try:
            for index in range(2):
                child = subprocess.Popen([sys.executable, "-I", "-B", "-c", launcher,
                    os.path.join(HERE, "heavy"), state, worker, ready[index], stop],
                    env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                children.append(child)
                deadline = heavy.time.monotonic() + 15
                while not os.path.exists(ready[index]) and child.poll() is None and heavy.time.monotonic() < deadline:
                    heavy.time.sleep(0.05)
                assert os.path.exists(ready[index]) and child.poll() is None
            # Stop only our older monitor. Its command remains alive in its
            # own process group, as with terminal job control.
            with heavy.registry(state):
                # Stop outside the child's critical section so reading the
                # stale report below does not contend with a stopped holder.
                os.kill(children[0].pid, signal.SIGSTOP)
                await_stopped(children[0])
            deadline = heavy.time.monotonic() + heavy.REPORT_STALE_SECONDS + 2
            while heavy.time.monotonic() < deadline:
                assert children[1].poll() is None, children[1].communicate()
                heavy.time.sleep(0.1)
            # Wait for a publication by the running monitor, not for a fixed
            # scheduler budget after the older report becomes stale.
            deadline = heavy.time.monotonic() + 15
            while heavy.time.monotonic() < deadline:
                reports = heavy.jobs(state)
                if len(reports) == 2 and sum(not r["fresh"] for r in reports) == 1:
                    break
                assert children[1].poll() is None, children[1].communicate()
                heavy.time.sleep(0.05)
            assert len(reports) == 2 and sum(not r["fresh"] for r in reports) == 1
            cap = int(0.5 * GB)
            stale = next(r for r in reports if not r["fresh"])
            verified = slot_monitor(state, "slot0") is not None
            assert stale["legacy"] == (not verified)
            with mock.patch.object(heavy, "jobs", return_value=reports):
                charge = heavy.heavy_rss_kb(state, cap)
            if verified:
                assert charge > 0.6 * cap and stale["rss_kb"] is not None
            else:
                assert 0 < charge <= 0.6 * cap and stale["rss_kb"] is None
            total, victim = heavy.memory_victim(reports, cap)
            assert total < cap and victim is None
            os.kill(children[0].pid, signal.SIGCONT)
            with open(stop, "w") as f:
                f.write("stop")
            for child in children:
                out, err = child.communicate(timeout=15)
                assert child.returncode == 0, (out, err)
        finally:
            if children and children[0].poll() is None:
                os.kill(children[0].pid, signal.SIGCONT)
            with open(stop, "w") as f:
                f.write("stop")
            for child in children:
                if child.poll() is None:
                    child.terminate()
                child.communicate(timeout=15)


def test_unverified_owners():
    # fren-covers: testing::heavy_lease, testing::heavy_memory_victim
    # Exercise the filesystem/visibility fallback on every host, including
    # hosts whose normal scratch directory supports kernel verification.
    with mock.patch.object(heavy, "flock_owners", return_value={}):
        test_slot_identity()
        test_legacy_report_reuse()
        test_report_clock()
        test_stopped_owner()
    print("heavy: lease tests passed with kernel lock owners hidden")


def test_cpu_ticks():
    # fren-covers: testing::heavy_busy
    with tempfile.TemporaryDirectory() as state:
        path = os.path.join(state, "stat")
        assert heavy.cpu_ticks(path) is None
        for line, expected in (
                ("cpu 10 20 30 40 50 60 70 80 900 1000\ncpu0 1 2 3 4\n",
                 (10, 20, 30, 40, 50, 60, 70, 80)),  # Guest must not count twice.
                ("cpu 1 2 3 4\n", (1, 2, 3, 4, 0, 0, 0, 0)),
                ("cpu 1 2 3 4 5\n", (1, 2, 3, 4, 5, 0, 0, 0)),
                ("cpu0 1 2 3 4\n", None), ("cpu 1 2 3\n", None),
                ("cpu 1 2 3 -4\n", None), ("cpu 1 2 nope 4\n", None), ("", None)):
            with open(path, "w") as f:
                f.write(line)
            assert heavy.cpu_ticks(path) == expected, line
        with open(path, "wb") as f:
            f.write(b"cpu 1 2 3 \xff\n")
        assert heavy.cpu_ticks(path) is None
        assert heavy.cpu_ticks(state) is None  # Unreadable / unavailable is non-fatal.


def test_cpu_samples():
    # fren-covers: testing::heavy_busy, testing::heavy_cpu
    zero = (0,) * 8
    first = (10, 5, 15, 40, 10, 5, 5, 10)  # 50 busy of 100; idle/iowait excluded.
    second = (90, 15, 65, 50, 20, 15, 15, 30)  # 180 busy of the next 200.
    assert heavy.cpu_interval(zero, first) == {"busy_ticks": 50, "total_ticks": 100}
    assert heavy.cpu_interval(None, first) is None
    assert heavy.cpu_interval(first, None) is None
    assert heavy.cpu_interval(first, first) is None
    for i in range(8):
        reset = list(second)
        reset[i] = first[i] - 1
        assert heavy.cpu_interval(first, reset) is None
    readings = iter([zero, first, second])
    record = {"cpu_busy_samples": [], "cpu_user_seconds": 3.5,
              "cpu_system_seconds": 1.5, "run_seconds": 2, "peak_rss_kb": 0}
    sample = lambda now, last=None, final=False: heavy.sample_cpu(
        record, now, last, final, lambda: next(readings))
    last = sample(0)
    assert sample(29.99, last) is last
    last = sample(30, last)
    assert sample(30.99, last) is last
    sample(31, last, final=True)  # Final interval counts even below the cadence.
    heavy.cpu_summary(record)
    assert len(record["cpu_busy_samples"]) == 2
    assert record["cpu_busy_mean"] == 230 / 300  # Weighted by ticks, not sample count.
    assert record["cpu_busy_max"] == 0.9
    assert record["cpu_seconds"] == 5 and record["cpu_parallelism"] == 2.5
    record.update(cpu_busy_samples=[], run_seconds=0)
    heavy.cpu_summary(record)
    assert record["cpu_busy_mean"] is record["cpu_busy_max"] is record["cpu_parallelism"] is None
    # Missing readings and counter resets discard only their adjacent intervals.
    for readings in ([zero, None, first, second], [second, zero, first]):
        record["cpu_busy_samples"] = []
        last = None
        for i, ticks in enumerate(readings):
            last = heavy.sample_cpu(record, i * 30, last, reader=lambda: ticks)
        assert len(record["cpu_busy_samples"]) == 1
    with tempfile.TemporaryDirectory() as state, \
         tempfile.TemporaryFile(mode="w+") as slot, \
         mock.patch.object(heavy, "cpu_ticks", return_value=None), \
         mock.patch.object(heavy.subprocess, "Popen", side_effect=OSError(2, "missing")), \
         contextlib.redirect_stderr(io.StringIO()):
        record = {"started_at": 0}
        assert heavy.run(slot, ["missing"], "missing", "missing", record,
                         heavy.time.monotonic(), state, {}, lambda: None) == 127
        with open(os.path.join(state, "log.jsonl")) as f:
            row = json.loads(f.read())
        assert row["cpu_busy_samples"] == []
        assert row["cpu_busy_mean"] is row["cpu_busy_max"] is None
        assert row["cpu_seconds"] == 0 and row["exit_status"] == 127


def test_cpu_monitor():
    # fren-covers: testing::heavy_cpu, testing::heavy_busy
    record = {"started_at": 0, "peak_rss_kb": 0, "load_samples": [],
              "cpu_busy_samples": [], "cpu_user_seconds": 0, "cpu_system_seconds": 0}
    child = SimpleNamespace(pid=42, returncode=None)
    usage = SimpleNamespace(ru_utime=2.5, ru_stime=1.25, ru_maxrss=100, ru_nivcsw=6)
    clock = [0]

    def sleep(seconds):
        clock[0] += 30

    with tempfile.TemporaryDirectory() as state, \
         tempfile.TemporaryFile(mode="w+") as slot, \
         mock.patch.object(heavy.subprocess, "Popen", return_value=child), \
         mock.patch.object(heavy.os, "wait4", side_effect=[(0, 0, None)] * 3 + [(42, 7 << 8, usage)]), \
         mock.patch.object(heavy.time, "monotonic", side_effect=lambda: clock[0]), \
         mock.patch.object(heavy.time, "sleep", side_effect=sleep), \
         mock.patch.object(heavy, "cpu_ticks", side_effect=[
             (0,) * 8, (10, 0, 0, 10, 0, 0, 0, 0),
             (30, 0, 0, 10, 0, 0, 0, 0), (30, 0, 0, 30, 0, 0, 0, 0)]), \
         mock.patch.object(heavy, "group_rss_kb", return_value={}), \
         mock.patch.object(heavy, "group_processes", return_value=[]), \
         mock.patch.object(heavy, "visible_group", return_value=42), \
         mock.patch.object(heavy, "machine_counters", return_value={}), \
         mock.patch.object(heavy, "mem_cap_kb", return_value=GB), \
         mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()), \
         mock.patch.object(heavy.signal, "signal"):
        assert heavy.monitor_command(slot, ["tiny"], "tiny", record, state, {}, lambda: 0.5, False) == 7
    assert record["cpu_busy_samples"] == [
        {"busy_ticks": 10, "total_ticks": 20},
        {"busy_ticks": 20, "total_ticks": 20},
        {"busy_ticks": 0, "total_ticks": 20}]
    record["run_seconds"] = 90
    heavy.cpu_summary(record)
    assert record["cpu_busy_mean"] == 0.5 and record["cpu_busy_max"] == 1
    assert record["cpu_user_seconds"] == 2.5 and record["cpu_system_seconds"] == 1.25
    assert record["cpu_scope"] == "waited_tree"
    assert record["involuntary_context_switches"] == 6
    # Rechecking an already-reaped child must not count it again.
    assert heavy.reap_child(child, record)
    assert record["cpu_seconds"] == 3.75


def test_monitor_group_completion():
    # fren-covers: testing::heavy_group_gone
    for subreaper, readings, expected_pids, returncode, status in (
            (False, [{"pid": 143}, {"pid": 144}], "143, 144", 7, 7),
            (True, [{"pid": 143}, {"pid": 144}], "143, 144", 7, 7),
            (True, None, "unavailable", 7, 7), (False, [], "none sampled", 7, 7),
            (True, [{"pid": 143}, {"pid": 144}], "143, 144", -9, 137),
            (False, [{"pid": 143}, {"pid": 144}], "143, 144", -15, 143)):
        record = {"started_at": 0, "peak_rss_kb": 0, "load_samples": []}
        child = SimpleNamespace(pid=42, returncode=returncode)
        clock = [0]
        def sleep(seconds):
            assert seconds == 1
            clock[0] += 1
        stderr = io.StringIO()
        with tempfile.TemporaryDirectory() as state, \
             tempfile.TemporaryFile(mode="w+") as slot, \
             contextlib.redirect_stderr(stderr), \
             mock.patch.object(heavy.subprocess, "Popen", return_value=child), \
             mock.patch.object(heavy, "reap_child", return_value=True), \
             mock.patch.multiple(heavy, visible_group=mock.Mock(return_value=142),
                                 group_processes=mock.Mock(return_value=readings),
                                 machine_counters=mock.Mock(return_value={}),
                                 cpu_ticks=mock.Mock(return_value=None)), \
             mock.patch.object(heavy.ProcessSampler, "sample"), \
             mock.patch.object(heavy, "group_rss_kb", return_value={142: 10}), \
             mock.patch.object(heavy, "jobs", return_value=[]), \
             mock.patch.object(heavy, "publish_memory") as publish, \
             mock.patch.object(heavy, "mem_cap_kb", return_value=100), \
             mock.patch.object(heavy.os, "getpid", return_value=2), \
             mock.patch.object(heavy.os, "killpg", side_effect=[None] * 32 + [ProcessLookupError()]) as probe, \
             mock.patch.object(heavy.time, "monotonic", side_effect=lambda: clock[0]), \
             mock.patch.object(heavy.time, "sleep", side_effect=sleep), \
             mock.patch.object(heavy.signal, "signal"), \
             mock.patch.object(heavy, "kill_group", side_effect=AssertionError("normal completion signaled")):
            assert heavy.monitor_command(slot, ["tiny"], "tiny", record, state, {}, lambda: 0, subreaper) == status
            # Keep accounting/holding the slot while the original group lives;
            # identify the actual procfs view and throttle diagnostics to 30 s.
            assert probe.call_args_list == [mock.call(42, 0)] * 33
            assert publish.call_args_list == [mock.call(slot, 10, state)] * 32
            assert record["peak_rss_kb"] == 10
        lines = stderr.getvalue().splitlines()
        assert len(lines) == 2, lines
        assert all(f"leader exited with {status}" in line and "holding slot" in line
                   and "42 (namespace-local PGID)" in line
                   and f"remaining procfs-view PIDs: {expected_pids}" in line for line in lines), lines


def test_cpu_descendants():
    # fren-covers: testing::heavy_cpu
    worker = ("import json,os,resource,time; start=time.process_time(); "
              "exec('while time.process_time()-start < 0.3: os.stat(\"/dev/null\")'); "
              "u=resource.getrusage(resource.RUSAGE_SELF); "
              "print(json.dumps([u.ru_utime,u.ru_stime]),flush=True)")
    commands = [f"ps=[subprocess.Popen([sys.executable,'-c',{worker!r}]) for _ in range(2)]; "
                "assert all(p.wait()==0 for p in ps)"]
    if heavy.platform.system() == "Linux":
        # An orphan stays in the job's group. Count it even when the leader
        # exits first, or dies from a signal, without changing the leader's status.
        with heavy.child_subreaper() as enabled:
            assert enabled
        commands.extend([
            f"subprocess.Popen([sys.executable,'-c',{worker!r}]); raise SystemExit(7)",
            f"subprocess.Popen([sys.executable,'-c',{worker!r}]); os.kill(os.getpid(),signal.SIGTERM)"])
    with tempfile.TemporaryDirectory() as state:
        for body, status in zip(commands, (0, 7, 143)):
            command = "import os,signal,subprocess,sys; " + body
            result = tiny_job(state, [sys.executable, "-c", command])
            assert result.returncode == status, result.stderr
            readings = [json.loads(line) for line in result.stdout.splitlines()]
            user, system = (sum(r[i] for r in readings) for i in range(2))
            with open(os.path.join(state, "log.jsonl")) as f:
                row = [json.loads(line) for line in f][-1]
            assert user + system >= 0.3
            assert row["cpu_user_seconds"] >= user and row["cpu_system_seconds"] >= system
            if heavy.platform.system() == "Linux":
                assert row["cpu_scope"] == "process_group"
            # Parent/interpreter shutdown adds a little CPU; the descendant
            # must be counted once, rather than once directly and again in its parent.
            assert row["cpu_seconds"] < 2 * (user + system)


def test_cpu_reaping():
    # fren-covers: testing::heavy_cpu, testing::heavy_group_gone
    record = {"peak_rss_kb": 0, "cpu_user_seconds": 0, "cpu_system_seconds": 0,
              "cpu_busy_samples": [], "run_seconds": 2}
    child = SimpleNamespace(pid=42, returncode=None, heavy_subreaper=True)
    leader = SimpleNamespace(ru_utime=2, ru_stime=1, ru_maxrss=204800, ru_nivcsw=7)
    worker = SimpleNamespace(ru_utime=3, ru_stime=4, ru_maxrss=102400, ru_nivcsw=11)
    calls = [0]

    def wait(pid, flags):
        assert pid == -42 and flags == os.WNOHANG
        calls[0] += 1
        if calls[0] == 1:
            # Simulate a signal handler reaping another process after the
            # outer wait4 has succeeded but before its caller stores usage.
            assert not heavy.reap_child(child, record)
            return 42, 7 << 8, leader
        if calls[0] == 2:
            return 43, 9 << 8, worker
        raise ChildProcessError

    with mock.patch.object(heavy.os, "wait4", side_effect=wait), \
         mock.patch.object(heavy.platform, "system", return_value="Linux"):
        assert heavy.reap_child(child, record)
        assert heavy.reap_child(child, record)
    heavy.cpu_summary(record)
    assert child.returncode == 7  # A worker's status never replaces the command's.
    assert record["cpu_user_seconds"] == record["cpu_system_seconds"] == 5
    assert record["cpu_seconds"] == 10 and record["cpu_parallelism"] == 5
    assert record["peak_rss_kb"] == 204800 and "_cpu_usage" not in record
    assert record["involuntary_context_switches"] == 18
    heavy.cpu_summary(record)
    assert record["involuntary_context_switches"] == 18 and record["cpu_seconds"] == 10


def test_child_subreaper():
    def prctl(op, value, *unused):
        if op == 37:
            value._obj.value = 1  # Preserve an already-enabled setting too.
        return 0

    with mock.patch.object(heavy.platform, "system", return_value="Linux"), \
         mock.patch.object(heavy.ctypes, "CDLL") as libc:
        libc.return_value.prctl.side_effect = prctl
        with heavy.child_subreaper() as enabled:
            assert enabled
        assert [call.args[:2] for call in libc.return_value.prctl.call_args_list][1:] == [(36, 1), (36, 1)]
        libc.return_value.prctl.reset_mock(side_effect=True)
        libc.return_value.prctl.return_value = -1
        with heavy.child_subreaper() as enabled:
            assert not enabled
        assert libc.return_value.prctl.call_count == 1
        libc.return_value.prctl.reset_mock()
        libc.return_value.prctl.side_effect = [0, -1]  # GET works; SET is refused.
        with heavy.child_subreaper() as enabled:
            assert not enabled
        assert libc.return_value.prctl.call_count == 2
    with mock.patch.object(heavy.platform, "system", return_value="Darwin"), \
         mock.patch.object(heavy.ctypes, "CDLL", side_effect=AssertionError("not Linux")):
        with heavy.child_subreaper() as enabled:
            assert not enabled


def test_cpu_many_waits():
    # fren-covers: testing::heavy_cpu
    record = {"peak_rss_kb": 0, "cpu_user_seconds": 0, "cpu_system_seconds": 0,
              "cpu_busy_samples": [], "run_seconds": 10}
    child = SimpleNamespace(pid=42, returncode=None, heavy_subreaper=True)
    usage = SimpleNamespace(ru_utime=0.25, ru_stime=0.5, ru_maxrss=100, ru_nivcsw=3)
    count = [0]
    def wait(pid, flags):
        assert pid == -42 and flags == os.WNOHANG
        assert len(repr(record)) < 500
        if count[0] == 4000:
            raise ChildProcessError
        count[0] += 1
        return (42 if count[0] == 1 else 42 + count[0]), 0, usage
    with mock.patch.object(heavy.os, "wait4", side_effect=wait), \
         mock.patch.object(heavy.platform, "system", return_value="Linux"):
        assert heavy.reap_child(child, record)
    heavy.cpu_summary(record)
    assert record["cpu_user_seconds"] == 1000 and record["cpu_system_seconds"] == 2000
    assert record["cpu_seconds"] == 3000 and record["involuntary_context_switches"] == 12000
    assert record["peak_rss_kb"] == 100


def test_cpu_signal_fold():
    # fren-covers: testing::heavy_cpu
    handled = {signal.SIGINT, signal.SIGTERM, signal.SIGHUP}
    for sig in handled:
        record = {"peak_rss_kb": 0, "cpu_user_seconds": 0, "cpu_system_seconds": 0,
                  "cpu_busy_samples": [], "run_seconds": 2}
        child = SimpleNamespace(pid=42, returncode=None, heavy_subreaper=True)
        sent, observed = [], []
        class LeaderUsage:
            ru_stime, ru_maxrss, ru_nivcsw = 1, 100, 7
            @property
            def ru_utime(self):
                # Interrupt after the old aggregate is read, before the
                # replacement is stored: the signal must wait for that store.
                if not sent:
                    sent.append(sig)
                    os.kill(os.getpid(), sig)
                return 2
        worker = SimpleNamespace(ru_utime=3, ru_stime=4, ru_maxrss=200, ru_nivcsw=11)
        results = iter([(42, 7 << 8, LeaderUsage()), (43, 0, worker)])
        def wait(pid, flags):
            # Exercise the blocking cleanup path too, with no new signal mask.
            assert flags == 0 and handled.isdisjoint(signal.pthread_sigmask(signal.SIG_BLOCK, []))
            try:
                return next(results)
            except StopIteration:
                raise ChildProcessError from None
        def on_signal(signo, frame):
            observed.append(record.get("_cpu_usage"))
            assert heavy.reap_child(child, record, 0)
        previous_handler = signal.signal(sig, on_signal)
        previous_mask = signal.pthread_sigmask(signal.SIG_UNBLOCK, handled)
        try:
            with mock.patch.object(heavy.os, "wait4", side_effect=wait), \
                 mock.patch.object(heavy.platform, "system", return_value="Linux"):
                assert heavy.reap_child(child, record, 0)
        finally:
            signal.signal(sig, previous_handler)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        assert sent == [sig] and observed == [(2, 1, 100, 7)]
        heavy.cpu_summary(record)
        assert child.returncode == 7
        assert record["cpu_user_seconds"] == record["cpu_system_seconds"] == 5
        assert record["peak_rss_kb"] == 200 and record["involuntary_context_switches"] == 18


def test_process_readings():
    # fren-covers: testing::heavy_counter_rate
    row = heavy.process_stat(proc_line(name="a ) b ( c"))
    assert row["comm"] == "a ) b ( c" and row["ticks"] == 30
    assert row["pid"] == 123 and row["pgrp"] == 7 and row["start"] == 100
    for text in ("", "123 (short) R", proc_line(user=-1)):
        assert raises(lambda: heavy.process_stat(text), (ValueError, IndexError))
    assert heavy.process_switches("voluntary_ctxt_switches: 99\nnonvoluntary_ctxt_switches: 7\n") == 7
    assert heavy.process_switches("nonvoluntary_ctxt_switches: -1\n") is None
    assert heavy.process_switches("voluntary_ctxt_switches: 99\n") is None
    with tempfile.TemporaryDirectory() as proc:
        for pid, group in ((123, 7), (124, 8)):
            path = os.path.join(proc, str(pid))
            os.mkdir(path)
            with open(os.path.join(path, "stat"), "w") as f:
                f.write(proc_line(pid=pid, group=group, name="fren_fuzz_front"))
            with open(os.path.join(path, "status"), "w") as f:
                f.write("nonvoluntary_ctxt_switches: 7\n")
            os.symlink("/nix/store/example/bin/fren_fuzz_frontends", os.path.join(path, "exe"))
        live = set()
        readings = heavy.group_processes(7, proc, live)
        assert len(readings) == 1
        assert live == {(123, 100), (124, 100)}  # Includes the other group.
        assert readings[0]["name"] == "fren_fuzz_frontends" and readings[0]["switches"] == 7
        rss = heavy.group_rss_kb(proc, "Linux")
        assert rss[7] == rss[8] == 3 * os.sysconf("SC_PAGE_SIZE") // 1024
        os.unlink(os.path.join(proc, "123", "exe"))
        assert heavy.group_processes(7, proc)[0]["name"] is None
        # A PID reused between the two stat reads must not mix identities.
        with mock.patch.object(heavy.os, "listdir", return_value=["123"]), \
             mock.patch.object(heavy, "process_stat", side_effect=[row, dict(row, start=101)]):
            assert heavy.group_processes(7, proc) == []
        assert heavy.group_processes(7, os.path.join(proc, "missing")) is None


def process_row(pid, name, ticks, switches=0, start=10000, state="R"):
    return {"pid": pid, "name": name, "comm": (name or "unknown")[:15],
            "ticks": ticks, "switches": switches, "start": start, "state": state}


def test_process_sampling():
    # fren-covers: testing::heavy_counter_rate
    sampler = heavy.ProcessSampler(100, 100)
    sampler.sample(101, 101, [process_row(1, "lean", 100, 5),
                              process_row(2, "lean", 50, 1, start=10050),
                              process_row(3, "cvc5", 200, 3)])
    sampler.sample(102, 102, [process_row(1, "lean", 200, 8),
                              process_row(2, "lean", 150, 2, start=10050),
                              process_row(3, "cvc5", 400, 6)])
    record = {}
    sampler.finish(record)
    lean, solver = record["process_cpu"]["lean"], record["process_cpu"]["cvc5"]
    assert lean["core_seconds"] == lean["observed_process_seconds"] == 3.5
    assert lean["mean_cores_per_process"] == lean["peak_cores_per_process"] == 1
    assert lean["peak_process_count"] == lean["processes_seen"] == 2
    assert solver["core_seconds"] == 4 and solver["mean_cores_per_process"] == 2
    assert solver["peak_cores_per_process"] == 2 and solver["peak_process_count"] == 1
    assert record["nonvoluntary_ctxt_switches"] == 16
    # PID reuse is a new lifetime; absent workers add no CPU or concurrency.
    sampler.sample(103, 103, [process_row(1, "lean", 50, 4, start=10200)])
    sampler.finish(record)
    assert lean["core_seconds"] == 4 and lean["processes_seen"] == 3
    assert lean["peak_process_count"] == 2 and record["nonvoluntary_ctxt_switches"] == 20
    # exec preserves counters but changes attribution; a missing exe link
    # on the next (zombie) reading must retain the full cached executable.
    sampler.sample(104, 104, [process_row(1, "fren_fuzz_frontends", 150, 7, start=10200)])
    sampler.sample(105, 105, [dict(process_row(1, None, 200, 9, start=10200, state="Z"),
                                  comm="fren_fuzz_front")])
    sampler.finish(record)
    fuzz = record["process_cpu"]["fren_fuzz_frontends"]
    assert fuzz["core_seconds"] == 1.5 and fuzz["processes_seen"] == fuzz["peak_process_count"] == 1
    assert record["nonvoluntary_ctxt_switches"] == 25
    empty = heavy.ProcessSampler(0, 100)
    empty.sample(1, 1, None)
    empty.finish(record)
    assert record["process_cpu"] is record["nonvoluntary_ctxt_switches"] is None
    # A missing scan contributes known lifetime CPU when the process returns,
    # but cannot inflate the rate by adding that CPU to a shorter time window.
    gap = heavy.ProcessSampler(0, 100)
    gap.sample(1, 1, [process_row(1, "lean", 100, None, start=0)])
    gap.sample(2, 2, None)
    gap.sample(3, 3, [process_row(1, "lean", 300, 5, start=0)])
    gap.sample(4, 4, [process_row(1, "lean", 400, None, start=0)])
    gap.sample(5, 5, [process_row(1, "lean", 500, 8, start=0)])
    gap.finish(record)
    data = record["process_cpu"]["lean"]
    assert data["core_seconds"] == 5 and data["observed_core_seconds"] == 3
    assert data["observed_process_seconds"] == 3 and data["mean_cores_per_process"] == 1
    assert record["nonvoluntary_ctxt_switches"] == 8
    gap.sample(6, 6, [process_row(1, "lean", 10, 2, start=0)])
    gap.finish(record)
    assert data["core_seconds"] == 5 and record["nonvoluntary_ctxt_switches"] == 8
    renamed = heavy.ProcessSampler(0, 100)
    for i, name in enumerate(("lean", "lake", "lean"), 1):
        renamed.sample(i, i, [process_row(1, name, i * 100, start=0)])
    renamed.finish(record)
    assert record["process_cpu"]["lean"]["processes_seen"] == 1
    assert record["process_cpu"]["lean"]["core_seconds"] == 2
    exited = heavy.ProcessSampler(0, 100)
    exited.sample(1, 1, [process_row(1, "lake", 100, start=0)])
    exited.sample(2, 2, [dict(process_row(1, None, 200, start=0, state="Z"), comm="lean")])
    exited.finish(record)
    assert record["process_cpu"]["lake"]["core_seconds"] == 1
    assert record["process_cpu"]["lean"]["core_seconds"] == 1


def test_process_lifetime_retention():
    # fren-covers: testing::heavy_counter_rate
    sampler = heavy.ProcessSampler(0, 100)
    for i in range(1, 4001):
        sampler.sample(i, i, [process_row(i, "lean", 100, 2, start=i * 100 - 50)])
        assert len(sampler.previous) == 1
        assert len(repr(sampler.__dict__)) < 2000
    record = {}
    sampler.finish(record)
    data = record["process_cpu"]["lean"]
    assert data["processes_seen"] == 4000
    assert data["core_seconds"] == 4000
    assert record["nonvoluntary_ctxt_switches"] == 8000
    sampler.sample(4001, 4001, [])
    assert sampler.previous == {}
    sampler.finish(record)
    assert data["processes_seen"] == 4000 and data["core_seconds"] == 4000


def test_process_group_reentry():
    # fren-covers: testing::heavy_counter_rate
    sampler = heavy.ProcessSampler(0, 100)
    identity = (7, 0)
    sampler.sample(1, 1, [process_row(7, "lean", 100, 10, start=0)], {identity})
    sampler.sample(2, 2, [], {identity})  # Alive in another process group.
    assert len(sampler.previous) == 1
    sampler.sample(3, 3, [process_row(7, "lean", 300, 30, start=0)], {identity})
    sampler.sample(4, 4, [process_row(7, "lean", 400, 40, start=0)], {identity})
    record = {}
    sampler.finish(record)
    data = record["process_cpu"]["lean"]
    assert data["core_seconds"] == 4 and data["processes_seen"] == 1
    assert data["observed_core_seconds"] == data["observed_process_seconds"] == 2
    assert record["nonvoluntary_ctxt_switches"] == 40
    sampler.sample(5, 5, [], set())  # The lifetime really ended.
    assert sampler.previous == {}


def test_machine_pressure():
    # fren-covers: testing::heavy_pressure, testing::heavy_counter_rate
    with tempfile.TemporaryDirectory() as proc:
        path = os.path.join(proc, "stat")
        with open(path, "w") as f:
            f.write("cpu 0 0 0 0\ncpu0 0 0 0 0\ncpu1 0 0 0 0\n"
                    "ctxt 1000\nprocs_running 8\nprocs_blocked 99\n")
        assert heavy.machine_counters(path) == {"cpu_cores": 2, "ctxt": 1000, "procs_running": 8}
        with open(path, "w") as f:
            f.write("cpu0 0 0 0 0\nctxt -1\nprocs_running nope\n")
        assert heavy.machine_counters(path) == {"cpu_cores": 1}
        assert heavy.machine_counters(proc) == {}
    sampler = heavy.MachineSampler()
    sampler.sample(0, {"cpu_cores": 4, "procs_running": 8, "ctxt": 100})
    sampler.sample(1, {"cpu_cores": 2, "procs_running": 2, "ctxt": 300})
    sampler.sample(3, {"cpu_cores": 2, "procs_running": 0, "ctxt": 500})
    record = {}
    sampler.finish(record)
    assert record["procs_running_mean"] == 10 / 3 and record["procs_running_max"] == 8
    assert record["runnable_per_core_mean"] == 1 and record["runnable_per_core_max"] == 2
    assert record["oversubscribed_fraction"] == 1 / 3  # Equality is not oversubscription.
    assert record["ctxt_per_second_mean"] == 400 / 3 and record["ctxt_per_second_max"] == 200
    assert record["procs_running_sample_count"] == 3
    assert record["ctxt_rate_sample_count"] == 2
    assert record["ctxt_switches"] == 400 and record["ctxt_observed_seconds"] == 3
    # Thousands of seconds must not grow retained state or the logged record.
    for now in range(4, 4004):
        sampler.sample(now, {"cpu_cores": 2, "procs_running": 2, "ctxt": 500 + now})
    long_record = {}
    sampler.finish(long_record)
    assert long_record["procs_running_sample_count"] == 4003
    assert long_record["ctxt_rate_sample_count"] == 4002
    assert long_record.keys() == record.keys()
    assert all(not isinstance(v, (list, dict)) for v in vars(sampler).values())
    assert len(json.dumps(long_record)) < 800
    assert "procs_running_samples" not in long_record and "ctxt_rate_samples" not in long_record
    gap = heavy.MachineSampler()
    for now, reading in enumerate(({"ctxt": 100}, {}, {"ctxt": 500}, {"ctxt": 400}, {"ctxt": 700})):
        gap.sample(now, reading)
    gap.finish(record)
    assert record["ctxt_per_second_mean"] == record["ctxt_per_second_max"] == 300
    assert record["oversubscribed_fraction"] is record["procs_running_mean"] is None
    gap.sample(5, {"cpu_cores": 0, "procs_running": 100})
    gap.finish(record)
    assert record["procs_running_sample_count"] == 0


def test_memory_prediction():
    # fren-covers: testing::heavy_memory_prediction
    if not os.access(os.path.join(HERE, "../tools/heavy-observe/.lake/build/bin/compiler_advice"), os.X_OK):
        assert heavy.command_forecast("lake build") == (None, 0)
        return
    with tempfile.TemporaryDirectory() as state:
        now = 1000000
        def job(ended, peak, kind="lake build"):
            heavy.append_log({"event": "job", "job_kind": kind, "command": kind,
                              "ended_at": ended, "peak_rss_kb": peak}, state, {})
        assert heavy.command_forecast("lake build", state, {}, now) == (None, 0)
        for i in reversed(range(1, 26)):
            job(now - 30 + i, 100 + i if i > 5 else 99999)
        for ended, peak, kind in ((now + 1, 999999, "lake build"),
                                  (now - heavy.PREDICTION_SECONDS - 1, 999999, "lake build"),
                                  (now, 999999, "lake test"), (now, True, "lake build"),
                                  (now, 0, "lake build"), (float("nan"), 999999, "lake build"),
                                  (10 ** 1000, 999999, "lake build")):
            job(ended, peak, kind)
        assert heavy.command_forecast("lake build", state, {}, now) == (125, 20)
        with open(os.path.join(state, "log.jsonl"), "a") as f:
            f.write('null\n[]\n{"partial":')
        assert heavy.command_forecast("lake build", state, {}, now) == (125, 20)
        override = os.path.join(state, "override.jsonl")
        heavy.append_log({"job_kind": "lake build", "command": "lake build", "ended_at": now - 1, "peak_rss_kb": 777},
                         state, {"HEAVY_LOG": override})
        with open(override, "ab") as f:
            f.write(b"\xff\n")
        assert heavy.command_forecast("lake build", state, {"HEAVY_LOG": override}, now) == (777, 1)
        # Freeze the prediction before execution, then keep it beside the
        # actual peak rather than recomputing with the new observation.
        record = {"started_at": now}
        def execute(*args):
            record["peak_rss_kb"] = 999
            return 0
        with tempfile.TemporaryFile(mode="w+") as slot, \
             mock.patch.object(heavy, "run_command", side_effect=execute):
            assert heavy.run(slot, ["lake", "build"], "lake build", "lake build", record,
                             heavy.time.monotonic(), state, {"HEAVY_LOG": override}, lambda: 0) == 0
        assert record["predicted_peak_rss_kb"] == 777 and record["prediction_jobs"] == 1
        assert record["peak_rss_kb"] == 999


def test_forecast_kind():
    # fren-covers: testing::heavy_memory_prediction, testing::heavy_prediction_key
    if not os.access(os.path.join(HERE, "../tools/heavy-observe/.lake/build/bin/compiler_advice"), os.X_OK):
        return
    command = [sys.executable, "-c", "pass"]
    normal = heavy.job_kind(command)
    logical = "coordinator build"
    for override in (logical, None, ""):
        with tempfile.TemporaryDirectory() as state:
            now = heavy.time.time()
            heavy.append_log({"event": "job", "command": heavy.shlex.join(command),
                              "job_kind": "unrelated label", "ended_at": now - 1,
                              "peak_rss_kb": 777}, state, {})
            environ = {} if override is None else {"FREN_JOB_KIND": override}
            result = tiny_job(state, command, environ)
            assert result.returncode == 0, result.stderr
            with open(os.path.join(state, "log.jsonl")) as f:
                record = json.loads(f.readlines()[-1])
            assert record["job_kind"] == (override or normal)
            assert (record["predicted_peak_rss_kb"], record["prediction_jobs"]) == (777, 1)


def test_command_forecast_real_rows():
    # fren-covers: testing::heavy_memory_prediction, testing::heavy_prediction_key
    if not os.access(os.path.join(HERE, "../tools/heavy-observe/.lake/build/bin/compiler_advice"), os.X_OK):
        return
    rows = [
        {"command": "--offline lake test", "job_kind": "heavy", "peak_rss_kb": 17911340,
         "predicted_peak_rss_kb": 6121136, "exit_status": 137},
        {"command": "/home/ubuntu/coord/out/fd-soft-overlap/phases/001-author-d29e0ab6-83f7-4138-914d-b7f457b0fac3/overlap-controls.sh",
         "job_kind": "test", "peak_rss_kb": 13566436, "predicted_peak_rss_kb": 1649900},
    ]
    with tempfile.TemporaryDirectory() as state:
        now = 1794249291
        for row in rows:
            heavy.append_log({**row, "ended_at": now - 1}, state, {})
        for i in range(30):
            heavy.append_log({"command": "lake build Other", "job_kind": "heavy", "ended_at": now,
                              "peak_rss_kb": 100}, state, {})
        for row in rows:
            command = row["command"].removeprefix("--offline ")
            assert heavy.command_forecast(command, state, {}, now) == (row["peak_rss_kb"], 1)
        # Full commands distinguish build targets and shell wrappers, including
        # shell bodies containing paths that the old job-kind normalizer dropped.
        for command in ("lake build fren-dev fren_dev_test", "bash -c 'lake test /tmp/a'"):
            heavy.append_log({"command": command, "job_kind": "heavy", "ended_at": now,
                              "peak_rss_kb": 20000000}, state, {})
            assert heavy.command_forecast(command, state, {}, now) == (20000000, 1)
        assert heavy.command_forecast("bash -c 'lake build /tmp/a'", state, {}, now) == (None, 0)
        # New records retain the full command even when display is truncated.
        command = "bash -c '" + "x" * 300 + "'"
        heavy.append_log({"command": command[:237] + "...", "prediction_command": command,
                          "job_kind": "heavy", "ended_at": now, "peak_rss_kb": 444}, state, {})
        assert heavy.command_forecast(command, state, {}, now) == (444, 1)

def test_process_integration():
    # fren-covers: testing::heavy_counter_rate, testing::heavy_pressure
    code = ("import os,time; start=time.process_time(); "
            "exec('while time.process_time()-start < 1.2: os.stat(\"/dev/null\")')")
    with tempfile.TemporaryDirectory() as state:
        result = tiny_job(state, [sys.executable, "-c", code])
        assert result.returncode == 0, result.stderr
        with open(os.path.join(state, "log.jsonl")) as f:
            row = json.loads(f.read())
        assert row["involuntary_context_switches"] >= 0
        if heavy.platform.system() == "Linux":
            assert row["process_samples"] > 0
            data = list(row["process_cpu"].values())
            assert sum(d["core_seconds"] for d in data) > 0.5
            assert max(d["peak_process_count"] for d in data) >= 1
            assert 0 <= row["nonvoluntary_ctxt_switches"] <= row["involuntary_context_switches"]
            assert row["procs_running_sample_count"] > 0 and 0 <= row["oversubscribed_fraction"] <= 1
            assert row["ctxt_per_second_mean"] >= 0


def test_subreaper_outside_parent():
    # fren-covers: testing::heavy_group_gone, testing::heavy_owned_signal
    if heavy.platform.system() != "Linux":
        return
    with heavy.child_subreaper() as enabled, tempfile.TemporaryDirectory() as state:
        assert enabled
        ready, outside, reaped = [os.path.join(state, name) for name in ("worker", "outside", "reaped")]
        worker = ("import os,pathlib,signal,sys,time; "
                  "signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                  "pathlib.Path(sys.argv[1]+'.tmp').write_text(str(os.getpid())); "
                  "os.replace(sys.argv[1]+'.tmp',sys.argv[1]); time.sleep(60)")
        parent = ("import os,pathlib,subprocess,sys,time; "
                  f"child=subprocess.Popen([sys.executable,'-c',{worker!r},sys.argv[1]]); "
                  "exec('while not pathlib.Path(sys.argv[1]).exists(): time.sleep(0.01)'); "
                  "os.setpgid(0,0); pathlib.Path(sys.argv[2]+'.tmp').write_text(str(os.getpid())); "
                  "os.replace(sys.argv[2]+'.tmp',sys.argv[2]); result=child.wait(); "
                  "pathlib.Path(sys.argv[3]+'.tmp').write_text(str(result)); "
                  "os.replace(sys.argv[3]+'.tmp',sys.argv[3]); time.sleep(60)")
        leader = ("import pathlib,subprocess,sys,time\n"
                  f"subprocess.Popen([sys.executable,'-c',{parent!r},{ready!r},{outside!r},{reaped!r}])\n"
                  f"while not pathlib.Path({outside!r}).exists(): time.sleep(0.01)\n"
                  "raise SystemExit(7)\n")
        child = subprocess.Popen([sys.executable, "-I", "-B", "-c", leader], start_new_session=True)
        child.heavy_subreaper = True
        record = {"peak_rss_kb": 0}
        reap = lambda: heavy.reap_child(child, record)
        worker_pid, parent_pid = None, None
        try:
            deadline = heavy.time.monotonic() + 15
            while (child.returncode is None or not os.path.exists(outside)) and heavy.time.monotonic() < deadline:
                reap()
                heavy.time.sleep(0.02)
            assert child.returncode == 7 and os.path.exists(outside)
            with open(ready) as f:
                worker_pid = int(f.read())
            with open(outside) as f:
                parent_pid = int(f.read())
            assert os.getpgid(parent_pid) == parent_pid
            assert os.getpgid(worker_pid) == child.pid
            assert reap()  # ECHILD for -PGID, while the grandchild is not adoptable.
            assert not heavy.group_gone(child.pid, reap, True), "ECHILD hid a live group member"
            heavy.kill_group(child.pid, reap, True)
            assert child.returncode == 7
            os.kill(parent_pid, 0)  # The outside parent stayed alive throughout.
            deadline = heavy.time.monotonic() + 5
            while not os.path.exists(reaped) and heavy.time.monotonic() < deadline:
                heavy.time.sleep(0.02)
            assert os.path.exists(reaped)
            with open(reaped) as f:
                assert int(f.read()) == -signal.SIGKILL
            assert raises(lambda: os.kill(worker_pid, 0), ProcessLookupError)
        finally:
            if child.returncode is None:
                child.kill()
                child.wait(timeout=10)
            if parent_pid is None and os.path.exists(outside):
                with open(outside) as f:
                    parent_pid = int(f.read())
            if worker_pid is None and os.path.exists(ready):
                with open(ready) as f:
                    worker_pid = int(f.read())
            # Kill/reap the adopted outside parent first, so any surviving
            # worker becomes our child and cannot be reused before our wait.
            if parent_pid is not None:
                try:
                    os.kill(parent_pid, signal.SIGKILL)
                    os.waitpid(parent_pid, 0)
                except (ProcessLookupError, ChildProcessError):
                    pass
            if worker_pid is not None:
                try:
                    found, _ = os.waitpid(worker_pid, os.WNOHANG)
                    if not found:
                        os.kill(worker_pid, signal.SIGKILL)
                        os.waitpid(worker_pid, 0)
                except ChildProcessError:
                    pass  # Its parent already waited for it.


def main():
    tests = [test_process_lifetime_retention, test_process_group_reentry,
             test_cpu_ticks, test_cpu_samples, test_cpu_monitor, test_monitor_group_completion,
             test_cpu_descendants, test_cpu_reaping, test_cpu_many_waits, test_cpu_signal_fold,
             test_child_subreaper, test_process_readings,
             test_process_sampling, test_machine_pressure, test_memory_prediction, test_forecast_kind, test_command_forecast_real_rows,
             test_process_integration,
             test_parse_args, test_missing_command, test_recheck_wait_message, test_reservation_wait_message,
             test_registry_wait_messages,
             test_physical_memory,
             test_overrides, test_offline_command, test_load_admission, test_job_log,
             test_admission_snapshot, test_job_kinds, test_policy_flip_while_waiting,
             test_stats_and_appends, test_short_appends, test_policy_comparison,
             test_partial_policy_coverage, test_alternate, test_alternate_hangup,
             test_alternate_ignored_hangup, test_slot_identity, test_proc_namespace_translation,
             test_memory_victim, test_legacy_reservations, test_report_owner, test_legacy_proc_readings,
             test_legacy_report_reuse, test_legacy_coexistence, test_group_completion, test_fallback_escalation,
             test_namespace_init_reaping, test_namespace_init_workers, test_subreaper_outside_parent,
             test_no_signal_after_reap, test_status_failure_cleanup, test_pid_namespace_jobs, test_report_clock,
             test_stopped_owner, test_registry_signals_and_release,
             test_own_cap_with_other_victim, test_stopped_registry_holder, test_unverified_owners]
    for t in tests:
        t()
    print(f"heavy: {len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
