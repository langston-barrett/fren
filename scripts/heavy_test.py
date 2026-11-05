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


def test_reservation_wait_message():
    class Waiting(Exception):
        pass

    environ = {"HEAVY_SLOTS": "2", "HEAVY_MEM_GB": "1", "HEAVY_MAX_LOAD": "off"}
    for recheck in (False, True):
        for rss, reason in ((None, "no compatible report"), (1, "stale or future-dated report")):
            with tempfile.TemporaryDirectory() as state:
                rows = [{"slot": "slot1", "rss_kb": rss, "fresh": False}]
                readings = [[], rows] if recheck else [rows]
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr), \
                     mock.patch.object(heavy, "jobs", side_effect=readings), \
                     mock.patch.object(heavy.time, "sleep", side_effect=Waiting), \
                     mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
                    assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                                                     environ, lambda: 0), Waiting)
                assert f"slot1 ({reason})" in stderr.getvalue()
                assert "resume stopped monitors or drain incompatible heavy jobs" in stderr.getvalue()
                assert "slots busy" not in stderr.getvalue()

    # A prior generic load warning must not hide a later reservation warning.
    with tempfile.TemporaryDirectory() as state:
        stderr = io.StringIO()
        rows = [{"slot": "slot0", "rss_kb": None, "fresh": False}]
        with contextlib.redirect_stderr(stderr), \
             mock.patch.object(heavy, "jobs", side_effect=[[], rows]), \
             mock.patch.object(heavy.time, "sleep", side_effect=[None, Waiting]), \
             mock.patch.object(heavy, "run", side_effect=AssertionError("admitted")):
            assert raises(lambda: heavy.main([sys.executable, "-c", "pass"], state,
                          dict(environ, HEAVY_MAX_LOAD="1"), lambda: 100), Waiting)
        assert "waiting for memory or load" in stderr.getvalue()
        assert "slot0 (no compatible report)" in stderr.getvalue()


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


def test_slot_identity():
    with tempfile.TemporaryDirectory() as state:
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
            # A stale live report blocks admission; it does not become zero.
            stale = dict(first.heavy_job, updated_monotonic=heavy.time.monotonic() - heavy.REPORT_STALE_SECONDS - 1)
            with heavy.registry(state):
                heavy.atomic_state(heavy.report_path(state, "slot0"), stale)
            assert heavy.heavy_rss_kb(state, 80) > 0.6 * 80
            assert heavy.memory_victim(heavy.jobs(state), 80) == (70, None)
            rows = {r["slot"]: r for r in heavy.jobs(state)}
            assert rows["slot0"]["rss_kb"] == 40
            assert rows["slot0"]["fresh"] is False
            # Wall-clock changes cannot turn reservations into eviction evidence.
            with mock.patch.object(heavy.time, "time", return_value=-1000000):
                assert heavy.memory_victim(heavy.jobs(state), 80) == (70, None)
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
            assert heavy.heavy_rss_kb(state, 80) > 0.6 * 80  # Empty does not mean unheld.
            legacy.write("5 10 foreign-job\n")
            legacy.flush()
            assert heavy.heavy_rss_kb(state, 80) > 0.6 * 80  # Legacy IDs are not globally valid.
        assert heavy.jobs(state) == []


def test_proc_namespace_translation():
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
    assert heavy.memory_victim([older, missing], 1) == (60, None)
    legacy = {"job_id": None, "order": None, "rss_kb": None}
    for leases in ([legacy], [older, legacy, newer], [newer, legacy, older]):
        assert heavy.memory_victim(leases, 1)[1] is None


def test_group_completion():
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
            reaper.join(timeout=1)
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
    with mock.patch.object(heavy.os, "killpg", side_effect=ProcessLookupError()) as probe:
        heavy.kill_group(5, lambda: True)
        probe.assert_called_once_with(5, 0)


def test_pid_namespace_jobs():
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
    with tempfile.TemporaryDirectory() as state, tempfile.TemporaryFile(mode="w+") as slot:
        slot.heavy_job = {"job_id": "older"}
        rows = [{"job_id": "older", "order": 1, "rss_kb": 101},
                {"job_id": "stopped-newer", "order": 2, "rss_kb": 1, "fresh": False}]
        record = {"started_at": 0, "peak_rss_kb": 0, "load_samples": []}
        with mock.patch.object(heavy.subprocess, "Popen", return_value=mock.Mock(pid=42)), \
             mock.patch.object(heavy, "visible_group", return_value=42), \
             mock.patch.object(heavy, "group_rss_kb", return_value={42: 101}), \
             mock.patch.object(heavy, "publish_memory"), \
             mock.patch.object(heavy, "jobs", return_value=rows), \
             mock.patch.object(heavy, "mem_cap_kb", return_value=100), \
             mock.patch.object(heavy, "reap_child", return_value=False), \
             mock.patch.object(heavy, "kill_group") as kill, \
             contextlib.redirect_stderr(io.StringIO()):
            assert heavy.run_command(slot, ["tiny"], "tiny", record, state, {}, lambda: 0) == 137
            assert kill.call_count == 1


def registry_timeout_paths(state):
    # Run in a separate process so the harness can time out a regression
    # even if one of these calls accidentally uses a blocking flock again.
    before = signal.pthread_sigmask(signal.SIG_BLOCK, ())
    assert raises(lambda: heavy.jobs(state), heavy.RegistryBusy)
    assert heavy.heavy_rss_kb(state, 100) == math.inf
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
            with open(f"/proc/{holder.pid}/stat") as f:
                assert f.read().split(")")[-1].split()[0] == "T"
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
    with tempfile.TemporaryDirectory() as state:
        slot = open(os.path.join(state, "slot0"), "a+")
        try:
            with heavy.registry(state):
                assert heavy.claim_slot(slot, "slot0", state, {"enqueued_at": 0})
            heavy.publish_memory(slot, 40, state)
            stamp = slot.heavy_job["updated_monotonic"]
            with mock.patch.object(heavy.time, "time", return_value=10**12), \
                 mock.patch.object(heavy.time, "monotonic", return_value=stamp + 1):
                assert heavy.jobs(state)[0]["fresh"]
                assert heavy.heavy_rss_kb(state, 80) == 40
            for now in (stamp - 1, stamp + heavy.REPORT_STALE_SECONDS + 1):
                with mock.patch.object(heavy.time, "monotonic", return_value=now):
                    row = heavy.jobs(state)[0]
                    assert not row["fresh"] and row["rss_kb"] == 40
                    assert heavy.heavy_rss_kb(state, 80) == 80
                    assert heavy.memory_victim([row], 80) == (40, None)
        finally:
            heavy.release_slot(slot, state)


def test_stopped_owner():
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
                deadline = heavy.time.monotonic() + 5
                while heavy.time.monotonic() < deadline:
                    with open(f"/proc/{children[0].pid}/stat") as f:
                        if f.read().rpartition(")")[2].split()[0] == "T":
                            break
                    heavy.time.sleep(0.01)
                else:
                    raise AssertionError("monitor did not stop before registry unlock")
            deadline = heavy.time.monotonic() + heavy.REPORT_STALE_SECONDS + 2
            while heavy.time.monotonic() < deadline:
                assert children[1].poll() is None, children[1].communicate()
                heavy.time.sleep(0.1)
            reports = heavy.jobs(state)
            assert len(reports) == 2 and sum(not r["fresh"] for r in reports) == 1
            cap = int(0.5 * GB)
            assert heavy.heavy_rss_kb(state, cap) > 0.6 * cap
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


def main():
    tests = [test_parse_args, test_missing_command, test_recheck_wait_message, test_reservation_wait_message,
             test_physical_memory,
             test_overrides, test_offline_command, test_load_admission, test_job_log,
             test_admission_snapshot, test_job_kinds, test_policy_flip_while_waiting,
             test_stats_and_appends, test_short_appends, test_policy_comparison,
             test_partial_policy_coverage, test_alternate, test_alternate_hangup,
             test_alternate_ignored_hangup, test_slot_identity, test_proc_namespace_translation,
             test_memory_victim, test_group_completion, test_fallback_escalation,
             test_no_signal_after_reap, test_pid_namespace_jobs, test_report_clock,
             test_stopped_owner, test_registry_signals_and_release,
             test_own_cap_with_other_victim, test_stopped_registry_holder]
    for t in tests:
        t()
    print(f"heavy: {len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
