#!/usr/bin/env python3
"""Bounded actual lease/producer tests, with owned temporary session state.
The registered gate runs no workload timing comparison. --lake is the one
manual changed-source control, staged separately under a shared perf lease.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from overlay import create

BIN = HERE / ".lake/build/bin"
REAL = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/lean"


def wait_for(predicate, message, seconds=3):
    limit = time.monotonic() + seconds
    while not predicate():
        assert time.monotonic() < limit, message
        time.sleep(.005)


def records(directory):
    return [json.loads(p.read_text()) for p in directory.glob("process-*.json")]


def producer(case, work, shim):
    events = work / "events"
    os.environ["BUDGET_EVENTS"] = str(events)
    session = Path(os.environ.get("HEAVY_BUDGET_DIR", str(work / "unused")))
    children = []

    def launch(name):
        p = subprocess.Popen([str(shim), str(work / (name + ".lean"))], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        children.append(p)
        return p

    def started(name):
        wait_for(lambda: (events / (name + ".start")).exists(), "child did not start " + name)

    def release(name):
        (events / (name + ".release")).touch()

    def result(p, status=0):
        out, err = p.communicate(timeout=3)
        assert p.returncode == status, (case, status, p.returncode, out, err)
        return dict(status=p.returncode, stdout=out.decode(), stderr=err.decode())

    def ticket(n):
        wait_for(lambda: len(list(session.glob("ticket-*"))) >= n, "no gate ticket")

    evidence = {}
    try:
        if case in ("serial-fifo", "unequal", "cancel", "wait-cancel", "bypass"):
            a = launch("A"); started("A")
            b = launch("B"); ticket(2) if case != "bypass" else started("B")
            if case == "wait-cancel":
                b.send_signal(signal.SIGTERM); evidence["waiting_cancel"] = result(b, 125)
                assert not (events / "B.start").exists()
                release("A"); evidence["a"] = result(a)
                c = launch("B"); started("B"); release("B"); evidence["after_cancel"] = result(c)
                (work / "producer.json").write_text(json.dumps(evidence, indent=2)); return
            if case == "unequal":
                started("B")
                assert not (events / "A.end").exists(), "fitting children did not overlap"
                release("A"); release("B")
            elif case == "bypass":
                assert not (events / "A.end").exists()
                evidence["bypassed_gate_violates_no_overlap"] = True
                release("A"); release("B")
            else:
                time.sleep(.08)
                assert not (events / "B.start").exists(), "non-fitting child overlapped"
                if case == "cancel":
                    a.send_signal(signal.SIGTERM)
                    evidence["cancel"] = result(a, 125)
                else:
                    c = launch("C"); ticket(3)
                    time.sleep(.05)
                    assert not (events / "C.start").exists(), "later fitting waiter bypassed FIFO"
                    release("A")
                started("B")
                if case == "serial-fifo":
                    started("C"); release("C")
                    evidence["c"] = result(c)
                release("B")
            if case != "cancel": evidence["a"] = result(a)
            evidence["b"] = result(b)
        elif case in ("unknown", "pid-reuse", "namespace", "partial", "raw-stale", "unlocked"):
            held = (session / "ticket-00000000000000000000").open("w+")
            os.chmod(held.name, 0o600)
            if case != "unlocked": fcntl.flock(held, fcntl.LOCK_EX)
            stat = Path("/proc/self/stat").read_text().rsplit(")", 1)[1].split()
            start = int(stat[19])
            ns = Path("/proc/self/ns/pid").stat()
            boot = Path("/proc/sys/kernel/random/boot_id").read_text().strip()
            space = f"{boot}:{ns.st_dev}:{ns.st_ino}"
            if case == "pid-reuse": start += 1
            if case == "namespace": space += "-foreign"
            # Held old ticket is valid only for raw-stale: no timestamp ages a
            # frozen reservation. State=running, ticket=99, positive charge=7.
            row = f"99 1 7 {os.getpid()} {start} {space}\n"
            if case in ("partial", "unlocked"): row = "partial-publication"
            if case == "unknown": row = "99 1 7 2147483647 1 absent\n"
            held.write(row); held.flush()
            a = launch("A")
            if case == "raw-stale":
                ticket(2); time.sleep(.08)
                assert not (events / "A.start").exists(), "held reservation aged to zero"
                held.close(); started("A"); release("A"); evidence["a"] = result(a)
            elif case == "unlocked":
                started("A"); release("A"); evidence["a"] = result(a); held.close()
            else:
                evidence["a"] = result(a, 125)
                assert not (events / "A.start").exists()
                held.close()
        elif case in ("oversize", "bad-config", "bad-counter", "registry", "write-error", "missing-manifest", "preexec-error"):
            held = None
            if case == "bad-config": (session / "config").write_text("malformed")
            if case == "bad-counter": (session / "counter").write_text("partial")
            if case == "registry":
                held = (session / "registry").open("r+"); fcntl.flock(held, fcntl.LOCK_EX)
            if case == "write-error":
                os.environ["LD_PRELOAD"] = str(work.parent / "fault.so")
                os.environ["BUDGET_FAIL_WRITE"] = str(session / "counter")
            if case == "preexec-error":
                os.environ["LD_PRELOAD"] = str(work.parent / "fault.so")
                os.environ["BUDGET_FAIL_PREEXEC"] = "1"
            if case == "missing-manifest": (session / "requests").unlink()
            a = launch("A"); evidence["a"] = result(a, 125)
            assert not (events / "A.start").exists()
            if held: held.close()
        elif case in ("exec-error", "exit", "fallback"):
            if case == "exec-error":
                (shim.parent.parent / "real-lean.path").write_text(str(work / "missing-executable"))
            if case == "fallback": (work / "A.lean").write_text("mismatched source bytes")
            name = "Exit" if case == "exit" else "A"
            release(name)
            a = launch(name)
            evidence["a"] = result(a, 127 if case == "exec-error" else 7 if case == "exit" else 0)
        elif case == "fork-lease":
            os.environ["BUDGET_FORK"] = "1"
            release("A"); a = launch("A"); evidence["a"] = result(a)
            wait_for(lambda: (events / "A.descendant").exists(), "missing inherited holder")
            b = launch("B"); evidence["b"] = result(b, 125)
            assert not (events / "B.start").exists(), "inherited lock discarded"
            # Session cleanup must kill this retained group member and observe
            # its lease unlock, without ever using a row PID as a signal target.
        elif case == "observer-death":
            a = launch("A"); started("A")
            child = json.loads((events / "A.start").read_text())["pid"]
            a.kill(); result(a, -signal.SIGKILL)
            # The actual child inherited the lease, and its PDEATHSIG kills it.
            # A transient held/dead-owner row must error, never admit as zero.
            wait_for(lambda: not Path(f"/proc/{child}").exists() or
                     Path(f"/proc/{child}/stat").read_text().rsplit(")", 1)[1].split()[0] == "Z", "child survived observer")
            b = launch("B"); started("B"); release("B"); evidence["b"] = result(b)
        elif case == "owner-death":
            # Driver kills the session owner once this child is running. Parent
            # death propagates command -> observer -> compiler, all owned.
            a = launch("A"); started("A")
            (work / "owner-ready").touch()
            time.sleep(5)
            raise AssertionError("session owner death did not cancel producer")
        else:
            raise AssertionError(case)
        (work / "producer.json").write_text(json.dumps(evidence, indent=2))
    finally:
        for p in children:
            if p.poll() is None: p.kill()
            p.communicate(timeout=3)


def main():
    if sys.argv[1:2] == ["--producer"]:
        producer(sys.argv[2], Path(sys.argv[3]), Path(sys.argv[4])); return
    (HERE / "test-work").mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="budget-", dir=HERE / "test-work"))
    cases = ["serial-fifo", "unequal", "cancel", "wait-cancel", "unknown", "pid-reuse", "namespace", "partial", "raw-stale",
             "unlocked", "oversize", "bad-config", "bad-counter", "registry", "write-error", "missing-manifest", "preexec-error",
             "exec-error", "exit", "fallback", "fork-lease", "observer-death", "owner-death", "bypass"]
    signal_control = subprocess.run([sys.executable, "-I", str(HERE / "notice_signal_test.py")], capture_output=True, timeout=60)
    assert signal_control.returncode == 0, (signal_control.stdout, signal_control.stderr)
    feedback = subprocess.run([sys.executable, "-I", str(HERE / "feedback_test.py")], capture_output=True, timeout=30)
    assert feedback.returncode == 0, (feedback.stdout, feedback.stderr)
    pure = subprocess.run([str(BIN / "budget_tests")], capture_output=True, timeout=3)
    assert pure.returncode == 0, (pure.stdout, pure.stderr)
    fault_command = ["cc", "-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror",
                     str(HERE / "budget_fault.c"), "-o", str(work / "fault.so")]
    fault = subprocess.run(fault_command, capture_output=True, timeout=10)
    assert fault.returncode == 0, fault.stderr
    report = {"work": str(work), "pure": pure.stdout.decode(), "fault_command": fault_command, "cases": []}
    for case in cases:
        start = time.monotonic()
        directory = work / case; directory.mkdir(); (directory / "events").mkdir()
        overlay = create(directory / "overlay", REAL, BIN / "heavy_observe")
        fixture = directory / "fixture"
        fixture.write_bytes((HERE / "budget_fixture.py").read_bytes()); fixture.chmod(0o700)
        (overlay / "real-lean.path").write_text(str(fixture))
        manifest = directory / "manifest"
        demands = {"A": 7, "B": 2 if case == "unequal" else 7, "C": 2, "Exit": 3}
        lines = []
        for name, demand in demands.items():
            source = directory / (name + ".lean"); source.write_text("fixture " + name)
            digest = subprocess.check_output([str(BIN / "process_tests"), "--read", str(source)], text=True).strip().removeprefix("some:")
            lines.append(f"{source}\tlean-bytearray64:{source.stat().st_size}:{digest}\t{demand}\n")
        manifest.write_text("".join(lines))
        allowance = 6 if case == "oversize" else 10
        wait_ms = 200 if case == "registry" else 2500
        command = [str(BIN / "budget_session"), str(directory / "session"), str(allowance), "1", "9", str(wait_ms),
                   str(manifest), "--", "/usr/bin/python3", "-I", str(Path(__file__).resolve()), "--producer", case,
                   str(directory), str(overlay / "bin/lean")]
        environment = dict(os.environ)
        if case == "bypass":
            # Actual negative control: identical child producer, no gate path.
            # Its explicit overlap observation must violate the serial rule.
            command = ["/usr/bin/python3", "-I", str(Path(__file__).resolve()), "--producer", case,
                       str(directory), str(overlay / "bin/lean")]
            environment["HEAVY_BUDGET_DIR"] = str(directory / "unused")
            # Unset inside a trivial child environment before invoking observer.
            environment.pop("HEAVY_BUDGET_DIR")
        child = subprocess.Popen(command, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 start_new_session=True)
        try:
            if case == "owner-death":
                wait_for(lambda: (directory / "owner-ready").exists(), "owner control not ready")
                child.kill()
            stdout, stderr = child.communicate(timeout=9)
        except BaseException:
            child.send_signal(signal.SIGTERM)
            try: child.communicate(timeout=2)
            except subprocess.TimeoutExpired: child.kill(); child.communicate()
            raise
        (directory / "stdout").write_bytes(stdout); (directory / "stderr").write_bytes(stderr)
        expected = -signal.SIGKILL if case == "owner-death" else 0
        assert child.returncode == expected, (case, child.returncode, stdout, stderr, directory)
        rows = records(overlay / "records")
        if case == "serial-fifo":
            successful = sorted(rows, key=lambda r: r["reservation_ticket"])
            assert [r["requested_reservation_kib"] for r in successful] == [7, 7, 2]
            assert successful[1]["admission_wait_ns"] > 80000000
            assert successful[1]["admission_granted_ns"] < successful[2]["admission_granted_ns"]
            assert successful[2]["held_before_kib"] == 7
        if case == "unequal":
            assert sorted(r["held_before_kib"] for r in rows) == [0, 7]
        if case == "preexec-error":
            assert rows[0]["launch_errno"] == 5 and rows[0]["raw_wait_status"] == 125 << 8
            assert rows[0]["measured_peak_rss_kib"] is None and rows[0]["result_kind"] == 3
        if case == "fallback":
            assert rows[0]["request_provenance"] == "explicit-unknown-fallback" and rows[0]["requested_reservation_kib"] == 9
        if case == "bypass": assert all("gate_errno" not in r for r in rows)
        if case == "owner-death":
            info = json.loads((directory / "events/A.start").read_text())
            wait_for(lambda: not Path(f"/proc/{info['pid']}").exists() or
                     Path(f"/proc/{info['pid']}/stat").read_text().rsplit(")", 1)[1].split()[0] == "Z", "owner death child survived")
        report["cases"].append(dict(case=case, seconds=time.monotonic()-start, status=child.returncode,
                                    records=rows, stdout=stdout.decode(), stderr=stderr.decode()))
        (work / "report.json").write_text(json.dumps(report, indent=2))
    print(json.dumps({"passed": cases, "report": str(work / "report.json")}))


if __name__ == "__main__": main()
