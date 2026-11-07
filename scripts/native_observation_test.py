#!/usr/bin/env python3
"""Real process regressions for the production observer and root relay."""
import argparse
import json
import os
from pathlib import Path
import selectors
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time

from native_test_process import NativeTimeout, cleanup, initialize, run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", required=True)
    parser.add_argument("--receipts")
    args = parser.parse_args()
    driver = str(Path(args.driver).resolve())
    wrapper = str(Path(__file__).with_name("native_diagnostic.py").resolve())
    debugger = shutil.which("gdb")
    assert debugger, "native observation harness requires GDB"
    initialize()
    destination = Path(args.receipts) if args.receipts else None
    if destination:
        destination.mkdir(parents=True, exist_ok=True)
    rows = []
    peer = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    try:
        with tempfile.TemporaryDirectory(prefix="fren-observation-test-") as directory:
            root = Path(directory)
            plain = run([driver, "--job", "nativeObservationProbe"], peers=(peer.pid,))
            assert plain.returncode == 0 and plain.stdout == "[]\n" and not plain.stderr, plain
            env = dict(os.environ, FREN_DIAG_OWN_SPEC_INITIAL="1")
            env.pop("FREN_NATIVE_LIVE_FILE", None)
            child = subprocess.Popen([driver, "--native-observable-parent"], env=env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            live = b""
            try:
                with selectors.DefaultSelector() as ready:
                    ready.register(child.stderr, selectors.EVENT_READ)
                    deadline = time.monotonic() + 4
                    while b"live-isolated-start" not in live and time.monotonic() < deadline:
                        if ready.select(0.05):
                            live += os.read(child.stderr.fileno(), 4096)
                assert b"live-isolated-start" in live and child.poll() is None, (child.poll(), live)
                assert b"invocation" in live and b"original-start" in live, live
                stdout, stderr = child.communicate(timeout=5)
                live += stderr
                assert child.returncode == 0 and stdout == plain.stdout.encode(), (child.returncode, stdout, live)
                assert b"live-isolated-done" in live and b"isolated output must not escape" not in live, live
                rows.append({"case": "root-live-before-completion", "status": child.returncode,
                             "stdout": stdout.decode(), "stderr": live.decode()})
            finally:
                receipt = cleanup(child, (peer.pid,))
                assert not receipt["remaining"] and not receipt["errors"], receipt
                child.stdout.close()
                child.stderr.close()

            def command(name, program, *options, argv=None):
                return [sys.executable, wrapper, "--report", str(root / (name + ".json")),
                        *options, "--", *(argv or [sys.executable, "-c", program])]

            def execute(name, program, *options, argv=None, env=None):
                started = time.monotonic()
                try:
                    result = run(command(name, program, *options, argv=argv), timeout=10, peers=(peer.pid,), env=env)
                except NativeTimeout as error:
                    report_file = root / (name + ".json")
                    rows.append({"case": name, "seconds": time.monotonic() - started,
                                 "status": None, "timeout": error.receipt,
                                 "report": json.loads(report_file.read_text()) if report_file.exists() else None})
                    raise
                report = json.loads((root / (name + ".json")).read_text())
                rows.append({"case": name, "seconds": time.monotonic() - started,
                    "status": result.returncode, "stdout": result.stdout,
                    "stderr": result.stderr, "report": report, "cleanup": result.cleanup})
                assert peer.poll() is None, "observer killed the peer"
                assert not report["cleanup"]["remaining"] and not report["cleanup"]["errors"], report
                return result, report

            slow = ("import os,time; from pathlib import Path; "
                    "p=Path(os.environ['FREN_ENUM_PROGRESS']); "
                    "p.write_text('[\"phase\",\"slow-original\"]\\n'); "
                    "time.sleep(1.2); print('[]')")
            result, report = execute("slow-gdb", slow, "--sample-seconds", "0.25", "--operation-seconds", "3")
            assert result.returncode == 0 and result.stdout == "[]\n" and not result.stderr, rows[-1]
            assert report["original_exit"] == 0 and report["debugger_exit"] == 0, report
            assert report["original_pid"] != report["observer_child_pid"], report
            assert report["fault_signal"] is None and report["original_signal"] is None, report
            assert report["observation_status"] == "complete", report
            assert report["observation"]["initiator"] == "native-observer", report
            assert "#0" in report["observation"]["backtrace"] and "slow-original" in report["context"], report

            # A real GDB blocked before loading its helper. No fake frames,
            # supplied health Boolean, or inferred native child status.
            blocked = root / "blocked-gdb"
            blocked.write_text("#!/bin/sh\nexec " + shlex.quote(debugger) +
                " -iex 'python import time; time.sleep(60)' \"$@\"\n")
            blocked.chmod(0o755)
            result, report = execute("blocked-observer", "import time; time.sleep(60)", "--debugger", str(blocked),
                                     "--operation-seconds", "0.3")
            assert result.returncode == 125 and not result.stdout, rows[-1]
            assert report["original_exit"] is None and report["original_signal"] is None, report
            assert report["fault_signal"] is None and report["observation_status"] == "incomplete", report
            assert report["snapshot"]["owned"] and report["cleanup_initiator"] == "native-observer:operation-budget", report

            # Block an actual debugger backtrace after a real native ABRT.
            # Only this owned debugger ignores its interrupt; the original
            # child's dispositions and physical status are never replaced.
            commands = root / "blocked-bt.gdb"
            commands.write_text("define bt\npython import signal,time; signal.signal(signal.SIGINT,signal.SIG_IGN); time.sleep(60)\nend\n")
            blocked.write_text("#!/bin/sh\nexec " + shlex.quote(debugger) + " -ix " +
                               shlex.quote(str(commands)) + " \"$@\"\n")
            result, report = execute("blocked-backtrace", "", "--debugger", str(blocked),
                "--operation-seconds", "1", argv=[driver, "--job", "nativeDiagnosticProbe", "crash"])
            assert result.returncode == 134 and report["fault_signal"] == 6, rows[-1]
            assert report["original_exit"] is None and report["original_signal"] is None, report
            assert report["debugger_exit"] is None and report["debugger_cleanup_exit"] == -9, report
            assert report["observation_status"] == "incomplete" and report["faults"][0]["backtrace"] is None, report

            # Real original completion can precede a failing GDB command.
            # The command's failure must not erase GDB's actual exit event.
            fact = root / "terminal-fact.json"
            commands.write_text("define hookpost-run\npython import gdb,json; from pathlib import Path; " +
                "Path(" + repr(str(fact)) + ").write_text(json.dumps({\"exit_code\":int(gdb.convenience_variable(\"_exitcode\"))}))\n" +
                "python raise RuntimeError(\"controlled failure after original completion\")\nend\n")
            result, report = execute("post-run-error", "print('[]')", "--debugger", str(blocked))
            assert json.loads(fact.read_text())["exit_code"] == 0, fact.read_text()
            assert result.returncode == 125 and report["original_exit"] == 0, rows[-1]
            assert report["debugger_exit"] == 0 and report["observation_status"] == "failed", report
            assert "controlled failure after original completion" in report["helper_error"], report
            assert report["debugger_state"]["failed_operation"]["operation"] == "run", report
            assert report["terminal_status_event"] == "exited" and report["fault_signal"] is None, report
            assert set(report["debugger_state"]["error_observations"]) == {
                "info threads", "info program", "p $_exitsignal", "show scheduler-locking"}, report

            if sys.platform == "linux":
                # Stop the real native original after its coreless startup
                # hook, then fail a real GDB command. Raw transport results
                # describe this still-owned inferior, not a supplied health flag.
                commands.write_text("define hook-run\nbreak lean_initialize\nend\n"
                    "define hookpost-run\npython raise RuntimeError('controlled live transport observation')\nend\n")
                live = root / "transport.jsonl"
                live.touch()
                result, report = execute("live-transport-error", "", "--debugger", str(blocked),
                    argv=[driver, "--job", "nativeDiagnosticProbe", "pass"],
                    env=dict(os.environ, FREN_NATIVE_LIVE_FILE=str(live)))
                assert result.returncode == 125 and not result.stdout, rows[-1]
                assert report["original_exit"] is None and report["fault_signal"] is None, report
                assert "controlled live transport observation" in report["helper_error"], report
                facts = report["debugger_state"]["transport"]
                assert facts["inferior_pid"] == report["original_pid"], facts
                assert facts["inferior_ppid"] == report["observer_child_pid"], facts
                assert facts["gdb_read_bytes"] == 1 and facts["cached_proc_mem"], facts
                assert all(row.get("read_bytes") == 1 or "errno" in row
                           for row in facts["cached_proc_mem"]), facts
                assert isinstance(facts["peekdata"]["errno"], int), facts
                assert "new_proc_mem_read_bytes" in facts or "new_proc_mem_errno" in facts, facts
                assert facts["debugger_status"] and facts["kernel"] and facts["gdb"], facts
                events = [json.loads(line) for line in live.read_text().splitlines()]
                assert any(row["native"] == "transport-observation" for row in events), events

            # The original really exits while gdb.execute('run') is still
            # inside its post-run hook. This must become bounded control
            # work, not wait for the 120-second productive sampling clock.
            commands.write_text("define hookpost-run\npython import signal,time; " +
                "signal.signal(signal.SIGINT,signal.SIG_IGN); time.sleep(60)\nend\n")
            result, report = execute("terminal-command-return", "", "--debugger", str(blocked),
                "--operation-seconds", "1", argv=[driver, "--job", "nativeDiagnosticProbe", "pass"])
            assert result.returncode == 125 and report["original_exit"] == 0, rows[-1]
            assert result.stdout == "[]\n" and report["original_signal"] is None and report["fault_signal"] is None, report
            assert report["control_operation"] == "terminal-command-return", report
            assert report["debugger_state"]["operation"] == "run", report
            assert report["debugger_exit"] is None and report["debugger_cleanup_exit"] == -9, report
            assert report["observation_status"] == "incomplete" and report["cleanup_initiator"] == "native-observer:operation-budget", report

            # Hold the real debugger after the production helper returns.
            # Its physical status is still unknown, but the original's
            # actual terminal status must be published before that wait.
            commands.write_text("define hookpost-run\npython raise RuntimeError(\"controlled error before debugger shutdown\")\nend\n")
            blocked.write_text("#!" + sys.executable + "\nimport os,sys\na=sys.argv[1:]\ni=a.index('--args')\n" +
                "os.execv(" + repr(debugger) + ", [" + repr(debugger) + ",'-ix'," + repr(str(commands)) + "]+a[:i]+['-ex'," +
                repr("python import signal,time; signal.signal(signal.SIGINT,signal.SIG_IGN); time.sleep(60)") +
                "]+a[i:])\n")
            name = "completed-before-debugger"
            child = subprocess.Popen(command(name, "raise SystemExit(23)", "--debugger", str(blocked),
                "--operation-seconds", "1"), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                start_new_session=True)
            try:
                deadline = time.monotonic() + 4
                report = {}
                while time.monotonic() < deadline:
                    try:
                        report = json.loads((root / (name + ".json")).read_text())
                    except (FileNotFoundError, json.JSONDecodeError):
                        pass
                    if report.get("original_exit") == 23:
                        break
                    time.sleep(0.01)
                assert report.get("original_exit") == 23 and child.poll() is None, report
                assert report["debugger_exit"] is None and not report["complete"], report
                stdout, stderr = child.communicate(timeout=5)
                report = json.loads((root / (name + ".json")).read_text())
                assert child.returncode == 23 and report["original_exit"] == 23, report
                assert report["debugger_exit"] is None and report["debugger_cleanup_exit"] == -9, report
                assert report["observation_status"] == "incomplete", report
                assert "controlled error before debugger shutdown" in report["helper_error"], report
                assert "observation budget" in report["error"], report
                assert report["cleanup_initiator"] == "native-observer:operation-budget", report
                assert report["debugger_state"]["operation"] == "debugger-shutdown", report
                rows.append({"case": name, "status": child.returncode, "stdout": stdout.decode(),
                             "stderr": stderr.decode(), "report": report})
            finally:
                receipt = cleanup(child, (peer.pid,))
                assert not receipt["remaining"] and not receipt["errors"] and peer.poll() is None, receipt
                child.stdout.close()
                child.stderr.close()

            if sys.platform == "linux":
                holder = "import os,time; p=os.fork(); time.sleep(60) if p==0 else print('[]',flush=True)"
                # The old pipe-shaped capture really blocks on EOF after
                # its leader exits. Retain that negative control and reap
                # its adopted writer before testing the production path.
                try:
                    run([sys.executable, "-c", holder], timeout=0.2, peers=(peer.pid,))
                    raise AssertionError("pipe-holder negative control did not block")
                except NativeTimeout as error:
                    assert error.receipt["timed_out"] and not error.receipt["remaining"], error.receipt
                    rows.append({"case": "inherited-pipe-negative", "receipt": error.receipt})
                result, report = execute("inherited-writer", holder, "--capture-only")
                assert result.returncode == 125 and result.stdout == "[]\n", rows[-1]
                assert report["original_exit"] == 0 and report["debugger_exit"] is None, report
                assert report["observation_status"] == "incomplete" and report["cleanup"]["reaped"], report
                assert report["cleanup_initiator"] == "native-observer:surviving-descendants", report
                result, report = execute("inherited-writer-nonzero", holder + "; raise SystemExit(23)", "--capture-only")
                assert result.returncode == 23 and report["original_exit"] == 23, rows[-1]
                assert report["observation_status"] == "incomplete" and report["cleanup"]["reaped"], report
                assert report["cleanup_initiator"] == "native-observer:surviving-descendants", report

            for name, sig in [("cancelled", signal.SIGTERM), ("lost-final", signal.SIGKILL)]:
                live_path = root / (name + ".jsonl")
                live_path.touch()
                child = subprocess.Popen(command(name, "import time; time.sleep(60)", "--capture-only"),
                    env=dict(os.environ, FREN_NATIVE_LIVE_FILE=str(live_path)),
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
                try:
                    deadline = time.monotonic() + 3
                    while "original-start" not in live_path.read_text() and time.monotonic() < deadline:
                        time.sleep(0.02)
                    assert "original-start" in live_path.read_text() and child.poll() is None
                    before = json.loads((root / (name + ".json")).read_text())
                    assert not before["complete"] and before["original_exit"] is None, before
                    child.send_signal(sig)
                    stdout, stderr = child.communicate(timeout=4)
                    report = json.loads((root / (name + ".json")).read_text())
                    assert report["original_exit"] is None and report["fault_signal"] is None, report
                    if sig == signal.SIGTERM:
                        assert child.returncode == 125 and report["observation_status"] == "cancelled", report
                        assert report["cleanup_initiator"] == "native-observer:cancel" and report["cancel_signal"] == 15, report
                    else:
                        assert child.returncode == -9 and not report["complete"], report
                    rows.append({"case": name, "status": child.returncode, "stdout": stdout.decode(),
                        "stderr": stderr.decode(), "report": report, "live": live_path.read_text()})
                finally:
                    receipt = cleanup(child, (peer.pid,))
                    assert not receipt["remaining"] and not receipt["errors"] and peer.poll() is None, receipt
                    rows[-1]["external_test_cleanup"] = receipt
                    child.stdout.close()
                    child.stderr.close()
        return 0
    finally:
        peer.terminate()
        peer.wait(timeout=2)
        if destination:
            (destination / "observations.json").write_text(json.dumps(rows, indent=2) + "\n")
        for row in rows:
            print(json.dumps({k: row[k] for k in ("case", "status", "seconds") if k in row}))


if __name__ == "__main__":
    sys.exit(main())
