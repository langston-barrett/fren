#!/usr/bin/env python3
"""Source-bound integration checks for the in-place native wrapper."""
import argparse
import json
import resource
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", required=True)
    parser.add_argument("--receipts")
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    driver = str(Path(args.driver).resolve())
    wrapper = str(Path(__file__).with_name("native_diagnostic.py"))
    debugger = shutil.which("gdb")
    plain = subprocess.run([driver, "--job", "nativeDiagnosticProbe", "pass"],
                           capture_output=True, text=True, timeout=60)
    assert plain.returncode == 0 and plain.stdout.strip() == "[]" and not plain.stderr, plain
    crash = subprocess.run([driver, "--job", "nativeDiagnosticProbe", "crash"],
                           capture_output=True, text=True, timeout=60)
    assert crash.returncode == -6 and not crash.stdout and not crash.stderr, crash
    cases = [("pass", "fren-deliberately-missing-debugger", 125)]
    if debugger:
        cases += [("pass", debugger, 0), ("crash", debugger, 134)]
    # An actual sibling stays alive while the controlled child crashes.
    # The wrapper must target/reap only its own inferior, not this cohort.
    sibling = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    try:
        with tempfile.TemporaryDirectory(prefix="fren-native-diag-test-") as directory:
            for i, (mode, tool, expected) in enumerate(cases):
                cohort = [["nativeDiagnosticProbe", mode], ["nativeDiagnosticSibling"]]
                report_file = Path(directory) / f"report-{i}.json"
                command = [sys.executable, wrapper, "--report", str(report_file),
                           "--cohort", json.dumps(cohort), "--workers", "2", "--debugger", tool,
                           "--", driver, "--job", "nativeDiagnosticProbe", mode]
                child = subprocess.run(command, capture_output=True, text=True, timeout=60)
                report = json.loads(report_file.read_text())
                if args.receipts:
                    destination = Path(args.receipts)
                    destination.mkdir(parents=True, exist_ok=True)
                    (destination / f"case-{i}.json").write_text(json.dumps(report, indent=2) + "\n")
                assert child.returncode == expected, (command, child.returncode, child.stderr)
                assert report["cohort"] == cohort and report["workers"] == 2, report
                assert '["phase","controlled-check"]' in report["context"], report
                assert '["method","solver"]' in report["context"], report
                assert "own_spec_progress.fren" in report["context"], report
                assert '["diagnostic-env","0","1"]' in report["context"], report
                assert sibling.poll() is None, "diagnostics terminated the sibling workload"
                assert "captured output must not escape" not in child.stdout, child.stdout
                if tool == "fren-deliberately-missing-debugger":
                    assert report["debugger_status"] == "missing", report
                    assert report["original_exit"] == 0, report
                    assert child.stdout.strip() == "[]", child.stdout
                    assert "unavailable" in child.stderr, child.stderr
                elif mode == "pass":
                    assert report["original_exit"] == 0 and report["original_signal"] is None, report
                    assert report["debugger_exit"] == 0 and not report["faults"], report
                    assert report["debugger_status"] == "captured", report
                    assert child.stdout == plain.stdout and not child.stderr, child
                else:
                    assert report["original_signal"] == 6, report
                    assert report["original_exit"] == 134 and not report["terminated_by_debugger"], report
                    assert report["debugger_status"] == "captured" and not report["error"], report
                    assert report["debugger_exit"] == 0, report
                    assert report["faults"][0]["signal"] == "SIGABRT", report
                    assert "#0" in report["faults"][0]["backtrace"], report
                    assert "si_signo" in report["faults"][0]["siginfo"], report
                    assert "first" in report["context"] and not child.stdout, report
                    assert "SIGABRT" in child.stderr and "backtrace" in child.stderr, child.stderr
                print(json.dumps({"mode": mode, "debugger": tool, "status": child.returncode,
                                  "original_exit": report["original_exit"],
                                  "original_signal": report["original_signal"],
                                  "debugger_exit": report["debugger_exit"]}))
            if debugger:
                # A handler that returns must not erase a recorded fault,
                # even when this same original child later exits zero.
                report_file = Path(directory) / "handled.json"
                handled = "import os,signal; signal.signal(signal.SIGSEGV,lambda *_:None); os.kill(os.getpid(),signal.SIGSEGV)"
                child = subprocess.run([sys.executable, wrapper, "--report", str(report_file),
                                        "--", sys.executable, "-c", handled],
                                       capture_output=True, text=True, timeout=60)
                report = json.loads(report_file.read_text())
                assert child.returncode == 139 and report["original_exit"] == 0, report
                assert report["original_signal"] is None and report["fault_signal"] == 11, report
                assert report["debugger_exit"] == 0 and report["debugger_status"] == "captured", report
                assert not report["terminated_by_debugger"] and sibling.poll() is None, report
                if args.receipts:
                    (Path(args.receipts) / "handled.json").write_text(json.dumps(report, indent=2) + "\n")
    finally:
        sibling.terminate()
        sibling.wait()
    if not debugger:
        # The missing-debugger case above still verifies explicit failure
        # and execution of the original check. CI's opt-in mode also fails.
        print("skipped: native backtrace assertions: gdb unavailable")
    return 0


if __name__ == "__main__":
    sys.exit(main())
