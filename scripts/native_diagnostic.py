#!/usr/bin/env python3
"""Run one original native test child under GDB, without a later replay.

Successful output is the child's output. On failure, append a bounded
checkpoint trail and native frames. Debugger and original-child statuses
are separate; a successful debugger never turns a child crash green.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import sys
import tempfile


def encoded(returncode):
    return 128 - returncode if returncode < 0 else returncode


def run(command, env, cohort, workers, debugger="gdb"):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    with tempfile.TemporaryDirectory(prefix="fren-native-diag-") as directory:
        root = Path(directory)
        journal = root / "progress"
        journal.touch()
        child_env = dict(env, FREN_ENUM_PROGRESS=str(journal),
                         FREN_ENUM_DIAG_ACTIVE="1", FREN_DIAG_ENUMERATION="0",
                         FREN_NATIVE_DIAG_DIR=str(root))
        executable = shutil.which(debugger)
        report = {"cohort": cohort, "workers": workers, "debugger": debugger,
                  "debugger_exit": None, "original_exit": None,
                  "original_signal": None, "fault_signal": None,
                  "terminated_by_debugger": False, "faults": [], "error": None}
        if executable is None:
            # Preserve the original check even when diagnostics cannot
            # start, but explicitly fail the requested diagnostic mode.
            child = subprocess.run(command, env=child_env, capture_output=True)
            report.update(debugger_status="missing", original_exit=encoded(child.returncode),
                          original_signal=-child.returncode if child.returncode < 0 else None,
                          error="requested native debugger is unavailable")
            stdout, stderr = child.stdout, child.stderr
            code = encoded(child.returncode) or 125
        else:
            helper = Path(__file__).with_name("native_diag_gdb.py").resolve()
            with (root / "debugger").open("wb") as log:
                debug = subprocess.run([executable, "-q", "-nx", "-batch",
                                        "-iex", "set debuginfod enabled off", "-x", str(helper),
                                        "--args", *command], env=child_env,
                                       stdout=log, stderr=subprocess.STDOUT)
            report["debugger_exit"] = debug.returncode
            state_file = root / "inferior.json"
            state = json.loads(state_file.read_text()) if state_file.exists() else {}
            faults = state.get("signals", [])
            terminal_signal = state.get("terminal_signal")
            terminated = state.get("terminated_by_debugger", False)
            report.update(debugger_status="captured" if not state.get("error") and debug.returncode == 0 else "failed",
                          original_exit=(128 + terminal_signal if terminal_signal else state.get("exit_code")) if not terminated else None,
                          original_signal=terminal_signal if not terminated else None,
                          terminated_by_debugger=terminated, faults=faults,
                          error=state.get("error"))
            if faults:
                report["fault_signal"] = int(getattr(signal, faults[0]["signal"]))
            if not state.get("started") or not state_file.exists():
                report["error"] = report["error"] or "debugger did not report an executed original child"
                report["debugger_status"] = "failed"
            stdout = (root / "stdout").read_bytes() if (root / "stdout").exists() else b""
            stderr = (root / "stderr").read_bytes() if (root / "stderr").exists() else b""
            # There is one original child, not a crash followed by a replay.
            # A handled fault or GDB's own zero exit cannot hide that fault.
            code = (128 + report["fault_signal"]) if faults else report["original_exit"]
            if report["debugger_status"] != "captured" or code is None:
                code = code or 125
            report["debugger_log"] = (root / "debugger").read_text(errors="replace")[-65536:]
        report["context"] = "\n".join(journal.read_text(errors="replace").splitlines()[-64:])
        report["status"] = code
        return code, stdout, stderr, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True)
    parser.add_argument("--cohort", default="[]")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--debugger", default="gdb")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("an original command is required")
    code, stdout, stderr, report = run(command, os.environ, json.loads(args.cohort), args.workers, args.debugger)
    Path(args.report).write_text(json.dumps(report, indent=2) + "\n")
    sys.stdout.buffer.write(stdout)
    sys.stderr.buffer.write(stderr)
    if code:
        sys.stderr.write("\nnative diagnostic: " + json.dumps(report, indent=2) + "\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
