#!/usr/bin/env python3
"""Observe one original child; never replay or substitute a product verdict."""
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
import time

from native_observer import emit, invocation, read, save, snapshot, tail
from native_test_process import cleanup, initialize


def encoded(returncode):
    return 128 - returncode if returncode < 0 else returncode


def observe_state(report, state):
    """Publish real terminal evidence independently of debugger completion."""
    report["debugger_state"] = {key: state[key] for key in (
        "operation", "operation_id", "completed_operation_id", "operation_output",
        "helper_complete", "error", "failed_operation", "started", "original_pid", "exit_code",
        "terminal_signal", "terminal_status_source", "terminal_status_event", "terminal_wait") if key in state}
    report["helper_error"] = state.get("error")
    if state.get("original_pid"):
        report["original_pid"] = state["original_pid"]
    if state.get("terminal_status_source") and not state.get("terminated_by_debugger"):
        terminal_signal = state.get("terminal_signal")
        report.update(original_exit=128 + terminal_signal if terminal_signal else state.get("exit_code"),
                      original_signal=terminal_signal,
                      terminal_status_source=state["terminal_status_source"],
                      terminal_status_event=state.get("terminal_status_event"))


def run(command, env, cohort, workers, debugger="gdb", progress_env="FREN_ENUM_PROGRESS",
        *, report_path=None, capture_only=False, sample_seconds=120, operation_seconds=5):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    initialize()
    process = None
    report = None
    cancelled = []
    previous = {}
    for sig in (signal.SIGTERM, signal.SIGINT):
        previous[sig] = signal.signal(sig, lambda signum, _frame: cancelled.append(signum))
    try:
        with tempfile.TemporaryDirectory(prefix="fren-native-diag-") as directory:
            root = Path(directory)
            journal = Path(env[progress_env]) if env.get(progress_env) else root / "progress"
            journal.touch()
            child_env = dict(env, FREN_NATIVE_CORELESS="1", FREN_NATIVE_DIAG_DIR=str(root))
            child_env[progress_env] = str(journal)
            if not capture_only:
                child_env.update(FREN_ENUM_PROGRESS=str(journal), FREN_ENUM_DIAG_ACTIVE="1",
                                 FREN_DIAG_ENUMERATION="0", FREN_DIAG_OWN_SPEC_INITIAL="0",
                                 FREN_OWN_DIAG_ACTIVE="1")
            executable = None if capture_only else shutil.which(debugger)
            report = {"command": command, "progress_env": progress_env, "cohort": cohort,
                      "workers": workers, "debugger": debugger, "debugger_exit": None,
                      "original_exit": None, "original_signal": None, "fault_signal": None,
                      "terminated_by_debugger": False, "faults": [], "error": None,
                      "observation_status": "running", "complete": False,
                      "debugger_status": "not-requested" if capture_only else "starting",
                      "observation_policy": {"sample_seconds": sample_seconds,
                                             "operation_seconds": operation_seconds},
                      "cleanup_initiator": None}

            def retain(event, **fields):
                report["context"] = "\n".join(tail(journal).splitlines()[-64:])
                report["milestone"] = event
                if report_path:
                    save(report_path, report)
                emit(env, event, **fields)

            retain("invocation", **invocation(command, cohort, workers))
            if executable:
                helper = Path(__file__).with_name("native_diag_gdb.py").resolve()
                argv = [executable, "-q", "-nx", "-batch", "-iex", "set debuginfod enabled off",
                        "-x", str(helper), "--args", *command]
            else:
                argv = command
                if not capture_only:
                    report.update(debugger_status="missing", error="requested native debugger is unavailable")
            # Regular files break inherited-pipe EOF waits. A descendant
            # surviving its leader is still an explicit lifetime failure.
            with (root / ("debugger" if executable else "stdout")).open("wb") as stdout, \
                    (root / "stderr").open("wb") as stderr:
                process = subprocess.Popen(argv, env=child_env, stdin=subprocess.DEVNULL,
                    stdout=stdout, stderr=subprocess.STDOUT if executable else stderr,
                    start_new_session=True)
                report["observer_child_pid"] = process.pid
                if not executable:
                    report["original_pid"] = process.pid
                retain("debugger-start" if executable else "original-start", pid=process.pid)
                started = time.monotonic()
                last_sample, last_heartbeat = started, started
                pending = None
                operation = "starting"
                operation_start = started
                terminal_start = None
                sequence = 0
                while process.poll() is None:
                    now = time.monotonic()
                    state = read(root / "inferior.json") if executable else {}
                    old_state = report.get("debugger_state")
                    old_terminal = report["original_exit"]
                    old_pid = report.get("original_pid")
                    if executable:
                        observe_state(report, state)
                    if report["original_exit"] is not None and terminal_start is None:
                        terminal_start = now
                    observed_operation = state.get("operation", "starting")
                    if observed_operation != operation or state.get("operation_id") != report.get("operation_id"):
                        operation, operation_start = observed_operation, now
                        report["operation_id"] = state.get("operation_id")
                        retain("debugger-wait", operation=operation, original_pid=state.get("original_pid"),
                               helper_error=state.get("error"))
                    elif executable and old_state != report["debugger_state"]:
                        retain("debugger-state", operation=operation, helper_error=state.get("error"),
                               output=state.get("operation_output", "")[-1024:])
                    if state.get("original_pid") and state["original_pid"] != old_pid:
                        retain("original-start", pid=state["original_pid"])
                    if old_terminal is None and report["original_exit"] is not None:
                        retain("original-terminal", original_exit=report["original_exit"],
                               original_signal=report["original_signal"],
                               source=report["terminal_status_source"])
                    if pending and state.get("observation", {}).get("id") == pending[0]:
                        report["observation"] = state["observation"]
                        retain("observation-complete", observation=report["observation"])
                        pending = None
                        last_sample = now
                    if now - last_heartbeat >= min(30, sample_seconds):
                        report["snapshot"] = snapshot()
                        retain("progress", operation=operation if executable else "original-wait",
                               context=tail(journal, 1536), snapshot=report["snapshot"])
                        last_heartbeat = now
                    # run/continue are productive waits, not query/cohort
                    # deadlines. Sample the same live child and resume it.
                    if executable and terminal_start is None and not pending and operation in ("run", "continue") and now - last_sample >= sample_seconds:
                        sequence += 1
                        save(root / "observe.json", {"id": sequence, "initiator": "native-observer"})
                        report["snapshot"] = snapshot()
                        retain("interrupt-request", id=sequence, snapshot=report["snapshot"])
                        process.send_signal(signal.SIGINT)
                        pending = (sequence, now + operation_seconds)
                    # A GDB run/continue call can still be unwinding after
                    # its original exited. That is now control work, not a
                    # productive child wait. Start its unchanged budget at
                    # the observed terminal event, never at the child's start.
                    terminal_command = terminal_start is not None and operation in ("run", "continue")
                    control_start = terminal_start if terminal_command else operation_start
                    control_operation = "terminal-command-return" if terminal_command else operation
                    blocked = executable and (terminal_command or operation not in ("run", "continue")) and now - control_start >= operation_seconds
                    incomplete = pending and now >= pending[1]
                    if cancelled or blocked or incomplete:
                        report["observation_status"] = "cancelled" if cancelled else "incomplete"
                        report["cancel_signal"] = cancelled[0] if cancelled else None
                        report["error"] = "observer cancelled" if cancelled else "diagnostic operation did not complete within observation budget"
                        report["snapshot"] = snapshot()
                        report["control_operation"] = control_operation
                        report["cleanup_initiator"] = "native-observer:cancel" if cancelled else "native-observer:operation-budget"
                        retain("observation-incomplete", operation=control_operation, snapshot=report["snapshot"],
                               original_exit=report["original_exit"], debugger_exit=None,
                               helper_error=state.get("error"), initiator=report["cleanup_initiator"])
                        # One bounded interrupt opportunity even for an
                        # observer blocked before the helper's run call.
                        if executable and not pending and not cancelled:
                            process.send_signal(signal.SIGINT)
                            end = time.monotonic() + min(1, operation_seconds)
                            while process.poll() is None and time.monotonic() < end:
                                time.sleep(0.02)
                        break
                    time.sleep(0.02)
                interrupted = report["observation_status"] != "running"
                state = read(root / "inferior.json") if executable else {}
                # Only a real terminal observation made before cleanup
                # is original evidence. Cleanup's SIGKILL is separate.
                if executable:
                    observe_state(report, state)
                    report["debugger_exit"] = process.poll()
                    faults = state.get("signals", [])
                    report.update(faults=faults, terminated_by_debugger=state.get("terminated_by_debugger", False),
                                  debugger_core_policy=state.get("core_policy"),
                                  terminal_status_source=state.get("terminal_status_source"),
                                  observation=state.get("observation", report.get("observation")))
                    if state.get("terminal_status_source") and not state.get("terminated_by_debugger"):
                        terminal_signal = state.get("terminal_signal")
                        report.update(original_exit=128 + terminal_signal if terminal_signal else state.get("exit_code"),
                                      original_signal=terminal_signal)
                    if faults:
                        report["fault_signal"] = int(getattr(signal, faults[0]["signal"]))
                    report["debugger_status"] = "captured" if not interrupted and not state.get("error") and process.returncode == 0 and report["original_exit"] is not None else "failed"
                    report["error"] = report["error"] or state.get("error")
                    if report["debugger_status"] == "failed":
                        report["error"] = report["error"] or "debugger did not report an executed original child's terminal status"
                        if report["observation_status"] == "running":
                            report["observation_status"] = "failed"
                elif not interrupted:
                    report.update(original_exit=encoded(process.returncode),
                                  original_signal=-process.returncode if process.returncode < 0 else None,
                                  terminal_status_source="waitpid")
                retain("terminal-observation", original_exit=report["original_exit"],
                       original_signal=report["original_signal"], fault_signal=report["fault_signal"],
                       debugger_exit=report["debugger_exit"], observation_status=report["observation_status"])
                # Reaping an already-zombie signal helper is ordinary
                # cleanup, not evidence of a surviving live workload.
                alive = [row["pid"] for row in snapshot()["owned"]
                         if any(t["state"] not in ("Z", "X")
                                for t in row["threads"])]
                receipt = cleanup(process, ())
                report["cleanup"] = receipt
                if alive and receipt["killed"] and report["cleanup_initiator"] is None:
                    report["cleanup_initiator"] = "native-observer:surviving-descendants"
                    report["observation_status"] = "incomplete"
                    report["error"] = report["error"] or "owned descendants survived the observed leader"
                if receipt["remaining"] or receipt["errors"]:
                    report["observation_status"] = "incomplete"
                    report["error"] = report["error"] or "owned cleanup incomplete"
                if executable:
                    report["debugger_cleanup_exit"] = process.returncode
            output = (root / "stdout").read_bytes() if (root / "stdout").exists() else b""
            errors = (root / "stderr").read_bytes()
            if executable:
                report["debugger_log"] = tail(root / "debugger", 65536)
            if report["observation_status"] == "running":
                report["observation_status"] = "complete"
            code = 128 + report["fault_signal"] if report["fault_signal"] else report["original_exit"]
            if report["error"] or report["observation_status"] != "complete" or code is None:
                code = code or 125
            report.update(status=code, wrapper_exit=code, complete=True)
            retain("wrapper-terminal", status=code, original_exit=report["original_exit"],
                   debugger_exit=report["debugger_exit"], observation_status=report["observation_status"],
                   cleanup_initiator=report["cleanup_initiator"])
            return code, output, errors, report
    except BaseException as error:
        if process is not None:
            receipt = cleanup(process, ())
            if report is not None:
                report.update(error=f"observer exception: {type(error).__name__}: {error}",
                              observation_status="failed", cleanup=receipt,
                              cleanup_initiator="native-observer:exception", status=125,
                              wrapper_exit=125, complete=True)
                if report_path:
                    save(report_path, report)
        raise
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def positive(value):
    number = float(value)
    if not 0 < number < float("inf"):
        raise argparse.ArgumentTypeError("observation interval must be finite and positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True)
    parser.add_argument("--cohort", default="[]")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--debugger", default="gdb")
    parser.add_argument("--capture-only", action="store_true")
    parser.add_argument("--sample-seconds", type=positive, default=120)
    parser.add_argument("--operation-seconds", type=positive, default=5)
    parser.add_argument("--progress-env", choices=["FREN_ENUM_PROGRESS", "FREN_OWN_SPEC_PROGRESS"], default="FREN_ENUM_PROGRESS")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("an original command is required")
    try:
        code, stdout, stderr, report = run(command, os.environ, json.loads(args.cohort), args.workers,
            args.debugger, args.progress_env, report_path=Path(args.report), capture_only=args.capture_only,
            sample_seconds=args.sample_seconds, operation_seconds=args.operation_seconds)
    except Exception as error:
        print(f"native observer failed: {type(error).__name__}: {error}", file=sys.stderr)
        return 125
    sys.stdout.buffer.write(stdout)
    sys.stderr.buffer.write(stderr)
    if code and (not args.capture_only or report["error"]):
        sys.stderr.write("\nnative diagnostic: " + json.dumps(report, indent=2) + "\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
