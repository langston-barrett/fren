"""GDB-side capture for native_diagnostic.py; only debugs its own inferior."""
import json
import os
import shlex
from pathlib import Path

import gdb

root = Path(os.environ["FREN_NATIVE_DIAG_DIR"])
state = {"started": False, "exit_code": None, "terminal_signal": None,
         "terminated_by_debugger": False, "signals": [], "error": None}
fatal = {"SIGSEGV", "SIGBUS", "SIGILL", "SIGABRT", "SIGFPE"}
last_signal = None


def stopped(event):
    global last_signal
    last_signal = event.stop_signal if isinstance(event, gdb.SignalEvent) else None


def started(_event):
    state["started"] = True


def exited(event):
    state["exit_code"] = getattr(event, "exit_code", None)


gdb.events.stop.connect(stopped)
gdb.events.new_thread.connect(started)
gdb.events.exited.connect(exited)
try:
    for command in ["set pagination off", "set confirm off", "set print thread-events off",
                    "set print frame-arguments none",
                    "set disable-randomization off", "set follow-fork-mode parent",
                    "set detach-on-fork on"]:
        gdb.execute(command)
    for sig in sorted(fatal):
        gdb.execute(f"handle {sig} stop print pass")
    redirection = f" > {shlex.quote(str(root / 'stdout'))} 2> {shlex.quote(str(root / 'stderr'))} < /dev/null"
    # Supplying redirections to `run` replaces its argument list too.
    # Keep the original --args rather than accidentally running no job.
    arguments = gdb.parameter("args")
    gdb.execute("run " + arguments + redirection)
    while gdb.selected_inferior().pid:
        if last_signal in fatal:
            sig = last_signal
            receiving_thread = gdb.selected_thread()
            fault = {"signal": sig, "siginfo": None, "backtrace": None}
            state["signals"].append(fault)
            for key, command in [("siginfo", "p $_siginfo"), ("backtrace", "thread apply all bt 32")]:
                try:
                    fault[key] = gdb.execute(command, to_string=True)
                except Exception as error:
                    state["error"] = f"{key} unavailable: {error}"
            # Deliver the original signal, rather than replacing it with
            # a successful debugger exit. A returning/repeating handler
            # cannot erase the first fault or create an infinite replay.
            # The runtime may return from a first SIGSEGV after resetting
            # its handler. Allow the next signal to terminate it normally.
            if len(state["signals"]) >= 8:
                state["error"] = "repeated fatal signal; terminating this inferior"
                state["terminated_by_debugger"] = True
                gdb.execute("kill")
                break
            if receiving_thread.is_valid():
                receiving_thread.switch()
        gdb.execute("continue")
    if not gdb.selected_inferior().pid:
        try:
            state["terminal_signal"] = int(gdb.parse_and_eval("$_exitsignal"))
        except gdb.error:
            pass  # A normal exit has no $_exitsignal.
except Exception as error:
    state["error"] = str(error)
finally:
    (root / "inferior.json").write_text(json.dumps(state, indent=2) + "\n")
