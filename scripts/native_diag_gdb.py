"""GDB-side capture for native_diagnostic.py; only debugs its own inferior."""
import ctypes
import json
import os
import resource
import shlex
import sys
import time
from pathlib import Path

import gdb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from native_observer import read, save

root = Path(os.environ["FREN_NATIVE_DIAG_DIR"])
state = {"started": False, "exit_code": None, "terminal_signal": None,
         "terminated_by_debugger": False, "signals": [], "error": None}
fatal = {"SIGSEGV", "SIGBUS", "SIGILL", "SIGABRT", "SIGFPE"}
last_signal = None


def operation(name):
    state["operation"] = name
    state["operation_id"] = state.get("operation_id", 0) + 1
    save(root / "inferior.json", state)


def execute(command, name):
    operation(name)
    try:
        return gdb.execute(command, to_string=True)
    except KeyboardInterrupt:
        if not (root / "observe.json").exists():
            raise
        return ""


def stopped(event):
    global last_signal
    state["started"] = True
    state["original_pid"] = gdb.selected_inferior().pid
    last_signal = event.stop_signal if isinstance(event, gdb.SignalEvent) else None
    save(root / "inferior.json", state)


def started_thread(_event):
    pid = gdb.selected_inferior().pid
    if pid and not state.get("original_pid"):
        state.update(started=True, original_pid=pid)
        save(root / "inferior.json", state)


def terminal_status():
    # These values are set by GDB on actual process termination. Reading
    # them does not require a live selected thread or infer status from a
    # previously observed signal. A thread exit alone is not process exit.
    for key, name in [("terminal_signal", "_exitsignal"), ("exit_code", "_exitcode")]:
        value = gdb.convenience_variable(name)
        if value is not None and value.type.code != gdb.TYPE_CODE_VOID:
            state[key] = int(value)
            state["terminal_status_source"] = "gdb"
            state["started"] = True
            save(root / "inferior.json", state)
            return True
    return False


def reap_terminal(pid):
    # Linux GDB can remove a zombie leader before its final wait status
    # arrives. With no threads left it reports NO_RESUMED, then only
    # reaps that leader during quit. Wait for this exact GDB-owned child
    # here instead; never infer process status from the earlier fault.
    deadline = time.monotonic() + 2
    while True:
        waited, status = os.waitpid(pid, os.WNOHANG)
        if waited:
            if os.WIFSIGNALED(status):
                state["terminal_signal"] = os.WTERMSIG(status)
            elif os.WIFEXITED(status):
                state["exit_code"] = os.WEXITSTATUS(status)
            else:
                raise RuntimeError("native child wait did not report termination")
            state["terminal_status_source"] = "waitpid"
            save(root / "inferior.json", state)
            return
        if time.monotonic() >= deadline:
            raise RuntimeError("native child terminal wait did not complete")
        time.sleep(0.01)


gdb.events.stop.connect(stopped)
gdb.events.new_thread.connect(started_thread)
try:
    operation("configure")
    # Protect this debugger too, not only its native inferior. Linux's
    # piped collectors ignore RLIMIT_CORE even when it is zero.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    policy = {"rlimit_core": resource.getrlimit(resource.RLIMIT_CORE)}
    if sys.platform == "linux":
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.prctl(4, 0, 0, 0, 0) != 0:  # PR_SET_DUMPABLE
            raise OSError(ctypes.get_errno(), "cannot protect debugger from core collectors")
        policy["dumpable"] = libc.prctl(3, 0, 0, 0, 0)  # PR_GET_DUMPABLE
        if policy["dumpable"] != 0:
            raise RuntimeError("debugger remains dumpable")
    state["core_policy"] = policy
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
    gdb.set_convenience_variable("_exitcode", None)
    gdb.set_convenience_variable("_exitsignal", None)
    execute("run " + arguments + redirection, "run")
    previous_threads = None
    while not terminal_status():
        sig, last_signal = last_signal, None
        request = read(root / "observe.json")
        if request and sig in (None, "SIGINT"):
            # The supervisor interrupted this same original child. This
            # stop is observational, never a native product fault. Drop
            # only our interrupt before resuming the original invocation.
            state["observation"] = {"id": request["id"], "initiator": request["initiator"]}
            state["observation"]["backtrace"] = execute("thread apply all bt 8", "observation-backtrace")
            (root / "observe.json").unlink()
            save(root / "inferior.json", state)
            execute("signal 0", "continue")
            previous_threads = None
            continue
        if sig is not None:
            previous_threads = None
        if sig in fatal:
            fault = {"signal": sig, "siginfo": None, "backtrace": None}
            state["signals"].append(fault)
            save(root / "inferior.json", state)
            for key, command in [("siginfo", "p $_siginfo"), ("backtrace", "thread apply all bt 32")]:
                try:
                    fault[key] = execute(command, key)
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
            # `thread apply all` restores the receiving thread itself.
            # Do not retain a Python thread object across process teardown.
        elif sig is None:
            live = [t for t in gdb.selected_inferior().threads() if t.is_stopped()]
            identities = tuple(t.global_num for t in live)
            if not live:
                if gdb.selected_inferior().threads():
                    raise RuntimeError("debugger returned with running threads but no stop")
                pid = gdb.selected_inferior().pid
                if sys.platform != "linux" or not pid:
                    raise RuntimeError("debugger stopped without threads or terminal status")
                operation("terminal-reap")
                reap_terminal(pid)
                break
            if identities == previous_threads:
                raise RuntimeError("debugger stopped without thread progress or terminal status")
            previous_threads = identities if sig is None else None
            live[0].switch()
            del live
        execute("continue", "continue")
except Exception as error:
    state["error"] = f"{type(error).__name__}: {error} (line {sys.exc_info()[2].tb_lineno})"
    for command in ["info threads", "info program", "p $_exitsignal", "show scheduler-locking"]:
        try:
            gdb.write(gdb.execute(command, to_string=True))
        except Exception as detail:
            gdb.write(f"{command}: {detail}\n")
finally:
    operation("finished")
