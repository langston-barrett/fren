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
        output = gdb.execute(command, to_string=True)
        state["operation_output"] = output[-8192:]
        state["completed_operation_id"] = state["operation_id"]
        save(root / "inferior.json", state)
        return output
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


def exited(event):
    # This is GDB's actual process-exit event, not a thread exit or an
    # inference from /proc. Publish before command hooks/unwinding/quit
    # can fail or block and prevent the caller's next convenience read.
    code = getattr(event, "exit_code", None)
    if code is not None:
        state.update(started=True, exit_code=code,
                     terminal_status_source="gdb", terminal_status_event="exited")
        save(root / "inferior.json", state)


def terminal_status():
    # These values are set by GDB on actual process termination. Reading
    # them does not require a live selected thread or infer status from a
    # previously observed signal. A thread exit alone is not process exit.
    if state["exit_code"] is not None or state["terminal_signal"] is not None:
        return True
    for key, name in [("terminal_signal", "_exitsignal"), ("exit_code", "_exitcode")]:
        value = gdb.convenience_variable(name)
        if value is not None and value.type.code != gdb.TYPE_CODE_VOID:
            state[key] = int(value)
            state["terminal_status_source"] = "gdb"
            state["started"] = True
            save(root / "inferior.json", state)
            return True
    return False


def transport_observation():
    """Read only this debugger and its current inferior; retain no memory bytes."""
    facts = {"kernel": os.uname().release, "gdb": gdb.VERSION}
    if sys.platform != "linux":
        return dict(facts, unavailable="Linux transport observation is unavailable")
    facts["debugger_status"] = [line for line in Path("/proc/self/status").read_text().splitlines()
                                if line.startswith(("Uid:", "Gid:", "CapEff:", "CapPrm:", "Seccomp:"))]
    facts["uid_map"] = Path("/proc/self/uid_map").read_text()[:256]
    save(root / "transport.json", facts)
    inferior = gdb.selected_inferior()
    pid = inferior.pid
    facts["inferior_pid"] = pid
    if not pid:
        return facts
    fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
    facts["inferior_state"] = fields[0]
    facts["inferior_ppid"] = int(fields[1])
    if facts["inferior_ppid"] != os.getpid():
        return dict(facts, unavailable="inferior is not this debugger's child")
    thread = gdb.selected_thread()
    facts["selected_ptid"] = thread.ptid if thread else None
    save(root / "transport.json", facts)
    # This exported native-test symbol supplies a real mapped code address.
    # Report lengths/errno only, never the original's memory contents.
    address = int(gdb.parse_and_eval("(void*)&fren_test_raise_abrt"))
    facts["address_source"] = "fren_test_raise_abrt"
    libc = ctypes.CDLL(None, use_errno=True)
    libc.ptrace.restype = ctypes.c_long
    libc.ptrace.argtypes = [ctypes.c_uint, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
    tid = thread.ptid[1] if thread else pid
    ctypes.set_errno(0)
    result = libc.ptrace(2, tid, address, None)  # PTRACE_PEEKDATA, owned inferior only.
    facts["peekdata"] = {"tid": tid, "returned_minus_one": result == -1, "errno": ctypes.get_errno()}
    if os.uname().machine == "x86_64":
        # ps_get_thread_area uses this same x86-64 fs_base register slot.
        ctypes.set_errno(0)
        result = libc.ptrace(3, tid, 21 * 8, None)  # PTRACE_PEEKUSER.
        facts["peekuser_fs_base"] = {"tid": tid, "returned_minus_one": result == -1,
                                     "errno": ctypes.get_errno()}
    try:
        directory = os.open(f"/proc/{pid}", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            # Pin this proc entry and recheck ownership before opening mem;
            # PID reuse cannot redirect the relative open to another task.
            with os.fdopen(os.open("stat", os.O_RDONLY, dir_fd=directory)) as entry:
                parent = int(entry.read().rsplit(")", 1)[1].split()[1])
            if parent != os.getpid():
                raise PermissionError("proc entry is not this debugger's child")
            fd = os.open("mem", os.O_RDONLY | os.O_CLOEXEC, dir_fd=directory)
            try:
                facts["new_proc_mem_read_bytes"] = len(os.pread(fd, 1, address))
            finally:
                os.close(fd)
        finally:
            os.close(directory)
    except OSError as error:
        facts["new_proc_mem_errno"] = error.errno
    facts["cached_proc_mem"] = []
    for entry in list(Path("/proc/self/fd").iterdir())[:256]:
        try:
            target = os.readlink(entry)
            if target.startswith(f"/proc/{pid}/") and target.endswith("/mem"):
                row = {"fd": int(entry.name), "target": target}
                try:
                    row["read_bytes"] = len(os.pread(int(entry.name), 1, address))
                except OSError as error:
                    row["errno"] = error.errno
                facts["cached_proc_mem"].append(row)
        except FileNotFoundError:
            pass
    save(root / "transport.json", facts)
    # Publish the raw kernel results before a GDB memory query can block.
    try:
        facts["gdb_read_bytes"] = len(inferior.read_memory(address, 1))
    except Exception as error:
        facts["gdb_read_error"] = str(error)
    return facts


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
            state["terminal_wait"] = {"pid": pid, "raw_status": status}
            save(root / "inferior.json", state)
            return
        if time.monotonic() >= deadline:
            raise RuntimeError("native child terminal wait did not complete")
        time.sleep(0.01)


gdb.events.stop.connect(stopped)
gdb.events.new_thread.connect(started_thread)
gdb.events.exited.connect(exited)
try:
    operation("configure")
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    for command in ["set pagination off", "set confirm off", "set print thread-events off",
                    "set print frame-arguments none",
                    "set disable-randomization off", "set follow-fork-mode parent",
                    "set detach-on-fork on"]:
        gdb.execute(command)
    for sig in sorted(fatal):
        gdb.execute(f"handle {sig} stop print pass")
    redirection = f" > {shlex.quote(str(root / 'stdout'))} 2> {shlex.quote(str(root / 'stderr'))} < /dev/null"
    # Supplying redirections to `starti` replaces its argument list too.
    # Keep the original --args rather than accidentally running no job.
    arguments = gdb.parameter("args")
    gdb.set_convenience_variable("_exitcode", None)
    gdb.set_convenience_variable("_exitsignal", None)
    # GDB initializes its proc-memory transport during inferior startup.
    # Setting its dumpability to zero earlier makes /proc/self/mem owned
    # by root and inaccessible to a non-root GDB. Its cached self-test then
    # selects ptrace, which cannot read our non-dumpable native child.
    # Stop this one original at its first instruction, before its runtime,
    # then protect GDB before continuing. There is no warmup child/replay.
    execute("starti " + arguments + redirection, "startup")
    inferior, thread = gdb.selected_inferior(), gdb.selected_thread()
    if not inferior.pid or thread is None or not thread.is_stopped():
        raise RuntimeError("native startup did not stop the original child")
    state["startup"] = {"pid": inferior.pid, "ptid": thread.ptid,
                        "pc": gdb.selected_frame().pc()}
    if sys.platform == "linux":
        state["startup"]["exe"] = os.readlink(f"/proc/{inferior.pid}/exe")
        state["startup"]["debugger_uid"] = os.geteuid()
        state["startup"]["debugger_capabilities"] = [
            line for line in Path("/proc/self/status").read_text().splitlines()
            if line.startswith(("CapPrm:", "CapEff:"))]
    operation("protect-debugger")
    # Piped collectors ignore RLIMIT_CORE, so preserve dumpability zero
    # during the workload for both this debugger and the native child.
    policy = {"rlimit_core": resource.getrlimit(resource.RLIMIT_CORE)}
    if sys.platform == "linux":
        libc = ctypes.CDLL(None, use_errno=True)
        state["startup"]["debugger_dumpable_before"] = libc.prctl(3, 0, 0, 0, 0)
        if libc.prctl(4, 0, 0, 0, 0) != 0:  # PR_SET_DUMPABLE
            raise OSError(ctypes.get_errno(), "cannot protect debugger from core collectors")
        policy["dumpable"] = libc.prctl(3, 0, 0, 0, 0)  # PR_GET_DUMPABLE
        if policy["dumpable"] != 0:
            raise RuntimeError("debugger remains dumpable")
        state["startup"]["debugger_dumpable_after"] = policy["dumpable"]
    state["core_policy"] = policy
    save(root / "inferior.json", state)
    if last_signal not in fatal:
        last_signal = None  # The initial instruction stop is observational.
        execute("continue", "run")
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
except BaseException as error:
    state["error"] = f"{type(error).__name__}: {error} (line {sys.exc_info()[2].tb_lineno})"
    state["failed_operation"] = {"operation": state.get("operation"),
                                 "operation_id": state.get("operation_id"), "error": state["error"]}
    # Preserve the original command error even if a subsequent diagnostic
    # query or GDB shutdown cannot finish. A budget error must not erase it.
    save(root / "inferior.json", state)
    terminal_status()
    operation("error-transport")
    try:
        state["transport"] = transport_observation()
    except Exception as detail:
        state["transport"] = dict(read(root / "transport.json"), unavailable=str(detail))
    save(root / "inferior.json", state)
    state["error_observations"] = {}
    for command in ["info threads", "info program", "p $_exitsignal", "show scheduler-locking"]:
        try:
            output = execute(command, "error-observation")
            state["error_observations"][command] = output[-2048:]
        except Exception as detail:
            state["error_observations"][command] = str(detail)
        save(root / "inferior.json", state)
finally:
    terminal_status()
    # The helper returning does not imply that the debugger has exited.
    # The outer observer still waits for that separate physical status.
    state["helper_complete"] = True
    operation("debugger-shutdown")
