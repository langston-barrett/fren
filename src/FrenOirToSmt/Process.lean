module

public section
namespace FrenOirToSmt.Process

/-! Process ownership primitives (`c/fren2_process.c`) that Lean's
`IO.Process` lacks. The bounded solver transport and the Fren2 test runner's
deadline controller own a child started with `setsid`, so that its PID is
also its process group's ID. They observe its exit without reaping it, keep
it unreaped through the last group signal, so that the numeric group cannot
be reused, and only then reap it. -/

/-- How a child stands, from `observeExit` or `reap`. -/
inductive Status where
  | running
  | exited (code : UInt8)
  | signaled (signal : UInt8)
  deriving Repr, BEq, Inhabited

def Status.decode (raw : UInt32) : Status :=
  if raw == 0xFFFFFFFF then .running
  else if raw < 0x100 then .exited raw.toUInt8
  else .signaled (raw &&& 0xFF).toUInt8

/-- A shell-style status: the exit code, or 128 plus the signal. -/
def Status.shell : Status → UInt32
  | .running => 125
  | .exited code => code.toUInt32
  | .signaled sig => 128 + sig.toUInt32

/-- A Python-style return code: the exit code, or minus the signal. -/
def Status.returnCode? : Status → Option Int
  | .running => none
  | .exited code => some code.toNat
  | .signaled sig => some (-(sig.toNat : Int))

def sigint : UInt32 := 2
def sigkill : UInt32 := 9
def sigterm : UInt32 := 15
def sighup : UInt32 := 1
def sigcont : UInt32 := 18
def sigstop : UInt32 := 19
def sigchld : UInt32 := 17

@[extern "fren2_spawn"] private opaque spawnRaw (argv : @& Array String) (session pipes : Bool) :
  IO (Array UInt32)

/-- A child with pipes for its stdin, stdout and stderr: plain descriptors
that their owner must close (`closeFd`). -/
structure Piped where
  pid : UInt32
  stdin : UInt32
  stdout : UInt32
  stderr : UInt32

/-- Spawn `argv` (no shell; `argv[0]` is searched on PATH), in a new session
when `session`, with its standard streams on new pipes. SIGPIPE, SIGINT,
SIGTERM and SIGHUP start at their defaults and no signal is blocked. -/
def spawnPiped (argv : Array String) (session : Bool) : IO Piped := do
  let #[pid, stdin, stdout, stderr] ← spawnRaw argv session true
    | throw (IO.userError "spawn: unexpected result")
  return ⟨pid, stdin, stdout, stderr⟩

/-- Spawn as `spawnPiped`, inheriting this process's standard streams. -/
def spawnInherit (argv : Array String) (session : Bool) : IO UInt32 := do
  let #[pid] ← spawnRaw argv session false | throw (IO.userError "spawn: unexpected result")
  return pid

/-- Poll at most `timeoutMs`, then one non-blocking `read` of at most `max`
bytes: `none` if nothing arrived, `some` bytes, empty at end of file. -/
@[extern "fren2_fd_read"] opaque readFd (fd : UInt32) (max : USize) (timeoutMs : UInt32) :
  IO (Option ByteArray)
/-- Poll at most `timeoutMs`, then write what fits of `bytes` from `offset`:
the count written, possibly 0. A closed reader (EPIPE) is an error. -/
@[extern "fren2_fd_write"] opaque writeFd (fd : UInt32) (bytes : @& ByteArray) (offset : USize)
  (timeoutMs : UInt32) : IO USize

@[extern "fren2_observe_exit"] private opaque observeExitRaw (pid : UInt32) : IO UInt32
/-- `waitid(WEXITED | WNOHANG | WNOWAIT)`: the child's exit, leaving it
waitable. Throws if the PID is no longer a waitable child of this process. -/
def observeExit (pid : UInt32) : IO Status := return .decode (← observeExitRaw pid)

/-- `killpg`; `pgid = 0` is the caller's own group. False if no such group. -/
@[extern "fren2_signal_group"] opaque signalGroup (pgid sig : UInt32) : IO Bool
/-- `kill` of one PID. False if no such process. -/
@[extern "fren2_signal_process"] opaque signalProcess (pid sig : UInt32) : IO Bool

/-- `raise`: signal the calling thread, so that the signal is handled before
this returns. A `signalProcess` of this process's own PID may be handled
later, by another thread. -/
@[extern "fren2_raise"] opaque raiseSignal (sig : UInt32) : IO Unit

/-- Test-only: ignore `sig` (true) or restore its default (false). -/
@[extern "fren2_set_ignored"] opaque setIgnored (sig : UInt32) (ignore : Bool) : IO Unit

@[extern "fren2_reap"] private opaque reapRaw (pid : UInt32) : IO UInt32
/-- Blocking `waitpid` of one child: its final status. -/
def reap (pid : UInt32) : IO Status := return .decode (← reapRaw pid)

@[extern "fren2_reap_group"] private opaque reapGroupRaw (pgid : UInt32) (block : Bool) : IO UInt32
/-- `waitpid(-pgid)`: `some pid` reaped, `some 0` if none has exited (only
when not blocking), `none` when no child of the group is left. -/
def reapGroup (pgid : UInt32) (block : Bool) : IO (Option UInt32) := do
  let raw ← reapGroupRaw pgid block
  return if raw == 0xFFFFFFFF then none else some raw

@[extern "fren2_parent_pid"] opaque parentPid : IO UInt32
/-- `PR_SET_CHILD_SUBREAPER` (Linux). -/
@[extern "fren2_set_subreaper"] opaque setSubreaper : IO Unit
/-- Kill and reap all children adopted by the dedicated subreaper. -/
@[extern "fren2_reap_adopted"] opaque reapAdopted : IO Unit
@[extern "fren2_close_fd"] opaque closeFd (fd : UInt32) : IO Unit
/-- Test-only inheritable descriptor. -/
@[extern "fren2_test_open_fd"] opaque testOpenFd : IO UInt32
/-- A pidfd for one process (Linux). -/
@[extern "fren2_pidfd_open"] opaque pidfdOpen (pid : UInt32) : IO UInt32
/-- `pidfd_send_signal`. False (ESRCH) once the process has been reaped. -/
@[extern "fren2_pidfd_signal"] opaque pidfdSignal (fd sig : UInt32) : IO Bool

/-- Open a watch for SIGINT, SIGTERM and SIGHUP: while any watch is open, the
first such signal is recorded instead of taking its usual effect (one that
was ignored stays ignored), and SIGCHLD is at its default, so that no owned
child is reaped behind its owner's back. -/
@[extern "fren2_watch_begin"] opaque watchBegin : IO Unit
/-- The first signal recorded since the watches opened, or 0. -/
@[extern "fren2_watched_signal"] opaque watchedSignal : IO UInt32
/-- Close a watch, returning the recorded signal or 0. The last one restores
the previous dispositions, forgets the signal and, with `reraise`, raises it
again under them. -/
@[extern "fren2_watch_end"] opaque watchEnd (reraise : Bool) : IO UInt32

end FrenOirToSmt.Process
