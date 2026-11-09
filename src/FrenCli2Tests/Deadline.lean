module

public import FrenOirToSmt.Process

public section
namespace FrenCli2Tests.Deadline
open FrenOirToSmt

/-! The Fren2 test runner's deadline controller. The runner starts it as
`fren2_test --fren2-controller-run RUNNER-PID COMMAND...`, a process of its
own between the runner and the job, with a fixed 30-second deadline. It
runs the job in a new session, so that the job's PID names its process
group, and becomes a subreaper, so that the job's orphaned descendants in
that group are its children too. It observes the job's exit without reaping
it, so that the unreaped leader anchors the numeric group through the
group's SIGKILL; then it reaps the whole group. It ends the job when the job
exits, the deadline passes, the runner exits or it receives SIGINT, SIGTERM
or SIGHUP. -/

def productionMs : Nat := 30000

/-- Test-only: at cleanup entry and again after the group signal, send this
process SIGTERM, SIGINT and SIGHUP, which must not interrupt the cleanup. -/
private def cleanupSignals (label : String) : IO Unit := do
  IO.eprintln label
  (← IO.getStderr).flush
  for sig in [Process.sigterm, Process.sigint, Process.sighup] do
    Process.raiseSignal sig

/-- Run `command` under the deadline; the job's status, 124 at the deadline,
125 when the runner exits or control fails, or 128 plus a received signal.
`linux := false` is the unsupported-platform control. -/
def control (command : Array String) (ms : Nat) (parent : UInt32)
    (emit : String → IO Unit := fun s => do IO.eprintln ("fren2_test: " ++ s); (← IO.getStderr).flush)
    (linux : Bool := (System.Platform.target.splitOn "-").contains "linux") (testCleanup : Bool := false) : IO UInt32 := do
  unless linux do
    emit "Linux pidfds, subreapers and signal watches are required"
    return 125
  let mut pid? : Option UInt32 := none
  let mut reason := ""
  let mut result : UInt32 := 125
  -- Mutable state set inside `try` is lost when it throws, so each step
  -- reports its own outcome and the child is recorded outside any `try`.
  let start ← IO.monoMsNow
  let setup : IO UInt32 := do
    if command.isEmpty then throw (IO.userError "no command")
    if (← Process.parentPid) != parent then throw (IO.userError "runner disappeared before controller startup")
    Process.setSubreaper
    -- Recorded, never acted on in a handler: a signal cannot land between
    -- the spawn and retaining the child, or interrupt the owned cleanup.
    Process.watchBegin
    if (← Process.parentPid) != parent then throw (IO.userError "runner disappeared before controller startup")
    Process.spawnInherit command (session := true)
  match ← setup.toBaseIO with
  | .error e => reason := s!"control failure: {e}"
  | .ok pid =>
    pid? := some pid
    let wait : IO (String × UInt32) := do
      repeat
        if (← Process.watchedSignal) != 0 then return ("", 125)
        let now ← IO.monoMsNow
        if now >= start + ms then return ("deadline", 125)
        if (← Process.parentPid) != parent then return ("runner exited", 125)
        -- WNOWAIT keeps the leader's PID and process group anchored.
        let status ← Process.observeExit pid
        if status != .running then return ("", status.shell)
        IO.sleep (min 10 (start + ms - now)).toUInt32
      return ("", 125)
    match ← wait.toBaseIO with
    | .ok (r, code) =>
      reason := r
      result := code
    | .error e =>
      reason := s!"control failure: {e}"
      result := 125
  if testCleanup then cleanupSignals "cleanup-entry signals"
  if let some pid := pid? then
    -- The unreaped direct child anchors the numeric process group.
    let killed ← match ← (Process.signalGroup pid Process.sigkill).toBaseIO with
      | .ok _ => pure true
      | .error e =>
        reason := s!"control failure during cleanup: {e}"
        result := 125
        pure false
    if testCleanup then cleanupSignals "cleanup-blocked signals"
    -- The subreaper adopts orphaned same-group descendants. No further
    -- group signal follows once the leader is reaped.
    let reapAll : IO Unit := do
      repeat
        match ← Process.reapGroup pid killed with
        | none | some 0 => break
        | some _ => pure ()
    if let .error e ← reapAll.toBaseIO then
      reason := s!"control failure while reaping: {e}"
      result := 125
  let sig ← (Process.watchedSignal).toBaseIO
  let sig := match sig with | .ok s => s | .error _ => 0
  if sig != 0 && !reason.startsWith "control failure" then
    reason := s!"controller received signal {sig}"
    result := 128 + sig
  if !reason.isEmpty then
    emit reason
    if reason == "deadline" then return 124
    if reason == "runner exited" then return 125
  return result

end FrenCli2Tests.Deadline
