module

public import FrenOirToSmt.Types
public import FrenOirToSmt.Process

public section
namespace FrenOirToSmt

/-- Exit and complete protocol are checked before recognizing an answer. A
solver diagnostic, extra answer or nonzero exit can never become Unsat. -/
@[expose] def classify (exitCode : Option Int) (stdout stderr kind reason : String) : Outcome :=
  if kind == "resource" then .resourceExhausted reason
  else if kind != "finished" then .error reason
  else if exitCode != some 0 then .error "solver exited unsuccessfully"
  else if !stderr.trimAscii.toString.isEmpty then .error "solver stderr diagnostic"
  else match stdout.trimAscii.toString with
    | "sat" => .sat
    | "unsat" => .unsat
    | "unsupported" => .unsupported "cvc5 reported unsupported"
    | "unknown" => .unknown "cvc5 returned unknown under the configured limits"
    | _ => .error "invalid solver answer protocol"

/-- Paths belong to the source tree shipped with the Lake executable. Missing
assets are explicit transport errors; this code never downloads a solver. -/
def sourceRoot : IO System.FilePath := do
  let app ← IO.appPath
  let some dir := app.parent | throw (IO.userError "no executable directory")
  IO.FS.realPath (dir / ".." / ".." / "..")

def solverCommand (limits : Limits) : IO (Array String) := do
  let root ← sourceRoot
  return #[(root / ".lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5").toString,
    "--lang=smt2", s!"--tlimit-per={limits.solverMs}", s!"--rlimit-per={limits.solverResources}"]

/-- Test-only observation points of one transport. Production uses the
defaults; the owned cleanup controls check the kernel state at the group
signal and simulate a lost leader through `observe`. -/
structure Hooks where
  onSpawn : UInt32 → IO Unit := fun _ => pure ()
  beforeGroupSignal : UInt32 → IO Unit := fun _ => pure ()
  observe : UInt32 → IO Process.Status := Process.observeExit

def deadlineReason : String := "outer wall deadline"
def outputReason : String := "combined solver output limit"
def cancelReason : String := "transport cancelled"
def lostReason : String := "transport error: solver leader is no longer waitable"

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

def hex (bytes : ByteArray) : String :=
  bytes.foldl (fun s b => (s.push (hexDigit (b >>> 4))).push (hexDigit (b &&& 15))) ""

private def allFinished (tasks : Array (Task α)) : BaseIO Bool :=
  tasks.allM IO.hasFinished

/-- Write the script, then close the solver's stdin. A closed reader (EPIPE;
SIGPIPE is ignored) ends the input, as an early exit does. -/
private def feed (fd : UInt32) (bytes : ByteArray) : IO Unit := do
  try Process.writeFd fd bytes catch _ => pure ()
  Process.closeFd fd

/-- Decode, replacing each byte that starts no valid UTF-8 character with
U+FFFD; the exact bytes are kept separately as hex. -/
def lossyUtf8 (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for _ in [:bytes.size] do
    if i >= bytes.size then break
    let mut step := 0
    for n in [1:5] do
      if step == 0 && i + n <= bytes.size then
        if let some s := String.fromUTF8? (bytes.extract i (i + n)) then
          if s.length == 1 then
            out := out ++ s
            step := n
    if step == 0 then
      out := out.push '�'
      step := 1
    i := i + step
  return out

/-- One bounded solver process. The command runs with no shell in a new
session, so its PID names its process group. Its stdin gets the script; its
stdout and stderr are read together up to `outputBytes`. It ends at the wall
deadline, the output limit or a watched cancellation signal, or when it has
closed every stream and exited. Its exit is observed without reaping it, so
that its unreaped PID keeps the numeric group from reuse through the group's
final SIGKILL, even after a normal exit; only then is it reaped. If it is no
longer waitable, no group is signalled and no answer is reported.

SIGINT, SIGTERM and SIGHUP that arrive meanwhile cancel it, after which it
is killed and reaped as above. With `reraise`, and no enclosing watch, the
signal then takes the effect it would have had. -/
def transportWith (hooks : Hooks) (command : Array String) (script : String) (limits : Limits := {})
    (binding : String := "") (reraise : Bool := true) : IO Receipt := do
  let started ← IO.monoMsNow
  let failure (message : String) : IO Receipt := do
    return ⟨command, none, "", "", "", "", (← IO.monoMsNow) - started, message, .error message, script, binding, "error", limits⟩
  if limits.wallMs == 0 || limits.wallMs > 10000 || limits.solverMs == 0 ||
      limits.solverResources == 0 || limits.outputBytes == 0 || limits.outputBytes > 1048576 ||
      limits.inputBytes == 0 || limits.inputBytes > 1048576 then
    return ← failure "invalid bounded solver limits"
  if command.isEmpty || command.any (·.contains (Char.ofNat 0)) then
    return ← failure "invalid bounded transport configuration"
  if script.utf8ByteSize > limits.inputBytes then
    return ⟨command, none, "", "", "", "", 0, "script input limit", .resourceExhausted "script input limit", script, binding, "resource", limits⟩
  try Process.watchBegin catch e => return ← failure ("transport setup: " ++ e.toString)
  let deadline := started + limits.wallMs
  let budget ← IO.mkRef limits.outputBytes
  let overflow ← IO.mkRef false
  let outBuf ← IO.mkRef ByteArray.empty
  let errBuf ← IO.mkRef ByteArray.empty
  -- Each stream has its own reader; both draw on one combined byte budget.
  -- Each closes its descriptor; none is closed under a blocked reader.
  let reader (fd : UInt32) (buf : IO.Ref ByteArray) : IO Unit := do
    try
      repeat
        let chunk ← Process.readFd fd 4096
        if chunk.isEmpty then break
        let take ← budget.modifyGet fun avail => (min avail chunk.size, avail - min avail chunk.size)
        buf.modify (· ++ chunk.extract 0 take)
        if chunk.size > take then
          overflow.set true
          break
    finally
      Process.closeFd fd
  let mut reason := ""
  let mut exitCode : Option Int := none
  let mut lost := false
  let mut pid? : Option UInt32 := none
  let mut readers : Array (Task (Except IO.Error Unit)) := #[]
  -- Mutable state set inside `try` is lost when it throws: the child is
  -- recorded outside it, so that cleanup always finds it.
  match ← (Process.spawnPiped command (session := true)).toBaseIO with
  | .error e => reason := "transport error: " ++ e.toString
  | .ok child =>
    pid? := some child.pid
    readers := #[← IO.asTask (prio := .dedicated) (feed child.stdin script.toUTF8),
      ← IO.asTask (prio := .dedicated) (reader child.stdout outBuf),
      ← IO.asTask (prio := .dedicated) (reader child.stderr errBuf)]
    let loop : IO String := do
      hooks.onSpawn child.pid
      repeat
        if (← Process.watchedSignal) != 0 then return cancelReason
        let now ← IO.monoMsNow
        if now >= deadline then return deadlineReason
        if ← overflow.get then return outputReason
        -- A child can close both output streams and keep computing.
        if ← allFinished readers then
          if (← hooks.observe child.pid) != .running then return ""
        IO.sleep (min 10 (deadline - now)).toUInt32
      return ""
    match ← loop.toBaseIO with
    | .ok r => reason := r
    | .error e => reason := "transport error: " ++ e.toString
  if let some pid := pid? then
    match ← (hooks.observe pid).toBaseIO with
    | .error _ =>
      -- Lost ownership forbids signalling a possibly reused group.
      lost := true
      reason := lostReason
    | .ok _ =>
      let cleanup : IO (Option Int) := do
        hooks.beforeGroupSignal pid
        let _ ← Process.signalGroup pid Process.sigkill
        return (← Process.reap pid).returnCode?
      match ← cleanup.toBaseIO with
      | .ok code => exitCode := code
      | .error e => reason := "transport error during cleanup: " ++ e.toString
    -- The group is gone, so its pipes are closed unless a member escaped it.
    let graceEnd := (← IO.monoMsNow) + 200
    while !(← allFinished readers) && (← IO.monoMsNow) < graceEnd do
      IO.sleep 5
  if (← Process.watchedSignal) != 0 && !lost then
    reason := cancelReason
  let out ← outBuf.get
  let err ← errBuf.get
  let (stdout, stderr) ← match String.fromUTF8? out, String.fromUTF8? err with
    | some o, some e => pure (o, e)
    | _, _ =>
      reason := "transport error: non-UTF-8 solver output"
      pure (lossyUtf8 out, lossyUtf8 err)
  let kind := if reason.isEmpty then "finished"
    else if [deadlineReason, outputReason, cancelReason].contains reason then "resource" else "error"
  let receipt : Receipt := ⟨command, exitCode, stdout, stderr, hex out, hex err,
    (← IO.monoMsNow) - started, reason, classify exitCode stdout stderr kind reason, script, binding, kind, limits⟩
  let _ ← Process.watchEnd reraise
  return receipt

/-- Low-level transport is exposed for owned failure controls. The source
producer/solver entry never accepts its output as an admission witness. -/
def transport (command : Array String) (script : String) (limits : Limits := {}) (binding : String := "") : IO Receipt :=
  transportWith {} command script limits binding

theorem classify_nonzero (code : Int) (h : code ≠ 0) :
    classify (some code) "unsat" "" "finished" "" = .error "solver exited unsuccessfully" := by
  simp [classify, h]

theorem classify_resource (code : Option Int) (out err reason : String) :
    classify code out err "resource" reason = .resourceExhausted reason := rfl

end FrenOirToSmt
