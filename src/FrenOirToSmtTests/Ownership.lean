module

public import FrenOirToSmtTests.Support

public section
namespace FrenOirToSmtTests
open FrenOirToSmt

/-! Actual transport ownership, cancellation and cleanup controls. At the
group signal they check the kernel's state (the leader is still a waitable
child), not `/proc`; afterwards that production, not this harness, reaped
it. Cancellation is a real SIGTERM, raised in the thread that sends it, under a watch that this
harness holds so that the transport reports it instead of raising it. -/

private def signalSelf (sig : UInt32) : IO Unit :=
  Process.raiseSignal sig

private def waitable (pid : UInt32) : IO Bool := do
  match ← (Process.observeExit pid).toBaseIO with
  | .ok _ => return true
  | .error _ => return false

/-- Failure cleanup, conditional on an unreaped direct-child anchor: never
signal the old solver PID after production reaped it. -/
private def release (children : Array UInt32) : IO Unit := do
  for pid in children do
    if ← waitable pid then
      let _ ← Process.signalGroup pid Process.sigkill
      let _ ← Process.reap pid

private def check (name : String) (command : Array String) (script : String := "")
    (wallMs : Nat := 100) (expectedKind : String := "finished") (expectedCode : Option Int := some 0)
    (expectedState : String := "exited") (atCleanup : Bool := false)
    (cancelReady : Option System.FilePath := none) : IO Receipt := do
  let children ← IO.mkRef (#[] : Array UInt32)
  let observations ← IO.mkRef (#[] : Array (UInt32 × String))
  let hooks : Hooks := {
    onSpawn := fun pid => children.modify (·.push pid)
    beforeGroupSignal := fun pid => do
      -- Throws unless the leader is still this process's waitable child.
      let state ← Process.observeExit pid
      require ((← children.get).contains pid) "not an owned direct child"
      observations.modify (·.push (pid, if state == .running then "running" else "exited"))
      if atCleanup then
        -- Repeated cancellation at cleanup entry cannot release the leader
        -- or interrupt the anchored group signal and the following reap.
        signalSelf Process.sigterm
        signalSelf Process.sigterm }
  Process.watchBegin
  let sender ← IO.asTask (prio := .dedicated) do
    let some ready := cancelReady | return
    let limit := (← IO.monoMsNow) + 1000
    while !(← ready.pathExists) && (← IO.monoMsNow) < limit do
      IO.sleep 5
    unless ← ready.pathExists do throw (IO.userError "owned solver readiness failed")
    signalSelf Process.sigterm
    signalSelf Process.sigterm
  try
    let r ← transportWith hooks command script {wallMs, outputBytes := 1024, inputBytes := 1024}
      (reraise := false)
    if let .error e := sender.get then throw e
    let shown := s!"{name}: {reprStr r}; {← observations.get}"
    require (r.kind == expectedKind && r.exitCode == expectedCode) shown
    if atCleanup || cancelReady.isSome then
      require (r.reason == cancelReason) shown
    let seen ← observations.get
    require (seen.size == 1) shown
    require (seen.all (·.2 == expectedState)) shown
    -- The production transport, not this harness, must perform the reap.
    for pid in ← children.get do
      require (!(← waitable pid)) s!"{name}: production left the owned direct child waitable"
    evidence ("ownership-" ++ name) (Lean.Json.mkObj [("receipt", receiptJson r),
      ("ownership_checks", Lean.toJson (seen.map fun (pid, state) =>
        Lean.Json.mkObj [("pid", Lean.toJson pid.toNat), ("leader_still_waitable", true),
          ("leader_state", Lean.toJson state)]))])
    return r
  finally
    let _ ← IO.wait sender
    release (← children.get)
    let _ ← Process.watchEnd false

/-- An unexpected reaper must turn even an unsat response into an error,
without any remembered-group signal. Cancellation cannot mask the loss. -/
private def lostAnchor : IO Unit := do
  let children ← IO.mkRef (#[] : Array UInt32)
  let signals ← IO.mkRef 0
  let hooks : Hooks := {
    onSpawn := fun pid => children.modify (·.push pid)
    beforeGroupSignal := fun _ => signals.modify (· + 1)
    observe := fun pid => do
      if (← Process.observeExit pid) != .running then
        let _ ← Process.reap pid  -- Deliberate test-only loss, never production policy.
        signalSelf Process.sigterm
      Process.observeExit pid }
  Process.watchBegin
  try
    let limits : Limits := {wallMs := 1000, outputBytes := 1024, inputBytes := 1024}
    let r ← transportWith hooks (← fakeSolver "unsat") "" limits (reraise := false)
    require (r.kind == "error" && r.reason == lostReason && r.stdout == "unsat\n" &&
      (← signals.get) == 0 && (← Process.watchedSignal) == Process.sigterm) s!"lost anchor: {reprStr r}"
    evidence "ownership-lost-anchor-no-signal" (receiptJson r)
  finally
    release (← children.get)
    let _ ← Process.watchEnd false

def runOwnership : IO Unit := do
  let solver := (← sourceRoot) / ".lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5"
  let real ← check "real-cvc5-normal-unsat" #[solver.toString, "--lang=smt2"]
    "(set-logic ALL)\n(assert false)\n(check-sat)\n" (wallMs := 1000)
  require (real.stdout == "unsat\n") "real cvc5 unsat"
  let _ ← check "normal-nonzero" (← fakeSolver "nonzero") (wallMs := 1000) (expectedCode := some 7)
  let _ ← check "closed-streams-normal-exit" (← fakeSolver "closed-exit") (wallMs := 500)
  let directory ← IO.FS.createTempDir
  try
    let ready := directory / "pid"
    let _ ← check "repeated-running-cancellation" ((← fakeSolver "ready").push ready.toString)
      (wallMs := 2000) (expectedKind := "resource") (expectedCode := some (-9))
      (expectedState := "running") (cancelReady := some ready)
  finally
    IO.FS.removeDirAll directory
  let _ ← check "repeated-cleanup-entry-cancellation" (← fakeSolver "sleep") (expectedKind := "resource")
    (expectedCode := some (-9)) (expectedState := "running") (atCleanup := true)
  let _ ← check "exited-leader-with-pipe-holding-descendant" (← fakeSolver "orphan")
    (expectedKind := "resource") (wallMs := 500)
  lostAnchor
  IO.println "owned cleanup: six kernel waitability checks at group signals; normal exit, nonzero, closed streams, repeated running/cleanup cancellation and surviving descendant; lost anchor forbids signal and solver answer"

end FrenOirToSmtTests
