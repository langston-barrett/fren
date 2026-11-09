module

public import FrenCli2Tests.Command
public import FrenCli2Tests.Deadline

public section
namespace FrenCli2Tests.Deadline
open FrenOirToSmt

/-! The deadline controller's process-level regression, run by `fren_test`'s
`fren2Deadlines` job as `fren2_test --fren2-deadline-controls`. Fixtures are
`fren2_test --fren2-deadline-fixture MODE`. Each fixture hands over its
identity: it writes its PID to a file and stays blocked until acknowledged,
so the harness's pidfd for that PID names the fixture itself. The harness
never has to reacquire an identity from a numeric PID later. -/

def identitiesVar : String := "FREN2_TEST_IDENTITIES"

private def stderrLine (s : String) : IO Unit := do
  IO.eprintln s
  (← IO.getStderr).flush

/-- Publish this process's identity and wait for its acknowledgement. -/
def publish (role : String) : IO Unit := do
  let some dir ← IO.getEnv identitiesVar | throw (IO.userError "no identity directory")
  let pid ← IO.Process.getPID
  let dir : System.FilePath := dir
  IO.FS.writeFile (dir / s!".{pid}.tmp") s!"{role} {pid}\n"
  IO.FS.rename (dir / s!".{pid}.tmp") (dir / s!"{pid}.id")
  while !(← (dir / s!"{pid}.ack").pathExists) do IO.sleep 5

private def forever : IO Unit := do
  repeat IO.sleep 1000

private def spawnSelf (args : Array String) (stdio : IO.Process.Stdio := .inherit) :
    IO (IO.Process.Child {stdin := .null, stdout := stdio, stderr := stdio}) := do
  IO.Process.spawn {cmd := (← IO.appPath).toString, args, stdin := .null, stdout := stdio, stderr := stdio}

def fixture (mode : String) (args : List String) : IO UInt32 := do
  if mode == "foreign" then
    IO.sleep 20000
    return 0
  if mode == "descendant" then
    publish "descendant"
    forever
  publish "leader"
  match mode with
  | "success" =>
    IO.println "fixture stdout"
    (← IO.getStdout).flush
    stderrLine "fixture stderr"
    return 0
  | "context" =>
    IO.println (Lean.Json.arr #[Lean.toJson (← IO.currentDir).toString, Lean.toJson args,
      Lean.toJson ((← IO.getEnv "FREN2_TEST_MARKER").getD "")]).compress
    return 0
  | "stream" =>
    IO.println "stream ready"
    (← IO.getStdout).flush
    forever
  | "failure" => return 7
  | "signal" =>
    let _ ← Process.signalProcess (← IO.Process.getPID) Process.sigterm
    pure ()
  | "orphan" | "stopped" =>
    let child ← spawnSelf #["--fren2-deadline-fixture", "descendant"]
    let some dir ← IO.getEnv identitiesVar | return 125
    while !(← (System.FilePath.mk dir / s!"{child.pid}.ack").pathExists) do IO.sleep 5
    if mode == "orphan" then return 0
    let _ ← Process.signalGroup 0 Process.sigstop
    pure ()
  | _ => pure ()
  forever
  return 0

private def dead (fd : UInt32) : IO Unit := do
  -- A held pidfd cannot silently change identity after PID reuse.
  let info ← IO.FS.readFile s!"/proc/self/fdinfo/{fd}"
  require ((info.splitOn "\n").contains "Pid:\t-1") s!"owned process was not reaped: {info}"

/-- Claim the next identity, open a pidfd for it while the fixture is still
blocked, then acknowledge it. -/
def receive (dir : System.FilePath) (role : String)
    (beforeAck : UInt32 → IO Unit := fun _ => pure ()) : IO UInt32 := do
  let limit := (← IO.monoMsNow) + 2000
  repeat
    let entries := (← dir.readDir).filter (·.path.extension == some "id")
    if let some entry := entries[0]? then
      let content ← IO.FS.readFile entry.path
      IO.FS.removeFile entry.path
      let some pid := (match content.splitOn " " with
        | [r, p] => if r == role && p.endsWith "\n" then (p.dropEnd 1).toString.toNat? else none
        | _ => none) | throw (IO.userError "incomplete fixture identity")
      let fd ← Process.pidfdOpen pid.toUInt32
      try
        beforeAck pid.toUInt32
        IO.FS.writeFile (dir / s!"{pid}.ack") ""
      catch e =>
        Process.closeFd fd
        throw e
      return fd
    if (← IO.monoMsNow) >= limit then throw (IO.userError s!"no {role} identity")
    IO.sleep 5
  throw (IO.userError "unreachable")

private abbrev Piped := IO.Process.Child {stdin := .null, stdout := .piped, stderr := .piped}

/-- Wait at most `ms` for exit and both streams' end; the status is read
with `waitpid`, so a signal is distinguished from an exit code. -/
private def finish (p : Piped) (expected : Process.Status) (ms : Nat := 4000) : IO (String × String) := do
  let out ← IO.asTask (prio := .dedicated) p.stdout.readToEnd
  let err ← IO.asTask (prio := .dedicated) p.stderr.readToEnd
  let limit := (← IO.monoMsNow) + ms
  while (← Process.observeExit p.pid) == .running || !(← IO.hasFinished out) || !(← IO.hasFinished err) do
    if (← IO.monoMsNow) >= limit then
      throw (IO.userError s!"process {p.pid} did not finish")
    IO.sleep 5
  let status ← Process.reap p.pid
  let out ← IO.ofExcept out.get
  let err ← IO.ofExcept err.get
  require (status == expected) s!"status {reprStr status}, expected {reprStr expected}: {out}{err}"
  IO.println s!"fixture status={status.shell}"
  return (out, err)

private def has (s part : String) : Bool := (s.splitOn part).length > 1

private def controlsIn (tmp : System.FilePath) : IO UInt32 := do
  let self ← IO.appPath
  let me ← IO.Process.getPID
  let ids := tmp / "identities"
  IO.FS.createDirAll ids
  let env := #[(identitiesVar, some ids.toString), ("FREN2_TEST_MARKER", some "inherited")]
  let processes ← IO.mkRef (#[] : Array Piped)
  let identities ← IO.mkRef (#[] : Array UInt32)
  let spawn (args : Array String) : IO Piped := do
    let p ← IO.Process.spawn {cmd := self.toString, args, env, stdin := .null, stdout := .piped, stderr := .piped}
    processes.modify (·.push p)
    return p
  let take (role : String) : IO UInt32 := do
    let fd ← receive ids role
    identities.modify (·.push fd)
    return fd
  let invoke (mode : String) (ms : Nat := 350) : IO (Piped × UInt32) := do
    let p ← spawn #["--fren2-controller-test", toString ms, toString me, self.toString,
      "--fren2-deadline-fixture", mode]
    return (p, ← take "leader")
  let mut stoppedMs := 0
  try
    IO.println "controls: normal success, status and streams"
    let (p, leader) ← invoke "success"
    let (out, err) ← finish p (.exited 0); dead leader
    require (out == "fixture stdout\n" && err == "fixture stderr\n") s!"streams: {out} {err}"
    let (p, leader) ← invoke "context"
    let (out, _) ← finish p (.exited 0); dead leader
    let expected := Lean.Json.arr #[Lean.toJson (← IO.currentDir).toString,
      Lean.toJson ["--fren2-deadline-fixture", "context"], "inherited"]
    require (out.trimAscii.toString == expected.compress) s!"context: {out}"
    let (p, leader) ← invoke "stream"
    require ((← p.stdout.getLine) == "stream ready\n" && (← Process.observeExit p.pid) == .running) "stream"
    let _ ← finish p (.exited 124); dead leader
    let (p, leader) ← invoke "failure"
    let _ ← finish p (.exited 7); dead leader
    let (p, leader) ← invoke "signal"
    let _ ← finish p (.exited 143); dead leader
    let foreign ← spawn #["--fren2-deadline-fixture", "foreign"]
    IO.println "controls: stopped group, repeated stop/resume, orphan and foreign peer"
    let start ← IO.monoMsNow
    let (p, leader) ← invoke "stopped"
    let descendant ← take "descendant"
    let (_, err) ← finish p (.exited 124)
    stoppedMs := (← IO.monoMsNow) - start
    require (has err "deadline" && stoppedMs < 3000) s!"stopped group: {stoppedMs} ms; {err}"
    dead leader; dead descendant
    let (p, leader) ← invoke "sleep" 600
    for _ in [0:4] do
      let _ ← Process.pidfdSignal leader Process.sigstop; IO.sleep 25
      let _ ← Process.pidfdSignal leader Process.sigcont; IO.sleep 25
    let (_, err) ← finish p (.exited 124)
    require (has err "deadline") err
    dead leader
    -- A held pidfd remains tied to the original process after expiry.
    require (!(← Process.pidfdSignal leader Process.sigcont)) "signal unexpectedly reached a reaped fixture"
    IO.println "expired pidfd refused signal: ESRCH"
    let (p, leader) ← invoke "orphan" 2000
    let descendant ← take "descendant"
    let _ ← finish p (.exited 0); dead leader; dead descendant
    require ((← Process.observeExit foreign.pid) == .running) "foreign peer was signalled"
    IO.println "controls: controller cancellation and runner death"
    let (p, leader) ← invoke "sleep" 5000
    let _ ← Process.signalProcess p.pid Process.sigterm
    let _ ← finish p (.exited 143); dead leader
    let parent ← spawn #["--fren2-deadline-parent"]
    let leader ← take "leader"
    let _ ← Process.signalProcess parent.pid Process.sigterm
    let _ ← finish parent (.signaled 15); dead leader
    IO.println "runner termination status=-15; owned child reaped"
    require ((← Process.observeExit foreign.pid) == .running) "foreign peer was signalled"
    -- A failed handoff must still terminate and wait for its owned parent.
    let parent ← spawn #["--fren2-deadline-parent"]
    let captured ← IO.mkRef (#[] : Array UInt32)
    try
      let _ ← receive ids "leader" fun pid => do
        let fd ← Process.pidfdOpen pid
        captured.modify (·.push fd)
        identities.modify (·.push fd)
        throw (IO.userError "forced readiness failure")
      throw (IO.userError "forced readiness failure was not raised")
    catch e =>
      require (toString e == "forced readiness failure") (toString e)
    finally
      let _ ← Process.signalProcess parent.pid Process.sigterm
      let _ ← finish parent (.signaled 15)
    let caught ← captured.get
    require (caught.size == 1) "captured identity"
    dead caught[0]!
    IO.println "forced readiness failure: parent waited and fixture reaped"
    -- A partial handoff without a PID is rejected.
    let partialDir := tmp / "partial"
    IO.FS.createDirAll partialDir
    IO.FS.writeFile (partialDir / "1.id") "le"
    try
      let _ ← receive partialDir "leader"
      throw (IO.userError "partial identity accepted")
    catch e =>
      require (toString e == "incomplete fixture identity") (toString e)
    IO.println "partial handoff rejected"
    IO.println "controls: cleanup-entry cancellation"
    for mode in ["normal", "cancel"] do
      let p ← spawn #["--fren2-controller-cleanup", mode]
      let leader ← take "leader"
      let descendant ← if mode == "normal" then some <$> take "descendant" else pure none
      if mode == "cancel" then
        let _ ← Process.signalProcess p.pid Process.sigterm
      let (_, err) ← finish p (.exited 143)
      require (has err "cleanup-entry signals" && has err "cleanup-blocked signals") err
      IO.println s!"{mode}: real signals at cleanup entry and after the group signal; status 143"
      dead leader
      if let some d := descendant then dead d
  finally
    for p in ← processes.get do
      if (← (Process.observeExit p.pid).toBaseIO) matches .ok .running then
        let _ ← Process.signalProcess p.pid Process.sigterm
        let limit := (← IO.monoMsNow) + 7000
        while (← Process.observeExit p.pid) == .running && (← IO.monoMsNow) < limit do IO.sleep 10
        if (← Process.observeExit p.pid) == .running then
          let _ ← Process.signalProcess p.pid Process.sigkill
      if (← (Process.observeExit p.pid).toBaseIO) matches .ok _ then
        let _ ← Process.reap p.pid
    for fd in ← identities.get do
      try Process.closeFd fd catch _ => pure ()
  IO.println "controls: exact environment through production entry"
  let path := (← IO.getEnv "PATH").getD ""
  let mut found := none
  for dir in path.splitOn ":" do
    if found.isNone && (← (System.FilePath.mk dir / "env").pathExists) then
      found := some (System.FilePath.mk dir / "env")
  let some envTool := found | throw (IO.userError "no env tool")
  let environ ← IO.FS.readBinFile "/proc/self/environ"
  let entries (bytes : String) : List (String × String) :=
    ((bytes.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)).map fun e =>
      match e.splitOn "=" with
      | k :: rest => (k, "=".intercalate rest)
      | [] => ("", "")
  let some mine := String.fromUTF8? environ | throw (IO.userError "environment is not UTF-8")
  let mine := entries mine
  for (label, change) in [("set", ("FREN2_TEST_MARKER", some "inherited")), ("unset", ("HOME", none))] do
    let p ← runCommand self.toString #["--fren2-controller-run", toString me, envTool.toString, "-0"]
      (env := #[change])
    require (p.code == 0) s!"{label}: {p.stderr}"
    let expected := (mine.filter (·.1 != change.1)) ++ (change.2.map (change.1, ·)).toList
    let actual := entries p.stdout
    require (actual.length == expected.length && expected.all actual.contains) s!"environment {label}: {actual}"
  IO.println "controls: control failures and public dispatch"
  let messages ← IO.mkRef (#[] : Array String)
  let status ← control #[] 1000 0 (emit := fun s => messages.modify (·.push s)) (linux := false)
  require (status == 125 && (← messages.get).any (has · "required")) "unsupported platform"
  let failed ← runCommand self.toString #["--fren2-controller-test", "1000", toString me, (tmp / "absent").toString]
  require (failed.code == 125 && has failed.stderr "control failure") s!"failed start: {failed.stderr}"
  -- The runner needs no Python, or anything else on PATH.
  let p ← runCommand self.toString #["--job", "resolver"] (env := #[("PATH", some (tmp / "absent").toString)])
    (timeoutMs := 40000)
  require (p.code == 0 && has p.stdout "resolver cases:") s!"runner without PATH: {p.code} {p.stderr}"
  let p ← runCommand self.toString #["--job", "resolver"] (timeoutMs := 40000)
  require (p.code == 0 && has p.stdout "resolver cases:") s!"runner: {p.code} {p.stderr}"
  let elsewhere ← runCommand self.toString #["--job", "resolver"] (cwd := tmp) (timeoutMs := 40000)
  require (elsewhere.code != 0 && has elsewhere.stderr "test/FrenResolve/s1.fren") s!"elsewhere: {elsewhere.stderr}"
  let p ← runCommand self.toString #["--lib", "missing"] (timeoutMs := 40000)
  require (p.code == 2 && has p.stderr "unknown or ambiguous") s!"--lib missing: {p.code} {p.stderr}"
  let p ← runCommand self.toString #["--fren2-internal-job", "--job", "resolver"]
  require (p.code == 125) s!"direct internal dispatch: {p.code}"
  IO.println s!"deadline controls passed; stopped-group timeout {stoppedMs} ms, orphan and foreign controls passed"
  return 0

def runControls : IO UInt32 := do
  let tmp ← IO.FS.createTempDir
  try controlsIn tmp finally IO.FS.removeDirAll tmp

/-- Spawns a controller as its runner, then waits to be terminated. -/
def testParent : IO UInt32 := do
  let self := (← IO.appPath).toString
  let _ ← IO.Process.spawn {cmd := self, args := #["--fren2-controller-test", "5000",
    toString (← IO.Process.getPID), self, "--fren2-deadline-fixture", "sleep"]}
  forever
  return 0

/-- The controller with signals at cleanup entry and after the group signal. -/
def testCleanup (mode : String) : IO UInt32 := do
  let self := (← IO.appPath).toString
  control #[self, "--fren2-deadline-fixture", if mode == "normal" then "orphan" else "sleep"] 5000
    (← Process.parentPid) (testCleanup := true)

end FrenCli2Tests.Deadline
