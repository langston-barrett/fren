module

public import FrenCli2

public section
namespace FrenCli2Tests
open Lean

/-! Run the actual source command, including owned physical failure
controls. No constructor-only driver, expected-output fixture, network,
shell or Python is used. The temporary tree isolates its fixed solver path
from the shipped real cvc5. -/

def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

structure Output where
  code : UInt32
  stdout : String
  stderr : String
  deriving Repr

/-- One process with captured output, failing after `timeoutMs`. -/
def runCommand (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) (timeoutMs : Nat := 12000) : IO Output := do
  let child ← IO.Process.spawn {cmd, args, cwd, env, stdin := .null, stdout := .piped, stderr := .piped}
  let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
  let err ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
  let deadline := (← IO.monoMsNow) + timeoutMs
  let mut status := none
  repeat
    status ← child.tryWait
    if status.isSome || (← IO.monoMsNow) >= deadline then break
    IO.sleep 10
  let some code := status | do
    child.kill
    let _ ← child.wait
    throw (IO.userError s!"{cmd} {args} timed out")
  return ⟨code, ← IO.ofExcept out.get, ← IO.ofExcept err.get⟩

private def field (j : Json) (k : String) : Json := j.getObjValD k
private def text (j : Json) (k : String) : String := ((field j k).getStr?).toOption.getD ""
private def int? (j : Json) (k : String) : Option Int := ((field j k).getInt?).toOption
private def rows (j : Json) (k : String) : Array Json := ((field j k).getArr?).toOption.getD #[]

private def copyExecutable (source target : System.FilePath) : IO Unit := do
  if let some dir := target.parent then IO.FS.createDirAll dir
  IO.FS.writeBinFile target (← IO.FS.readBinFile source)
  let rights : IO.FileRight := {
    user := {read := true, write := true, execution := true},
    group := {read := true, execution := true}, other := {read := true, execution := true} }
  IO.setAccessRights target rights

def runCommandControls : IO Unit := do
  let root ← FrenOirToSmt.sourceRoot
  let exe := root / ".lake/build/bin/fren2_check"
  let tmp ← IO.FS.createTempDir
  let mut count := 0
  try
    let source := tmp / "source space;$(false)`false`\nfile.fren"
    let sentinel := tmp / "unexpected-shell-write"
    let evidence ← IO.mkRef (#[] : Array Json)
    let run (label : String) (input : Option ByteArray := none) (options : Array String := #[])
        (expected : Nat := 0) (verdict := "verified") (binary := exe) (path := source)
        (env : Array (String × Option String) := #[]) : IO Json := do
      if let some bytes := input then IO.FS.writeBinFile path bytes
      let started ← IO.monoMsNow
      let p ← runCommand binary.toString (options.push path.toString) (cwd := tmp) (env := env)
      let elapsed := (← IO.monoMsNow) - started
      let output ← IO.ofExcept (Json.parse p.stdout)
      let shown := s!"{label}: exit {p.code}; {p.stdout}{p.stderr}"
      evidence.modify (·.push (Json.mkObj [("label", toJson label), ("exit_code", toJson p.code.toNat), ("ms", toJson elapsed),
        ("command", toJson ((options.push path.toString).toList.cons binary.toString)), ("output", output)]))
      require (p.code.toNat == expected) shown
      require (int? output "exit_code" == some expected && text output "verdict" == verdict) shown
      require (text output "file" == path.toString) shown
      require p.stderr.isEmpty shown
      require (!(← sentinel.pathExists)) "path passed to a shell"
      return output
    let good := "mod command\nfn next(n: Int): Int := n + 1\nexpect safe(n: Int) { assume a: n >= 0 expect grows: next(n) > n }"
    let verified ← run "verified" good.toUTF8
    let checks := rows verified "checks"
    require (!checks.isEmpty && checks.all (fun r => ["verified", "witness"].contains (text r "status")))
      "verified statuses"
    require (checks.any (fun r => text r "status" == "witness" && !(field r "assignment_summary").isNull))
      "witness without assignment summary"
    require (checks.all (fun r => !(text r "owner").isEmpty && !(text r "reason").isEmpty)) "owner/reason"
    let bad := "mod command\nexpect bad(n: Int) { assume a: n = 2 expect wrong: n = 3 }"
    let refuted ← run "refuted" bad.toUTF8 (expected := 1) (verdict := "refuted")
    let some counter := (rows refuted "checks").find? (text · "status" == "counterexample")
      | throw (IO.userError "refuted without counterexample")
    require ((text counter "owner").endsWith ".bad" && !(field counter "location").isNull &&
      !(field counter "model_ref").isNull) "counterexample owner/location/model"
    require ((field (field counter "assignment_summary") "values").compress ==
      (Json.arr #[Json.mkObj [("parameter_index", 0), ("value", "2")]]).compress) "counterexample values"
    require (int? (field counter "location") "start_byte" ==
      some ((bad.splitOn "n = 3")[0]!.utf8ByteSize : Int)) "counterexample span"
    let inconsistent ← run "inconsistent" "mod command\nexpect c(n: Int) { assume a: n = 0 assume b: n = 1 expect bad: false }".toUTF8
      (expected := 2) (verdict := "inconsistent")
    require ((rows inconsistent "checks").any (text · "status" == "vacuous")) "vacuous row"
    for (label, input) in [("no-module-checks", "mod empty"), ("no-block-checks", "mod empty\nexpect empty() {}")] do
      let _ ← run label input.toUTF8 (expected := 4) (verdict := "noChecks")
    for (label, input, token) in [("parse", "mod command\r\nexpect c() { expect bad: }", some "}"),
        ("resolution-bytes", "-- λ\r\nmod command\r\nexpect c() { expect bad: absent }", some "absent"),
        ("type", "mod command\nexpect c() { expect bad: 1 + true = 2 }", none)] do
      let result ← run label input.toUTF8 (expected := 5) (verdict := "inputFailure")
      let span := field (field result "diagnostic") "location"
      let some start := int? span "start_byte" | throw (IO.userError s!"{label}: no span")
      let some stop := int? span "stop_byte" | throw (IO.userError s!"{label}: no span")
      require (0 ≤ start && start ≤ stop && stop ≤ input.utf8ByteSize) s!"{label}: span"
      if let some token := token then
        require (start == ((input.splitOn token)[0]!.utf8ByteSize : Int)) s!"{label}: span start"
    let _ ← run "invalid-utf8" ("mod command\n".toUTF8.push 0xff) (expected := 5) (verdict := "inputFailure")
    let _ ← run "oversize-source" (ByteArray.mk (Array.replicate 1048577 32)) (expected := 5) (verdict := "inputFailure")
    let _ ← run "missing-file" (path := tmp / "missing.fren") (expected := 5) (verdict := "inputFailure")
    -- A relative dash path exercises the parser's end-of-options marker.
    IO.FS.writeFile (tmp / "-source.fren") good
    let dash ← runCommand exe.toString #["--", "-source.fren"] (cwd := tmp)
    require (dash.code == 0 && text (← IO.ofExcept (Json.parse dash.stdout)) "verdict" == "verified") "dash path"
    evidence.modify (·.push (Json.mkObj [("label", "dash-path"), ("stdout", toJson dash.stdout)]))
    -- This path would create a marker if ever interpolated into a shell.
    let _ ← run "shell-path" good.toUTF8 (path := tmp / "$(touch unexpected-shell-write).fren")
    for (label, opts, status) in [("real-unknown", #["--solver-resources", "1"], "unknown"),
        ("script-limit", #["--input-bytes", "1"], "resourceExhausted"),
        ("evaluation-limit", #["--evaluation-depth", "0"], "unconfirmed")] do
      let result ← run label good.toUTF8 (options := opts) (expected := 3) (verdict := "inconclusive")
      require ((rows result "checks").any (text · "status" == status)) s!"{label}: {result.compress}"
    let definedness ← run "definedness-confirmation" "mod command\nexpect c() { expect goal: 1 div 0 = 0 }".toUTF8
      (expected := 1) (verdict := "refuted")
    require ((rows definedness "checks").any fun r => text r "status" == "counterexample" &&
      !(field r "model_ref").isNull &&
      text (field r "assignment_summary") "confirmation" == "FrenOirToSmt.Confirmation.counterexample")
      "definedness confirmation"
    let s := source.toString
    for args in [#[], #["--bogus", "1", s], #["--wall-ms", "0", s], #["--wall-ms", "10001", s],
        #["--solver-ms", "0", s], #["--solver-resources", "1000000001", s], #["--output-bytes", "1048577", s],
        #["--input-bytes", "0", s], #["--evaluation-depth", "10001", s], #["--wall-ms", "-1", s],
        #["--wall-ms", "1x", s], #["--wall-ms"], #["-source.fren"], #[s, s]] do
      let p ← runCommand exe.toString args (cwd := tmp)
      let result ← IO.ofExcept (Json.parse p.stdout)
      require (p.code == 5 && text result "verdict" == "inputFailure") s!"argument failure {args}: {p.stdout}"
      evidence.modify (·.push (Json.mkObj [("label", "argument-failure"), ("command", toJson args),
        ("exit_code", toJson p.code.toNat), ("output", result)]))
      count := count + 1
    let help ← runCommand exe.toString #["--help"]
    require (help.code == 0 && help.stdout.startsWith "Usage: fren2_check") "help"
    evidence.modify (·.push (Json.mkObj [("label", "help"), ("stdout", toJson help.stdout)]))
    count := count + 2
    -- An owned tree: this binary, with the fake solver at its fixed cvc5 path.
    let isolated := tmp / "owned tree"
    let binary := isolated / ".lake/build/bin/fren2_check"
    copyExecutable exe binary
    let solver := isolated / ".lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5"
    copyExecutable (root / ".lake/build/bin/fren2_fake_solver") solver
    for (mode, status) in [("unknown", "unknown"), ("unsupported", "unsupported"),
        ("nonzero", "processFailure"), ("stderr", "processFailure"), ("protocol", "processFailure"),
        ("bytes", "processFailure"), ("flood", "resourceExhausted"), ("timeout", "resourceExhausted")] do
      IO.FS.writeFile (solver.withExtension "mode") mode
      let result ← run ("owned-" ++ mode) good.toUTF8 (options := #["--wall-ms", "100", "--output-bytes", "64"])
        (expected := 3) (verdict := "inconclusive") (binary := binary)
      require ((rows result "checks").any (text · "status" == status)) s!"owned {mode}: {result.compress}"
    -- No Python, or anything else on PATH, is needed: real cvc5 and the owned tree.
    let noPath := #[("PATH", some (tmp / "absent").toString)]
    let _ ← run "no-path-verified" good.toUTF8 (env := noPath)
    IO.FS.writeFile (solver.withExtension "mode") "unknown"
    let owned ← run "no-path-owned" good.toUTF8 (expected := 3) (verdict := "inconclusive") (binary := binary)
      (env := noPath)
    require ((rows owned "checks").any (text · "status" == "unknown")) "owned solver without PATH"
    -- Cancellation: SIGTERM to the command mid-query kills and reaps its
    -- solver, then ends the command as SIGTERM would have.
    IO.FS.writeFile (solver.withExtension "mode") "ready"
    let ready := solver.withExtension "pid"
    let command ← FrenOirToSmt.Process.spawnInherit #[binary.toString, "--wall-ms", "10000", source.toString]
      (session := false)
    let cancelled : IO Unit := do
      let limit := (← IO.monoMsNow) + 5000
      while !(← ready.pathExists) && (← IO.monoMsNow) < limit do IO.sleep 5
      let some solverPid := (← IO.FS.readFile ready).toNat?
        | throw (IO.userError "cancelled command: the owned solver never started")
      -- The solver is still asleep, so the pidfd names it.
      let solverFd ← FrenOirToSmt.Process.pidfdOpen solverPid.toUInt32
      try
        let _ ← FrenOirToSmt.Process.signalProcess command FrenOirToSmt.Process.sigterm
        let status ← FrenOirToSmt.Process.reap command
        let info ← IO.FS.readFile s!"/proc/self/fdinfo/{solverFd}"
        require (status == .signaled 15 && (info.splitOn "\n").contains "Pid:\t-1")
          s!"cancelled command: {reprStr status}; solver {info}"
      finally
        FrenOirToSmt.Process.closeFd solverFd
    try cancelled
    catch e =>
      -- Never leave the command behind: kill and reap it if it is still ours.
      if (← (FrenOirToSmt.Process.observeExit command).toBaseIO) matches .ok _ then
        let _ ← FrenOirToSmt.Process.signalProcess command FrenOirToSmt.Process.sigkill
        let _ ← FrenOirToSmt.Process.reap command
      throw e
    count := count + 1
    IO.FS.removeFile solver
    let missing ← run "missing-solver" good.toUTF8 (expected := 3) (verdict := "inconclusive") (binary := binary)
    require ((rows missing "checks").any (text · "status" == "processFailure")) "missing solver"
    let all ← evidence.get
    for row in all do
      require ((row.compress.splitOn "(check-sat)").length == 1) "raw script dumped"
    count := count + all.size
    if let some dir ← IO.getEnv "FREN2_COMMAND_EVIDENCE_DIR" then
      IO.FS.createDirAll dir
      IO.FS.writeFile (System.FilePath.mk dir / s!"command-{← IO.Process.getPID}.json")
        ((Json.mkObj [("executable", toJson exe.toString), ("cases", toJson all)]).pretty ++ "\n")
  finally
    IO.FS.removeDirAll tmp
  IO.println s!"source-command-controls: {count} actual command invocations; real cvc5 outcomes and owned physical failures; no PATH needed"

end FrenCli2Tests
