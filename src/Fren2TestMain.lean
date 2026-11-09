module

meta import FrenBaseTests.Properties
meta import FrenBaseTests.Binding
meta import FrenSourceTests.Properties
import FrenSexpTests
import FrenTextDemo
import FrenAstTests
import FrenParseTests
import FrenAstToHirTests
import FrenHirToThirTests
import FrenEvalTests
import FrenThirDesugarTests
import FrenThirToMirTests
import FrenFlatToLirTests
import FrenLirToOirTests
import FrenOirTests
import FrenOirToSmtTests
import FrenCli2Tests

fren_test_runners textRunners

/-- Run the public fren2_check library pipeline on every annotated source file.
Empty directories, malformed annotations and missing verdicts fail the job. -/
private def runVerdictCorpus : IO Unit := do
  let started ← IO.monoMsNow
  let directory := (← FrenOirToSmt.sourceRoot) / "test/fren2-verdicts"
  let files := ((← directory.readDir).filter (fun e => e.path.extension == some "fren"))
    |>.qsort (fun a b => a.fileName < b.fileName)
  FrenOirToSmtTests.require (!files.isEmpty) "empty known-verdict corpus"
  for entry in files do
    let text ← IO.FS.readFile entry.path
    let annotation := (text.splitOn "\n").head!
    let ["--", "verdict:", expected, "exit:", code] := annotation.splitOn " "
      | throw (IO.userError s!"{entry.path}: malformed verdict annotation")
    let some code := code.toNat? | throw (IO.userError s!"{entry.path}: malformed exit annotation")
    let result ← FrenCli2.checkFile entry.path
    FrenOirToSmtTests.evidence ("corpus-" ++ entry.fileName) (FrenCli2.resultJson entry.path.toString {} result)
    FrenOirToSmtTests.require (FrenCli2.verdictName result.report.verdict == expected &&
      (FrenCli2.exitCode result.report.verdict).toNat == code)
      s!"{entry.path}: expected {expected}/{code}, got {FrenCli2.verdictName result.report.verdict}/{FrenCli2.exitCode result.report.verdict}"
    let elapsed := (← IO.monoMsNow) - started
    FrenOirToSmtTests.require (elapsed < 29000) s!"verdict-corpus exceeded 29 s budget after {entry.fileName}: {elapsed} ms"
  IO.println s!"verdict-corpus: {files.size} annotated programs through fren2_check pipeline in {(← IO.monoMsNow) - started} ms"

private def runJob (args : List String) : IO UInt32 := do
  if args == ["--job", "resolver"] then
    FrenAstToHirTests.runCases
    return 0
  if args == ["--job", "resolverProperties"] then
    FrenAstToHirTests.runProperties
    return 0
  if args == ["--job", "walkingProperties"] then
    FrenHirToThirTests.runWalkingProperties
    return 0
  if args == ["--job", "walking"] then
    FrenHirToThirTests.runWalking
    return ← Fren.TextTests.cli textRunners ["--lib", "FrenWalking"]
  if args == ["--job", "typing"] then
    FrenHirToThirTests.runCases
    FrenHirToThirTests.runAdmission
    return 0
  if args == ["--job", "typingOperators"] then
    FrenHirToThirTests.runOperators
    return 0
  if args == ["--job", "typingProperties"] then
    FrenHirToThirTests.runProperties
    return 0
  if args == ["--job", "verdictCorpus"] then
    runVerdictCorpus
    return 0
  if args == ["--job", "definednessControls"] then
    FrenOirToSmtTests.runDefinednessControls
    return 0
  if args == ["--job", "smt"] then
    FrenOirToSmtTests.runCases
    return 0
  if args == ["--job", "smtControls"] then
    FrenOirToSmtTests.runControls
    FrenCli2Tests.run
    return 0
  if args == ["--job", "smtProperties"] then
    FrenOirToSmtTests.runProperties
    return 0
  if args == ["--job", "oir"] then
    FrenOirTests.run
    FrenLirToOirTests.runCases
    return 0
  if args == ["--job", "oirControls"] then
    FrenLirToOirTests.runControls
    return 0
  if args == ["--job", "oirProperties"] then
    FrenLirToOirTests.runProperties
    return 0
  if args == ["--job", "lir"] then
    FrenFlatToLirTests.runCases
    return 0
  if args == ["--job", "lirProperties"] then
    FrenFlatToLirTests.runProperties
    return 0
  if args == ["--job", "mir"] then
    FrenThirToMirTests.runCases
    return 0
  if args == ["--job", "mirProperties"] then
    FrenThirToMirTests.runProperties
    return 0
  if args == ["--job", "desugaring"] then
    FrenThirDesugarTests.run
    return 0
  if args == ["--job", "evaluator"] then
    FrenEvalTests.runCases
    return 0
  if args == ["--job", "evaluatorProperties"] then
    FrenEvalTests.runProperties
    return 0
  return ← Fren.TextTests.cli textRunners args

-- Each job runs under the deadline controller, a separate process of this
-- same executable (`FrenCli2Tests.Deadline`), with the fixed production deadline.
private def bounded (args : List String) (internal : String := "--fren2-internal-job") : IO UInt32 := do
  try
    let self := (← IO.appPath).toString
    let child ← IO.Process.spawn {
      cmd := self, args := #["--fren2-controller-run", toString (← IO.Process.getPID), self, internal] ++
        args.toArray,
      stdin := .inherit, stdout := .inherit, stderr := .inherit }
    return ← child.wait
  catch e =>
    IO.eprintln s!"fren2_test: deadline controller failed: {e}"
    return 125

-- Reject accidental direct dispatch; the controller's fixed production entry
-- supplies the 30-second deadline. This is not an authorization boundary.
private def controlled (args : List String) : IO Bool := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let some line := (status.splitOn "\n").find? (·.startsWith "PPid:") | return false
    let some pid := (line.drop 5).trimAscii.toString.toNat? | return false
    let parent := s!"/proc/{pid}"
    let parentStatus ← IO.FS.readFile (parent ++ "/status")
    let some parentLine := (parentStatus.splitOn "\n").find? (·.startsWith "PPid:") | return false
    let runnerPid := (parentLine.drop 5).trimAscii.toString
    let bytes ← IO.FS.readBinFile (parent ++ "/cmdline")
    let some cmdline := String.fromUTF8? bytes | return false
    let parts := cmdline.splitOn (String.singleton (Char.ofNat 0))
    let self := (← IO.appPath).toString
    return parts == [self, "--fren2-controller-run", runnerPid, self] ++ args ++ [""]
  catch _ => return false

/-- Hidden entries of the controller and its regression's fixtures. -/
private def controllerEntry : List String → Option (IO UInt32)
  | "--fren2-controller-run" :: runner :: command => some do
    let some runner := runner.toNat? | return 125
    FrenCli2Tests.Deadline.control command.toArray FrenCli2Tests.Deadline.productionMs runner.toUInt32
  | "--fren2-controller-test" :: ms :: runner :: command => some do
    let (some ms, some runner) := (ms.toNat?, runner.toNat?) | return 125
    FrenCli2Tests.Deadline.control command.toArray ms runner.toUInt32
  | ["--fren2-controller-cleanup", mode] => some (FrenCli2Tests.Deadline.testCleanup mode)
  | args@("--fren2-deadline-fixture" :: mode :: _) => some (FrenCli2Tests.Deadline.fixture mode args)
  | ["--fren2-deadline-parent"] => some FrenCli2Tests.Deadline.testParent
  | ["--fren2-deadline-controls"] => some FrenCli2Tests.Deadline.runControls
  | _ => none

public def main (args : List String) : IO UInt32 := do
  if let some entry := controllerEntry args then return ← entry
  if args.head? == some "--fren2-internal-job" || args.head? == some "--fren2-internal-sexp" then
    unless ← controlled args do
      IO.eprintln "fren2_test: internal dispatch requires the deadline controller"
      return 125
    if args == ["--fren2-internal-sexp", "run"] then
      Fren.SexpTests.run
      return 0
    if args == ["--fren2-internal-sexp", "derive"] then
      Fren.SexpTests.runDerive
      return 0
    if args == ["--fren2-internal-sexp", "phase"] then
      Fren.SexpTests.Phase.run
      return 0
    unless args.head? == some "--fren2-internal-job" do return 125
    if args.tail.isEmpty then
      IO.eprintln "fren2_test: missing internal job"
      return 125
    return ← runJob args.tail
  unless args.isEmpty do return ← bounded args
  for job in [["--job", "resolver"], ["--job", "resolverProperties"],
      ["--job", "walking"], ["--job", "walkingProperties"], ["--job", "typing"],
      ["--job", "typingOperators"], ["--job", "typingProperties"],
      ["--job", "evaluator"], ["--job", "evaluatorProperties"], ["--job", "desugaring"],
      ["--job", "mir"], ["--job", "mirProperties"],
      ["--job", "lir"], ["--job", "lirProperties"],
      ["--job", "oir"], ["--job", "oirControls"], ["--job", "oirProperties"],
      ["--job", "smt"], ["--job", "smtControls"], ["--job", "smtProperties"],
      ["--job", "definednessControls"], ["--job", "verdictCorpus"]] do
    let status ← bounded job
    if status != 0 then return status
  for name in ["run", "derive", "phase"] do
    let status ← bounded [name] "--fren2-internal-sexp"
    if status != 0 then return status
  return 0
