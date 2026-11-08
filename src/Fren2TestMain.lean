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

fren_test_runners textRunners

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
  if args == ["--job", "evaluator"] then
    FrenEvalTests.runCases
    return 0
  if args == ["--job", "evaluatorProperties"] then
    FrenEvalTests.runProperties
    return 0
  return ← Fren.TextTests.cli textRunners args

-- The helper is shipped with the source tree containing this Lake executable.
private def helperPath : IO System.FilePath := do
  let app ← IO.appPath
  let some bin := app.parent | throw <| IO.userError "fren2_test: no executable directory"
  let root ← IO.FS.realPath (bin / ".." / ".." / "..")
  return root / "test" / "Fren2Driver" / "deadlines.py"

private def bounded (args : List String) (internal : String := "--fren2-internal-job") : IO UInt32 := do
  try
    let original ← IO.getEnv "PYTHONCOERCECLOCALE"
    let child ← IO.Process.spawn {
      cmd := "python3", args := #[(← helperPath).toString, "--run", toString (← IO.Process.getPID),
        (if original.isSome then "set" else "unset"), original.getD "",
        (← IO.appPath).toString, internal] ++ args.toArray,
      env := #[("PYTHONCOERCECLOCALE", some "0")],
      stdin := .inherit, stdout := .inherit, stderr := .inherit }
    return ← child.wait
  catch e =>
    IO.eprintln s!"fren2_test: deadline controller failed: {e}"
    return 125

-- Reject accidental direct dispatch; the helper's fixed --run mode supplies
-- the 30-second deadline. This is not an authorization boundary.
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
    let original ← IO.getEnv "PYTHONCOERCECLOCALE"
    return parts.drop 1 == [(← helperPath).toString, "--run", runnerPid,
      (if original.isSome then "set" else "unset"), original.getD "", (← IO.appPath).toString] ++ args ++ [""]
  catch _ => return false

public def main (args : List String) : IO UInt32 := do
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
      ["--job", "evaluator"], ["--job", "evaluatorProperties"]] do
    let status ← bounded job
    if status != 0 then return status
  for name in ["run", "derive", "phase"] do
    let status ← bounded [name] "--fren2-internal-sexp"
    if status != 0 then return status
  return 0
