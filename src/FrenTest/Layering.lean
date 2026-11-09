module

public import Lean.Elab.Import

public section

namespace FrenTest.Layering

private def base : List String := ["FrenBase", "FrenSource", "FrenDiag", "FrenSexp"]
private def ir : List String := ["FrenAst", "FrenModule", "FrenExpr", "FrenMir", "FrenLir", "FrenOir"]

-- The sole table of direct production-library dependencies. The drivers
-- may import all production libraries except the test-only FrenProp.
private def allowed : List (String × List String) :=
  [("FrenBase", []), ("FrenSource", ["FrenBase"]),
   ("FrenDiag", ["FrenBase", "FrenSource"]), ("FrenSexp", []),
   ("FrenProp", ["FrenSexp"]), ("FrenAst", base), ("FrenModule", base ++ ["FrenAst", "FrenExpr"]),
   ("FrenExpr", base ++ ["FrenAst"]), ("FrenMir", base ++ ["FrenExpr", "FrenModule"]),
   ("FrenLir", base ++ ["FrenMir"]), ("FrenOir", base ++ ["FrenLir"]),
   ("FrenParse", base ++ ["FrenAst"]),
   ("FrenAstToHir", base ++ ["FrenAst", "FrenModule", "FrenExpr", "FrenParse"]),
   ("FrenHirToThir", base ++ ["FrenAst", "FrenModule", "FrenExpr", "FrenAstToHir"]),
   ("FrenThirDesugar", base ++ ["FrenModule", "FrenExpr", "FrenHirToThir"]),
   -- This walking producer consumes the actual checked desugaring witness.
   ("FrenThirToMir", base ++ ["FrenModule", "FrenExpr", "FrenMir", "FrenThirDesugar"]),
   ("FrenMirToMono", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenMonoToFo", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenFoToFlat", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenMirToLean", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   -- Direct walking lowering requires the real admitted MIR producer.
   ("FrenFlatToLir", base ++ ["FrenExpr", "FrenMir", "FrenLir", "FrenThirToMir"]),
   ("FrenLirToOir", base ++ ["FrenLir", "FrenOir", "FrenModule", "FrenFlatToLir"]),
   ("FrenOirToSmt", base ++ ["FrenOir"]),
   -- The walking adapter proves admission with the actual checked producer.
   -- This dependency does not prescribe the future generic evaluator boundary.
   ("FrenEval", base ++ ["FrenModule", "FrenExpr", "FrenMir", "FrenHirToThir"]),
   ("FrenLirEval", base ++ ["FrenLir"]),
   ("FrenGen", base ++ ["FrenProp"] ++ ir),
   ("FrenCli2", []), ("FrenHosted2", [])]

private def roots : List String := allowed.map Prod.fst
private def tests : List String := roots.map (· ++ "Tests")

-- Extend the existing inventory with its test support and default-build shim.
-- Spec wrappers and FrenTestMain remain Fren1 infrastructure, not Fren2 roots.
private def owners : List String := roots ++ tests ++
  ["FrenTextTests", "FrenTextTestsTests", "FrenTextDemo", "FrenTextDemoTests",
   "Fren2TestMain", "FrenTest.Layering", "FrenTest.Fren2Resolver", "FrenTest.Fren2Typing",
   "FrenTest.Fren2Mir", "FrenTest.Fren2Lir"]

private def testOnly (owner : String) : Bool :=
  tests.contains owner || ["FrenTextTestsTests", "FrenTextDemoTests", "Fren2TestMain",
    "FrenTest.Layering", "FrenTest.Fren2Resolver", "FrenTest.Fren2Typing",
    "FrenTest.Fren2Mir", "FrenTest.Fren2Lir"].contains owner

private def permits (owner imported : String) : Bool := Id.run do
  if ["Lean", "Std", "Init"].contains imported then return true
  if owner == imported then return true
  if owner == "FrenLirToOirTests" && ["FrenFlatToLirTests", "Plausible"].contains imported then return true
  if owner == "FrenTest.Fren2Lir" then return imported == "FrenFlatToLirTests"
  if owner == "FrenFlatToLirTests" && ["Plausible", "FrenEval"].contains imported then return true
  if owner == "FrenTest.Fren2Mir" then return imported == "FrenThirToMirTests"
  if owner == "FrenThirToMirTests" && ["Plausible", "FrenEval"].contains imported then return true
  if owner == "FrenTest.Fren2Typing" then return imported == "FrenHirToThirTests"
  if owner == "FrenTest.Fren2Resolver" then return imported == "FrenAstToHirTests"
  if ["FrenProp", "FrenAstToHirTests", "FrenHirToThirTests", "FrenEvalTests", "FrenThirDesugarTests"].contains owner && imported == "Plausible" then return true
  if owner == "FrenTextTests" then return false
  if owner == "FrenTextTestsTests" then return imported == "FrenTextTests"
  if owner == "FrenTextDemo" then return imported == "FrenTextTests"
  if owner == "FrenTextDemoTests" then return imported == "FrenTextDemo"
  if owner == "Fren2TestMain" then return (roots ++ tests ++ ["FrenTextDemo"]).contains imported
  if owner == "FrenThirDesugarTests" && imported == "FrenEval" then return true
  if let some original := owner.dropSuffix? "Tests" then
    let original := original.toString
    if !roots.contains original then return false
    return (base ++ ["FrenProp", "FrenGen", "FrenTextTests", original] ++
      (if ["FrenCli2", "FrenHosted2"].contains original then roots else
        (allowed.lookup original).getD [])).contains imported
  if ["FrenCli2", "FrenHosted2"].contains owner then
    return roots.contains imported && imported != "FrenProp"
  return ((allowed.lookup owner).getD []).contains imported

#guard !permits "FrenAst" "FrenTextTests"
#guard !permits "FrenCli2" "FrenTextDemo"
#guard permits "FrenProp" "Plausible"
#guard !permits "FrenBase" "Plausible"
#guard permits "FrenGen" "FrenProp"
#guard permits "FrenBaseTests" "FrenProp"
#guard !permits "FrenCli2" "FrenProp"
#guard !permits "FrenHosted2" "FrenProp"
#guard !permits "FrenBase" "FrenExpr"
#guard permits "FrenAst" "FrenSexp"
#guard !permits "Fren2TestMain" "FrenCore"
#guard !permits "FrenBaseTests" "Fren"
#guard permits "FrenThirToMir" "FrenThirDesugar"
#guard !permits "FrenThirToMir" "FrenEval"
#guard !permits "FrenMir" "FrenThirDesugar"
#guard !permits "FrenMir" "FrenEval"
#guard permits "FrenEval" "FrenHirToThir"
#guard permits "FrenEvalTests" "Plausible"
#guard !permits "FrenEval" "Plausible"
#guard !permits "FrenEval" "FrenCore"
#guard permits "FrenFlatToLir" "FrenThirToMir"
#guard !permits "FrenFlatToLir" "FrenEval"
#guard !permits "FrenLirEval" "FrenHirToThir"

private def rootOf (name : Lean.Name) : String :=
  (name.toString.splitOn ".").headD ""

/-- Physical lines: LF separates lines, an unterminated last line counts,
CRLF counts once, and the empty file has zero lines. Comments/blanks count. -/
private def physicalLines (source : String) : Nat :=
  if source.isEmpty then 0
  else (source.splitOn "\n").length - (if source.endsWith "\n" then 1 else 0)

/-- Optional extra test allowance requires a parsed trailing top-level section.
The builtin command parser suffices for this deliberately narrow convention;
files using custom command syntax in this opt-in form must split their tests.
Named declarations, nesting, commands after the closing end, and fake markers
in strings/comments never acquire the extra allowance. -/
private def testStart (source path : String) (input : Lean.Parser.InputContext)
    (initial : Lean.Parser.ModuleParserState) : IO (Except String (Option Nat)) := do
  if !(source.splitOn "\n").any (fun line => line.trimAsciiEnd.toString == "section Fren2Tests") then
    return .ok none
  let env ← Lean.mkEmptyEnvironment
  let mut state := initial
  let mut depth := 0
  let mut start := none
  let mut closed := false
  for _ in [:source.utf8ByteSize + 1] do
    let (command, next, messages) := Lean.Parser.parseCommand input {env, options := {}} state {}
    if messages.hasErrors then
      let errors ← messages.toList.mapM (fun message => message.data.toString)
      return .error s!"{path}: cannot parse co-located test section: {String.intercalate "; " errors}"
    if command.isOfKind ``Lean.Parser.Command.eoi then
      if start.isNone || closed then return .ok start
      return .error s!"{path}: expected a complete trailing section Fren2Tests"
    if closed then return .error s!"{path}: commands follow end Fren2Tests"
    if start.isSome then
      if command.isOfKind ``Lean.Parser.Command.end && command[1][0].getId == `Fren2Tests then
        closed := true
      else if !((command.isOfKind ``Lean.Parser.Command.declaration &&
          command[1].isOfKind ``Lean.Parser.Command.example) ||
          command.isOfKind ``Lean.Parser.Command.eval || command.isOfKind ``Lean.Parser.Command.check) then
        return .error s!"{path}: Fren2Tests permits only anonymous examples, #eval and #check"
    else if command.isOfKind ``Lean.Parser.Command.section && command[2][0].getId == `Fren2Tests then
      let some pos := command.getPos? | return .error s!"{path}: test section has no source position"
      let location := input.fileMap.toPosition pos
      if depth != 0 || location.column != 0 ||
          (source.splitOn "\n")[location.line - 1]?.map (·.trimAsciiEnd.toString) != some "section Fren2Tests" then
        return .error s!"{path}: Fren2Tests must be an unmodified top-level section on its own line"
      start := some (location.line - 1)
    else if command.isOfKind ``Lean.Parser.Command.section || command.isOfKind ``Lean.Parser.Command.namespace then
      depth := depth + 1
    else if command.isOfKind ``Lean.Parser.Command.end then
      depth := depth - 1
    if next.pos <= state.pos then return .error s!"{path}: test-section parser made no progress"
    state := next
  return .error s!"{path}: test-section parser exhausted source-derived progress bound"

private def checkSource (owner path source : String) : IO (Array String) := do
  let input := Lean.Parser.mkInputContext source path
  let (header, state, messages) ← Lean.Parser.parseHeader input
  if messages.hasErrors then return #[s!"{path}: cannot parse Lean header"]
  let mut failures := #[]
  unless Lean.Elab.HeaderSyntax.isModule header do
    failures := failures.push s!"{path}: Fren2 requires Lean module mode"
  let total := physicalLines source
  if testOnly owner then
    if total > 500 then failures := failures.push s!"{path}: {total} physical test lines exceed 500"
  else
    match ← testStart source path input state with
    | .error error => failures := failures.push error
    | .ok start =>
      let production := start.getD total
      let testLines := total - production
      if production > 1000 then
        failures := failures.push s!"{path}: {production} physical source lines exceed 1000"
      if testLines > 500 then
        failures := failures.push s!"{path}: {testLines} physical co-located test lines exceed 500"
  for i in Lean.Elab.HeaderSyntax.imports header do
    let imported := rootOf i.module
    unless permits owner imported do
      failures := failures.push s!"{path}: {owner} may not import {imported} ({i.module})"
  return failures

private def files (root : String) : IO (Array System.FilePath) := do
  let path : System.FilePath := "src" / root.replace "." "/"
  let mut result := #[path.withExtension "lean"]
  if ← path.isDir then
    result := result ++ (← path.walkDir).filter (·.extension == some "lean")
  return result

/-- Boundary controls run inside the actual default layering job. The same
checker handles synthetic inputs and each physical file in the inventory. -/
private def qualityControls : IO (Array String) := do
  let mut failures := #[]
  let pad (n : Nat) := String.join (List.replicate n "-- counted comment\n")
  let production (n : Nat) := "module\n" ++ pad (n - 1)
  let tests (n : Nat) := "section Fren2Tests\nexample : True := True.intro\n" ++ pad (n - 3) ++ "end Fren2Tests\n"
  let cases : List (String × String × String × Bool) := [
    ("module", "FrenAst", "module\n", true),
    ("leading nested comments", "FrenAst", "/- outer /- module -/ -/\nmodule\n", true),
    ("missing module", "FrenAst", "def x := 1\n", false),
    ("comment-only fake module", "FrenAst", "/- module -/\ndef x := 1\n", false),
    ("module after imports", "FrenAst", "import Lean\nmodule\n", false),
    ("module after declaration", "FrenAst", "def x := 1\nmodule\n", false),
    ("inert marker in comment", "FrenAst", "module\n/-\n" ++ tests 3 ++ "-/\ndef x := 1\n", true),
    ("inert marker in doc comment", "FrenAst", "module\n/--\n" ++ tests 3 ++ "-/\ndef x := 1\n", true),
    ("inert marker in string", "FrenAst", "module\ndef marker := \"\nsection Fren2Tests\nend Fren2Tests\n\"\ndef x := 1\n", true),
    ("exact production", "FrenAst", production 1000, true),
    ("production one over", "FrenAst", production 1001, false),
    ("no blanket 1500", "FrenAst", production 1500, false),
    ("exact standalone tests", "FrenAstTests", production 500, true),
    ("standalone tests one over", "FrenAstTests", production 501, false),
    ("test driver one over", "Fren2TestMain", production 501, false),
    ("blank lines count", "FrenAstTests", "module\n" ++ String.join (List.replicate 500 "\n"), false),
    ("exact split", "FrenAst", production 1000 ++ tests 500, true),
    ("exact split CRLF", "FrenAst", (production 1000 ++ tests 500).replace "\n" "\r\n", true),
    ("eval/check test section", "FrenAst", production 1000 ++
      "section Fren2Tests\n#check Nat\n#eval 1\nend Fren2Tests\n", true),
    ("split source one over", "FrenAst", production 1001 ++ tests 499, false),
    ("split tests one over", "FrenAst", production 999 ++ tests 501, false),
    ("test-region production declaration", "FrenAst", production 1000 ++
      "section Fren2Tests\ndef hiddenProduction := 1\nend Fren2Tests\n", false),
    ("nontrailing section", "FrenAst", production 2 ++ tests 3 ++ "def afterTests := 1\n", false),
    ("unclosed section", "FrenAst", production 2 ++ "section Fren2Tests\nexample : True := True.intro\n", false),
    ("nested section", "FrenAst", production 2 ++ "namespace N\n" ++ tests 3 ++ "end N\n", false),
    ("fake section in comment", "FrenAst", production 1000 ++ "/-\n" ++ tests 3 ++ "-/\n", false),
    ("fake section in doc comment", "FrenAst", production 1000 ++ "/--\n" ++ tests 3 ++ "-/\ndef x := 1\n", false),
    ("fake section in string", "FrenAst", production 1000 ++
      "def marker := \"\nsection Fren2Tests\nend Fren2Tests\n\"\n", false),
    ("CRLF physical lines", "FrenAstTests", (production 500).replace "\n" "\r\n", true),
    ("unterminated final line", "FrenAstTests", production 500 ++ "-- last", false)]
  for (name, owner, source, expected) in cases do
    let actual ← checkSource owner ("src/" ++ owner ++ "/quality-fixture.lean") source
    unless actual.isEmpty == expected do
      failures := failures.push s!"quality control {name}: expected acceptance={expected}, got {actual}"
    if name.startsWith "fake section in " then
      let diagnostic := s!"src/{owner}/quality-fixture.lean: {physicalLines source} physical source lines exceed 1000"
      unless actual == #[diagnostic] do
        failures := failures.push s!"quality control {name}: expected only the source-cap diagnostic, got {actual}"
  unless !owners.contains "Spec.Compiler.Hir" && !owners.contains "FrenTestMain" do
    failures := failures.push "quality inventory included legacy Fren1 documentation/driver infrastructure"
  let nested ← checkSource "FrenAst" "src/FrenAst/Spec/Compiler/Hir.lean" "import Lean\n"
  unless nested.any (·.contains "requires Lean module mode".toSlice) do
    failures := failures.push "Spec-like path inside a Fren2 runtime root escaped the module rule"
  unless physicalLines "" == 0 && physicalLines "\n" == 1 && physicalLines "a\n\n" == 2 &&
      physicalLines "a" == 1 && physicalLines "a\r\n" == 1 do
    failures := failures.push "physical line counting boundary"
  IO.println s!"Fren2 quality controls: {cases.length} header/line/section cases plus inventory/path/count controls"
  return failures

/-- The default layering job checks imports, actual header module mode and
physical source/test budgets for every file under the same Fren2 inventory. -/
def check : IO (Array String) := do
  let mut failures ← qualityControls
  let fixture ← checkSource "FrenBase" "fixture"
    "module\npublic import Lean\nimport /- nested /- comment -/ -/ FrenExpr\n"
  unless fixture.size == 1 && (fixture[0]!).contains "FrenBase may not import FrenExpr".toSlice do
    failures := failures.push s!"layering fixture did not reject FrenBase -> FrenExpr: {fixture}"
  let mut checked := 0
  let mut production := 0
  let mut standalone := 0
  for owner in owners do
    for path in ← files owner do
      let source ← IO.FS.readFile path
      failures := failures ++ (← checkSource owner path.toString source)
      checked := checked + 1
      if testOnly owner then standalone := standalone + 1 else production := production + 1
  IO.println s!"Fren2 quality inventory: {checked} physical files ({production} production, {standalone} standalone tests/driver/support); Spec wrappers and FrenTestMain excluded"
  return failures

end FrenTest.Layering
