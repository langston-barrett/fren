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
   ("FrenProp", ["FrenSexp"]), ("FrenAst", base), ("FrenModule", base),
   ("FrenExpr", base), ("FrenMir", base ++ ["FrenExpr", "FrenModule"]),
   ("FrenLir", base ++ ["FrenMir"]), ("FrenOir", base ++ ["FrenLir"]),
   ("FrenParse", base ++ ["FrenAst"]),
   ("FrenAstToHir", base ++ ["FrenAst", "FrenModule", "FrenExpr"]),
   ("FrenHirToThir", base ++ ["FrenModule", "FrenExpr"]),
   ("FrenThirDesugar", base ++ ["FrenModule", "FrenExpr"]),
   ("FrenThirToMir", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenMirToMono", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenMonoToFo", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenFoToFlat", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenMirToLean", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenFlatToLir", base ++ ["FrenExpr", "FrenMir", "FrenLir"]),
   ("FrenLirToOir", base ++ ["FrenLir", "FrenOir"]),
   ("FrenOirToSmt", base ++ ["FrenOir"]),
   ("FrenEval", base ++ ["FrenModule", "FrenExpr", "FrenMir"]),
   ("FrenLirEval", base ++ ["FrenLir"]),
   ("FrenGen", base ++ ["FrenProp"] ++ ir),
   ("FrenCli2", []), ("FrenHosted2", [])]

private def roots : List String := allowed.map Prod.fst
private def tests : List String := roots.map (· ++ "Tests")

private def permits (owner imported : String) : Bool := Id.run do
  if ["Lean", "Std", "Init"].contains imported then return true
  if owner == imported then return true
  if owner == "FrenProp" && imported == "Plausible" then return true
  if owner == "Fren2TestMain" then return (roots ++ tests).contains imported
  if let some original := owner.dropSuffix? "Tests" then
    let original := original.toString
    if !roots.contains original then return false
    return (base ++ ["FrenProp", "FrenGen", original] ++
      (if ["FrenCli2", "FrenHosted2"].contains original then roots else
        (allowed.lookup original).getD [])).contains imported
  if ["FrenCli2", "FrenHosted2"].contains owner then
    return roots.contains imported && imported != "FrenProp"
  return ((allowed.lookup owner).getD []).contains imported

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

private def rootOf (name : Lean.Name) : String :=
  (name.toString.splitOn ".").headD ""

private def checkSource (owner path source : String) : IO (Array String) := do
  let (imports, _, messages) ← Lean.Elab.parseImports source (some path)
  if messages.hasErrors then return #[s!"{path}: cannot parse Lean header"]
  let mut failures := #[]
  for i in imports do
    let imported := rootOf i.module
    unless permits owner imported do
      failures := failures.push s!"{path}: {owner} may not import {imported} ({i.module})"
  return failures

private def files (root : String) : IO (Array System.FilePath) := do
  let path : System.FilePath := "src" / root
  let mut result := #[path.withExtension "lean"]
  if ← path.isDir then
    result := result ++ (← path.walkDir).filter (·.extension == some "lean")
  return result

/-- Check direct imports in every Fren2 library and in its test driver. -/
def check : IO (Array String) := do
  let mut failures := #[]
  -- Exercise the real parser and edge check with an illegal import after
  -- a nested comment and a legal public import.
  let fixture ← checkSource "FrenBase" "fixture"
    "module\npublic import Lean\nimport /- nested /- comment -/ -/ FrenExpr\n"
  unless fixture.size == 1 && (fixture[0]!).contains "FrenBase may not import FrenExpr".toSlice do
    failures := failures.push s!"layering fixture did not reject FrenBase -> FrenExpr: {fixture}"
  for owner in roots ++ tests ++ ["Fren2TestMain"] do
    for path in ← files owner do
      failures := failures ++ (← checkSource owner path.toString (← IO.FS.readFile path))
  return failures

end FrenTest.Layering
