module

public import Lean
import FrenTest.Layering
import FrenTest.ProofLint.Simp
import FrenTest.ProofLint.Unsqueezed
-- Imported so that building the test driver builds the cases the jobs load.
import FrenTest.ProofLint.Cases

/-!
The proof-linter jobs of `fren_test`: `proofLint simp` and
`proofLint unsqueezed`. Each first checks its linter on the cases of
`FrenTest.ProofLint.Cases`, then lints every file of the Fren2 inventory that
the `layering` job checks.

Findings that predate the linters are listed in `test/fren2/proof-lint-allow.txt`.
A job fails on a finding that the list does not permit and on an entry that
no longer matches a finding, so the list can only shrink: the unit that
cleans the proofs empties it. Each job prints every finding, permitted or not.

Lean's own `linter.unusedSimpArgs` is on by default and reports during the
build, which `lake build --wfail` turns into a failure, so it needs no job.
The `unsqueezed` job checks only that no Fren2 file and no build option turns
it off.
-/

public section

namespace FrenTest.ProofLint
open Lean

private def allowPath : System.FilePath := "test/fren2/proof-lint-allow.txt"
private def casesModule : Name := `FrenTest.ProofLint.Cases
private def casesPath : String := "src/FrenTest/ProofLint/Cases.lean"

/-- The simp lemmas of the cases that each linter must report, and no others. -/
private def expected : List (String × String) :=
  [("simpNF", "twice_same"), ("simpNF", "same_same"), ("simpNF", "again_eq"),
   ("simpNF", "twice_both"), ("simpNF", "twice_zero_add"), ("simpNF", "up_eq"), ("simpNF", "next_eq"),
   ("simpLoop", "mix_comm"), ("simpLoop", "up_eq"), ("simpLoop", "next_eq")]

/-- Cases of the unsqueezed linter that no compiled proof can hold: a `grind`
that leaves its goal open does not compile, and the proof of an `impl` needs
a spec to check. They are parsed only. -/
private def parsedCases : String := "module
example (p : Prop) (h : p) : p := by
  grind -- unsqueezed
  exact h
example (p : Prop) (h : p) : p := by
  grind? [h] -- unsqueezed
  grind only [h] -- squeezed, so not reported
  simp? -- unsqueezed
  simp_all only [h]
  exact h
example (p : Prop) (h : p) : p ∧ p := by
  constructor
  simp -- unsqueezed
  simp
open Fren.Lang
impl closes: double for (n : Int) { n := n } by
  intro n
  simp
impl continues: double for (n : Int) { n := n } by
  simp -- unsqueezed
  rfl
"

/-- The lint targets with their module names: the layering inventory's files
and the Lean files of the spec under `src/Spec`, which hold the proofs about
Fren2's chapters although the inventory's rules for modules leave them out.
The cases must be reported, so they are no target. -/
private def targets : IO (Array (Name × System.FilePath)) := do
  let spec := (← System.FilePath.walkDir "src/Spec").filter (·.extension == some "lean")
  let paths := (← FrenTest.Layering.inventory).map (·.2) ++ spec.qsort (·.toString < ·.toString)
  let mut found := #[]
  for path in paths do
    let parts := (path.withExtension "").components.drop 1
    let module := parts.foldl (fun name part => Name.str name part) Name.anonymous
    if module != casesModule then found := found.push (module, path)
  return found

/-- Modules that cannot join the others in one environment: the two
executables' roots each define `main`, and loading the linter would load its
cases. A syntactic check shows that they declare no simp lemma. -/
private def apart (module : Name) : Bool :=
  [`Fren2TestMain, `Fren2FakeSolver].contains module || (`FrenTest.ProofLint).isPrefixOf module

private unsafe def load (modules : Array Name) : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  importModules (modules.map fun module => { module, importAll := true }) {} (loadExts := true)

private structure Allowed where
  key : String
  count : Nat

/-- The allowlist's entries for one linter: `linter key` permits one finding,
`linter key count` that many. `#` starts a comment. -/
private def allowed (linter : String) : IO (Except String (Array Allowed)) := do
  let mut entries := #[]
  for line in (← IO.FS.readFile allowPath).splitOn "\n" do
    let words := ((line.splitOn "#").headD "").splitOn " " |>.filter (· != "")
    match words with
    | [] => pure ()
    | [name, key] => if name == linter then entries := entries.push { key, count := 1 }
    | [name, key, count] =>
      let some count := count.toNat? | return .error s!"{allowPath}: bad count in '{line}'"
      if count == 0 then return .error s!"{allowPath}: remove the entry '{line}' rather than permit nothing"
      if name == linter then entries := entries.push { key, count }
    | _ => return .error s!"{allowPath}: cannot read '{line}'"
    unless ["simpNF", "simpLoop", "unsqueezed"].contains (words.headD "simpNF") do
      return .error s!"{allowPath}: unknown linter in '{line}'"
  return .ok entries

/-- Compares a linter's findings, as (key, description) pairs, with the
allowlist: every key must have exactly as many findings as its entries permit. -/
private def compare (linter : String) (findings : Array (String × String)) : IO (Array String) := do
  let entries ← match ← allowed linter with
    | .ok entries => pure entries
    | .error error => return #[error]
  let mut failures := #[]
  let keys := (findings.map (·.1) ++ entries.map (·.key)).foldl (init := #[]) fun keys key =>
    if keys.contains key then keys else keys.push key
  for key in keys do
    let actual := findings.filter (·.1 == key)
    let permitted := (entries.filter (·.key == key)).foldl (· + ·.count) 0
    if actual.size > permitted then
      let listed := "; ".intercalate (actual.map (·.2)).toList
      failures := failures.push s!"{linter} {key}: {actual.size} findings where {allowPath} permits {permitted}. Fix the new one rather than permit it: {listed}"
    else if actual.size < permitted then
      failures := failures.push s!"{linter} {key}: {actual.size} findings remain where {allowPath} permits {permitted}. Lower the entry to match, or remove it"
  return failures

private def describe (finding : Finding) : String :=
  s!"{finding.linter} {finding.decl}: {finding.message}"

private unsafe def simpJob : IO (Array String) := do
  let mut failures := #[]
  -- The cases, alone in their own environment.
  let (caseFindings, caseLemmas) ← lintSimp (← load #[casesModule]) #[casesModule]
  let reported := caseFindings.map fun finding =>
    (finding.linter, finding.decl.components.getLast?.map toString |>.getD "")
  for want in expected do
    unless reported.contains want do
      failures := failures.push s!"proof-lint cases: {want.1} did not report {want.2}"
  for finding in caseFindings do
    unless expected.contains (finding.linter, finding.decl.components.getLast?.map toString |>.getD "") do
      failures := failures.push s!"proof-lint cases: unexpected {describe finding}"
  IO.println s!"proof-lint cases: {caseLemmas} simp lemmas, {caseFindings.size} findings"
  -- The inventory.
  let all ← targets
  let together := all.filter (!apart ·.1)
  let env ← load (together.map (·.1))
  for (module, path) in all do
    if apart module then
      match ← parseFile env path.toString (← IO.FS.readFile path) with
      | .error error => failures := failures.push s!"{path}: cannot parse: {error}"
      | .ok commands =>
        if hasSimpAttribute commands then
          failures := failures.push s!"{path}: a simp lemma in a module that simpNF cannot load; declare it in another module"
  let (findings, lemmas) ← lintSimp env (together.map (·.1))
  for finding in findings do IO.println (describe finding)
  for linter in ["simpNF", "simpLoop"] do
    let mine := findings.filter (·.linter == linter)
    IO.println s!"{linter}: {mine.size} findings in {lemmas} simp lemmas of {together.size} modules"
    failures := failures ++ (← compare linter (mine.map fun finding => (toString finding.decl, finding.message)))
  return failures

/-- The reported tactics of a file as (line, text) pairs, or its parse error. -/
private def unsqueezedIn (env : Environment) (path source : String) :
    IO (Except String (Array (Nat × String) × Array Syntax)) := do
  match ← parseFile env path source with
  | .error error => return .error error
  | .ok commands =>
    let map := FileMap.ofString source
    let lines := source.splitOn "\n"
    let hits := (unsqueezed commands).map fun stx =>
      let line := (map.toPosition (stx.getPos?.getD 0)).line
      (line, (lines.getD (line - 1) "").trimAscii.toString)
    return .ok (hits, commands)

private def caseCheck (env : Environment) (path source : String) : IO (Array String) := do
  match ← unsqueezedIn env path source with
  | .error error => return #[s!"{path}: cannot parse: {error}"]
  | .ok (hits, _) =>
    let lines := (source.splitOn "\n").toArray
    let marked := (Array.range lines.size).filter (fun i => lines[i]!.trimAsciiEnd.toString.endsWith "-- unsqueezed")
      |>.map (· + 1)
    let reported := hits.map (·.1)
    let missed := marked.filter (!reported.contains ·)
    let extra := reported.filter (!marked.contains ·)
    IO.println s!"proof-lint cases: {path}: {marked.size} marked lines, {reported.size} reported"
    return missed.map (s!"{path}:{·}: the unsqueezed linter did not report this marked line") ++
      extra.map (s!"{path}:{·}: the unsqueezed linter reported an unmarked line")

private unsafe def unsqueezedJob : IO (Array String) := do
  let all ← targets
  let env ← load ((all.filter (!apart ·.1)).map (·.1))
  let mut failures ← caseCheck env casesPath (← IO.FS.readFile casesPath)
  failures := failures ++ (← caseCheck env "parsed cases" parsedCases)
  let mut findings := #[]
  let options := [`linter.unusedSimpArgs, `linter.all]
  for (_, path) in all do
    let source ← IO.FS.readFile path
    match ← unsqueezedIn env path.toString source with
    | .error error => failures := failures.push s!"{path}: cannot parse: {error}"
    | .ok (hits, commands) =>
      for (line, text) in hits do
        IO.println s!"unsqueezed {path}:{line}: {text}"
        findings := findings.push (path.toString, s!"line {line}: {text}")
      unless (optionMentions options commands).isEmpty do
        failures := failures.push s!"{path}: sets {options}; linter.unusedSimpArgs must stay on in Fren2"
  if ((← IO.FS.readFile "lakefile.lean").splitOn "unusedSimpArgs").length > 1 then
    failures := failures.push "lakefile.lean: sets linter.unusedSimpArgs; it must stay at its default, on"
  IO.println s!"unsqueezed: {findings.size} findings in {all.size} files"
  return failures ++ (← compare "unsqueezed" findings)

/-- The proof-linter jobs. -/
unsafe def check : List String → IO (Array String)
  | ["simp"] => simpJob
  | ["unsqueezed"] => unsqueezedJob
  | other => return #[s!"unknown proofLint job {other}"]

end FrenTest.ProofLint
