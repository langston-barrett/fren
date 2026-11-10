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

Findings that predate the linters are listed in `test/fren2/proof-lint-allow.txt`,
one entry for each finding, by its identity: the declaration and the
finding's number within it, never a line. A job fails on a finding that no
entry names and on an entry that names no finding, so the list can only
shrink: the unit that cleans the proofs empties it. A finding that replaces
another under the same identity (the same declaration and number) is the one
change that the list cannot see. Each job prints every finding, permitted or
not, with its identity.

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
   ("simpNF", "twice_both"), ("simpNF", "same_zero"), ("simpNF", "twice_zero_add"),
   ("simpLoop", "mix_comm"), ("simpLoop", "spin_eq"), ("simpLoop", "star_self")] ++
  -- simp fails on the left-hand side of every lemma of a cycle; `simpLoop`
  -- reports the `r` lemmas' cycle of five no more, beyond its bound.
  ["up_eq", "next_eq", "spin_eq", "star_self", "q1_eq", "q2_eq", "q3_eq", "q4_eq",
   "r1_eq", "r2_eq", "r3_eq", "r4_eq", "r5_eq"].map (("simpNF", ·)) ++
  ["up_eq", "next_eq", "q1_eq", "q2_eq", "q3_eq", "q4_eq"].map (("simpLoop", ·))

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

/-- The allowlist's entries for one linter: a line `linter identity` permits
the one finding of that identity. A line that starts with `#` is a comment. -/
private def allowed (linter : String) : IO (Except String (Array String)) := do
  let mut entries := #[]
  for line in (← IO.FS.readFile allowPath).splitOn "\n" do
    match (if line.startsWith "#" then "" else line).splitOn " " |>.filter (· != "") with
    | [] => pure ()
    | [name, identity] =>
      unless ["simpNF", "simpLoop", "unsqueezed"].contains name do
        return .error s!"{allowPath}: unknown linter in '{line}'"
      if name == linter then entries := entries.push identity
    | _ => return .error s!"{allowPath}: cannot read '{line}'"
  return .ok entries

/-- What separates a linter's findings, as (identity, description) pairs, from
the entries that permit them: each finding needs an entry of its identity,
and each entry a finding. -/
private def unmatched (linter : String) (entries : Array String) (findings : Array (String × String)) :
    Array String := Id.run do
  let mut failures := #[]
  for (identity, description) in findings do
    unless entries.contains identity do
      failures := failures.push s!"{linter} {identity}: a finding that {allowPath} does not permit. Fix it rather than permit it: {description}"
  for i in [:entries.size] do
    if (entries.extract 0 i).contains entries[i]! then
      failures := failures.push s!"{linter} {entries[i]!}: {allowPath} lists this entry twice"
    else unless findings.any (·.1 == entries[i]!) do
      failures := failures.push s!"{linter} {entries[i]!}: {allowPath} permits a finding that is gone. Remove the entry"
  return failures

/-- Checks `unmatched` itself: a finding that takes the place of a fixed one
in the same file is reported along with the fixed one's entry, and an entry
whose finding is gone is reported. -/
private def allowlistCases : Array String := Id.run do
  let finding (identity : String) := (identity, "text")
  let cases : List (String × Array String × Array String × List String) :=
    [("all permitted", #["f:a#1", "f:a#2"], #["f:a#1", "f:a#2"], []),
     ("one fixed and one new in the same file", #["f:a#1", "f:b#1"], #["f:a#1", "f:c#1"],
      ["f:c#1: a finding", "f:b#1: test/"]),
     ("one fixed in a declaration with two", #["f:a#1", "f:a#2"], #["f:a#1"], ["f:a#2: test/"]),
     ("a new finding", #[], #["f:a#1"], ["f:a#1: a finding"]),
     ("an entry listed twice", #["f:a#1", "f:a#1"], #["f:a#1"], ["f:a#1: test/"])]
  let mut failures := #[]
  for (name, entries, findings, want) in cases do
    let got := unmatched "x" entries (findings.map finding)
    unless got.size == want.length && want.all (fun part => got.any (·.startsWith s!"x {part}")) do
      failures := failures.push s!"proof-lint allowlist case '{name}': got {got}"
  return failures

private def compare (linter : String) (findings : Array (String × String)) : IO (Array String) := do
  match ← allowed linter with
  | .ok entries => return unmatched linter entries findings
  | .error error => return #[error]

/-- A linter's findings with their identities: the declaration, `#` and the
finding's number among the linter's findings for it, from 1. -/
private def identified (findings : Array Finding) : Array (String × Finding) := Id.run do
  let mut found : Array (String × Finding) := #[]
  for finding in findings do
    let before := (found.filter (·.2.decl == finding.decl)).size
    found := found.push (s!"{finding.decl}#{before + 1}", finding)
  return found

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
  for linter in ["simpNF", "simpLoop"] do
    let mine := identified (findings.filter (·.linter == linter))
    for (identity, finding) in mine do IO.println s!"{linter} {identity}: {finding.message}"
    IO.println s!"{linter}: {mine.size} findings in {lemmas} simp lemmas of {together.size} modules"
    failures := failures ++ (← compare linter (mine.map fun (identity, finding) => (identity, finding.message)))
  return failures

/-- The reported tactics of a file as (identity, line, text), or its parse error. -/
private def unsqueezedIn (env : Environment) (path source : String) :
    IO (Except String (Array (String × Nat × String) × Array Syntax)) := do
  match ← parseFile env path source with
  | .error error => return .error error
  | .ok commands =>
    let map := FileMap.ofString source
    let lines := source.splitOn "\n"
    let hits := (unsqueezed commands).map fun (identity, stx) =>
      let line := (map.toPosition (stx.getPos?.getD 0)).line
      (s!"{path}:{identity}", line, (lines.getD (line - 1) "").trimAscii.toString)
    return .ok (hits, commands)

private def caseCheck (env : Environment) (path source : String) : IO (Array String) := do
  match ← unsqueezedIn env path source with
  | .error error => return #[s!"{path}: cannot parse: {error}"]
  | .ok (hits, _) =>
    let lines := (source.splitOn "\n").toArray
    let marked := (Array.range lines.size).filter (fun i => lines[i]!.trimAsciiEnd.toString.endsWith "-- unsqueezed")
      |>.map (· + 1)
    let reported := hits.map (·.2.1)
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
      for (identity, line, text) in hits do
        IO.println s!"unsqueezed {identity} (line {line}): {text}"
        findings := findings.push (identity, s!"line {line}: {text}")
      unless (optionMentions options commands).isEmpty do
        failures := failures.push s!"{path}: sets {options}; linter.unusedSimpArgs must stay on in Fren2"
  if ((← IO.FS.readFile "lakefile.lean").splitOn "unusedSimpArgs").length > 1 then
    failures := failures.push "lakefile.lean: sets linter.unusedSimpArgs; it must stay at its default, on"
  IO.println s!"unsqueezed: {findings.size} findings in {all.size} files"
  return failures ++ (← compare "unsqueezed" findings)

/-- The proof-linter jobs. -/
unsafe def check : List String → IO (Array String)
  | ["simp"] => return allowlistCases ++ (← simpJob)
  | ["unsqueezed"] => return allowlistCases ++ (← unsqueezedJob)
  | other => return #[s!"unknown proofLint job {other}"]

end FrenTest.ProofLint
