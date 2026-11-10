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
one entry for each finding, by its identity, never a line or a position: a
simp lemma and the finding's kind, or a declaration and the tactic's source
text with its white space squeezed. A job fails on a finding that no entry
names and on an entry that names no finding, so the list can only shrink: the
unit that cleans the proofs empties it. A finding that replaces another has
another identity, so both the new finding and the stale entry are reported.
A declaration is named with its namespaces and named sections, and an
unnamed one by a hash of its signature. Only order tells apart two calls of
the same text in one declaration, two unnamed declarations of the same
signature in one scope, and two rewrites of one simp lemma with the same
left-hand side. Each job prints every finding, permitted or not, with its
identity.

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

/-- The findings that each linter must report for the simp lemmas of the
cases, by lemma and kind: exactly these, each once. -/
private def expected : List (String × String) :=
  let cycles := ["up_eq", "next_eq", "star_self", "q1_eq", "q2_eq", "q3_eq", "q4_eq"]
  let beyond := ["r1_eq", "r2_eq", "r3_eq", "r4_eq", "r5_eq"]
  [("simpNF", "twice_same:lhs-not-normal"), ("simpNF", "same_same:redundant"),
   ("simpNF", "again_eq:reducible-sides"), ("simpNF", "same_zero:redundant"),
   ("simpNF", "twice_zero_add:lhs-not-normal"),
   -- One finding for each rewrite of the conjunction, and no other; a
   -- rewrite is named by its left-hand side.
   ("simpNF", "twice_both:never-applies@twice 2"), ("simpNF", "twice_both:lhs-not-normal@twice (0 + n)"),
   ("simpNF", "turn_both:simp-fails@turn n 1"), ("simpLoop", "turn_both:self-instance@turn n 1"),
   ("simpLoop", "turn_both:depth-limit@turn n 1"),
   -- Two rewrites with findings of one kind.
   ("simpNF", "same_pair:redundant@same (same 1)"), ("simpNF", "same_pair:redundant@same (same 2)"),
   ("simpLoop", "mix_comm:renaming"),
   ("simpNF", "spin_eq:simp-fails"), ("simpLoop", "spin_eq:self-instance"),
   ("simpLoop", "spin_eq:depth-limit"),
   ("simpNF", "grow_eq:simp-fails"), ("simpLoop", "grow_eq:self-instance"),
   ("simpLoop", "grow_eq:step-limit")] ++
  -- Simp fails and runs away on the left-hand side of every lemma of a cycle;
  -- the cycle search names the cycles within its bound.
  (cycles ++ beyond).map (("simpNF", s!"{·}:simp-fails")) ++
  (cycles ++ beyond).map (("simpLoop", s!"{·}:depth-limit")) ++
  cycles.map (("simpLoop", s!"{·}:cycle")) ++
  -- Each is redundant although only its right-hand side simplifies, to its
  -- left-hand side, by the other lemmas of its cycle.
  (cycles ++ beyond).map (("simpNF", s!"{·}:redundant"))

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
the one finding of that identity, which is the rest of the line. A line that
starts with `#` is a comment. -/
private def allowed (linter : String) : IO (Except String (Array String)) := do
  let mut entries := #[]
  for line in (← IO.FS.readFile allowPath).splitOn "\n" do
    if line.startsWith "#" || line.trimAscii.toString.isEmpty then continue
    match line.splitOn " " with
    | name :: identity@(_ :: _) =>
      unless ["simpNF", "simpLoop", "unsqueezed"].contains name do
        return .error s!"{allowPath}: unknown linter in '{line}'"
      if name == linter then entries := entries.push (" ".intercalate identity)
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
     ("an entry listed twice", #["f:a#1", "f:a#1"], #["f:a#1"], ["f:a#1: test/"]),
     ("one finding of a simp lemma fixed and one of another kind new", #["l:redundant"],
      #["l:lhs-not-normal"], ["l:lhs-not-normal: a finding", "l:redundant: test/"]),
     -- A conjunct replaced by another that gives a finding of the same kind.
     (let identity (side : String) : String :=
        ({ linter := "simpNF", decl := `l, kind := "redundant", message := "", side } : Finding).identity
      ("one rewrite of a simp lemma replaced by another of the same kind", #[identity "f a", identity "g a"],
       #[identity "f b", identity "g a"], [s!"{identity "f b"}: a finding", s!"{identity "f a"}: test/"]))]
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

private def describe (finding : Finding) : String :=
  s!"{finding.linter} {finding.identity}: {finding.message}"

private unsafe def simpJob : IO (Array String) := do
  let mut failures := #[]
  -- The cases, alone in their own environment.
  let (caseFindings, caseLemmas) ← lintSimp (← load #[casesModule]) #[casesModule]
  -- By the last part of the lemma's name, which the cases' namespace precedes.
  let short (finding : Finding) : String × String :=
    let side := (finding.side.replace s!"{casesModule}." "").replace "✝" ""
    (finding.linter, s!"{finding.decl.components.getLast?.getD .anonymous}:{finding.kind}" ++
      (if side.isEmpty then "" else s!"@{side}"))
  let reported := caseFindings.map short
  let identities := caseFindings.map fun finding => (finding.linter, finding.identity)
  for i in [:identities.size] do
    if (identities.extract 0 i).contains identities[i]! then
      failures := failures.push s!"proof-lint cases: two findings share the identity {identities[i]!}"
  for want in expected do
    let times := (reported.filter (· == want)).size
    unless times == 1 do
      failures := failures.push s!"proof-lint cases: {want.1} reported {want.2} {times} times, not once"
  for finding in caseFindings do
    unless expected.contains (short finding) do
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
    let mine := findings.filter (·.linter == linter)
    for finding in mine do IO.println (describe finding)
    IO.println s!"{linter}: {mine.size} findings in {lemmas} simp lemmas of {together.size} modules"
    failures := failures ++ (← compare linter (mine.map fun finding => (finding.identity, finding.message)))
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

/-- Checks the identities on sources before and after a change: the entries
are the first source's findings, and the second's must leave the given
numbers of new findings and of stale entries. -/
private def identityCases (env : Environment) : IO (Array String) := do
  let named := "theorem t (p : Prop) (h : p) : p := by\n"
  let head := "module\n" ++ named
  let one := "example (p : Prop) (h : p) : p := by\n"
  let two := "example (q : Prop) (h : q) : q := by\n"
  let cases : List (String × String × String × Nat × Nat) :=
    [("one fixed and another added in the same declaration",
      head ++ "  simp at h\n  exact h\n", head ++ "  simp only [] at h\n  simp [h]\n  exact h\n", 1, 1),
     ("the first of two fixed and a third added after the second",
      head ++ "  simp at h\n  grind\n  exact h\n", head ++ "  grind\n  simp [h]\n  exact h\n", 1, 1),
     ("one fixed in an unnamed declaration and the same call added in another",
      "module\n" ++ one ++ "  simp at h\n  exact h\n" ++ two ++ "  exact h\n",
      "module\n" ++ one ++ "  exact h\n" ++ two ++ "  simp at h\n  exact h\n", 1, 1),
     ("moved and laid out anew",
      head ++ "  simp [h] at h\n  exact h\n",
      "module\n" ++ one ++ "  exact h\n\ntheorem t (p : Prop) (h : p) : p := by\n\n  simp  [h]\n      at h\n  exact h\n", 0, 0),
     ("one fixed in a namespace and the same call added to the same name in another",
      "module\nnamespace A\n" ++ named ++ "  simp at h\n  exact h\nend A\nnamespace B\n" ++ named ++ "  exact h\nend B\n",
      "module\nnamespace A\n" ++ named ++ "  exact h\nend A\nnamespace B\n" ++ named ++ "  simp at h\n  exact h\nend B\n", 1, 1),
     ("one fixed in a named section and the same call added to the same label in another",
      "module\nsection A\n" ++ one ++ "  simp at h\n  exact h\nend A\nsection B\n" ++ one ++ "  exact h\nend B\n",
      "module\nsection A\n" ++ one ++ "  exact h\nend A\nsection B\n" ++ one ++ "  simp at h\n  exact h\nend B\n", 1, 1),
     ("one fixed in an unnamed declaration and the same call added in another of the same signature",
      "module\n" ++ one ++ "  simp at h\n  exact h\n" ++ one ++ "  exact h\n",
      "module\n" ++ one ++ "  exact h\n" ++ one ++ "  simp at h\n  exact h\n", 1, 1),
     ("a namespace moved after another of the same declaration name",
      "module\nnamespace A\n" ++ named ++ "  simp at h\n  exact h\nend A\nnamespace B\n" ++ named ++ "  exact h\nend B\n",
      "module\nnamespace B\n" ++ named ++ "  exact h\nend B\n\nnamespace A\n" ++ named ++ "  simp at h\n  exact h\nend A\n", 0, 0),
     ("one of two calls of the same text fixed",
      head ++ "  simp at h\n  simp at h\n  exact h\n", head ++ "  simp at h\n  exact h\n", 0, 1)]
  let mut failures := #[]
  for (name, before, after, fresh, stale) in cases do
    match ← unsqueezedIn env "f" before, ← unsqueezedIn env "f" after with
    | .ok (entries, _), .ok (findings, _) =>
      let got := unmatched "x" (entries.map (·.1)) (findings.map fun (identity, _, text) => (identity, text))
      let count (part : String) := (got.filter fun line => (line.splitOn part).length > 1).size
      unless entries.size > 0 && count "does not permit" == fresh && count "is gone" == stale && got.size == fresh + stale do
        failures := failures.push s!"proof-lint identity case '{name}': entries {entries.map (·.1)}, got {got}"
    | _, _ => failures := failures.push s!"proof-lint identity case '{name}': cannot parse"
  return failures

private unsafe def unsqueezedJob : IO (Array String) := do
  let all ← targets
  let env ← load ((all.filter (!apart ·.1)).map (·.1))
  let mut failures ← caseCheck env casesPath (← IO.FS.readFile casesPath)
  failures := failures ++ (← caseCheck env "parsed cases" parsedCases)
  failures := failures ++ (← identityCases env)
  let mut findings := #[]
  let options := [`linter.unusedSimpArgs, `linter.all]
  for (_, path) in all do
    let source ← IO.FS.readFile path
    match ← unsqueezedIn env path.toString source with
    | .error error => failures := failures.push s!"{path}: cannot parse: {error}"
    | .ok (hits, commands) =>
      for (identity, line, text) in hits do
        IO.println s!"unsqueezed {identity}\t(line {line})"
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
