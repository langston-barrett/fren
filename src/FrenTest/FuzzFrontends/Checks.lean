-- keep-sorted start
import FrenTest.FuzzFrontends.Generate
import FrenTest.FuzzFrontends.Known
import FrenTest.FuzzFrontends.Running
import FrenTest.FuzzRecursion
-- keep-sorted end

open Lean FrenCli FrenCli.Eval
open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends (Report maskBetween headOf)

namespace FrenTest.FuzzFrontends

/-- How the differences `found` on the spec of `mode` and `seed`, those
that the solvers' time limits do not explain, fail to match `known`: those
that it does not list, each as often as it occurs beyond the times it is
listed, and the listed ones that do not occur as often as listed. A
listed one that does not occur on a spec where either front end left a
check undecided (`undecided`) may be hidden by it, and does not fail. -/
def unmatched (known : List Known) (mode : Mode) (seed : Nat) (found : Array String) (undecided : Bool) :
    Array String × List Known := Id.run do
  let mut unlisted := found
  let mut vanished := []
  for k in known do
    unless k.mode == mode && k.seed == seed do continue
    match unlisted.idxOf? k.difference with
    | some i => unlisted := unlisted.eraseIdx! i
    | none => unless undecided do vanished := vanished ++ [k]
  return (unlisted, vanished)

section
private def kd (mode : Mode := {}) (seed := 1) (difference := "d") : Known := { mode, seed, difference, issue := 0 }
-- A listed difference passes, and an unlisted one fails.
#guard unmatched [kd] {} 1 #["d"] false == (#[], [])
#guard (unmatched [kd] {} 1 #["d", "e"] false).1 == #["e"]
-- A listed one that no longer occurs fails, unless a check was undecided.
#guard ((unmatched [kd] {} 1 #[] false).2.map (·.difference)) == ["d"]
#guard (unmatched [kd] {} 1 #[] true).2.isEmpty
-- Another mode's or seed's entry does not match.
#guard (unmatched [kd (mode := { avoidKnown := true })] {} 1 #["d"] false).1 == #["d"]
#guard (unmatched [kd (seed := 2)] {} 1 #["d"] false).1 == #["d"]
-- Each entry matches one occurrence: an extra copy fails.
#guard (unmatched [kd] {} 1 #["d", "d"] false).1 == #["d"]
#guard unmatched [kd, kd] {} 1 #["d", "d"] false == (#[], [])
#guard ((unmatched [kd, kd] {} 1 #["d"] false).2.map (·.difference)) == ["d"]
end

/-- The static errors that the groups appended after the cuts of a spec
(`Mode.cuts`) add, given each cut's number of lines, each with the line
after which its group starts: each error of the `fren` command that is
not a check's result, located past the first cut's lines. Errors before
them, which may stop the checks already, are no group's. A static error
without a location, which the generator should never cause, is blamed on
the first group, when there are cuts. -/
def appendedErrors (cutLines : Array Nat) (diags : Array Diagnostic) : Array (Nat × Diagnostic) :=
  diags.filterMap fun d => do
    guard (d.severity == "error" && !FrenTest.Frontends.isCheckResult d && !FrenTest.Frontends.isStoppedTrailer d)
    if d.line == 0 then return (← cutLines[0]?, d)
    let start ← (cutLines.toList.filter (· < d.line)).max?
    return (start, d)

/-- The lines of the static errors of the `fren` command, those that are
not a check's result, the trailer that says that they stopped the checks,
nor an internal error, as the evaluator's that cannot read a formula
(`evaluatorUnread`), which is no error of the spec's and from which no
front end recovers (`knownKind`). -/
def staticErrorLines (diags : Array Diagnostic) : Array Nat :=
  diags.filterMap fun d =>
    if d.severity == "error" && !FrenTest.Frontends.isCheckResult d && !FrenTest.Frontends.isStoppedTrailer d
      && !d.text.startsWith "internal error" && d.line > 0 then some d.line else none

/-- The lines of the static errors that both front ends report, at the
same line and column (`staticErrorLines`): those that explain a
difference after them, which a static error that only one front end
reports does not, since it is a difference itself. -/
def sharedStaticErrorLines (cli hosted : Array Diagnostic) : Array Nat :=
  let isStatic (d : Diagnostic) := !(staticErrorLines #[d]).isEmpty
  (cli.filter fun d => isStatic d && hosted.any fun h => isStatic h && h.line == d.line && h.col == d.col).map
    (·.line)

section
private def errAt (line : Nat) (code : String := "F0304") : Diagnostic :=
  { line, severity := "error", text := "type mismatch", code? := some code }
-- An error before the first cut is no group's, even where the spec stops.
#guard (appendedErrors #[10, 20] #[errAt 3, { line := 0, severity := "error", text := Fren.Core.couldNotHeadline }]).isEmpty
-- An error in a group is caught, with the line its group starts after,
-- though an earlier one already stops the checks.
#guard (appendedErrors #[10, 20] #[errAt 3, errAt 12, errAt 25]).map (·.1) == #[10, 20]
-- A check's result and a warning are not static errors.
#guard (appendedErrors #[10] #[errAt 12 "F0603", { line := 12, severity := "warning", text := "w" }]).isEmpty
-- A static error without a location is blamed on the first group.
#guard (appendedErrors #[10, 20] #[{ line := 0, severity := "error", text := "unreadable", code? := some "F0001" }]).map (·.1) == #[10]
-- No cuts, as in `--guards`: nothing is a group's.
#guard (appendedErrors #[] #[errAt 12]).isEmpty
-- Only the static errors that both front ends report, at the same place.
#guard sharedStaticErrorLines #[errAt 3, errAt 7, errAt 9 "F0603"] #[{ errAt 3 with code? := none }, errAt 5,
  errAt 9] == #[3]
-- An internal error is no static error of the spec's.
#guard staticErrorLines #[errAt 3, { line := 25, severity := "error", text := "internal error: the evaluator does \
  not know the meaning of a formula of `fz::c0`" }] == #[3]
end

/-- A shared internal error or non-timeout undecided check still fails
the cardinality regressions. Only an explicit solver timeout is excused. -/
def setCardProblem? (d : Diagnostic) : Option String :=
  let h := headOf d
  let timedOut := !d.text.contains "solver error" &&
    (h.endsWith ": the solver returned unknown (TIMEOUT)" || h.endsWith ": TIMEOUT")
  if h.startsWith "internal error:" ||
      (h.startsWith "could not decide" && !timedOut) then some h else none

def setCardProblems (ran : Ran) : Array String :=
  (ran.cli ++ ran.hosted).filterMap setCardProblem?

section
private def cardUndecided (code? : Option String) (why : String) : Diagnostic :=
  { line := 1, severity := "error", code?, text := "could not decide whether `p::g` follows: " ++ why }
-- Both readers' ordinary timeouts stay eligible for the time-limit filter.
#guard (setCardProblem? (cardUndecided (some "F0608") "the solver returned unknown (TIMEOUT)")).isNone
#guard (setCardProblem? (cardUndecided none "TIMEOUT")).isNone
-- Agreement on a non-timeout unknown is still a cardinality regression.
#guard ([some "F0608", none].all fun code? =>
  ["INCOMPLETE", "RESOURCEOUT", "the solver returned unknown (INCOMPLETE)",
    "the solver returned unknown (RESOURCEOUT)", "undecided\nnote: TIMEOUT"].all fun why =>
    (setCardProblem? (cardUndecided code? why)).isSome)
-- #820 was a solver error, not a timeout, even when both readers agreed.
#guard (setCardProblem? (cardUndecided (some "F0608") "solver error: No more values for type E")).isSome
#guard (setCardProblem? (cardUndecided none "solver error: No more values for type E")).isSome
#guard (setCardProblem? (cardUndecided none "solver error: TIMEOUT")).isSome
#guard (setCardProblem? { line := 1, severity := "error", text := "internal error: refuted model" }).isSome
end

/-- Fresh runs of a generator that promises well-typed specs reject
shared static errors. Keep the cardinality modes' stricter checks too. -/
def freshProblems (mode : Mode) (ran : Ran) : Array String :=
  (if !(mode.genericFunctions || mode.shortInductions || mode.confirmCounts || mode.confirmArguments || mode.confirmMatches) && (mode.setCard || mode.setCardFallback) then setCardProblems ran else #[]) ++
    (if mode.genericFunctions || mode.shortInductions || mode.confirmMatches || mode.confirmCounts || mode.confirmArguments || mode.setCard || mode.setCardFallback || mode.genericTypes then
      (appendedErrors #[0] ran.cli ++ appendedErrors #[0] ran.hosted).map fun (_, d) =>
        s!"unexpected static error: {headOf d}"
     else #[])

section
private def sharedDiagnostic (d : Diagnostic) : Ran := {
  comparison := {}, reports := "", errors := #[], cli := #[d], hosted := #[d] }
private def sharedError (code : String) : Ran :=
  sharedDiagnostic { line := 1, severity := "error", text := "shared error", code? := some code }
-- Agreement on an invalid Bool binder cannot count as generic-type coverage.
#guard !(freshProblems { genericTypes := true } (sharedError "F0303")).isEmpty
-- Expected failed comparisons remain valid generated checks.
#guard (freshProblems { genericTypes := true } (sharedError "F0603")).isEmpty
-- The new mode leaves the existing modes' treatment of errors unchanged.
#guard (freshProblems {} (sharedError "F0303")).isEmpty
-- Generic-function mode keeps its existing priority over cardinality flags.
#guard !(freshProblems { genericFunctions := true } (sharedError "F0303")).isEmpty
#guard (freshProblems { genericFunctions := true, setCard := true }
  (sharedDiagnostic (cardUndecided (some "F0608") "INCOMPLETE"))).isEmpty
#guard !(freshProblems { setCard := true }
  (sharedDiagnostic (cardUndecided (some "F0608") "INCOMPLETE"))).isEmpty
-- Short induction preserves main's static-error check and flag priority.
#guard !(freshProblems { shortInductions := true } (sharedError "F0303")).isEmpty
#guard (freshProblems { shortInductions := true, setCard := true }
  (sharedDiagnostic (cardUndecided (some "F0608") "INCOMPLETE"))).isEmpty
-- Confirmation worker diagnostics retain their static-error policy when
-- combined with the new generic-type flag. Count and argument generators
-- keep their earlier selection priority too.
#guard !(freshProblems { confirmCounts := true, genericTypes := true } (sharedError "F0303")).isEmpty
#guard !(freshProblems { confirmMatches := true, genericTypes := true } (sharedError "F0303")).isEmpty
#guard !(freshProblems { confirmArguments := true, genericTypes := true } (sharedError "F0303")).isEmpty
#guard (freshProblems { confirmCounts := true, setCard := true }
  (sharedDiagnostic (cardUndecided (some "F0608") "INCOMPLETE"))).isEmpty
end

/-- Checks the specs of the corpus with both front ends, in this process.
Each failure is a difference that `knownDifferences` does not list, or a
listed one that no longer occurs (`unmatched`), leaving out those that
the solvers' time limits explain; or a static error in a group that the
generator appends after a cut (`appendedErrors`), which it must not
append, whether or not the spec stops before it. Finite-cardinality
regressions also reject shared internal errors and non-timeout undecided
queries.
The recursion-position mode also checks its promised verdict: valid cases
can fail a comparison, and invalid ones must reach `F0447`, rather than an
earlier static error. -/
def corpusFailures (env : Environment) (dir : System.FilePath) (specs : List (Mode × Nat)) :
    IO (Array String) := do
  IO.FS.createDirAll dir
  let path := dir / s!"corpus-{← IO.Process.getPID}.fren"
  let mut failures := #[]
  for (mode, s) in specs do
    let ran ← runFrontends env path (mode.spec s) (mode.confirm || mode.confirmMatches || mode.confirmCounts || mode.confirmArguments)
    let c := ran.comparison
    if !mode.genericFunctions && (mode.setCard || mode.setCardFallback) then
      for problem in setCardProblems ran do
        failures := failures.push s!"seed {s}{flags mode}: {problem}"
    let again := s!"`lake exe fren_fuzz_frontends{flags mode} --count 1 --seed {s}`"
    let (unlisted, vanished) := unmatched knownDifferences mode s c.decided c.undecided
    for f in unlisted do
      failures := failures.push s!"seed {s}{flags mode}: the front ends differ: {f.replace "\n" " "}\n  \
        reproduce it with {again}; if its issue is known, list it in `knownDifferences` as\n  \
        \{ mode := {mode.lean}, seed := {s}, difference := {(toJson f).compress}, issue := ISSUE }"
    for k in vanished do
      failures := failures.push s!"seed {s}{flags mode}: the front ends no longer differ by `{k.difference}` (#{k.issue}); \
        remove it from `knownDifferences`, or, if a change to the generator removed it, leave every seed's spec as it was"
    if mode.decidable then
      -- CLI internal errors have no code; expected failed checks do.
      -- A hosted-only error is already an unlisted front-end difference.
      for d in ran.cli do
        if d.severity == "error" && d.code?.isNone then
          failures := failures.push s!"seed {s}{flags mode}: {d.text}\n  reproduce it with {again}"
    if ({ mode with avoidKnown := false } : Mode) == { recursionPositions := true } then
      let rejects := (Id.run (FuzzRecursion.genCase.run' (rngOf s))).rejects
      let errors := ran.errors.toList.eraseDups
      if (rejects && errors != ["F0447"]) || (!rejects && errors.any (· != "F0603")) then
        let expected := if rejects then "a structural-recursion error (F0447)" else "only failed comparisons (F0603), if any"
        failures := failures.push s!"seed {s}{flags mode}: generator expected {expected}, got {errors}; reproduce with {again}"
    let cutLines := (mode.cuts s).map fun c => (c.splitOn "\n").length - 1
    let appended := appendedErrors cutLines ran.cli ++
      (if mode.confirmMatches || mode.confirmCounts || mode.confirmArguments then appendedErrors cutLines ran.hosted else #[])
    for (start, d) in appended do
      failures := failures.push s!"seed {s}{flags mode}: what the generator appends after line {start} adds a static \
        error at line {d.line}, error{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}; an error stops \
        every check of the spec, so put deliberate errors in a mode of their own \
        (print the spec with {again.replace "--count 1 --seed" "--print"})"
  try IO.FS.removeFile path catch _ => pure ()
  return failures

end FrenTest.FuzzFrontends
