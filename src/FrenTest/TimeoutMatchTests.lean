-- keep-sorted start
import FrenCore.Check.Reporting
import FrenTest.TimeoutMatch
-- keep-sorted end

/-! Regression tests for #779, using the checks' actual diagnostic text. -/

namespace FrenTest.TimeoutMatchTests

open Fren.Core FrenTest.TimeoutMatch

private def result (kind : CheckKind) (detail : Detail) : CheckResult :=
  { kind, comp := `p, prop? := some `q, verdict := .fail, detail }

private def redundancy : CheckResult := result .redundancy (.redundant #[])
private def expectation : CheckResult := result .expect (.counterexample #[])

private def timeout (r : CheckResult) : CheckResult :=
  { r with verdict := .inconclusive, detail := .unknown "the solver returned unknown (TIMEOUT)" }

private def diagnostics (r : CheckResult) (file := "a.fren") (start := 6) : String :=
  String.join <| (messages false r).toList.map fun m =>
    ({ level := m.severity, msg := m.msg, range := { start, stop := start + 1 } } : Diagnostic).render
      file "\n\n    q\n".toList.toArray

private def run (r : CheckResult) : String :=
  diagnostics r ++ match r.verdict with
    | .inconclusive => "fren: 1 passed, 0 failed, 1 inconclusive, 0 redundant"
    | .fail => "fren: 1 passed, 1 failed, 0 inconclusive, 0 redundant"
    | .pass => "fren: 2 passed, 0 failed, 0 inconclusive, 0 redundant"

-- The old positive guard excused p::e's failure for p::r's redundancy
-- timeout at exactly the same file, line and column. Reverse it.
#guard !onlyTimedOut (run (timeout { redundancy with prop? := some `r }))
  (run { expectation with prop? := some `e })
-- Vary the subject and kind separately, at that very same position.
#guard !onlyTimedOut (run (timeout redundancy)) (run { redundancy with prop? := some `other })
#guard !onlyTimedOut (run (timeout redundancy)) (run expectation)
#guard onlyTimedOut (run (timeout redundancy)) (run redundancy)
#guard onlyTimedOut (run redundancy) (run (timeout redundancy))
#guard !onlyTimedOut (run redundancy) (run expectation)
#guard onlyTimedOut (run (timeout expectation))
  (run expectation ++ "\nFor more information about this error, try `fren --explain F0603`.")

-- A timeout versus a silent pass, or a cover's reported witness.
#guard onlyTimedOut (run (timeout expectation)) (run { expectation with verdict := .pass, detail := .none })
#guard onlyTimedOut (run (timeout (result .cover .none)))
  (run { result .cover (.witness #[]) with verdict := .pass })

private def cases : Array CheckResult := #[
  result .realizable (.conflict #[] #[]),
  result .expect (.counterexample #[]),
  result .cover (.vacuous #[]),
  result .vacuity (.vacuous #[]),
  redundancy,
  result .determinism (.nondeterministic #[] "1" "2"),
  { result .inst (.counterexample #[]) with target? := some (`callee, `a) },
  { result .inst (.counterexample #[]) with target? := some (`callee, `x.value), subsetTy? := "Positive" },
  { result .definedness (.counterexample #[]) with index? := some 0 },
  { result .definedness (.counterexample #[]) with index? := some 1, subsetTy? := "Positive" },
  { result .completeness (.counterexample #[]) with site? := some 0, goal? := some (.completeness .table) },
  { result .completeness (.counterexample #[]) with site? := some 1, goal? := some (.completeness .match) },
  { result .completeness (.counterexample #[]) with site? := some 2, goal? := some (.completeness .tableMatch) },
  { result .disjointness (.counterexample #[]) with
    site? := some 0, rows? := some (0, 1), goal? := some (.disjointness .table 0 1) },
  { result .disjointness (.counterexample #[]) with
    site? := some 1, rows? := some (0, 1), goal? := some (.disjointness .tableMatch 0 1) },
  { result .reachability .none with site? := some 0, goal? := some (.reachability .table 1) },
  { result .reachability .none with site? := some 1, goal? := some (.reachability .match 1) },
  { result .reachability .none with site? := some 2, goal? := some (.reachability .tableMatch 1) },
  { result .precondition (.counterexample #[]) with target? := some (`f, `pre) },
  { result .postcondition (.counterexample #[]) with target? := some (`f, `post) },
  { result .realizable (.conflict #[] #[]) with target? := some (`f, `post) },
  { result .realizable (.conflict #[] #[]) with target? := some (`f, `post), generic := true },
  { result .realizable (.vacuousAssumptions #[]) with target? := some (`f, `pre) }]

-- Check all of the supported verdict shapes against the real renderer.
#guard cases.all fun r => onlyTimedOut (run (timeout r)) (run r) && onlyTimedOut (run r) (run (timeout r))
-- Different kinds at the same subject and position never match.
#guard cases.all fun r => cases.all fun s =>
  r.kind == s.kind || !onlyTimedOut (run (timeout r)) (run s)

-- Site and index positions still matter, even with the same question.
#guard !onlyTimedOut (diagnostics (timeout expectation)) (diagnostics expectation (file := "b.fren"))
#guard !onlyTimedOut (diagnostics (timeout expectation)) (diagnostics expectation (start := 5))
#guard !onlyTimedOut (diagnostics (timeout expectation)) (diagnostics expectation (start := 1))

private def disjoint : CheckResult :=
  { result .disjointness (.counterexample #[]) with rows? := some (0, 1), goal? := some (.disjointness .table 0 1) }
private def reachable : CheckResult :=
  { result .reachability .none with goal? := some (.reachability .table 1) }

-- Row pairs, single rows/arms, the split's kind and target clauses are
-- identity too, even when their rendered positions happen to coincide.
#guard !onlyTimedOut (run (timeout disjoint))
  (run { disjoint with rows? := some (0, 2), goal? := some (.disjointness .table 0 2) })
#guard !onlyTimedOut (run (timeout reachable)) (run { reachable with goal? := some (.reachability .table 2) })
#guard !onlyTimedOut (run (timeout reachable)) (run { reachable with goal? := some (.reachability .match 1) })
#guard !onlyTimedOut (run (timeout { expectation with kind := .precondition, target? := some (`f, `pre) }))
  (run { expectation with kind := .precondition, target? := some (`f, `other) })
#guard !onlyTimedOut (run (timeout { expectation with kind := .inst, target? := some (`f, `a) }))
  (run { expectation with kind := .inst, target? := some (`g, `a) })
#guard !onlyTimedOut (run (timeout { expectation with kind := .definedness, subsetTy? := "Positive" }))
  (run { expectation with kind := .definedness, subsetTy? := "Negative" })

-- One timeout excuses at most one decided result, from the other run.
#guard !onlyTimedOut (diagnostics (timeout expectation)) (diagnostics expectation ++ diagnostics expectation)
#guard onlyTimedOut (diagnostics (timeout expectation) ++ diagnostics (timeout expectation))
  (diagnostics expectation ++ diagnostics expectation)
#guard !onlyTimedOut (diagnostics (timeout expectation) ++ diagnostics expectation) "fren: 2 passed"
#guard !onlyTimedOut (run (timeout expectation)) (diagnostics expectation ++ run redundancy)

-- An unchanged timeout does not excuse a changed summary. Nor does text
-- in a note, or an unlocated or ambiguous diagnostic, create an exemption.
#guard !onlyTimedOut (run (timeout expectation)) (diagnostics (timeout expectation) ++ "fren: 3 passed")
#guard !onlyTimedOut "fren: 1 passed" "fren: 2 passed"
#guard !onlyTimedOut "warning[F0710]: unused variable `x`\n --> a.fren:3:5\n  = note: the solver returned unknown (TIMEOUT)\n"
  (diagnostics expectation)
#guard !onlyTimedOut (run (timeout expectation))
  "error[F0304]: expectation `p::q` does not hold\n --> a.fren:3:5\n"
#guard !onlyTimedOut "warning[F0608]: could not decide whether `p::q` holds: the solver returned unknown (TIMEOUT)\n"
  (diagnostics expectation)
#guard !onlyTimedOut (run (timeout expectation))
  (run { expectation with verdict := .inconclusive, detail := .refuted .goal #[] })
#guard !onlyTimedOut (run (timeout expectation))
  (run { expectation with verdict := .inconclusive, detail := .unknown "solver error: invalid query" })
#guard !onlyTimedOut (run (timeout expectation))
  (run { expectation with verdict := .inconclusive, detail := .unknown "the solver returned unknown (INCOMPLETE)" })
private def unsatisfiable : CheckResult :=
  { result .realizable (.vacuousAssumptions #[]) with prop? := none }
#guard !onlyTimedOut (run (timeout unsatisfiable)) (run unsatisfiable)
#guard !onlyTimedOut (run (timeout { unsatisfiable with kind := .vacuity })) (run unsatisfiable)

end FrenTest.TimeoutMatchTests
