-- Only the requirements that it implements: each module of Impls imports
-- those of its own, so that it waits only for them, not for every module of
-- Reqs.
-- keep-sorted start
import Fren
import Reqs.Check
-- keep-sorted end
open Fren.Lang

/-!
# The checks' verdicts (`Reqs/Check`)

The decisions in `FrenCore.Check` implement the comps of `check`: for every
answer the solver can give, the verdict and what is reported are as
required. Each obligation is proved by `decide`.
-/

namespace Fren.Impls

open Fren.Core (Answer Verdict CheckKind realizableVerdict expectVerdict vacuityVerdict coverVerdict
  determinismVerdict redundancyAsked kindsFor)

instance : Fren.Finite Answer := ⟨[.sat, .unsat, .unknown], by intro x; cases x <;> simp⟩
instance : Fren.Finite Verdict := ⟨[.pass, .fail, .inconclusive], by intro x; cases x <;> simp⟩

def toOutcome : Answer → check.Outcome
  | .sat => .Sat
  | .unsat => .Unsat
  | .unknown => .Unknown

def toVerdict : Verdict → check.Verdict
  | .pass => .Pass
  | .fail => .Fail
  | .inconclusive => .Inconclusive

instance : Fren.Finite CheckKind :=
  ⟨[.realizable, .inst, .«expect», .cover, .vacuity, .redundancy, .determinism, .definedness, .completeness,
    .disjointness], by intro x; cases x <;> simp⟩

def toCheckKind : CheckKind → check.Kind
  | .realizable => .Realizability
  | .inst => .InstanceAssumption
  | .«expect» => .Expectation
  | .cover => .Cover
  | .vacuity => .Vacuity
  | .redundancy => .Redundancy
  | .determinism => .Determinism
  | .definedness => .Definedness
  | .completeness => .Completeness
  | .disjointness => .Disjointness

instance : Fren.Finite Fren.Core.CheckedItem := ⟨[.component, .global, .body], by intro x; cases x <;> simp⟩

def toCheckedItem : Fren.Core.CheckedItem → check.CheckedItem
  | .component => .Component
  | .global => .GlobalExpectation
  | .body => .Body

impl applies: check::applies for (i : Fren.Core.CheckedItem) (k : CheckKind) {
  item := toCheckedItem i,
  kind := toCheckKind k,
  runs? := i.kinds.contains k,
}

impl realizable: check::realizability for (a c : Answer) {
  assume_q := toOutcome a,
  cex_q := toOutcome c,
  verdict := toVerdict (realizableVerdict a c).1,
  reports_cex? := (realizableVerdict a c).2.1,
  reports_vacuous? := (realizableVerdict a c).2.2,
}

impl expectation: check::expectation for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

impl cover_goal: check::cover_goal for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (coverVerdict q).1,
  reports_witness? := (coverVerdict q).2.1,
  reports_core? := (coverVerdict q).2.2,
}

impl instance_assumption: check::instance_assumption for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

impl non_vacuity: check::non_vacuity for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (vacuityVerdict q),
}

impl non_redundancy: check::non_redundancy for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (vacuityVerdict q),
}

impl redundancy_asked: check::redundancy_asked for (q : Answer) (v : Bool) {
  consistent_q := toOutcome q,
  vacuous? := v,
  asked? := redundancyAsked q v,
}

impl determinism: check::determinism for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (determinismVerdict q).1,
  reports_cex? := (determinismVerdict q).2,
}

-- `checkDefinedness` decides with `expectVerdict`, as `checkExpect` does.
impl definedness: check::definedness for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

-- `checkTable` decides with `expectVerdict`, as `checkDefinedness` does.
impl completeness: check::completeness for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

impl disjointness: check::disjointness for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_witness? := (expectVerdict q).2,
}

-- The two families of verdicts: `expectVerdict` for the checks that prove,
-- `vacuityVerdict` for those that ask whether something can hold.
impl proved: check::proved for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
}

impl satisfiable: check::satisfiable for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (vacuityVerdict q),
}

instance : Fren.Finite Fren.Core.Symbol :=
  ⟨[.input, .instanceVariable, .output, .function], by intro x; cases x <;> simp⟩

def toSymbol : Fren.Core.Symbol → check.Symbol
  | .input => .Input
  | .instanceVariable => .InstanceVariable
  | .output => .Output
  | .function => .Function

impl definitions: check::definitions for (k : CheckKind) {
  kind := toCheckKind k,
  substituted? := k.substitutes,
}

impl copied: check::copied for (s : Fren.Core.Symbol) {
  symbol := toSymbol s,
  copied? := s.copied,
}

def toRun : Fren.Core.Run → check.Run
  | .bySolver => .BySolver
  | .byTesting => .ByTesting
  | .skipped => .Skipped

impl run_of: check::by_testing for (k : CheckKind) (t : Bool) {
  kind := toCheckKind k,
  tested? := t,
  run := toRun (Fren.Core.runOf k t),
} by
  intro k t _
  cases k <;> cases t <;> decide

end Fren.Impls
