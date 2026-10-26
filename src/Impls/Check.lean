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
  determinismVerdict redundancyAsked kindsFor reachabilityAsked completenessAsked reachUses)

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
    .disjointness, .precondition, .postcondition, .reachability], by intro x; cases x <;> simp⟩

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
  | .precondition => .Precondition
  | .postcondition => .Postcondition
  | .reachability => .Reachability

instance : Fren.Finite Fren.Core.CheckedItem := ⟨[.component, .global, .body, .contract], by intro x; cases x <;> simp⟩

def toCheckedItem : Fren.Core.CheckedItem → check.CheckedItem
  | .component => .Component
  | .global => .GlobalExpectation
  | .body => .Body
  | .contract => .Contract

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

-- `checkReach` decides with `vacuityVerdict`, as `checkVacuity` does.
impl reachability: check::reachability for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (vacuityVerdict q),
}

-- Both front ends ask about the arms that `splitGoals` asks about, by
-- `reachabilityAsked`, and about the completeness of a `match` by
-- `completenessAsked`, from what `checkMatch` gives.
impl reachability_asked: check::reachability_asked for (g a : Bool) {
  guarded? := g,
  after_guard? := a,
  asked? := reachabilityAsked g a,
}

-- `Comp.reachHyps` keeps the hypotheses of definedness that `reachUses`
-- keeps, the enclosing constraint being the one that the site names.
impl reach_hypothesis: check::reach_hypothesis for (d e : Bool) {
  definedness? := d,
  enclosing? := e,
  used? := reachUses d e,
}

impl completeness_asked: check::completeness_asked for (u : Bool) {
  unguarded_exhaustive? := u,
  asked? := completenessAsked u,
}

-- `checkTable` decides a precondition's question too, and
-- `checkPostcondition` with `expectVerdict`, as `checkExpect` does.
impl precondition: check::precondition for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

impl postcondition: check::postcondition for (q : Answer) {
  q := toOutcome q,
  verdict := toVerdict (expectVerdict q).1,
  reports_cex? := (expectVerdict q).2,
}

/-- The goals of the questions that an application asks of the
preconditions `ps`, as both front ends build them
(`Core.preconditionQuestions`), where its guard is `g`, over the
preconditions' values. -/
def questionsOf (ps : List Bool) (g : Bool) : List Bool :=
  ((Fren.Core.preconditionQuestions (fun x => !g || x) `f (ps.toArray.map (`p, ·))).map (·.2)).toList

/-- The facts that an application brings of the postconditions `qs`, as
both front ends build them (`Core.postconditionFacts`), over the clauses'
values. -/
def factsOf (ps qs : List Bool) : List Bool :=
  ((Fren.Core.postconditionFacts (fun ps q => !ps.all id || q) ps.toArray (qs.toArray.map (`q, ·))).map (·.2)).toList

-- For every application, over the values of its function's clauses.
impl application_contract: check::application_contract for (ps qs : List Bool) (g : Bool) (k : Int) {
  pres := Fren.Seq.ofList ps,
  posts := Fren.Seq.ofList qs,
  guarded? := g,
  k := k,
  asks? := decide (0 ≤ k ∧ k < (questionsOf ps g).length),
  question? := decide (0 ≤ k) && ((questionsOf ps g)[k.toNat]?.getD false),
  brings? := decide (0 ≤ k ∧ k < (factsOf ps qs).length),
  fact? := decide (0 ≤ k) && ((factsOf ps qs)[k.toNat]?.getD false),
} by
  intro ps qs g k _
  -- The `k`th value of `l` through `f`, as a sequence's index reads it.
  have key : ∀ (l : List Bool) (f : Bool → Bool),
      (0 ≤ k ∧ (Option.map f l[k.toNat]?).getD false = true) ↔
        ((0 ≤ k ∧ k < l.length) ∧ f ((Fren.Seq.ofList l).nth k) = true) := by
    intro l f
    by_cases h0 : 0 ≤ k
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      by_cases h1 : n < l.length
      · rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)]
        simp [h1]
      · have : l[n]? = none := List.getElem?_eq_none (by omega)
        simp [this]
        omega
    · simp [h0]
  have falseIn : (!ps.all fun a => a) = true ↔ false ∈ ps := by simp
  simp [fren_spec, questionsOf, factsOf, Fren.Core.preconditionQuestions, Fren.Core.postconditionFacts]
  refine ⟨(key ps _).trans ?_, (key qs _).trans ?_⟩
  · simp
  · simp [falseIn]

/-- A solver over two arguments and two values, numbered from 0, which
decides by trying each: a formula is a predicate on an argument and a
value. A model is never needed. -/
def finiteBackend : Fren.Core.Backend Id (Nat → Nat → Bool) Unit where
  query hyps goal _ :=
    if (List.range 2).all fun a => (List.range 2).all fun v => !(hyps.all (·.2 a v)) || goal a v then .unsat
    else .sat #[]
  falseF _ _ := false
  notF f a v := !f a v
  conj fs a v := fs.all (· a v)
  existsOutputs f := pure fun a _ => (List.range 2).any (f a)
  pin _ _ := pure none
  render _ _ := pure ""
  prime f := f
  samePrimed _ _ _ := true
  subst _ f := f

/-- The result of the realizability check of the contract whose
preconditions hold at the arguments that `pre` says, and postconditions at
those and the values that `post` says: on the component that both front
ends build (`Core.contractComp`), with `finiteBackend`. -/
def contractResult (pre : Nat → Bool) (post : Nat → Nat → Bool) : Fren.Core.CheckResult :=
  (Fren.Core.checkRealizable finiteBackend
    (Fren.Core.contractComp `m `f #[`x] `v #[(`p, fun a _ => pre a)] #[(`q, post)])).run

/-- Whether a result reports a conflict, and whether contradictory
assumptions (`Core.messages`). -/
def reportsConflict (r : Fren.Core.CheckResult) : Bool := r.detail matches .conflict ..
def reportsVacuous (r : Fren.Core.CheckResult) : Bool := r.detail matches .vacuousAssumptions ..

def argumentOf (a : Nat) : check.Argument := if a == 0 then .A0 else .A1
def valueOf (v : Nat) : check.Value := if v == 0 then .V0 else .V1

/-- The set of the arguments that `p0` and `p1` say. -/
def argumentsOf (p0 p1 : Bool) : Fren.FinSet check.Argument :=
  Fren.FinSet.ofList ((if p0 then [check.Argument.A0] else []) ++ (if p1 then [.A1] else []))

/-- What holds at the argument `a`, from what holds at each. -/
def pre (p0 p1 : Bool) (a : Nat) : Bool := if a == 0 then p0 else p1

/-- What holds at the argument `a` and the value `v`, from what holds at each. -/
def post (q00 q01 q10 q11 : Bool) (a v : Nat) : Bool :=
  if a == 0 then (if v == 0 then q00 else q01) else (if v == 0 then q10 else q11)

-- For every contract over two arguments and two values.
impl contract_realizability: check::contract_realizability for (p0 p1 q00 q01 q10 q11 : Bool) {
  pres := argumentsOf p0 p1,
  posts := Fren.FinSet.ofList ((if q00 then [{ arg := .A0, value := .V0 : check.Point }] else [])
    ++ (if q01 then [{ arg := .A0, value := .V1 }] else []) ++ (if q10 then [{ arg := .A1, value := .V0 }] else [])
    ++ (if q11 then [{ arg := .A1, value := .V1 }] else [])),
  verdict := toVerdict (contractResult (pre p0 p1) (post q00 q01 q10 q11)).verdict,
  reports_cex? := reportsConflict (contractResult (pre p0 p1) (post q00 q01 q10 q11)),
  reports_vacuous? := reportsVacuous (contractResult (pre p0 p1) (post q00 q01 q10 q11)),
}

/-- The component of the body of a defined function whose preconditions
hold at the arguments that `pre` says, and its postcondition at those that
`post` says, as both front ends build it, with `site`, a question about
an application in it. -/
def bodyComp (pre post : Nat → Bool) (sites : Array (Fren.Core.TableSite (Nat → Nat → Bool)) := #[]) :
    Fren.Core.Comp (Nat → Nat → Bool) :=
  { path := `m, vars := #[{ name := `x, role := .input, isPub := true }], assumes := #[(`f.p, fun a _ => pre a)]
    reqs := #[], expects := #[], triggers := #[], posts := #[(`f.q, fun a _ => post a)], fn? := some `f, tables := sites }

/-- The result of the precondition check at an application that is
evaluated at the arguments `guard` says, of a function whose precondition
holds at those that `pre` says: the question that both front ends build
(`Core.preconditionQuestions`), asked by the real check. -/
def preconditionResult (pre guard : Nat → Bool) : Fren.Core.CheckResult :=
  let guarded (f : Nat → Nat → Bool) (a v : Nat) : Bool := !guard a || f a v
  let (g, goal) := (Fren.Core.preconditionQuestions guarded `f #[(`p, fun (a _ : Nat) => pre a)])[0]!
  let site : Fren.Core.TableSite (Nat → Nat → Bool) := { site := { prop := `r, k := 0, place := .prop, goal }, goal := g }
  (Fren.Core.checkTable finiteBackend (bodyComp (fun _ => true) (fun _ => true)) site).run

/-- The result of the postcondition check of a defined function whose
preconditions hold at the arguments `pre` says, and postcondition at those
`post` says, by the real check. -/
def postconditionResult (pre post : Nat → Bool) : Fren.Core.CheckResult :=
  (Fren.Core.checkPostcondition finiteBackend (bodyComp pre post) (`f.q, fun a _ => post a)).run

-- For every precondition and guard over two arguments.
impl precondition_at: check::precondition_at for (p0 p1 g0 g1 : Bool) {
  pres := argumentsOf p0 p1,
  guarded := argumentsOf g0 g1,
  verdict := toVerdict (preconditionResult (pre p0 p1) (pre g0 g1)).verdict,
  reports_cex? := (preconditionResult (pre p0 p1) (pre g0 g1)).detail matches .counterexample ..,
}

-- For every precondition and postcondition over two arguments.
impl postcondition_at: check::postcondition_at for (p0 p1 q0 q1 : Bool) {
  pres := argumentsOf p0 p1,
  posts := argumentsOf q0 q1,
  verdict := toVerdict (postconditionResult (pre p0 p1) (pre q0 q1)).verdict,
  reports_cex? := (postconditionResult (pre p0 p1) (pre q0 q1)).detail matches .counterexample ..,
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
