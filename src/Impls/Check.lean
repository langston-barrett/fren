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

instance : Fren.Finite Fren.Core.CheckedItem := ⟨[.component, .global, .shortGlobal, .body, .contract], by intro x; cases x <;> simp⟩

def toCheckedItem : Fren.Core.CheckedItem → check.CheckedItem
  | .component => .Component
  | .global => .GlobalExpectation
  | .shortGlobal => .ShortExpectation
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

-- A subset type's obligation is a definedness site, which `checkDefinedness`
-- decides with `expectVerdict`.
impl subset_obligation: check::subset_obligation for (q : Answer) {
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
  pinVariant _ _ := pure none
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

/-! ## Forced outputs -/

instance : Fren.Finite check.Choice :=
  ⟨[.C0, .C1 false, .C1 true], by intro x; cases x with | C0 => simp | C1 b => cases b <;> simp⟩

/-- The three values of `check::Choice`. -/
def allChoices : List check.Choice := [.C0, .C1 false, .C1 true]

/-- A solver over one output with three values, which decides by trying
each: a formula is a predicate on the output's value, and a model is never
needed (`Core.forces` and `Core.forcesVariant` take the value as given). -/
def choiceBackend : Fren.Core.Backend Id (check.Choice → Bool) Unit where
  query hyps goal _ :=
    if allChoices.all fun v => !(hyps.all (·.2 v)) || goal v then .unsat else .sat #[]
  falseF _ := false
  notF f v := !f v
  conj fs v := fs.all (· v)
  existsOutputs f := pure fun _ => allChoices.any f
  pin _ _ := pure none
  pinVariant _ _ := pure none
  render _ _ := pure ""
  prime f := f
  samePrimed _ _ := true
  subst _ f := f

/-- The variant of `c`, as the backend's tester sees it. -/
def choiceVariant : check.Choice → Nat
  | .C0 => 0
  | .C1 _ => 1

/-- `choiceBackend`, pinning the output to the value `m`, and to its
variant, with the tester of `m`'s variant. -/
def pinning (m : check.Choice) : Fren.Core.Backend Id (check.Choice → Bool) Unit :=
  { choiceBackend with
    pin := fun _ _ => pure (some (· == m))
    pinVariant := fun _ _ => pure (some ({ name := "", arity := choiceVariant m }, (choiceVariant · == choiceVariant m))) }

/-- The values that `c0`, `c1` and `c2` say: `C0`, `C1(false)` and
`C1(true)`. -/
def valuesOf (c0 c1 c2 : Bool) (v : check.Choice) : Bool :=
  match v with
  | .C0 => c0
  | .C1 false => c1
  | .C1 true => c2

/-- The set of the values that `c0`, `c1` and `c2` say. -/
def choicesOf (c0 c1 c2 : Bool) : Fren.FinSet check.Choice :=
  Fren.FinSet.ofList ((if c0 then [check.Choice.C0] else []) ++ (if c1 then [.C1 false] else [])
    ++ (if c2 then [.C1 true] else []))

-- For every set of values of the output and every value in the model:
-- `Core.forces` and `Core.forcesVariant`, with the side's formula true at
-- exactly those values, ask the pin and variant queries and find what
-- forcing means.
impl forcing: check::forcing for (c0 c1 c2 : Bool) (m : check.Choice) {
  values := choicesOf c0 c1 c2,
  model := m,
  pin_q := toOutcome ((pinning m).query #[(`s, valuesOf c0 c1 c2)] (· == m) false).answer,
  variant_q := toOutcome ((pinning m).query #[(`s, valuesOf c0 c1 c2)] (choiceVariant · == choiceVariant m) false).answer,
  forced? := decide ([c0, c1, c2].count true ≤ 1),
  found? := (Fren.Core.forces (pinning m) #[(`s, valuesOf c0 c1 c2)] `o ()).run,
  variant_forced? := !(c0 && (c1 || c2)),
  variant_found? := (Fren.Core.forcesVariant (pinning m) #[(`s, valuesOf c0 c1 c2)] `o ()).run,
} by
  intro c0 c1 c2 m
  rcases m with _ | ⟨_ | _⟩ <;> cases c0 <;> cases c1 <;> cases c2 <;>
    simp +decide [fren_spec, pinning, choiceBackend, allChoices, choiceVariant, Fren.Core.forces, Fren.Core.forcesVariant,
      toOutcome, Fren.Core.Outcome.answer, Fren.Core.Outcome.isUnsat]

/-! ## The position of the first of a value in a sequence -/

theorem find?_range_getElem? [DecidableEq α] (l : List α) (x : α) :
    (List.range (l.length + 1)).find? (fun k => l[k]? == some x) = l.findIdx? (· == x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, List.findIdx?_cons]
    by_cases h : a = x
    · simp [h]
    · have hx : (a == x) = false := by simp [h]
      simp [hx, List.find?_map, Function.comp_def, ih]

theorem isPrefixOf_single [DecidableEq α] (l : List α) (x : α) (k : Nat) :
    [x].isPrefixOf (l.drop k) = (l[k]? == some x) := by
  have hd := List.head?_drop (l := l) (i := k)
  cases h : l.drop k with
  | nil => rw [h] at hd; simp at hd; simp [List.isPrefixOf, List.getElem?_eq_none hd]
  | cons b bs =>
    rw [h] at hd; simp at hd
    simp only [List.isPrefixOf, ← hd, Bool.and_true]
    by_cases hb : b = x
    · simp [hb]
    · have hb' : ¬x = b := fun e => hb e.symm
      rw [beq_eq_false_iff_ne.2 hb']
      simp [hb]

/-- `q.index_of([x], 0)`, the position of the first `x` in `q`, `-1` if none. -/
theorem indexOf_single [DecidableEq α] (l : List α) (x : α) :
    Fren.Seq.indexOf (Fren.Seq.ofList l) (Fren.Seq.unit x) 0 = ((l.findIdx? (· == x)).map Int.ofNat).getD (-1) := by
  unfold Fren.Seq.indexOf
  simp only [Fren.Seq.toList_ofList, Fren.Seq.toList_unit, Int.toNat_zero, Nat.zero_add]
  have hf : (fun k => [x].isPrefixOf (l.drop k)) = (fun k => l[k]? == some x) := funext (isPrefixOf_single l x)
  simp only [show (0 : Int) ≤ 0 by omega, Int.natCast_nonneg, and_self, if_true, Nat.sub_zero, hf, find?_range_getElem?]
  cases l.findIdx? (· == x) <;> simp

/-! ## The goals of the questions about guarded arms -/

/-- What a case does where the goal builder sees it (`Fren.Core.splitGoals`):
`none` for one taken wherever it is tried, and otherwise whether it is
taken. A `match`'s arm is its pattern's test and its guard; a table's row
is its condition, and its `_` row `none`. -/
def armAtOf : Option Bool → check.ArmAt
  | some false => .NoMatch
  | _ => .Taken

theorem armAtOf_taken (t : Option Bool) : armAtOf t = .Taken ↔ t.getD true = true := by
  rcases t with _ | _ | _ <;> simp [armAtOf]

theorem foldr_and (l : List Bool) (x : Bool) : l.foldr (· && ·) x = (l.all id && x) := by
  induction l <;> simp_all [Bool.and_assoc]

/-- `allOf?` over `Bool`s is `all`, `true` of none. -/
theorem allOf?_and (xs : Array Bool) : (Fren.Core.allOf? (· && ·) xs).getD true = xs.all id := by
  rcases xs with ⟨l⟩
  rcases List.eq_nil_or_concat l with rfl | ⟨l, x, rfl⟩
  · simp [Fren.Core.allOf?]
  · have : ({ toList := l.concat x } : Array Bool) = (l ++ [x]).toArray := by simp
    rw [this, ← List.push_toArray]
    simp [Fren.Core.allOf?, foldr_and]
    rfl

/-- The position of the first case taken, `-1` if none. -/
def firstTaken (t : List (Option Bool)) : Int :=
  (((t.map (·.getD true)).findIdx? id).map Int.ofNat).getD (-1)

theorem reachGoal_bool (t : List (Option Bool)) (j : Nat) (hj : j < t.length) :
    Fren.Core.reachGoal (· && ·) (!·) true t.toArray j = true ↔ firstTaken t ≠ j := by
  -- `j` is the first case taken exactly when it is taken and none before it is.
  have key : firstTaken t = j ↔
      (t[j].getD true = true ∧ ∀ i (hi : i < j), (t[i]'(Nat.lt_trans hi hj)).getD true = false) := by
    simp only [firstTaken]
    constructor
    · intro h
      cases hf : List.findIdx? id (t.map (·.getD true)) with
      | none => rw [hf] at h; simp at h
      | some i =>
        rw [hf] at h
        simp only [Option.map_some, Option.getD_some, Int.ofNat_eq_natCast] at h
        have hij : i = j := by omega
        subst hij
        obtain ⟨_, hp, hb⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
        exact ⟨by simpa using hp, fun k hk => by simpa using hb k hk⟩
    · rintro ⟨hp, hb⟩
      have : List.findIdx? id (t.map (·.getD true)) = some j :=
        List.findIdx?_eq_some_iff_getElem.2 ⟨by simpa using hj, by simpa using hp, fun k hk => by simpa using hb k hk⟩
      rw [this]
      rfl
  have hfails : (List.map (fun t? => !t?.getD true) (t.extract 0 j)).all id = true ↔
      ∀ i (hi : i < j), (t[i]'(Nat.lt_trans hi hj)).getD true = false := by
    have hx : t.extract 0 j = t.take j := by simp [List.extract_eq_take_drop]
    rw [hx, List.all_eq_true]
    constructor
    · intro h i hi
      have hm : t[i]'(Nat.lt_trans hi hj) ∈ t.take j := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by simp; omega, by simp⟩
      simpa using h _ (List.mem_map.2 ⟨_, hm, rfl⟩)
    · intro h x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
      simp only [List.length_take] at hi
      have := h i (by omega)
      simp only [List.getElem_take] at this ⊢
      simp [this]
  have hB : (t[j].toArray.all id) = t[j].getD true := by
    cases t[j] with
    | none => simp
    | some b => cases b <;> simp
  have hval : Fren.Core.reachGoal (· && ·) (!·) true t.toArray j =
      !((List.map (fun t? => !t?.getD true) (t.extract 0 j)).all id && t[j].getD true) := by
    simp only [Fren.Core.reachGoal, allOf?_and, Array.all_append, List.extract_toArray, List.map_toArray,
      List.all_toArray, List.getElem?_toArray, List.getElem?_eq_getElem hj, Option.join_some, hB]
  rw [hval, ne_eq, key, ← hfails]
  cases (List.map (fun t? => !t?.getD true) (t.extract 0 j)).all id <;> cases t[j].getD true <;> simp

theorem completeGoal_bool (t : List (Option Bool)) :
    Fren.Core.completeGoal (fun cs => cs.any id) true t.toArray = true ↔ firstTaken t ≥ 0 := by
  simp only [Fren.Core.completeGoal, Fren.Core.someCase, firstTaken]
  cases h : List.findIdx? id (List.map (fun x => x.getD true) t) with
  | none =>
    rw [List.findIdx?_eq_none_iff] at h
    simp
    intro x hx
    simpa using h _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  | some i =>
    obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    simp only [List.getElem_map, id_eq] at hp
    simp only [List.length_map] at hlt
    simp only [List.map_toArray, List.any_toArray, List.any_map, List.any_eq_true, Option.map_some, Option.getD_some,
      Int.ofNat_eq_natCast]
    exact ⟨fun _ => by omega, fun _ => ⟨t[i], List.getElem_mem _, by simpa using hp⟩⟩

impl split_questions: check::split_questions for (t : List (Option Bool)) (j k : Int) {
  arms := Fren.Seq.ofList (t.map armAtOf),
  j := j,
  k := k,
  first := firstTaken t,
  reach_goal? := Fren.Core.reachGoal (· && ·) (!·) true t.toArray j.toNat,
  complete_goal? := Fren.Core.completeGoal (fun cs => cs.any id) true t.toArray,
} by
  intro t j k hA
  simp [check.split_questions.assumes] at hA
  obtain ⟨hj0, hj1⟩ := hA
  simp only [fren_spec]
  have hj1' : j < t.length := by simpa [Fren.Seq.len_eq] using hj1
  have hjn : j.toNat < t.length := by omega
  refine ⟨?_, ?_, completeGoal_bool t⟩
  · rw [indexOf_single, firstTaken, List.findIdx?_map, List.findIdx?_map]
    congr 3
    funext a
    rcases a with _ | _ | _ <;> rfl
  · rw [reachGoal_bool t j.toNat hjn]
    constructor <;> intro h hc <;> apply h <;> omega

/-- Whether an arm has a guard (`check::GuardOf`). -/
def guardOf (g : Bool) : check.GuardOf := if g then .Guarded else .Unguarded

/-- Some case at or before `j` is `true`, as `armAsked` reads it. -/
theorem armAsked_iff (gs : List Bool) (j : Nat) :
    Fren.Core.armAsked gs.toArray j = true ↔ ∃ k, ∃ h : k < gs.length, k ≤ j ∧ gs[k] = true := by
  simp only [Fren.Core.armAsked, Fren.Core.reachabilityAsked, List.getElem?_toArray, List.extract_toArray,
    List.any_toArray, Bool.or_eq_true]
  have hx : gs.extract 0 j = gs.take j := by simp [List.extract_eq_take_drop]
  rw [hx, List.any_eq_true]
  constructor
  · rintro (h | ⟨x, hx, hx'⟩)
    · cases hg : gs[j]? with
      | none => simp [hg] at h
      | some b =>
        rw [hg] at h
        obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hg
        exact ⟨j, hlt, Nat.le_refl _, by simpa [he] using h⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
      simp only [List.length_take] at hk
      exact ⟨k, by omega, by omega, by simpa using hx'⟩
  · rintro ⟨k, hk, hkj, hg⟩
    by_cases hkj' : k = j
    · subst hkj'
      left
      simp [List.getElem?_eq_getElem hk, hg]
    · right
      refine ⟨gs[k], List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩, by simpa using hg⟩

/-- The first `true` is at or before `j` exactly when some `true` is. -/
theorem findIdx?_le_iff (gs : List Bool) (j : Int) :
    (0 ≤ ((gs.findIdx? id).map Int.ofNat).getD (-1) ∧ ((gs.findIdx? id).map Int.ofNat).getD (-1) ≤ j) ↔
      (0 ≤ j ∧ ∃ k, ∃ h : k < gs.length, (k : Int) ≤ j ∧ gs[k] = true) := by
  cases hf : gs.findIdx? id with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    simp only [Option.map_none, Option.getD_none]
    constructor
    · intro h; omega
    · rintro ⟨_, k, hk, _, hg⟩
      exact absurd (hf _ (List.getElem_mem hk)) (by simp [hg])
  | some i =>
    obtain ⟨hlt, hp, hb⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    simp only [Option.map_some, Option.getD_some, Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨_, hij⟩
      exact ⟨by omega, i, hlt, hij, by simpa using hp⟩
    · rintro ⟨_, k, hk, hkj, hg⟩
      have hik : i ≤ k := by
        refine Nat.le_of_not_lt fun hki => ?_
        exact hb k hki (by simpa using hg)
      exact ⟨by omega, by omega⟩

-- `splitGoals` asks about the arms that `armAsked` says, the guards
-- read from the arms of a `match` in order (`check::arms_asked`).
impl arms_asked: check::arms_asked for (gs : List Bool) (j : Int) {
  guards := Fren.Seq.ofList (gs.map guardOf),
  j := j,
  asked? := decide (0 ≤ j) && Fren.Core.armAsked gs.toArray j.toNat,
} by
  intro gs j _
  simp only [fren_spec]
  have hm : List.findIdx? (· == check.GuardOf.Guarded) (gs.map guardOf) = gs.findIdx? id := by
    rw [List.findIdx?_map]
    congr 1
    funext g
    cases g <;> rfl
  rw [indexOf_single, hm, findIdx?_le_iff, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hj, ha⟩
    obtain ⟨k, hk, hkj, hg⟩ := (armAsked_iff gs j.toNat).1 ha
    exact ⟨hj, k, hk, by omega, hg⟩
  · rintro ⟨hj, k, hk, hkj, hg⟩
    exact ⟨hj, (armAsked_iff gs j.toNat).2 ⟨k, hk, by omega, hg⟩⟩

/-! ## Flat patterns, and the hypotheses of reachability -/

/-- The pattern of an arm of a flat `match` on an enumeration of three
variants, and whether it has a guard (`check::FlatArm`). -/
def flatOf : check.FlatArm → Fren.Core.Pat × Bool
  | .Wild => (.wild false, false)
  | .A => (.ctor 0 #[], false)
  | .B => (.ctor 1 #[], false)
  | .C => (.ctor 2 #[], false)
  | .GuardedWild => (.wild false, true)
  | .GuardedA => (.ctor 0 #[], true)
  | .GuardedB => (.ctor 1 #[], true)
  | .GuardedC => (.ctor 2 #[], true)

theorem any_flatArm (l : List check.FlatArm) (a : check.FlatArm) : l.any (· == a) = decide (a ∈ l) := by
  rw [Bool.eq_iff_iff]; simp [List.any_eq_true]

theorem flatUnguardedExhaustive_flat (arms : List check.FlatArm) :
    (Fren.Core.flatUnguardedExhaustive? (fun _ => 3) (.enum `E []) (arms.toArray.map flatOf)).getD true =
      (decide (.Wild ∈ arms) || (decide (.A ∈ arms) && decide (.B ∈ arms) && decide (.C ∈ arms))) := by
  have hflat : ((List.map flatOf arms).toArray.all fun a => a.fst.flatEnum) = true := by
    simp only [List.all_toArray, List.all_map, List.all_eq_true]
    intro x _
    cases x <;> simp [flatOf, Fren.Core.Pat.flatEnum]
  have h0 : ∀ x, (!(flatOf x).2 && (flatOf x).1.names 0) = (x == .A) := by intro x; cases x <;> rfl
  have h1 : ∀ x, (!(flatOf x).2 && (flatOf x).1.names 1) = (x == .B) := by intro x; cases x <;> rfl
  have h2 : ∀ x, (!(flatOf x).2 && (flatOf x).1.names 2) = (x == .C) := by intro x; cases x <;> rfl
  simp only [Fren.Core.flatUnguardedExhaustive?, List.map_toArray, hflat, Bool.not_true, Bool.false_eq_true,
    if_false, Option.getD_some, List.filter_toArray, List.any_toArray, List.any_map, List.any_filter,
    Function.comp_def]
  simp only [List.range, List.range.loop, List.all_cons, List.all_nil, Bool.and_true, h0, h1, h2, any_flatArm,
    Bool.and_assoc]
  congr 1
  rw [← any_flatArm]
  congr 1
  funext x
  cases x <;> rfl

-- `checkMatch` decides whether the arms without guards are exhaustive with
-- `flatUnguardedExhaustive?` where every pattern is flat, as here.
impl flat_completeness_asked: check::flat_completeness_asked for (arms : List check.FlatArm) {
  arms := Fren.Seq.ofList arms,
  asked? := Fren.Core.completenessAsked
    ((Fren.Core.flatUnguardedExhaustive? (fun _ => 3) (.enum `E []) (arms.toArray.map flatOf)).getD true),
} by
  intro arms _
  simp only [fren_spec, flatUnguardedExhaustive_flat, Fren.Core.completenessAsked, Fren.Seq.mem_iff,
    Fren.Seq.toList_ofList]
  by_cases hw : check.FlatArm.Wild ∈ arms <;> by_cases ha : check.FlatArm.A ∈ arms <;>
    by_cases hb : check.FlatArm.B ∈ arms <;> by_cases hc : check.FlatArm.C ∈ arms <;> simp [hw, ha, hb, hc]

/-- What a hypothesis of reachability's candidates is, from its name and
the item `p` that the case is in (`check::HypAt`): each of them, the
definitions and the hypotheses of the place, is one of definedness's. -/
def hypAtOf (p n : Lean.Name) : check.HypAt := if n == p then .Enclosing else .Definedness

/-- `Comp.reachHyps` keeps the candidates that `reachUses` keeps, the item
that the case is in being the one its site names. -/
theorem reachHyps_filter {m : Type → Type} [Monad m] {F V : Type} (c : Fren.Core.Comp F)
    (b : Fren.Core.Backend m F V) (site : Fren.Core.IndexSite F) :
    c.reachHyps b site =
      (c.defEqs .reachability ++ c.siteHyps b site).filter fun h => Fren.Core.reachUses true (h.1 == site.prop) :=
  rfl

impl reach_hypotheses: check::reach_hypotheses for (ns : List Lean.Name) (p : Lean.Name) (k : Int) {
  hyps := Fren.Seq.ofList (ns.map (hypAtOf p)),
  k := k,
  used? := decide (0 ≤ k ∧ k < ns.length) && Fren.Core.reachUses true ((ns[k.toNat]?.getD .anonymous) == p),
} by
  intro ns p k _
  simp only [fren_spec, Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map]
  by_cases hk : 0 ≤ k ∧ k < ns.length
  · obtain ⟨hk0, hk1⟩ := hk
    have hn : k.toNat < ns.length := by omega
    rw [Fren.Seq.nth_of_lt _ _ hk0 (by simpa using hk1)]
    simp only [List.getElem?_eq_getElem hn, Option.getD_some, Fren.Seq.toList_ofList, List.getElem_map, hypAtOf,
      Fren.Core.reachUses]
    by_cases he : ns[k.toNat] = p <;> simp [he, hk0, hk1]
  · simp [hk]

/-! ## The goal of the disjointness of two cases -/

/-- What a case does, from whether its pattern matches and whether its
guard holds (`check::ArmAt`). -/
def caseAt : Bool × Bool → check.ArmAt
  | (false, _) => .NoMatch
  | (true, false) => .GuardFails
  | (true, true) => .Taken

/-- Whether the indexes in a case's guard are in range (`check::Indexes`). -/
def indexesAt (d : Bool) : check.Indexes := if d then .Defined else .Undefined

/-- The goal that `disjointGoals` builds for cases `i` and `j`, over
`Bool`s: each case taken where its pattern matches and its guard holds,
with its guard's indexes in range where the third says. -/
def disjointGoalOf (cs : List (Bool × Bool × Bool)) (i j : Nat) : Bool :=
  ((Fren.Core.disjointGoals .tableMatch (· && ·) (!·) true (cs.map fun c => some (c.1 && c.2.1)).toArray
    (cs.map fun c => some c.2.2).toArray #[(i, j)])[0]?.map (·.2)).getD true

-- Both front ends and the evaluator build the goal of each pair with
-- `disjointGoals` (`check::disjoint_question`).
impl disjoint_question: check::disjoint_question for (cs : List (Bool × Bool × Bool)) (i j : Int) {
  arms := Fren.Seq.ofList (cs.map fun c => caseAt (c.1, c.2.1)),
  defined := Fren.Seq.ofList (cs.map fun c => indexesAt c.2.2),
  i := i,
  j := j,
  goal? := disjointGoalOf cs i.toNat j.toNat,
} by
  intro cs i j hA
  have hl : (Fren.Seq.ofList (cs.map fun c => indexesAt c.2.2)).len = (cs.length : Int) := by
    simp [Fren.Seq.len_eq]
  simp only [check.disjoint_question.assumes, check.disjoint_question.assume.pair] at hA
  have hl' : (Fren.Seq.ofList (cs.map fun c => caseAt (c.1, c.2.1))).len = (cs.length : Int) := by
    simp [Fren.Seq.len_eq]
  rw [hl, hl'] at hA
  simp only [fren_spec]
  have hi : i.toNat < cs.length := by omega
  have hj : j.toNat < cs.length := by omega
  rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega), Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega),
    Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega), Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
  simp only [disjointGoalOf, Fren.Core.disjointGoals, Fren.Core.pairGoal]
  simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  rcases cs[i.toNat] with ⟨_ | _, _ | _, _ | _⟩ <;> rcases cs[j.toNat] with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp [caseAt, indexesAt]

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
