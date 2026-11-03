-- keep-sorted start
import FrenCore.Check
import Impls.Check
import Reqs.Models
-- keep-sorted end
open Fren.Lang

/-!
# Reading models (`Reqs/Models`)

`Fren.Core.contradiction?`, which both front ends use to decide what a
reported model contradicts, implements `model::decision`: for the truths of
any number of hypotheses and of the goal, the model is shown exactly when
nothing is contradicted, and the check is inconclusive otherwise, as
`Fren.Core.confirmReport` makes it. `model::report`, the same rule over
`lang::eval`, is trusted: that `decision` is its rule is by inspection, and
neither front end's evaluator is bound to `lang::eval`. The `fren`
command's evaluator is tested against it, over the forms that
`src/FrenTest/Semantics.lean` generates, and the Lean-hosted front end's
agreement with it is trusted (`Reqs/Models#how-the-front-ends-evaluate`).

`Fren.Core.appliedKnown` and `Fren.Core.iteKnown`, by which both front ends'
evaluators decide whether an application's and an `if`'s values are known
in a model's confirmation, implement `model::known_application` and
`model::known_if` (`Reqs/Models#known-values`). `Fren.Core.asksAgain` and
`Fren.Core.keepsSecond`, by which both front ends decide, in
`Fren.Core.askedAgain`, whether to ask a query whose model confirmation
contradicts again and whether to keep the second answer, implement
`model::requery` (`Reqs/Models#asking-again`). `Fren.Core.armTest`, by
which the `fren` command combines the tests of a `match` arm's patterns,
implements `model::arm_test_of`; the Lean-hosted front end writes the same
conjunction as `∧`, which `Enumerate.knownOf` reads by
`Fren.Core.Enumeration.andTruth`. Which patterns test anything both front
ends decide by `Fren.Core.Pat.irrefutable`, which implements
`model::irrefutable?` by inspection: no `impl` binds it, which would need a
translation of `lang::Pattern` into `Fren.Core.Pat`. The `fren` command's
use of it is tested against `model::known_eval`, over single scrutinees and
their or-patterns, by `src/FrenTest/Semantics.lean`, and the Lean-hosted
front end's against the `fren` command's by `fren_fuzz_frontends --confirm`. `model::application_known`,
`model::if_known`, `model::and_known`, `model::or_known` and
`model::count_known` relate the rules to `lang::eval`, and
`model::and_sound`, `model::or_sound` and `model::if_sound` state the
extensions' soundness at every completion; random testing checks them.
-/

namespace Fren.Impls

open Fren.Core (Verdict contradiction?)
open Fren.Generated

/-- A truth as the evaluator knows it, as an outcome of `lang::eval`. -/
def toLangOutcome : Option Bool → lang.Outcome
  | some true => .Defined .True
  | some false => .Defined .False
  | none => .Undefined

theorem contradiction?_isNone (hs : List (Option Bool)) (g : Option Bool) :
    (contradiction? (hs.toArray.map (Lean.Name.anonymous, ·)) g).isNone = true ↔
      (some false ∉ hs ∧ g ≠ some true) := by
  unfold contradiction?
  split
  · next h heq =>
    have := Array.find?_some heq
    have hm := Array.mem_of_find?_eq_some heq
    simp only [Array.mem_map, List.mem_toArray] at hm
    obtain ⟨x, hx, e⟩ := hm
    cases e
    simp at this
    subst this
    simp [hx]
  · next heq =>
    have hnone := Array.find?_eq_none.1 heq
    have : some false ∉ hs := fun hm => by
      have := hnone _ (Array.mem_map.2 ⟨some false, by simpa using hm, rfl⟩)
      simp at this
    by_cases hg : g = some true <;> simp [hg, this]

theorem toLangOutcome_false (x : Option Bool) : toLangOutcome x = .Defined .False ↔ x = some false := by
  rcases x with _ | _ | _ <;> simp [toLangOutcome]

theorem toLangOutcome_true (x : Option Bool) : toLangOutcome x = .Defined .True ↔ x = some true := by
  rcases x with _ | _ | _ <;> simp [toLangOutcome]

-- For any number of hypotheses, each `true`, `false` or unknown.
impl decision_of: model::decision for (hs : List (Option Bool)) (g : Option Bool) (v : Verdict) {
  hypotheses := Fren.Seq.ofList (hs.map toLangOutcome),
  goal := toLangOutcome g,
  solver := toVerdict v,
  shown? := (contradiction? (hs.toArray.map (Lean.Name.anonymous, ·)) g).isNone,
  internal? := (contradiction? (hs.toArray.map (Lean.Name.anonymous, ·)) g).isSome,
  verdict := toVerdict (if (contradiction? (hs.toArray.map (Lean.Name.anonymous, ·)) g).isSome then .inconclusive else v),
} by
  intro hs g v _
  have hmem : lang.Outcome.Defined .False ∈ Fren.Seq.ofList (hs.map toLangOutcome) ↔ some false ∈ hs := by
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => (toLangOutcome_false x).1 e ▸ hx, fun h => ⟨_, h, rfl⟩⟩
  have hn := contradiction?_isNone hs g
  cases hc : (contradiction? (hs.toArray.map (Lean.Name.anonymous, ·)) g) <;>
    simp_all [fren_spec, toLangOutcome_true, Option.isSome, Option.isNone, toVerdict]

-- For any number of arguments.
impl known_application_of: model::known_application for (args : List Bool) (b : Bool) {
  arguments := Fren.Seq.ofList args,
  «body_known?» := b,
  «known?» := Fren.Core.appliedKnown args b,
} by
  intro args b
  cases b <;> simp [fren_spec, Fren.Core.appliedKnown, Fren.Seq.mem_iff]

/-- A truth as the evaluator knows it, as `check::Truth`. -/
def toTruth : Option Bool → check.Truth
  | some true => .True
  | some false => .False
  | none => .Unknown

theorem toTruth_false (x : Option Bool) : toTruth x = .False ↔ x = some false := by
  rcases x with _ | _ | _ <;> simp [toTruth]

theorem toTruth_unknown (x : Option Bool) : toTruth x = .Unknown ↔ x = none := by
  rcases x with _ | _ | _ <;> simp [toTruth]

-- For any number of patterns that test their scrutinees.
impl arm_test_of_tests: model::arm_test_of for (tests : List (Option Bool)) {
  tests := Fren.Seq.ofList (tests.map toTruth),
  test := toTruth (Fren.Core.armTest tests),
} by
  intro tests
  have hf : check.Truth.False ∈ Fren.Seq.ofList (tests.map toTruth) ↔ some false ∈ tests := by
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => (toTruth_false x).1 e ▸ hx, fun h => ⟨_, h, rfl⟩⟩
  have hu : check.Truth.Unknown ∈ Fren.Seq.ofList (tests.map toTruth) ↔ none ∈ tests := by
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => (toTruth_unknown x).1 e ▸ hx, fun h => ⟨_, h, rfl⟩⟩
  unfold Fren.Core.armTest
  simp only [fren_spec]
  by_cases h1 : some false ∈ tests
  · rw [if_pos (hf.2 h1)]; simp [h1, toTruth]
  · rw [if_neg (mt hf.1 h1)]
    by_cases h2 : none ∈ tests
    · rw [if_pos (hu.2 h2)]; simp [h1, h2, toTruth]
    · rw [if_neg (mt hu.1 h2)]; simp [h1, h2, toTruth]

impl known_if_of: model::known_if for (c : Option Bool) (y n same : Bool) {
  condition := toTruth c,
  «then_known?» := y,
  «else_known?» := n,
  «same?» := same,
  «known?» := Fren.Core.iteKnown c y n same,
} by
  intro c y n same
  rcases c with _ | _ | _ <;> cases y <;> cases n <;> cases same <;>
    simp [fren_spec, toTruth, Fren.Core.iteKnown]

impl requery_of: model::requery for (contradicted canAsk againSat againContradicted : Bool) {
  «first_contradicted?» := contradicted,
  «can_ask?» := canAsk,
  «again_sat?» := againSat,
  «again_contradicted?» := againContradicted,
  «asks?» := Fren.Core.asksAgain contradicted canAsk,
  «second?» := Fren.Core.keepsSecond (Fren.Core.asksAgain contradicted canAsk) againSat againContradicted,
} by
  intro contradicted canAsk againSat againContradicted
  cases contradicted <;> cases canAsk <;> cases againSat <;> cases againContradicted <;>
    simp [fren_spec, Fren.Core.asksAgain, Fren.Core.keepsSecond]

trusted model::report: "the rule over `lang::eval`, which no front end implements as an equivalence: they implement `model::confirmed_report` instead (`Reqs/Models#reporting`), over `model::known_eval`, which knows more than `lang::eval`, and a model that it shows satisfies `report`'s readable statement, `reported_real`, as `model::confirmed_real` checks"

trusted model::confirmed_report: "both front ends decide by `contradiction?`, which implements `model::decision`, over the outcomes of their evaluators: the `fren` command's strict `Ex.eval`, which `src/FrenTest/Semantics.lean` tests against `model::known_eval` over the forms that it generates, and the Lean-hosted front end's compiled definitions read by `Enumerate.knownOf`, which `fren_fuzz_frontends --confirm` compares with the `fren` command with both misreading models, so that a model that one refutes and the other shows, both having read it alike, is a difference in what they know; the Lean-hosted front end knows less than `known_eval` of the formulas that `Reqs/Models#known-values` lists as not evaluated, and shows a model that only those decide on the solver's word"

trusted model::reported_real: "the readable statement of `Reqs/Models`, which `model::report` refines, as `model::report_real` checks"

end Fren.Impls
