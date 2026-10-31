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

trusted model::report: "the front ends decide by `contradiction?`, which implements `model::decision`, `report`'s rule by inspection, from the outcomes of their own evaluators: the `fren eval` evaluator, whose agreement with `lang::eval` is tested by `src/FrenTest/Semantics.lean`, over the forms that it generates, and the compiled generated Lean definitions, whose agreement is trusted, as `Reqs/Models#how-the-front-ends-evaluate` states"

trusted model::reported_real: "the readable statement of `Reqs/Models`, which `model::report` refines, as `model::report_real` checks"

end Fren.Impls
