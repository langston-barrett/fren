-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

-- The shared policies used when constructing recursive queries and reporting
-- their results; these bind the structured requirements to the real helpers.
impl recursive_facts: lang::recursive_facts for (depth unfoldings : Nat) (bound constrained : Bool) {
  depth := depth,
  unfoldings := unfoldings,
  bound? := bound,
  constrained_result? := constrained,
  facts := { result_type? := Fren.Core.recursiveResultFact constrained && (Fren.Core.recursiveFacts depth bound unfoldings).1,
             posts? := (Fren.Core.recursiveFacts depth bound unfoldings).1,
             equation? := (Fren.Core.recursiveFacts depth bound unfoldings).2 },
} by
  intro depth unfoldings bound constrained _
  cases bound <;> cases constrained <;> by_cases h : depth < unfoldings <;>
    simp [fren_spec, Fren.Core.recursiveFacts, Fren.Core.recursiveResultFact, h]

-- The shared depth comparison reads the previous depth itself, not a
-- precomputed decision about whether the application needs another visit.
impl recursive_depth: lang::recursive_depth for (previous : Option Nat) (depth : Nat) {
  previous := previous.map Int.ofNat,
  depth := depth,
  «improves?» := Fren.Core.recursiveDepthImproves previous depth,
} by
  intro previous depth _
  cases previous with
  | none => simp [fren_spec, Fren.Core.recursiveDepthImproves]
  | some earlier =>
    simp [fren_spec, Fren.Core.recursiveDepthImproves]

impl recursive_post_result: lang::recursive_post_result for (r : lang.RecPost) (failed : Bool) {
  result := r,
  another_unproved? := failed,
  reported := if r = .Passed ∧ !Fren.Core.recursivePostResult true failed then .Inconclusive else r,
} by
  intro r failed _
  cases r <;> cases failed <;> simp [fren_spec, Fren.Core.recursivePostResult]

impl recursive_counterexample: lang::recursive_counterexample for (recursive confirms facts : Bool) {
  applies_recursive? := recursive,
  evaluation_confirms? := confirms,
  facts_recursive? := facts,
  report_counterexample? := Fren.Core.recursiveCounterexample recursive confirms facts,
} by
  intro recursive confirms facts _
  cases recursive <;> cases confirms <;> cases facts <;> simp [fren_spec, Fren.Core.recursiveCounterexample]

/-- What evaluation gives a formula (`lang::Evaluated`). -/
def evaluatedOf : Option Bool → lang.Evaluated
  | some true => .Holds
  | some false => .Fails
  | none => .Unevaluated

/-- A formula of a query as the solver has it (`lang::ModelFormula`). -/
def modelFormulaOf (f : Bool × Option Bool) : lang.ModelFormula :=
  { recursive? := f.1, value := evaluatedOf f.2 }

/-- The value that evaluation gives a formula, of what it gives
(`evaluatedOf`'s inverse). -/
def ofEvaluated : lang.Evaluated → Option Bool
  | .Holds => some true
  | .Fails => some false
  | .Unevaluated => none

theorem evaluatedOf_eq (o : Option Bool) (v : lang.Evaluated) : evaluatedOf o = v ↔ o = ofEvaluated v := by
  rcases o with _ | _ | _ <;> cases v <;> simp [evaluatedOf, ofEvaluated]

theorem modelFormulas_exists_nth (l : List lang.ModelFormula) (P : lang.ModelFormula → Prop) :
    (∃ k : Int, (0 ≤ k ∧ k < (Fren.Seq.ofList l).len) ∧ P ((Fren.Seq.ofList l).nth k)) ↔ ∃ x ∈ l, P x := by
  constructor
  · rintro ⟨k, ⟨h0, h1⟩, hp⟩
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList] at h1
    rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)] at hp
    exact ⟨_, List.getElem_mem _, hp⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨i, ⟨by omega, by simp [hi]⟩, ?_⟩
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hi)]
    simpa using hp

theorem modelFormulas_forall_nth (l : List lang.ModelFormula) (P : lang.ModelFormula → Prop) :
    (∀ k : Int, 0 ≤ k ∧ k < (Fren.Seq.ofList l).len → P ((Fren.Seq.ofList l).nth k)) ↔ ∀ x ∈ l, P x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i ⟨by omega, by simp [hi]⟩
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hi)] at this
    simpa using this
  · rintro h k ⟨h0, h1⟩
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList] at h1
    rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)]
    exact h _ (List.getElem_mem _)

-- Both front ends decide whether a check reports the solver's model with
-- `counterexampleReported`, over any formulas of the query.
impl counterexample_confirmed: lang::counterexample_confirmed
    for (hs : List (Bool × Option Bool)) (g : Bool × Option Bool) (facts : Bool) {
  hyps := Fren.Seq.ofList (hs.map modelFormulaOf),
  goal := modelFormulaOf g,
  facts_recursive? := facts,
  report_counterexample? := Fren.Core.counterexampleReported hs.toArray g facts,
} by
  intro hs g facts _
  obtain ⟨gr, gv⟩ := g
  have e1 := modelFormulas_exists_nth (hs.map modelFormulaOf) (fun x => x.recursive? = true)
  have e2 := modelFormulas_forall_nth (hs.map modelFormulaOf) (fun x => x.value = lang.Evaluated.Holds)
  have r1 : (∃ x, x ∈ hs.map modelFormulaOf ∧ x.recursive? = true) ↔ ∃ a ∈ hs, a.1 = true := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
      exact ⟨a, ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨_, ⟨a, ha, rfl⟩, h⟩
  have r2 : (∀ x, x ∈ hs.map modelFormulaOf → x.value = lang.Evaluated.Holds) ↔ ∀ a ∈ hs, a.2 = some true := by
    simp only [List.mem_map]
    constructor
    · intro h a ha
      exact (evaluatedOf_eq _ _).mp (h _ ⟨a, ha, rfl⟩)
    · rintro h _ ⟨a, ha, rfl⟩
      exact (evaluatedOf_eq _ _).mpr (h a ha)
  simp only [fren_spec, e1, e2, r1, r2]
  cases facts <;> cases gr <;> rcases gv with _ | _ | _ <;>
    simp [Fren.Core.counterexampleReported, Fren.Core.recursiveCounterexample, modelFormulaOf, evaluatedOf_eq,
      ofEvaluated, List.all_eq_true]

/-- The facts of the applications `brought`, of the pairs `rel` of each
application and a formula of its facts, in order. -/
def factsOfApps (rel : List (Nat × Nat)) (brought : List Nat) : List Nat :=
  brought.flatMap fun a => (rel.filter (·.1 == a)).map (·.2)

theorem mem_image_factsOfApps (rel : List (Nat × Nat)) (brought : List Nat) (x : Int) :
    x ∈ Fren.FinSet.image (Fren.FinSet.ofList (rel.map fun (p : Nat × Nat) => ((p.1 : Int), (p.2 : Int))))
      (Fren.FinSet.ofList (brought.map fun (a : Nat) => (a : Int))) ↔
    ∃ b ∈ factsOfApps rel brought, (b : Int) = x := by
  simp only [Fren.FinSet.mem_image, Fren.FinSet.mem_ofList, List.mem_map, factsOfApps, List.mem_flatMap,
    List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, q, hq, he⟩
    simp only [Prod.mk.injEq] at he
    exact ⟨q.2, ⟨a, ha, q, ⟨hq, Int.ofNat_inj.mp he.1⟩, rfl⟩, he.2⟩
  · rintro ⟨b, ⟨a, ha, q, ⟨hq, hqa⟩, rfl⟩, rfl⟩
    exact ⟨a, ⟨a, ha, rfl⟩, q, hq, by rw [hqa]⟩

/-- The positions of `fs`, formulas named by nothing, as `Int`s. -/
def positions (fs : Array (Lean.Name × Nat)) : Fren.FinSet Int :=
  Fren.FinSet.ofList (fs.toList.map fun (p : Lean.Name × Nat) => (p.2 : Int))

/-- `ns` as formulas named by nothing. -/
def unnamed (ns : List Nat) : Array (Lean.Name × Nat) := ns.toArray.map ((Lean.Name.anonymous, ·))

theorem mem_positions_unnamed (ns : List Nat) (x : Int) :
    x ∈ Fren.FinSet.ofList ((unnamed ns).toList.map fun (p : Lean.Name × Nat) => (p.2 : Int)) ↔
      ∃ b ∈ ns, (b : Int) = x := by
  simp [unnamed]

-- Both front ends' query builders reflect the facts of their variables and
-- of the applications that a query has, and then its hypotheses
-- (`recursionFormulas`), over any variables' facts, hypotheses, facts of
-- any applications, and applications that it has.
impl recursion_formulas: lang::recursion_formulas for (vars hyps : List Nat) (rel : List (Nat × Nat))
    (brought : List Nat) {
  variables := Fren.FinSet.ofList (vars.map fun (a : Nat) => (a : Int)),
  written := Fren.FinSet.ofList (hyps.map fun (a : Nat) => (a : Int)),
  facts := Fren.FinSet.ofList (rel.map fun (p : Nat × Nat) => ((p.1 : Int), (p.2 : Int))),
  brought := Fren.FinSet.ofList (brought.map fun (a : Nat) => (a : Int)),
  reflected := positions (Fren.Core.recursionFormulas (unnamed vars) (unnamed (factsOfApps rel brought))
    (unnamed hyps)),
} by
  intro vars hyps rel brought _
  refine ⟨?_, trivial⟩
  apply Fren.FinSet.ext
  intro x
  simp only [positions, Fren.Core.recursionFormulas, Array.toList_append,
    List.map_append, List.mem_append, Fren.FinSet.mem_ofList, Fren.FinSet.mem_union, mem_image_factsOfApps]
  simp [unnamed, or_assoc]

end Fren.Impls
