import Fren.FinSet
import Lean.Elab.Tactic.Omega

/-!
# Complete activation of a finite candidate set

Each productive round removes every enabled candidate from the pending list.
The measure counts candidates, independently of the number of signature items.
-/

namespace Fren.Core.FiniteActivation

open Fren (FinSet)

/-- Collect finite outputs without choosing a representative of the set. -/
def collect (f : A → List B) (s : FinSet A) : FinSet B :=
  Quotient.liftOn s (fun xs => FinSet.ofList (xs.flatMap f)) (by
    intro xs ys h
    apply FinSet.ext
    intro b
    simp only [FinSet.mem_ofList, List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hb⟩; exact ⟨a, (h a).mp ha, hb⟩
    · rintro ⟨a, ha, hb⟩; exact ⟨a, (h a).mpr ha, hb⟩)

@[simp] theorem mem_collect : b ∈ collect f s ↔ ∃ a ∈ s, b ∈ f a := by
  induction s using FinSet.ind with
  | h xs =>
    change b ∈ xs.flatMap f ↔ ∃ a ∈ xs, b ∈ f a
    simp only [List.mem_flatMap]

theorem collect_mono (h : s ⊆ t) : collect f s ⊆ collect f t := by
  intro b hb
  obtain ⟨a, ha, hb⟩ := mem_collect.mp hb
  exact mem_collect.mpr ⟨a, h a ha, hb⟩

structure Result (enabled : C → FinSet C → Bool) (pending : List C) (initial : FinSet C) where
  members : List C
  kept : initial ⊆ FinSet.ofList members
  bounded : FinSet.ofList members ⊆ initial ∪ FinSet.ofList pending
  closed : ∀ c ∈ pending, enabled c (FinSet.ofList members) = true → c ∈ FinSet.ofList members
  sound : (∀ c a b, a ⊆ b → enabled c a = true → enabled c b = true) →
    ∀ c ∈ FinSet.ofList members, c ∈ initial ∨ enabled c (FinSet.ofList members) = true
  least : ∀ target : FinSet C, initial ⊆ target →
    (∀ c a, a ⊆ target → enabled c a = true → enabled c target = true) →
    (∀ c ∈ pending, enabled c target = true → c ∈ target) → FinSet.ofList members ⊆ target

universe u

def Result.value {C : Type u} {enabled : C → FinSet C → Bool}
    {pending : List C} {initial : FinSet C} (r : Result enabled pending initial) : FinSet C :=
  FinSet.ofList r.members

/-- The result is the least closed extension whenever enabling is monotone.
No caller supplies a round limit, and there is no exhaustion result. -/
def run (enabled : C → FinSet C → Bool) (pending initial : List C) :
    Result enabled pending (FinSet.ofList initial) :=
  let known := FinSet.ofList initial
  if h : (pending.filter (enabled · known)).isEmpty then
    { members := initial
      kept := fun _ hc => hc
      bounded := fun _ hc => FinSet.mem_union.mpr (Or.inl hc)
      closed := by
        intro c hc he
        have hn := List.filter_eq_nil_iff.mp (List.isEmpty_iff.mp h) c hc
        change enabled c known = true at he
        simp [he] at hn
      sound := fun _ _ hc => Or.inl hc
      least := fun _ hi _ _ => hi }
  else
    let ready := pending.filter (enabled · known)
    let rest := pending.filter (fun c => !enabled c known)
    let next := initial ++ ready
    let result := run enabled rest next
    { members := result.members
      kept := by
        intro c hc
        apply result.kept c
        change c ∈ known ∪ FinSet.ofList ready
        exact FinSet.mem_union.mpr (Or.inl hc)
      bounded := by
        intro c hc
        rcases FinSet.mem_union.mp (result.bounded c hc) with hn | hr
        · change c ∈ known ∪ FinSet.ofList ready at hn
          rcases FinSet.mem_union.mp hn with hi | ha
          · exact FinSet.mem_union.mpr (Or.inl hi)
          · exact FinSet.mem_union.mpr (Or.inr (List.mem_filter.mp ha).1)
        · exact FinSet.mem_union.mpr (Or.inr (List.mem_filter.mp hr).1)
      closed := by
        intro c hc he
        by_cases ha : enabled c known = true
        · apply result.kept c
          change c ∈ known ∪ FinSet.ofList ready
          exact FinSet.mem_union.mpr (Or.inr (List.mem_filter.mpr ⟨hc, ha⟩))
        · exact result.closed c (List.mem_filter.mpr ⟨hc, by simpa using ha⟩) he
      sound := by
        intro hm c hc
        rcases result.sound hm c hc with hn | he
        · change c ∈ known ∪ FinSet.ofList ready at hn
          rcases FinSet.mem_union.mp hn with hi | hr
          · exact Or.inl hi
          · have he := (List.mem_filter.mp hr).2
            apply Or.inr
            apply hm c known (FinSet.ofList result.members) ?_ he
            intro c hc
            apply result.kept c
            change c ∈ known ∪ FinSet.ofList ready
            exact FinSet.mem_union.mpr (Or.inl hc)
        · exact Or.inr he
      least := by
        intro target hi hm hc
        apply result.least target
        · intro c hn
          change c ∈ known ∪ FinSet.ofList ready at hn
          rcases FinSet.mem_union.mp hn with hin | hr
          · exact hi c hin
          · have ⟨hp, he⟩ := List.mem_filter.mp hr
            exact hc c hp (hm c known hi he)
        · exact hm
        · intro c hr he
          exact hc c (List.mem_filter.mp hr).1 he }
termination_by pending.length
decreasing_by
  have le := List.length_filter_le (fun c => !enabled c (FinSet.ofList initial)) pending
  have ne : (pending.filter (fun c => !enabled c (FinSet.ofList initial))).length ≠ pending.length := by
    intro eq
    have all := List.length_filter_eq_length_iff.mp eq
    apply h
    apply List.isEmpty_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    simpa using all c hc
  omega

end Fren.Core.FiniteActivation
