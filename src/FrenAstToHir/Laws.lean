module

public import FrenAstToHir.Lookup
import all FrenBase.Identity

public section
namespace FrenAstToHir
open FrenBase

/-- The equality primitive is the actual collector's deciding function. -/
theorem same_scope (first second : String) : sameName first second = true ↔ first = second := by
  simp [sameName]

@[simp] theorem nearest_fresh (names : List String) (query : String) :
    nearest (query :: names) query = some 0 := by simp [nearest]

@[simp] theorem nearest_older (names : List String) (name query : String) (h : name ≠ query) :
    nearest (name :: names) query = (nearest names query).map (· + 1) := by simp [nearest, h]

theorem nearest_none (names : List String) (query : String) :
    nearest names query = none ↔ query ∉ names := by
  induction names with
  | nil => simp [nearest]
  | cons name rest ih =>
    by_cases h : name = query
    · subst name; simp [nearest]
    · simp [nearest, h, ih, Ne.symm h]

/-- Successful search selects the first matching entry in the actual binding
context, not just some in-bounds slot. This instantiates the checked chapter's
arbitrary-context NearestName obligation without importing the Fren1 checker. -/
theorem nearest_first (names : List String) (query : String) (i : Nat) :
    nearest names query = some i ↔
      Binding.lookup names i = some query ∧
        ∀ j, j < i → Binding.lookup names j ≠ some query := by
  induction names generalizing i with
  | nil => simp [nearest, Binding.lookup]
  | cons name rest ih =>
    cases i with
    | zero => simp [nearest, Binding.lookup, Option.map_eq_some_iff]
    | succ i =>
      by_cases h : name = query
      · subst name
        simp only [nearest, ↓reduceIte]
        constructor
        · intro impossible; simp at impossible
        · rintro ⟨_, first⟩
          exact False.elim (first 0 (by omega) rfl)
      · simp only [nearest, if_neg h, Option.map_eq_some_iff]
        constructor
        · rintro ⟨j, hj, heq⟩
          have eq : j = i := by omega
          subst j
          obtain ⟨hit, first⟩ := (ih i).mp hj
          refine ⟨hit, ?_⟩
          intro k hk
          cases k with
          | zero => simpa [Binding.lookup] using h
          | succ k => exact first k (by omega)
        · rintro ⟨hit, first⟩
          refine ⟨i, (ih i).mpr ⟨hit, ?_⟩, rfl⟩
          intro j hj
          exact first (j + 1) (by omega)

theorem nearest_scoped (names : List String) (query : String) (i : Nat)
    (h : nearest names query = some i) : Binding.InScope names.length i :=
  Binding.hasType_scoped ((nearest_first names query i).mp h).1

/-- The finite primitive contract uses integers as equality atoms. For string
spellings the actual decision specializes to the same two-slot truth table. -/
theorem nearest_two (near far query : String) :
    nearest [near, far] query =
      (if query = near then some 0 else if query = far then some 1 else none) := by
  by_cases a : near = query <;> by_cases b : far = query <;>
    simp [nearest, a, b, eq_comm]

theorem canonical_child (p q : ItemId) (a b : String) :
    p.named a = q.named b ↔ p = q ∧ a = b := by
  simp [ItemId.named, ItemId.child_eq_child]

end FrenAstToHir
