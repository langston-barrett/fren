module

public import Std

public section

namespace FrenBase.Binding

/-- Slots are nearest first: index zero denotes the newest entry. Entries may
be types, values or other caller-owned slot data. Length alone gives no
correspondence between two contexts. -/
abbrev Context (α : Type u) := List α

/-- Raw indices have a separate scope contract; no index inhabits scope zero. -/
@[expose] def InScope (size index : Nat) : Prop := index < size

instance : Decidable (InScope size index) := inferInstanceAs (Decidable (index < size))

/-- Out-of-scope lookup returns none, including every lookup in an empty context. -/
@[expose] def lookup (ctx : Context α) (index : Nat) : Option α := ctx[index]?

/-- When entries are types, this is typed context membership. It compares the
actual entry, rather than inferring membership from the context length. -/
@[expose] def HasType (ctx : Context Ty) (index : Nat) (ty : Ty) : Prop :=
  lookup ctx index = some ty

instance [DecidableEq Ty] : Decidable (HasType ctx i (ty : Ty)) :=
  inferInstanceAs (Decidable (lookup ctx i = some ty))

@[simp] theorem lookup_empty (i : Nat) : lookup ([] : Context α) i = none := by
  simp [lookup]

@[simp] theorem lookup_fresh (ctx : Context α) (entry : α) :
    lookup (entry :: ctx) 0 = some entry := rfl

@[simp] theorem lookup_older (ctx : Context α) (entry : α) (i : Nat) :
    lookup (entry :: ctx) (i + 1) = lookup ctx i := rfl

theorem lookup_none_iff (ctx : Context α) (i : Nat) :
    lookup ctx i = none ↔ ¬ InScope ctx.length i := by
  simp [lookup, InScope]

theorem hasType_scoped (h : HasType ctx i ty) : InScope ctx.length i := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  exact hi

theorem exists_hasType_iff (ctx : Context Ty) (i : Nat) :
    (∃ ty, HasType ctx i ty) ↔ InScope ctx.length i := by
  constructor
  · rintro ⟨ty, h⟩
    exact hasType_scoped h
  · intro hi
    exact ⟨ctx[i], List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩⟩

/-- Insert `amount` slots at `cutoff`. The arithmetic is total even for a
dangling index or a cutoff past the context. A context insertion requires
`cutoff ≤ size`; this operation supplies no context-removal operation. -/
@[expose] def shiftIndex (amount cutoff index : Nat) : Nat :=
  if index < cutoff then index else index + amount

@[simp] theorem shiftIndex_below (h : i < c) : shiftIndex a c i = i := by
  simp [shiftIndex, h]

theorem shiftIndex_above (h : c ≤ i) : shiftIndex a c i = i + a := by
  simp [shiftIndex, Nat.not_lt.mpr h]

@[simp] theorem shiftIndex_zero (c i : Nat) : shiftIndex 0 c i = i := by
  simp [shiftIndex]

@[simp] theorem shiftIndex_at (a c : Nat) : shiftIndex a c c = c + a := by
  simp [shiftIndex]

theorem shiftIndex_scoped (hi : InScope n i) : InScope (n + a) (shiftIndex a c i) := by
  unfold InScope at *
  unfold shiftIndex
  split <;> omega

/-- Two insertions at the same cutoff accumulate, even on raw dangling indices. -/
theorem shiftIndex_comp (a b c i : Nat) :
    shiftIndex b c (shiftIndex a c i) = shiftIndex (a + b) c i := by
  unfold shiftIndex
  by_cases h : i < c
  · simp [h]
  · simp only [if_neg h, if_neg (show ¬ i + a < c by omega)]
    omega

theorem shiftIndex_injective (a c : Nat) : Function.Injective (shiftIndex a c) := by
  intro i j h
  unfold shiftIndex at h
  split at h <;> split at h <;> omega

/-- Environments are total on raw indices. Only the first `n` images carry
scope guarantees; a caller must not assume anything about later images. -/
@[expose] def MapsInto (n m : Nat) (ρ : Nat → Nat) : Prop := ∀ i, InScope n i → InScope m (ρ i)

/-- Cross one binder, protecting its fresh slot and moving older images out. -/
@[expose] def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

@[simp] theorem liftRen_fresh (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_older (ρ : Nat → Nat) (i : Nat) :
    liftRen ρ (i + 1) = ρ i + 1 := rfl

theorem liftRen_id : liftRen id = id := by
  funext i
  cases i <;> rfl

theorem liftRen_comp (η ρ : Nat → Nat) :
    liftRen (η ∘ ρ) = liftRen η ∘ liftRen ρ := by
  funext i
  cases i <;> rfl

theorem liftRen_scoped (h : MapsInto n m ρ) : MapsInto (n + 1) (m + 1) (liftRen ρ) := by
  intro i hi
  cases i with
  | zero => exact Nat.zero_lt_succ _
  | succ i => exact Nat.succ_lt_succ (h i (by exact Nat.lt_of_succ_lt_succ hi))

/-- Cross `count` nested binders. Siblings use the same original environment. -/
@[expose] def liftRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | k + 1, ρ => liftRen (liftRenN k ρ)

theorem liftRenN_id (k : Nat) : liftRenN k id = id := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change liftRen (liftRenN k id) = id
    rw [ih, liftRen_id]

theorem liftRenN_comp (k : Nat) (η ρ : Nat → Nat) :
    liftRenN k (η ∘ ρ) = liftRenN k η ∘ liftRenN k ρ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change liftRen (liftRenN k (η ∘ ρ)) = _
    rw [ih, liftRen_comp]
    rfl

theorem liftRenN_fresh (h : i < k) : liftRenN k ρ i = i := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change liftRenN k ρ i + 1 = i + 1
      rw [ih (by omega)]

theorem liftRenN_older (k i : Nat) (ρ : Nat → Nat) :
    liftRenN k ρ (i + k) = ρ i + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.add_succ, liftRenN, liftRen_older, ih]

theorem liftRenN_scoped (h : MapsInto n m ρ) : MapsInto (n + k) (m + k) (liftRenN k ρ) := by
  induction k with
  | zero => exact h
  | succ k ih => exact liftRen_scoped ih

/-- The cutoff grows by the number of binders crossed. -/
theorem liftRenN_shift (k a c i : Nat) :
    liftRenN k (shiftIndex a c) i = shiftIndex a (c + k) i := by
  by_cases h : i < k
  · rw [liftRenN_fresh h, shiftIndex_below (by omega)]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    rw [Nat.add_comm k j, liftRenN_older]
    unfold shiftIndex
    split <;> split <;> omega

/-- Extend a substitution environment under one binder, independently of any
term datatype. `var` constructs a variable; `weaken` must shift a value into
the destination context extended by a newest slot. Its semantic obligations
belong to the caller (scope preservation alone does not rule out capture). -/
@[expose] def liftSub (var : Nat → α) (weaken : α → α) (σ : Nat → α) : Nat → α
  | 0 => var 0
  | i + 1 => weaken (σ i)

@[simp] theorem liftSub_fresh (var : Nat → α) (weaken : α → α) (σ : Nat → α) :
    liftSub var weaken σ 0 = var 0 := rfl

@[simp] theorem liftSub_older (var : Nat → α) (weaken : α → α) (σ : Nat → α) (i : Nat) :
    liftSub var weaken σ (i + 1) = weaken (σ i) := rfl

theorem liftSub_var (h : ∀ i, weaken (var i) = var (i + 1)) (i : Nat) :
    liftSub var weaken var i = var i := by
  cases i with
  | zero => rfl
  | succ i => exact h i

/-- A precise conditional scope contract for a caller's actual value type and
shift action. No typing, traversal or substitution law is assumed or proved. -/
theorem liftSub_scoped (Scoped : Nat → α → Prop)
    (hv : Scoped (m + 1) (var 0))
    (hw : ∀ x, Scoped m x → Scoped (m + 1) (weaken x))
    (hσ : ∀ i, InScope n i → Scoped m (σ i)) :
    ∀ i, InScope (n + 1) i → Scoped (m + 1) (liftSub var weaken σ i) := by
  intro i hi
  cases i with
  | zero => exact hv
  | succ i => exact hw _ (hσ i (Nat.lt_of_succ_lt_succ hi))

end FrenBase.Binding
