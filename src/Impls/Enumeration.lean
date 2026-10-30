-- keep-sorted start
import FrenCore.Enumeration
import Impls.Check
import Reqs.Check
-- keep-sorted end
open Fren.Lang

/-!
# Checking by enumeration (`Reqs/Check#checking-by-enumeration`)

The enumerator of `FrenCore.Enumeration`, proved complete: each value of a
shape of size at most the bound is listed exactly once, with its size,
smallest first (`check::listed`, `check::smallest_first`), by the typing
rules of shapes, `SHas`, which follow `check::value_size`; and the
decisions of enumeration, `methodOf`, `enumeratedVerdict` and
`combinedVerdict`, as `check` requires.
-/

namespace Fren.Impls.Enumeration

open Fren.Core (CheckKind Verdict)
open Fren.Core.Enumeration

/-! ## Shapes' values -/

mutual
inductive SHas : Shape → EVal → Nat → Prop
  | bool (b : Bool) : SHas .bool (.bool b) 0
  | int (i : Int) : SHas .int (.int i) i.natAbs
  | nat (k : Nat) : SHas .nat (.int k) k
  | ints {vs : List Int} {i : Int} : i ∈ vs → SHas (.ints vs) (.int i) 0
  | abstract (k : Nat) : SHas .abstract (.abs k) k
  | ctors {cs v k} : CHas cs 0 v k → SHas (.ctors cs) v k
  | record {fs vs k} : SsHas fs vs k → SHas (.record fs) (.ctor 0 vs) k
  | filter {s keep v k} : SHas s v k → keep v = true → SHas (.filter s keep) v k
inductive SsHas : Shapes → List EVal → Nat → Prop
  | nil : SsHas .nil [] 0
  | cons {s ss v vs k l} : SHas s v k → SsHas ss vs l → SsHas (.cons s ss) (v :: vs) (max k l)
inductive CHas : Ctors → Nat → EVal → Nat → Prop
  | nullary {rest i} : CHas (.cons .nil rest) i (.ctor i []) 0
  | payload {p ps rest i vs k} : SsHas (.cons p ps) vs k → CHas (.cons (.cons p ps) rest) i (.ctor i vs) (k + 1)
  | there {ps rest i v k} : CHas rest (i + 1) v k → CHas (.cons ps rest) i v k
end

theorem mem_intsUpTo (n : Nat) (i : Int) : i ∈ intsUpTo n ↔ i.natAbs ≤ n := by
  simp only [intsUpTo, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hi⟩
    split at hi <;> simp at hi <;> omega
  · intro h
    refine ⟨i.natAbs, by omega, ?_⟩
    split <;> simp <;> omega

theorem mem_prodWith (xs : List (EVal × Nat)) (rest : List (List EVal × Nat)) (vs : List EVal) (m : Nat) :
    (vs, m) ∈ prodWith xs rest ↔ ∃ v k ws l, vs = v :: ws ∧ m = max k l ∧ (v, k) ∈ xs ∧ (ws, l) ∈ rest := by
  simp only [prodWith, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨v, k⟩, hx, ⟨ws, l⟩, hr, rfl, rfl⟩; exact ⟨v, k, ws, l, rfl, rfl, hx, hr⟩
  · rintro ⟨v, k, ws, l, rfl, rfl, hx, hr⟩; exact ⟨(v, k), hx, (ws, l), hr, rfl, rfl⟩

mutual
theorem mem_vals : (s : Shape) → (n : Nat) → (v : EVal) → (k : Nat) → ((v, k) ∈ s.vals n ↔ SHas s v k ∧ k ≤ n)
  | .bool, n, v, k => by
    simp [Shape.vals, valueSize]; constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨.bool _, by omega⟩
    · rintro ⟨h, -⟩; cases h with | bool b => cases b <;> simp
  | .int, n, v, k => by
    simp only [Shape.vals, valueSize, List.mem_map, Prod.mk.injEq, mem_intsUpTo]; constructor
    · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨.int i, hi⟩
    · rintro ⟨h, hk⟩; cases h with | int i => exact ⟨i, hk, rfl, rfl⟩
  | .nat, n, v, k => by
    simp only [Shape.vals, valueSize, List.mem_map, Prod.mk.injEq, List.mem_range]; constructor
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨by simpa using SHas.nat j, by simp; omega⟩
    · rintro ⟨h, hk⟩; cases h; exact ⟨_, by omega, rfl, by simp⟩
  | .ints vs, n, v, k => by
    simp only [Shape.vals, valueSize, List.mem_map, Prod.mk.injEq]; constructor
    · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨.ints hi, by omega⟩
    · rintro ⟨h, -⟩; cases h with | ints hi => exact ⟨_, hi, rfl, rfl⟩
  | .abstract, n, v, k => by
    simp only [Shape.vals, valueSize, List.mem_map, Prod.mk.injEq, List.mem_range]; constructor
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨by simpa using SHas.abstract j, by simp; omega⟩
    · rintro ⟨h, hk⟩; cases h; exact ⟨_, by omega, rfl, by simp⟩
  | .ctors cs, n, v, k => by
    simp only [Shape.vals]; rw [mem_cvals cs 0 n v k]; constructor
    · rintro ⟨h, hk⟩; exact ⟨.ctors h, hk⟩
    · rintro ⟨h, hk⟩; cases h with | ctors h => exact ⟨h, hk⟩
  | .record fs, n, v, k => by
    simp only [Shape.vals, valueSize, List.mem_map, Prod.mk.injEq]; constructor
    · rintro ⟨⟨vs, l⟩, h, rfl, rfl⟩; have := (mem_svals fs n vs l).1 h; exact ⟨.record this.1, this.2⟩
    · rintro ⟨h, hk⟩; cases h with | record h => exact ⟨(_, k), (mem_svals fs n _ k).2 ⟨h, hk⟩, rfl, rfl⟩
  | .filter s keep, n, v, k => by
    simp only [Shape.vals, List.mem_filter]; rw [mem_vals s n v k]; constructor
    · rintro ⟨⟨h, hk⟩, hkeep⟩; exact ⟨.filter h hkeep, hk⟩
    · rintro ⟨h, hk⟩; cases h with | filter h hkeep => exact ⟨⟨h, hk⟩, hkeep⟩
  | .empty, n, v, k => by
    simp [Shape.vals]; intro h; cases h

theorem mem_svals : (ss : Shapes) → (n : Nat) → (vs : List EVal) → (k : Nat) →
    ((vs, k) ∈ ss.vals n ↔ SsHas ss vs k ∧ k ≤ n)
  | .nil, n, vs, k => by
    simp [Shapes.vals]; constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨.nil, by omega⟩
    · rintro ⟨h, -⟩; cases h; simp
  | .cons s rest, n, vs, k => by
    simp only [Shapes.vals]; rw [mem_prodWith]; constructor
    · rintro ⟨v, k₁, ws, l, rfl, rfl, hx, hr⟩
      have h1 := (mem_vals s n v k₁).1 hx; have h2 := (mem_svals rest n ws l).1 hr
      exact ⟨.cons h1.1 h2.1, by omega⟩
    · rintro ⟨h, hk⟩
      cases h with
      | cons h1 h2 => exact ⟨_, _, _, _, rfl, rfl, (mem_vals s n _ _).2 ⟨h1, by omega⟩, (mem_svals rest n _ _).2 ⟨h2, by omega⟩⟩

theorem mem_cvals : (cs : Ctors) → (i n : Nat) → (v : EVal) → (k : Nat) →
    ((v, k) ∈ cs.vals i n ↔ CHas cs i v k ∧ k ≤ n)
  | .nil, i, n, v, k => by simp [Ctors.vals]; intro h; cases h
  | .cons .nil rest, i, n, v, k => by
    simp only [Ctors.vals, valueSize, List.mem_cons, Prod.mk.injEq]; rw [mem_cvals rest (i + 1) n v k]; constructor
    · rintro (⟨rfl, rfl⟩ | ⟨h, hk⟩)
      · exact ⟨.nullary, by omega⟩
      · exact ⟨.there h, hk⟩
    · rintro ⟨h, hk⟩
      cases h with
      | nullary => left; exact ⟨rfl, rfl⟩
      | there h => right; exact ⟨h, hk⟩
  | .cons (.cons p ps) rest, i, n, v, k => by
    simp only [Ctors.vals, List.mem_append]; rw [mem_cvals rest (i + 1) n v k]
    cases n with
    | zero =>
      simp only [List.not_mem_nil, false_or]; constructor
      · rintro ⟨h, hk⟩; exact ⟨.there h, hk⟩
      · rintro ⟨h, hk⟩
        cases h with
        | payload h => omega
        | there h => exact ⟨h, hk⟩
    | succ m =>
      simp only [valueSize, List.mem_map, Prod.mk.injEq]; constructor
      · rintro (⟨⟨vs, l⟩, h, rfl, rfl⟩ | ⟨h, hk⟩)
        · have := (mem_svals (.cons p ps) m vs l).1 h; exact ⟨.payload this.1, by omega⟩
        · exact ⟨.there h, hk⟩
      · rintro ⟨h, hk⟩
        cases h with
        | payload h => left; exact ⟨(_, _), (mem_svals (.cons p ps) m _ _).2 ⟨h, by omega⟩, rfl, rfl⟩
        | there h => right; exact ⟨h, hk⟩
end


theorem chas_index : {cs : Ctors} → {i : Nat} → {v : EVal} → {k : Nat} → CHas cs i v k → ∃ j vs, v = .ctor j vs ∧ i ≤ j
  | _, _, _, _, .nullary => ⟨_, _, rfl, Nat.le_refl _⟩
  | _, _, _, _, .payload _ => ⟨_, _, rfl, Nat.le_refl _⟩
  | _, _, _, _, .there h => let ⟨j, vs, e, hj⟩ := chas_index h; ⟨j, vs, e, by omega⟩

theorem cvals_index_gt {cs : Ctors} {i : Nat} {vs : List EVal} {k : Nat} (h : CHas cs (i + 1) (.ctor i vs) k) : False := by
  obtain ⟨j, ws, e, hj⟩ := chas_index h
  cases e; omega

mutual
theorem size_unique : {s : Shape} → {v : EVal} → {k k' : Nat} → SHas s v k → SHas s v k' → k = k'
  | _, _, _, _, .bool _, h => by cases h; rfl
  | _, _, _, _, .int _, h => by cases h; rfl
  | _, _, _, _, .nat _, h => by cases h; rfl
  | _, _, _, _, .ints _, h => by cases h; rfl
  | _, _, _, _, .abstract _, h => by cases h; rfl
  | _, _, _, _, .ctors h₁, h => by cases h with | ctors h₂ => exact csize_unique h₁ h₂
  | _, _, _, _, .record h₁, h => by cases h with | record h₂ => exact ssize_unique h₁ h₂
  | _, _, _, _, .filter h₁ _, h => by cases h with | filter h₂ _ => exact size_unique h₁ h₂
theorem ssize_unique : {ss : Shapes} → {vs : List EVal} → {k k' : Nat} → SsHas ss vs k → SsHas ss vs k' → k = k'
  | _, _, _, _, .nil, h => by cases h; rfl
  | _, _, _, _, .cons h₁ r₁, h => by
    cases h with | cons h₂ r₂ => rw [size_unique h₁ h₂, ssize_unique r₁ r₂]
theorem csize_unique : {cs : Ctors} → {i : Nat} → {v : EVal} → {k k' : Nat} → CHas cs i v k → CHas cs i v k' → k = k'
  | _, _, _, _, _, .nullary, h => by
    cases h with
    | nullary => rfl
    | there h => exact (cvals_index_gt h).elim
  | _, _, _, _, _, .payload h₁, h => by
    cases h with
    | payload h₂ => rw [ssize_unique h₁ h₂]
    | there h => exact (cvals_index_gt h).elim
  | _, _, _, _, _, .there h₁, h => by
    cases h with
    | nullary => exact (cvals_index_gt h₁).elim
    | payload _ => exact (cvals_index_gt h₁).elim
    | there h₂ => exact csize_unique h₁ h₂
end

mutual
def SDistinct : Shape → Prop
  | .ints vs => vs.Nodup
  | .ctors cs => CDistinct cs
  | .record fs => SsDistinct fs
  | .filter s _ => SDistinct s
  | _ => True
def SsDistinct : Shapes → Prop
  | .nil => True
  | .cons s r => SDistinct s ∧ SsDistinct r
def CDistinct : Ctors → Prop
  | .nil => True
  | .cons p r => SsDistinct p ∧ CDistinct r
end

theorem nodup_map_on {α β : Type} {f : α → β} {l : List α} (h : l.Nodup)
    (inj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 h)
  exact this.imp fun ⟨ha, hb, hne⟩ e => hne (inj _ ha _ hb e)

theorem nodup_filter {α : Type} {p : α → Bool} {l : List α} (h : l.Nodup) : (l.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_filter]
  exact (List.nodup_iff_pairwise_ne.1 h).imp fun hne _ _ => hne

theorem nodup_intsUpTo (n : Nat) : (intsUpTo n).Nodup := by
  rw [List.nodup_iff_pairwise_ne, intsUpTo, List.pairwise_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · split <;> simp <;> omega
  · have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 (@List.nodup_range (n + 1)))
    refine this.imp fun ⟨_, _, hne⟩ x hx y hy e => ?_
    subst e
    split at hx <;> split at hy <;> simp at hx hy <;> omega

theorem nodup_prodWith (xs : List (EVal × Nat)) (rest : List (List EVal × Nat)) (h₁ : xs.Nodup) (h₂ : rest.Nodup)
    (fx : ∀ v k k', (v, k) ∈ xs → (v, k') ∈ xs → k = k') (fr : ∀ vs l l', (vs, l) ∈ rest → (vs, l') ∈ rest → l = l') :
    (prodWith xs rest).Nodup := by
  rw [List.nodup_iff_pairwise_ne, prodWith, List.pairwise_flatMap]
  refine ⟨fun ⟨v, k⟩ _ => ?_, ?_⟩
  · rw [← List.nodup_iff_pairwise_ne]
    refine nodup_map_on h₂ fun ⟨ws, l⟩ ha ⟨ws', l'⟩ hb e => ?_
    simp only [Prod.mk.injEq, List.cons.injEq] at e
    obtain ⟨⟨-, rfl⟩, -⟩ := e
    rw [fr ws l l' ha hb]
  · have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 h₁)
    refine this.imp fun {a b} ⟨ha, hb, hne⟩ x hx y hy e => ?_
    obtain ⟨v, k⟩ := a; obtain ⟨w, j⟩ := b
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, e'⟩ := hy
    rw [← e'] at e
    simp only [Prod.mk.injEq, List.cons.injEq] at e
    obtain ⟨⟨rfl, -⟩, -⟩ := e
    exact hne (by rw [fx v k j ha hb])

theorem vals_fun (s : Shape) (n : Nat) : ∀ v k k', (v, k) ∈ s.vals n → (v, k') ∈ s.vals n → k = k' :=
  fun v k k' h h' => size_unique ((mem_vals s n v k).1 h).1 ((mem_vals s n v k').1 h').1

theorem svals_fun (ss : Shapes) (n : Nat) : ∀ vs l l', (vs, l) ∈ ss.vals n → (vs, l') ∈ ss.vals n → l = l' :=
  fun vs l l' h h' => ssize_unique ((mem_svals ss n vs l).1 h).1 ((mem_svals ss n vs l').1 h').1

mutual
theorem nodup_vals : (s : Shape) → SDistinct s → (n : Nat) → (s.vals n).Nodup
  | .bool, _, n => by simp [Shape.vals]
  | .int, _, n => nodup_map_on (nodup_intsUpTo n) fun a _ b _ e => by simp at e; exact e.1
  | .nat, _, n => nodup_map_on List.nodup_range fun a _ b _ e => by simp at e; omega
  | .ints vs, h, _ => nodup_map_on h fun a _ b _ e => by simp at e; exact e.1
  | .abstract, _, n => nodup_map_on List.nodup_range fun a _ b _ e => by simp at e; exact e.1
  | .ctors cs, h, n => nodup_cvals cs h 0 n
  | .record fs, h, n => nodup_map_on (nodup_svals fs h n) fun ⟨vs, k⟩ ha ⟨ws, j⟩ hb e => by
      simp only [Prod.mk.injEq, EVal.ctor.injEq, valueSize] at e
      obtain ⟨⟨-, rfl⟩, rfl⟩ := e; rfl
  | .filter s keep, h, n => nodup_filter (nodup_vals s h n)
  | .empty, _, n => by simp [Shape.vals]
theorem nodup_svals : (ss : Shapes) → SsDistinct ss → (n : Nat) → (ss.vals n).Nodup
  | .nil, _, n => by simp [Shapes.vals]
  | .cons s rest, ⟨h₁, h₂⟩, n =>
    nodup_prodWith _ _ (nodup_vals s h₁ n) (nodup_svals rest h₂ n) (vals_fun s n) (svals_fun rest n)
theorem nodup_cvals : (cs : Ctors) → CDistinct cs → (i n : Nat) → (cs.vals i n).Nodup
  | .nil, _, _, _ => by simp [Ctors.vals]
  | .cons .nil rest, ⟨_, h⟩, i, n => by
    simp only [Ctors.vals]
    rw [List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_cvals rest h (i + 1) n⟩
    exact cvals_index_gt ((mem_cvals rest (i + 1) n _ _).1 hm).1
  | .cons (.cons p ps) rest, ⟨h₁, h₂⟩, i, n => by
    simp only [Ctors.vals]
    rw [List.nodup_append]
    refine ⟨?_, nodup_cvals rest h₂ (i + 1) n, ?_⟩
    · cases n with
      | zero => simp
      | succ m =>
        exact nodup_map_on (nodup_svals _ h₁ m) fun ⟨vs, k⟩ _ ⟨ws, j⟩ _ e => by
          simp only [Prod.mk.injEq, EVal.ctor.injEq, valueSize] at e
          obtain ⟨⟨-, rfl⟩, e⟩ := e; rw [show k = j by omega]
    · intro a ha b hb e
      subst e
      cases n with
      | zero => simp at ha
      | succ m =>
        simp only [List.mem_map] at ha
        obtain ⟨⟨vs, k⟩, -, rfl⟩ := ha
        exact cvals_index_gt ((mem_cvals rest (i + 1) _ _ _).1 hb).1
end


theorem mem_ordered (s : Shape) (n : Nat) (v : EVal) (k : Nat) :
    (v, k) ∈ s.ordered n ↔ SHas s v k ∧ k ≤ n := by
  simp only [Shape.ordered, List.mem_flatMap, List.mem_range, List.mem_filter, beq_iff_eq]
  rw [← mem_vals]
  constructor
  · rintro ⟨_, _, h, _⟩; exact h
  · intro h; exact ⟨k, by have := ((mem_vals s n v k).1 h).2; omega, h, rfl⟩

theorem nodup_ordered (s : Shape) (h : SDistinct s) (n : Nat) : (s.ordered n).Nodup := by
  rw [List.nodup_iff_pairwise_ne, Shape.ordered, List.pairwise_flatMap]
  refine ⟨fun k _ => (List.nodup_iff_pairwise_ne.1 (nodup_filter (nodup_vals s h n))), ?_⟩
  have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 (@List.nodup_range (n + 1)))
  refine this.imp fun ⟨_, _, hne⟩ x hx y hy e => ?_
  subst e
  simp only [List.mem_filter, beq_iff_eq] at hx hy
  exact hne (hx.2.symm.trans hy.2)

theorem ordered_sorted (s : Shape) (n : Nat) : (s.ordered n).Pairwise (fun a b => a.2 ≤ b.2) := by
  rw [Shape.ordered, List.pairwise_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · rw [List.pairwise_filter]
    exact List.pairwise_of_forall fun {a b} ha hb => by simp at ha hb; omega
  · refine (List.pairwise_lt_range).imp fun {i j} hij x hx y hy => ?_
    simp only [List.mem_filter, beq_iff_eq] at hx hy
    omega


/-- How many times `l` lists `x`. -/
noncomputable def times {α : Type} (l : List α) (x : α) : Nat :=
  open Classical in l.countP (fun y => decide (y = x))

open Classical in
theorem times_nodup {α : Type} (l : List α) (x : α) (h : l.Nodup) : times l x = if x ∈ l then 1 else 0 := by
  induction l with
  | nil => simp [times]
  | cons y ys ih =>
    rw [List.nodup_cons] at h
    have ih := ih h.2
    simp only [times] at ih ⊢
    rw [List.countP_cons, ih]
    by_cases hy : y = x
    · subst hy; simp [h.1]
    · have : ¬x = y := fun e => hy e.symm
      simp [hy, this]

/-! ## Exhausted shapes -/

mutual
theorem exhausted_within : (s : Shape) → (n : Nat) → s.exhausted n = true → ∀ {v k}, SHas s v k → k ≤ n
  | .bool, _, _, _, _, h => by cases h; omega
  | .int, _, he, _, _, _ => by simp [Shape.exhausted] at he
  | .nat, _, he, _, _, _ => by simp [Shape.exhausted] at he
  | .ints _, _, _, _, _, h => by cases h; omega
  | .abstract, _, he, _, _, _ => by simp [Shape.exhausted] at he
  | .ctors cs, n, he, _, _, h => by cases h with | ctors h => exact cexhausted_within cs 0 n (by simpa [Shape.exhausted] using he) h
  | .record fs, n, he, _, _, h => by cases h with | record h => exact sexhausted_within fs n (by simpa [Shape.exhausted] using he) h
  | .filter s _, n, he, _, _, h => by cases h with | filter h _ => exact exhausted_within s n (by simpa [Shape.exhausted] using he) h
  | .empty, _, _, _, _, h => by cases h
theorem sexhausted_within : (ss : Shapes) → (n : Nat) → ss.exhausted n = true → ∀ {vs k}, SsHas ss vs k → k ≤ n
  | .nil, _, _, _, _, h => by cases h; omega
  | .cons s rest, n, he, _, _, h => by
    simp only [Shapes.exhausted, Bool.and_eq_true] at he
    cases h with | cons h1 h2 => have := exhausted_within s n he.1 h1; have := sexhausted_within rest n he.2 h2; omega
theorem cexhausted_within : (cs : Ctors) → (i n : Nat) → cs.exhausted n = true → ∀ {v k}, CHas cs i v k → k ≤ n
  | .nil, _, _, _, _, _, h => by cases h
  | .cons .nil rest, i, n, he, _, _, h => by
    cases h with
    | nullary => omega
    | there h => exact cexhausted_within rest (i + 1) n (by simpa [Ctors.exhausted] using he) h
  | .cons (.cons p ps) rest, i, n, he, _, _, h => by
    simp only [Ctors.exhausted, Bool.and_eq_true] at he
    cases h with
    | payload h =>
      cases n with
      | zero => simp at he
      | succ m => have := sexhausted_within (.cons p ps) m he.1 h; omega
    | there h => exact cexhausted_within rest (i + 1) n he.2 h
end

/-! ## The search -/



theorem findSome_map {α β γ : Type} (l : List α) (g : α → Option β) (h : β → γ) :
    (l.findSome? g).map h = l.findSome? (fun a => (g a).map h) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hg : g a <;> simp [hg, ih]

theorem findSome_congr {α β : Type} (l : List α) (g g' : α → Option β) (h : ∀ a ∈ l, g a = g' a) :
    l.findSome? g = l.findSome? g' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem find_flatMap {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).find? p = l.findSome? (fun a => (f a).find? p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.find?_append, List.findSome?_cons, ih]
    cases (f a).find? p <;> rfl

/-- That `ok` accepts each prefix of `a` after `pre` as it is made. -/
def okAlong (ok : List Nat → Bool) (pre a : List Nat) : Bool :=
  (List.range a.length).all fun i => ok (pre ++ a.take (i + 1))

theorem okAlong_cons (ok : List Nat → Bool) (pre : List Nat) (j : Nat) (a : List Nat) :
    okAlong ok pre (j :: a) = (ok (pre ++ [j]) && okAlong ok (pre ++ [j]) a) := by
  simp only [okAlong, List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map]
  simp [Function.comp_def, List.take_succ_cons]

theorem dfs_spec (ok : List Nat → Bool) (lims pre : List Nat) :
    dfs ok pre lims = ((lexAll lims).find? (okAlong ok pre)).map (pre ++ ·) := by
  induction lims generalizing pre with
  | nil => simp [dfs, lexAll, okAlong]
  | cons l ls ih =>
    simp only [dfs, lexAll, find_flatMap, findSome_map]
    apply findSome_congr
    intro j _
    rw [List.find?_map]
    simp only [Function.comp_def, okAlong_cons]
    by_cases hj : ok (pre ++ [j]) = true
    · simp only [hj, if_true, Bool.true_and, ih, Option.map_map]
      congr 1; funext a; simp [Function.comp]
    · have hf : (List.find? (fun _ => false) (lexAll ls)) = none := by simp
      simp [hj, hf]

theorem setAll_not_mem (e : Array Nat) (ss c : List Nat) (s : Nat) (h : s ∉ ss) :
    (setAll e ss c)[s]? = e[s]? := by
  induction ss generalizing e c with
  | nil => simp [setAll]
  | cons x xs ih =>
    cases c with
    | nil => simp [setAll]
    | cons j js =>
      simp only [List.mem_cons, not_or] at h
      have := ih (e.set! x j) js h.2
      simp only [setAll, List.zip_cons_cons, List.foldl_cons] at this ⊢
      rw [this]
      simp [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm h.1)]

theorem setAll_split (e : Array Nat) (ss c : List Nat) (r : Nat) (hr : r ≤ c.length) :
    setAll e ss c = setAll (setAll e ss (c.take r)) (ss.drop r) (c.drop r) := by
  induction ss generalizing e c r with
  | nil => simp [setAll]
  | cons x xs ih =>
    cases c with
    | nil => simp [setAll]
    | cons j js =>
      cases r with
      | zero => simp [setAll]
      | succ r =>
        simp only [setAll, List.zip_cons_cons, List.foldl_cons, List.take_succ_cons, List.drop_succ_cons] at ih ⊢
        exact ih _ js r (by simp at hr; omega)

theorem not_mem_drop (l : List Nat) (h : l.Nodup) (s r : Nat) (hi : l.idxOf s < r) : s ∉ l.drop r := by
  induction l generalizing r with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    cases r with
    | zero => simp at hi
    | succ r =>
      simp only [List.drop_succ_cons]
      by_cases hx : x = s
      · subst hx; exact fun hm => h.1 (List.mem_of_mem_drop hm)
      · have : xs.idxOf s < r := by
          have hb : (x == s) = false := by simp [hx]
          simp only [List.idxOf, List.findIdx_cons, hb, cond_false] at hi; simp only [List.idxOf]; omega
        exact ih h.2 r this

def readyStep (slots : List Nat) (m s : Nat) : Nat := if slots.contains s then max m (slots.idxOf s + 1) else m

theorem readyAt_eq (slots ss : List Nat) : readyAt slots ss = ss.foldl (readyStep slots) 0 := rfl

theorem readyStep_ge (slots : List Nat) (m x : Nat) : m ≤ readyStep slots m x := by
  unfold readyStep; split <;> omega

theorem readyStep_mem (slots : List Nat) (m s : Nat) (hm : s ∈ slots) : slots.idxOf s < readyStep slots m s := by
  have : slots.contains s = true := by simpa using hm
  unfold readyStep; simp only [this, if_true]; omega

theorem fold_ge (slots ss : List Nat) (m : Nat) : m ≤ ss.foldl (readyStep slots) m := by
  induction ss generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have := ih (readyStep slots m x)
    have := readyStep_ge slots m x
    omega

theorem fold_mem (slots ss : List Nat) (s m : Nat) (hs : s ∈ ss) (hm : s ∈ slots) :
    slots.idxOf s < ss.foldl (readyStep slots) m := by
  induction ss generalizing m with
  | nil => simp at hs
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hs with rfl | hx
    · have := fold_ge slots xs (readyStep slots m s)
      have := readyStep_mem slots m s hm
      omega
    · exact ih _ hx

theorem fold_le (slots ss : List Nat) (m : Nat) (h : m ≤ slots.length) : ss.foldl (readyStep slots) m ≤ slots.length := by
  induction ss generalizing m with
  | nil => simpa
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold readyStep
    split
    · have : slots.idxOf x < slots.length := List.idxOf_lt_length_of_mem (by simpa using ‹slots.contains x = true›)
      omega
    · exact h

theorem readyAt_ge (slots ss : List Nat) (s : Nat) (hs : s ∈ ss) (hm : s ∈ slots) :
    slots.idxOf s < readyAt slots ss := by
  rw [readyAt_eq]; exact fold_mem slots ss s 0 hs hm

theorem readyAt_le (slots ss : List Nat) : readyAt slots ss ≤ slots.length := by
  rw [readyAt_eq]; exact fold_le slots ss 0 (Nat.zero_le _)

/-- That a part's value depends only on the slots it reads. -/
def Local (p : List Nat × (Array Nat → Bool)) : Prop :=
  ∀ e e' : Array Nat, (∀ s ∈ p.1, e[s]? = e'[s]?) → p.2 e = p.2 e'

theorem ready_agree (base : Array Nat) (slots a : List Nat) (hn : slots.Nodup) (hl : a.length = slots.length)
    (p : List Nat × (Array Nat → Bool)) (hp : Local p) :
    p.2 (setAll base slots (a.take (readyAt slots p.1))) = p.2 (setAll base slots a) := by
  apply hp
  intro s hs
  have hr := readyAt_le slots p.1
  rw [setAll_split base slots a (readyAt slots p.1) (by omega)]
  rw [setAll_not_mem (setAll base slots (a.take (readyAt slots p.1))) (slots.drop (readyAt slots p.1))
    (a.drop (readyAt slots p.1)) s ?_]
  intro hd
  have hm : s ∈ slots := List.mem_of_mem_drop hd
  exact not_mem_drop slots hn s _ (readyAt_ge slots p.1 s hs hm) hd


theorem find_congr {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem lexAll_length (lims a : List Nat) (h : a ∈ lexAll lims) : a.length = lims.length := by
  induction lims generalizing a with
  | nil => simp [lexAll] at h; simp [h]
  | cons l ls ih =>
    simp only [lexAll, List.mem_flatMap, List.mem_map] at h
    obtain ⟨j, _, b, hb, rfl⟩ := h
    simp [ih b hb]

theorem newlyHold_eq (base : Array Nat) (slots : List Nat) (ps : List (Nat × (Array Nat → Bool))) (c : List Nat) :
    newlyHold base slots ps c = ps.all fun p => p.1 != c.length || p.2 (setAll base slots c) := by
  unfold newlyHold
  by_cases h : (ps.filter (·.1 == c.length)).isEmpty
  · simp only [h, Bool.true_or]
    symm; rw [List.all_eq_true]; intro p hp
    rw [List.isEmpty_iff, List.filter_eq_nil_iff] at h
    have := h p hp; simp at this; simp [this]
  · simp only [h, Bool.false_or]
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.mem_filter, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true]
    constructor
    · intro hall p hp
      by_cases hr : p.1 = c.length
      · exact Or.inr (hall p ⟨hp, hr⟩)
      · exact Or.inl hr
    · intro hall p ⟨hp, hr⟩
      rcases hall p hp with h' | h'
      · exact absurd hr h'
      · exact h'

theorem key (base : Array Nat) (slots : List Nat) (parts : List (List Nat × (Array Nat → Bool))) (a : List Nat)
    (hn : slots.Nodup) (hl : a.length = slots.length) (hloc : ∀ p ∈ parts, Local p) :
    (newlyHold base slots (parts.map fun (ss, f) => (readyAt slots ss, f)) [] &&
      okAlong (newlyHold base slots (parts.map fun (ss, f) => (readyAt slots ss, f))) [] a) =
    parts.all (·.2 (setAll base slots a)) := by
  apply Bool.eq_iff_iff.2
  simp only [okAlong, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.nil_append, newlyHold_eq,
    List.mem_map, bne_iff_ne, ne_eq, Bool.or_eq_true, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, List.length_nil, List.length_take]
  constructor
  · rintro ⟨h0, hall⟩ p hp
    have hr := readyAt_le slots p.1
    rw [← ready_agree base slots a hn hl p (hloc p hp)]
    by_cases hz : readyAt slots p.1 = 0
    · rcases h0 p hp with h | h
      · exact absurd hz h
      · rw [hz]; simpa using h
    · rcases hall (readyAt slots p.1 - 1) (by omega) p hp with h | h
      · omega
      · have : readyAt slots p.1 - 1 + 1 = readyAt slots p.1 := by omega
        rw [this] at h; exact h
  · intro hall
    refine ⟨fun p hp => ?_, fun i hi p hp => ?_⟩
    · by_cases hz : readyAt slots p.1 = 0
      · right; have := hall p hp; rw [← ready_agree base slots a hn hl p (hloc p hp), hz] at this; simpa using this
      · left; exact hz
    · by_cases hz : readyAt slots p.1 = min (i + 1) a.length
      · right
        have := hall p hp
        rw [← ready_agree base slots a hn hl p (hloc p hp)] at this
        have hh : min (i + 1) a.length = i + 1 := by omega
        rw [hz, hh] at this; exact this
      · left; exact hz

theorem firstChoice_spec (base : Array Nat) (slots lims : List Nat) (parts : List (List Nat × (Array Nat → Bool)))
    (hn : slots.Nodup) (hlen : lims.length = slots.length) (hloc : ∀ p ∈ parts, Local p) :
    firstChoice base slots lims parts =
      ((lexAll lims).find? fun a => parts.all (·.2 (setAll base slots a))).map (setAll base slots) := by
  unfold firstChoice
  simp only
  rw [dfs_spec]
  have hk : ∀ a ∈ lexAll lims, _ := fun a ha => key base slots parts a hn (by rw [lexAll_length lims a ha, hlen]) hloc
  split
  · rename_i h0
    rw [Option.map_map]
    have hf : (setAll base slots ∘ fun x => [] ++ x) = setAll base slots := by funext a; simp
    rw [hf]
    congr 1
    apply find_congr
    intro a ha
    have := hk a ha; rw [h0, Bool.true_and] at this; exact this
  · rename_i h0
    symm
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro a ha
    have := hk a ha
    simp only [Bool.not_eq_true] at h0
    rw [h0, Bool.false_and] at this
    simp [← this]


theorem dedup_nodup (xs : List Nat) : (dedup xs).Nodup := by
  unfold dedup
  suffices ∀ acc : List Nat, acc.Nodup → (xs.foldl (fun (a : List Nat) x => if a.contains x then a else a ++ [x]) acc).Nodup from this [] List.nodup_nil
  induction xs with
  | nil => intro acc h; simpa
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i hx
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb e
      simp at hb; subst hb; subst e
      exact hx (by simpa using ha)

theorem slotsOf_nodup (sp : Space) (ats : Atoms) (parts : Array EF) : (slotsOf sp ats parts).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (dedup_nodup _)

theorem any_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons]; rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem levelPart_local (sp : Space) (slots : List Nat) (k : Nat) : Local (sp.levelPart slots k) := by
  intro e e' h
  simp only [Space.levelPart] at h ⊢
  apply any_congr_mem
  intro s hs
  rw [h s hs]


/-- The search finds the first assignment of the fair order that makes
every part true, where each part's value depends only on the slots it
reads. -/
theorem search_spec (sp : Space) (ats : Atoms) (parts : Array EF)
    (hloc : ∀ p ∈ partsOf sp ats parts, Local p) (hne : slotsOf sp ats parts ≠ []) :
    (search sp ats parts).map (·.1) =
      ((sp.fairList (Array.replicate sp.names.size 0) (slotsOf sp ats parts)).find? fun a =>
        (partsOf sp ats parts).all (·.2 (setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts) a))).map
        (setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts)) := by
  have hne' : (slotsOf sp ats parts).isEmpty = false := by simpa using hne
  simp only [search, hne', Bool.false_eq_true, if_false, Space.fairList, fairList, find_flatMap, findSome_map,
    Option.map_map]
  apply findSome_congr
  intro k _
  rw [firstChoice_spec _ _ _ _ (slotsOf_nodup sp ats parts) (by simp) ?_]
  · rw [List.find?_filter, Option.map_map]
    have hf : (Prod.fst ∘ fun x => (x, k)) ∘ setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts) =
        setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts) := by funext a; rfl
    rw [hf]
    congr 1
    apply find_congr
    intro a _
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    cases (sp.levelPart (slotsOf sp ats parts) k).2 _ <;> simp [Bool.and_comm]
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hloc p hp
    · simp at hp; subst hp; exact levelPart_local sp _ k


/-- Two assignments of the same slots agree on the slots `ss`. -/
def Agree (ss : List Nat) (e e' : Array Nat) : Prop := e.size = e'.size ∧ ∀ s ∈ ss, e[s]? = e'[s]?

theorem Agree.mono {ss ss' : List Nat} {e e' : Array Nat} (h : Agree ss e e') (hs : ∀ s ∈ ss', s ∈ ss) : Agree ss' e e' :=
  ⟨h.1, fun s m => h.2 s (hs s m)⟩

theorem setAll_size (e : Array Nat) (ss c : List Nat) : (setAll e ss c).size = e.size := by
  induction ss generalizing e c with
  | nil => simp [setAll]
  | cons x xs ih =>
    cases c with
    | nil => simp [setAll]
    | cons j js =>
      have := ih (e.set! x j) js
      simp only [setAll, List.zip_cons_cons, List.foldl_cons] at this ⊢
      rw [this]; simp [Array.set!_eq_setIfInBounds]

theorem setAll_mem (e : Array Nat) (ss c : List Nat) (hn : ss.Nodup) (s : Nat) (hs : s ∈ ss)
    (hi : ss.idxOf s < c.length) : (setAll e ss c)[s]? = if s < e.size then c[ss.idxOf s]? else none := by
  induction ss generalizing e c with
  | nil => simp at hs
  | cons x xs ih =>
    rw [List.nodup_cons] at hn
    cases c with
    | nil => simp at hi
    | cons j js =>
      show (setAll (e.set! x j) xs js)[s]? = _
      by_cases hx : x = s
      · subst hx
        rw [setAll_not_mem _ _ _ _ hn.1]
        simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
      · have hs' : s ∈ xs := (List.mem_cons.1 hs).resolve_left (fun h => hx h.symm)
        have hb : (x == s) = false := by simp [hx]
        have hidx : (x :: xs).idxOf s = xs.idxOf s + 1 := by simp [List.idxOf, List.findIdx_cons, hb]
        rw [hidx] at hi ⊢
        rw [ih (e.set! x j) js hn.2 hs' (by simpa using hi)]
        simp [Array.set!_eq_setIfInBounds]

theorem primed_agree (sp : Space) (ss : List Nat) (e e' : Array Nat)
    (h : Agree (ss.map fun x => (sp.primeOf[x]?.join).getD x) e e') : Agree ss (sp.primedEnv e) (sp.primedEnv e') := by
  refine ⟨by simp [Space.primedEnv, h.1], fun s hs => ?_⟩
  unfold Space.primedEnv
  rw [Array.getElem?_mapIdx, Array.getElem?_mapIdx]
  have hm : (sp.primeOf[s]?.join).getD s ∈ ss.map fun x => (sp.primeOf[x]?.join).getD x := List.mem_map_of_mem hs
  cases hp : sp.primeOf[s]?.join with
  | none =>
    rw [hp] at hm; have := h.2 s (by simpa using hm); rw [this]
  | some p =>
    rw [hp] at hm; have hpe := h.2 p (by simpa using hm)
    have hpe' : e.getD p 0 = e'.getD p 0 := by simp only [Array.getD_eq_getD_getElem?, hpe]
    by_cases hlt : s < e.size
    · have hlt' : s < e'.size := h.1 ▸ hlt
      simp [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem hlt', hpe']
    · have hlt' : ¬ s < e'.size := h.1 ▸ hlt
      simp [Array.getElem?_eq_none (Nat.le_of_not_lt hlt), Array.getElem?_eq_none (Nat.le_of_not_lt hlt')]


theorem all_attach_congr (fs : Array EF) (p q : EF → Bool) (h : ∀ f ∈ fs, p f = q f) :
    (fs.attach.all fun x => p x.1) = (fs.attach.all fun x => q x.1) := by
  apply Bool.eq_iff_iff.2
  rw [Array.all_eq_true, Array.all_eq_true]
  constructor
  · intro hh i hi
    have := hh i hi
    simp only [Array.getElem_attach] at this ⊢
    rw [← h _ (Array.getElem_mem (by simpa using hi))]; exact this
  · intro hh i hi
    have := hh i hi
    simp only [Array.getElem_attach] at this ⊢
    rw [h _ (Array.getElem_mem (by simpa using hi))]; exact this

theorem mem_conj_slots (sp : Space) (ats : Atoms) (fs : Array EF) (g : EF) (hg : g ∈ fs) (s : Nat)
    (hs : s ∈ g.slots sp ats) : s ∈ (EF.conj fs).slots sp ats := by
  simp only [EF.slots, List.mem_flatten, List.mem_map]
  exact ⟨g.slots sp ats, ⟨⟨g, hg⟩, Array.mem_toList_iff.2 (Array.mem_attach _ _), rfl⟩, hs⟩

theorem dfs_congr (ok ok' : List Nat → Bool) (lims pre : List Nat)
    (h : ∀ c, c.length ≤ pre.length + lims.length → ok c = ok' c) : dfs ok pre lims = dfs ok' pre lims := by
  induction lims generalizing pre with
  | nil => rfl
  | cons l ls ih =>
    simp only [dfs]
    apply findSome_congr
    intro j _
    rw [h (pre ++ [j]) (by simp)]
    rw [ih (pre ++ [j]) (fun c hc => h c (by simp at hc ⊢; omega))]

/-- Where `f` reads a slot of `outs` only after choosing it, `newlyHold`
agrees on two bases that agree elsewhere. -/
theorem firstChoice_isSome_congr (e e' : Array Nat) (outs lims : List Nat) (parts : List (List Nat × (Array Nat → Bool)))
    (hlen : lims.length = outs.length)
    (h : ∀ c, c.length ≤ outs.length → ∀ p ∈ parts, readyAt outs p.1 = c.length →
      p.2 (setAll e outs c) = p.2 (setAll e' outs c)) :
    (firstChoice e outs lims parts).isSome = (firstChoice e' outs lims parts).isSome := by
  have hn : ∀ c, c.length ≤ outs.length →
      newlyHold e outs (parts.map fun (ss, f) => (readyAt outs ss, f)) c =
        newlyHold e' outs (parts.map fun (ss, f) => (readyAt outs ss, f)) c := by
    intro c hc
    rw [newlyHold_eq, newlyHold_eq]
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      bne_iff_ne, ne_eq, Bool.or_eq_true]
    constructor
    · intro hh p hp
      rcases hh p hp with h1 | h1
      · exact Or.inl h1
      · by_cases hr : readyAt outs p.1 = c.length
        · exact Or.inr (by rw [← h c hc p hp hr]; exact h1)
        · exact Or.inl hr
    · intro hh p hp
      rcases hh p hp with h1 | h1
      · exact Or.inl h1
      · by_cases hr : readyAt outs p.1 = c.length
        · exact Or.inr (by rw [h c hc p hp hr]; exact h1)
        · exact Or.inl hr
  unfold firstChoice
  simp only
  rw [hn [] (by simp)]
  split
  · rw [dfs_congr _ (newlyHold e' outs (parts.map fun (ss, f) => (readyAt outs ss, f))) lims []
      (fun c hc => hn c (by simp at hc; omega))]
    cases dfs _ [] lims <;> simp
  · rfl


/-- The slots of a formula under `∃ outputs`, chosen or not, agree in two
bases set to the same choice of the outputs, where the bases agree on the
slots that are not outputs. -/
theorem setAll_outs_agree (sp : Space) (ss fslots : List Nat) (env e' : Array Nat) (c : List Nat)
    (houts : sp.outputs.toList.Nodup) (hsub : ∀ s ∈ ss, s ∈ fslots)
    (h : Agree (fslots.filter (!sp.outputs.contains ·)) env e')
    (hready : readyAt (sp.outputs.toList.filter fun o => fslots.contains o) ss = c.length) :
    Agree ss (setAll env (sp.outputs.toList.filter fun o => fslots.contains o) c)
      (setAll e' (sp.outputs.toList.filter fun o => fslots.contains o) c) := by
  let outs := sp.outputs.toList.filter fun o => fslots.contains o
  have hn : outs.Nodup := houts.sublist List.filter_sublist
  refine ⟨by rw [setAll_size, setAll_size, h.1], fun s hs => ?_⟩
  by_cases ho : s ∈ outs
  · have hi : outs.idxOf s < c.length := hready ▸ readyAt_ge outs ss s hs ho
    rw [setAll_mem _ _ _ hn s ho hi, setAll_mem _ _ _ hn s ho hi, h.1]
  · rw [setAll_not_mem _ _ _ _ ho, setAll_not_mem _ _ _ _ ho]
    apply h.2
    simp only [List.mem_filter, Bool.not_eq_true']
    refine ⟨hsub s hs, ?_⟩
    cases hc : sp.outputs.contains s with
    | false => rfl
    | true =>
      exfalso
      apply ho
      simp only [outs, List.mem_filter]
      refine ⟨?_, by simpa using hsub s hs⟩
      rw [Array.contains_iff_mem] at hc
      exact Array.mem_toList_iff.2 hc

/-- What each formula's value depends on: given that each atom's value
depends only on the slots it reads, and each defined output's on those of
its definition, the value of every formula depends only on `EF.slots`
(`check::slots_suffice`). -/
theorem eval_local (sp : Space) (ats : Atoms)
    (hat : ∀ k e e', Agree (ats.slots[k]?.getD #[]).toList e e' → ats.eval k e = ats.eval k e')
    (hsame : ∀ x e₁ e₂ e₁' e₂', Agree (ats.defSlots x).toList e₁ e₁' → Agree (ats.defSlots x).toList e₂ e₂' →
      ats.sameDefined x e₁ e₂ = ats.sameDefined x e₁' e₂')
    (houts : sp.outputs.toList.Nodup) (env : Array Nat) (f : EF) :
    ∀ e', Agree (f.slots sp ats) env e' → f.eval sp ats env = f.eval sp ats e' := by
  induction env, f using EF.eval.induct sp ats with
  | case1 env k => intro e' h; simp only [EF.slots] at h; simp only [EF.eval]; exact hat k env e' h
  | case2 env => intro e' _; simp only [EF.eval]
  | case3 env => intro e' _; simp only [EF.eval]
  | case4 env f ih => intro e' h; simp only [EF.slots] at h; simp only [EF.eval]; rw [ih e' h]
  | case5 env fs ih =>
    intro e' h
    simp only [EF.eval]
    exact all_attach_congr fs _ _ fun g hg =>
      ih g hg e' (h.mono fun s hs => mem_conj_slots sp ats fs g hg s hs)
  | case6 env fs ih =>
    intro e' h
    have hs : (EF.exOutputs (EF.conj fs)).slots sp ats = ((EF.conj fs).slots sp ats).filter (!sp.outputs.contains ·) := by
      rw [EF.slots.eq_def sp ats (EF.exOutputs (EF.conj fs))]
    rw [hs] at h
    simp only [EF.eval]
    apply firstChoice_isSome_congr _ _ _ _ _ (by simp)
    intro c _ p hp hr
    simp only [List.mem_map] at hp
    obtain ⟨⟨g, hg⟩, _, rfl⟩ := hp
    exact ih g hg _ _ (setAll_outs_agree sp _ _ _ _ c houts (fun s hs => mem_conj_slots sp ats fs g hg s hs) h hr)
  | case7 env f hnc ih =>
    intro e' h
    have hs : (EF.exOutputs f).slots sp ats = (f.slots sp ats).filter (!sp.outputs.contains ·) := by
      simp only [EF.slots]
    rw [hs] at h
    have he : ∀ e, (EF.exOutputs f).eval sp ats e =
        (firstChoice e (sp.outputs.toList.filter fun o => (f.slots sp ats).contains o)
          ((sp.outputs.toList.filter fun o => (f.slots sp ats).contains o).map fun s => (sp.sizes[s]?.getD #[]).size)
          [(f.slots sp ats, fun e => f.eval sp ats e)]).isSome := by
      intro e
      cases f with
      | conj fs => exact absurd rfl (hnc fs)
      | _ => simp only [EF.eval]
    rw [he, he]
    apply firstChoice_isSome_congr _ _ _ _ _ (by simp)
    intro c _ p hp hr
    simp only [List.mem_singleton] at hp
    subst hp
    exact ih _ _ (setAll_outs_agree sp _ _ _ _ c houts (fun s hs => hs) h hr)
  | case8 env x v =>
    intro e' h; simp only [EF.eval]; rw [h.2 x (by simp [EF.slots])]
  | case9 env x vs =>
    intro e' h; simp only [EF.eval]; rw [h.2 x (by simp [EF.slots])]
  | case10 env f ih =>
    intro e' h
    simp only [EF.slots] at h
    simp only [EF.eval]
    exact ih (sp.primedEnv e') (primed_agree sp _ env e' h)
  | case11 env x s hs p hp =>
    intro e' h
    simp only [EF.eval, hs, hp]
    rw [h.2 s (by simp [EF.slots, hs]), h.2 p (by simp [EF.slots, hs, hp])]
  | case12 env x s hs hp => intro e' _; simp only [EF.eval, hs, hp]
  | case13 env x hs =>
    intro e' h
    simp only [EF.eval, hs]
    have hsl : (EF.same x).slots sp ats = (ats.defSlots x).toList ++ (ats.defSlots x).toList.filterMap (sp.primeOf[·]?.join) := by
      simp [EF.slots, hs]
    rw [hsl] at h
    apply hsame
    · exact h.mono fun s hs => List.mem_append_left _ hs
    · apply primed_agree
      apply h.mono
      intro s hs
      simp only [List.mem_map] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      cases hp : sp.primeOf[y]?.join with
      | none => exact List.mem_append_left _ hy
      | some p => exact List.mem_append_right _ (List.mem_filterMap.2 ⟨y, hy, hp⟩)


theorem nodup_map_on' {α β : Type} {f : α → β} {l : List α} (h : l.Nodup)
    (inj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 h)
  exact this.imp fun ⟨ha, hb, hne⟩ e => hne (inj _ ha _ hb e)

/-- Each value of a choice is below its slot's number of values. -/
inductive Fits : List Nat → List Nat → Prop
  | nil : Fits [] []
  | cons {j l a ls} : j < l → Fits a ls → Fits (j :: a) (l :: ls)

theorem nodup_filter' {α : Type} {p : α → Bool} {l : List α} (h : l.Nodup) : (l.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_filter]
  exact (List.nodup_iff_pairwise_ne.1 h).imp fun hne _ _ => hne

theorem mem_lexAll (lims a : List Nat) : a ∈ lexAll lims ↔ Fits a lims := by
  induction lims generalizing a with
  | nil =>
    simp only [lexAll, List.mem_singleton]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons l ls ih =>
    simp only [lexAll, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j, hj, b, hb, rfl⟩; exact Fits.cons hj ((ih b).1 hb)
    · intro h
      cases h with
      | cons hj hb => exact ⟨_, hj, _, (ih _).2 hb, rfl⟩

theorem lexAll_nodup (lims : List Nat) : (lexAll lims).Nodup := by
  induction lims with
  | nil => simp [lexAll]
  | cons l ls ih =>
    rw [List.nodup_iff_pairwise_ne, lexAll, List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · rw [← List.nodup_iff_pairwise_ne]
      exact nodup_map_on' ih fun a _ b _ e => by simpa using e
    · have := List.Pairwise.and_mem.1 (List.nodup_iff_pairwise_ne.1 (@List.nodup_range l))
      refine this.imp fun ⟨_, _, hne⟩ x hx y hy e => ?_
      simp only [List.mem_map] at hx hy
      obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy
      simp at e; exact hne e.1


theorem setAll_pair (base : Array Nat) (slots a : List Nat) (hn : slots.Nodup) (s j : Nat)
    (hm : (s, j) ∈ slots.zip a) (hs : s < base.size) : (setAll base slots a)[s]? = some j := by
  induction slots generalizing base a with
  | nil => simp at hm
  | cons x xs ih =>
    rw [List.nodup_cons] at hn
    cases a with
    | nil => simp at hm
    | cons j0 js =>
      show (setAll (base.set! x j0) xs js)[s]? = _
      have hm' : (s = x ∧ j = j0) ∨ (s, j) ∈ xs.zip js := by simpa using hm
      rcases hm' with ⟨rfl, rfl⟩ | h
      · rw [setAll_not_mem _ _ _ _ hn.1]
        simp [Array.set!_eq_setIfInBounds, hs]
      · exact ih (base.set! x j0) js hn.2 h (by simp [Array.set!_eq_setIfInBounds, hs])

theorem fold_max_ge (sp : Space) (l : List (Nat × Nat)) (m : Nat) :
    m ≤ l.foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) m := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; have := ih (max m (sp.sizeAt x.1 x.2)); omega

theorem fold_max_mem (sp : Space) (l : List (Nat × Nat)) (m : Nat) (p : Nat × Nat) (hp : p ∈ l) :
    sp.sizeAt p.1 p.2 ≤ l.foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) m := by
  induction l generalizing m with
  | nil => simp at hp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | h
    · have := fold_max_ge sp xs (max m (sp.sizeAt p.1 p.2)); omega
    · exact ih _ h

theorem fold_max_attained (sp : Space) (l : List (Nat × Nat)) (m : Nat) :
    l.foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) m = m ∨
      ∃ p ∈ l, sp.sizeAt p.1 p.2 = l.foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) m := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (max m (sp.sizeAt x.1 x.2)) with h | ⟨p, hp, h⟩
    · rw [h]
      by_cases hx : sp.sizeAt x.1 x.2 ≤ m
      · left; omega
      · right; exact ⟨x, by simp, by omega⟩
    · right; exact ⟨p, by simp [hp], h⟩

theorem levelOf_ge (sp : Space) (slots a : List Nat) (s j : Nat) (hm : (s, j) ∈ slots.zip a) :
    sp.sizeAt s j ≤ sp.levelOf slots a := fold_max_mem sp _ 0 (s, j) hm

theorem levelOf_attained (sp : Space) (slots a : List Nat) (hne : slots.zip a ≠ []) :
    ∃ p ∈ slots.zip a, sp.sizeAt p.1 p.2 = sp.levelOf slots a := by
  rcases fold_max_attained sp (slots.zip a) 0 with h | h
  · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    refine ⟨p, hp, ?_⟩
    have := fold_max_mem sp _ 0 p hp
    unfold Space.levelOf; omega
  · exact h

theorem fits_zip (slots a : List Nat) (lim : Nat → Nat) :
    Fits a (slots.map lim) ↔ a.length = slots.length ∧ ∀ p ∈ slots.zip a, p.2 < lim p.1 := by
  induction slots generalizing a with
  | nil =>
    cases a with
    | nil => simp only [List.map_nil, List.length_nil, List.zip_nil_left, List.not_mem_nil, false_imp_iff,
        implies_true, and_self, iff_true]; exact .nil
    | cons j js => constructor
                   · intro h; cases h
                   · rintro ⟨h, -⟩; simp at h
  | cons x xs ih =>
    cases a with
    | nil => constructor
             · intro h; cases h
             · rintro ⟨h, -⟩; simp at h
    | cons j js =>
      simp only [List.map_cons, List.length_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp,
        Nat.add_right_cancel_iff]
      constructor
      · intro h; cases h with | cons hj hr => have := (ih js).1 hr; exact ⟨this.1, hj, this.2⟩
      · rintro ⟨hl, hj, hr⟩; exact .cons hj ((ih js).2 ⟨hl, hr⟩)


theorem zip_exists (slots a : List Nat) (hl : a.length = slots.length) (s : Nat) (hs : s ∈ slots) :
    ∃ j, (s, j) ∈ slots.zip a := by
  induction slots generalizing a with
  | nil => simp at hs
  | cons x xs ih =>
    cases a with
    | nil => simp at hl
    | cons j js =>
      rcases List.mem_cons.1 hs with rfl | h
      · exact ⟨j, by simp⟩
      · obtain ⟨j', hj⟩ := ih js (by simpa using hl) h
        exact ⟨j', by simp [hj]⟩

theorem zip_mem_left (slots a : List Nat) (p : Nat × Nat) (h : p ∈ slots.zip a) : p.1 ∈ slots :=
  (List.of_mem_zip h).1

/-- The space's invariant that the search relies on: of each slot's
values, those of size at most `k`, up to the bound, are its first
`within s k`. -/
def SizesOrdered (sp : Space) (slots : List Nat) : Prop :=
  ∀ s ∈ slots, ∀ k ≤ sp.bound, ∀ j, j < sp.within s k ↔ (j < (sp.sizes[s]?.getD #[]).size ∧ sp.sizeAt s j ≤ k)

theorem levelPart_iff (sp : Space) (base : Array Nat) (slots a : List Nat) (k : Nat) (hn : slots.Nodup)
    (hl : a.length = slots.length) (hs : ∀ s ∈ slots, s < base.size) :
    (sp.levelPart slots k).2 (setAll base slots a) = true ↔ ∃ p ∈ slots.zip a, sp.sizeAt p.1 p.2 = k := by
  simp only [Space.levelPart, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨s, hm, h⟩
    obtain ⟨j, hj⟩ := zip_exists slots a hl s hm
    rw [setAll_pair base slots a hn s j hj (hs s hm)] at h
    exact ⟨(s, j), hj, h⟩
  · rintro ⟨⟨s, j⟩, hj, h⟩
    have hm := zip_mem_left slots a _ hj
    refine ⟨s, hm, ?_⟩
    rw [setAll_pair base slots a hn s j hj (hs s hm)]
    exact h

/-- Each assignment of a level's block is of that level. -/
theorem block_level (sp : Space) (base : Array Nat) (slots a : List Nat) (k : Nat) (hk : k ≤ sp.bound)
    (hn : slots.Nodup) (hs : ∀ s ∈ slots, s < base.size) (hw : SizesOrdered sp slots)
    (ha : a ∈ lexAll (slots.map (sp.within · k))) (hlev : (sp.levelPart slots k).2 (setAll base slots a) = true) :
    sp.levelOf slots a = k := by
  have hf := (fits_zip slots a _).1 ((mem_lexAll _ a).1 ha)
  obtain ⟨⟨s, j⟩, hj, hsz⟩ := (levelPart_iff sp base slots a k hn hf.1 hs).1 hlev
  have hge := levelOf_ge sp slots a s j hj
  have hle : sp.levelOf slots a ≤ k := by
    have hne : slots.zip a ≠ [] := List.ne_nil_of_mem hj
    obtain ⟨p, hp, hp'⟩ := levelOf_attained sp slots a hne
    have := ((hw p.1 (zip_mem_left slots a p hp) k hk p.2).1 (hf.2 p hp)).2
    omega
  simp at hsz; omega

/-- No starvation: every assignment of the slots up to the bound is in the
fair order (`check::fair_order`). -/
theorem fair_complete (sp : Space) (base : Array Nat) (slots a : List Nat) (hne : slots ≠ [])
    (hn : slots.Nodup) (hs : ∀ s ∈ slots, s < base.size) (hw : SizesOrdered sp slots)
    (ha : a ∈ lexAll (slots.map (sp.within · sp.bound))) : a ∈ sp.fairList base slots := by
  have hf := (fits_zip slots a _).1 ((mem_lexAll _ a).1 ha)
  have hz : slots.zip a ≠ [] := by
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨j, hj⟩ := zip_exists slots a hf.1 s hs
    exact List.ne_nil_of_mem hj
  obtain ⟨p, hp, hpL⟩ := levelOf_attained sp slots a hz
  have hall : ∀ q ∈ slots.zip a, q.2 < (sp.sizes[q.1]?.getD #[]).size ∧ sp.sizeAt q.1 q.2 ≤ sp.bound :=
    fun q hq => (hw q.1 (zip_mem_left slots a q hq) sp.bound (Nat.le_refl _) q.2).1 (hf.2 q hq)
  have hL : sp.levelOf slots a ≤ sp.bound := hpL ▸ (hall p hp).2
  simp only [Space.fairList, fairList, List.mem_flatMap, List.mem_range, List.mem_filter]
  refine ⟨sp.levelOf slots a, by omega, ?_, ?_⟩
  · rw [mem_lexAll, fits_zip]
    refine ⟨hf.1, fun q hq => ?_⟩
    exact (hw q.1 (zip_mem_left slots a q hq) _ hL q.2).2 ⟨(hall q hq).1, levelOf_ge sp slots a q.1 q.2 hq⟩
  · exact (levelPart_iff sp base slots a _ hn hf.1 hs).2 ⟨p, hp, hpL⟩

/-- The fair order lists the assignments smallest first: by level
(`check::fair_order`). -/
theorem fair_sorted (sp : Space) (base : Array Nat) (slots : List Nat)
    (hn : slots.Nodup) (hs : ∀ s ∈ slots, s < base.size) (hw : SizesOrdered sp slots) :
    (sp.fairList base slots).Pairwise fun a b => sp.levelOf slots a ≤ sp.levelOf slots b := by
  simp only [Space.fairList, fairList]
  rw [List.pairwise_flatMap]
  refine ⟨fun k hk => ?_, ?_⟩
  · refine (List.pairwise_of_forall (R := fun _ _ => True) (fun _ _ => trivial)).imp_of_mem ?_
    intro a b ha hb _
    simp only [List.mem_filter] at ha hb
    simp [List.mem_range] at hk
    rw [block_level sp base slots a k (by omega) hn hs hw ha.1 ha.2, block_level sp base slots b k (by omega) hn hs hw hb.1 hb.2]
    exact Nat.le_refl _
  · refine (List.Pairwise.and_mem.1 List.pairwise_lt_range).imp fun {k k'} ⟨_, hk', hkk'⟩ a ha b hb => ?_
    simp only [List.mem_filter] at ha hb
    simp only [List.mem_range] at hk'
    rw [block_level sp base slots a k (by omega) hn hs hw ha.1 ha.2, block_level sp base slots b k' (by omega) hn hs hw hb.1 hb.2]
    omega


/-- The fair order lists each assignment once (`check::fair_order`). -/
theorem fair_nodup (sp : Space) (base : Array Nat) (slots : List Nat)
    (hn : slots.Nodup) (hs : ∀ s ∈ slots, s < base.size) (hw : SizesOrdered sp slots) :
    (sp.fairList base slots).Nodup := by
  simp only [Space.fairList, fairList]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun k _ => List.nodup_iff_pairwise_ne.1 (nodup_filter' (lexAll_nodup _)), ?_⟩
  refine (List.Pairwise.and_mem.1 List.pairwise_lt_range).imp fun {k k'} ⟨hk, hk', hkk'⟩ a ha b hb e => ?_
  subst e
  simp only [List.mem_filter] at ha hb
  simp only [List.mem_range] at hk hk'
  have h1 := block_level sp base slots a k (by omega) hn hs hw ha.1 ha.2
  have h2 := block_level sp base slots a k' (by omega) hn hs hw hb.1 hb.2
  omega


/-! ## The links -/

open Classical in
-- Each value of a shape of size at most the bound is listed once, and
-- nothing else is (`Shape.vals`).
impl listed: check::listed for (sh : Shape) (_h : SDistinct sh) (n : Nat) (v : EVal) (k : Nat) {
  value? := decide (SHas sh v k),
  size := k,
  bound := n,
  times := times (sh.vals n) (v, k),
} by
  intro sh h n v k
  simp only [fren_spec]
  rw [times_nodup _ _ (nodup_vals sh h n)]
  intro _
  have := mem_vals sh n v k
  by_cases hv : SHas sh v k <;> by_cases hk : k ≤ n <;> simp_all

-- Smallest first (`Shape.ordered`).
impl smallest_first: check::smallest_first for (sh : Shape) (n i j : Nat) {
  earlier? := decide (i < j ∧ j < (sh.ordered n).length),
  first := (((sh.ordered n)[i]?).map (·.2)).getD 0,
  second := (((sh.ordered n)[j]?).map (·.2)).getD 0,
  ordered? := true,
} by
  intro sh n i j
  simp only [fren_spec]
  by_cases hij : i < j ∧ j < (sh.ordered n).length
  · have := List.pairwise_iff_getElem.1 (ordered_sorted sh n) i j (by omega) hij.2 hij.1
    simp [hij, List.getElem?_eq_getElem (show i < (sh.ordered n).length by omega), this]
  · simp [hij]

instance : Fren.Finite SizeKind :=
  ⟨[.bool, .int, .nat, .finiteInt, .abstract, .nullary, .variant, .record], by intro x; cases x <;> simp⟩

def toSized : SizeKind → check.Sized
  | .bool => .Boolean
  | .int => .Integer
  | .nat => .Natural
  | .finiteInt => .FiniteInteger
  | .abstract => .AbstractValue
  | .nullary => .Nullary
  | .variant => .WithPayload
  | .record => .Record

-- The sizes that `Shape.vals` gives its values.
impl value_size: check::value_size for (sk : SizeKind) (i : Int) (l : Nat) {
  kind := toSized sk,
  value := i,
  largest := l,
  size := valueSize sk i l,
} by
  intro sk i l
  cases sk <;> simp [fren_spec, toSized, valueSize] <;> omega

-- The limit on the behaviours that a component's enumeration searches.
impl enumeration_limit: check::enumeration_limit for (c : Nat) {
  count := c,
  runs? := withinLimit c,
} by
  intro c
  simp only [fren_spec, withinLimit, maxBehaviours]
  intro _
  simp only [decide_eq_true_eq]
  omega

instance : Fren.Finite check.EvidenceValue :=
  ⟨[.Solver, .Random, .Enumerated, .EnumeratedRandom, .Tested, .EnumeratedTested, .Other],
    by intro x; cases x <;> simp⟩

/-- A value of `fren.evidence` of each kind. -/
def evidenceText : check.EvidenceValue → String
  | .Solver => "solver"
  | .Random => "random"
  | .Enumerated => "enumerated"
  | .EnumeratedRandom => "enumerated+random"
  | .Tested => "tested"
  | .EnumeratedTested => "enumerated+tested"
  | .Other => "guess"

-- The values of `fren.evidence` (`Fren.Core.evidenceOf?`).
impl evidence_value: check::evidence_value for (v : check.EvidenceValue) {
  value := v,
  valid? := (Fren.Core.evidenceOf? (evidenceText v)).isSome,
  random? := ((Fren.Core.evidenceOf? (evidenceText v)).map (·.tested)).getD false,
  enumerated? := ((Fren.Core.evidenceOf? (evidenceText v)).map (·.enumerated)).getD false,
} by
  intro v _
  cases v <;> decide

def toMethod : Method → check.Method
  | .solver => .Solver
  | .testing => .Testing
  | .enumeration => .Enumeration
  | .enumerationThenTesting => .EnumerationThenTesting
  | .skipped => .Skipped

-- How each check is run (`methodOf`).
impl method_of: check::by_evidence for (k : CheckKind) (t e o : Bool) {
  kind := toCheckKind k,
  tested? := t,
  enumerated? := e,
  obligation? := o,
  method := toMethod (methodOf k (Fren.Core.Evidence.mk t e) o),
} by
  intro k t e o _
  cases k <;> cases t <;> cases e <;> cases o <;> decide

instance : Fren.Finite Fren.Core.ProofMethod := ⟨[.solver, .enumerated, .random, .lean], by intro x; cases x <;> simp⟩

def toProofMethod : Fren.Core.ProofMethod → check.ProofMethod
  | .solver => .Solver
  | .enumerated => .Enumerated
  | .random => .Random
  | .lean => .Lean

def toDispatch : Fren.Core.Dispatch → check.Dispatch
  | .run => .Run
  | .bySolver => .BySolver
  | .skip => .Skip
  | .reject => .Reject

def toReason : Fren.Core.Reason → check.Reason
  | .selected => .Selected
  | .noLean => .NoLean
  | .notSettable => .NotSettable
  | .patternType => .SubsetType
  | .noWitnessSearch => .NoWitnessSearch
  | .noValue => .NoValue
  | .notEnumerated => .NotEnumerated

-- What runs each check, under each method (`dispatchOf`).
impl dispatch_of: check::method_run for (k : CheckKind) (i : Fren.Core.CheckedItem) (m : Fren.Core.ProofMethod) (o : Bool) {
  kind := toCheckKind k,
  item := toCheckedItem i,
  method := toProofMethod m,
  obligation? := o,
  dispatch := toDispatch (Fren.Core.dispatchOf k i m o).1,
  reason := toReason (Fren.Core.dispatchOf k i m o).2,
} by
  intro k i m o _
  cases k <;> cases i <;> cases m <;> cases o <;> decide

-- The verdicts of enumeration (`enumeratedVerdict`).
impl enumerated_verdict: check::enumerated_verdict for (k : CheckKind) (v : Verdict) (c x o : Bool) {
  kind := toCheckKind k,
  verdict := toVerdict v,
  conflict? := c,
  exact? := x,
  outputs_exact? := o,
  reported := toVerdict (enumeratedVerdict k v c x o).1,
  bounded? := (enumeratedVerdict k v c x o).2,
} by
  intro k v c x o _
  cases k <;> cases v <;> cases c <;> cases x <;> cases o <;> decide


-- An exhausted shape has no value beyond the bound (`Shape.exhausted`).
open Classical in
impl shape_bound: check::shape_bound for (sh : Shape) (n : Nat) (v : EVal) (k : Nat) {
  exhausted? := sh.exhausted n,
  bound := n,
  value? := decide (SHas sh v k),
  size := k,
} by
  intro sh n v k _ h
  simp only [decide_eq_true_eq] at h
  exact exhausted_within sh n h.1 h.2

-- Trying each part as soon as it can be finds the first choice
-- (`firstChoice`).
open Classical in
impl pruning: check::pruning for (base : Array Nat) (slots lims : List Nat) (parts : List (List Nat × (Array Nat → Bool))) {
  local? := decide (∀ p ∈ parts, Local p),
  distinct? := decide (slots.Nodup ∧ lims.length = slots.length),
  first? := decide (firstChoice base slots lims parts =
    ((lexAll lims).find? fun a => parts.all (·.2 (setAll base slots a))).map (setAll base slots)),
} by
  intro base slots lims parts _ h
  simp only [decide_eq_true_eq] at h ⊢
  exact firstChoice_spec base slots lims parts h.2.1 h.2.2 h.1

-- Every slot that a formula's value depends on is among `EF.slots`.
open Classical in
impl slots_suffice: check::slots_suffice for (sp : Space) (ats : Atoms) (f : EF) (e e' : Array Nat) {
  atoms_local? := decide (∀ k e e', Agree (ats.slots[k]?.getD #[]).toList e e' → ats.eval k e = ats.eval k e'),
  definitions_local? := decide (∀ x e₁ e₂ e₁' e₂', Agree (ats.defSlots x).toList e₁ e₁' →
    Agree (ats.defSlots x).toList e₂ e₂' → ats.sameDefined x e₁ e₂ = ats.sameDefined x e₁' e₂'),
  outputs_distinct? := decide sp.outputs.toList.Nodup,
  agree? := decide (Agree (f.slots sp ats) e e'),
  same_value? := f.eval sp ats e == f.eval sp ats e',
} by
  intro sp ats f e e' _ h
  simp only [decide_eq_true_eq] at h
  simp [eval_local sp ats h.1.1.1 h.1.1.2 h.1.2 e f e' h.2]

/-- The invariant of a space's slots that the fair order rests on. -/
def Ordered (sp : Space) (base : Array Nat) (slots : List Nat) : Prop :=
  slots.Nodup ∧ (∀ s ∈ slots, s < base.size) ∧ SizesOrdered sp slots

-- The fair order (`Space.fairList`): complete, each assignment once, by level.
open Classical in
impl fair_order: check::fair_order for (sp : Space) (base : Array Nat) (slots a : List Nat) (i j : Nat) {
  ordered? := decide (Ordered sp base slots),
  within? := decide (slots ≠ [] ∧ a ∈ lexAll (slots.map (sp.within · sp.bound))),
  earlier? := decide (i < j ∧ j < (sp.fairList base slots).length),
  listed? := decide (a ∈ sp.fairList base slots),
  times := times (sp.fairList base slots) a,
  first_level := (((sp.fairList base slots)[i]?).map (sp.levelOf slots)).getD 0,
  second_level := (((sp.fairList base slots)[j]?).map (sp.levelOf slots)).getD 0,
} by
  intro sp base slots a i j _
  refine ⟨fun ⟨ho, hw⟩ => ?_, fun ho => ?_, fun ⟨ho, he⟩ => ?_⟩
  · simp only [decide_eq_true_eq] at ho hw ⊢
    exact fair_complete sp base slots a hw.1 ho.1 ho.2.1 ho.2.2 hw.2
  · simp only [decide_eq_true_eq] at ho
    rw [times_nodup _ _ (fair_nodup sp base slots ho.1 ho.2.1 ho.2.2)]
    by_cases hm : a ∈ sp.fairList base slots <;> simp [hm]
  · simp only [decide_eq_true_eq] at ho he
    have hs := List.pairwise_iff_getElem.1 (fair_sorted sp base slots ho.1 ho.2.1 ho.2.2) i j (by omega) he.2 he.1
    rw [List.getElem?_eq_getElem (show i < (sp.fairList base slots).length by omega), List.getElem?_eq_getElem he.2]
    simpa using hs

-- The search finds the first assignment of the fair order (`search`).
open Classical in
impl search_first: check::search_first for (sp : Space) (ats : Atoms) (parts : Array EF) {
  local? := decide (∀ p ∈ partsOf sp ats parts, Local p),
  reads? := decide (slotsOf sp ats parts ≠ []),
  first? := decide ((search sp ats parts).map (·.1) =
      ((sp.fairList (Array.replicate sp.names.size 0) (slotsOf sp ats parts)).find? fun a =>
        (partsOf sp ats parts).all (·.2 (setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts) a))).map
        (setAll (Array.replicate sp.names.size 0) (slotsOf sp ats parts))),
} by
  intro sp ats parts _ h
  simp only [decide_eq_true_eq] at h ⊢
  exact search_spec sp ats parts h.1 h.2

/-- What a search found, as the Reqs name it. -/
def toFound (b : Bool) : check.Found := if b then .Model else .NoModel

-- A query's answer, from the search and testing (`answerOf`).
impl enumerated_answer: check::enumerated_answer for (s t testing : Bool) {
  search := toFound s,
  testing? := testing,
  test := toFound t,
  answer := match answerOf (if s then some () else none) testing (fun _ => if t then some () else none) with
    | some _ => check.Outcome.Sat
    | none => check.Outcome.Unsat,
  from_test? := ((answerOf (if s then some () else none) testing (fun _ => if t then some () else none)).map (·.2)).getD false,
} by
  intro s t testing _
  cases s <;> cases t <;> cases testing <;> decide

end Fren.Impls.Enumeration
