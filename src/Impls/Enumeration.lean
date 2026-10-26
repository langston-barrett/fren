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

/-! ## The links -/

open Classical in
-- Each value of a shape of size at most the bound is listed once, and
-- nothing else is (\`Shape.vals\`).
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

-- Smallest first (\`Shape.ordered\`).
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

-- The sizes that \`Shape.vals\` gives its values.
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
  ⟨[.Solver, .Tested, .Enumerated, .EnumeratedTested, .Other], by intro x; cases x <;> simp⟩

/-- A value of \`fren.evidence\` of each kind. -/
def evidenceText : check.EvidenceValue → String
  | .Solver => "solver"
  | .Tested => "tested"
  | .Enumerated => "enumerated"
  | .EnumeratedTested => "enumerated+tested"
  | .Other => "guess"

-- The values of \`fren.evidence\` (\`Fren.Core.evidenceOf?\`).
impl evidence_value: check::evidence_value for (v : check.EvidenceValue) {
  value := v,
  valid? := (Fren.Core.evidenceOf? (evidenceText v)).isSome,
  tested? := ((Fren.Core.evidenceOf? (evidenceText v)).map (·.tested)).getD false,
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

-- How each check is run (\`methodOf\`).
impl method_of: check::by_evidence for (k : CheckKind) (t e : Bool) {
  kind := toCheckKind k,
  tested? := t,
  enumerated? := e,
  method := toMethod (methodOf k (Fren.Core.Evidence.mk t e)),
} by
  intro k t e _
  cases k <;> cases t <;> cases e <;> decide

-- The verdicts of enumeration (\`enumeratedVerdict\`).
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

def toTestOutcome : Option Verdict → check.TestOutcome
  | none => .NotTested
  | some .pass => .TestPassed
  | some .fail => .TestFailed
  | some .inconclusive => .TestInconclusive

-- Enumeration then testing (\`combinedVerdict\`).
impl combined_evidence: check::combined_evidence for (v : Verdict) (b : Bool) (t : Option Verdict) {
  enumerated := toVerdict v,
  bounded? := b,
  test := toTestOutcome t,
  verdict := toVerdict (combinedVerdict v b t).1,
  testing? := (combinedVerdict v b t).2,
} by
  intro v b t _
  cases v <;> cases b <;> rcases t with _ | ⟨_ | _ | _⟩ <;> decide

end Fren.Impls.Enumeration
