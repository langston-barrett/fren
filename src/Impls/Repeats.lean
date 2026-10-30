-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Texts written the same as earlier ones (`Reqs/Lint/Suspicious/Expressions`)

`first_same`, `ifs_same_cond` and `duplicate_elements`, proved of
`earlierSame` and `repeatedForms`, which both front ends call on the written forms of a
chain's tests and of a literal's elements, for any number of them. -/

namespace Fren.Impls.Repeats

open Fren.Core

/-- The text at position `i` of `l` is the same as an earlier one. -/
def Rep (l : List String) (i : Nat) : Prop := ∃ h : i < l.length, ∃ j, ∃ hj : j < i, l[j] = l[i]

theorem nth_ofList (l : List String) (i : Int) (h0 : 0 ≤ i) (h : i.toNat < l.length) :
    (Fren.Seq.ofList l).nth i = l[i.toNat] := by
  rw [Fren.Seq.nth_of_lt _ _ h0 (by simp; omega)]; rfl

theorem repeated_iff (l : List String) (k : Int) :
    lint.repeated? (Fren.Seq.ofList l) k = true ↔ 0 ≤ k ∧ Rep l k.toNat := by
  simp only [lint.repeated?, decide_eq_true_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList]
  constructor
  · rintro ⟨⟨h0, hk⟩, j, ⟨hj0, hjk⟩, he⟩
    refine ⟨h0, by omega, j.toNat, by omega, ?_⟩
    rw [nth_ofList l j hj0 (by omega), nth_ofList l k h0 (by omega)] at he
    exact he
  · rintro ⟨h0, hk, j, hj, he⟩
    refine ⟨⟨h0, by omega⟩, (j : Int), ⟨by omega, by omega⟩, ?_⟩
    rw [nth_ofList l j (by omega) (by simp; omega), nth_ofList l k h0 hk]
    simpa using he

theorem mem_repeatedForms (l : List String) (i : Nat) : i ∈ repeatedForms l.toArray ↔ Rep l i := by
  simp only [repeatedForms, Array.mem_filter, Array.mem_range, List.size_toArray, Rep]
  constructor
  · rintro ⟨hi, hc⟩
    rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hc
    obtain ⟨j, hj, he⟩ := hc
    simp only [Array.size_extract, List.size_toArray] at hj
    refine ⟨hi, j, by omega, ?_⟩
    rw [Array.getElem_extract] at he
    simp only [List.getElem_toArray, Nat.zero_add] at he
    rw [he, getElem!_pos l.toArray i (by simpa using hi)]; rfl
  · rintro ⟨hi, j, hj, he⟩
    refine ⟨hi, ?_⟩
    rw [Array.contains_iff_mem, Array.mem_iff_getElem]
    refine ⟨j, by simp; omega, ?_⟩
    rw [Array.getElem_extract]
    simp only [List.getElem_toArray, Nat.zero_add]
    rw [he, getElem!_pos l.toArray i (by simpa using hi)]; rfl

theorem find_range_some (p : Nat → Bool) (i j : Nat) :
    (List.range i).find? p = some j ↔ j < i ∧ p j = true ∧ ∀ j' < j, p j' = false := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.find?_append]
    cases h : (List.range i).find? p with
    | some j0 =>
      simp only [Option.some_or]
      rw [ih j0] at h
      constructor
      · intro e; cases e; exact ⟨by omega, h.2.1, h.2.2⟩
      · rintro ⟨_, hp, hb⟩
        congr
        rcases Nat.lt_trichotomy j0 j with c | c | c
        · exact absurd h.2.1 (by simp [hb j0 c])
        · exact c
        · exact absurd hp (by simp [h.2.2 j c])
    | none =>
      simp only [Option.none_or, List.find?_singleton]
      rw [List.find?_eq_none] at h
      constructor
      · intro e
        split at e
        · cases e
          refine ⟨by omega, by assumption, fun j' hj' => ?_⟩
          simpa using h j' (List.mem_range.mpr hj')
        · cases e
      · rintro ⟨hj, hp, hb⟩
        rcases Nat.lt_or_ge j i with c | c
        · exact absurd hp (by simpa using h j (List.mem_range.mpr c))
        · have : j = i := by omega
          subst this; simp [hp]

theorem find_range_none (p : Nat → Bool) (i : Nat) :
    (List.range i).find? p = none ↔ ∀ j < i, p j = false := by
  rw [List.find?_eq_none]; simp

theorem getElem!_toArray (l : List String) (j : Nat) (h : j < l.length) : l.toArray[j]! = l[j] := by
  rw [getElem!_pos l.toArray j (by simpa using h)]; rfl

/-- `earlierSame` is the first earlier position with the same text. -/
theorem earlierSame_some (l : List String) (i j : Nat) (hi : i < l.length) :
    earlierSame l.toArray i = some j ↔
      ∃ hj : j < i, l[j] = l[i] ∧ ∀ j' (h : j' < j), l[j'] ≠ l[i] := by
  unfold earlierSame
  rw [find_range_some]
  constructor
  · rintro ⟨hj, hp, hb⟩
    rw [getElem!_toArray l j (by omega), getElem!_toArray l i hi, beq_iff_eq] at hp
    refine ⟨hj, hp, fun j' h' e => ?_⟩
    have := hb j' h'
    rw [getElem!_toArray l j' (by omega), getElem!_toArray l i hi, e] at this
    simp at this
  · rintro ⟨hj, he, hb⟩
    refine ⟨hj, ?_, fun j' h' => ?_⟩
    · rw [getElem!_toArray l j (by omega), getElem!_toArray l i hi, he]; simp
    · rw [getElem!_toArray l j' (by omega), getElem!_toArray l i hi]
      simpa using hb j' h'

theorem earlierSame_none (l : List String) (i : Nat) (hi : i < l.length) :
    earlierSame l.toArray i = none ↔ ¬ Rep l i := by
  unfold earlierSame
  rw [find_range_none]
  simp only [Rep, not_exists]
  constructor
  · intro h _ j hj e
    have := h j hj
    rw [getElem!_toArray l j (by omega), getElem!_toArray l i hi, e] at this
    simp at this
  · intro h j hj
    rw [getElem!_toArray l j (by omega), getElem!_toArray l i hi]
    simpa using h hi j hj

/-- The first earlier position written the same as the one at `k`, or `-1`,
as `ifsSameCondAt` computes it with `earlierSame`. -/
def firstSame (ts : List String) (k : Int) : Int :=
  if 0 ≤ k ∧ k.toNat < ts.length then
    (match earlierSame ts.toArray k.toNat with | some j => (j : Int) | none => -1) else -1

/-- `firstSame` meets `lint::first_same`'s guarantees. -/
theorem firstSame_ensures (ts : List String) (k : Int) :
    lint.first_same.ensures (Fren.Seq.ofList ts) k (firstSame ts k) := by
  unfold lint.first_same.ensures lint.first_same.ensure.first lint.first_same.ensure.none firstSame
  rw [repeated_iff]
  by_cases hk : 0 ≤ k ∧ k.toNat < ts.length
  · rw [if_pos hk]
    cases e : earlierSame ts.toArray k.toNat with
    | none =>
      have hr := (earlierSame_none ts k.toNat hk.2).mp e
      exact ⟨fun h => absurd h.2 hr, fun _ => rfl⟩
    | some j =>
      obtain ⟨hj, he, hb⟩ := (earlierSame_some ts k.toNat j hk.2).mp e
      dsimp only
      refine ⟨fun _ => ⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, fun h => absurd ⟨hk.1, hk.2, j, hj, he⟩ h⟩
      · rw [nth_ofList ts j (by omega) (by simp; omega), nth_ofList ts k hk.1 hk.2]; simpa using he
      · intro j' ⟨h0, h1⟩
        rw [nth_ofList ts j' h0 (by omega), nth_ofList ts k hk.1 hk.2]
        exact hb j'.toNat (by omega)
  · rw [if_neg hk]
    exact ⟨fun ⟨h0, hl, _⟩ => absurd ⟨h0, hl⟩ hk, fun _ => rfl⟩

impl first_same: lint::first_same for (ts : List String) (k : Int) {
  forms := Fren.Seq.ofList ts,
  k := k,
  earlier := firstSame ts k,
} by
  intro ts k _
  exact firstSame_ensures ts k

-- Both front ends decide `ifs_same_cond` with `earlierSame`, in
-- `ifsSameCondAt`, of the written forms of the chain's tests.
impl ifs_same_cond: lint::ifs_same_cond for (ts : List String) (k : Int) {
  tests := Fren.Seq.ofList ts,
  k := k,
  «fires?» := decide (0 ≤ k ∧ k.toNat < ts.length) && (earlierSame ts.toArray k.toNat).isSome,
  earlier := firstSame ts k,
} by
  intro ts k _
  refine ⟨Fren.Seq.ofList ts, k, firstSame ts k, ⟨?_, rfl⟩, ?_⟩
  · unfold lint.ifs_same_cond.ensure.rule
    rw [repeated_iff]
    by_cases hk : 0 ≤ k ∧ k.toNat < ts.length
    · rw [decide_eq_true hk, Bool.true_and, Option.isSome_iff_ne_none, ne_eq,
        earlierSame_none ts k.toNat hk.2, Classical.not_not]
      exact ⟨fun h => ⟨hk.1, h⟩, fun h => h.2⟩
    · rw [decide_eq_false hk, Bool.false_and]
      exact ⟨fun h => absurd h (by simp), fun ⟨h0, hl, _⟩ => absurd ⟨h0, hl⟩ hk⟩
  · exact ⟨⟨rfl, rfl⟩, trivial, firstSame_ensures ts k⟩

-- Both front ends decide `duplicate_elements` with `repeatedForms`, through
-- `repeatedElements`, of the written forms of the literal's elements.
impl duplicate_elements: lint::duplicate_elements for (ts : List String) (k : Int) {
  elements := Fren.Seq.ofList ts,
  k := k,
  «fires?» := duplicateElements (repeatedForms ts.toArray).size,
  «repeat?» := decide (0 ≤ k) && (repeatedForms ts.toArray).contains k.toNat,
} by
  intro ts k _
  unfold lint.duplicate_elements.ensures lint.duplicate_elements.ensure.rule lint.duplicate_elements.ensure.removed
  have R := repeated_iff ts
  simp only [lint.repeated?, decide_eq_true_eq] at R
  refine ⟨?_, ?_⟩
  · simp only [duplicateElements, decide_eq_true_eq, gt_iff_lt]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := Array.exists_mem_of_size_pos h
      have := (mem_repeatedForms ts i).mp hi
      have hR := (R i).mpr ⟨by omega, by simpa using this⟩
      exact ⟨i, hR.1, hR⟩
    · rintro ⟨i, _, hi⟩
      obtain ⟨_, hr⟩ := (R i).mp hi
      exact Array.size_pos_of_mem ((mem_repeatedForms ts i.toNat).mpr hr)
  · rw [repeated_iff, Bool.and_eq_true, decide_eq_true_iff, Array.contains_iff_mem, mem_repeatedForms]

end Fren.Impls.Repeats
