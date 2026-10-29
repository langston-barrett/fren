-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Unused assumptions (`Reqs/Lint/Unused#unused-assumptions`)

`unused_assumption`, proved of the functions that both front ends call:
`usedAssumptions`, which finds the assumptions that a set of links
reaches, and `unusedAssumption`, in the two steps that the front ends take,
for any number of assumptions and links. -/

namespace Fren.Impls.Assumptions

open Fren.Core

/-! ## Reaching assumptions -/

section
variable {α : Type}

/-- The assumption at position `i` is reached from the links `u`: it links
one of them, or shares a link with one reached. -/
inductive Reach (ms : List (List α)) (u : List α) : Nat → Prop
  | base {i : Nat} (h : i < ms.length) (x : α) (hx : x ∈ ms.getD i []) (hu : x ∈ u) : Reach ms u i
  | step {i j : Nat} (hj : Reach ms u j) (h : i < ms.length) (x : α) (hx : x ∈ ms.getD i [])
      (hxj : x ∈ ms.getD j []) : Reach ms u i

theorem Reach.lt {ms : List (List α)} {u : List α} {i : Nat} : Reach ms u i → i < ms.length
  | .base h .. => h
  | .step _ h .. => h

variable [DecidableEq α]

/-- A list of distinct positions below `n`, at least `n` of them, has each. -/
theorem mem_of_nodup (out : List Nat) (n : Nat) (hnd : out.Nodup) (hb : ∀ i ∈ out, i < n)
    (hl : n ≤ out.length) (k : Nat) (hk : k < n) : k ∈ out := by
  refine Decidable.byContradiction fun hko => ?_
  have hsub : ∀ x ∈ out, x ∈ (List.range n).erase k := fun x hx => by
    rw [(List.nodup_range).mem_erase_iff]
    exact ⟨fun e => hko (e ▸ hx), List.mem_range.mpr (hb x hx)⟩
  have := Fren.FinSet.length_le_of_nodup hnd hsub
  rw [List.length_erase_of_mem (List.mem_range.mpr hk), List.length_range] at this
  omega

theorem markUsed_spec (ms : List (List α)) (u : List α) :
    ∀ fuel used out,
      (∀ i ∈ out, Reach ms u i) →
      (∀ x, x ∈ used ↔ x ∈ u ∨ ∃ i ∈ out, x ∈ ms.getD i []) →
      out.Nodup → (∀ i ∈ out, i < ms.length) → ms.length ≤ fuel + out.length →
      ∀ i, i ∈ markUsed ms fuel used out ↔ Reach ms u i := by
  intro fuel
  induction fuel with
  | zero =>
    intro used out hr _ hnd hb hl i
    simp only [markUsed]
    exact ⟨hr i, fun h => mem_of_nodup out ms.length hnd hb (by omega) i h.lt⟩
  | succ fuel ih =>
    intro used out hr hu hnd hb hl i
    simp only [markUsed]
    split
    · rename_i hnone
      refine ⟨hr i, fun h => ?_⟩
      have closed : ∀ j, j < ms.length → j ∉ out → ∀ x ∈ ms.getD j [], x ∉ used := by
        intro j hj hjo x hx hxu
        have := List.find?_eq_none.mp hnone j (List.mem_range.mpr hj)
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, List.any_eq_true,
          not_and] at this
        have h1 : (out.contains j) = false := by simpa using hjo
        exact absurd (this h1) (by simp; exact ⟨x, hx, hxu⟩)
      induction h with
      | base hi x hx hxu =>
        exact Decidable.byContradiction fun hio => closed _ hi hio x hx ((hu x).mpr (Or.inl hxu))
      | step _ hi x hx hxj ihj =>
        exact Decidable.byContradiction fun hio => closed _ hi hio x hx ((hu x).mpr (Or.inr ⟨_, ihj, hxj⟩))
    · rename_i i0 hsome
      have hmem := List.mem_of_find?_eq_some hsome
      have hp := List.find?_some hsome
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.contains_iff_mem] at hp
      obtain ⟨hno, x, hx, hxu⟩ := hp
      have hi0 : i0 < ms.length := List.mem_range.mp hmem
      have hno' : i0 ∉ out := by simpa using hno
      refine ih (used ++ ms.getD i0 []) (i0 :: out) ?_ ?_ ?_ ?_ ?_ i
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · rcases (hu x).mp hxu with h | ⟨k, hk, hxk⟩
          · exact .base hi0 x hx h
          · exact .step (hr k hk) hi0 x hx hxk
        · exact hr j hj
      · intro y
        simp only [List.mem_append, hu, List.mem_cons]
        constructor
        · rintro ((h | ⟨k, hk, hy⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨k, Or.inr hk, hy⟩
          · exact Or.inr ⟨i0, Or.inl rfl, h⟩
        · rintro (h | ⟨k, rfl | hk, hy⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr hy
          · exact Or.inl (Or.inr ⟨k, hk, hy⟩)
      · exact List.nodup_cons.mpr ⟨hno', hnd⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi0
        · exact hb j hj
      · simp only [List.length_cons]; omega

theorem mem_markUsed (ms : List (List α)) (u : List α) (i : Nat) :
    i ∈ markUsed ms ms.length u [] ↔ Reach ms u i :=
  markUsed_spec ms u ms.length u [] (by simp) (by simp) List.nodup_nil (by simp) (by simp) i

theorem usedAssumptions_iff (ms : List (List α)) (u : List α) (i : Nat) :
    (usedAssumptions (ms.map List.toArray).toArray u.toArray)[i]?.getD false = true ↔ Reach ms u i := by
  have hm : ((ms.map List.toArray).toArray.toList.map (·.toList)) = ms := by
    simp [Function.comp_def]
  unfold usedAssumptions
  simp only [hm]
  by_cases hi : i < ms.length
  · simp [hi, mem_markUsed]
  · have : (List.range ms.length)[i]? = none := List.getElem?_eq_none (by simpa using hi)
    simp only [Array.getElem?_map, List.getElem?_toArray, this, Option.map_none, Option.getD_none,
      Bool.false_eq_true, false_iff]
    intro h; exact hi h.lt

omit [DecidableEq α] in
theorem not_reach_nil (ms : List (List α)) (i : Nat) : ¬ Reach ms [] i := by
  intro h
  induction h with
  | base _ _ _ hu => simp at hu
  | step _ _ _ _ _ ih => exact ih

end

/-! ## The model's assumptions -/

theorem lt_of_mem_getD {β : Type} {ls : List (List β)} {n : Nat} {x : β} (h : x ∈ ls.getD n []) : n < ls.length := by
  rcases Nat.lt_or_ge n ls.length with hl | hl
  · exact hl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at h; simp at h

/-- The model's relation of positions to links, from each assumption's
links, in order. -/
def linkPairs (ls : List (List lint.Link)) : List (Int × lint.Link) :=
  (List.range ls.length).flatMap fun i => (ls.getD i []).map fun x => ((i : Int), x)

theorem mem_linkPairs (ls : List (List lint.Link)) (i : Int) (x : lint.Link) :
    (i, x) ∈ linkPairs ls ↔ 0 ≤ i ∧ x ∈ ls.getD i.toNat [] := by
  simp only [linkPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨n, _, y, hy, rfl, rfl⟩; exact ⟨by omega, by simpa using hy⟩
  · rintro ⟨h0, hx⟩
    exact ⟨i.toNat, lt_of_mem_getD hx, x, hx, by omega, rfl⟩

/-- The model's `reached` is the assumptions that `Reach` reaches. -/
theorem mem_reached (ls : List (List lint.Link)) (u : List lint.Link) (k : Int) :
    k ∈ lint.reached (Fren.FinSet.ofList (linkPairs ls)) (Fren.FinSet.ofList u) ↔ 0 ≤ k ∧ Reach ls u k.toNat := by
  unfold lint.reached
  simp only [Fren.FinSet.mem_union, Fren.FinSet.mem_image, Fren.FinSet.mem_inverse, Fren.FinSet.mem_closure,
    Fren.FinSet.mem_join, Fren.FinSet.mem_ofList, mem_linkPairs]
  constructor
  · rintro (⟨x, hxu, h0, hx⟩ | ⟨d, ⟨x, hxu, hd0, hdx⟩, ht⟩)
    · exact ⟨h0, .base (lt_of_mem_getD hx) x hx hxu⟩
    · have hd : Reach ls u d.toNat := .base (lt_of_mem_getD hdx) x hdx hxu
      induction ht with
      | single h =>
        obtain ⟨y, ⟨_, hy1⟩, ⟨hb0, hy2⟩⟩ := h
        exact ⟨hb0, .step hd (lt_of_mem_getD hy2) y hy2 hy1⟩
      | tail _ h ih =>
        obtain ⟨y, ⟨_, hy1⟩, ⟨hc0, hy2⟩⟩ := h
        obtain ⟨_, hb⟩ := ih
        exact ⟨hc0, .step hb (lt_of_mem_getD hy2) y hy2 hy1⟩
  · rintro ⟨h0, h⟩
    have key : ∀ n, Reach ls u n → (∃ x, x ∈ u ∧ x ∈ ls.getD n []) ∨
        ∃ d : Int, (∃ x, x ∈ u ∧ 0 ≤ d ∧ x ∈ ls.getD d.toNat []) ∧
          Relation.TransGen (fun a b => ∃ y, (0 ≤ a ∧ y ∈ ls.getD a.toNat []) ∧ 0 ≤ b ∧ y ∈ ls.getD b.toNat [])
            d (n : Int) := by
      intro n hn
      induction hn with
      | base _ x hx hu => exact Or.inl ⟨x, hu, hx⟩
      | step _ _ x hx hxj ih =>
        rename_i i j _ _
        right
        rcases ih with ⟨y, hyu, hy⟩ | ⟨d, hd, ht⟩
        · exact ⟨j, ⟨y, hyu, by omega, by simpa using hy⟩, .single ⟨x, ⟨by omega, by simpa using hxj⟩, by omega, by simpa using hx⟩⟩
        · exact ⟨d, hd, .tail ht ⟨x, ⟨by omega, by simpa using hxj⟩, by omega, by simpa using hx⟩⟩
    rcases key _ h with ⟨x, hxu, hx⟩ | ⟨d, hd, ht⟩
    · exact Or.inl ⟨x, hxu, h0, hx⟩
    · right
      refine ⟨d, hd, ?_⟩
      rw [show k = ((k.toNat : Nat) : Int) by omega]
      exact ht

/-! ## The two steps -/

def isVar : lint.Link → Bool
  | .Var _ => true
  | .Fn _ => false

/-- The variables that the assumption at position `i` mentions. -/
def varsOf (ls : List (List lint.Link)) (i : Nat) : List lint.Link := (ls.getD i []).filter isVar

/-- The assumptions that the first step records, where the front ends
elaborate the procedure (`lintCompUnused`): those that mention variables,
all of them inputs, and that what the procedure's members mention does
not reach. It, and `reported` below, mirror the front ends' two steps by
hand, calling the same `usedAssumptions` and `unusedAssumption` that
`lintCompUnused` and `unusedAssumptionReports` call; the records' names,
spans and messages are left out. -/
def recorded (ls : List (List lint.Link)) (ins ms : List lint.Link) : List Nat :=
  (List.range ls.length).filter fun i =>
    unusedAssumption (varsOf ls i).length ((varsOf ls i).all ins.contains)
      ((usedAssumptions (ls.map List.toArray).toArray ms.toArray)[i]?.getD false) false

/-- Whether the second step reports the assumption at `k`, at the end of
the file (`unusedAssumptionReports`): it is recorded, and the inputs that
the file reads, if it reads them, do not reach it among those recorded. -/
def reported (ls : List (List lint.Link)) (ins ms : List lint.Link) (rd : Bool) (k : Nat) : Bool :=
  let rs := recorded ls ins ms
  rs.contains k &&
    unusedAssumption 1 true false
      ((usedAssumptions (rs.map fun i => (ls.getD i []).toArray).toArray (if rd then ins else []).toArray)[rs.idxOf k]?.getD
        false)

theorem mem_recorded (ls : List (List lint.Link)) (ins ms : List lint.Link) (k : Nat) :
    k ∈ recorded ls ins ms ↔ k < ls.length ∧ (∃ x, lint.Link.Var x ∈ ls.getD k []) ∧
      (∀ x, lint.Link.Var x ∈ ls.getD k [] → lint.Link.Var x ∈ ins) ∧ ¬ Reach ls ms k := by
  have hu := usedAssumptions_iff ls ms k
  simp only [recorded, List.mem_filter, List.mem_range, unusedAssumption, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.not_false]
  rw [show ((usedAssumptions (ls.map List.toArray).toArray ms.toArray)[k]?.getD false = false) ↔ ¬ Reach ls ms k by
    rw [← hu]; simp]
  have hv : (varsOf ls k).length > 0 ↔ ∃ x, lint.Link.Var x ∈ ls.getD k [] := by
    simp only [varsOf, gt_iff_lt, List.length_pos_iff_exists_mem, List.mem_filter]
    constructor
    · rintro ⟨y, hy, hv⟩; cases y with
      | Var x => exact ⟨x, hy⟩
      | Fn _ => simp [isVar] at hv
    · rintro ⟨x, hx⟩; exact ⟨_, hx, rfl⟩
  have ha : (varsOf ls k).all ins.contains = true ↔ ∀ x, lint.Link.Var x ∈ ls.getD k [] → lint.Link.Var x ∈ ins := by
    simp only [varsOf, List.all_eq_true, List.mem_filter, List.contains_iff_mem, and_imp]
    constructor
    · intro h x hx; exact h _ hx rfl
    · intro h y hy hv; cases y with
      | Var x => exact h x hy
      | Fn _ => simp [isVar] at hv
  rw [hv, ha]
  constructor
  · rintro ⟨hk, ⟨⟨a, b⟩, c⟩, _⟩; exact ⟨hk, a, b, c⟩
  · rintro ⟨hk, a, b, c⟩; exact ⟨hk, ⟨⟨a, b⟩, c⟩, trivial⟩

theorem getElem?_idxOf {l : List Nat} {k : Nat} (h : k ∈ l) : l[l.idxOf k]? = some k := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.idxOf_cons]
    by_cases e : a = k
    · subst e; simp
    · have hk : k ∈ l := by simpa [Ne.symm e] using h
      have hb : (a == k) = false := by simpa using e
      rw [hb, cond_false, List.getElem?_cons_succ]
      exact ih hk

theorem reported_iff (ls : List (List lint.Link)) (ins ms : List lint.Link) (rd : Bool) (k : Nat) :
    reported ls ins ms rd k = true ↔ k < ls.length ∧ (∃ x, lint.Link.Var x ∈ ls.getD k []) ∧
      (∀ x, lint.Link.Var x ∈ ls.getD k [] → lint.Link.Var x ∈ ins) ∧
      ¬ Reach ls (ms ++ if rd then ins else []) k := by
  have hrec := mem_recorded ls ins ms k
  simp only [reported, Bool.and_eq_true, List.contains_iff_mem, unusedAssumption, decide_eq_true_eq,
    Bool.not_eq_true', Bool.not_false, true_and, Nat.one_pos, gt_iff_lt]
  rw [hrec]
  cases rd with
  | false =>
    simp only [Bool.false_eq_true, if_false, List.append_nil]
    have : (usedAssumptions ((recorded ls ins ms).map fun i => (ls.getD i []).toArray).toArray
        ([] : List lint.Link).toArray)[(recorded ls ins ms).idxOf k]?.getD false = false := by
      have h := usedAssumptions_iff ((recorded ls ins ms).map fun i => ls.getD i []) [] ((recorded ls ins ms).idxOf k)
      simp only [List.map_map, Function.comp_def] at h
      cases e : (usedAssumptions ((recorded ls ins ms).map fun i => (ls.getD i []).toArray).toArray
        ([] : List lint.Link).toArray)[(recorded ls ins ms).idxOf k]?.getD false
      · rfl
      · exact absurd (h.mp e) (not_reach_nil _ _)
    simp only [this, and_true]
  | true =>
    simp only [if_true]
    constructor
    · rintro ⟨hr, hnot⟩
      exfalso
      have hmem : k ∈ recorded ls ins ms := (mem_recorded ls ins ms k).mpr hr
      obtain ⟨_, ⟨x, hx⟩, hin, _⟩ := hr
      have hidx : (recorded ls ins ms).idxOf k < (recorded ls ins ms).length := List.idxOf_lt_length_iff.mpr hmem
      have hget : ((recorded ls ins ms).map fun i => ls.getD i []).getD ((recorded ls ins ms).idxOf k) [] = ls.getD k [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, getElem?_idxOf hmem]
        simp
      have h := (usedAssumptions_iff ((recorded ls ins ms).map fun i => ls.getD i []) ins ((recorded ls ins ms).idxOf k)).mpr
        (.base (by simpa using hidx) _ (hget ▸ hx) (hin x hx))
      simp only [List.map_map, Function.comp_def] at h
      rw [h] at hnot; exact absurd hnot (by simp)
    · rintro ⟨_, ⟨x, hx⟩, hin, hnr⟩
      exfalso; exact hnr (.base (lt_of_mem_getD hx) _ hx (List.mem_append_right _ (hin x hx)))

theorem union_ofList (ms ins : List lint.Link) (rd : Bool) :
    Fren.FinSet.ofList ms ∪ (if rd = true then Fren.FinSet.ofList ins else ∅) =
      Fren.FinSet.ofList (ms ++ if rd then ins else []) := by
  apply Fren.FinSet.ext
  intro x
  cases rd <;> simp [Fren.FinSet.mem_union, Fren.FinSet.mem_ofList]

/-- The file's uses of a procedure read its inputs exactly where one is a
call. -/
theorem reads_inputs_iff (us : List lint.ProcUse) :
    lint.reads_inputs? (Fren.FinSet.ofList us) = true ↔ us.contains .Call = true := by
  simp only [List.contains_iff_mem]
  simp only [lint.reads_inputs?, lint.checks_assumptions?, fren_spec, Fren.FinSet.mem_ofList]
  simp

-- Both front ends decide in the two steps of `recorded` and `reported`:
-- `lintCompUnused`, where they elaborate the procedure, and
-- `unusedAssumptionReports` at the end of the file, each with
-- `usedAssumptions` and `unusedAssumption`, for every list of assumptions.
-- The file reads the inputs where it calls the procedure: both front ends
-- add reads at calls only, not at `refines` claims.
impl unused_assumption: lint::unused_assumption
    for (ls : List (List lint.Link)) (ins ms : List lint.Link) (us : List lint.ProcUse) (k : Int) {
  links := Fren.FinSet.ofList (linkPairs ls),
  inputs := Fren.FinSet.ofList ins,
  mentioned := Fren.FinSet.ofList ms,
  uses := Fren.FinSet.ofList us,
  k := k,
  «fires?» := decide (0 ≤ k) && reported ls ins ms (us.contains .Call) k.toNat,
} by
  intro ls ins ms us k _
  unfold lint.unused_assumption.ensures lint.unused_assumption.ensure.rule
  have hr : (lint.reads_inputs? (Fren.FinSet.ofList us) = true) ↔ (us.contains .Call = true) := reads_inputs_iff us
  simp only [hr]
  rw [Bool.and_eq_true, decide_eq_true_iff, reported_iff, union_ofList, mem_reached]
  simp only [Fren.FinSet.mem_ofList, mem_linkPairs]
  constructor
  · rintro ⟨h0, _, ⟨x, hx⟩, hin, hnr⟩
    exact ⟨⟨⟨x, h0, hx⟩, fun y ⟨_, hy⟩ => hin y hy⟩, fun ⟨_, h⟩ => hnr h⟩
  · rintro ⟨⟨⟨x, h0, hx⟩, hin⟩, hnr⟩
    exact ⟨h0, lt_of_mem_getD hx, ⟨x, hx⟩, fun y hy => hin y ⟨h0, hy⟩, fun h => hnr ⟨h0, h⟩⟩

end Fren.Impls.Assumptions
