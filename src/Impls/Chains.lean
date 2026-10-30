-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Chained comparisons (`Reqs/Lint/Style/Comparisons#chained-comparisons`)

`chainable_comparison`, proved of `chainFlips`, which both front ends call
on each two adjacent conjuncts of a run of `and`, for conjuncts of any
length and operands written any way. -/

namespace Fren.Impls.Chains

open Fren.Core

/-- The operator of a step of the model, in a chain that orders ascending
if `asc`. -/
def opText (asc strict : Bool) : String :=
  if asc then (if strict then "<" else "<=") else (if strict then ">" else ">=")

/-- A conjunct of the model, as the lint reads one, with each operand's
text for the operand. -/
def toPart (c : lint.Chain) : ChainPart String :=
  { operands := (c.first :: c.steps.toList.map (·.operand)).toArray
    ops := (c.steps.toList.map fun s => opText c.«ascending?» s.«strict?»).toArray }

theorem steps_ne (c : lint.Chain) (h : c.steps ≠ ∅) : c.steps.toList ≠ [] := by
  intro e; exact h (Fren.Seq.ext (by simpa using e))

theorem p_opText (a x : Bool) : (fun op : String => op matches "<" | "<=") (opText a x) = a := by
  cases a <;> cases x <;> decide

theorem all_opText (a : Bool) (l : List lint.Step) (hne : l ≠ []) :
    (l.map fun s => opText a s.«strict?»).all (fun op => op matches "<" | "<=") = a := by
  cases a
  · cases l with
    | nil => exact absurd rfl hne
    | cons s ss =>
      have h := p_opText false s.«strict?»
      dsimp only at h
      simp only [List.map_cons, List.all_cons, h, Bool.false_and]
  · rw [List.all_eq_true]; intro op hop
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hop
    have h := p_opText true s.«strict?»
    dsimp only at h
    exact h

theorem nth_last (q : Fren.Seq lint.Step) (h : q.toList ≠ []) : q.nth (q.len - 1) = q.toList.getLast h := by
  have : 0 < q.toList.length := List.length_pos_iff.mpr h
  unfold Fren.Seq.nth
  rw [dif_pos (by simp; omega)]
  rw [List.getLast_eq_getElem]
  congr 1; simp

theorem back_cons (x : String) (l : List lint.Step) (h : l ≠ []) :
    (x :: l.map (·.operand)).toArray.back! = (l.getLast h).operand := by
  rw [Array.back!_eq_back?, List.back?_toArray, List.getLast?_cons, List.getLast?_map, List.getLast?_eq_some_getLast h]
  simp

theorem toPart_ascending (c : lint.Chain) (h : c.steps ≠ ∅) : (toPart c).ascending = c.«ascending?» := by
  simp only [toPart, ChainPart.ascending, List.all_toArray]
  exact all_opText _ _ (steps_ne c h)

theorem toPart_first (c : lint.Chain) : (toPart c).operands[0]! = c.first := by
  simp [toPart]

theorem toPart_last (c : lint.Chain) (h : c.steps ≠ ∅) : (toPart c).operands.back! = lint.last_operand c := by
  simp only [toPart, lint.last_operand, if_neg h, nth_last _ (steps_ne c h)]
  exact back_cons _ _ (steps_ne c h)

theorem toPart_single (c : lint.Chain) : ((toPart c).ops.size == 1) = decide (c.steps.len = 1) := by
  simp only [toPart, List.size_toArray, List.length_map, Fren.Seq.len_eq]
  rw [Bool.eq_iff_iff]; simp; omega

/-! ## A conjunct the other way round -/

theorem reversed_last (c : lint.Chain) : lint.last_operand (lint.reversed c) = c.first := by
  simp [lint.last_operand, Fren.Seq.ext_iff, Fren.Seq.nth]

theorem oriented_eq (c : lint.Chain) (h : c.steps ≠ ∅) (a : Bool) :
    lint.oriented c a = if a then lint.reversed c else c := by
  cases a <;> simp [lint.oriented, h]

-- Both front ends join two conjuncts with `chainFlips`, in `chainableAt`,
-- with `lSingle` where the left is one conjunct that is one comparison.
impl chainable_comparison: lint::chainable_comparison for (l r : lint.Chain) (ls : Bool) {
  left := l,
  right := r,
  «left_single?» := ls,
  «fires?» := (chainFlips id (toPart l) (toPart r) ls).1,
  «flip_left?» := (chainFlips id (toPart l) (toPart r) ls).2.1,
  «flip_right?» := (chainFlips id (toPart l) (toPart r) ls).2.2,
} by
  intro l r ls ⟨⟨hl, hr⟩, hs⟩
  have hcode : chainFlips id (toPart l) (toPart r) ls = chainableComparison l.«ascending?» r.«ascending?» ls
      (decide (r.steps.len = 1)) (lint.last_operand l == r.first) (l.first == lint.last_operand r)
      (l.first == r.first) (lint.last_operand l == lint.last_operand r) := by
    simp only [chainFlips, toPart_ascending l hl, toPart_ascending r hr, toPart_single, toPart_first,
      toPart_last l hl, toPart_last r hr, id]
  rw [hcode]
  unfold lint.chainable_comparison.defs lint.chainable_comparison.def.«fires?» lint.chainable_comparison.def.«flip_left?»
    lint.chainable_comparison.def.«flip_right?»
  simp only [lint.chains_flipped?, oriented_eq l hl, oriented_eq r hr, if_true, if_false,
    Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, true_or, true_and, and_true]
  simp only [lint.chains?, reversed_last]
  clear hcode hs
  have h1 : (lint.last_operand l = r.first) ↔ (lint.last_operand l == r.first) = true := beq_iff_eq.symm
  have h2 : (l.first = lint.last_operand r) ↔ (l.first == lint.last_operand r) = true := beq_iff_eq.symm
  have h3 : (l.first = r.first) ↔ (l.first == r.first) = true := beq_iff_eq.symm
  have h4 : (lint.last_operand l = lint.last_operand r) ↔ (lint.last_operand l == lint.last_operand r) = true :=
    beq_iff_eq.symm
  simp only [ne_eq, h1, h2, h3, h4]
  clear h1 h2 h3 h4
  generalize (lint.last_operand l == r.first) = p1
  generalize (l.first == lint.last_operand r) = p2
  generalize (l.first == r.first) = p3
  generalize (lint.last_operand l == lint.last_operand r) = p4
  generalize l.«ascending?» = A
  generalize r.«ascending?» = B
  by_cases hS : r.steps.len = 1 <;> simp only [hS, decide_true, decide_false] <;> clear hl hr <;>
    revert A B ls p1 p2 p3 p4 <;> decide

end Fren.Impls.Chains
