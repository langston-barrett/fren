-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Chained comparisons (`Reqs/Lint/Style/Comparisons#chained-comparisons`)

`chainable_comparison`, proved of `chainFlips`, which both front ends call
on each two adjacent conjuncts of a run of `and`, for conjuncts of any
length and operands written any way, and `chainable_joined`, proved of
`ChainPart.join`, which writes the chain of two. Each conjunct that the
code reads is `toPart` of a `lint.Chain`, with its operands as written:
`chainPart?`'s, by `chainPart?_toPart`, and a join's, by `map_join` and `join_toPart`. -/

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

theorem p_opText (a x : Bool) : ascendingOp (opText a x) = a := by
  cases a <;> cases x <;> decide

theorem all_opText (a : Bool) (l : List lint.Step) (hne : l ≠ []) :
    (l.map fun s => opText a s.«strict?»).all ascendingOp = a := by
  cases a
  · cases l with
    | nil => exact absurd rfl hne
    | cons s ss =>
      have h := p_opText false s.«strict?»
      simp only [List.map_cons, List.all_cons, h, Bool.false_and]
  · rw [List.all_eq_true]; intro op hop
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hop
    exact p_opText true s.«strict?»

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

/-- Whether `op` is a strict operator, `<` or `>`. -/
def strictOp (op : String) : Bool := op == "<" || op == ">"

/-- A conjunct of the code as one of the model, given its operands' texts:
its first operand, whether it orders ascending, and each operator, strict
or not, with the operand after it. -/
def fromPart (p : ChainPart String) : lint.Chain :=
  { first := p.operands[0]!
    «ascending?» := p.ascending
    steps := Fren.Seq.ofList ((p.ops.toList.zip (p.operands.toList.drop 1)).map fun (op, x) =>
      { «strict?» := strictOp op, operand := x }) }

theorem strict_opText (a x : Bool) : strictOp (opText a x) = x := by
  cases a <;> cases x <;> decide

theorem fromPart_toPart (c : lint.Chain) (h : c.steps ≠ ∅) : fromPart (toPart c) = c := by
  have ha := toPart_ascending c h
  rcases c with ⟨first, asc, steps⟩
  · simp only [fromPart, ha, toPart_first]
    congr 1
    apply Fren.Seq.ext
    simp only [toPart, List.toList_toArray, List.drop_succ_cons, List.drop_zero, Fren.Seq.toList_ofList]
    rw [List.zip_map', List.map_map]
    conv => rhs; rw [← List.map_id steps.toList]
    apply List.map_congr_left; intro s _
    simp [strict_opText]

/-! ## Each conjunct the code reads is one of the model -/

theorem opText_asc (op : String) (h : ascendingOp op = true) :
    opText true (strictOp op) = op := by
  revert h; unfold ascendingOp; split <;> intro h <;> first | rfl | simp at h | decide

theorem opText_desc (op : String) (h : descendingOp op = true) :
    opText false (strictOp op) = op := by
  revert h; unfold descendingOp; split <;> intro h <;> first | rfl | simp at h | decide

theorem ops_round (l : List String)
    (ho : l.all ascendingOp = true ∨ l.all descendingOp = true) :
    l.map (fun op => opText (l.all ascendingOp) (strictOp op)) = l := by
  by_cases ha : l.all ascendingOp = true
  · rw [ha]
    conv => rhs; rw [← List.map_id l]
    apply List.map_congr_left; intro op hop
    exact opText_asc op (List.all_eq_true.mp ha op hop)
  · have hd : l.all descendingOp = true := by simpa [ha] using ho
    rw [Bool.not_eq_true] at ha; rw [ha]
    conv => rhs; rw [← List.map_id l]
    apply List.map_congr_left; intro op hop
    exact opText_desc op (List.all_eq_true.mp hd op hop)

theorem map_zip_fst (f : String → β) (O L : List String) (h : O.length ≤ L.length) :
    (O.zip L).map (fun q => f q.1) = O.map f := by
  conv => rhs; rw [← List.map_fst_zip (l₁ := O) (l₂ := L) h]
  rw [List.map_map]; rfl

theorem map_zip_opText (A : Bool) (O L : List String) (h : O.length ≤ L.length) :
    (O.zip L).map (fun q => opText A (strictOp q.1)) = O.map (fun op => opText A (strictOp op)) :=
  map_zip_fst (fun op => opText A (strictOp op)) O L h

/-- A conjunct whose operators order one way, with one more operand than
operators, is `toPart` of the model's chain of it. -/
theorem toPart_fromPart (p : ChainPart String) (hs : p.operands.size = p.ops.size + 1)
    (ho : orderingOps p.ops = true) : toPart (fromPart p) = p := by
  obtain ⟨operands, ops⟩ := p
  simp only at hs
  simp only [orderingOps, Bool.and_eq_true, Bool.or_eq_true] at ho
  obtain ⟨_, ho⟩ := ho
  rcases operands with ⟨L⟩
  rcases ops with ⟨O⟩
  simp only [List.size_toArray] at hs
  cases L with
  | nil => simp at hs
  | cons x L =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hs
    have hz1 : (O.zip L).map Prod.snd = L := List.map_snd_zip (by omega)
    have hz2 : (O.zip L).map Prod.fst = O := List.map_fst_zip (by omega)
    simp only [toPart, fromPart, ChainPart.ascending, List.all_toArray, Fren.Seq.toList_ofList,
      List.drop_succ_cons, List.drop_zero, List.map_map]
    change O.toArray.all _ = true ∨ O.toArray.all _ = true at ho
    simp only [List.all_toArray] at ho
    simp only [Function.comp_def]
    rw [map_zip_opText _ O L (by omega), ops_round O ho]
    have e1 : List.map (fun (q : String × String) => q.snd) (O.zip L) = L := hz1
    simp [e1]

/-- A conjunct of the code whose operators order one way, with one more
operand than operators, is `toPart` of a chain of the model. -/
theorem toPart_of (q : ChainPart String) (hs : q.operands.size = q.ops.size + 1)
    (ho : orderingOps q.ops = true) : ∃ c : lint.Chain, c.steps ≠ ∅ ∧ q = toPart c := by
  refine ⟨fromPart q, ?_, (toPart_fromPart q hs ho).symm⟩
  intro e
  have h := congrArg ChainPart.ops (toPart_fromPart q hs ho)
  simp only [toPart, e, Fren.Seq.toList_empty, List.map_nil] at h
  simp [orderingOps, ← h] at ho

theorem chainPart?_wf (n : BNode α) (p : ChainPart (BNode α)) (h : chainPart? n = some p) :
    p.operands.size = p.ops.size + 1 ∧ orderingOps p.ops = true := by
  unfold chainPart? at h
  split at h
  · split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨by simp [hc.2], hc.1⟩
    · simp at h
  · split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.2.symm, hc.1⟩
    · simp at h
  · simp at h

/-- Each conjunct that `chainPart?` reads, with its operands as written, is
`toPart` of a chain of the model. -/
theorem chainPart?_toPart (form : BNode α → String) (n : BNode α) (p : ChainPart (BNode α))
    (h : chainPart? n = some p) : ∃ c : lint.Chain, c.steps ≠ ∅ ∧ p.map form = toPart c := by
  obtain ⟨hs, ho⟩ := chainPart?_wf n p h
  exact toPart_of (p.map form) (by simpa [ChainPart.map] using hs) (by simpa [ChainPart.map] using ho)

/-- The join of two conjuncts, with their operands as written, is the join
of the conjuncts as written. -/
theorem map_join (f : σ → τ) (l r : ChainPart σ) (fl fr : Bool) :
    (l.join r fl fr).map f = (l.map f).join (r.map f) fl fr := by
  cases fl <;> cases fr <;>
    simp [ChainPart.join, ChainPart.map, ChainPart.flip, Array.map_append, Array.map_reverse, Array.map_extract]

/-! ## A conjunct the other way round -/

theorem reversed_last (c : lint.Chain) : lint.last_operand (lint.reversed c) = c.first := by
  simp [lint.last_operand, Fren.Seq.ext_iff, Fren.Seq.nth]

theorem oriented_eq (c : lint.Chain) (h : c.steps ≠ ∅) (a : Bool) :
    lint.oriented c a = if a then lint.reversed c else c := by
  cases a <;> simp [lint.oriented, h]

-- Both front ends join two conjuncts with `chainFlips`, in `chainableAt`,
-- on their operands as written.
impl chainable_comparison: lint::chainable_comparison for (l r : lint.Chain) {
  left := l,
  right := r,
  «fires?» := (chainFlips (toPart l) (toPart r)).1,
  «flip_left?» := (chainFlips (toPart l) (toPart r)).2.1,
  «flip_right?» := (chainFlips (toPart l) (toPart r)).2.2,
} by
  intro l r ⟨hl, hr⟩
  have hcode : chainFlips (toPart l) (toPart r) = chainableComparison l.«ascending?» r.«ascending?»
      (decide (l.steps.len = 1)) (decide (r.steps.len = 1)) (lint.last_operand l == r.first)
      (l.first == lint.last_operand r) (l.first == r.first) (lint.last_operand l == lint.last_operand r) := by
    simp only [chainFlips, toPart_ascending l hl, toPart_ascending r hr, toPart_single, toPart_first,
      toPart_last l hl, toPart_last r hr]
  rw [hcode]
  unfold lint.chainable_comparison.defs lint.chainable_comparison.def.«fires?» lint.chainable_comparison.def.«flip_left?»
    lint.chainable_comparison.def.«flip_right?»
  simp only [lint.chains_flipped?, oriented_eq l hl, oriented_eq r hr, if_true, if_false,
    Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, true_or, true_and, and_true]
  simp only [lint.chains?, reversed_last]
  clear hcode
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
  by_cases hL : l.steps.len = 1 <;> by_cases hS : r.steps.len = 1 <;>
    simp only [hL, hS, decide_true, decide_false] <;> clear hl hr <;>
    revert A B p1 p2 p3 p4 <;> decide

/-! ## The chain of two conjuncts -/

theorem single_steps (c : lint.Chain) (h : c.steps.len = 1) : ∃ s, c.steps.toList = [s] := by
  simp only [Fren.Seq.len_eq] at h
  exact List.length_eq_one_iff.mp (by omega)

theorem mirror_opText (a x : Bool) :
    ((Comparison.ofOp? (opText a x)).map (·.mirror.op)).getD (opText a x) = opText (!a) x := by
  cases a <;> cases x <;> rfl

theorem flip_toPart (c : lint.Chain) (h : c.steps.len = 1) : (toPart c).flip = toPart (lint.reversed c) := by
  obtain ⟨s, hs⟩ := single_steps c h
  rcases c with ⟨first, asc, steps⟩
  · simp only at hs
    have e0 : steps.nth 0 = s := by simp [Fren.Seq.nth, hs]
    have el : lint.last_operand ⟨first, asc, steps⟩ = s.operand := by
      simp [lint.last_operand, Fren.Seq.ext_iff, hs, Fren.Seq.nth]
    simp only [lint.reversed, el, e0]
    simp [ChainPart.flip, toPart, hs, mirror_opText]

theorem oriented_toPart (c : lint.Chain) (h : c.steps ≠ ∅) (f : Bool) (hf : f = true → c.steps.len = 1) :
    (if f then (toPart c).flip else toPart c) = toPart (lint.oriented c f) := by
  cases f
  · simp [lint.oriented]
  · simp [oriented_eq c h, flip_toPart c (hf rfl)]

theorem reversed_len (c : lint.Chain) : (lint.reversed c).steps.len = 1 := by
  simp

theorem oriented_len (c : lint.Chain) (f : Bool) (hf : f = true → c.steps.len = 1) :
    (lint.oriented c f).steps.len = c.steps.len := by
  cases f
  · simp [lint.oriented]
  · by_cases h : c.steps = ∅
    · simp [lint.oriented, h]
    · rw [oriented_eq c h, if_pos rfl, reversed_len, hf rfl]

theorem oriented_ne (c : lint.Chain) (h : c.steps ≠ ∅) (f : Bool) (hf : f = true → c.steps.len = 1) :
    (lint.oriented c f).steps ≠ ∅ := by
  intro e
  have := oriented_len c f hf
  rw [e] at this
  exact h (Fren.Seq.ext (List.length_eq_zero_iff.mp (by simp at this; omega)))

/-- What `chains_flipped?` gives: each conjunct written the other way round
is one comparison, and as written, they order the same way, and the left's
last operand is the right's first. -/
theorem chains_facts (l r : lint.Chain) (fl fr : Bool) (h : lint.chains_flipped? l r fl fr = true) :
    (fl = true → l.steps.len = 1) ∧ (fr = true → r.steps.len = 1)
      ∧ (lint.oriented l fl).«ascending?» = (lint.oriented r fr).«ascending?»
      ∧ lint.last_operand (lint.oriented l fl) = (lint.oriented r fr).first := by
  simp only [lint.chains_flipped?, lint.chains?, decide_eq_true_eq, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, _⟩ := h
  refine ⟨fun e => h1.resolve_left (by simp [e]), fun e => h2.resolve_left (by simp [e]),
    Bool.eq_iff_iff.mpr h3, h4⟩

theorem toPart_join (a b : lint.Chain) (hab : a.«ascending?» = b.«ascending?») :
    ({ operands := (toPart a).operands ++ (toPart b).operands.extract 1, ops := (toPart a).ops ++ (toPart b).ops } :
      ChainPart String) = toPart (lint.joined a b) := by
  rcases a with ⟨fa, aa, sa⟩
  rcases b with ⟨fb, ab, sb⟩
  simp only at hab
  subst hab
  unfold lint.joined
  simp only [toPart, Fren.Seq.toList_append, List.map_append]
  congr 1
  · apply Array.toList_inj.mp
    simp [List.take_of_length_le]
  · simp

/-- The code's join of two conjuncts of the model is the model's chain of
them, as the fix writes them. -/
theorem join_toPart (l r : lint.Chain) (hl : l.steps ≠ ∅) (hr : r.steps ≠ ∅) (fl fr : Bool)
    (h : lint.chains_flipped? l r fl fr = true) :
    (toPart l).join (toPart r) fl fr = toPart (lint.joined (lint.oriented l fl) (lint.oriented r fr)) := by
  obtain ⟨hfl, hfr, hasc, _⟩ := chains_facts l r fl fr h
  simp only [ChainPart.join]
  rw [oriented_toPart l hl fl hfl, oriented_toPart r hr fr hfr]
  exact toPart_join _ _ hasc

theorem joined_ne (a b : lint.Chain) (h : a.steps ≠ ∅) : (lint.joined a b).steps ≠ ∅ := by
  intro e; apply h; apply Fren.Seq.ext
  have := congrArg Fren.Seq.toList e
  unfold lint.joined at this
  simp only [Fren.Seq.toList_append, Fren.Seq.toList_empty, List.append_eq_nil_iff] at this
  simpa using this.1

-- Both front ends write the chain of two conjuncts with `ChainPart.join`,
-- in `chainableAt`, on the conjuncts that `chainFlips` joins.
impl chainable_joined: lint::chainable_joined for (l r : lint.Chain) (fl fr : Bool) {
  left := l,
  right := r,
  «flip_left?» := fl,
  «flip_right?» := fr,
  chain := fromPart ((toPart l).join (toPart r) fl fr),
} by
  intro l r fl fr ⟨⟨hl, hr⟩, h⟩
  obtain ⟨hfl, _, _, _⟩ := chains_facts l r fl fr h
  rw [join_toPart l r hl hr fl fr h, fromPart_toPart _ (joined_ne _ _ (oriented_ne l hl fl hfl))]
  simp [fren_spec]

end Fren.Impls.Chains
