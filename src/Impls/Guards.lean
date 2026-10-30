-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
import Std.Tactic.BVDecide
-- keep-sorted end
open Fren.Lang

/-! # Guards (`Reqs/Lint/Complexity/Matches`, `Reqs/Lint/Style/Matches`)

`trivial_guard`, `redundant_guards` and `match_arm_if_else`, proved of the
functions that both front ends call. -/

namespace Fren.Impls.Guards

/-- A bound of a range of the model (`lint::Bound`), as the code's are. -/
def toBound : lint.Bound → Option Int
  | .Open => none
  | .At k => some k

/-- A guard as `trivial_guard` reads it (`lint::Guard`). -/
def toGuardForm : lint.Guard → Fren.Core.GuardForm
  | .Absent => .absent
  | .Literal b => .literal b
  | .Other _ => .other

def toGuardFix : Fren.Core.GuardFix → lint.GuardFix
  | .unchanged => .Unchanged
  | .dropGuard => .DropGuard
  | .dropArm => .DropArm

-- Both front ends read the guard without its parentheses, and decide with
-- `trivialGuard`, from `matchAccepted` of the arms after the fix and
-- whether the text it removes has a comment.
impl trivial_guard: lint::trivial_guard for (g : lint.Guard) (m a c : Bool) {
  guard := g,
  matches? := m,
  accepted? := a,
  commented? := c,
  fires? := (Fren.Core.trivialGuard (toGuardForm g) a c).1,
  fix := toGuardFix (Fren.Core.trivialGuard (toGuardForm g) a c).2,
} by
  intro g m a c _
  rcases g with _ | ⟨_ | _⟩ | _ <;> cases a <;> cases c <;>
    simp [fren_spec, Fren.Core.trivialGuard, toGuardForm, toGuardFix]

/-- A leaf of the model as the code's patterns write it (`lint::Leaf`). -/
def leafToCore : lint.Leaf → Fren.Core.Pat
  | .Wild => .wild false
  | .Binder _ _ => .wild true
  | .Lit k => .int (some k) (some k)
  | .Range lo hi => .int (toBound lo) (toBound hi)

/-- A pattern of the model as the code's patterns write it (`lint::Pat`). -/
def patToCore : lint.Pat → Fren.Core.Pat
  | .Wild => .wild false
  | .Binder _ _ => .wild true
  | .Lit k => .int (some k) (some k)
  | .Range lo hi => .int (toBound lo) (toBound hi)
  | .Tag t => .ctor t.toNat #[]
  | .Variant t l m => .ctor t.toNat #[leafToCore l, leafToCore m]

/-- The path to the binder named `n` of the model's pattern `p`, which the
front ends find from the binder's name (`Fren.Core.guardBinderPath?`). -/
def binderPath (p : lint.Pat) (n : Int) : Option (List Nat) :=
  if n < 0 then none else
  match p with
  | .Binder k _ => if k = n then some [] else none
  | .Variant _ l m => if lint.leaf_name l = n then some [0] else if lint.leaf_name m = n then some [1] else none
  | _ => none

def toGuardValue : lint.GuardValue → Fren.Core.GuardValue
  | .Written c => .pattern (.int (some c) (some c))
  | .Other _ => .other

/-- The binders of a pattern have distinct names (`lint::redundant_guards`'s
`distinct`). -/
abbrev DistinctBinders (p : lint.Pat) : Prop := match p with
  | .Variant _ l m => lint.leaf_name l < 0 ∨ lint.leaf_name l ≠ lint.leaf_name m
  | _ => True

-- The code's new pattern is the spec's, `pat_with`, read as the code's
-- patterns are, wherever the guard compares a binder of the pattern with a
-- value that a pattern writes, and nothing otherwise: the binder is found
-- by its name, which no other binder of the pattern has.
theorem redundantGuard_pat_with (p : lint.Pat) (n : Int) (v : lint.GuardValue) (hd : DistinctBinders p) :
    Fren.Core.redundantGuard? (patToCore p) (binderPath p n) (toGuardValue v) =
      if lint.binds_name? p n = true ∧ v = .Written (lint.guard_value v) then
        some (patToCore (lint.pat_with p n (lint.guard_value v)))
      else none := by
  rcases v with c | c <;>
  rcases p with _ | ⟨k, b⟩ | k | ⟨lo, hi⟩ | t | ⟨t, l, m⟩ <;>
  simp [fren_spec, binderPath, patToCore, toGuardValue, Fren.Core.redundantGuard?, lint.binds_name?, lint.pat_with,
    lint.guard_value, Fren.Core.Pat.replaceAt]
  all_goals (try rcases l with _ | ⟨k1, b1⟩ | _ | _)
  all_goals (try rcases m with _ | ⟨k2, b2⟩ | _ | _)
  all_goals (try simp [DistinctBinders, fren_spec, lint.leaf_name] at hd)
  all_goals (repeat' split) <;> simp_all [fren_spec, leafToCore, Fren.Core.Pat.replaceAt] <;> omega

theorem redundantGuard_isSome (p : lint.Pat) (n : Int) (v : lint.GuardValue) (hd : DistinctBinders p) :
    (Fren.Core.redundantGuard? (patToCore p) (binderPath p n) (toGuardValue v)).isSome = true ↔
      lint.binds_name? p n = true ∧ v = .Written (lint.guard_value v) := by
  rw [redundantGuard_pat_with p n v hd]
  by_cases h : lint.binds_name? p n = true ∧ v = .Written (lint.guard_value v)
  · rw [if_pos h]; simp only [Option.isSome_some, true_iff]; exact h
  · rw [if_neg h]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; exact h

theorem redundant_guards_distinct (p : lint.Pat) (n : Int) (v : lint.GuardValue) (a : Bool) (b : lint.Body)
    (x : lint.Val) (o : Int) (fs : Bool) (fx : lint.Pat) (h : lint.redundant_guards.assume.distinct p n v a b x o fs fx) :
    DistinctBinders p := by
  rcases p <;> simp_all [lint.redundant_guards.assume.distinct, fren_spec, DistinctBinders]

-- Both front ends decide with `redundantGuard?`, from the path of the binder
-- that the guard names and the value it compares it with, and
-- `matchAccepted` of the arms with its pattern and without the guard. The
-- new pattern is the code's, by `redundantGuard_pat_with`.
impl redundant_guards: lint::redundant_guards for (p : lint.Pat) (n : Int) (v : lint.GuardValue) (a : Bool)
    (b : lint.Body) (x : lint.Val) (o : Int) {
  pattern := p,
  name := n,
  value := v,
  accepted? := a,
  body := b,
  x := x,
  o := o,
  fires? := (Fren.Core.redundantGuard? (patToCore p) (binderPath p n) (toGuardValue v)).isSome && a,
  fixed := if (Fren.Core.redundantGuard? (patToCore p) (binderPath p n) (toGuardValue v)).isSome && a
    then lint.pat_with p n (lint.guard_value v) else p,
} by
  intro p n v a b x o hA
  have hd := redundant_guards_distinct p n v a b x o _ _ hA
  unfold lint.redundant_guards.ensures lint.redundant_guards.ensure.rule lint.redundant_guards.ensure.fix
  refine ⟨?_, rfl⟩
  rw [Bool.and_eq_true, redundantGuard_isSome p n v hd]
  rcases v <;> simp [fren_spec, lint.guard_value, lint.GuardValue.Written.x0]

trusted lint::trivial_guard_written: "a model of an expression, checked by the refinements in its section"
trusted lint::trivial_guard_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::redundant_guards_written: "a model of an expression, checked by the refinements in its section"
trusted lint::redundant_guards_fixed: "a model of an expression, checked by the refinements in its section"

/-! ## `match_arm_if_else` -/

/-- An arm's body as `match_arm_if_else` reads it (`lint::IfBody`). -/
def toIfArmBody : lint.IfBody → Fren.Core.IfArmBody lint.Body
  | .IfElse _ _ d => .ifElse d
  | .Plain b => .plain b

/-- Whether a pattern of the model matches every value: `_` or a binder. -/
def wildPat (p : lint.Pat) : Bool := match p with | .Wild | .Binder _ _ => true | _ => false

/-- An arm as `match_arm_if_else` reads it (`lint::IfArm`). -/
def toIfArmInfo (a : lint.IfArm) : Fren.Core.IfArmInfo lint.Body :=
  { wild := wildPat a.pat, body := toIfArmBody a.body, binds := a.«binds?» }

/-- Two bodies of the model are written the same where they are equal. -/
def sameBody (b c : lint.Body) : Bool := decide (b = c)

/-- Whether `d` names a binder of arm `j` of `l`. -/
def mentionsIn (l : List lint.IfArm) (d : lint.Body) (j : Nat) : Bool :=
  (l[j]?.map fun a => lint.names_binder? d a.pat).getD false

/-- Whether the patterns of arms `i` and `j` of `l` may overlap, as the
model says (`lint::overlap?`). -/
def overlapIn (l : List lint.IfArm) (i j : Nat) : Bool :=
  match l[i]?, l[j]? with
  | some a, some b => lint.overlap? a.pat b.pat
  | _, _ => false

/-- Whether the fix moves the arm `a`'s condition into a guard, where the
`else` branch is `d` (`lint::moved?`), and whether its body is `d`, not
as an `if`. -/
def movedArm (d : lint.Body) (a : lint.IfArm) : Bool := (toIfArmInfo a).moved sameBody d

def plainArm (d : lint.Body) (a : lint.IfArm) : Bool := (toIfArmInfo a).plainIs sameBody d

theorem moved_fold (d : lint.Body) (a : lint.IfArm) : (toIfArmInfo a).moved sameBody d = movedArm d a := rfl

theorem plain_fold (d : lint.Body) (a : lint.IfArm) : (toIfArmInfo a).plainIs sameBody d = plainArm d a := rfl

theorem wild_fold (a : lint.IfArm) : (toIfArmInfo a).wild = wildPat a.pat := rfl

theorem binds_fold (a : lint.IfArm) : (toIfArmInfo a).binds = a.«binds?» := rfl

theorem wildPat_spec (p : lint.Pat) :
    (p = .Wild ∨ p = .Binder (lint.Pat.Binder.x0 p) (lint.Pat.Binder.x1 p)) ↔ wildPat p = true := by
  cases p <;> simp [wildPat, lint.Pat.Binder.x0, lint.Pat.Binder.x1]

theorem plainArm_spec (d : lint.Body) (a : lint.IfArm) : a.body = .Plain d ↔ plainArm d a = true := by
  rcases a with ⟨p, b, bi⟩
  cases b <;> cases bi <;> simp [plainArm, toIfArmInfo, toIfArmBody, Fren.Core.IfArmInfo.plainIs, sameBody]

theorem movedArm_spec (d : lint.Body) (a : lint.IfArm) :
    ((¬(match a.pat with | .Wild => true | .Binder _ _ => true | _ => false) = true) ∧
      (match a.body with | .IfElse _ _ _ => true | _ => false) = true) ∧ lint.else_of a.body = d ↔
      movedArm d a = true := by
  rcases a with ⟨p, b, bi⟩
  cases p <;> cases b <;> cases bi <;> simp [movedArm, toIfArmInfo, wildPat, toIfArmBody, Fren.Core.IfArmInfo.moved,
    sameBody, lint.else_of]

theorem nth_slot (l : List lint.IfArm) (s : lint.Slot) (h : (lint.pos s).toNat < l.length) :
    (Fren.Seq.ofList l).nth (lint.pos s) = l[(lint.pos s).toNat] := by
  have hp : 0 ≤ lint.pos s := by cases s <;> simp [lint.pos]
  rw [Fren.Seq.nth_of_lt _ _ hp (by simp; omega)]; rfl

-- The spec's `moved?` of a slot is the code's test of the arm there, and
-- false past the last arm.
theorem moved_eq (l : List lint.IfArm) (s : lint.Slot) (d : lint.Body) :
    lint.moved? (Fren.Seq.ofList l) s d = ((l[(lint.pos s).toNat]?).map (movedArm d)).getD false := by
  have hp : 0 ≤ lint.pos s := by cases s <;> simp [lint.pos]
  rw [Bool.eq_iff_iff]
  simp only [lint.moved?, decide_eq_true_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList]
  by_cases h : lint.pos s < l.length
  · have h' : (lint.pos s).toNat < l.length := by omega
    rw [nth_slot l s h', List.getElem?_eq_getElem h']
    simp only [Option.map_some, Option.getD_some, ← movedArm_spec]
    constructor
    · rintro ⟨⟨⟨_, a⟩, b⟩, c⟩; exact ⟨⟨a, b⟩, c⟩
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨⟨h, a⟩, b⟩, c⟩
  · rw [List.getElem?_eq_none (by omega)]
    simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, iff_false]
    rintro ⟨⟨⟨hl, _⟩, _⟩, _⟩; exact h hl

theorem ite_some_isSome (c : Prop) [Decidable c] (x : α) : (if c then some x else none).isSome = decide c := by
  by_cases h : c <;> simp [h]

-- Whether the fix adds `_ => d`: the code reads the last arm, as the spec
-- does.
theorem appended_iff (l : List lint.IfArm) (h : l ≠ []) (d : lint.Body) :
    Fren.Core.matchArmIfElseAppends sameBody (l.map toIfArmInfo) d = lint.appends? (Fren.Seq.ofList l) d := by
  have hn : 0 < l.length := List.length_pos_iff.mpr h
  have hlast : (Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1) = l.getLast h := by
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList]
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
    simp only [Fren.Seq.toList_ofList, List.getLast_eq_getElem]
    congr 1; omega
  have hne : ¬Fren.Seq.ofList l = ∅ := by
    intro he
    have := congrArg Fren.Seq.len he
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList] at this
    exact h (by simpa using this)
  rw [Bool.eq_iff_iff]
  simp only [lint.appends?, decide_eq_true_eq, hlast, plainArm_spec]
  simp only [Fren.Core.matchArmIfElseAppends, List.getLast?_map, List.getLast?_eq_some_getLast h, Option.map_some,
    Option.any_some, plain_fold, wild_fold]
  cases plainArm d (l.getLast h) <;> cases (l.getLast h).pat <;> simp [wildPat, hne]

/-- Normalizes the rule of `match_arm_if_else` over a list of arms written
out, to the tests of each arm and of each pair. -/
macro "arms_normal" : tactic => `(tactic| (
  repeat rw [moved_eq]
  simp (config := { decide := true }) only [lint.pos, Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_cons,
    List.length_nil, Fren.Seq.nth, plainArm_spec, Int.reduceToNat, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, dite_true, dite_false,
    List.getElem_cons_zero, List.getElem_cons_succ, Fren.Core.matchArmIfElseFor, List.map_cons, List.map_nil,
    mentionsIn, overlapIn, moved_fold, plain_fold, binds_fold, List.range, List.range.loop, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, ite_some_isSome]
  simp only [false_and, and_false, false_implies, true_and, and_true, or_false, false_or,
    decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true]))

-- Both front ends decide with `matchArmIfElseFor`, through
-- `matchArmIfElse?`, which tries the `else` branches in order, and with
-- `matchArmIfElseAppends`: here over the model's bodies, with `overlap?` for
-- the overlap of two patterns. The front ends give it `Pat.overlapWit?`,
-- whose agreement with `overlap?` is proved for patterns of one value
-- (`lang::pattern_overlap`), not for the model's variants of two; and
-- `mentionsName` over the binders' names for `names_binder?`. The rule is
-- proved for each number of arms, one to four, as the spec has: each is a
-- formula over the tests of the arms and of each pair, which `bv_decide`
-- decides. Its proofs are checked by Lean's compiled LRAT checker
-- (`Lean.ofReduceBool`, the `_native.bv_decide.ax_*` axioms), not by the
-- kernel alone: a weaker level of trust than this file's other proofs,
-- stated here rather than left to the evidence report.
set_option linter.unusedSimpArgs false in
impl match_arm_if_else: lint::match_arm_if_else for (l : List lint.IfArm) (d : lint.Body) (a : Bool) {
  arms := Fren.Seq.ofList l,
  d := d,
  accepted? := a,
  fires? := (Fren.Core.matchArmIfElseFor sameBody (mentionsIn l) (overlapIn l) (l.map toIfArmInfo) d).isSome && a,
  appended? := Fren.Core.matchArmIfElseAppends sameBody (l.map toIfArmInfo) d,
} by
  intro l d a hA
  have hl : 1 ≤ l.length ∧ l.length ≤ 4 := by
    simp only [lint.match_arm_if_else.assumes, lint.match_arm_if_else.assume.size, Fren.Seq.len_eq,
      Fren.Seq.toList_ofList] at hA
    omega
  have hne : l ≠ [] := by intro h; simp [h] at hl
  unfold lint.match_arm_if_else.ensures
  refine ⟨?_, by rw [appended_iff l hne d]⟩
  dsimp only [lint.match_arm_if_else.ensure.rule]
  -- `fires_on?` as a proposition over the tests of each arm and pair, which
  -- its `decide` decides classically.
  rw [(@decide_eq_true_iff _ (Classical.propDecidable _) : lint.fires_on? (Fren.Seq.ofList l) d = true ↔ _)]
  match l, hl with
  | [a0], _ =>
    arms_normal
    generalize movedArm d a0 = m0
    generalize a0.«binds?» = b0
    revert m0 b0 a
    bv_decide
  | [a0, a1], _ =>
    arms_normal
    generalize movedArm d a0 = m0; generalize movedArm d a1 = m1
    generalize plainArm d a1 = p1
    generalize lint.names_binder? d a0.pat = n0; generalize lint.names_binder? d a1.pat = n1
    generalize lint.overlap? a0.pat a1.pat = o01
    generalize a0.«binds?» = b0; generalize a1.«binds?» = b1
    revert m0 m1 p1 n0 n1 o01 b0 b1 a
    bv_decide
  | [a0, a1, a2], _ =>
    arms_normal
    generalize movedArm d a0 = m0; generalize movedArm d a1 = m1; generalize movedArm d a2 = m2
    generalize plainArm d a1 = p1; generalize plainArm d a2 = p2
    generalize lint.names_binder? d a0.pat = n0; generalize lint.names_binder? d a1.pat = n1
    generalize lint.names_binder? d a2.pat = n2
    generalize lint.overlap? a0.pat a1.pat = o01; generalize lint.overlap? a0.pat a2.pat = o02
    generalize lint.overlap? a1.pat a2.pat = o12
    generalize a0.«binds?» = b0; generalize a1.«binds?» = b1; generalize a2.«binds?» = b2
    revert m0 m1 m2 p1 p2 n0 n1 n2 o01 o02 o12 b0 b1 b2 a
    bv_decide
  | [a0, a1, a2, a3], _ =>
    arms_normal
    generalize movedArm d a0 = m0; generalize movedArm d a1 = m1; generalize movedArm d a2 = m2
    generalize movedArm d a3 = m3
    generalize plainArm d a1 = p1; generalize plainArm d a2 = p2; generalize plainArm d a3 = p3
    generalize lint.names_binder? d a0.pat = n0; generalize lint.names_binder? d a1.pat = n1
    generalize lint.names_binder? d a2.pat = n2; generalize lint.names_binder? d a3.pat = n3
    generalize lint.overlap? a0.pat a1.pat = o01; generalize lint.overlap? a0.pat a2.pat = o02
    generalize lint.overlap? a0.pat a3.pat = o03; generalize lint.overlap? a1.pat a2.pat = o12
    generalize lint.overlap? a1.pat a3.pat = o13; generalize lint.overlap? a2.pat a3.pat = o23
    generalize a0.«binds?» = b0; generalize a1.«binds?» = b1; generalize a2.«binds?» = b2
    generalize a3.«binds?» = b3
    revert m0 m1 m2 m3 p1 p2 p3 n0 n1 n2 n3 o01 o02 o03 o12 o13 o23 b0 b1 b2 b3 a
    bv_decide
  | [], h => simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-! ### The fix keeps the meaning (`lint::match_arm_if_else_keeps_meaning`) -/

-- A lower bound and an upper bound that hold of one value meet.
theorem reaches_of (a b : lint.Bound) (v : Int) (ha : lint.lower_holds? a v = true)
    (hb : lint.upper_holds? b v = true) : lint.reaches? a b = true := by
  cases a <;> cases b <;> simp [lint.lower_holds?, lint.upper_holds?, lint.reaches?, lint.Bound.At.x0] at ha hb ⊢
  omega

-- A leaf that matches `v` has `v` within its bounds.
theorem leaf_bounds (l : lint.Leaf) (v : Int) (h : lint.leaf_matches? l v = true) :
    lint.lower_holds? (lint.leaf_min l) v = true ∧ lint.upper_holds? (lint.leaf_max l) v = true := by
  cases l <;> simp [lint.leaf_matches?, lint.leaf_min, lint.leaf_max, lint.lower_holds?, lint.upper_holds?,
    lint.Bound.At.x0, lint.Leaf.Lit.x0, lint.Leaf.Range.x0, lint.Leaf.Range.x1] at h ⊢ <;> grind

theorem leaves_overlap_of (l m : lint.Leaf) (v : Int) (hl : lint.leaf_matches? l v = true)
    (hm : lint.leaf_matches? m v = true) : lint.leaves_overlap? l m = true := by
  obtain ⟨l1, l2⟩ := leaf_bounds l v hl
  obtain ⟨m1, m2⟩ := leaf_bounds m v hm
  simp [lint.leaves_overlap?, reaches_of _ _ v l1 m2, reaches_of _ _ v m1 l2]

-- An integer pattern that matches `x` has `x.n` within its bounds.
theorem int_bounds (p : lint.Pat) (x : lint.Val) (h : lint.pat_matches? p x = true)
    (hi : lint.integers_pattern? p = true) :
    lint.lower_holds? (lint.lower_of p) x.n = true ∧ lint.upper_holds? (lint.upper_of p) x.n = true := by
  cases p <;> simp [lint.pat_matches?, lint.integers_pattern?, lint.lower_of, lint.upper_of, lint.lower_holds?,
    lint.upper_holds?, lint.Bound.At.x0, lint.Pat.Lit.x0, lint.Pat.Range.x0, lint.Pat.Range.x1] at h hi ⊢ <;> grind

-- Every pattern is `_` or a binder, an integer pattern, or a variant pattern.
theorem pat_kinds (p : lint.Pat) :
    wildPat p = true ∨ lint.integers_pattern? p = true ∨ lint.variants_pattern? p = true := by
  cases p <;> simp [wildPat, lint.integers_pattern?, lint.variants_pattern?]

-- A variant pattern that matches `x` has its tag, and its leaves match its
-- payload.
theorem variant_facts (p : lint.Pat) (x : lint.Val) (h : lint.pat_matches? p x = true)
    (hv : lint.variants_pattern? p = true) :
    lint.pattern_tag p = x.tag ∧ lint.leaf_matches? (lint.first_leaf p) x.a = true ∧
      lint.leaf_matches? (lint.second_leaf p) x.b = true := by
  cases p <;> simp only [lint.variants_pattern?, decide_false, decide_true, Bool.false_eq_true] at hv <;>
    simp only [lint.pat_matches?, lint.pattern_tag, lint.first_leaf, lint.second_leaf, reduceCtorEq, ↓reduceIte,
      lint.Pat.Tag.x0, lint.Pat.Variant.x0, lint.Pat.Variant.x1, lint.Pat.Variant.x2, decide_eq_true_eq] at h ⊢
  · exact ⟨h.symm, trivial, trivial⟩
  · exact ⟨h.1.1.symm, h.1.2, h.2⟩

-- `overlap?` is sound: two patterns of one type that match a value in common
-- overlap. The same statement as `lint::overlap_matches`, which the solver
-- checks: a change to one changes the other.
theorem overlap_sound (p q : lint.Pat) (x : lint.Val) (hp : lint.pat_matches? p x = true)
    (hq : lint.pat_matches? q x = true)
    (h1 : ¬(lint.integers_pattern? p = true ∧ lint.variants_pattern? q = true))
    (h2 : ¬(lint.variants_pattern? p = true ∧ lint.integers_pattern? q = true)) :
    lint.overlap? p q = true := by
  rw [lint.overlap?.eq_def, decide_eq_true_eq]
  rcases pat_kinds p with kp | kp | kp
  · exact Or.inl (Or.inl (Or.inl kp))
  rcases pat_kinds q with kq | kq | kq
  · exact Or.inl (Or.inl (Or.inr kq))
  · obtain ⟨p1, p2⟩ := int_bounds p x hp kp
    obtain ⟨q1, q2⟩ := int_bounds q x hq kq
    exact Or.inl (Or.inr ⟨⟨⟨kp, kq⟩, reaches_of _ _ _ p1 q2⟩, reaches_of _ _ _ q1 p2⟩)
  · exact absurd ⟨kp, kq⟩ h1
  rcases pat_kinds q with kq | kq | kq
  · exact Or.inl (Or.inl (Or.inr kq))
  · exact absurd ⟨kp, kq⟩ h2
  · obtain ⟨t1, a1, b1⟩ := variant_facts p x hp kp
    obtain ⟨t2, a2, b2⟩ := variant_facts q x hq kq
    exact Or.inr ⟨⟨⟨⟨kp, kq⟩, t1.trans t2.symm⟩, leaves_overlap_of _ _ _ a1 a2⟩, leaves_overlap_of _ _ _ b1 b2⟩

-- A body that names no binder of the pattern has its value outside the `match`.
theorem in_arm_outside (p : lint.Pat) (b : lint.Body) (x : lint.Val) (o : Int)
    (h : lint.names_binder? b p = false) :
    lint.in_arm p b x o = lint.body_value b (-1) 0 (-1) 0 (-1) 0 o := by
  rcases b with ⟨f, u⟩
  cases p <;> cases u <;> simp [lint.in_arm, lint.names_binder?, lint.body_value, lint.leaf_name,
    lint.Use.Name.x0, lint.Pat.Binder.x0, lint.Pat.Binder.x1, lint.Pat.Variant.x0, lint.Pat.Variant.x1,
    lint.Pat.Variant.x2] at h ⊢ <;> grind

-- A moved arm whose condition holds has the value of its `then` branch.
theorem arm_kept (d : lint.Body) (a : lint.IfArm) (x : lint.Val) (o : Int) (hm : movedArm d a = true)
    (hc : lint.cond_of? a.body = true) : lint.in_arm a.pat (lint.then_of a.body) x o = lint.arm_value a x o := by
  rcases a with ⟨p, b, i⟩
  cases b <;> simp_all [movedArm, toIfArmInfo, toIfArmBody, Fren.Core.IfArmInfo.moved, lint.cond_of?, lint.then_of,
    lint.arm_value]

-- A moved arm whose condition fails has its `else` branch `d`, the value
-- that `d` has outside the `match`, where it names none of the arm's binders.
theorem arm_falls (d : lint.Body) (a : lint.IfArm) (x : lint.Val) (o : Int) (hm : movedArm d a = true)
    (hc : lint.cond_of? a.body = false) (hn : lint.names_binder? d a.pat = false) :
    lint.arm_value a x o = lint.body_value d (-1) 0 (-1) 0 (-1) 0 o := by
  have he := ((movedArm_spec d a).2 hm).2
  rcases a with ⟨p, b, i⟩
  cases b with
  | IfElse c t e =>
    simp only [lint.else_of] at he
    subst he
    cases c
    · simp only [lint.arm_value, Bool.false_eq_true, ↓reduceIte]
      exact in_arm_outside p _ x o hn
    · simp [lint.cond_of?] at hc
  | Plain _ => simp [movedArm, toIfArmInfo, toIfArmBody, Fren.Core.IfArmInfo.moved] at hm

-- An arm whose body is `d`, not as an `if`, has the value that `d` has
-- outside the `match`, where it names none of the arm's binders; and the fix
-- does not move it.
theorem arm_plain (d : lint.Body) (a : lint.IfArm) (x : lint.Val) (o : Int) (hp : plainArm d a = true)
    (hn : lint.names_binder? d a.pat = false) :
    lint.arm_value a x o = lint.body_value d (-1) 0 (-1) 0 (-1) 0 o := by
  rw [← plainArm_spec] at hp
  rcases a with ⟨p, b, i⟩
  simp only at hp
  subst hp
  simp only [lint.arm_value]
  exact in_arm_outside p d x o hn

theorem plain_unmoved (d : lint.Body) (a : lint.IfArm) (hp : plainArm d a = true) : movedArm d a = false := by
  rw [← plainArm_spec] at hp
  rcases a with ⟨p, b, i⟩
  simp only at hp
  subst hp
  simp [movedArm, toIfArmInfo, toIfArmBody, Fren.Core.IfArmInfo.moved]

-- `_` or a binder matches every value, and the fix does not move its arm.
theorem wild_matches (p : lint.Pat) (h : wildPat p = true) (x : lint.Val) : lint.pat_matches? p x = true := by
  cases p <;> simp_all [wildPat, lint.pat_matches?]

theorem wild_unmoved (d : lint.Body) (a : lint.IfArm) (h : wildPat a.pat = true) : movedArm d a = false := by
  rcases a with ⟨p, b, i⟩
  cases p <;> simp_all [wildPat, movedArm, toIfArmInfo, Fren.Core.IfArmInfo.moved]

section keeps
-- The tests and values of single arms stay folded while `simp` takes the
-- spec's functions apart: they are reducible, and `decide_eq_true_eq` would
-- unfold them.
set_option allowUnsafeReducibility true
attribute [local irreducible] lint.moved? lint.names_binder? lint.overlap? lint.pat_matches? lint.cond_of?
  lint.arm_value lint.in_arm lint.then_of lint.body_value lint.integers_pattern? lint.variants_pattern? lint.appends?

/-- Normalizes `keeps_meaning` over a list of arms written out, to the tests
and values of each arm and of each pair, with `appends?` as the code reads
the last arm (`appended_iff`). -/
macro "keeps_normal" : tactic => `(tactic| (
  rw [← appended_iff _ (by simp) _]
  simp (config := { decide := true }) only [lint.pos, Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_cons,
    List.length_nil, Fren.Seq.nth, plainArm_spec, Int.reduceToNat, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, dite_true, dite_false,
    List.getElem_cons_zero, List.getElem_cons_succ, Fren.Core.matchArmIfElseAppends, List.map_cons, List.map_nil,
    List.getLast?_cons_cons, List.getLast?_singleton, Option.any_some, plain_fold, wild_fold]))

/-- The facts of one arm `a`'s value and tests, for `grind`. -/
macro "arm_facts" d:term:max a:term:max x:term:max o:term:max : tactic => `(tactic| (
  have := arm_kept $d $a $x $o; have := arm_falls $d $a $x $o; have := arm_plain $d $a $x $o
  have := plain_unmoved $d $a))

-- For every sequence of up to four arms, each arm that the `match` takes as
-- written, every value of the scrutinee and every value outside the
-- `match`: each case is a formula over the tests and values of the arms and
-- of each pair, with the facts that relate them, which `grind` decides.
impl match_arm_if_else_keeps_meaning: lint::match_arm_if_else_keeps_meaning for (l : List lint.IfArm) (d : lint.Body)
    (x : lint.Val) (o : Int) {
  arms := Fren.Seq.ofList l, d := d, x := x, o := o,
} by
  intro l d x o _
  unfold lint.match_arm_if_else_keeps_meaning.ensures
  dsimp only [lint.match_arm_if_else_keeps_meaning.ensure.keeps_meaning]
  simp only [lint.one_type?, lint.fires_on?, lint.keeps_where_fires?, lint.first_arm?, lint.keeps?, lint.first_fixed?,
    lint.taken_fixed?, lint.fixed_value, lint.arm_matches?, decide_eq_true_eq]
  repeat rw [moved_eq]
  match l with
  | [] => simp
  | [a0] =>
    keeps_normal
    arm_facts d a0 x o
    grind
  | [a0, a1] =>
    keeps_normal
    arm_facts d a0 x o; arm_facts d a1 x o
    have := overlap_sound a0.pat a1.pat x
    have := wild_matches a1.pat; have := wild_unmoved d a1
    grind
  | [a0, a1, a2] =>
    keeps_normal
    arm_facts d a0 x o; arm_facts d a1 x o; arm_facts d a2 x o
    have := overlap_sound a0.pat a1.pat x; have := overlap_sound a0.pat a2.pat x
    have := overlap_sound a1.pat a2.pat x
    have := wild_matches a2.pat; have := wild_unmoved d a2
    grind
  | [a0, a1, a2, a3] =>
    keeps_normal
    arm_facts d a0 x o; arm_facts d a1 x o; arm_facts d a2 x o; arm_facts d a3 x o
    have := overlap_sound a0.pat a1.pat x; have := overlap_sound a0.pat a2.pat x
    have := overlap_sound a0.pat a3.pat x; have := overlap_sound a1.pat a2.pat x
    have := overlap_sound a1.pat a3.pat x; have := overlap_sound a2.pat a3.pat x
    have := wild_matches a3.pat; have := wild_unmoved d a3
    -- Each arm that the `match` takes as written on its own; with four arms,
    -- the earlier ones need more than `grind`'s default nine case splits.
    repeat' apply And.intro
    all_goals grind (splits := 16)
  | _ :: _ :: _ :: _ :: _ :: _ => simp; omega

end keeps

trusted lint::match_arm_if_else_written: "a model of an expression, checked by the refinements in its section"
trusted lint::match_arm_if_else_fixed: "a model of an expression, checked by the refinements in its section"
end Fren.Impls.Guards
