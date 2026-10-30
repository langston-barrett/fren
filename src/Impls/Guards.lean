-- keep-sorted start
import FrenCore.Lint
import Impls.PatternTests
import Reqs.Lint
import Std.Tactic.BVDecide
-- keep-sorted end
open Fren.Lang

/-! # Guards (`Reqs/Lint/Complexity/Matches`, `Reqs/Lint/Style/Matches`)

`trivial_guard`, `redundant_guards` and `match_arm_if_else`, proved of the
functions that both front ends call. -/

namespace Fren.Impls.Guards

open Fren.Impls.PatternTests (toBound)

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
    Fren.Core.matchArmIfElseAppends sameBody (l.map toIfArmInfo) d = true ↔
      ¬((((Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1)).pat = .Wild ∨
          ((Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1)).pat =
            .Binder (lint.Pat.Binder.x0 ((Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1)).pat)
              (lint.Pat.Binder.x1 ((Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1)).pat)) ∧
        ((Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1)).body = .Plain d) := by
  have hn : 0 < l.length := List.length_pos_iff.mpr h
  have hlast : (Fren.Seq.ofList l).nth ((Fren.Seq.ofList l).len - 1) = l.getLast h := by
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList]
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
    simp only [Fren.Seq.toList_ofList, List.getLast_eq_getElem]
    congr 1; omega
  rw [hlast, wildPat_spec, plainArm_spec]
  simp only [Fren.Core.matchArmIfElseAppends, List.getLast?_map, List.getLast?_eq_some_getLast h, Option.map_some,
    Option.any_some, plain_fold, wild_fold]
  cases wildPat (l.getLast h).pat <;> cases plainArm d (l.getLast h) <;> simp

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
impl match_arm_if_else: lint::match_arm_if_else for (l : List lint.IfArm) (d : lint.Body) (a : Bool) (x : lint.Val)
    (o : Int) {
  arms := Fren.Seq.ofList l,
  d := d,
  accepted? := a,
  x := x,
  o := o,
  fires? := (Fren.Core.matchArmIfElseFor sameBody (mentionsIn l) (overlapIn l) (l.map toIfArmInfo) d).isSome && a,
  appended? := Fren.Core.matchArmIfElseAppends sameBody (l.map toIfArmInfo) d,
} by
  intro l d a x o hA
  have hl : 1 ≤ l.length ∧ l.length ≤ 4 := by
    simp only [lint.match_arm_if_else.assumes, lint.match_arm_if_else.assume.size, Fren.Seq.len_eq,
      Fren.Seq.toList_ofList] at hA
    omega
  have hne : l ≠ [] := by intro h; simp [h] at hl
  unfold lint.match_arm_if_else.ensures
  refine ⟨?_, (appended_iff l hne d)⟩
  dsimp only [lint.match_arm_if_else.ensure.rule]
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

trusted lint::match_arm_if_else_written: "a model of an expression, checked by the refinements in its section"
trusted lint::match_arm_if_else_fixed: "a model of an expression, checked by the refinements in its section"
end Fren.Impls.Guards
