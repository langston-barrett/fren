-- keep-sorted start
import FrenCore.Meaning
import Impls.Lang
-- keep-sorted end
open Fren.Lang

/-! # The core of meaning (`Reqs/Lang/Meaning`)

The core's environment and functions are interpreted with
`Fren.Core.Meaning`'s, and `lang::choice_arms` and `lang::node` are proved
of its definitions, for every layer. -/

namespace Fren.Impls

namespace Meaning

open Fren.Core.Meaning

variable {ctx : Ctx}

/-- A value, as the spec writes it. -/
def toValue : Value → lang.Value
  | .b x => .B x
  | .i n => .I n
  | .s x => .S x
  | .nil => .Nil
  | .cons v rest => .Cons (toValue v) (toValue rest)
  | .c c v => .C c (toValue v)

/-- A value of the spec's, as `Fren.Core.Meaning` writes it. -/
def ofValue : lang.Value → Value
  | .B x => .b x
  | .I n => .i n
  | .S x => .s x
  | .Nil => .nil
  | .Cons v rest => .cons (ofValue v) (ofValue rest)
  | .C c v => .c c (ofValue v)

@[simp] theorem ofValue_toValue (v : Value) : ofValue (toValue v) = v := by
  induction v <;> simp_all [toValue, ofValue]

@[simp] theorem toValue_ofValue (v : lang.Value) : toValue (ofValue v) = v := by
  induction v <;> simp_all [toValue, ofValue]

@[simp] theorem toValue_inj {v w : Value} : toValue v = toValue w ↔ v = w :=
  ⟨fun h => by simpa using congrArg ofValue h, fun h => h ▸ rfl⟩

@[simp] theorem toValue_eq_B {v : Value} {x : Bool} : toValue v = .B x ↔ v = .b x := by
  cases v <;> simp [toValue]

def toHead : Head → lang.Head
  | .literal v => .Literal (toValue v)
  | .bound v => .Bound (toValue v)
  | .constant c => .Constant c
  | .variable x => .Variable x
  | .definition x => .Definition x
  | .binder b => .Binder b
  | .construction c o => .Construction c o
  | .method m => .Method m
  | .uninterpreted f => .Uninterpreted f
  | .defined f => .Defined f
  | .op o s => .Op o s

def ofHead : lang.Head → Head
  | .Literal v => .literal (ofValue v)
  | .Bound v => .bound (ofValue v)
  | .Constant c => .constant c
  | .Variable x => .variable x
  | .Definition x => .definition x
  | .Binder b => .binder b
  | .Construction c o => .construction c o
  | .Method m => .method m
  | .Uninterpreted f => .uninterpreted f
  | .Defined f => .defined f
  | .Op o s => .op o s

@[simp] theorem ofHead_toHead (h : Head) : ofHead (toHead h) = h := by
  cases h <;> simp [toHead, ofHead]

@[simp] theorem toHead_ofHead (h : lang.Head) : toHead (ofHead h) = h := by
  cases h <;> simp [toHead, ofHead]

/-- A sequence of values, as the spec writes it. -/
def toValues (l : List Value) : Fren.Seq lang.Value := Fren.Seq.ofList (l.map toValue)

def ofValues (vs : Fren.Seq lang.Value) : List Value := vs.toList.map ofValue

@[simp] theorem ofValues_toValues (l : List Value) : ofValues (toValues l) = l := by
  simp [ofValues, toValues, Function.comp_def]

@[simp] theorem toValues_ofValues (vs : Fren.Seq lang.Value) : toValues (ofValues vs) = vs := by
  simp [ofValues, toValues, Function.comp_def]

@[simp] theorem ofValues_empty : ofValues ∅ = [] := rfl

@[simp] theorem len_toValues (l : List Value) : (toValues l).len = l.length := by
  simp [toValues]


theorem part_toValues (l : List Value) (k : Int) : lang.part (toValues l) k = toValue (part l k) := by
  unfold lang.part part
  by_cases h0 : 0 ≤ k
  · by_cases h1 : k < l.length
    · have : k.toNat < l.length := by omega
      simp [h0, h1, toValues, this]
    · have : ¬ k.toNat < l.length := by omega
      simp [h0, h1, toValues, toValue]
  · simp [h0, toValue]

theorem connective_eq (o : String) : lang.connective? o = connective o := by
  rw [Bool.eq_iff_iff]; simp [lang.connective?, connective, Fren.Str.lit, or_assoc]

theorem choice_eq (o : String) : lang.choice? o = choice o := by
  rw [Bool.eq_iff_iff]; simp [lang.choice?, choice, Fren.Str.lit]

theorem total_eq (o : String) : lang.total? o = total o := by
  rw [Bool.eq_iff_iff]; simp [lang.total?, total, connective_eq, Fren.Str.lit, or_assoc]

theorem operator_toHead (h : Head) : lang.operator (toHead h) = h.operator := by
  cases h <;> simp [lang.operator, toHead, Head.operator, Fren.Str.lit, lang.Head.Op.x0, lang.Head.Op.x1]

theorem isTrue_iff (v : Value) : v.isTrue = true ↔ v = .b true := by
  simp [Value.isTrue]

theorem connectiveValue_toValues (o : String) (l : List Value) :
    lang.connective_value o (toValues l) = toValue (connectiveValue o l) := by
  unfold lang.connective_value connectiveValue
  simp only [part_toValues, toValue_eq_B, Fren.Str.lit]
  by_cases hc : part l 0 = .b true <;>
    simp [hc, Value.isTrue, apply_ite toValue, toValue]

theorem armOpen_toValues (h : Head) (l : List Value) (k : Nat) :
    lang.arm_open? (toHead h) (toValues l) k (armMatches ctx h k (ofValue (lang.part (toValues l) 0)))
      = armOpen ctx h l k := by
  rw [Bool.eq_iff_iff]
  simp only [lang.arm_open?, armOpen, part_toValues, ofValue_toValue, operator_toHead, choice_eq, lang.arm_present?,
    lang.guard_at, guardAt, len_toValues, Fren.Str.lit, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  constructor <;> rintro ⟨⟨a, b⟩, c⟩ <;> exact ⟨⟨a, by omega⟩, c⟩

theorem armOpen_op (o s : String) (l : List Value) (k : Nat) :
    lang.arm_open? (lang.Head.Op o s) (toValues l) k (armMatches ctx (.op o s) k (part l 0)) = armOpen ctx (.op o s) l k := by
  simpa [part_toValues, toHead] using armOpen_toValues (.op o s) l k

theorem moreArms_op (o s : String) (l : List Value) :
    lang.more_arms? (lang.Head.Op o s) (toValues l) = (choice o && decide (l.length > 7)) := by
  rw [Bool.eq_iff_iff]
  simp [lang.more_arms?, choice_eq, lang.operator, lang.Head.Op.x0, lang.Head.Op.x1, toValues]
  exact fun _ => by constructor <;> intro <;> omega

theorem moreArms (h : Head) (l : List Value) :
    lang.more_arms? (toHead h) (toValues l) = (choice h.operator && decide (l.length > 7)) := by
  rw [Bool.eq_iff_iff]
  simp [lang.more_arms?, choice_eq, operator_toHead, toValues]
  exact fun _ => by constructor <;> intro <;> omega

theorem ofList_append {α : Type} (a b : List α) : FinSet.ofList (a ++ b) = FinSet.ofList a ∪ FinSet.ofList b := by
  apply FinSet.ext; simp

theorem armUnevaluated_eq (h : Head) (l : List Value) (i : Nat) :
    FinSet.ofList (armUnevaluated ctx h l i) = lang.unevaluated_arm i (armOpen ctx h l i && noneBefore ctx h l i) (armFires ctx h l i) := by
  apply FinSet.ext; intro k
  simp only [armUnevaluated, ofList_append, lang.unevaluated_arm, lang.guard_at, guardAt, FinSet.mem_union]
  split <;> split <;> simp <;> omega

theorem secondGuard_eq (o : String) : lang.second_guard o = toGuardedOperand (secondGuard o) := by
  unfold lang.second_guard secondGuard
  by_cases h1 : o = "or" <;> by_cases h2 : o = "when" <;> by_cases h3 : o = "unless" <;> by_cases h4 : o = "if" <;>
    simp [h1, h2, h3, h4, toGuardedOperand, Fren.Str.lit]

/-- `lang::guard`'s rule, of an operand and its condition, as
`Fren.Core.Meaning.evaluated` decides it. -/
theorem guard_rule (g : Fren.Core.GuardedOperand) (c : lang.Value) :
    lang.guard.ensure.rule (toGuardedOperand g) c (decide (c = .B true)) (evaluated g (ofValue c)) := by
  have : (ofValue c).isTrue = decide (c = .B true) := by
    cases c <;> simp only [ofValue, Value.isTrue] <;> (try rw [Bool.eq_iff_iff]) <;> simp
  cases g <;> simp [lang.guard.ensure.rule, toGuardedOperand, evaluated, this, Fren.Core.GuardedOperand.guard,
    Fren.Core.GuardedOperand.whenHolds]

theorem mentionedBy_eq (h : Head) (pm : List Fren.Core.Mention) :
    lang.mentioned_by (toHead h) (mentionSet pm) = mentionSet (mentionedBy h pm) := by
  cases h <;> simp [lang.mentioned_by, toHead, mentionedBy, lang.Head.Variable.x0, lang.Head.Uninterpreted.x0,
    lang.Head.Literal.x0, lang.Head.Bound.x0, lang.Head.Constant.x0, Fren.Impls.mentionSet, toMention]
  all_goals apply FinSet.ext; intro; simp

theorem read_eq (h : Head) (e : Env) (l : List Value) :
    (if toHead h = lang.Head.Variable (lang.Head.Variable.x0 (toHead h)) then
        toValue (e.lookup (lang.Head.Variable.x0 (toHead h)))
      else if toHead h = lang.Head.Uninterpreted (lang.Head.Uninterpreted.x0 (toHead h)) then
        toValue (e.meaning (lang.Head.Uninterpreted.x0 (toHead h)) l)
      else lang.Value.Nil) = toValue (Fren.Core.Meaning.read h e l) := by
  cases h <;> simp [toHead, Fren.Core.Meaning.read, lang.Head.Variable.x0, lang.Head.Uninterpreted.x0, toValue]

theorem specified_eq (h : Head) (l : List Value) :
    (if toHead h = lang.Head.Literal (lang.Head.Literal.x0 (toHead h)) ∨
          toHead h = lang.Head.Bound (lang.Head.Bound.x0 (toHead h)) ∨
            toHead h = lang.Head.Variable (lang.Head.Variable.x0 (toHead h)) ∨
              toHead h = lang.Head.Definition (lang.Head.Definition.x0 (toHead h)) ∨
                toHead h = lang.Head.Construction (lang.Head.Construction.x0 (toHead h))
                  (lang.Head.Construction.x1 (toHead h)) ∨
                  toHead h = lang.Head.Uninterpreted (lang.Head.Uninterpreted.x0 (toHead h)) then true
      else if toHead h = lang.Head.Op (lang.Head.Op.x0 (toHead h)) (lang.Head.Op.x1 (toHead h)) then
        if lang.choice? (lang.Head.Op.x0 (toHead h)) = true then (firstFired ctx h l).isSome
        else decide (lang.total? (lang.Head.Op.x0 (toHead h)) = true ∨ fixedSpecified ctx h l = true)
      else fixedSpecified ctx h l) = specified ctx h l := by
  cases h <;> simp [toHead, specified, lang.Head.Literal.x0, lang.Head.Bound.x0, lang.Head.Variable.x0,
    lang.Head.Definition.x0, lang.Head.Construction.x0, lang.Head.Construction.x1, lang.Head.Uninterpreted.x0,
    lang.Head.Op.x0, lang.Head.Op.x1, choice_eq, ← total_eq]

theorem unevaluated_eq (h : Head) (l : List Value) :
    ((if lang.connective? (lang.operator (toHead h)) = true ∧ ¬evaluated (secondGuard h.operator) (part l 0) = true
        then {1} else ∅) ∪
      (if lang.operator (toHead h) = Fren.Str.lit "if" ∧ ¬evaluated .elseBranch (part l 0) = true then {2} else ∅)) ∪
      (if lang.choice? (lang.operator (toHead h)) = true then FinSet.ofList (choiceUnevaluated ctx h l) else ∅)
      = FinSet.ofList (unevaluated ctx h l) := by
  simp only [operator_toHead, connective_eq, choice_eq, unevaluated, ofList_append, Fren.Str.lit, beq_iff_eq,
    Bool.and_eq_true, Bool.not_eq_true']
  congr 1
  · congr 1 <;> (split <;> split <;> first | rfl | simp_all)
  · split <;> rfl

theorem fixedValue_constant (p : Program) (c : String) (l : List Value)
    (hs : fixedSpecified (Program.context p) (.constant c) l = true) :
    fixedValue (Program.context p) (.constant c) l = (Definition.value (Program.definition p c) l).getD .nil := by
  cases l with
  | nil => simp [fixedValue, fixedValue?, Program.ctx_value]
  | cons _ _ => simp [fixedSpecified, fixedValue?] at hs

theorem fixedValue_defined (p : Program) (f : String) (l : List Value) :
    fixedValue (Program.context p) (.defined f) l = (Definition.value (Program.definition p f) l).getD .nil := by
  simp [fixedValue, fixedValue?, Program.ctx_value]

theorem armGuard_toValues (l : List Value) (k : Nat) :
    lang.arm_guard (toValues l) k = toValue (Fren.Core.Meaning.armGuard l k) := by
  simp [lang.arm_guard, Fren.Core.Meaning.armGuard, lang.guard_at, guardAt, part_toValues]

theorem armBody_toValues (l : List Value) (k : Nat) :
    lang.arm_body (toValues l) k = toValue (Fren.Core.Meaning.armBody l k) := by
  simp [lang.arm_body, Fren.Core.Meaning.armBody, lang.guard_at, guardAt, part_toValues]

theorem fires_toValues (h : Head) (l : List Value) (k : Nat) (hk : k < 3) :
    lang.fires_at? (toValues l) (armOpen ctx h l 0) (armOpen ctx h l 1) (armOpen ctx h l 2) k = armFires ctx h l k := by
  have g0 : lang.arm_guard (toValues l) 0 = toValue (armGuard l 0) := by simpa using armGuard_toValues l 0
  have g1 : lang.arm_guard (toValues l) 1 = toValue (armGuard l 1) := by simpa using armGuard_toValues l 1
  have g2 : lang.arm_guard (toValues l) 2 = toValue (armGuard l 2) := by simpa using armGuard_toValues l 2
  rw [Bool.eq_iff_iff]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
    simp only [lang.fires_at?, g0, g1, g2, toValue_eq_B, armFires_zero, armFires_one, armFires_two, armHolds,
      Value.isTrue] <;> simp

end Meaning

open Meaning
open Fren.Core.Meaning (armOpen armFires firstFired statedUnevaluated choiceUnevaluated armMatches laterUnevaluated
  fixedValue fixedSpecified)

/-- What the program `p` gives a layer. -/
abbrev pctx (p : Fren.Core.Meaning.Program) : Fren.Core.Meaning.Ctx := Fren.Core.Meaning.Program.context p

-- An environment is any three functions: the values of variables and bound
-- names, of uninterpreted functions, and of unspecified layers. So what is
-- proved for every `Env` holds in every behaviour and interpretation.
interp lang::Env := Fren.Core.Meaning.Env
interp lang::lookup := fun (e : Fren.Core.Meaning.Env) x => Meaning.toValue (e.lookup x)
interp lang::meaning := fun (e : Fren.Core.Meaning.Env) f args => Meaning.toValue (e.meaning f (Meaning.ofValues args))
interp lang::unspecified := fun (e : Fren.Core.Meaning.Env) h vs => Meaning.toValue (e.unspecified (Meaning.ofHead h) (Meaning.ofValues vs))
-- A program is its declarations in order, each evaluated with those
-- before it. The values that the spec fixes are where
-- `Fren.Core.Meaning.fixedValue?` states them, and unspecified elsewhere.
interp lang::Program := Fren.Core.Meaning.Program
interp lang::definition_value := fun (p : Fren.Core.Meaning.Program) x vs =>
  Meaning.toValue ((Fren.Core.Meaning.Definition.value (Fren.Core.Meaning.Program.definition p x) (Meaning.ofValues vs)).getD .nil)
interp lang::fixed_specified? := fun (p : Fren.Core.Meaning.Program) h vs =>
  fixedSpecified (pctx p) (Meaning.ofHead h) (Meaning.ofValues vs)
interp lang::fixed_value := fun (p : Fren.Core.Meaning.Program) h vs => Meaning.toValue (fixedValue (pctx p) (Meaning.ofHead h) (Meaning.ofValues vs))
interp lang::construct := fun c vs => Meaning.toValue (Fren.Core.Meaning.construct c (Meaning.ofValues vs))
interp lang::arm_matches? := fun (p : Fren.Core.Meaning.Program) h i v => armMatches (pctx p) (Meaning.ofHead h) i (Meaning.ofValue v)
interp lang::later_unevaluated := fun (p : Fren.Core.Meaning.Program) h vs => Fren.FinSet.ofList (laterUnevaluated (pctx p) (Meaning.ofHead h) (Meaning.ofValues vs))
-- The value of one layer, `Fren.Core.Meaning.step`, which its postcondition
-- determines.
interp lang::step := fun (p : Fren.Core.Meaning.Program) h (e : Fren.Core.Meaning.Env) vs =>
    Meaning.toValue (Fren.Core.Meaning.step (pctx p) (Meaning.ofHead h) e (Meaning.ofValues vs)) by
  intro p h e vs
  rw [← Meaning.toHead_ofHead h, ← Meaning.toValues_ofValues vs]
  generalize Meaning.ofHead h = h
  generalize Meaning.ofValues vs = l
  unfold lang.step.layer
  simp only [Meaning.ofHead_toHead, Meaning.ofValues_toValues, Meaning.ofValue_toValue, Meaning.part_toValues,
    lang.lookup, lang.meaning, lang.unspecified, lang.fixed_value, lang.fixed_specified?, lang.construct,
    lang.arm_matches?]
  cases h
  case op o s =>
    have o2 : lang.arm_open? (lang.Head.Op o s) (Meaning.toValues l) 2
        (armMatches (pctx p) (.op o s) 2 (Fren.Core.Meaning.part l 0))
        = armOpen (pctx p) (.op o s) l 2 := Meaning.armOpen_op o s l 2
    have o1 : lang.arm_open? (lang.Head.Op o s) (Meaning.toValues l) 1
        (armMatches (pctx p) (.op o s) 1 (Fren.Core.Meaning.part l 0))
        = armOpen (pctx p) (.op o s) l 1 := Meaning.armOpen_op o s l 1
    have o0 : lang.arm_open? (lang.Head.Op o s) (Meaning.toValues l) 0
        (armMatches (pctx p) (.op o s) 0 (Fren.Core.Meaning.part l 0))
        = armOpen (pctx p) (.op o s) l 0 := Meaning.armOpen_op o s l 0
    have f := fun (k : Nat) (hk : k < 3) => Meaning.fires_toValues (ctx := pctx p) (.op o s) l k hk
    have f0 : lang.fires_at? (Meaning.toValues l) _ _ _ 0 = _ := f 0 (by omega)
    have f1 : lang.fires_at? (Meaning.toValues l) _ _ _ 1 = _ := f 1 (by omega)
    have f2 : lang.fires_at? (Meaning.toValues l) _ _ _ 2 = _ := f 2 (by omega)
    simp only [Meaning.toHead, lang.Head.Op.x0, lang.Head.Op.x1, reduceCtorEq, if_true, if_false,
      o0, o1, o2, f0, f1, f2, Meaning.connective_eq, Meaning.choice_eq, Meaning.total_eq,
      Meaning.connectiveValue_toValues, Meaning.moreArms_op, Meaning.ofValues_empty, Fren.Core.Meaning.step_op, apply_ite Meaning.toValue]
    simp [lang.guard_at, Fren.Core.Meaning.armBody, Fren.Core.Meaning.guardAt]
  case constant c =>
    by_cases hs : fixedSpecified (pctx p) (.constant c) l
    · simp [Meaning.toHead, Fren.Core.Meaning.step, hs, Meaning.fixedValue_constant p c l hs, lang.declared,
        lang.definition_value, lang.Head.Constant.x0]
    · simp [Meaning.toHead, Fren.Core.Meaning.step, hs, lang.Head.Constant.x0]
  case defined f =>
    by_cases hs : fixedSpecified (pctx p) (.defined f) l
    · simp [Meaning.toHead, Fren.Core.Meaning.step, hs, Meaning.fixedValue_defined p f l, lang.declared,
        lang.definition_value, lang.Head.Defined.x0, lang.Head.Constant.x0]
    · simp [Meaning.toHead, Fren.Core.Meaning.step, hs, lang.Head.Defined.x0, lang.Head.Constant.x0]
  all_goals simp [Meaning.toHead, Fren.Core.Meaning.step, lang.Head.Literal.x0, lang.Head.Bound.x0,
    lang.Head.Variable.x0, lang.Head.Definition.x0, lang.Head.Construction.x0, lang.Head.Construction.x1,
    lang.Head.Uninterpreted.x0, apply_ite Meaning.toValue]

-- For every layer and parts' values: which arms of a choice are open and
-- fire, and which of their guards and bodies are not evaluated, by
-- `Fren.Core.Meaning`'s rule over every arm.
impl choice_arms: lang::choice_arms for (p : Fren.Core.Meaning.Program) (h : Fren.Core.Meaning.Head)
    (l : List Fren.Core.Meaning.Value) {
  program := p,
  head := Meaning.toHead h,
  values := Meaning.toValues l,
  open0? := armOpen (pctx p) h l 0,
  open1? := armOpen (pctx p) h l 1,
  open2? := armOpen (pctx p) h l 2,
  fired0? := armFires (pctx p) h l 0,
  fired1? := armFires (pctx p) h l 1,
  fired2? := armFires (pctx p) h l 2,
  specified? := (firstFired (pctx p) h l).isSome,
  stated := Fren.FinSet.ofList (statedUnevaluated (pctx p) h l),
  unevaluated := Fren.FinSet.ofList (choiceUnevaluated (pctx p) h l),
} by
  intro p h l _
  open Fren.Core.Meaning in
  refine ⟨.ArmGuard, .B (armOpen (pctx p) h l 0), armOpen (pctx p) h l 0, armOpen (pctx p) h l 0,
    .ArmBody, .B (armFires (pctx p) h l 0), armFires (pctx p) h l 0, armFires (pctx p) h l 0,
    .ArmGuard, .B (decide (armOpen (pctx p) h l 1 = true ∧ ¬armFires (pctx p) h l 0 = true)),
      decide (armOpen (pctx p) h l 1 = true ∧ ¬armFires (pctx p) h l 0 = true), decide (armOpen (pctx p) h l 1 = true ∧ ¬armFires (pctx p) h l 0 = true),
    .ArmBody, .B (armFires (pctx p) h l 1), armFires (pctx p) h l 1, armFires (pctx p) h l 1,
    .ArmGuard, .B (decide ((armOpen (pctx p) h l 2 = true ∧ ¬armFires (pctx p) h l 0 = true) ∧ ¬armFires (pctx p) h l 1 = true)),
      decide ((armOpen (pctx p) h l 2 = true ∧ ¬armFires (pctx p) h l 0 = true) ∧ ¬armFires (pctx p) h l 1 = true),
      decide ((armOpen (pctx p) h l 2 = true ∧ ¬armFires (pctx p) h l 0 = true) ∧ ¬armFires (pctx p) h l 1 = true),
    .ArmBody, .B (armFires (pctx p) h l 2), armFires (pctx p) h l 2, armFires (pctx p) h l 2, ?_⟩
  have o0 : lang.arm_open? (Meaning.toHead h) (Meaning.toValues l) 0
      (armMatches (pctx p) h 0 (Fren.Core.Meaning.part l 0)) = armOpen (pctx p) h l 0 := by
    simpa [Meaning.part_toValues] using Meaning.armOpen_toValues h l 0
  have o1 : lang.arm_open? (Meaning.toHead h) (Meaning.toValues l) 1
      (armMatches (pctx p) h 1 (Fren.Core.Meaning.part l 0)) = armOpen (pctx p) h l 1 := by
    simpa [Meaning.part_toValues] using Meaning.armOpen_toValues h l 1
  have o2 : lang.arm_open? (Meaning.toHead h) (Meaning.toValues l) 2
      (armMatches (pctx p) h 2 (Fren.Core.Meaning.part l 0)) = armOpen (pctx p) h l 2 :=
    Meaning.armOpen_toValues h l 2 ▸ by simp [Meaning.part_toValues]
  have f := fun (k : Nat) (hk : k < 3) => Meaning.fires_toValues (ctx := pctx p) h l k hk
  have f0 : lang.fires_at? (Meaning.toValues l) _ _ _ 0 = _ := f 0 (by omega)
  have f1 : lang.fires_at? (Meaning.toValues l) _ _ _ 1 = _ := f 1 (by omega)
  have f2 : lang.fires_at? (Meaning.toValues l) _ _ _ 2 = _ := f 2 (by omega)
  simp only [lang.choice_arms.defs, lang.choice_arms.def.open0?, lang.choice_arms.def.open1?,
    lang.choice_arms.def.open2?, lang.choice_arms.def.fired0?, lang.choice_arms.def.fired1?,
    lang.choice_arms.def.fired2?, lang.choice_arms.def.specified?, lang.choice_arms.def.stated,
    lang.choice_arms.def.unevaluated, lang.choice_arms.ensures, lang.choice_arms.inst.guard0,
    lang.choice_arms.inst.body0, lang.choice_arms.inst.guard1, lang.choice_arms.inst.body1,
    lang.choice_arms.inst.guard2, lang.choice_arms.inst.body2, lang.guard.defs, lang.guard.def.holds?,
    lang.guard.assumes, lang.guard.ensures, lang.guard.ensure.rule, lang.arm_matches?, lang.fixed_specified?,
    lang.later_unevaluated, Meaning.ofHead_toHead, Meaning.ofValues_toValues, Meaning.ofValue_toValue,
    Meaning.part_toValues, o0, o1, o2, f0, f1, f2, Meaning.moreArms, lang.Value.B.injEq, decide_eq_true_eq,
    true_and, and_self, reduceCtorEq]
  have u0 : FinSet.ofList (armUnevaluated (pctx p) h l 0) = lang.unevaluated_arm 0 _ _ :=
    Meaning.armUnevaluated_eq h l 0
  have u1 : FinSet.ofList (armUnevaluated (pctx p) h l 1) = lang.unevaluated_arm 1 _ _ :=
    Meaning.armUnevaluated_eq h l 1
  have u2 : FinSet.ofList (armUnevaluated (pctx p) h l 2) = lang.unevaluated_arm 2 _ _ :=
    Meaning.armUnevaluated_eq h l 2
  simp only [Fren.Core.Meaning.noneBefore_zero, Fren.Core.Meaning.noneBefore_one, Fren.Core.Meaning.noneBefore_two,
    Bool.and_true] at u0 u1 u2
  have stated : FinSet.ofList (statedUnevaluated (pctx p) h l) =
      lang.unevaluated_arm 0 (armOpen (pctx p) h l 0) (armFires (pctx p) h l 0)
        ∪ lang.unevaluated_arm 1 (decide (armOpen (pctx p) h l 1 = true ∧ ¬armFires (pctx p) h l 0 = true))
          (armFires (pctx p) h l 1)
        ∪ lang.unevaluated_arm 2
          (decide ((armOpen (pctx p) h l 2 = true ∧ ¬armFires (pctx p) h l 0 = true)
            ∧ ¬armFires (pctx p) h l 1 = true)) (armFires (pctx p) h l 2) := by
    rw [Fren.Core.Meaning.statedUnevaluated, Meaning.ofList_append, Meaning.ofList_append, u0, u1, u2]
    simp [Bool.and_assoc]
  refine ⟨⟨?_, stated, ?_⟩, ?_⟩
  · rw [Fren.Core.Meaning.firstFired_isSome]
    simp [Bool.or_assoc]
  · rw [Fren.Core.Meaning.choiceUnevaluated, Meaning.ofList_append, stated]
    congr 1
    split
    · apply FinSet.ext; intro k
      simp only [FinSet.mem_ofList, FinSet.mem_sdiff, FinSet.mem_insert, FinSet.mem_singleton]
      constructor
      · intro hk
        have := Fren.Core.Meaning.le_of_mem_laterUnevaluated hk
        exact ⟨hk, by omega⟩
      · exact And.left
    · rfl
  · simp

-- For every layer, environment, parts' values, and what the parts mention and
-- which are not defined: one layer's value, what it reads and mentions,
-- whether it is specified, which parts it does not evaluate, and whether it
-- is defined, all by `Fren.Core.Meaning`. Its instance `arms` is the
-- implementation of `lang::choice_arms` above.
impl node: lang::node for (p : Fren.Core.Meaning.Program) (h : Fren.Core.Meaning.Head) (e : Fren.Core.Meaning.Env)
    (l : List Fren.Core.Meaning.Value) (pm : List Fren.Core.Mention) (up : List Int) {
  program := p,
  head := Meaning.toHead h,
  env := e,
  values := Meaning.toValues l,
  parts_mentioned := mentionSet pm,
  undefined_parts := Fren.FinSet.ofList up,
  value := Meaning.toValue (Fren.Core.Meaning.step (pctx p) h e l),
  mentioned := mentionSet (Fren.Core.Meaning.mentionedBy h pm),
  mentions? := !(Fren.Core.Meaning.mentionedBy h pm).isEmpty,
  read := Meaning.toValue (Fren.Core.Meaning.read h e l),
  specified? := Fren.Core.Meaning.specified (pctx p) h l,
  unevaluated := Fren.FinSet.ofList (Fren.Core.Meaning.unevaluated (pctx p) h l),
  defined? := Fren.Core.Meaning.defined (pctx p) h l up,
} by
  intro p h e l pm up _
  obtain ⟨g0o, g0c, g0h, g0e, b0o, b0c, b0h, b0e, g1o, g1c, g1h, g1e, b1o, b1c, b1h, b1e,
    g2o, g2c, g2h, g2e, b2o, b2c, b2h, b2e, harms⟩ := choice_arms p h l trivial
  open Fren.Core.Meaning in
  refine ⟨lang.second_guard (lang.operator (Meaning.toHead h)), lang.part (Meaning.toValues l) 0,
    decide (lang.part (Meaning.toValues l) 0 = .B true), evaluated (secondGuard h.operator) (part l 0),
    .ElseBranch, lang.part (Meaning.toValues l) 0,
    decide (lang.part (Meaning.toValues l) 0 = .B true), evaluated .elseBranch (part l 0),
    p, Meaning.toHead h, Meaning.toValues l, armOpen (pctx p) h l 0, armOpen (pctx p) h l 1, armOpen (pctx p) h l 2,
    armFires (pctx p) h l 0, armFires (pctx p) h l 1, armFires (pctx p) h l 2, (firstFired (pctx p) h l).isSome,
    Fren.FinSet.ofList (statedUnevaluated (pctx p) h l), Fren.FinSet.ofList (choiceUnevaluated (pctx p) h l),
    g0o, g0c, g0h, g0e, b0o, b0c, b0h, b0e, g1o, g1c, g1h, g1e, b1o, b1c, b1h, b1e,
    g2o, g2c, g2h, g2e, b2o, b2c, b2h, b2e, ?_, trivial, ?_, ?_, ⟨⟨rfl, rfl, rfl⟩, harms.1, trivial, harms.2⟩⟩
  · simp only [lang.node.defs, lang.node.def.value, lang.node.def.mentioned, lang.node.def.mentions?,
      lang.node.def.read, lang.node.def.specified?, lang.node.def.unevaluated, lang.node.def.defined?, lang.step,
      lang.lookup, lang.meaning, Meaning.ofHead_toHead, Meaning.ofValues_toValues, Meaning.mentionedBy_eq,
      lang.fixed_specified?, Meaning.read_eq, Meaning.specified_eq, Meaning.unevaluated_eq]
    simp only [mentionSet, defined, Fren.FinSet.subset_def, true_and, Fren.FinSet.mem_ofList,
      ne_eq, Fren.FinSet.ofList_eq_empty, List.map_eq_nil_iff]
    refine ⟨?_, ?_⟩
    · cases Fren.Core.Meaning.mentionedBy h pm <;> simp
    · congr 1; rw [Bool.eq_iff_iff]; simp [List.all_eq_true]
  · refine ⟨⟨rfl, rfl⟩, rfl, trivial, ?_⟩
    simpa [Meaning.part_toValues, Meaning.operator_toHead, Meaning.secondGuard_eq] using
      Meaning.guard_rule (Fren.Core.Meaning.secondGuard h.operator) (lang.part (Meaning.toValues l) 0)
  · refine ⟨⟨rfl, rfl⟩, rfl, trivial, ?_⟩
    simpa [Meaning.part_toValues, toGuardedOperand] using
      Meaning.guard_rule .elseBranch (lang.part (Meaning.toValues l) 0)

-- The `impl`s above prove the spec of a layer consistent with
-- `Fren.Core.Meaning`, which no front end evaluates through yet: that Fren
-- follows the model is trusted until they do.
trusted lang::node: "proved of `Fren.Core.Meaning` by `impl node`, but no front end evaluates through `Fren.Core.Meaning` yet, so that Fren's evaluation follows this model is trusted until both do; `fren_test`'s `evaluation` job tests the binary's evaluator against it on integers and `Bool`s (#281)"
trusted lang::choice_arms: "proved of `Fren.Core.Meaning` by `impl choice_arms`, but no front end evaluates through `Fren.Core.Meaning` yet, so that Fren's evaluation of a choice follows this model is trusted until both do (#281)"

end Fren.Impls
