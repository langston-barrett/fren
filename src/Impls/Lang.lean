-- keep-sorted start
import FrenCli.Lex
import FrenCore.Checking
import FrenCore.Guards
import FrenCore.Patterns
import FrenCore.Ty
import FrenCore.Typing
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Language rules (`Reqs/Lang`) -/

namespace Fren.Impls

/-- The type written for a variable: `none` if none is, else whether it is
`Bool`. -/
def isBool? : lang.Annot → Option Bool
  | .Missing => none
  | .BoolTy => some true
  | .IntTy | .NatTy | .StringTy | .NamedTy => some false

-- For every name: `checkVarName` reads the suffix from the name itself, with
-- the meaning of `ends_with?` that Fren fixes.
impl bool_naming: lang::bool_naming for (s : String) (a : lang.Annot) {
  name := s,
  annot := a,
  accepted? := (Fren.Core.checkVarName (.mkSimple s) (isBool? a)).isOk,
} by
  intro s a _
  have hs : Fren.Core.nameText (.mkSimple s) = s := rfl
  cases h : Fren.Str.endsWith s "?" <;> cases a <;>
    simp [fren_spec, Fren.Core.checkVarName, Fren.Core.checkVarKind, isBool?, hs, h, Except.isOk, Except.toBool] <;> rfl

def toExprKind : Fren.Core.MentionKind → lang.ExprKind
  | .literal => .Literal
  | .constant => .Constant
  | .variable => .Variable
  | .definedOutput => .DefinedOutput
  | .binder => .Binder
  | .construction => .Construction
  | .method => .Method
  | .uninterpreted => .Uninterpreted
  | .defined => .Defined
  | .compound => .Compound

-- For every expression's shape: the decision for each kind, and the walk over
-- a shape that both front ends decide by. That each front end classifies its
-- syntax into the right kinds is not proved here, but tested by both on the
-- same ui tests.
impl mentions: lang::mentions for (k : Fren.Core.MentionKind) (ps : List Fren.Core.MentionShape) {
  expr_kind := toExprKind k,
  parts? := Fren.Core.MentionShape.anyMentions ps,
  mentions? := (Fren.Core.MentionShape.node k ps).mentions,
} by
  intro k ps _
  cases k <;> simp [fren_spec, toExprKind, Fren.Core.MentionShape.mentions, Fren.Core.kindMentions]

def toGuardedOperand : Fren.Core.GuardedOperand → lang.GuardedOperand
  | .whenBody => .WhenBody
  | .unlessBody => .UnlessBody
  | .thenBranch => .ThenBranch
  | .elseBranch => .ElseBranch
  | .andRight => .AndRight
  | .orRight => .OrRight
  | .armBody => .ArmBody

-- For every operand and condition: the guard that both front ends add, by
-- `GuardedOperand.guard`, here over the condition's truth. That each front
-- end calls it with the right operand is not proved here, but tested by both
-- on the same ui tests.
impl guard: lang::guard for (o : Fren.Core.GuardedOperand) (h : Bool) {
  operand := toGuardedOperand o,
  holds? := h,
  evaluated? := o.guard h (!h),
} by
  intro o h _
  cases o <;> cases h <;>
    simp [fren_spec, toGuardedOperand, Fren.Core.GuardedOperand.guard, Fren.Core.GuardedOperand.whenHolds]

def toPosition : Fren.Core.Position → lang.Position
  | .declared => .Declared
  | .shared => .Shared
  | .compared => .Compared
  | .synthesized => .Synthesized

-- For every position: the decision that both front ends make for each part
-- of an expression. That each classifies its syntax into the right positions
-- and shapes is not proved here, but tested by both on the same ui tests.
impl checked: lang::checked for (p : Fren.Core.Position) (e s : Bool) {
  position := toPosition p,
  expected? := e,
  sibling? := s,
  checked? := p.checked e s,
} by
  intro p e s _
  cases p <;> cases e <;> cases s <;> simp [fren_spec, toPosition, Fren.Core.Position.checked]

def toShape : Fren.Core.TypeShape → lang.Shape
  | .emptyLiteral => .EmptyLiteral
  | .anyPart _ => .SharedParts
  | .pair .. => .Pair
  | .other => .Other

/-- The shared parts of an expression of shape `s`, or a pair's members. -/
def shapeParts : Fren.Core.TypeShape → List Fren.Core.TypeShape
  | .anyPart ps => ps
  | .pair a b => [a, b]
  | .emptyLiteral | .other => []

theorem anySynthesizes_eq_any (ps : List Fren.Core.TypeShape) :
    Fren.Core.TypeShape.anySynthesizes ps = ps.any Fren.Core.TypeShape.synthesizes := by
  induction ps with
  | nil => simp [Fren.Core.TypeShape.anySynthesizes]
  | cons p ps ih => simp [Fren.Core.TypeShape.anySynthesizes, ih]

-- For every shape, with its parts' own decisions: the walk that both front
-- ends decide by.
impl synthesizes: lang::synthesizes for (s : Fren.Core.TypeShape) {
  shape := toShape s,
  parts := ((shapeParts s).length : Int),
  synthesizing := ((shapeParts s).filter Fren.Core.TypeShape.synthesizes).length,
  synthesizes? := s.synthesizes,
} by
  intro s _
  cases s with
  | emptyLiteral => simp [fren_spec, toShape, Fren.Core.TypeShape.synthesizes]
  | other => simp [fren_spec, toShape, Fren.Core.TypeShape.synthesizes]
  | pair a b =>
    cases ha : a.synthesizes <;> cases hb : b.synthesizes <;>
      simp [fren_spec, toShape, shapeParts, Fren.Core.TypeShape.synthesizes, ha, hb, List.filter]
  | anyPart ps =>
    simp only [fren_spec, toShape, shapeParts, Fren.Core.TypeShape.synthesizes, anySynthesizes_eq_any]
    cases h : ps.any Fren.Core.TypeShape.synthesizes <;>
      simp_all [List.any_eq_false, List.any_eq_true, List.filter_eq_nil_iff, List.length_pos_iff]

impl linear_product: lang::linear_product for (a b : Bool) {
  a_mentions? := a,
  b_mentions? := b,
  accepted? := Fren.Core.productAccepted a b,
} by
  intro a b _
  cases a <;> cases b <;> simp [fren_spec, Fren.Core.productAccepted]

def toDivisorForm : Fren.Core.DivisorForm → lang.DivisorForm
  | .literal => .LiteralDivisor
  | .knownConstant => .KnownConstant
  | .unknownConstant => .UnknownConstant
  | .other => .OtherDivisor

-- For every divisor, by the form and value that both front ends give
-- `Fren.Core.checkDivisor`.
impl divisor: lang::divisor for (f : Fren.Core.DivisorForm) (v : Int) {
  form := toDivisorForm f,
  value := v,
  accepted? := Fren.Core.divisorAccepted f v,
} by
  intro f v _
  cases f <;> simp [fren_spec, toDivisorForm, Fren.Core.divisorAccepted]

interp lang::Ty := Fren.Core.Ty

theorem join_eq_wider (tx ty : Fren.Core.Ty) : tx.join ty = if tx.widens ty then ty else tx := by
  unfold Fren.Core.Ty.join Fren.Core.Ty.widens
  by_cases h : tx = ty <;> by_cases ha : tx = .nat <;> by_cases hb : ty = .int <;> simp_all

theorem checkType_isOk (e f : Fren.Core.Ty) (why : Option String) :
    (Fren.Core.checkType e f why).isOk = f.widens e := by
  by_cases h : f.widens e = true <;>
    simp_all [Fren.Core.checkType, Except.isOk, Except.toBool, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

theorem checkArm_isOk (b a : Fren.Core.Ty) :
    (Fren.Core.checkArm (some b) a).isOk = (a.widens b || b.widens a) := by
  by_cases h : (a.widens b || b.widens a) = true <;>
    simp_all [Fren.Core.checkArm, Except.isOk, Except.toBool, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]

theorem checkType_bool_isOk (c : Fren.Core.Ty) : (Fren.Core.checkType .bool c).isOk = (c == .bool) := by
  by_cases hc : c = .bool <;>
    simp [Fren.Core.checkType, Fren.Core.Ty.widens, hc, Except.isOk, Except.toBool, pure, Except.pure, throw,
      throwThe, MonadExceptOf.throw]

theorem checkBranches_isOk (tx ty : Fren.Core.Ty) :
    (Fren.Core.checkBranches tx ty).isOk = (tx.widens ty || ty.widens tx) := by
  by_cases h : (tx.widens ty || ty.widens tx) = true <;>
    simp_all [Fren.Core.checkBranches, Except.isOk, Except.toBool, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

-- For every type of the condition and the branches: the checks that both
-- front ends make (`Core.checkType` and `Core.checkBranches`), and the type
-- that the `fren` command gives the conditional (`Ty.join`).
impl conditional: lang::conditional for (c tx ty : Fren.Core.Ty) {
  condition_bool? := c == .bool,
  then_ty := tx,
  else_ty := ty,
  then_widens? := tx.widens ty,
  else_widens? := ty.widens tx,
  accepted? := (Fren.Core.checkType .bool c).isOk && (Fren.Core.checkBranches tx ty).isOk,
  ty := tx.join ty,
} by
  intro c tx ty _
  simp [fren_spec, checkType_bool_isOk, checkBranches_isOk, join_eq_wider]

/-- What is expected of an empty literal (`lang::Expected`). -/
def toExpected : Option Fren.Core.Ty → lang.Expected
  | none => .NoType
  | some (.set _) | some (.rel ..) => .SetOrRelation
  | some (.seq _) => .Sequence
  | some _ => .NotCollection

/-- The outcome of `Core.checkEmptyLiteral` (`lang::EmptyOutcome`): an error
whose code is `F0324` is a type that cannot be known. -/
def toEmptyOutcome : Except Fren.Core.Msg Fren.Core.Ty → lang.EmptyOutcome
  | .ok _ => .Typed
  | .error m => if m.code? == some "F0324" then .Unknown else .OtherKind

-- For each empty literal and every type expected of it, or none, by the
-- check that both front ends make (`Core.checkEmptyLiteral`).
impl empty_literal: lang::empty_literal for (seq : Bool) (t? : Option Fren.Core.Ty) {
  seq? := seq,
  expected := toExpected t?,
  outcome := toEmptyOutcome (Fren.Core.checkEmptyLiteral seq t?),
} by
  intro seq t? _
  rcases t? with _ | t
  · cases seq <;> simp [fren_spec, toExpected, toEmptyOutcome, Fren.Core.checkEmptyLiteral, throw, throwThe,
      MonadExceptOf.throw, Fren.Core.emptySetTypeMsg, Fren.Core.emptySeqTypeMsg]
  · cases seq <;> cases t <;> simp [fren_spec, toExpected, toEmptyOutcome, Fren.Core.checkEmptyLiteral, throw,
      throwThe, MonadExceptOf.throw, pure, Except.pure, Fren.Core.emptySetTypeMsg, Fren.Core.emptySeqTypeMsg,
      Fren.Core.emptyKindMsg]

-- For every type of an arm and of the arms before it: the check that both
-- front ends make (`Core.checkArm`), and the type that it gives the arms so
-- far (`Ty.join`).
impl arm_type: lang::arm_type for (b a : Fren.Core.Ty) {
  before := b,
  arm := a,
  arm_widens? := a.widens b,
  before_widens? := b.widens a,
  accepted? := (Fren.Core.checkArm (some b) a).isOk,
  ty := b.join a,
} by
  intro b a _
  simp [fren_spec, checkArm_isOk, join_eq_wider]

-- For every application, over the types that the `fren` command compares.
impl application: lang::application for (ps as : Array Fren.Core.Ty) (k : Int) {
  params := Fren.Seq.ofList ps.toList,
  args := Fren.Seq.ofList as.toList,
  k := k,
  accepted? := Fren.Core.applicationAccepted ps as,
} by
  intro ps as k _
  simp [fren_spec, Fren.Core.applicationAccepted, Fren.Seq.ext_iff]

/-- The kind of a type (`lang::kind`). -/
def kindOf : Fren.Core.Ty → lang.ValueType
  | .bool => .BoolTy
  | .int => .IntTy
  | .nat => .NatTy
  | .string => .StringTy
  | .set _ => .SetTy
  | .rel .. => .RelTy
  | .seq _ => .SeqTy
  | .enum _ => .EnumTy
  | .record _ => .RecordTy
  | .abstract _ => .AbstractTy
  -- A newtype is a record (`Reqs/Lang/Items#newtypes`).
  | .newtype _ _ => .RecordTy

interp lang::kind := kindOf

interp lang::newtype? := fun (t : Fren.Core.Ty) => t matches .newtype ..

/-- The underlying type of a newtype, and any other type itself. -/
def underOf : Fren.Core.Ty → Fren.Core.Ty
  | .newtype _ u => u
  | t => t

interp lang::under := underOf

-- For every two types, with the check that both front ends make wherever a
-- type is declared (`Core.checkType`).
impl widening: lang::widening for (f e : Fren.Core.Ty) {
  found := f,
  expected := e,
  accepted? := (Fren.Core.checkType e f).isOk,
} by
  intro f e _
  rw [checkType_isOk]
  cases f <;> cases e <;> simp [fren_spec, Fren.Core.Ty.widens, kindOf]

impl literal_type: lang::literal_type for (b : Bool) {
  nat_expected? := b,
  result := kindOf (Fren.Core.literalTy b),
} by
  intro b _
  cases b <;> simp [fren_spec, Fren.Core.literalTy, kindOf]

def toNatOp : Fren.Core.NatOp → lang.NatOp
  | .div => .Div
  | .mod => .Mod
  | .min => .Min
  | .max => .Max
  | .abs => .Abs

impl nat_result: lang::nat_result for (op : Fren.Core.NatOp) (a b p : Bool) {
  op := toNatOp op,
  a_nat? := a,
  b_nat? := b,
  positive? := p,
  nat? := Fren.Core.natResult op a b p,
} by
  intro op a b p _
  cases op <;> cases a <;> cases b <;> cases p <;> simp [fren_spec, toNatOp, Fren.Core.natResult]

def toTypePlace : Fren.Core.TypePlace → lang.TypePlace
  | .variable => .Variable
  | .parameter => .Parameter
  | .result => .Result
  | .constant => .Constant
  | .definition => .Definition
  | .field => .Field
  | .payload => .Payload
  | .element => .Element

impl nat_place: lang::nat_place for (p : Fren.Core.TypePlace) {
  place := toTypePlace p,
  accepted? := Fren.Core.natPlaceAccepted p,
} by
  intro p _
  cases p <;> simp [fren_spec, toTypePlace, Fren.Core.natPlaceAccepted]

def toBrought : Fren.Core.Brought → lang.Brought
  | .nothing => .Nothing
  | .assumption => .Assumption
  | .requirement => .Requirement

impl nat_variable: lang::nat_variable for (o d : Bool) {
  own_output? := o,
  defined? := d,
  brought := toBrought (Fren.Core.natBrought o d),
} by
  intro o d _
  cases o <;> cases d <;> simp [fren_spec, toBrought, Fren.Core.natBrought]

impl constant: lang::constant for (t : lang.ValueType) (a : Bool) {
  ty := t,
  applies? := a,
  accepted? := Fren.Core.constantAccepted (t == .AbstractTy) a,
}

impl field_type: lang::field_type for (k : lang.ValueType) (a own s pay : Bool) {
  kind := k,
  abstract_within? := a,
  own? := own,
  own_in_set? := s,
  payload? := pay,
  accepted? := Fren.Core.fieldTypeAccepted a own s pay,
} by
  intro k a own s pay _
  cases a <;> cases own <;> cases s <;> cases pay <;> simp [fren_spec, Fren.Core.fieldTypeAccepted]

-- For every newtype, with the check that both front ends use, and how
-- both decide its boundedness.
impl newtype: lang::newtype for (n : Nat) (f u : Bool) {
  n_fields := n,
  field_accepted? := f,
  underlying_unbounded? := u,
  accepted? := Fren.Core.newtypeAccepted n f,
  unbounded? := Fren.Core.newtypeUnbounded u,
} by
  intro n f u _
  simp [fren_spec, Fren.Core.newtypeAccepted, Fren.Core.newtypeUnbounded]
  omega

def toNewtypeOp : Fren.Core.NewtypeOp → lang.NewtypeOp
  | .equality => .Equality
  | .order => .Order
  | .sum => .Sum
  | .other => .Other

-- For every operator and underlying type, with the check that both front
-- ends use.
impl newtype_operator: lang::newtype_operator for (op : Fren.Core.NewtypeOp) (u : Fren.Core.Ty) (o : Bool) {
  op := toNewtypeOp op,
  underlying := kindOf u,
  ordered? := o && u matches .enum _,
  accepted? := Fren.Core.newtypeOpAccepted op u o,
} by
  intro op u o _
  cases op <;> cases u <;> cases o <;> simp [fren_spec, toNewtypeOp, kindOf, Fren.Core.newtypeOpAccepted]

/-- The variants of `vs` for which `p` holds are all of them exactly when
there are as many. -/
theorem ofList_filter_eq (vs : List Lean.Name) (p : Lean.Name → Bool) :
    Fren.FinSet.ofList (vs.filter p) = Fren.FinSet.ofList vs ↔ (vs.filter p).length = vs.length := by
  rw [Fren.FinSet.ext_iff]
  simp only [Fren.FinSet.mem_ofList, List.mem_filter]
  have hle := List.length_filter_le p vs
  have hlt := @List.length_filter_lt_length_iff_exists _ p vs
  constructor
  · intro h
    have : ¬ (vs.filter p).length < vs.length := fun hl =>
      let ⟨x, hx, hp⟩ := hlt.mp hl; hp ((h x).mpr hx).2
    omega
  · intro h x
    refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
    cases hp : p x
    · have := hlt.mpr ⟨x, hx, by simp [hp]⟩
      omega
    · rfl

interp lang::VariantName := Lean.Name

-- For every enumeration, its variants `vs` and which are recursive, `p`,
-- with the count that both front ends compare.
impl well_founded: lang::well_founded for (vs : List Lean.Name) (p : Lean.Name → Bool) {
  variants := Fren.FinSet.ofList vs,
  recursive := Fren.FinSet.ofList (vs.filter p),
  accepted? := Fren.Core.wellFounded vs.length (vs.filter p).length,
} by
  intro vs p _
  simp [fren_spec, Fren.Core.wellFounded, ofList_filter_eq]

-- For every enumeration, whether it is ordered and how many of its variants
-- have a payload, which both front ends give `Fren.Core.orderedEnumAccepted`.
impl ordered_enumeration: lang::ordered_enumeration for (o : Bool) (n : Nat) {
  ordered? := o,
  n_payloads := n,
  accepted? := Fren.Core.orderedEnumAccepted o n,
} by
  intro o n _
  cases o <;> simp [fren_spec, Fren.Core.orderedEnumAccepted]

interp lang::FieldName := Lean.Name

-- For every literal, with the check that both front ends use.
impl record_literal: lang::record_literal for (fields given : Array Lean.Name) {
  fields := Fren.FinSet.ofArray fields,
  given := Fren.FinSet.ofArray given,
  n_repeated := Fren.Core.repeatsOf given,
  accepted? := Fren.Core.recordLiteralAccepted fields given,
} by
  intro fields given _
  have : Fren.FinSet.ofArray given = Fren.FinSet.ofArray fields ↔ (∀ g ∈ given, g ∈ fields) ∧ ∀ f ∈ fields, f ∈ given := by
    rw [Fren.FinSet.ext_iff]
    simp only [Fren.FinSet.mem_ofArray]
    exact ⟨fun h => ⟨fun g hg => (h g).mp hg, fun f hf => (h f).mpr hf⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩
  simp only [fren_spec, Fren.Core.recordLiteralAccepted, this, Bool.and_eq_true, Array.all_eq_true',
    Array.contains_iff_mem, beq_iff_eq]
  simp

-- For every update, whether the updated value is of a record, `r`, with
-- the check that both front ends use.
impl record_update: lang::record_update for (r : Bool) (fields given : Array Lean.Name) {
  record? := r,
  fields := Fren.FinSet.ofArray fields,
  given := Fren.FinSet.ofArray given,
  n_repeated := Fren.Core.repeatsOf given,
  accepted? := Fren.Core.recordUpdateAccepted r fields given,
} by
  intro r fields given _
  simp only [fren_spec, Fren.Core.recordUpdateAccepted, Fren.FinSet.subset_def, Fren.FinSet.mem_ofArray,
    Bool.and_eq_true, Array.all_eq_true', Array.contains_iff_mem, beq_iff_eq]
  simp

impl variable_type: lang::variable_type for (o u d : Bool) {
  output? := o,
  unbounded? := u,
  defined? := d,
  accepted? := Fren.Core.variableTypeAccepted o u d,
}

-- For every declaration: its name `n`, what it hides if anything (`w`, when
-- `h`), and whether it has `!`, through the check that both front ends call.
-- This proves the rule, given `hides?`, not that `hides?` is computed
-- correctly: `Table.hidden?`, `bindingLocals`, and a function's absence from
-- the table while its parameters are declared, which `o` stands for, are
-- tested (`test/ui/lang/shadowing_static.fren`), not proved.
impl shadowing: lang::shadowing for (n : Lean.Name) (w : String) (h b o : Bool) {
  hides? := h,
  bang? := b,
  own_function? := o,
  accepted? := (Fren.Core.checkShadowing n (if h then some w else none) b).isOk,
} by
  intro n w h b o _
  cases h <;> cases b <;>
    simp [fren_spec, Fren.Core.checkShadowing, Fren.Core.shadowingAccepted, Except.isOk, Except.toBool] <;> rfl

impl field_init: lang::field_init for (f : Bool) (n : Nat) {
  field? := f,
  n := n,
  accepted? := Fren.Core.fieldInitOk f n,
} by
  intro f n _
  cases f <;> simp [fren_spec, Fren.Core.fieldInitOk] <;> omega

-- For every `match`: the counts of the arms and alternatives that are not
-- useful, and whether it is exhaustive, which `checkMatch` decides by.
impl match_arms: lang::match_arms for (a b : Nat) (e : Bool) {
  n_useless_arms := a,
  n_useless_alternatives := b,
  exhaustive? := e,
  accepted? := Fren.Core.matchArmsAccepted (a + b) e,
} by
  intro a b e _
  cases e <;> simp [fren_spec, Fren.Core.matchArmsAccepted] <;> omega

-- For every pattern test: the counts that `checkPatternTest` decides by.
impl pattern_test: lang::pattern_test for (b u : Nat) (m : Bool) {
  n_bound := b,
  n_useless_alternatives := u,
  matches_some? := m,
  accepted? := Fren.Core.patternTestAccepted b u m,
} by
  intro b u m _
  cases m <;> simp [fren_spec, Fren.Core.patternTestAccepted]

/-! ## Patterns (`Reqs/Lang/Patterns`) -/

def toPatternName : Fren.Core.PatternName → lang.PatternName
  | .boolLiteral => .BoolLiteral
  | .variant => .Variant
  | .binder => .Binder

-- For every identifier of one segment, not applied, in a pattern: both
-- front ends and the evaluator read it with `patternName`.
impl pattern_name: lang::pattern_name for (w b v : Bool) {
  bool_word? := w,
  bang? := b,
  variant? := v,
  reading := toPatternName (Fren.Core.patternName w b v),
} by
  intro w b v _
  cases w <;> cases b <;> cases v <;> simp [fren_spec, toPatternName, Fren.Core.patternName]

-- For every range and integer: the bounds as `Option`s, as both front ends
-- and the evaluator read them.
impl range_pattern: lang::range_pattern for (hl : Bool) (l : Int) (hu : Bool) (u : Int) (inc : Bool) (v : Int) {
  has_lower? := hl,
  lower := l,
  has_upper? := hu,
  upper := u,
  inclusive? := inc,
  value := v,
  matches? := Fren.Core.rangeMatches (if hl then some l else none) (if hu then some u else none) inc v,
  empty? := Fren.Core.rangeEmpty (if hl then some l else none) (if hu then some u else none) inc,
} by
  intro hl l hu u inc v _
  cases hl <;> cases hu <;> cases inc <;> simp [fren_spec, Fren.Core.rangeMatches, Fren.Core.rangeEmpty]

def toHeadKind : Fren.Core.HeadKind → lang.HeadKind
  | .constructor => .Constructor
  | .wildcard => .Wildcard
  | .or => .Or

-- For every step of `useful`, which calls `usefulStep` with the smaller
-- problems as functions.
impl usefulness: lang::usefulness for (c r : Nat) (h : Fren.Core.HeadKind) (k sp ss d sa : Bool) {
  columns := c,
  rows := r,
  head := toHeadKind h,
  complete? := k,
  specialized? := sp,
  some_specialized? := ss,
  default? := d,
  some_alternative? := sa,
  useful? := Fren.Core.usefulStep c r h k (fun _ => sp) (fun _ => ss) (fun _ => d) (fun _ => sa),
} by
  intro c r h k sp ss d sa _
  cases h <;> cases k <;> by_cases hc : c = 0 <;>
    simp [fren_spec, toHeadKind, Fren.Core.usefulStep, hc] <;> omega

-- For every row's head and constructor, by the head's kind.
impl specialize: lang::specialize for (p : Fren.Core.Pat) (c : Fren.Core.Ctor) (a : Nat) {
  head := toHeadKind p.headKind,
  same? := p.sameCtor c,
  arity := a,
  n_args := p.args.length,
  kept? := (Fren.Core.specializeHead c a p).isSome,
  added := ((Fren.Core.specializeHead c a p).map (·.length)).getD 0,
} by
  intro p c a _
  simp only [Fren.Core.specializeHead]
  cases p.headKind <;> cases p.sameCtor c <;> simp [fren_spec, toHeadKind]

def toColumnType : Fren.Core.ColumnKind → lang.ColumnType
  | .enumeration => .EnumType
  | .boolean => .BoolType
  | .integer => .IntType
  | .string => .StringType
  | .other => .OtherType

-- For every column, as `columnCtors` decides it.
impl signature_complete: lang::signature_complete for (k : Fren.Core.ColumnKind) (n m : Nat) (t f i : Bool) {
  column := toColumnType k,
  n_variants := n,
  n_named := m,
  has_true? := t,
  has_false? := f,
  covers_integers? := i,
  complete? := Fren.Core.signatureComplete k n m t f i,
} by
  intro k n m t f i _
  cases k <;> simp [fren_spec, toColumnType, Fren.Core.signatureComplete] <;> omega

impl function_params: lang::function_params for (d : Bool) (p n : Nat) {
  defined? := d,
  n_params := p,
  n_named := n,
  accepted? := Fren.Core.functionParamsAccepted d p n,
} by
  intro d p n _
  cases d <;> simp [fren_spec, Fren.Core.functionParamsAccepted] <;> omega

def toCardinality : Fren.Core.Cardinality → lang.Cardinality
  | .exactlyOne => .Exactly
  | .atMostOne => .AtMost

-- For every operator and number of arguments that are `true`: the value that
-- the evaluator gives it. That both front ends' translations, a sum compared
-- with 1, agree with it is not proved here, but confirmed on the solver's
-- models and tested by both on the same ui tests.
impl cardinality: lang::cardinality for (c : Fren.Core.Cardinality) (n k : Nat) {
  op := toCardinality c,
  n_args := n,
  n_true := k,
  value? := c.holds k,
} by
  intro c n k _
  cases c <;> simp [fren_spec, toCardinality, Fren.Core.Cardinality.holds] <;> omega

-- For every chained comparison, by the counts of its operators' kinds that
-- `Fren.Core.checkChain`, which both front ends call, takes.
impl comparison_chain: lang::comparison_chain for (a d o : Nat) {
  n_ascending := a,
  n_descending := d,
  n_other := o,
  accepted? := Fren.Core.chainAccepted a d o,
} by
  intro a d o _
  simp [fren_spec, Fren.Core.chainAccepted] <;> omega

/-! ## Strings and decidability (`Reqs/Lang/Types#strings`, `Reqs/Lang/Decidability`) -/

impl string_char: lang::string_char for (c : Nat) {
  code := c,
  accepted? := Fren.Core.stringCharAccepted c,
} by
  intro c _
  simp [fren_spec, Fren.Core.stringCharAccepted, Fren.Core.maxChar]

-- With the pattern parser, which both front ends use.
impl char_range: lang::char_range for (lo hi : Int) {
  low := lo,
  high := hi,
  accepted? := Fren.Core.charRangeAccepted lo hi,
} by
  intro lo hi _
  simp [fren_spec, Fren.Core.charRangeAccepted]

instance : Fren.Finite Fren.Core.Method :=
  ⟨Fren.Core.Method.all.toList, by intro x; cases x <;> simp [Fren.Core.Method.all]⟩

def toMethod : Fren.Core.Method → lang.Method
  | .len => .Len
  | .startsWith => .StartsWith
  | .endsWith => .EndsWith
  | .contains => .Contains
  | .matches => .Matches
  | .at => .At
  | .slice => .Slice
  | .indexOf => .IndexOf
  | .replace => .Replace
  | .replaceAll => .ReplaceAll
  | .card => .Card
  | .inverse => .Inverse
  | .closure => .Closure
  | .image => .Image
  | .domain => .Domain
  | .range => .Range
  | .update => .Update
  | .rev => .Rev
  | .abs => .Abs
  | .min => .Min
  | .max => .Max

-- The table of methods that both front ends use, where `o` says that the
-- receiver is an ordered enumeration.
impl method_type: lang::method_type for (m : Fren.Core.Method) (k : lang.ValueType) (o : Bool) {
  method := toMethod m,
  receiver := k,
  ordered? := o,
  accepted? := m.accepts (k == .StringTy) (k == .SetTy) (k == .RelTy) (k == .SeqTy) (k == .IntTy || k == .NatTy) o,
  -- `string` is the receiver's type, and `elem` is never a result; an
  -- ordered enumeration's `min` and `max` give the receiver's type, as both
  -- front ends' `callMethod` does.
  result := if o && (m matches .min | .max) then k else match m.result with
    | .bool => .BoolTy | .int => .IntTy | .string | .elem => k | .set => .SetTy | .rel => .RelTy,
  n_params := m.arity,
} by
  intro m k o _
  cases m <;> cases k <;> cases o <;> simp [fren_spec, toMethod, Fren.Core.Method.accepts, Fren.Core.Method.relational,
    Fren.Core.Method.result,
    Fren.Core.Method.arity, Fren.Core.Method.params]

instance : Fren.Finite Fren.Core.Construct :=
  ⟨[.stringCompare, .stringAtom, .stringIndex, .stringSearch, .setAlgebra, .setFunction, .relational, .relationalCard, .seqArray, .seqWord], by intro x; cases x <;> simp⟩

def toConstruct : Fren.Core.Construct → lang.Construct
  | .stringCompare => .StringCompare
  | .stringAtom => .StringAtom
  | .stringIndex => .StringIndex
  | .stringSearch => .StringSearch
  | .setAlgebra => .SetAlgebra
  | .setFunction => .SetFunction
  | .relational => .Relational
  | .relationalCard => .RelationalCard
  | .seqArray => .SeqArray
  | .seqWord => .SeqWord

impl in_core: lang::in_core for (c : Fren.Core.Construct) (a m i g f r l : Bool) {
  construct := toConstruct c,
  constant_args? := a,
  comparable? := m,
  infinite_output? := i,
  ground? := g,
  infinite_elems? := f,
  finite_range? := r,
  literal_operand? := l,
  decidable? := Fren.Core.inCore c a m i g f r l,
} by
  intro c a m i g f r l _
  cases c <;> simp [fren_spec, toConstruct, Fren.Core.inCore]

/-! ## Lexical structure -/

-- For every identifier: the lexer's reserved words are the spec's.
impl reserved_word: lang::reserved_word for (s : String) {
  lexeme := s,
  reserved? := FrenCli.reserved.contains s,
} by
  intro s _
  simp [fren_spec, FrenCli.reserved]

-- For every lexeme: the lexer's punctuators are the spec's.
impl punctuator: lang::punctuator for (s : String) {
  lexeme := s,
  accepted? := FrenCli.punctuators.contains s,
} by
  intro s _
  simp [fren_spec, FrenCli.punctuators]

namespace Lexical

open Fren.Core (inRanges isIdStart isIdRest Re)

/-- A one-character range is that character. -/
theorem le_le_self (d c : Char) : (decide (d ≤ c) && decide (c ≤ d)) = (c == d) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩

/-- `[A-Za-z_]` is `isIdStart`. -/
theorem start_class (c : Char) : inRanges [('A', 'Z'), ('a', 'z'), ('_', '_')] c = isIdStart c := by
  simp [inRanges, isIdStart, le_le_self, Bool.or_assoc]

/-- `[A-Za-z0-9_'?!]` is what continues an identifier. -/
theorem continue_class (c : Char) :
    inRanges [('A', 'Z'), ('a', 'z'), ('0', '9'), ('_', '_'), ('\'', '\''), ('?', '?'), ('!', '!')] c =
      (isIdRest c || c == '?' || c == '!') := by
  simp [inRanges, isIdRest, le_le_self, Bool.or_assoc]

theorem dot_class (c : Char) : inRanges [('.', '.')] c = (c == '.') := by
  simp [inRanges, le_le_self]

/-- `ends_with?("?")` is about the last character. -/
theorem endsWith_question (cs : List Char) :
    Fren.Str.endsWith (String.ofList cs) (Fren.Str.lit "?") = (cs.getLast? == some '?') := by
  rcases List.eq_nil_or_concat cs with h | ⟨l, x, rfl⟩
  · subst h; rfl
  · simp [Fren.Str.endsWith, Fren.Str.lit, List.isSuffixOf, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

/-- A character, then `r`: the first character is that one. -/
theorem mat_cat_char (a : Char) (r : Re) (cs : List Char) :
    (Re.cat (.str [a]) r).mat cs = match cs with
      | [] => false
      | c :: t => c == a && r.mat t := by
  rw [Re.mat_cat]
  cases cs with
  | nil => simp [Re.mat]
  | cons c t =>
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Re.mat, beq_iff_eq]
    constructor
    · rintro ⟨i, _, h1, h2⟩
      match i, h1, h2 with
      | 1, h1, h2 => simp at h1 h2; exact ⟨h1, h2⟩
      | 0, h1, _ => simp at h1
      | k + 2, h1, h2 =>
        cases t with
        | nil => simp at h1 h2; exact ⟨h1, h2⟩
        | cons _ _ => simp at h1
    · rintro ⟨h1, h2⟩
      exact ⟨1, by simp, by simp [h1], by simpa using h2⟩

/-- A repeated class, then a class: the last character is in the second, and
the others in the first. -/
theorem mat_star_cls_cls (n m : Bool) (rs qs : List (Char × Char)) (cs : List Char) :
    (Re.cat (.star (.cls n rs)) (.cls m qs)).mat cs = match cs.getLast? with
      | some c => (inRanges qs c != m) && cs.dropLast.all fun d => inRanges rs d != n
      | none => false := by
  rw [Re.mat_cat]
  rcases List.eq_nil_or_concat cs with rfl | ⟨l, x, rfl⟩
  · simp [Re.mat_cls]
  · simp only [List.concat_eq_append, List.getLast?_concat, List.dropLast_concat]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Re.mat_star_cls]
    constructor
    · rintro ⟨i, hi, h1, h2⟩
      rw [Re.mat_cls] at h2
      have hlen : (List.drop i (l ++ [x])).length = 1 := by split at h2 <;> simp_all
      have hi' : i = l.length := by simp at hlen hi; omega
      subst hi'
      simp at h1 h2
      exact ⟨by simpa using h2, by simpa using h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨l.length, by simp; omega, by simpa using h2, by simp [Re.mat_cls, h1]⟩

theorem mat_union (a b : Re) (cs : List Char) : (Re.union a b).mat cs = (a.mat cs || b.mat cs) := by
  rw [Re.mat]

theorem mat_empty (cs : List Char) : (Re.str []).mat cs = (cs == []) := by
  rw [Re.mat]

theorem decimal_class (c : Char) : inRanges [('0', '9')] c = Fren.Core.isDecimalDigit c := by
  simp [inRanges, Fren.Core.isDecimalDigit]

theorem decimal_sep_class (c : Char) :
    inRanges [('0', '9'), ('_', '_')] c = (Fren.Core.isDecimalDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isDecimalDigit, le_le_self]

theorem hex_class (c : Char) :
    inRanges [('0', '9'), ('a', 'f'), ('A', 'F')] c = Fren.Core.isHexDigit c := by
  simp [inRanges, Fren.Core.isHexDigit, Fren.Core.isDecimalDigit, Bool.or_assoc]

theorem hex_sep_class (c : Char) :
    inRanges [('0', '9'), ('a', 'f'), ('A', 'F'), ('_', '_')] c = (Fren.Core.isHexDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isHexDigit, Fren.Core.isDecimalDigit, le_le_self, Bool.or_assoc]

theorem binary_class (c : Char) : inRanges [('0', '1')] c = Fren.Core.isBinaryDigit c := by
  simp [inRanges, Fren.Core.isBinaryDigit]

theorem binary_sep_class (c : Char) :
    inRanges [('0', '1'), ('_', '_')] c = (Fren.Core.isBinaryDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isBinaryDigit, le_le_self]

theorem octal_class (c : Char) : inRanges [('0', '7')] c = Fren.Core.isOctalDigit c := by
  simp [inRanges, Fren.Core.isOctalDigit]

theorem octal_sep_class (c : Char) :
    inRanges [('0', '7'), ('_', '_')] c = (Fren.Core.isOctalDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isOctalDigit, le_le_self]

theorem pair_class (a b c : Char) : inRanges [(a, a), (b, b)] c = (c == a || c == b) := by
  simp [inRanges, le_le_self]

/-- `ends_with?("!")` is about the last character. -/
theorem endsWith_bang (cs : List Char) :
    Fren.Str.endsWith (String.ofList cs) (Fren.Str.lit "!") = (cs.getLast? == some '!') := by
  rcases List.eq_nil_or_concat cs with h | ⟨l, x, rfl⟩
  · subst h; rfl
  · simp [Fren.Str.endsWith, Fren.Str.lit, List.isSuffixOf, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

/-- `starts_with?("!")` is about the first character. -/
theorem startsWith_bang (cs : List Char) :
    Fren.Str.startsWith (String.ofList cs) (Fren.Str.lit "!") = (cs.head? == some '!') := by
  rcases cs with _ | ⟨c, t⟩
  · rfl
  · simp [Fren.Str.startsWith, Fren.Str.lit, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

end Lexical

-- For every lexeme and the input after it: whether the lexer continues it.
-- The lexer calls `identExtends src last j` on the whole input, which reads
-- only `src[j]` and `src[j + 1]`, so it is this applied to the input after
-- `j`.
impl identifier_end: lang::identifier_end for (cs rest : List Char) {
  lexeme := String.ofList cs,
  remaining := String.ofList rest,
  ends? := Fren.Core.identExtends rest.toArray (cs.getLast?.getD ' ') 0 == 0,
} by
  rintro cs rest -
  simp only [fren_spec, Lexical.endsWith_question, Lexical.endsWith_bang, Lexical.startsWith_bang,
    Fren.Core.Re.matches, String.toList_ofList, Fren.Core.Re.mat_cat_cls, Fren.Core.Re.mat_star_any]
  cases h : cs.getLast? with
  | some l =>
    by_cases hb : l = '!'
    · subst hb; simp [Fren.Core.identExtends]
    by_cases hl : l = '?'
    · subst hl
      rcases rest with _ | ⟨c, t⟩
      · simp [Fren.Core.identExtends]
      · by_cases hc : c = '!'
        · subst hc; simp [Fren.Core.identExtends, Lexical.continue_class]
        · simp [Fren.Core.identExtends, hc]
    · rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
        simp [Fren.Core.identExtends, hl, hb, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
        split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with (hc | hc) | hc <;> simp_all)
  | none =>
    rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
      simp [Fren.Core.identExtends, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
      split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with (hc | hc) | hc <;> simp_all)

namespace Lexical

open Fren.Core (Re)

/-- The patterns of `lang::integer_literal`, as `Reqs/Lang/Lexical.md` writes
them. -/
def decimalRe : Re :=
  .cat (.cls false [('0', '9')]) (.union (.str []) (.cat (.star (.cls false [('0', '9'), ('_', '_')])) (.cls false [('0', '9')])))

def basedRe (b B : Char) (digits : List (Char × Char)) : Re :=
  .cat (.str ['0']) (.cat (.cls false [(b, b), (B, B)]) (.cat (.star (.cls false (digits ++ [('_', '_')]))) (.cls false digits)))

theorem beq_flip (a b : Char) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact eq_comm

theorem integerLiteral_regex (s : String) :
    Fren.Core.integerLiteral s =
      ((decimalRe.mat s.toList && !['0', '_'].isPrefixOf s.toList)
        || (basedRe 'x' 'X' [('0', '9'), ('a', 'f'), ('A', 'F')]).mat s.toList
        || (basedRe 'b' 'B' [('0', '1')]).mat s.toList
        || (basedRe 'o' 'O' [('0', '7')]).mat s.toList) := by
  simp only [Fren.Core.integerLiteral, decimalRe, basedRe, List.cons_append, List.nil_append]
  generalize s.toList = cs
  rcases cs with _ | ⟨c, _ | ⟨b, ds⟩⟩
  · simp [Fren.Core.Re.mat_cat_cls, mat_cat_char, List.isPrefixOf]
  · simp [Fren.Core.Re.mat_cat_cls, mat_cat_char, mat_union, mat_empty, mat_star_cls_cls, decimal_class,
      List.isPrefixOf]
  · simp only [mat_cat_char, Fren.Core.Re.mat_cat_cls, mat_star_cls_cls, mat_union, mat_empty,
      Fren.Core.digitsEndingInDigit, decimal_class, decimal_sep_class, hex_class, hex_sep_class, binary_class,
      binary_sep_class, octal_class, octal_sep_class, pair_class, List.isPrefixOf, Bool.bne_false, Bool.and_true,
      List.isEmpty_cons, Bool.false_or, List.head?_cons]
    rw [beq_flip '0' c, beq_flip '_' b]
    cases hd : ds.getLast? <;> rcases hl : (b :: ds).getLast? with _ | l <;>
      rw [Bool.eq_iff_iff] <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.false_eq_true, and_false, or_false] <;>
      by_cases hc : c = '0' <;> by_cases hb : b = '_' <;> simp_all [or_assoc]

end Lexical

-- For every lexeme: the lexer's test for an integer literal is the spec's.
impl integer_literal: lang::integer_literal for (s : String) {
  lexeme := s,
  accepted? := Fren.Core.integerLiteral s,
} by
  intro s _
  have h0 : "0_".toList = ['0', '_'] := by decide
  simp only [fren_spec, Fren.Core.Re.matches, Fren.Str.startsWith, Fren.Str.lit, Lexical.integerLiteral_regex, h0,
    Lexical.decimalRe, Lexical.basedRe, List.cons_append, List.nil_append, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Bool.not_eq_true, or_assoc]

-- For every payload and mention: the elaborators' check, which both front
-- ends call through `variantMentionMsg?`.
impl variant_mention: lang::variant_mention for (n : Nat) (a : Bool) {
  payload := n,
  applied? := a,
  accepted? := Fren.Core.variantMentionAccepted n a,
} by
  intro n a _
  cases a <;> rcases n with _ | n <;> simp [fren_spec, Fren.Core.variantMentionAccepted] <;> omega

interp lang::DeclaredName := Lean.Name

/-- A list's distinct members are as many as it has exactly when none
repeats. -/
theorem nub_length_eq_iff {α : Type} [DecidableEq α] :
    ∀ (l : List α), (Fren.FinSet.nub l).length = l.length ↔ l.Nodup
  | [] => by simp [Fren.FinSet.nub]
  | a :: l => by
    have ih := nub_length_eq_iff l
    have hle : (Fren.FinSet.nub l).length ≤ l.length :=
      Fren.FinSet.length_le_of_nodup (Fren.FinSet.nodup_nub l) fun _ hx => Fren.FinSet.mem_nub.mp hx
    unfold Fren.FinSet.nub
    by_cases h : a ∈ Fren.FinSet.nub l
    · have ha : a ∈ l := Fren.FinSet.mem_nub.mp h
      simp only [h, if_true, List.length_cons, List.nodup_cons, ha, not_true_eq_false, false_and, iff_false]
      omega
    · have ha : a ∉ l := fun m => h (Fren.FinSet.mem_nub.mpr m)
      simp [h, List.nodup_cons, ha, ih]

/-- A list's set of members has as many as the list exactly when none
repeats. -/
theorem card_ofList_eq_length_iff {α : Type} [DecidableEq α] (l : List α) :
    (Fren.FinSet.ofList l).card = (l.length : Int) ↔ l.Nodup := by
  rw [Fren.FinSet.card_ofList, Int.natCast_inj]
  exact nub_length_eq_iff l

-- For every list of declared names, with the check that both front ends use.
impl distinct_names: lang::distinct_names for (names : Array Lean.Name) {
  count := names.size,
  names := Fren.FinSet.ofArray names,
  accepted? := (Fren.Core.repeatsAt names).isEmpty,
} by
  intro names _
  have := @card_ofList_eq_length_iff _ (fun a b => Classical.propDecidable (a = b)) names.toList
  simp only [Array.length_toList] at this
  simp only [fren_spec, Fren.FinSet.ofArray, Array.isEmpty_iff, Fren.Core.repeatsAt_eq_empty]
  exact this.symm

end Fren.Impls
