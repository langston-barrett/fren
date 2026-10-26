-- keep-sorted start
import FrenCli.Lex
import FrenCore.Checking
import FrenCore.Guards
import FrenCore.PatternTypes
import FrenCore.Patterns
import FrenCore.Quantifier
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
  | .bound => .Bound
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
  | .armGuard => .ArmGuard
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
  | .recursivePayload => .RecursivePayload
  | .element => .Element

impl nat_place: lang::nat_place for (p : Fren.Core.TypePlace) {
  place := toTypePlace p,
  accepted? := Fren.Core.natPlaceAccepted p,
} by
  intro p _
  cases p <;> simp [fren_spec, toTypePlace, Fren.Core.natPlaceAccepted]

impl pattern_place: lang::pattern_place for (p : Fren.Core.PatternPlace) (r : Bool) {
  place := match p with | .top => .Top | .field => .Field | .payload => .Payload | .element => .Element,
  recursive? := r && p == .payload,
  decidable? := Fren.Core.patternPlaceDecidable p (r && p == .payload),
} by
  intro p r _
  cases p <;> cases r <;> simp [fren_spec, Fren.Core.patternPlaceDecidable]

impl pattern_finite: lang::pattern_finite for (b i n : Bool) {
  base_finite? := b && !i,
  integers? := i,
  bounded? := n,
  finite? := Fren.Core.patternFinite (b && !i) i n,
} by
  intro b i n _
  cases b <;> cases i <;> cases n <;> simp [fren_spec, Fren.Core.patternFinite]

impl pattern_widening: lang::pattern_widening for (p w : Bool) {
  patterned? := p,
  widened? := w,
  accepted? := (Fren.Core.patternWidening w p).1,
  obliged? := (Fren.Core.patternWidening w p).2,
} by
  intro p w _
  cases p <;> cases w <;> simp [fren_spec, Fren.Core.patternWidening]

def toBrought : Fren.Core.Brought → lang.Brought
  | .nothing => .Nothing
  | .assumption => .Assumption
  | .guarantee => .Guarantee

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
  | .add => .Addition
  | .sub => .Subtraction
  | .other => .Other

-- For every operator, underlying type and whether the newtype is ordered,
-- with the check that both front ends use.
impl newtype_operator: lang::newtype_operator for (op : Fren.Core.NewtypeOp) (u : Fren.Core.Ty) (o : Bool) {
  op := toNewtypeOp op,
  underlying := u,
  ordered? := o,
  inner_has? := match u with
    | .newtype _ v => Fren.Core.newtypeOpAccepted op v false
    | _ => false,
  accepted? := Fren.Core.newtypeOpAccepted op u o,
} by
  intro op u o _
  cases op <;> cases u <;> simp [fren_spec, toNewtypeOp, kindOf, Fren.Core.newtypeOpAccepted]

interp lang::TypeName := Lean.Name

/-- The path of an enumeration, record or newtype (`lang::type_name`). -/
def typeNameOf : Fren.Core.Ty → Lean.Name
  | .enum p | .record p | .newtype p _ => p
  | _ => .anonymous

interp lang::type_name := typeNameOf

/-- `Ty.ordered`, where the declarations declared `ordered` are those of
`os`, as `lang::ordered_in?` states it of the type's kind and name. -/
theorem ordered_iff (t : Fren.Core.Ty) (os : List Lean.Name) :
    t.ordered (fun x => decide (x ∈ os)) = true ↔
      (kindOf t = .IntTy ∨ kindOf t = .NatTy ∨ kindOf t = .StringTy) ∨
        ((kindOf t = .EnumTy ∨ kindOf t = .RecordTy) ∧ typeNameOf t ∈ os) := by
  cases t <;> simp [kindOf, typeNameOf, Fren.Core.Ty.ordered]

/-- A position, or `-1` for none. -/
def posOr : Option Nat → Int
  | none => -1
  | some i => i

-- For every declared type, with its pattern, where `os` are the
-- declarations declared `ordered`, by the function that both front ends
-- ask of a declaration's fields (`Fren.Core.PTy.ordered`), which is
-- `Fren.Core.Ty.ordered`, asked of an expression's type, of its base.
impl ordered_type: lang::ordered_type for (pt : Fren.Core.PTy) (os : List Lean.Name) {
  base := pt.ty,
  patterned? := pt.pat?.isSome,
  ordered_items := Fren.FinSet.ofList os,
  ordered? := pt.ordered (fun x => decide (x ∈ os)),
} by
  intro pt os _
  simp [fren_spec, Fren.Core.PTy.ordered, ordered_iff]

def toDeclaration : Fren.Core.OrderedDecl → lang.Declaration
  | .enumeration => .Enumeration
  | .record => .Record
  | .newtype => .Newtype

theorem firstUnordered_some (od : Lean.Name → Bool) :
    ∀ (ts : List Fren.Core.PTy) (i : Nat), Fren.Core.PTy.firstUnordered? od ts = some i →
      ∃ h : i < ts.length, ts[i].ordered od = false
  | [], _, h => by simp [Fren.Core.PTy.firstUnordered?] at h
  | t :: ts, i, h => by
    by_cases ht : t.ordered od = true
    · simp only [Fren.Core.PTy.firstUnordered?, ht, if_true, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨hl, hf⟩ := firstUnordered_some od ts j hj
      exact ⟨by simp; omega, by simpa using hf⟩
    · simp only [Fren.Core.PTy.firstUnordered?, ht] at h
      simp at h
      subst h
      exact ⟨by simp, by simpa using ht⟩

theorem firstUnordered_le (od : Lean.Name → Bool) :
    ∀ (ts : List Fren.Core.PTy) (k : Nat) (hk : k < ts.length), ts[k].ordered od = false →
      ∃ i, Fren.Core.PTy.firstUnordered? od ts = some i ∧ i ≤ k
  | [], _, hk, _ => by simp at hk
  | t :: ts, k, hk, hf => by
    by_cases ht : t.ordered od = true
    · cases k with
      | zero => simp_all
      | succ k =>
        obtain ⟨i, hi, hle⟩ := firstUnordered_le od ts k (by simp at hk; omega) (by simpa using hf)
        exact ⟨i + 1, by simp [Fren.Core.PTy.firstUnordered?, ht, hi], by omega⟩
    · exact ⟨0, by simp [Fren.Core.PTy.firstUnordered?, ht], by omega⟩

-- For every declaration, whether it is ordered, how many of its variants
-- have a payload, and its fields' declared types, where `os` are the
-- declarations declared `ordered`, by the functions that both front ends
-- call to accept it and to report its field.
impl ordered_declaration: lang::ordered_declaration
    for (d : Fren.Core.OrderedDecl) (o : Bool) (n : Nat) (pts : List Fren.Core.PTy) (os : List Lean.Name) (k : Int) {
  declaration := toDeclaration d,
  ordered? := o,
  n_payloads := n,
  fields := Fren.Seq.ofList (pts.map (·.ty)),
  ordered_items := Fren.FinSet.ofList os,
  k := k,
  first_unordered := posOr (Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts),
  accepted? := Fren.Core.orderedDeclAccepted o n (Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts),
} by
  intro d o n pts os k _
  simp only [fren_spec]
  have nth (i : Nat) (h : i < pts.length) : (Fren.Seq.ofList (pts.map (·.ty))).nth (i : Int) = pts[i].ty := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  have hord (t : Fren.Core.PTy) := ordered_iff t.ty os
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts with
    | none => simp [posOr]; omega
    | some i =>
      obtain ⟨hi, _⟩ := firstUnordered_some _ pts i hf
      simp [posOr]; omega
  · intro ⟨hki, hne⟩
    cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts with
    | none => simp [hf, posOr] at hki; omega
    | some i =>
      obtain ⟨hi, hu⟩ := firstUnordered_some _ pts i hf
      simp only [hf, posOr] at hki
      rw [hki, nth i hi]
      have := hord pts[i]
      simp only [Fren.Core.PTy.ordered] at hu
      simp_all
  · intro ⟨⟨h0, hk⟩, hno⟩
    have hk' : k.toNat < pts.length := by simp at hk; omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth k.toNat hk'] at hno
    have := hord pts[k.toNat]
    obtain ⟨i, hi, hle⟩ := firstUnordered_le (fun x => decide (x ∈ os)) pts k.toNat hk'
      (by
        simp only [Fren.Core.PTy.ordered]
        cases hc : pts[k.toNat].ty.ordered (fun x => decide (x ∈ os))
        · rfl
        · exact absurd (this.1 hc) (by simpa using hno))
    simp only [hi, posOr]
    omega
  · cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts <;>
      cases o <;> simp [Fren.Core.orderedDeclAccepted, posOr]

interp lang::FieldName := Lean.Name

/-- The kind of a plan (`lang::Plan`). -/
def planKind : Fren.Core.OrderPlan → lang.Plan
  | .number => .Number
  | .string => .Text
  | .enum _ => .Position
  | .newtype .. => .AsField
  | .record .. => .Fields

/-- A plan is only of an ordered type, and of the kind that `lang::plan_of`
gives of it. -/
theorem plan_kind (od : Lean.Name → Bool) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) :
    ∀ (m : Nat) (t : Fren.Core.Ty) (p : Fren.Core.OrderPlan), Fren.Core.orderPlanAt od fieldsOf m t = some p →
      planKind p = lang.plan_of (kindOf t) (t matches .newtype ..) ∧ t.ordered od = true
  | 0, _, _, h => by simp [Fren.Core.orderPlanAt] at h
  | m + 1, t, p, h => by
    cases t <;> simp only [Fren.Core.orderPlanAt] at h <;> try simp at h
    all_goals first
      | (subst h; simp [planKind, lang.plan_of, kindOf, Fren.Core.Ty.ordered])
      | (obtain ⟨hd, rfl⟩ := h; simp [planKind, lang.plan_of, kindOf, Fren.Core.Ty.ordered, hd])
      | (obtain ⟨hd, _, _, rfl⟩ := h; simp [planKind, lang.plan_of, kindOf, Fren.Core.Ty.ordered, hd])

/-- A record's plan has its fields' names, in order, and each field's plan
is its type's. -/
theorem fields_plan {α β : Type} (g : β → Option Fren.Core.OrderPlan) :
    ∀ (l : List (α × β)) (r : List (α × Fren.Core.OrderPlan)),
      l.mapM (fun (f, t) => (f, ·) <$> g t) = some r →
        r.map (·.1) = l.map (·.1) ∧ ∀ (i : Nat) (h : i < l.length), ∃ h' : i < r.length, g l[i].2 = some r[i].2
  | [], r, h => by simp at h; subst h; simp
  | (f, t) :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.map_eq_some_iff, Functor.map] at h
    obtain ⟨⟨f', p⟩, ⟨p', hp, hpe⟩, rs, hrs, hr⟩ := h
    cases hpe
    cases hr
    obtain ⟨hn, hi⟩ := fields_plan g l rs hrs
    refine ⟨by simp [hn], fun i hil => ?_⟩
    cases i with
    | zero => exact ⟨by simp, by simpa using hp⟩
    | succ i =>
      obtain ⟨h', hg⟩ := hi i (by simp at hil; omega)
      exact ⟨by simp; omega, by simpa using hg⟩

/-- The record's plan, where `t` is the record `q` that `od` orders. -/
theorem record_plan (od : Lean.Name → Bool) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) (m : Nat)
    (q : Lean.Name) (p : Fren.Core.OrderPlan) (h : Fren.Core.orderPlanAt od fieldsOf (m + 1) (.record q) = some p) :
    ∃ r, p = .record q r ∧
      (fieldsOf q).mapM (fun (f, t) => (f, ·) <$> Fren.Core.orderPlanAt od fieldsOf m t) = some r := by
  simp only [Fren.Core.orderPlanAt] at h
  split at h
  · simp only [Functor.map, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨r, rfl, hr⟩
  · simp at h

-- For every type, where `os` are the declarations declared `ordered` and
-- `fieldsOf` gives each record's fields, by the function that both front
-- ends call to plan a comparison, whose plan they render, and which the
-- evaluator follows (`Fren.Core.orderPlan?`).
impl order_plan: lang::order_plan
    for (t : Fren.Core.Ty) (os : List Lean.Name) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) (n k : Nat) {
  t := t,
  ordered_items := Fren.FinSet.ofList os,
  fields := Fren.Seq.ofList ((fieldsOf (typeNameOf t)).map (·.1)),
  field_types := Fren.Seq.ofList ((fieldsOf (typeNameOf t)).map (·.2)),
  k := k,
  planned? := (Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t).isSome,
  plan := ((Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t).map planKind).getD .Number,
  compared := Fren.Seq.ofList (match Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t with
    | some (.record _ fs) => fs.map (·.1)
    | _ => []),
  field_plans := Fren.Seq.ofList (match Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t with
    | some (.record _ fs) => fs.map (planKind ·.2)
    | _ => []),
} by
  intro t os fieldsOf n k _
  simp only [fren_spec, Fren.Core.orderPlan?]
  cases hp : Fren.Core.orderPlanAt (fun x => decide (x ∈ os)) fieldsOf (n + 2) t with
  | none => simp
  | some p =>
    obtain ⟨hk, hord⟩ := plan_kind _ fieldsOf (n + 2) t p hp
    have hin := (ordered_iff t os).1 (by simpa using hord)
    simp only [Option.isSome_some, Option.map_some, Option.getD_some, true_implies, hk, true_and]
    refine ⟨?_, ?_, ?_⟩
    · cases t <;> simp_all [kindOf, typeNameOf, Fren.Core.Ty.ordered]
    · intro hf
      obtain ⟨q, rfl⟩ : ∃ q, t = .record q := by
        cases t <;> first | exact ⟨_, rfl⟩ | simp [lang.plan_of, kindOf, Fren.Core.orderPlanAt] at hf hp
      · obtain ⟨r, rfl, hr⟩ := record_plan _ fieldsOf (n + 1) q p hp
        obtain ⟨hn, _⟩ := fields_plan _ (fieldsOf q) r hr
        have hlen : r.length = (fieldsOf q).length := by simpa using congrArg List.length hn
        exact ⟨by simp [typeNameOf, hn], by simp [typeNameOf, hlen]⟩
    · intro ⟨hf, h0, hkl⟩
      obtain ⟨q, rfl⟩ : ∃ q, t = .record q := by
        cases t <;> first | exact ⟨_, rfl⟩ | simp [lang.plan_of, kindOf, Fren.Core.orderPlanAt] at hf hp
      · obtain ⟨r, rfl, hr⟩ := record_plan _ fieldsOf (n + 1) q p hp
        obtain ⟨_, hi⟩ := fields_plan _ (fieldsOf q) r hr
        have hkl' : k < (fieldsOf q).length := by simp [typeNameOf] at hkl; omega
        obtain ⟨h', hg⟩ := hi k hkl'
        obtain ⟨hpk, _⟩ := plan_kind _ fieldsOf (n + 1) _ _ hg
        rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa [typeNameOf] using h'),
          Fren.Seq.nth_of_lt _ _ (by omega) (by simpa [typeNameOf] using hkl')]
        simp only [typeNameOf, Fren.Seq.toList_ofList, List.getElem_map, Int.toNat_natCast]
        rw [hpk]

def toFieldComparison : Ordering → lang.Comparison
  | .lt => .Less
  | .eq => .Equal
  | .gt => .Greater

/-- The first of `cs` that is not `eq`. -/
def firstDiffering? : List Ordering → Option Nat
  | [] => none
  | c :: cs => if c == .eq then (firstDiffering? cs).map (· + 1) else some 0

theorem lex_first : ∀ cs : List Ordering, Fren.Core.lexCompare cs = match firstDiffering? cs with
    | none => .eq
    | some i => cs.getD i .eq
  | [] => rfl
  | c :: cs => by
    cases c <;> simp [Fren.Core.lexCompare, firstDiffering?, lex_first cs] <;> split <;> simp_all

theorem differing_some : ∀ (cs : List Ordering) (i : Nat), firstDiffering? cs = some i →
    ∃ h : i < cs.length, cs[i] ≠ .eq
  | [], _, h => by simp [firstDiffering?] at h
  | c :: cs, i, h => by
    cases c with
    | eq =>
      cases hf : firstDiffering? cs with
      | none => simp [firstDiffering?, hf] at h
      | some j =>
        simp [firstDiffering?, hf] at h
        subst h
        obtain ⟨hl, hne⟩ := differing_some cs j hf
        exact ⟨by simp; omega, by simpa using hne⟩
    | lt | gt =>
      simp [firstDiffering?] at h
      subst h
      exact ⟨by simp, by simp⟩

theorem differing_le : ∀ (cs : List Ordering) (k : Nat) (hk : k < cs.length), cs[k] ≠ .eq →
    ∃ i, firstDiffering? cs = some i ∧ i ≤ k
  | [], _, hk, _ => by simp at hk
  | c :: cs, k, hk, hne => by
    cases c with
    | eq =>
      cases k with
      | zero => simp at hne
      | succ k =>
        obtain ⟨i, hi, hle⟩ := differing_le cs k (by simp at hk; omega) (by simpa using hne)
        exact ⟨i + 1, by simp [firstDiffering?, hi], by omega⟩
    | lt | gt => exact ⟨0, by simp [firstDiffering?], by omega⟩

theorem toFieldComparison_eq (c : Ordering) : toFieldComparison c = .Equal ↔ c = .eq := by
  cases c <;> simp [toFieldComparison]

-- For every sequence of fields' comparisons, by the function by which the
-- evaluator compares a record's values, or an enumeration's payloads
-- (`FrenCli.Eval.cmpV`).
impl lexicographic: lang::lexicographic for (cs : List Ordering) (k : Int) {
  fields := Fren.Seq.ofList (cs.map toFieldComparison),
  k := k,
  decider := posOr (firstDiffering? cs),
  result := toFieldComparison (Fren.Core.lexCompare cs),
} by
  intro cs k _
  simp only [fren_spec]
  have nth (i : Nat) (h : i < cs.length) : (Fren.Seq.ofList (cs.map toFieldComparison)).nth (i : Int) = toFieldComparison cs[i] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    cases hf : firstDiffering? cs with
    | none => simp [hf, posOr] at hne
    | some i =>
      obtain ⟨hi, hc⟩ := differing_some cs i hf
      simp only [posOr, nth i hi]
      exact ⟨⟨by omega, by simpa using hi⟩, by rw [Ne, toFieldComparison_eq]; exact hc⟩
  · intro ⟨⟨h0, hk⟩, hne⟩
    have hk' : k.toNat < cs.length := by simp at hk; omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth k.toNat hk', Ne, toFieldComparison_eq] at hne
    obtain ⟨i, hi, hle⟩ := differing_le cs k.toNat hk' hne
    simp only [hi, posOr]
    omega
  · rw [lex_first cs]
    cases hf : firstDiffering? cs with
    | none => simp [toFieldComparison, posOr]
    | some i =>
      obtain ⟨hi, _⟩ := differing_some cs i hf
      simp only [posOr]
      rw [if_neg (by omega), nth i hi]
      simp [List.getElem?_eq_getElem hi]

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

/-- A pattern of `lang::pattern_overlap` as the front ends resolve it. -/
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

/-- `some ()` where `b` holds: a step of overlap read as a decision. -/
def someIf (b : Bool) : Option Unit := if b then some () else none

-- For every step of `Pat.overlapWit?`, which calls `overlapStep` with the
-- smaller problems as functions; its decision is whether it has a witness.
impl overlap: lang::overlap for (f g : Fren.Core.HeadKind) (same args fm gm alt : Bool) {
  first := toHeadKind f,
  second := toHeadKind g,
  same? := same,
  args_overlap? := args,
  first_matches? := fm,
  second_matches? := gm,
  some_alternative? := alt,
  overlap? := (Fren.Core.overlapStep f g same (fun _ => someIf args) (fun _ => someIf fm) (fun _ => someIf gm)
    (fun _ => someIf alt)).isSome,
} by
  intro f g same args fm gm alt _
  cases f <;> cases g <;> cases same <;> cases args <;> cases fm <;> cases gm <;> cases alt <;>
    simp [fren_spec, toHeadKind, Fren.Core.overlapStep, someIf]

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

impl function_params: lang::function_params for (d c : Bool) (p n : Nat) {
  defined? := d,
  contract? := c,
  n_params := p,
  n_named := n,
  accepted? := Fren.Core.functionParamsAccepted d c p n,
} by
  intro d c p n _
  cases d <;> cases c <;> simp [fren_spec, Fren.Core.functionParamsAccepted] <;> omega

def toClauseKind : Fren.Core.ClauseKind → lang.ClauseKind
  | .precondition => .Precondition
  | .postcondition => .Postcondition

instance : Fren.Finite Fren.Core.ClauseKind := ⟨[.precondition, .postcondition], by intro x; cases x <;> simp⟩

-- For every clause and application: the rule that both front ends call at
-- each application of the function itself in its contract.
impl contract_application: lang::contract_application for (k : Fren.Core.ClauseKind) (o t : Bool) {
  clause := toClauseKind k,
  own? := o,
  to_params? := t,
  accepted? := Fren.Core.contractApplicationAccepted k o t,
}

/-- An argument as both front ends read it (`Core.appliesToParams`): a
parameter's name, or any other expression. -/
def writtenName? : lang.Written → Option Lean.Name
  | .Name .P0 => some `p0
  | .Name .P1 => some `p1
  | .Name .P2 => some `p2
  | .Other => none

/-- A parameter's name; `Other` is never one, and its name no argument's. -/
def paramName : lang.Written → Lean.Name
  | .Name .P0 => `p0
  | .Name .P1 => `p1
  | .Name .P2 => `p2
  | .Other => `«#other»

theorem writtenName_beq (a p : lang.Written) :
    (writtenName? a == some (paramName p)) = (decide (a = p) && !decide (p = .Other)) := by
  rcases a with ⟨_ | _ | _⟩ | _ <;> rcases p with ⟨_ | _ | _⟩ | _ <;> decide

theorem appliesToParams_iff (as ps : List lang.Written) :
    Fren.Core.appliesToParams (as.toArray.map writtenName?) (ps.toArray.map paramName)
      = (decide (as = ps) && !decide (lang.Written.Other ∈ ps)) := by
  simp only [Fren.Core.appliesToParams, Array.toList_map, List.map_map]
  induction as generalizing ps with
  | nil => cases ps <;> simp
  | cons a as ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      simp only [List.map_cons, List.cons_beq_cons, Function.comp_apply, writtenName_beq, ih, List.cons.injEq,
        List.mem_cons]
      by_cases h1 : a = p <;> by_cases h2 : p = .Other <;> by_cases h3 : as = ps <;>
        by_cases h4 : lang.Written.Other ∈ ps <;> simp [h1, h2, h3, h4, eq_comm]

-- For every application of the function in its own contract, of up to
-- three parameters: the rule that both front ends call, on the arguments
-- as they read them.
impl contract_arguments: lang::contract_arguments for (k : Fren.Core.ClauseKind) (o : Bool) (ps as : List lang.Written) {
  clause := toClauseKind k,
  own? := o,
  params := Fren.Seq.ofList ps,
  args := Fren.Seq.ofList as,
  accepted? := Fren.Core.contractApplicationAccepted k o
    (Fren.Core.appliesToParams (as.toArray.map writtenName?) (ps.toArray.map paramName)),
} by
  intro k o ps as _
  rw [appliesToParams_iff]
  cases k <;> cases o <;> simp [fren_spec, toClauseKind, Fren.Core.contractApplicationAccepted, Fren.Seq.ext_iff] <;>
    first | (intro h; exact absurd h (by decide)) | (intros; rfl)

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

/-! ## Quantifiers (`Reqs/Lang/Quantifiers`) -/

def toQuantifiedKind : lang.ValueType → Fren.Core.QuantifiedKind
  | .BoolTy => .bool
  | .EnumTy => .enum
  | .RecordTy => .record
  | .IntTy | .NatTy | .StringTy | .AbstractTy | .SetTy | .RelTy | .SeqTy => .other

-- For every type, by its kind, which both front ends compute from the type
-- they quantify over.
impl quantified_type: lang::quantified_type for (k : lang.ValueType) (r p : Bool) {
  type_kind := k,
  recursive? := r,
  parts? := p,
  listed? := Fren.Core.quantifiedTypeAccepted (toQuantifiedKind k) r p,
} by
  intro k r p _
  cases k <;> cases r <;> cases p <;> simp [fren_spec, toQuantifiedKind, Fren.Core.quantifiedTypeAccepted]

-- For every number of instances, which both front ends count.
impl quantifier_size: lang::quantifier_size for (n : Nat) {
  n_instances := n,
  accepted? := Fren.Core.quantifierSizeAccepted n,
} by
  intro n _
  simp [fren_spec, Fren.Core.quantifierSizeAccepted, Fren.Core.maxInstances] <;> omega

def toBinderTarget : lang.BinderTarget → Fren.Core.BinderTarget
  | .TypeName => .typeName
  | .Component => .component

-- For every binder, by what its type names.
impl quantifier_binder: lang::quantifier_binder for (t : lang.BinderTarget) (g : Bool) {
  target := t,
  global? := g,
  accepted? := (Fren.Core.quantifierBinder (toBinderTarget t) g).1,
  behaviours? := (Fren.Core.quantifierBinder (toBinderTarget t) g).2,
} by
  intro t g _
  cases t <;> cases g <;> simp [fren_spec, toBinderTarget, Fren.Core.quantifierBinder]

def toGuardOperand : lang.GuardOperand → Fren.Core.GuardOperand
  | .Name => .name
  | .Free => .free
  | .Later => .later
def toGuardRelation : lang.GuardRelation → Fren.Core.GuardRelation
  | .Lt => .lt
  | .Le => .le
  | .Gt => .gt
  | .Ge => .ge
  | .In => .mem
  | .Other => .other
def ofGuardBound : Fren.Core.GuardBound → lang.GuardBound
  | .members => .Members
  | .lower => .Lower
  | .upper => .Upper
  | .none => .NoBound

theorem guard_bound_of_eq (a : lang.GuardOperand) (r : lang.GuardRelation) (b : lang.GuardOperand) :
    ofGuardBound (Fren.Core.guardBound (toGuardOperand a) (toGuardRelation r) (toGuardOperand b)).1 = lang.guard_bound_of a r b := by
  cases a <;> cases r <;> cases b <;> decide

/-- The position of the bound name that a side is, written alone. -/
def sideAlone (s : lang.GuardSide) : Option Nat := if 0 ≤ s.alone then some s.alone.toNat else none
/-- The positions of the bound names that a side names. -/
def sideNames (s : lang.GuardSide) : List Nat := s.names.toList.filterMap fun j => if 0 ≤ j then some j.toNat else none
/-- A conjunct as both front ends give it to `Fren.Core.boundDomain`. -/
def toCoreConjunct (c : lang.GuardConjunct) : Fren.Core.GuardConjunct lang.GuardSide := some (c.lhs, toGuardRelation c.relation, c.rhs)

theorem guard_alone_iff (s : lang.GuardSide) (k : Nat) : (sideAlone s == some k) = true ↔ s.alone = (k : Int) := by
  unfold sideAlone
  split
  · rename_i h; simp only [beq_iff_eq, Option.some.injEq]; omega
  · rename_i h; simp only [beq_iff_eq, reduceCtorEq, false_iff]; omega

theorem guard_names_iff (s : lang.GuardSide) (k : Nat) :
    (sideNames s).any (· ≥ k) = true ↔ ∃ j, j ∈ s.names ∧ j ≥ (k : Int) := by
  unfold sideNames
  simp only [List.any_eq_true, List.mem_filterMap, Seq.mem_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨j, hj, e⟩, hk⟩
    split at e
    · rename_i h; simp only [Option.some.injEq] at e; exact ⟨j, hj, by omega⟩
    · simp at e
  · rintro ⟨j, hj, hk⟩
    exact ⟨j.toNat, ⟨j, hj, by rw [if_pos (by omega)]⟩, by omega⟩

theorem guard_operand_eq (s : lang.GuardSide) (k : Nat) :
    Fren.Core.guardOperandOf sideAlone sideNames k s = toGuardOperand (lang.guard_operand s k) := by
  unfold Fren.Core.guardOperandOf lang.guard_operand
  by_cases h1 : s.alone = (k : Int)
  · rw [if_pos h1, if_pos ((guard_alone_iff s k).2 h1)]; rfl
  · have a : ¬ (sideAlone s == some k) = true := fun h => h1 ((guard_alone_iff s k).1 h)
    rw [if_neg h1, if_neg a]
    by_cases h2 : ∃ j, j ∈ s.names ∧ j ≥ (k : Int)
    · rw [if_pos h2, if_pos ((guard_names_iff s k).2 h2)]; rfl
    · have b : ¬ (sideNames s).any (· ≥ k) = true := fun h => h2 ((guard_names_iff s k).1 h)
      rw [if_neg h2, if_neg b]; rfl

theorem conjunct_bound_of (c : lang.GuardConjunct) (k : Nat) :
    ofGuardBound (Fren.Core.conjunctBound sideAlone sideNames k (toCoreConjunct c)).1 = lang.conjunct_bound c k := by
  simp only [Fren.Core.conjunctBound, toCoreConjunct, guard_operand_eq, lang.conjunct_bound, ← guard_bound_of_eq]

theorem ofGuardBound_inj (a b : Fren.Core.GuardBound) : (ofGuardBound a == ofGuardBound b) = (a == b) := by
  cases a <;> cases b <;> decide

theorem guard_idxOf_map (l : List Fren.Core.GuardBound) (b : Fren.Core.GuardBound) :
    (l.map ofGuardBound).idxOf? (ofGuardBound b) = l.idxOf? b := by
  simp only [List.idxOf?, List.findIdx?_map]
  congr 1; funext x; exact ofGuardBound_inj x b

theorem guard_domain_map (l : List Fren.Core.GuardBound) (n : Bool) :
    Fren.Core.guardDomainBy lang.GuardBound.Members .Lower .Upper (l.map ofGuardBound) n = Fren.Core.guardDomain l n := by
  unfold Fren.Core.guardDomain Fren.Core.guardDomainBy
  have m := guard_idxOf_map l .members; have lo := guard_idxOf_map l .lower; have up := guard_idxOf_map l .upper
  simp only [ofGuardBound] at m lo up
  rw [m, lo, up]

theorem guard_idx_some [DecidableEq β] (l : List β) (b : β) (n : Nat) :
    l.idxOf? b = some n ↔ ∃ h : n < l.length, l[n] = b ∧ ∀ j (hj : j < n), l[j] ≠ b := by
  simp [List.idxOf?, List.findIdx?_eq_some_iff_getElem]

theorem guard_idx_none [DecidableEq β] (l : List β) (b : β) : l.idxOf? b = none ↔ b ∉ l := by
  simp [List.idxOf?, List.findIdx?_eq_none_iff]
  constructor
  · intro h hm; exact absurd rfl (h b hm)
  · intro h x hx e; exact h (e ▸ hx)

section
variable (cs : List lang.GuardConjunct) (k : Int)

local notation "BS" => cs.map (fun c => lang.conjunct_bound c k)

theorem guard_nb_iff (b : lang.GuardBound) (n : Int) (hk : n ≤ cs.length) :
    (∀ j : Int, 0 ≤ j ∧ j < n → lang.conjunct_bound ((Seq.ofList cs).nth j) k ≠ b) ↔
      ∀ j (hj : j < (BS).length), (j : Int) < n → (BS)[j] ≠ b := by
  constructor
  · intro h j hj hjk
    have := h j ⟨by omega, hjk⟩
    rw [Seq.nth_of_lt _ _ (by omega) (by simp at hj ⊢; omega)] at this
    simpa using this
  · rintro h j ⟨h0, hjk⟩
    rw [Seq.nth_of_lt _ _ h0 (by simp; omega)]
    have := h j.toNat (by simp; omega) (by omega)
    simpa [Int.toNat_of_nonneg h0] using this

theorem guard_none_len_iff (b : lang.GuardBound) :
    lang.none_before? (Seq.ofList cs) k b (Seq.ofList cs).len = true ↔ (BS).idxOf? b = none := by
  simp only [lang.none_before?, decide_eq_true_eq]
  rw [guard_nb_iff _ _ _ _ (by simp), guard_idx_none]
  constructor
  · intro h hm
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
    exact h j hj (by simp at hj ⊢; omega) e
  · intro h j hj _ e
    exact h (e ▸ List.getElem_mem hj)

theorem guard_first_iff (b : lang.GuardBound) (j : Int) :
    ((0 ≤ j ∧ j < (Seq.ofList cs).len) ∧ lang.first_at? (Seq.ofList cs) k b j = true) ↔
      0 ≤ j ∧ (BS).idxOf? b = some j.toNat := by
  simp only [Seq.len_eq, Seq.toList_ofList, lang.first_at?, lang.none_before?, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, hl⟩, e, hn⟩
    rw [Seq.nth_of_lt _ _ h0 (by simpa using hl)] at e
    rw [guard_nb_iff _ _ _ _ (by omega)] at hn
    refine ⟨h0, (guard_idx_some _ _ _).2 ⟨by simp; omega, by simpa using e, fun i hi => hn i (by simp; omega) (by omega)⟩⟩
  · rintro ⟨h0, h⟩
    obtain ⟨hl, e, hb⟩ := (guard_idx_some _ _ _).1 h
    simp at hl
    refine ⟨⟨h0, by omega⟩, ?_, ?_⟩
    · rw [Seq.nth_of_lt _ _ h0 (by simp; omega)]; simpa using e
    · rw [guard_nb_iff _ _ _ _ (by omega)]
      intro i hi hik
      exact hb i (by omega)
end

def guardDomainOut : Fren.Core.GuardDomain → lang.DomainShape × Int × Int
  | .members k => (.Members, k, -1)
  | .range lo hi => (.Range, lo, hi)
  | .fromZero hi => (.FromZero, -1, hi)
  | .unbounded => (.Unbounded, -1, -1)

/-- The domain that the code finds, of the bound name at `k`. -/
abbrev guardDomainOf (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) : lang.DomainShape × Int × Int :=
  guardDomainOut (Fren.Core.boundDomain sideAlone sideNames (cs.toArray.map toCoreConjunct) k n).1

theorem guardDomainOf_eq (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) :
    guardDomainOf cs k n = guardDomainOut (Fren.Core.guardDomainBy lang.GuardBound.Members .Lower .Upper
      (cs.map fun c => lang.conjunct_bound c k) n) := by
  simp only [guardDomainOf, Fren.Core.boundDomain, ← guard_domain_map]
  congr 2
  simp [List.map_map, Function.comp_def, conjunct_bound_of]

theorem guard_domain_meets (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) :
    lang.guard_domain.ensures (Seq.ofList cs) k n (guardDomainOf cs k n).1 (guardDomainOf cs k n).2.1
      (guardDomainOf cs k n).2.2 := by
  rw [guardDomainOf_eq]
  unfold lang.guard_domain.ensures lang.guard_domain.ensure.members lang.guard_domain.ensure.range
    lang.guard_domain.ensure.from_zero lang.guard_domain.ensure.unbounded
  simp only [Fren.Core.guardDomainBy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j h
    obtain ⟨h0, e⟩ := (guard_first_iff cs k _ j).1 ⟨h.1, h.2⟩
    simp [e, guardDomainOut, Int.toNat_of_nonneg h0]
  · intro l h' h
    obtain ⟨⟨⟨⟨hl, hh⟩, hm⟩, hlo⟩, hup⟩ := h
    obtain ⟨l0, el⟩ := (guard_first_iff cs k _ l).1 ⟨hl, hlo⟩
    obtain ⟨h0, eh⟩ := (guard_first_iff cs k _ h').1 ⟨hh, hup⟩
    rw [guard_none_len_iff] at hm
    simp [hm, el, eh, guardDomainOut, Int.toNat_of_nonneg l0, Int.toNat_of_nonneg h0]
  · intro h' h
    obtain ⟨⟨⟨⟨hh, hn⟩, hm⟩, hlo⟩, hup⟩ := h
    obtain ⟨h0, eh⟩ := (guard_first_iff cs k _ h').1 ⟨hh, hup⟩
    rw [guard_none_len_iff] at hm hlo
    simp [hm, hlo, eh, hn, guardDomainOut, Int.toNat_of_nonneg h0]
  · rintro ⟨hm, hu | ⟨hn, hlo⟩⟩
    · rw [guard_none_len_iff] at hm hu
      simp only [hm, hu]
      simp [guardDomainOut]
    · rw [guard_none_len_iff] at hm hlo
      simp only [hm, hlo]
      split <;> simp_all [guardDomainOut]

-- For every conjunct, as both front ends classify its operands
-- (`Fren.Core.conjunctBound`).
impl guard_bound: lang::guard_bound for (l : lang.GuardOperand) (r : lang.GuardRelation) (h : lang.GuardOperand) {
  lhs := l,
  relation := r,
  rhs := h,
  bound := ofGuardBound (Fren.Core.guardBound (toGuardOperand l) (toGuardRelation r) (toGuardOperand h)).1,
  strict? := (Fren.Core.guardBound (toGuardOperand l) (toGuardRelation r) (toGuardOperand h)).2,
} by
  intro l r h _
  cases l <;> cases r <;> cases h <;> decide

-- For every guard, as both front ends give its conjuncts to
-- `Fren.Core.boundDomain`: each side by the bound name it is alone and those
-- it names, the domain by `List.idxOf?`, characterized by the spec's
-- `first_at?` and `none_before?`.
impl guard_domain: lang::guard_domain for (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) {
  conjuncts := Fren.Seq.ofList cs,
  k := k,
  nat? := n,
  shape := (guardDomainOf cs k n).1,
  lo := (guardDomainOf cs k n).2.1,
  hi := (guardDomainOf cs k n).2.2,
} by
  intro cs k n _
  exact guard_domain_meets cs k n

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
-- receiver is of an ordered type other than a number.
impl method_type: lang::method_type for (m : Fren.Core.Method) (k : lang.ValueType) (o : Bool) {
  method := toMethod m,
  receiver := k,
  ordered? := o,
  accepted? := m.accepts (k == .StringTy) (k == .SetTy) (k == .RelTy) (k == .SeqTy) (k == .IntTy || k == .NatTy) o,
  -- `string` is the receiver's type, and `elem` is never a result; the
  -- `min` and `max` of another ordered type give the receiver's type, as
  -- both front ends' `callMethod` does.
  result := if o && (m matches .min | .max) then k else match m.result with
    | .bool => .BoolTy | .int => .IntTy | .string | .elem => k | .set => .SetTy | .rel => .RelTy,
  n_params := m.arity,
} by
  intro m k o _
  cases m <;> cases k <;> cases o <;> simp [fren_spec, toMethod, Fren.Core.Method.accepts, Fren.Core.Method.relational,
    Fren.Core.Method.result,
    Fren.Core.Method.arity, Fren.Core.Method.params]

instance : Fren.Finite Fren.Core.Construct :=
  ⟨[.stringCompare, .stringAtom, .stringIndex, .stringSearch, .setAlgebra, .setFunction, .relational, .relationalCard, .seqArray, .seqWord,
    .quantifier], by intro x; cases x <;> simp⟩

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
  | .quantifier => .Quantifier

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

/-! ## Guarded arms -/

/-- What an arm does at a value, from whether its pattern matches it and
whether its guard holds there (`lang::ArmAt`). -/
def toArmAt : Bool × Bool → lang.ArmAt
  | (false, _) => .NoMatch
  | (true, false) => .GuardFails
  | (true, true) => .Taken

/-- The position of the first arm whose pattern matches and whose guard
holds, `-1` if none. -/
def firstTakenIdx (arms : List (Bool × Bool × Int)) : Int :=
  ((arms.findIdx? fun a => a.1 && a.2.1).map Int.ofNat).getD (-1)

theorem toArmAt_taken (a : Bool × Bool) : toArmAt a = .Taken ↔ (a.1 && a.2) = true := by
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [toArmAt]

/-- `firstCase`, when whether each case is taken is known, takes the first
that is. -/
theorem firstCase_find (l : List α) (p : α → Bool) (f : α → β) :
    Fren.Core.firstCase l (fun a => some (if p a then some (f a) else none)) = some ((l.find? p).map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [Fren.Core.firstCase, h, ih]

theorem find?_eq_findIdx? (l : List α) (p : α → Bool) : l.find? p = (l.findIdx? p).bind (l[·]?) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, List.findIdx?_cons]
    · simp [h, List.findIdx?_cons, ih]
      cases l.findIdx? p <;> simp

theorem firstTakenIdx_indexOf (arms : List (Bool × Bool × Int)) :
    firstTakenIdx arms = Fren.Seq.indexOf (Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)))
      (Fren.Seq.unit lang.ArmAt.Taken) 0 := by
  rw [indexOf_single, firstTakenIdx, List.findIdx?_map]
  congr 3
  funext a
  rcases a with ⟨_ | _, _ | _, _⟩ <;> rfl

impl guarded_match: lang::guarded_match for (arms : List (Bool × Bool × Int)) (k : Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  bodies := Fren.Seq.ofList (arms.map (·.2.2)),
  k := k,
  first := firstTakenIdx arms,
  value := ((Fren.Core.firstCase arms fun a => some (if a.1 && a.2.1 then some a.2.2 else none)).join).getD 0,
} by
  intro arms k _
  simp only [fren_spec]
  refine ⟨firstTakenIdx_indexOf arms, fun h0 => ?_⟩
  · simp only [firstTakenIdx, firstCase_find, find?_eq_findIdx?]
    cases hi : arms.findIdx? (fun a => a.1 && a.2.1) with
    | none => simp [firstTakenIdx, hi] at h0
    | some i =>
      obtain ⟨hlt, _, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      rw [Fren.Seq.nth_of_lt _ _ (by simp) (by simpa using hlt)]
      simp [List.getElem?_eq_getElem hlt]

/-! ## The overlap of patterns -/

section PatternOverlap
open Fren.Core

/-- The integers of an interval, as `lang::in_range?` reads a range. -/
def inIv (iv : Option Int × Option Int) (n : Int) : Prop := (∀ l, iv.1 = some l → l ≤ n) ∧ (∀ h, iv.2 = some h → n ≤ h)

/-- The integer of an interval that `Wit.ofInterval` picks. -/
def ivPoint : Option Int × Option Int → Int
  | (some l, _) => l
  | (none, some h) => h
  | (none, none) => 0

theorem meet_some (ty : Fren.Core.PatTy) (a b iv : Option Int × Option Int)
    (h : Fren.Core.meetIntervals ty a b = some iv) :
    inIv a (ivPoint iv) ∧ inIv b (ivPoint iv) ∧ (ty = .nat → 0 ≤ ivPoint iv) := by
  rcases a with ⟨_ | a1, _ | a2⟩ <;> rcases b with ⟨_ | b1, _ | b2⟩ <;>
    by_cases hn : ty = .nat <;>
    simp [Fren.Core.meetIntervals, Fren.Core.maxBound, Fren.Core.minBound, hn] at h <;>
    (try obtain ⟨hc, rfl⟩ := h) <;> (try subst h) <;>
    simp [inIv, ivPoint, hn] <;> omega

theorem meet_none (ty : Fren.Core.PatTy) (a b : Option Int × Option Int)
    (h : Fren.Core.meetIntervals ty a b = none) (n : Int) (ha : inIv a n) (hb : inIv b n) (hn : ty = .nat → 0 ≤ n) :
    False := by
  rcases a with ⟨_ | a1, _ | a2⟩ <;> rcases b with ⟨_ | b1, _ | b2⟩ <;>
    by_cases hN : ty = .nat <;>
    simp [Fren.Core.meetIntervals, Fren.Core.maxBound, Fren.Core.minBound, hN] at h <;>
    simp [inIv] at ha hb <;> simp [hN] at hn <;> omega

/-- An enumeration of `k + 1` variants, each with one payload value of `pty`. -/
def ovSigs (k : Nat) (pty : PatTy) : Sigs := fun _ => (Array.range (k + 1)).map fun i => (Lean.Name.mkNum .anonymous i, #[pty])

theorem ow_ii (sigs : Sigs) (ty : PatTy) (a b c d : Option Int) :
    Pat.overlapWit? sigs ty (.int a b) (.int c d) = (meetIntervals ty (a, b) (c, d)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp only [overlapStep, Pat.headKind, Pat.sameHead]
  cases meetIntervals ty (a, b) (c, d) <;> simp
  all_goals (intros; simp_all)

theorem sw_i (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.someWit? sigs ty (.int c d) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.someWit?]

theorem ow_wi (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.overlapWit? sigs ty (.wild false) (.int c d) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_i]
  all_goals (intros; simp_all)

theorem ow_iw (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.overlapWit? sigs ty (.int c d) (.wild false) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_i]
  all_goals (intros; simp_all)

theorem ow_ww (sigs : Sigs) (ty : PatTy) : Pat.overlapWit? sigs ty (.wild false) (.wild false) = some .any := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, Pat.someWit?]
  all_goals (intros; simp_all)

theorem sw_c (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.someWit? (ovSigs k pty) (.enum `E) (.ctor i #[.int c d]) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.someWit?]
  simp [ctorTys, ovSigs, sw_i, Ctor.wit, Nat.lt_succ_of_le hi]
  cases meetIntervals pty (c, d) (none, none) <;> simp
  rfl

theorem ow_wv (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E) (.wild false) (.ctor i #[.int c d]) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_c k pty i hi]
  all_goals (intros; simp_all)

theorem ow_vw (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E) (.ctor i #[.int c d]) (.wild false) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_c k pty i hi]
  all_goals (intros; simp_all)

theorem ow_vv (k : Nat) (pty : PatTy) (i j : Nat) (hi : i ≤ k) (a b c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E) (.ctor i #[.int a b]) (.ctor j #[.int c d]) =
      if i = j then (meetIntervals pty (a, b) (c, d)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv]
      else none := by
  rw [Pat.overlapWit?]
  simp only [overlapStep, Pat.headKind, Pat.sameHead]
  by_cases hij : i = j
  · subst hij
    simp [ctorTys, ovSigs, ow_ii, Ctor.wit, Nat.lt_succ_of_le hi]
    cases meetIntervals pty (a, b) (c, d) <;> simp
    rfl
  · simp [hij]
  all_goals (intros; simp_all)

/-- The bounds of a range, each where it has one. -/
def toBounds (r : lang.IntRange) : Option Int × Option Int :=
  (if r.bounded_below? then some r.low else none, if r.bounded_above? then some r.high else none)

def toPat (p : lang.SimplePattern) : Pat :=
  match p.shape with
  | .Wildcard => .wild false
  | .Integers => .int (toBounds p.range).1 (toBounds p.range).2
  | .Variant => .ctor p.variant.toNat #[.int (toBounds p.payload).1 (toBounds p.payload).2]

/-- The integer of a witness, `0` for any. -/
def numOf : Wit → Int
  | .int (some n) _ => n
  | _ => 0

/-- The variant, by its position, that a witness's path names. -/
def variantOf : Lean.Name → Int
  | .num _ k => k
  | _ => 0

/-- A witness as a value of `lang::pattern_overlap`, `0` for any integer. -/
def toValue : Option Wit → lang.SimpleValue
  | some (.int (some n) _) => ⟨0, n⟩
  | some (.ctor p args) => ⟨variantOf p, ((args[0]?).map numOf).getD 0⟩
  | _ => ⟨0, 0⟩

/-- The type of the integers: `Nat` or `Int`. -/
def ptyOf (nat : Bool) : PatTy := if nat then .nat else .int

/-- What `Pat.overlapWit?` gives two patterns of `lang::pattern_overlap`. -/
def owOf (f s : lang.SimplePattern) (nat : Bool) : Option Wit :=
  Pat.overlapWit? (ovSigs (max f.variant.toNat s.variant.toNat) (ptyOf nat))
    (if f.shape = .Variant ∨ s.shape = .Variant then .enum `E else ptyOf nat) (toPat f) (toPat s)

theorem ofInterval_eq (iv : Option Int × Option Int) :
    Wit.ofInterval iv = .int (some (ivPoint iv)) (some (ivPoint iv)) := by
  rcases iv with ⟨_ | _, _ | _⟩ <;> rfl

theorem inIv_bounds (r : lang.IntRange) (n : Int) :
    inIv (toBounds r) n ↔ ((r.bounded_below? = false ∨ r.low ≤ n) ∧ (r.bounded_above? = false ∨ n ≤ r.high)) := by
  rcases r with ⟨_ | _, l, _ | _, h⟩ <;> simp [inIv, toBounds]

theorem natOk (nat : Bool) (n : Int) : (ptyOf nat = .nat → 0 ≤ n) ↔ (nat = false ∨ 0 ≤ n) := by
  cases nat <;> simp [ptyOf]

theorem inIv_none (n : Int) : inIv (none, none) n := by simp [inIv]

-- Both front ends decide whether two arms' patterns overlap, and name the
-- value that both match, by `Pat.overlapWit?`: here of the patterns of
-- one value, `_`, ranges and variants with one value of a payload, as the
-- front ends resolve them (`toPat`), and its witness read back (`toValue`).
impl pattern_overlap: lang::pattern_overlap for (first second : lang.SimplePattern) (nat : Bool) (v : lang.SimpleValue) {
  first := first,
  second := second,
  nat? := nat,
  v := v,
  overlap? := (owOf first second nat).isSome,
  witness := toValue (owOf first second nat),
} by
  intro first second nat v hA
  rcases first with ⟨fs, fr, fv, fp⟩
  rcases second with ⟨ss, sr, sv, sp⟩
  simp [lang.pattern_overlap.assumes, lang.pattern_overlap.assume.typed, lang.pattern_overlap.assume.variants] at hA
  obtain ⟨hfv, hsv⟩ := hA
  simp only [lang.pattern_overlap.ensures, lang.pattern_overlap.ensure.common, lang.pattern_overlap.ensure.complete]
  cases fs <;> cases ss <;> simp at hfv <;> simp [owOf, toPat]
  · simp [ow_ww, toValue]
  · rw [ow_wi]
    cases hm : meetIntervals (ptyOf nat) ((toBounds sr).fst, (toBounds sr).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds sr _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- `_` and a variant.
    rw [ow_wv _ _ _ (Nat.le_max_right _ _)]
    cases hm : meetIntervals (ptyOf nat) ((toBounds sp).fst, (toBounds sp).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro _ h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds sp _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.2]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- A range and `_`.
    rw [ow_iw]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fr).fst, (toBounds fr).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fr _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- Two ranges.
    rw [ow_ii]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fr).fst, (toBounds fr).snd) ((toBounds sr).fst, (toBounds sr).snd) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h1' h2' h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fr _).2 ⟨h1, h2⟩) ((inIv_bounds sr _).2 ⟨h1', h2'⟩)
        ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, h2, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1 h2; rw [natOk] at h3; simp_all
  · -- A variant and `_`.
    rw [ow_vw _ _ _ (Nat.le_max_left _ _)]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fp).fst, (toBounds fp).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro _ h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fp _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.1]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- Two variants.
    rw [ow_vv _ _ _ _ (Nat.le_max_left _ _)]
    by_cases hij : fv.toNat = sv.toNat
    · have hfs : fv = sv := by omega
      subst hfs
      simp only [↓reduceIte]
      cases hm : meetIntervals (ptyOf nat) ((toBounds fp).fst, (toBounds fp).snd) ((toBounds sp).fst, (toBounds sp).snd) with
      | none =>
        simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
        intro _ h1 h2 _ h1' h2' h3
        exact (meet_none _ _ _ hm v.number ((inIv_bounds fp _).2 ⟨h1, h2⟩) ((inIv_bounds sp _).2 ⟨h1', h2'⟩)
          ((natOk nat _).2 h3)).elim
      | some iv =>
        obtain ⟨h1, h2, h3⟩ := meet_some _ _ _ _ hm
        simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.1]
        rw [inIv_bounds] at h1 h2; rw [natOk] at h3; simp_all
    · simp only [if_neg hij, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 _ _ h2
      omega
end PatternOverlap

/-! ## Tables over a scrutinee -/

-- `checkTableArms` rejects a pair, or asks about it, by `tableArmPair`.
impl table_arm_pair: lang::table_arm_pair for (o g w : Bool) {
  overlap? := o,
  guarded? := g,
  otherwise? := w,
  rejected? := (Fren.Core.tableArmPair o g w).1,
  asked? := (Fren.Core.tableArmPair o g w).2,
} by
  intro o g w _
  cases o <;> cases g <;> cases w <;> simp [fren_spec, Fren.Core.tableArmPair]

/-- What an arm of a table over a scrutinee is, from whether its pattern is
`_` and whether it has a guard (`lang::TableArm`). -/
def armKind (a : Bool × Bool) : lang.TableArm := if a.2 then .Guarded else if a.1 then .Wildcard else .Unguarded

/-- Whether the static rules reject arms `a` and `b` of `arms`, each
whether its pattern is `_` and whether it has a guard, as
`checkTableArms` decides it (`armPair`), the patterns of arms `a` and `b`
overlapping where `ovm a b`. -/
def rejectedOf (arms : List (Bool × Bool)) (ovm : Nat → Nat → Bool) (a b : Nat) : Bool :=
  (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (a < arms.length) && ovm a b) a b).1

/-- The first element of `l` that satisfies `p` is `x` exactly when `x`
satisfies it and none before the first `x` does. -/
theorem find?_eq_some_iff_takeWhile [BEq α] [LawfulBEq α] (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) :
    l.find? p = some x ↔ p x = true ∧ ((l.takeWhile (· != x)).any p) = false := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax
      by_cases hp : p a
      · simp [hp]
      · simp only [List.find?_cons, hp, List.takeWhile_cons, bne_self_eq_false]
        simp only [Bool.false_eq_true, false_and, iff_false]
        exact fun h => hp (List.find?_some h)
    · have hx' : x ∈ l := by simpa [Ne.symm hax] using hx
      have hne : (a != x) = true := by simpa using hax
      by_cases hp : p a
      · simp [hp, hne, hax]
      · simp [hp, hne, ih hx']

theorem mem_armPairs (n i j : Nat) (hij : i < j) (hj : j < n) : (i, j) ∈ Fren.Core.armPairs n := by
  simp [Fren.Core.armPairs]
  exact ⟨j, hj, i, hij, rfl, rfl⟩

-- `checkTableArms` reports the first pair that `armPair` rejects
-- (`firstRejected?`), and asks about the pairs that it asks about.
impl table_arms: lang::table_arms for (arms : List (Bool × Bool)) (ovm : Nat → Nat → Bool) (i j : Nat) {
  arms := Fren.Seq.ofList (arms.map armKind),
  overlaps := Fren.Seq.ofList ((List.range arms.length).map fun k => if ovm k j then .Overlapping else .Apart),
  i := i,
  j := j,
  earlier_rejected? := ((Fren.Core.armPairs arms.length).takeWhile (· != (i, j))).any fun (a, b) => rejectedOf arms ovm a b,
  rejected? := rejectedOf arms ovm i j,
  asked? := (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (i < arms.length) && ovm i j) i j).2,
  reported? := Fren.Core.firstRejected? arms.length (rejectedOf arms ovm) == some (i, j),
} by
  intro arms ovm i j _
  simp only [fren_spec]
  simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map, List.length_range]
  have hrule : ∀ a b : Nat, (rejectedOf arms ovm a b = true ↔
      ((a < arms.length ∧ ovm a b = true) ∧ ¬((a < arms.length ∧ (arms.getD a (false, false)).2 = true) ∨
        (b < arms.length ∧ (arms.getD b (false, false)).2 = true)) ∧
        ¬(b + 1 = arms.length ∧ (arms.getD b (false, false)).1 = true ∧ (arms.getD b (false, false)).2 = false))) := by
    intro a b
    simp only [rejectedOf, Fren.Core.armPair, Fren.Core.tableArmPair, Fren.Core.isOtherwise]
    by_cases ha : a < arms.length <;> by_cases hb : b < arms.length <;>
      simp [ha, hb, List.getD_eq_getElem?_getD]
    by_cases h1 : arms[b].fst <;> by_cases h2 : arms[b].snd <;> by_cases h3 : arms[a].snd <;>
      by_cases h4 : ovm a b <;> by_cases h5 : b + 1 = arms.length <;> simp_all
  have hask : (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (i < arms.length) && ovm i j)
      i j).2 = true ↔
      ((i < arms.length ∧ ovm i j = true) ∧ ((i < arms.length ∧ (arms.getD i (false, false)).2 = true) ∨
        (j < arms.length ∧ (arms.getD j (false, false)).2 = true)) ∧
        ¬(j + 1 = arms.length ∧ (arms.getD j (false, false)).1 = true ∧ (arms.getD j (false, false)).2 = false)) := by
    simp only [Fren.Core.armPair, Fren.Core.tableArmPair, Fren.Core.isOtherwise]
    by_cases ha : i < arms.length <;> by_cases hb : j < arms.length <;>
      simp [ha, hb, List.getD_eq_getElem?_getD]
    all_goals by_cases h1 : arms[j].fst <;> by_cases h2 : arms[j].snd <;> by_cases h4 : ovm i j <;>
      by_cases h5 : j + 1 = arms.length <;> simp_all
  have hfirst : (Fren.Core.firstRejected? arms.length (rejectedOf arms ovm) == some (i, j)) = true ↔
      (i < j ∧ j < arms.length ∧ rejectedOf arms ovm i j = true ∧
        ((Fren.Core.armPairs arms.length).takeWhile (· != (i, j))).any (fun (a, b) => rejectedOf arms ovm a b) = false) := by
    simp only [beq_iff_eq, Fren.Core.firstRejected?]
    by_cases hp : i < j ∧ j < arms.length
    · rw [find?_eq_some_iff_takeWhile _ _ _ (mem_armPairs _ _ _ hp.1 hp.2)]
      simp [hp]
    · constructor
      · intro h
        have hm := List.mem_of_find?_eq_some h
        simp [Fren.Core.armPairs] at hm
        omega
      · intro h; exact absurd ⟨h.1, h.2.1⟩ hp
  have kG (a : Bool × Bool) : armKind a = .Guarded ↔ a.2 = true := by
    rcases a with ⟨_ | _, _ | _⟩ <;> simp [armKind]
  have kW (a : Bool × Bool) : armKind a = .Wildcard ↔ (a.1 = true ∧ a.2 = false) := by
    rcases a with ⟨_ | _, _ | _⟩ <;> simp [armKind]
  have oO (b : Bool) : ((if b then lang.Overlap.Overlapping else lang.Overlap.Apart) = .Overlapping) ↔ b = true := by
    cases b <;> simp
  have hje : ((j : Int) = (arms.length : Int) - 1) ↔ j + 1 = arms.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hrule]
    by_cases hi : i < arms.length <;> by_cases hj : j < arms.length <;>
      simp [hi, hj, kG, kW, oO, hje, List.getD_eq_getElem?_getD]
    all_goals first | (intros; omega) | (simp only [and_assoc]; done) | (constructor <;> intro h <;> simp_all)
  · rw [hask]
    by_cases hi : i < arms.length <;> by_cases hj : j < arms.length <;>
      simp [hi, hj, kG, kW, oO, hje, List.getD_eq_getElem?_getD]
    all_goals first | (intros; omega) | (simp only [and_assoc]; done) | (constructor <;> intro h <;> simp_all)
  · rw [hfirst]
    constructor
    · rintro ⟨hij, hjn, hr, he⟩
      refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hr⟩, ?_⟩
      simpa using he
    · rintro ⟨⟨⟨⟨_, hij⟩, hjn⟩, hr⟩, he⟩
      exact ⟨by omega, by omega, hr, by simpa using he⟩

/-- `checkTableArms` reports a table at the first pair of its arms that
`armPair` rejects, by `firstRejected?`, as `table_arms`'s `reported?` is
bound: with `F0391`, at the later arm, naming the earlier one, where no
arm stands for too many cases. -/
theorem checkTableArms_reports (sigs : Fren.Core.Sigs) (ty : Fren.Core.PatTy) (arms : Array Fren.Core.Pat)
    (guarded : Array Bool) (i j : Nat) (hc : arms.findIdx? (·.cases > Fren.Core.maxCases) = none)
    (hr : Fren.Core.firstRejected? arms.size (fun i j => (Fren.Core.tableArmVerdict sigs ty arms guarded i j).1) =
      some (i, j)) :
    Fren.Core.checkTableArms sigs ty arms guarded =
      .error (some (j, none), Fren.Core.armsOverlapMsg i (arms[i]!.overlapWit? sigs ty arms[j]!).get!) := by
  unfold Fren.Core.checkTableArms
  simp only [hc, hr]
  rfl

/-- The arms of a table over a scrutinee as the evaluator tries them, the
`_` arm last, whose pattern matches and which has no guard. -/
def evalArms (arms : List (Bool × Bool × Int)) (otherwise : Option Int) : List (Bool × Bool × Int) :=
  arms ++ otherwise.toList.map fun v => (true, true, v)

/-- The value that the evaluator gives a table over a scrutinee: that of
its first arm taken (`Fren.Core.firstCase`), as of the `match` it means. -/
def evalTable (arms : List (Bool × Bool × Int)) (otherwise : Option Int) : Int :=
  ((Fren.Core.firstCase (evalArms arms otherwise) fun a => some (if a.1 && a.2.1 then some a.2.2 else none)).join).getD 0

theorem evalTable_first (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (i : Nat)
    (hi : arms.findIdx? (fun a => a.1 && a.2.1) = some i) :
    evalTable arms otherwise = (arms[i]?.map (·.2.2)).getD 0 := by
  obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have hf : (evalArms arms otherwise).find? (fun a => a.1 && a.2.1) = some arms[i] := by
    rw [evalArms, List.find?_append, find?_eq_findIdx?, hi]
    simp [List.getElem?_eq_getElem hlt]
  simp only [evalTable, firstCase_find, hf, List.getElem?_eq_getElem hlt]
  simp

theorem evalTable_none (arms : List (Bool × Bool × Int)) (v : Int)
    (hi : arms.findIdx? (fun a => a.1 && a.2.1) = none) : evalTable arms (some v) = v := by
  have hn : arms.find? (fun a => a.1 && a.2.1) = none := by
    rw [find?_eq_findIdx?, hi]; rfl
  rw [evalTable, firstCase_find, evalArms, List.find?_append, hn]
  simp

theorem evalTable_held (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (h0 : firstTakenIdx arms ≥ 0) :
    evalTable arms otherwise = (Fren.Seq.ofList (arms.map (·.2.2))).nth (firstTakenIdx arms) := by
  cases hi : arms.findIdx? (fun a => a.1 && a.2.1) with
  | none => simp [firstTakenIdx, hi] at h0
  | some i =>
    obtain ⟨hlt, _, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    rw [evalTable_first arms otherwise i hi, firstTakenIdx, hi,
      Fren.Seq.nth_of_lt _ _ (by simp) (by simpa using hlt)]
    simp [List.getElem?_eq_getElem hlt]

theorem evalTable_otherwise (arms : List (Bool × Bool × Int)) (otherwise : Option Int)
    (h1 : firstTakenIdx arms = -1) (h2 : Fren.Seq.ofList otherwise.toList ≠ ∅) :
    evalTable arms otherwise = (Fren.Seq.ofList otherwise.toList).nth 0 := by
  cases otherwise with
  | none => exact absurd rfl h2
  | some v =>
    have hi : arms.findIdx? (fun a => a.1 && a.2.1) = none := by
      cases h : arms.findIdx? (fun a => a.1 && a.2.1) with
      | none => rfl
      | some i => simp [firstTakenIdx, h] at h1
    rw [evalTable_none arms v hi, Fren.Seq.nth_of_lt _ _ (by simp) (by simp)]
    rfl

impl table_eval: lang::table_eval for (arms : List (Bool × Bool × Int)) (otherwise : Option Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  values := Fren.Seq.ofList (arms.map (·.2.2)),
  otherwise := Fren.Seq.ofList otherwise.toList,
  first := firstTakenIdx arms,
  value := evalTable arms otherwise,
} by
  intro arms otherwise _
  simp only [fren_spec]
  exact ⟨firstTakenIdx_indexOf arms, evalTable_held arms otherwise, fun ⟨h1, h2⟩ => evalTable_otherwise arms otherwise h1 h2⟩

-- The meaning of a table over a scrutinee, as the evaluator gives it: the
-- value of its first arm taken, which is the one where they are disjoint.
impl table_match: lang::table_match for (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (k : Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  values := Fren.Seq.ofList (arms.map (·.2.2)),
  otherwise := Fren.Seq.ofList otherwise.toList,
  k := k,
  one := firstTakenIdx arms,
  disjoint? := decide (Fren.Seq.indexOf (Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)))
    (Fren.Seq.unit lang.ArmAt.Taken) (firstTakenIdx arms + 1) = -1),
  value := evalTable arms otherwise,
} by
  intro arms otherwise k _
  simp only [fren_spec]
  rw [← firstTakenIdx_indexOf arms]
  exact ⟨⟨rfl, rfl⟩, fun ⟨_, h0⟩ => evalTable_held arms otherwise h0,
    fun ⟨h1, h2⟩ => evalTable_otherwise arms otherwise h1 h2⟩

end Fren.Impls
