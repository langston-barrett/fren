-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

def toPosition : Fren.Core.Position → lang.Position
  | .declared => .Declared
  | .shared => .Shared
  | .compared => .Compared
  | .synthesized => .Synthesized

def toExprSite : Fren.Core.ExprSite → lang.ExprSite
  | .binding => .Binding
  | .recordField => .RecordField
  | .newtypeValue => .NewtypeValue
  | .functionArgument => .FunctionArgument
  | .payload => .Payload
  | .seqMethodArgument => .SeqMethodArgument
  | .orderedMethodArgument => .OrderedMethodArgument
  | .outputDefinition => .OutputDefinition
  | .functionBody => .FunctionBody
  | .constantValue => .ConstantValue
  | .typedDefinition => .TypedDefinition
  | .typedClosureBody => .TypedClosureBody
  | .setOperand => .SetOperand
  | .concatOperand => .ConcatOperand
  | .branch => .Branch
  | .armBody => .ArmBody
  | .rowValue => .RowValue
  | .element => .Element
  | .parenthesized => .Parenthesized
  | .letBody => .LetBody
  | .pairMember => .PairMember
  | .comparedOperand => .ComparedOperand
  | .subsetOperand => .SubsetOperand
  | .membershipRight => .MembershipRight
  | .membershipLeft => .MembershipLeft
  | .joinOperand => .JoinOperand
  | .stringOperand => .StringOperand
  | .methodArgument => .MethodArgument
  | .receiver => .Receiver
  | .scrutinee => .Scrutinee
  | .armGuard => .ArmGuard
  | .rowCondition => .RowCondition
  | .updatedRecord => .UpdatedRecord
  | .untypedDefinition => .UntypedDefinition
  | .untypedClosureBody => .UntypedClosureBody
  | .countArgument => .CountArgument

-- For every site: its position, and the decision that both front ends make
-- for each part of an expression, by `ExprSite.checked`. That each
-- classifies its syntax into the right sites and shapes is not proved here,
-- but tested by both on the same ui tests.
impl checked: lang::checked for (s : Fren.Core.ExprSite) (e sib : Bool) {
  site := toExprSite s,
  expected? := e,
  sibling? := sib,
  position := toPosition s.position,
  checked? := s.checked e sib,
} by
  intro s e sib _
  cases s <;> cases e <;> cases sib <;>
    simp [fren_spec, toExprSite, toPosition, Fren.Core.ExprSite.position, Fren.Core.ExprSite.checked,
      Fren.Core.Position.checked, lang.site_position]

def toShape : Fren.Core.TypeShape → lang.Shape
  | .emptyLiteral => .EmptyLiteral
  | .anyPart _ => .SharedParts
  | .pair .. => .Pair
  | .construction _ => .Construction
  | .other => .Other

/-- The shared parts of an expression of shape `s`, or a pair's members, or,
for a construction, each type parameter's values whose declared types
mention it, as one shape that synthesizes when one of them does. -/
def shapeParts : Fren.Core.TypeShape → List Fren.Core.TypeShape
  | .anyPart ps => ps
  | .pair a b => [a, b]
  | .construction ps => ps.map .anyPart
  | .emptyLiteral | .other => []

theorem anySynthesizes_eq_any (ps : List Fren.Core.TypeShape) :
    Fren.Core.TypeShape.anySynthesizes ps = ps.any Fren.Core.TypeShape.synthesizes := by
  induction ps with
  | nil => simp [Fren.Core.TypeShape.anySynthesizes]
  | cons p ps ih => simp [Fren.Core.TypeShape.anySynthesizes, ih]

theorem allGiven_eq_all (ps : List (List Fren.Core.TypeShape)) :
    Fren.Core.TypeShape.allGiven ps = (ps.map .anyPart).all Fren.Core.TypeShape.synthesizes := by
  induction ps with
  | nil => simp [Fren.Core.TypeShape.allGiven]
  | cons p ps ih => simp [Fren.Core.TypeShape.allGiven, Fren.Core.TypeShape.synthesizes, ih]

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
  | construction ps =>
    simp only [fren_spec, toShape, shapeParts, Fren.Core.TypeShape.synthesizes, allGiven_eq_all]
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    simp
    rw [Int.natCast_inj, ← List.length_map (f := Fren.Core.TypeShape.anyPart), List.length_filter_eq_length_iff]
    simp

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
  | .argument => .Argument

impl nat_place: lang::nat_place for (p : Fren.Core.TypePlace) {
  place := toTypePlace p,
  accepted? := Fren.Core.natPlaceAccepted p,
} by
  intro p _
  cases p <;> simp [fren_spec, toTypePlace, Fren.Core.natPlaceAccepted]

impl subset_place: lang::subset_place for (p : Fren.Core.SubsetPlace) (r : Bool) {
  place := match p with | .top => .Top | .field => .Field | .payload => .Payload | .element => .Element,
  recursive? := r && p == .payload,
  decidable? := Fren.Core.subsetPlaceDecidable p (r && p == .payload),
} by
  intro p r _
  cases p <;> cases r <;> simp [fren_spec, Fren.Core.subsetPlaceDecidable]

impl pattern_finite: lang::pattern_finite for (b i n : Bool) {
  base_finite? := b && !i,
  integers? := i,
  bounded? := n,
  finite? := Fren.Core.patternFinite (b && !i) i n,
} by
  intro b i n _
  cases b <;> cases i <;> cases n <;> simp [fren_spec, Fren.Core.patternFinite]

impl subset_widening: lang::subset_widening for (p w : Bool) {
  restricted? := p,
  widened? := w,
  accepted? := (Fren.Core.subsetWidening w p).1,
  obliged? := (Fren.Core.subsetWidening w p).2,
} by
  intro p w _
  cases p <;> cases w <;> simp [fren_spec, Fren.Core.subsetWidening]

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

theorem kindOf_eq_nat (t : Fren.Core.Ty) : kindOf t = .NatTy ↔ t = .nat := by
  cases t <;> simp [kindOf]

-- For every site and two types that may be given: the type that both
-- front ends expect of a part (`ExprSite.expected`), or, where none is
-- expected, the whole's.
impl expected_type: lang::expected_type for (site : Fren.Core.ExprSite) (w s : Option Fren.Core.Ty) {
  site := toExprSite site,
  whole? := w.isSome,
  whole := w.getD .bool,
  sibling? := s.isSome,
  sibling := s.getD .bool,
  typed? := (site.expected w s).isSome,
  expected := (site.expected w s).getD (w.getD .bool),
} by
  intro site w s _
  cases site
  all_goals cases w <;> cases s
  all_goals simp [fren_spec, toExprSite, lang.site_position, Fren.Core.ExprSite.expected, Fren.Core.ExprSite.wholeFirst,
    Fren.Core.ExprSite.position, Fren.Core.Position.expected, kindOf_eq_nat]
  all_goals (try split) <;> simp_all

def toWrittenShape : Fren.Core.WrittenShape → lang.WrittenShape
  | .seqLiteral => .SeqLiteral
  | .concat .. => .Concat
  | .conditional .. => .Conditional
  | .match _ => .Match
  | .table _ => .Table
  | .let _ => .Let
  | .parenthesized _ => .Parenthesized
  | .other => .Other

/-- The shared parts of an expression of shape `s`. -/
def writtenParts : Fren.Core.WrittenShape → List Fren.Core.WrittenShape
  | .concat a b | .conditional a b => [a, b]
  | .match ps | .table ps => ps
  | .let e | .parenthesized e => [e]
  | .seqLiteral | .other => []

theorem anySequence_eq_any (ps : List Fren.Core.WrittenShape) :
    Fren.Core.WrittenShape.anySequence ps = ps.any Fren.Core.WrittenShape.sequence := by
  induction ps with
  | nil => simp [Fren.Core.WrittenShape.anySequence]
  | cons p ps ih => simp [Fren.Core.WrittenShape.anySequence, ih]

-- For every shape, with its parts' own decisions: the walk that both front
-- ends decide by (`seqShaped`).
impl written_sequence: lang::written_sequence for (s : Fren.Core.WrittenShape) {
  shape := toWrittenShape s,
  parts := (writtenParts s).length,
  sequences := ((writtenParts s).filter Fren.Core.WrittenShape.sequence).length,
  sequence? := s.sequence,
} by
  intro s _
  have parts : s.sequence = (match s with
      | .seqLiteral => true
      | .other => false
      | _ => (writtenParts s).any Fren.Core.WrittenShape.sequence) := by
    cases s <;> simp [Fren.Core.WrittenShape.sequence, writtenParts, anySequence_eq_any]
  rw [parts]
  cases s
  case seqLiteral | other => simp [fren_spec, toWrittenShape]
  all_goals
    simp only [fren_spec, toWrittenShape]
    cases h : (writtenParts _).any Fren.Core.WrittenShape.sequence <;>
      simp_all [List.any_eq_false, List.any_eq_true, List.filter_eq_nil_iff, List.length_pos_iff]

end Fren.Impls
