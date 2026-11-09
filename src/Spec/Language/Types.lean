import Fren.Impl
import Fren.Literate
import FrenBase.Binding
import FrenExpr

open Fren.Lang

#fren_md "Types.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Types

/-- A local has its actual context entry, not merely some type at an
in-bounds index. This law uses the existing production binding primitive. -/
theorem local_type_unique {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (a b : Ty) (ha : FrenBase.Binding.HasType ctx i a)
    (hb : FrenBase.Binding.HasType ctx i b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

theorem local_type_scoped {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (ty : Ty) (h : FrenBase.Binding.HasType ctx i ty) :
    FrenBase.Binding.InScope ctx.length i :=
  FrenBase.Binding.hasType_scoped h

-- Equal lengths and valid indices alone cannot choose a local's type.
#guard FrenBase.Binding.HasType [true, false] 0 true
#guard ¬ FrenBase.Binding.HasType [true, false] 0 false
#guard FrenBase.Binding.HasType [false, true] 0 false
#guard ¬ FrenBase.Binding.HasType ([] : List Bool) 0 true

/-- The normative payload type uses the same generic production type carrier.
No tag/identity pair or display-string encoding is involved. -/
def coreType : spec.types.Ty → FrenExpr.ValueType (Fren.Seq String)
  | .Boolean => .bool
  | .Integer => .int
  | .Nominal owner => .enum owner

theorem core_type_injective : Function.Injective coreType := by
  intro a b h
  cases a <;> cases b <;> simp_all [coreType]

/-- Exact equality on canonical components instantiates production compatibility. -/
theorem core_compatibility (a b : spec.types.Ty) :
    @FrenExpr.ValueType.compatible (Fren.Seq String)
      ⟨fun x y => decide (x = y)⟩ (coreType a) (coreType b) = true ↔
        spec.types.compatible_type? a b := by
  cases a <;> cases b <;>
    simp [coreType, FrenExpr.ValueType.compatible, fren_spec]

/-- These adapters change only the spec's finite tags, not the deciding
implementation. Int equality atoms instantiate the same generic production
primitive that the walker instantiates with canonical ItemId. -/
def primitiveType : spec.types.ValueKind → Int → FrenExpr.ValueType Int
  | .Boolean, _ => .bool
  | .Integer, _ => .int
  | .Nominal, id => .enum id

def primitiveKind : FrenExpr.ValueType Int → spec.types.ValueKind
  | .bool => .Boolean | .int => .Integer | .enum _ => .Nominal

def primitiveUnary : spec.types.Unary → FrenAst.UnaryOp
  | .Negate => .neg | .Not => .not

def primitiveBinary : spec.types.Binary → FrenAst.BinaryOp
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Mod => .mod
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

/-- The normative unary rule agrees with the actual generic primitive. -/
theorem core_unary (op : spec.types.Unary) (operand result : spec.types.Ty) :
    @FrenExpr.unary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (primitiveUnary op) (coreType operand) = some (coreType result) ↔
        spec.types.unary_type? op operand result := by
  cases op <;> cases operand <;> cases result <;>
    simp [coreType, primitiveUnary, FrenExpr.unary, FrenExpr.unaryOperand,
      FrenExpr.ValueType.compatible, fren_spec]

/-- Every operator and nominal identity is covered; there is no bounded enum domain. -/
theorem core_binary (op : spec.types.Binary) (left right result : spec.types.Ty) :
    @FrenExpr.binary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (primitiveBinary op) (coreType left) (coreType right) = some (coreType result) ↔
        spec.types.binary_type? op left right result := by
  cases op <;> cases left <;> cases right <;> cases result <;>
    simp [coreType, primitiveBinary, FrenExpr.binary, FrenExpr.binaryOperand,
      FrenExpr.binaryResult, FrenExpr.ValueType.compatible, fren_spec, eq_comm]

impl compatibility: compatible for
    (left right : spec.types.ValueKind) (left_id right_id : Int) {
  left := left, right := right, left_id := left_id, right_id := right_id,
  same? := (primitiveType left left_id).compatible (primitiveType right right_id)
} by
  intro left right left_id right_id _
  cases left <;> cases right <;>
    simp [fren_spec, primitiveType, FrenExpr.ValueType.compatible, beq_iff_eq]

impl unary: unary for (op : spec.types.Unary) (operand : spec.types.ValueKind) {
  op := op, operand := operand,
  accepted? := (FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).isSome,
  result := primitiveKind ((FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).getD .bool)
} by
  intro op operand _
  cases op <;> cases operand <;>
    simp [fren_spec, primitiveUnary, primitiveType, primitiveKind, FrenExpr.unary,
      FrenExpr.unaryOperand, FrenExpr.ValueType.compatible]

impl binary: binary for
    (op : spec.types.Binary) (left right : spec.types.ValueKind) (left_id right_id : Int) {
  op := op, left := left, right := right, left_id := left_id, right_id := right_id,
  accepted? := (FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).isSome,
  result := primitiveKind ((FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).getD .bool)
} by
  intro op left right left_id right_id _
  cases op <;> cases left <;> cases right <;>
    simp [fren_spec, primitiveBinary, primitiveType, primitiveKind, FrenExpr.binary,
      FrenExpr.binaryOperand, FrenExpr.binaryResult, FrenExpr.ValueType.compatible, beq_iff_eq]
  all_goals by_cases h : left_id = right_id <;> simp_all [primitiveKind, eq_comm]

/-- Guarded integer quantifiers are finite for every supplied upper bound. -/
theorem forall_below_iff (upper : Int) (p : Int → Prop) :
    (∀ i : Int, 0 ≤ i ∧ i < upper → p i) ↔
      ∀ i : Fin upper.toNat, p (i.val : Int) := by
  constructor
  · intro h i
    exact h i.val (by have := i.isLt; omega)
  · intro h i hi
    have bound : i.toNat < upper.toNat := by omega
    have eq : (i.toNat : Int) = i := by omega
    simpa only [eq] using h ⟨i.toNat, bound⟩

theorem exists_below_iff (upper : Int) (p : Int → Prop) :
    (∃ i : Int, (0 ≤ i ∧ i < upper) ∧ p i) ↔
      ∃ i : Fin upper.toNat, p (i.val : Int) := by
  constructor
  · rintro ⟨i, hi, hp⟩
    have bound : i.toNat < upper.toNat := by omega
    refine ⟨⟨i.toNat, bound⟩, ?_⟩
    have eq : (i.toNat : Int) = i := by omega
    simpa only [eq] using hp
  · rintro ⟨i, hp⟩
    refine ⟨i.val, ?_, hp⟩
    constructor <;> have := i.isLt <;> omega

theorem forall_below_flat (upper : Int) (p : Int → Prop) :
    (∀ i : Int, 0 ≤ i → i < upper → p i) ↔
      ∀ i : Fin upper.toNat, p (i.val : Int) := by
  simpa only [and_imp] using forall_below_iff upper p

theorem exists_below_flat (upper : Int) (p : Int → Prop) :
    (∃ i : Int, 0 ≤ i ∧ i < upper ∧ p i) ↔
      ∃ i : Fin upper.toNat, p (i.val : Int) := by
  simpa only [and_assoc] using exists_below_iff upper p

-- Expanding generic layers and bounded arm tables needs more simplifier work.
set_option maxHeartbeats 1000000

-- A shared simp set keeps each finite example on the same exact definitions.
attribute [local simp] forall_below_flat exists_below_flat Fin.forall_fin_succ
  Fin.exists_fin_succ Fren.Seq.ofList Fren.Seq.unit Fren.Seq.len Fren.Seq.toList
  Fren.Seq.nth Fren.Seq.instAppend Fren.Seq.instEmptyCollection Fren.Str.lit and_assoc


example : spec.types.UNARY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.UNARY_REJECT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.BINARY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.BINARY_REJECT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.BOOLEAN_RIGHT_CHECKED_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.LET_BODY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.SUFFIX_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.LET_VALUE_SCOPE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONDITIONAL_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.BOTH_BRANCHES_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONDITION_TYPE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_ARMS_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_EMPTY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_ALL_BODIES_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.COVERAGE_SEPARATE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.DUPLICATES_SEPARATE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_ARITY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_ARGUMENT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONSTRUCTOR_NOT_CALLABLE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.FUNCTION_NOT_VALUE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONSTRUCTOR_TYPE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARENTHESES_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONTEXT_ALIGNMENT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARAMETER_ORDER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARAMETER_SUFFIX_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.IMPLICIT_BOOLEAN_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MISSING_ANNOTATION_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.EXPLICIT_NOT_OVERWRITTEN_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.VALUE_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.WRONG_VALUE_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.DIRECT_CALLEE_EXAMPLE := by
  simp [fren_spec] <;> decide

end Spec.Language.Types
