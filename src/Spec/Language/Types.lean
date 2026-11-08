import Fren.Impl
import Fren.Literate
import FrenBase.Binding
import FrenExpr

open Fren.Lang

#fren_md "Types.md"

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

end Spec.Language.Types
