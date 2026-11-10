module

public import FrenModule.Typed

public section
namespace FrenEval

inductive Value where
  | bool (value : Bool)
  | int (value : Int)
  | enum (owner constructor : FrenBase.ItemId)
  deriving Repr, BEq, DecidableEq

def Value.type : Value → FrenExpr.Ty
  | .bool _ => .bool
  | .int _ => .int
  | .enum owner _ => .enum owner

/-- External enum data must name an actual constructor of this exact owner.
Matching the type tag alone would admit invented constructors. -/
def Value.valid (t : FrenModule.Typed) : Value → Bool
  | .bool _ | .int _ => true
  | .enum owner ctor =>
    t.resolved.scope.items.any (fun i => i.id == owner && i.kind == .enumeration) &&
    t.resolved.scope.items.any (fun i => i.id == ctor && i.kind == .constructor) &&
    ctor.parent == some owner

inductive PrimitiveFailure where
  | undefined
  | operands
  deriving Repr, BEq, DecidableEq

abbrev PrimitiveResult := Except PrimitiveFailure Value

def unary : FrenAst.UnaryOp → Value → PrimitiveResult
  | .neg, .int n => .ok (.int (-n))
  | .not, .bool b => .ok (.bool (!b))
  | _, _ => .error .operands

/-- Strict primitive decisions. Division uses Lean's mathematical Euclidean
Int division, guarded before its totalized zero-divisor definition is reached. -/
@[expose] def binary (op : FrenAst.BinaryOp) (left right : Value) : PrimitiveResult :=
  match op, left, right with
  | .add, .int a, .int b => .ok (.int (a + b))
  | .sub, .int a, .int b => .ok (.int (a - b))
  | .mul, .int a, .int b => .ok (.int (a * b))
  | .div, .int a, .int b => if b == 0 then .error .undefined else .ok (.int (a / b))
  | .rem, .int a, .int b => if b == 0 then .error .undefined else .ok (.int (a % b))
  | .lt, .int a, .int b => .ok (.bool (a < b))
  | .le, .int a, .int b => .ok (.bool (a ≤ b))
  | .gt, .int a, .int b => .ok (.bool (a > b))
  | .ge, .int a, .int b => .ok (.bool (a ≥ b))
  | .and, .bool a, .bool b => .ok (.bool (a && b))
  | .or, .bool a, .bool b => .ok (.bool (a || b))
  | .iff, .bool a, .bool b => .ok (.bool (a == b))
  | .eq, a, b => if a.type == b.type then .ok (.bool (a == b)) else .error .operands
  | .ne, a, b => if a.type == b.type then .ok (.bool (a != b)) else .error .operands
  | _, _, _ => .error .operands

theorem binary_add (a b : Int) : binary .add (.int a) (.int b) = .ok (.int (a + b)) := rfl
theorem binary_sub (a b : Int) : binary .sub (.int a) (.int b) = .ok (.int (a - b)) := rfl
theorem binary_mul (a b : Int) : binary .mul (.int a) (.int b) = .ok (.int (a * b)) := rfl

theorem binary_div (a b : Int) (h : b ≠ 0) :
    binary .div (.int a) (.int b) = .ok (.int (a / b)) := by simp [binary, h]
theorem binary_mod (a b : Int) (h : b ≠ 0) :
    binary .rem (.int a) (.int b) = .ok (.int (a % b)) := by simp [binary, h]
theorem div_zero (a : Int) : binary .div (.int a) (.int 0) = .error .undefined := rfl
theorem mod_zero (a : Int) : binary .rem (.int a) (.int 0) = .error .undefined := rfl

/-- A contract about the actual primitive results, including negative divisors. -/
theorem euclidean (a b : Int) (h : b ≠ 0) :
    binary .div (.int a) (.int b) = .ok (.int (a / b)) ∧
    binary .rem (.int a) (.int b) = .ok (.int (a % b)) ∧
    a = (a / b) * b + a % b ∧ 0 ≤ a % b ∧ a % b < b.natAbs := by
  exact ⟨binary_div a b h, binary_mod a b h, (Int.ediv_mul_add_emod a b).symm,
    Int.emod_nonneg a h, Int.emod_lt a h⟩

end FrenEval
