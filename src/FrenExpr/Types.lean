module

public import FrenBase
public import FrenAst

public section
namespace FrenExpr

/-- Nominal equality is supplied by the identity type. Production instantiates
this with canonical ItemId; the primitive spec can instantiate it with Int. -/
inductive ValueType (Id : Type) where
  | bool | int | enum (owner : Id)
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

abbrev Ty := ValueType FrenBase.ItemId

variable {Id : Type}

namespace ValueType

@[expose] def compatible [BEq Id] : ValueType Id → ValueType Id → Bool
  | .bool, .bool | .int, .int => true
  | .enum a, .enum b => a == b
  | _, _ => false

theorem compatible_iff [BEq Id] [LawfulBEq Id] (a b : ValueType Id) :
    compatible a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [compatible, beq_iff_eq]

end ValueType

open FrenAst

@[expose] def unaryOperand : UnaryOp → ValueType Id
  | .neg => .int | .not => .bool

@[expose] def unary [BEq Id] (op : UnaryOp) (operand : ValueType Id) : Option (ValueType Id) :=
  if operand.compatible (unaryOperand op) then some operand else none

/-- Equality uses the left value type, including its real nominal identity.
All other binary operations require their fixed builtin operand type. -/
@[expose] def binaryOperand (op : BinaryOp) (left : ValueType Id) : ValueType Id :=
  match op with
  | .eq | .ne => left
  | .and | .or | .iff => .bool
  | _ => .int

@[expose] def binaryResult : BinaryOp → ValueType Id
  | .add | .sub | .mul | .div | .rem => .int
  | _ => .bool

@[expose] def binary [BEq Id] (op : BinaryOp) (left right : ValueType Id) : Option (ValueType Id) :=
  let expected := binaryOperand op left
  if left.compatible expected && right.compatible expected then some (binaryResult op) else none

theorem unary_accepts [BEq Id] [LawfulBEq Id] (op : UnaryOp) (t : ValueType Id) :
    (unary op t).isSome = true ↔ t = unaryOperand op := by
  simp [unary, ValueType.compatible_iff]

theorem binary_accepts [BEq Id] [LawfulBEq Id] (op : BinaryOp) (a b : ValueType Id) :
    (binary op a b).isSome = true ↔ a = binaryOperand op a ∧ b = binaryOperand op a := by
  simp [binary, ValueType.compatible_iff]

theorem binary_result [BEq Id] (op : BinaryOp) (a b t : ValueType Id)
    (h : binary op a b = some t) : t = binaryResult op := by
  simp only [binary] at h
  split at h <;> simp_all

/-- Diagnostic rendering only; never used for type identity. -/
@[expose] def Ty.display : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .enum id => String.intercalate "::" (id.components.map fun c => match c with
      | .named name => name | .generated kind i => s!"{kind}#{i}")

end FrenExpr
