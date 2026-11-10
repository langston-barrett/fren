module

public import FrenModule.Resolved
public import FrenExpr

public section
namespace FrenModule

structure TypedParameter where
  written : FrenAst.Parameter
  type : FrenExpr.Ty
  deriving Repr, BEq, ReflBEq, LawfulBEq

structure Signature where
  id : FrenBase.ItemId
  parameters : Array TypedParameter
  result : FrenExpr.Ty
  resultAnnotation : FrenAst.Ty
  deriving Repr, BEq, ReflBEq, LawfulBEq

abbrev TypeContext := FrenBase.Binding.Context (FrenAst.Token × FrenExpr.Ty)

inductive ExpressionType where
  | value (type : FrenExpr.Ty)
  | callable (signature : Signature)
  deriving Repr, BEq

/-- Postorder occurrence information over the retained syntax. A callee's
parentheses are retained too, but callables are never first-class values.
Contexts retain binder tokens as well as types, distinguishing siblings. -/
structure TypedOccurrence where
  expression : FrenAst.Expr
  context : TypeContext
  type : ExpressionType
  deriving Repr, BEq

structure TypedBody where
  owner : FrenBase.ItemId
  member : Option FrenAst.Member
  expression : FrenAst.Expr
  context : TypeContext
  type : FrenExpr.Ty
  occurrences : Array TypedOccurrence
  deriving Repr, BEq

/-- Retained resolved syntax is the erasure. Coverage and non-recursion are
separate obligations, not Boolean fields a caller may mark as validated. -/
structure Typed where
  resolved : Resolved
  signatures : Array Signature
  bodies : Array TypedBody
  deriving Repr, BEq

end FrenModule
