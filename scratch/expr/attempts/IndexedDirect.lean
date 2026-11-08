module
import Std

namespace ExprPrototype.IndexedDirect
inductive Expr : Nat → Type where
  | lit : Nat → Expr n
  | var : Fin n → Expr n
  | letE : Expr n → Expr (n + 1) → Expr n
  | all : Expr (n + 1) → Expr n
  | children : Array (Expr n) → Expr n
end ExprPrototype.IndexedDirect
