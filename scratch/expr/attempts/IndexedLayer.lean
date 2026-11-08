module
import Std

namespace ExprPrototype.IndexedLayer
inductive Layer (R : Nat → Type) (n : Nat) where
  | lit : Nat → Layer R n
  | var : Fin n → Layer R n
  | bind : R (n + 1) → Layer R n
  | children : Array (R n) → Layer R n

inductive Expr : Nat → Type where
  | roll : Layer Expr n → Expr n
end ExprPrototype.IndexedLayer
