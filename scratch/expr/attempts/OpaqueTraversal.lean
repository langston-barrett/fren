module

public import Std

public section
namespace ExprPrototype

inductive Phase where
  | high | low
  deriving DecidableEq, Repr

/-- The toy sugared form exists only before lowering. -/
def HasSugar (p : Phase) : Prop := p = .high
instance (p : Phase) : Decidable (HasSugar p) := inferInstanceAs (Decidable (p = .high))

/-- Child positions bind zero or one new variable; let values are outside the binder. -/
inductive Layer (p : Phase) (R : Type) where
  | lit (value : Nat)
  | var (index : Nat)
  | letE (value body : R)
  | all (body : R)
  | array (children : Array R)
  | sugar (gate : HasSugar p) (body : R)
  deriving BEq, Repr

inductive Expr (p : Phase) where
  | roll (layer : Layer p (Expr p))
  deriving BEq, Repr

namespace Layer
/-- Visit immediate children left to right, passing the number of new binders.
This is a one-layer traversal, not a recursive whole-term walk. -/
def mapChildrenM [Monad m] (f : Nat → R → m S) : Layer p R → m (Layer p S)
  | .lit n => pure (.lit n)
  | .var i => pure (.var i)
  | .letE v b => return .letE (← f 0 v) (← f 1 b)
  | .all b => return .all (← f 1 b)
  | .array xs => return .array (← xs.mapM (f 0))
  | .sugar h b => return .sugar h (← f 0 b)

def mapChildren (f : Nat → R → S) (layer : Layer p R) : Layer p S :=
  Id.run (mapChildrenM (fun d x => pure (f d x)) layer)
end Layer

/-- Deliberately rejected: the callback hides the structural decrease. -/
def badFold (alg : Layer p A → A) : Expr p → A
  | .roll layer => alg (layer.mapChildren (fun _ child => badFold alg child))

end ExprPrototype
