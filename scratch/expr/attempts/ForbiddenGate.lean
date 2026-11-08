module
import scratch.expr.Prototype
open ExprPrototype

-- Expected rejection: a low-phase sugared form has no valid gate proof.
#check (Expr.roll (Layer.sugar (p := .low) rfl (Expr.roll (.lit 0))))
