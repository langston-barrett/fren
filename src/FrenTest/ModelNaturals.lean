-- keep-sorted start
import Fren.Check
-- keep-sorted end

-- SMT represents Nat as Int. A negative reconstruction must retain its
-- type mismatch, so it cannot silently become a valid zero observation.
open Lean Meta in
run_meta do
  let nat := mkConst ``Nat
  for i in #[(0 : Int), 3] do
    let value ← Fren.modelValue nat (toExpr i)
    unless value == mkNatLit i.toNat do
      throwError "a nonnegative Nat model value was not restored"
  let negative := toExpr (-1 : Int)
  let value ← Fren.modelValue nat negative
  unless value == negative && (← inferType value).isConstOf ``Int do
    throwError "a negative Nat model value lost its type mismatch"
  -- Function results use the same reconstruction path as scalar values.
  let ty ← mkArrow nat nat
  let function := mkLambda `n BinderInfo.default nat negative
  let restored ← Fren.modelValue ty function
  let result ← whnf (mkApp restored (mkNatLit 0))
  unless result == negative && (← inferType result).isConstOf ``Int do
    throwError "a negative Nat model function result lost its type mismatch"
