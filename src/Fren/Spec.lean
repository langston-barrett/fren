-- keep-sorted start
import Fren.Claims
import Fren.Elab
import Fren.Prelude
-- keep-sorted end

/-!
# Specs without the checker

Everything needed to write specs and use the Lean definitions generated for
them, without lean-smt: implementation code can import spec types from files
that import only this. Checking (`#fren_check`) and `impl` need `Fren`.
-/
