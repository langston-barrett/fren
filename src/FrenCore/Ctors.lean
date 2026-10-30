-- keep-sorted start
import Lean.Elab.Term
-- keep-sorted end

/-!
# Every constructor of an enumeration

`ctors% T` is the array of the constructors of the inductive type `T`,
each without arguments, in the order that `T` declares them, so that a
list of every value of `T` needs no entry for each (`Lint.all`).
-/

namespace Fren.Core

open Lean Elab Term

elab "ctors% " t:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo t
  let .inductInfo i ← getConstInfo n | throwError "`{n}` is not an inductive type"
  unless i.numParams == 0 && i.numIndices == 0 do throwError "`{n}` has parameters or indices"
  let ctors ← i.ctors.mapM fun c => do
    let .ctorInfo ci ← getConstInfo c | throwError "`{c}` is not a constructor"
    unless ci.numFields == 0 do throwError "the constructor `{c}` has fields"
    pure (Lean.mkConst c)
  Meta.mkArrayLit (Lean.mkConst n) ctors

end Fren.Core
