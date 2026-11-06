-- keep-sorted start
import FrenTestFiles.InheritedCore
-- keep-sorted end
open Fren.Lang

-- The source helper's opt-out survives an .olean import, where its body
-- is not elaborated again in the caller's local state.
mod inherited_core_import_test
use inherited_core_test::wrapped?
pub proc imported(n: Int): (y?) {
    ensure value: y? iff wrapped?(n)
}

open Lean Elab Command in
elab "#check_imported_core" : command => do
  let some c := (← Fren.getState).comps.get? `inherited_core_import_test.imported
    | throwError "missing imported-core regression"
  if c.decidable then throwError "an imported helper lost its opt-out"
#check_imported_core
