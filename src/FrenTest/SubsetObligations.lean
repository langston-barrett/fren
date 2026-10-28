-- keep-sorted start
import Fren.Check
import Fren.Elab
-- keep-sorted end

open Fren.Lang
mod subset_obligation_test
set_option fren.lint.constant_output "allow"

type Byte = n: Int where low: n >= 0 and high: n <= 255
proc too_large(): (r: Byte) { out r := 256 }
type Empty = n: Int where low: n > 10 and high: n < 0
type Unsafe = values: Seq<Int> where head: values[0] > 0

-- Inspect the actual checker outcomes, so expected failures remain tests
-- without making this module itself an invalid specification.
open Lean Elab Command in
elab "#check_subset_obligations" : command => do
  liftTermElabM do
    let state ← Fren.getState
    let some wrong := state.comps.get? `subset_obligation_test.too_large
      | throwError "missing subset output component"
    let (wrongResults, _, _) ← Fren.checkComp wrong #[.definedness]
    unless wrongResults.any (fun r => r.verdict == Fren.Core.Verdict.fail &&
        r.patTy? == some "@invariant:subset_obligation_test::Byte::high") do
      throwError "the failing high invariant did not retain its logical identity"
    let some (_, empty) := state.comps.toList.find? (fun (_, c) => c.subset? == some `subset_obligation_test.Empty)
      | throwError "missing empty-type inhabitation check"
    let (emptyResults, _, _) ← Fren.checkComp empty
    unless emptyResults.any (·.verdict == Fren.Core.Verdict.fail) do
      throwError "an empty subset type was accepted"
    let some (_, unsafeInfo) := state.comps.toList.find? (fun (_, c) => c.subsetInvariant? == some `subset_obligation_test.Unsafe.head)
      | throwError "missing invariant definedness check"
    let (unsafeResults, _, _) ← Fren.checkComp unsafeInfo
    unless unsafeResults.any (fun r => r.kind == .definedness && r.verdict == Fren.Core.Verdict.fail) do
      throwError "an undefined invariant was accepted"

#check_subset_obligations
