-- keep-sorted start
import Fren.Check
import Fren.Elab
-- keep-sorted end

open Fren.Lang
mod subset_obligation_test
set_option fren.lint.constant_output "allow"

type Truth = b?: Bool where invariant: b?
type Byte = n: Int where low: n >= 0 and high: n <= 255
proc too_large(): (r: Byte) { out r := 256 }
type Empty = n: Int where low: n > 10 and high: n < 0
type Unsafe = values: Seq<Int> where head: values[0] > 0
type PositiveHead = values: Seq<Int> where nonempty: values.len > 0 and head: values[0] > 0
#guard_msgs in
pub struct TruthField { valid?: Truth }
proc abstract_output(): (r: Byte) {}
proc concrete_output(): (r: Int) {}
refine output_membership: concrete_output refines abstract_output
fn gate?(Int)
type FreeBase = n: Int where branch: if gate?(0) then n = 0 else n = 1
type Derived = n: FreeBase where zero: n = 0
type Partial = n: Int where selected: n = table { false => 0 } and fixed: n = 1

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
    let some refinement := state.refinements.get? `subset_obligation_test.output_membership
      | throwError "missing refinement component: {state.refinements.toList.map (·.1)}"
    let (refinementResults, _, _) ← Fren.checkComp refinement #[.definedness]
    unless refinementResults.any (fun r => r.verdict == Fren.Core.Verdict.fail &&
        r.patTy? == some "@invariant:subset_obligation_test::Byte::high") do
      throwError "refinement output obligations lost their invariant identity"
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
    let some (_, sequence) := state.comps.toList.find? (fun (_, c) => c.subset? == some `subset_obligation_test.PositiveHead)
      | throwError "missing fixed-interpretation sequence inhabitation check"
    let (sequenceResults, _, _) ← Fren.checkComp sequence
    unless sequenceResults.any (·.verdict == Fren.Core.Verdict.pass) do
      throwError "a fixed-interpretation sequence witness was not accepted"
    for path in #[`subset_obligation_test.Derived, `subset_obligation_test.Partial] do
      let some (_, dependent) := state.comps.toList.find? (fun (_, c) => c.subset? == some path)
        | throwError "missing interpretation-dependent inhabitation check"
      let (results, _, _) ← Fren.checkComp dependent
      unless results.any (·.verdict == Fren.Core.Verdict.fail) do
        throwError "a witness from one favorable interpretation was accepted as universal inhabitation"

#check_subset_obligations
