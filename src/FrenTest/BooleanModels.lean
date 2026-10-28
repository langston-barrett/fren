-- keep-sorted start
import Fren.View
-- keep-sorted end

open Fren.Lang

mod boolean_model_test
fn bit?(Int)
expect observed(n: Int, values: Seq<Int>) {
    assume active: bit?(n)
    cover witness: or { first: bit?(n), second: values[0] = 0 }
}

-- The same primary model interprets the uninterpreted function and the
-- evaluation guard. The skipped second member has no defined value here.
open Lean Elab Command in
elab "#check_boolean_model" : command => do
  liftTermElabM do
    let some comp := (← Fren.getState).globals.get? `boolean_model_test.observed
      | throwError "missing observation component"
    let (results, _, _) ← Fren.checkComp comp #[.cover]
    let some result := results[0]? | throwError "missing cover result"
    unless result.verdict == Fren.Core.Verdict.pass do throwError "cover did not pass"
    let some first := result.memberValues[0]? | throwError "missing first member observation"
    let some second := result.memberValues[1]? | throwError "missing skipped member observation"
    unless first.evaluated? == some true && first.value? == some true do
      throwError "the function's primary-model value was not preserved"
    unless second.evaluated? == some false && second.value?.isNone do
      throwError "a short-circuited member was evaluated"

#check_boolean_model
