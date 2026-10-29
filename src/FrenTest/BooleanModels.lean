-- keep-sorted start
import Fren.View
-- keep-sorted end

open Fren.Lang

mod boolean_model_test
fn bit?(Int)
fn bit_bool?(Bool)
type Token
fn bit_token?(Token)
expect observed(n: Int, values: Seq<Int>) {
    assume active: bit?(n)
    cover witness: or { first: bit?(n), second: values[0] = 0 }
}

expect observed_bool(x?, values: Seq<Int>) {
    assume active: bit_bool?(x?)
    cover witness: or { first: bit_bool?(x?), second: values[0] = 0 }
}
expect observed_token(token: Token, values: Seq<Int>) {
    assume active: bit_token?(token)
    cover witness: or { first: bit_token?(token), second: values[0] = 0 }
}
expect one_source(x?, y?, values: Seq<Int>) {
    expect result: one { first: x?, second: y?, third: values[0] = 0 }
}

expect ordinary_let(values: Seq<Int>) {
    expect result: let value := values[0] in value + value > 0
}

fn indexed?(values: Seq<Int>) := and { part: one { first: true, second: false, third: values[0] = 0 } }
expect repeated_indices(left: Seq<Int>, right: Seq<Int>) {
    expect result: indexed?(left) and indexed?(right)
}

-- The same primary model interprets the uninterpreted function and the
-- evaluation guard. The skipped second member has no defined value here.
open Lean Elab Command in
elab "#check_boolean_model" : command => do
  liftTermElabM do
    for path in #[`boolean_model_test.observed, `boolean_model_test.observed_bool, `boolean_model_test.observed_token] do
      let some comp := (← Fren.getState).globals.get? path
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
    let some oneComp := (← Fren.getState).globals.get? `boolean_model_test.one_source
      | throwError "missing one source component"
    unless oneComp.indexes.size == 1 do throwError "one source index produced multiple check sites"
    let (results, _, _) ← Fren.checkComp oneComp #[.definedness]
    unless results.size == 1 && results[0]?.any (·.verdict == Fren.Core.Verdict.fail) do
      throwError "one source index did not retain its reachable undefinedness obligation"
    let some ordinary := (← Fren.getState).globals.get? `boolean_model_test.ordinary_let
      | throwError "missing ordinary let component"
    unless ordinary.indexes.size == 2 do
      throwError "Boolean lowering aggregation merged ordinary repeated let sites"
    let some repeated := (← Fren.getState).globals.get? `boolean_model_test.repeated_indices
      | throwError "missing repeated predicate source component"
    unless repeated.indexes.size == 2 && repeated.indexes[0]!.1 != repeated.indexes[1]!.1 do
      throwError "distinct predicate applications lost their own source index identities"
    let (repeatedResults, _, _) ← Fren.checkComp repeated #[.definedness]
    unless repeatedResults.size == 2 && repeatedResults.all (·.verdict == Fren.Core.Verdict.fail) do
      throwError "distinct predicate arguments lost their own undefinedness obligations"

#check_boolean_model

-- fren-covers: lang::block_evaluation, lang::block_values, lang::exactly_one_reach, lang::named_identity
