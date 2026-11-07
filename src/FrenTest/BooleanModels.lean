-- keep-sorted start
import Fren.Impl
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

-- A domain annotation protects only its own binder. An unbounded
-- quantifier nested inside it still has no value in Fren's evaluation.
open Lean Elab Command Meta Term in
elab "#check_quantifier_model" : command => do
  liftTermElabM do
    let fin ← instantiateMVars (← elabType (← `(Fin 1)))
    for (stx, expected) in #[((← `(∀ x : Fin 1, x = x)), some true),
        ((← `(∀ x : Fin 1, ∃ y : Fin 1, y = x)), none),
        ((← `(∀ x : Fin 1, ∀ y : Fin 1, y = x)), none),
        ((← `(∀ x : Fin 1, True → ∀ y : Fin 1, y = x)), none),
        ((← `(∀ x : Fin 1, x ∈ Fren.Seq.ofList ([] : List (Fin 1)) → ∃ y : Fin 1, y = x)), some true),
        ((← `(∃ x : Fin 1, x ∈ Fren.Seq.ofList ([] : List (Fin 1)) ∧ ∀ y : Fin 1, y = x)), some false)] do
      let p ← instantiateMVars (← elabTerm stx none)
      let p := Fren.markQuantifierDomains [true] p
      let prepared ← Fren.unknownQuantifiers #[fin] p
      let prepared := (← Fren.Enumerate.readIndexes prepared (unspecified := true)).1
      let values ← Fren.decideAll #[some (prepared, prepared)]
      unless values == #[expected] do
        throwError "a bounded binder changed a nested quantifier: expected {repr expected}, got {repr values}; {prepared}"

#check_quantifier_model

-- Substitution must rebuild a compound condition's whole decision, not
-- just its inferred type. The false conjunct still decides the formula.
open Lean Elab Command Meta Term in
elab "#check_quantifier_decision" : command => do
  liftTermElabM do
    let p ← instantiateMVars (← elabTerm
      (← `(False ∧ ((if Fren.unusedQuantifier Int True ∧ True then (1 : Int) else 0) = 1))) none)
    let p ← Fren.unknownQuantifiers #[] p
    check p
    let p := (← Fren.Enumerate.readIndexes p (unspecified := true)).1
    unless (← Fren.decideAll #[some (p, p)]) == #[some false] do
      throwError "an unused binder's compound decision hid a known false conjunct"

#check_quantifier_decision

-- Solver formulas must lose confirmation's domain annotations before
-- lean-smt introduces locals and embeds Nat into Int (#847, seed 52).
-- Confirmation must retain them, including on both parts of an exists.
open Lean Elab Command Meta Term in
elab "#check_solver_quantifier_domains" : command => do
  liftTermElabM do
    for (stx, domains) in #[
        ((← `(∀ i : Nat, i < 3 → i < 1 ∨ i < 3)), [true]),
        ((← `(∃ i : Nat, i < 3 ∧ i = 0)), [true]),
        ((← `(∀ (i : Int) (j : Nat), 0 ≤ i → i < 3 → j < i → j < 3)), [true, true]),
        ((← `(∃ (i : Nat) (j : Int), i < 3 ∧ 0 ≤ j ∧ j < i)), [true, true])] do
      let p ← instantiateMVars (← elabTerm stx none)
      let marked := Fren.markQuantifierDomains domains p
      let plain ← Fren.unfoldDefined p
      unless Expr.equal (← Fren.unfoldDefined marked) plain do
        throwError "confirmation annotations changed a solver formula"
      unless (← Fren.solverAnswer marked) == Fren.Core.Answer.unsat do
        throwError "confirmation annotations changed an implementation proof"
      let retained ← Fren.unfoldDefined marked (keepLastArm := true)
      unless (retained.find? fun
          | .mdata d _ => d.contains Fren.quantifierDomainKey
          | _ => false).isSome do
        throwError "confirmation lost its quantifier domains"
    let invalid ← instantiateMVars (← elabTerm (← `(∀ i : Nat, i < 3 → i < 0)) none)
    unless (← Fren.solverAnswer (Fren.markQuantifierDomains [true] invalid)) == Fren.Core.Answer.sat do
      throwError "an invalid annotated implementation proof was accepted"
    let nat := Expr.mdata (KVMap.empty.insert Fren.quantifierDomainKey (.ofBool true)) (Lean.mkConst ``Nat)
    withLocalDeclD `introduced nat fun x => do
      let guard ← mkAppM ``LT.lt #[x, Lean.mkNatLit 3]
      let small ← mkAppM ``LT.lt #[x, Lean.mkNatLit 1]
      let goal ← mkArrow guard (mkOr small guard)
      unless (← Fren.solverAnswer goal) == Fren.Core.Answer.unsat do
        throwError "an introduced annotation changed an implementation proof"
      Fren.withSolverQuantifierDomainsErased do
        unless Expr.equal (← inferType x) (Lean.mkConst ``Nat) do
          throwError "an introduced local retained a confirmation annotation"
      unless Expr.equal (← inferType x) nat do
        throwError "solver cleanup changed the caller's context"

#check_solver_quantifier_domains
