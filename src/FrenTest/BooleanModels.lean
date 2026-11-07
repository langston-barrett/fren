-- keep-sorted start
import Fren.Elab.GlobalBlocks
import Fren.Impl
import Fren.View
import Reqs.Models
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
        ((← `(∃ x : Fin 1, x ∈ Fren.Seq.ofList ([] : List (Fin 1)) ∧ ∀ y : Fin 1, y = x)), some false),
        ((← `(∃ x : Fin 1, x ∈ Fren.Seq.ofList ([0] : List (Fin 1)) ∧ ∀ y : Fin 1, y = x)), none),
        ((← `(∃ x : Fin 1, x ∈ Fren.Seq.ofList ([0] : List (Fin 1)) ∧ (False ∧ ∀ y : Fin 1, y = x))), some false),
        ((← `(∀ x : Fin 1, x ∈ Fren.Seq.ofList ([0] : List (Fin 1)) → (True ∨ ∀ y : Fin 1, y = x))), some true)] do
      let p ← instantiateMVars (← elabTerm stx none)
      let p := Fren.markQuantifierDomains [true] p
      let prepared ← Fren.unknownQuantifiers #[fin] p
      let prepared := (← Fren.Enumerate.readIndexes prepared (unspecified := true)).1
      let values ← Fren.decideAll #[some (prepared, prepared)]
      unless values == #[expected] do
        throwError "a bounded binder changed a nested quantifier: expected {repr expected}, got {repr values}; {prepared}"
      -- Compose the actual prepared/index-rewritten quantifier with the
      -- complete-match marker. Its body being a literal must neither
      -- lose a known empty-domain result nor make an unknown one known.
      let decideOf (q : Expr) : MetaM Expr :=
        return mkApp2 (mkConst ``Decidable.decide) q (← Fren.Enumerate.decidableOf q)
      let decision ← decideOf prepared
      for body in #[false, true] do
        for scrutinee in #[decision, prepared] do
          let wrapped ← mkAppM ``Fren.lastArm #[scrutinee, mkConst (if body then ``True else ``False)]
          unless (← Fren.decideAll #[some (wrapped, wrapped)]) == #[expected.map (fun _ => body)] do
            throwError "lastArm lost its partially evaluated scrutinee or was not strict"
          for typeArgument in #[fin, ← mkArrow fin fin] do
            let genericApplication ← mkAppM ``Fren.lastArm #[typeArgument, wrapped]
            unless (← Fren.decideAll #[some (genericApplication, genericApplication)]) == #[expected.map (fun _ => body)] do
              throwError "a strict type argument discarded its quantified body's value"
      let finalArm ← mkAppM ``Fren.lastArm #[decision, mkConst ``False]
      let complete ← mkAppOptM ``ite #[some (mkSort 0), some prepared, some (← Fren.Enumerate.decidableOf prepared),
        some (mkConst ``True), some finalArm]
      unless (← Fren.decideAll #[some (complete, complete)]) == #[expected] do
        throwError "a complete Boolean match changed its quantified scrutinee"
      let finalValue ← mkAppM ``Fren.lastArm #[prepared, mkConst ``Bool.false]
      let completeValue ← mkAppOptM ``ite #[some (mkConst ``Bool), some prepared,
        some (← Fren.Enumerate.decidableOf prepared), some (mkConst ``Bool.true), some finalValue]
      let completeValue ← mkEq completeValue (mkConst ``Bool.true)
      unless (← Fren.decideAll #[some (completeValue, completeValue)]) == #[expected] do
        throwError "a value-valued Boolean match changed its quantified scrutinee"
      for scrutinee in #[decision, prepared] do
        let wrapped ← mkAppM ``Fren.lastArm #[scrutinee, mkNatLit 7]
        let equal ← mkEq wrapped (mkNatLit 7)
        let actual ← Fren.decideAll #[some (equal, equal)]
        unless actual == #[expected.map (fun _ => true)] do
          throwError "a value-valued lastArm changed its quantified scrutinee: {repr actual}; {prepared}"

#check_quantifier_model

-- Compare the whole prepared composition with the executable reference,
-- whose quantifier expansion contains body expressions, not supplied truths.
open Lean Elab Command Meta Term Fren.Generated in
elab "#check_quantified_counts" : command => do
  liftTermElabM do
    let fin ← instantiateMVars (← elabType (← `(Fin 1)))
    let referenceInterp : lang.Interp := ⟨.Empty, .Empty, .Empty⟩
    let singleton ← instantiateMVars (← elabTerm (← `(Fren.Seq.ofList ([0] : List (Fin 1)))) none)
    let lit (k : Int) : lang.Expr String := .Literal (.Integer k)
    let referenceTruth (e : lang.Expr String) : Option Bool :=
      match model.known_eval referenceInterp .Empty e with
      | .Defined .True => some true
      | .Defined .False => some false
      | _ => none
    for (stx, reference, unknown) in #[
        ((← `(∀ x : Fin 1, ∀ y : Fin 1, y = x)),
          model.quantified_expr true true (.Cons (model.quantified_expr true false .Nil) (.Nil : lang.Expr String)), true),
        ((← `(∃ x : Fin 1, x ∈ Fren.Seq.ofList ([] : List (Fin 1)) ∧ ∀ y : Fin 1, y = x)),
          model.quantified_expr false true .Nil, false),
        ((← `(∀ x : Fin 1, x ∈ Fren.Seq.ofList ([] : List (Fin 1)) → ∃ y : Fin 1, y = x)),
          model.quantified_expr true true .Nil, false)] do
      let p ← instantiateMVars (← elabTerm stx none)
      let p ← Fren.unknownQuantifiers #[fin] (Fren.markQuantifierDomains [true] p)
      let p := (← Fren.Enumerate.readIndexes p (unspecified := true)).1
      for ty in #[Lean.mkConst ``Int, Lean.mkConst ``Nat] do
        for k in [0:3] do
          let numeral (n : Nat) := mkNumeral ty n
          let indicator ← mkAppOptM ``ite #[some ty, some p, some (← Fren.Enumerate.decidableOf p),
            some (← numeral 1), some (← numeral 0)]
          let sum ← mkAppM ``HAdd.hAdd #[indicator, ← numeral k]
          let refSum : lang.Expr String := .Binary .Add (.If reference (lit 1) (lit 0)) (lit k)
          let domain : Fren.Enumerate.PartialEnv :=
            { values := fun _ => pure (#[], false), base := `Fren._count_test
              known? := some (Fren.Enumerate.knownOf fun q => do
                return mkApp2 (mkConst ``Decidable.decide) q (← Fren.Enumerate.decidableOf q)) }
          if unknown then
            let value ← Fren.Enumerate.partialValue domain sum
            let known ← mkAppM ``Option.isSome #[value]
            unless (← Fren.compileValues Bool (mkConst ``Bool) #[known]) == #[false] do
              throwError "the numeric sum of an unknown condition became known"
          for shape in [0:4] do
            let one ← numeral 1
            let (count, refCount) ← match shape with
              | 0 => pure (← mkEq sum one, lang.Expr.Binary .Eq refSum (lit 1))
              | 1 => pure (← mkEq one sum, lang.Expr.Binary .Eq (lit 1) refSum)
              | 2 => pure (← mkAppM ``LE.le #[sum, one], lang.Expr.Binary .Le refSum (lit 1))
              | _ => pure (← mkAppM ``GE.ge #[one, sum], lang.Expr.Binary .Le refSum (lit 1))
            let negated := mkApp (mkConst ``Not) count
            let last ← mkAppM ``Fren.lastArm #[count, mkConst ``True]
            let value ← mkAppOptM ``ite #[some (mkConst ``Bool), some count,
              some (← Fren.Enumerate.decidableOf count), some (mkConst ``Bool.true), some (mkConst ``Bool.false)]
            let value ← mkEq value (mkConst ``Bool.true)
            let unknownIndex ← instantiateMVars (← elabTerm
              (← `(Fren.Seq.nth (Fren.Seq.ofList ([] : List Int)) 0 = 0)) none)
            let unknownIndex := (← Fren.Enumerate.readIndexes unknownIndex (unspecified := true)).1
            let outer (universal : Bool) := withLocalDeclD `i fin fun x => do
              let member ← mkAppM ``Membership.mem #[singleton, x]
              if universal then mkForallFVars #[x] (← mkArrow member count)
              else mkAppM ``Exists #[← mkLambdaFVars #[x] (mkAnd member count)]
            let ps := #[count, negated, last, value, mkAnd count unknownIndex, mkOr count (mkConst ``True),
              ← outer true, ← outer false]
            for q in ps do check q
            let actual ← Fren.decideAll (ps.map fun q => some (q, q))
            let refTrue : lang.Expr String := .Literal .True
            let refFalse : lang.Expr String := .Literal .False
            let refs := #[refCount, .Unary .Not refCount,
              .Apply "strict" (.Cons refCount .Nil) (.Cons "unused" .Nil) refTrue,
              .Binary .Eq (.If refCount refTrue refFalse) refTrue,
              .And refCount (.Index .Nil (lit 0)), .Or refCount refTrue,
              model.quantified_expr true true (.Cons refCount .Nil),
              model.quantified_expr false true (.Cons refCount .Nil)]
            let wanted := refs.map referenceTruth
            unless actual == wanted do
              throwError "quantified count composition disagrees with known_eval (shape {shape}, k {k}): {repr actual} versus {repr wanted}"

#check_quantified_counts

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

-- Expansion changes the condition as well as its decision. Count the
-- logical quantifier once, even if the decision repeats its annotation.
open Lean Elab Command Meta Term in
elab "#check_expanded_quantifier_decision" : command => do
  liftTermElabM do
    let seq ← instantiateMVars (← elabType (← `(Fren.Seq Int)))
    withLocalDeclD `q seq fun q => do
      for all in #[false, true] do
        let p ← withLocalDeclD `y (mkConst ``Int) fun y => do
          let member ← mkAppM ``Membership.mem #[q, y]
          if all then mkForallFVars #[y] (← mkArrow member (mkConst ``True))
          else mkAppM ``Exists #[← mkLambdaFVars #[y] (mkAnd member (mkConst ``True))]
        for repeated in #[false, true] do
          let marked := Fren.Elems.mark 1 p
          let decision := mkApp (mkConst ``Classical.propDecidable) (if repeated then marked else p)
          let e ← mkAppOptM ``ite #[some (mkConst ``Bool), some marked, some decision,
            some (mkConst ``Bool.true), some (mkConst ``Bool.false)]
          let scan ← IO.mkRef ({} : Fren.Elems.Scan)
          let e ← Fren.Elems.scan (.ofList [q.fvarId!]) scan #[] e
          let sites := (← scan.get).sites
          unless sites.size == 1 do throwError "a decision duplicated its source quantifier"
          let count ← IO.mkRef 0
          let expanded ← Fren.Elems.expand sites (fun _ _ _ => pure []) count e
          check expanded
          unless !expanded.hasFVar && (← count.get) == 0 do
            throwError "empty expansion kept an old decision or consumed the instance budget"
          unless (← Fren.compileValues Bool (mkConst ``Bool) #[expanded]) == #[all] do
            throwError "an empty-domain condition changed its Boolean value"
          let count ← IO.mkRef 0
          let overflow ← try
            discard <| Fren.Elems.expand sites
              (fun _ _ _ => pure (List.replicate (Fren.Core.maxElementInstances + 1) (mkIntLit 0))) count e
            pure false
          catch ex => pure ((← ex.toMessageData.toString).startsWith Fren.Elems.tooManyTag)
          unless overflow do throwError "quantifier expansion lost its instance limit"

#check_expanded_quantifier_decision

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

-- Use the actual source component and its applied/unfolded pair, not
-- only a hand-built count. A generic Bool application is noncomputable
-- until its strict body is unfolded for partial quantified evaluation.
set_option fren.lint.undecidable "allow" in
fn count_source_all?<T>(x: T) := forall (y: T), y = x
set_option fren.lint.unused_variables "allow" in
fn count_source_accept?<T>(x: T) := true
proc quantified_count_source(q: Seq<Int>, a: Int) {
    require pinned: a = 1 or (((if count_source_all?(true) then 1 else 0) + 2 <= 1) and q[5] = 0)
    expect e: a = 3
}
proc quantified_count_strict_source(q: Seq<Int>, a: Int) {
    require pinned: a = 1 or ((not count_source_accept?((if count_source_all?(true) then 1 else 0) + 2 = 1)) and q[5] = 0)
    expect e: a = 3
}

open Lean Elab Command Meta in
elab "#check_quantified_count_source" : command => do
  liftTermElabM do
    for path in #[`boolean_model_test.quantified_count_source, `boolean_model_test.quantified_count_strict_source] do
      let some c := (← Fren.getState).comps.get? path
        | throwError "missing quantified count source component"
      Fren.withNatUses c.uses fun uses _ => do
        let rep (e : Expr) := Lean.Core.betaReduce (Fren.replaceUses c.uses uses e)
        let types ← c.vars.mapM fun v => rep v.type
        withLocalDeclsD ((c.vars.zip types).map fun (v, t) => (v.name, fun _ => pure t)) fun fvs => do
          let int := mkConst ``Int
          let empty ← mkAppM ``Fren.Seq.ofList #[← mkListLit int []]
          let values := (fvs.zip types).map fun (x, t) => (x, some (if t.isConstOf ``Int then mkIntLit 2 else empty))
          let some pinned := c.assumes.find? (·.name.getString! == "pinned")
            | throwError "missing pinned hypothesis"
          let formula := (← rep pinned.body).beta fvs
          let prepared ← Fren.atModel values formula
          unless (← Fren.decideAll #[prepared]) == #[some false] do
            throwError "the actual source's applied expression discarded a known count contradiction"

#check_quantified_count_source
