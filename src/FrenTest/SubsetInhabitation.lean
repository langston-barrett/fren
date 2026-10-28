import FrenCore.Check

namespace FrenTest.SubsetInhabitation
open Lean Fren.Core

-- A world supplies one uninterpreted Boolean; the value is a Boolean.
-- Queries enumerate both actual domains, and output quantification keeps
-- the world fixed while searching every value.
abbrev Formula := Bool → Bool → Bool
private def backend (base : Formula := fun _ _ => true) (outputs : Bool := true) : Backend Id Formula Bool where
  query hypotheses goal _ :=
    match ([false, true].flatMap fun world => [false, true].map (world, ·)).find? fun (world, value) =>
      base world value && hypotheses.all (fun (_, f) => f world value) && !goal world value with
    | some (_, value) => .sat #[(`value, value)]
    | none => .unsat
  falseF := fun _ _ => false
  notF f := fun world value => !f world value
  conj formulas := fun world value => formulas.all (· world value)
  existsOutputs formula := if outputs then
    fun world _ => [false, true].any fun value => base world value && formula world value
    else formula
  pin _ value := some fun _ candidate => candidate == value
  pinVariant _ _ := none
  render _ value := if value then "true" else "false"
  prime := id
  samePrimed _ := fun _ _ => true
  subst _ formula := formula

private def declaration (requirements : Array (Name × Formula)) : Comp Formula := {
  path := `Subset
  vars := #[{ name := `value, role := .output, isPub := true }]
  assumes := #[]
  reqs := requirements
  expects := #[]
  triggers := #[]
  inhabitation := true
}

private def ensure (holds : Bool) (reason : String) : IO Unit :=
  unless holds do throw (IO.userError reason)

#eval do
  let positive := declaration #[(`positive, fun _ value => value)]
  ensure ((checkRealizable backend positive).verdict == Verdict.pass)
    "a fixed interpreted membership relation has an existential witness"
  let empty := declaration #[(`positive, fun _ value => value), (`negative, fun _ value => !value)]
  let failure := checkRealizable backend empty
  ensure (failure.verdict == Verdict.fail) "empty interpreted subset must fail"
  let .conflict _ core := failure.detail | throw (IO.userError "missing empty-subset conflict")
  ensure (core.contains `positive && core.contains `negative)
    "the empty-subset core must retain both incompatible invariants"
  let varying := declaration #[(`chosen, fun world value => world && value)]
  ensure ((checkRealizable backend varying (interprets := fun _ => true)).verdict == Verdict.fail)
    "a witness in one UF interpretation cannot certify universal inhabitation"
  let constrainedBase := fun world value => world == value
  let extension := { declaration #[(`zero, fun _ value => !value)] with typesInterpreted := true }
  ensure ((checkRealizable (backend constrainedBase) extension).verdict == Verdict.fail)
    "inherited type facts can vary even when the new invariant is interpreted"
  let emptyBase := fun _ _ => false
  ensure ((checkRealizable (backend emptyBase) positive).verdict == Verdict.fail)
    "the static satisfiability query must include every base-type fact"

#eval do
  let plain := declaration #[]
  ensure plain.fixedInhabitation "a fixed declaration carrier permits the SAT shortcut"
  let inputCarrier := { declaration #[(`positive, fun _ value => value)] with
    vars := #[{ name := `value, role := .input, isPub := true }] }
  ensure (!inputCarrier.fixedInhabitation) "an input-dependent procedure cannot use existential SAT"
  ensure ((checkRealizable (backend (outputs := false)) inputCarrier).verdict == Verdict.fail)
    "one satisfying input must not certify every input of a tagged procedure"
  let definitionCarrier := { plain with defs := #[(`value, (fun _ v => v), (fun _ _ => false))] }
  ensure (!definitionCarrier.fixedInhabitation) "defined outputs require substitution, not the declaration shortcut"
  let assumptionCarrier := { plain with assumes := #[(`input, fun world _ => world)] }
  ensure (!assumptionCarrier.fixedInhabitation) "assumptions are not a fresh declaration carrier"
  let callee : Inst Formula := {
    name := `call
    comp := `callee
    bindings := fun _ _ => true
    behaviour := fun _ _ => true
    assumes := #[] }
  let callCarrier := { plain with insts := #[callee] }
  ensure (!callCarrier.fixedInhabitation) "calls must retain the universal realizability protocol"

#eval do
  let fact : Formula := fun _ value => value
  let base := { declaration #[] with
    inhabitation := false
    assumes := #[(Name.mkSimple "claim.predicate@1.invariant", fact)] }
  let site : IndexSite Formula := {
    prop := `claim
    k := 0
    place := .assume
    goal := fact
    excludeSelf := true }
  ensure ((checkDefinedness backend base site).verdict == Verdict.fail)
    "a grouping owner's expanded assumptions cannot prove its own argument obligation"
  let guaranteed := { base with assumes := #[], reqs := base.assumes }
  ensure ((checkDefinedness backend guaranteed { site with place := .prop }).verdict == Verdict.fail)
    "a grouping owner's expanded guarantees cannot prove its own argument obligation"
  let sibling := { base with assumes := base.assumes.push (`independent, fact) }
  ensure ((checkDefinedness backend sibling site).verdict == Verdict.pass)
    "an independent assumption remains available to prove membership"

end FrenTest.SubsetInhabitation
