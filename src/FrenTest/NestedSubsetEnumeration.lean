-- keep-sorted start
import Fren.Enumerate
-- keep-sorted end
open Fren.Lang
mod nested_subset_enumeration
type Truth = value?: Bool where invariant: value?
struct Flag { on?: Truth }
struct Wrapped(Truth)
enum Payload { Value(Truth) }
fn choose?(Bool)
fn refined?(Bool): Truth
set_option fren.evidence "enumerated" in
proc constrained_result(x?) { expect holds: refined?(x?) }
type Selected = value?: Bool where invariant: value? iff choose?(false)
type Positive = value: Int where invariant: value > 0
set_option fren.evidence "enumerated" in
type Maybe = value?: Bool where invariant: choose?(value?)
set_option fren.evidence "enumerated" in
proc records(a: Flag, b: Flag) { expect same: a = b }
set_option fren.evidence "enumerated" in
proc wrappers(a: Wrapped, b: Wrapped) { expect same: a = b }
set_option fren.evidence "enumerated" in
proc payloads(a: Payload, b: Payload) { expect same: a = b }
set_option fren.evidence "enumerated" in
proc shared(a?: Selected, b?: Selected) { expect same: a? = b? }
set_option fren.evidence "enumerated" in
proc numeric(x: Positive) {
  expect positive: x > 0
  expect stricter: x > 1
}
set_option fren.evidence "enumerated" in
proc bad_output(): (r?: Truth) { ensure opposite: not r? }
set_option fren.evidence "enumerated" in
set_option fren.lint.constant_output "allow" in
proc bad_definition(): (r: Positive) { out r := 0 }
open Lean Elab Command in
elab "#check_nested_enumeration" : command => do
  liftTermElabM do
    let state ← Fren.getState
    for path in #[`nested_subset_enumeration.records, `nested_subset_enumeration.wrappers,
        `nested_subset_enumeration.payloads, `nested_subset_enumeration.shared] do
      let some comp := state.comps.get? path | throwError "missing enumeration component {path}"
      let (_, _, checked) ← Fren.checkComp comp #[.expect] (some Fren.Enumerate.enumerate)
      let some checked := checked | throwError "enumeration was not requested for {path}"
      let checked ← match checked with
        | .ok checked => pure checked
        | .error why => throwError "enumeration unsupported for {path}: {why.text}"
      let results := checked.results
      unless results.size == 1 && results.all (·.verdict == Fren.Core.Verdict.pass) do
        throwError "nested membership was not enforced for {path}"
    let some (_, maybeType) := state.comps.toList.find? (fun (_, c) => c.subset? == some `nested_subset_enumeration.Maybe)
      | throwError "missing interpreted inhabitation component"
    let (_, _, checked) ← Fren.checkComp maybeType #[.realizable] (some Fren.Enumerate.enumerate)
    let some (.ok checked) := checked | throwError "interpreted inhabitation was not enumerated"
    let maybeResults := checked.results
    unless maybeResults.size == 1 && maybeResults.all (·.verdict == .fail) do
      throwError "one favorable interpretation certified universal inhabitation"
    let some numeric := state.comps.get? `nested_subset_enumeration.numeric | throwError "missing numeric component"
    let (_, _, checked) ← Fren.checkComp numeric #[.expect] (some Fren.Enumerate.enumerate)
    let some (.ok checked) := checked | throwError "numeric membership was not enumerated"
    let results := checked.results
    unless results.any (fun r => r.prop? == some `positive && r.verdict != .fail) &&
        results.any (fun r => r.prop? == some `stricter && r.verdict == .fail) do
      throwError "numeric invariant admitted an invalid counterexample or hid a valid one"
    let some bad := state.comps.get? `nested_subset_enumeration.bad_output | throwError "missing output component"
    let (_, _, checked) ← Fren.checkComp bad #[.realizable] (some Fren.Enumerate.enumerate)
    let some (.ok checked) := checked | throwError "output membership was not enumerated"
    let results := checked.results
    unless results.size == 1 && results.all (·.verdict == .fail) do
      throwError "an invalid output witnessed realizability"
    let some constrained := state.comps.get? `nested_subset_enumeration.constrained_result | throwError "missing constrained function component"
    let (_, _, result) ← Fren.checkComp constrained #[.expect] (some Fren.Enumerate.enumerate)
    let some (.error why) := result | throwError "a constrained UF result table was silently enumerated without its invariant"
    unless why.code? == some "F0645" do throwError "unsupported result constraint was not reported honestly"
    let some defined := state.comps.get? `nested_subset_enumeration.bad_definition | throwError "missing defined output component"
    let (definedResults, _, _) ← Fren.checkComp defined #[.definedness] (some Fren.Enumerate.enumerate)
    unless definedResults.any (fun r => r.verdict == .fail && r.patTy? == some "@invariant:nested_subset_enumeration::Positive::invariant") do
      throwError "a defined output assumed its own invariant before the giving-site check"
#check_nested_enumeration

-- fren-covers: lang::subset_inheritance, lang::subset_membership, lang::subset_obligations
