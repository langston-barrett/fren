-- keep-sorted start
import Fren.Check
import Fren.Elab.GlobalBlocks
-- keep-sorted end
open Fren.Lang
mod cover_members
#guard_msgs in
fn empty_or?(g?) := when g?, or { }
#guard_msgs in
fn empty_one?(g?) := when g?, one { }
fn both?(x?) := and { yes: x?, no: not x? }
fn either?(x?) := or { held: x?, skipped: false }
fn unique?(x?) := one { held: x?, absent: false }
fn same?(x?) := iff { held: x?, also: true }
expect joint(x?, g?) {
  assume active: g?
  cover impossible: both?(x?)
  cover guarded: when g?, both?(x?)
}
expect observations(x?) {
  assume input: x?
  cover disjunction: either?(x?)
  cover uniqueness: unique?(x?)
  cover equivalence: same?(x?)
}
expect empty(g?) {
  assume inactive: not g?
  expect disjunction: empty_or?(g?)
  expect uniqueness: empty_one?(g?)
}
private def guardedEmptyAccepted (props : Array Fren.PropInfo) (results : Array Fren.Core.CheckResult) : Bool :=
  let expects := props.filter (·.kind == .expect)
  let checked := results.filter (·.kind == .expect)
  expects.size == 2 && expects.any (·.name == `disjunction) && expects.any (·.name == `uniqueness) &&
    checked.size == 2 && checked.any (·.prop? == some `disjunction) &&
    checked.any (·.prop? == some `uniqueness) &&
    expects.all (fun p => p.branchGroups.size == 1 &&
      p.branchGroups.all (fun group => group.members.isEmpty && group.guard?.isSome)) &&
    results.all (·.verdict == .pass)

open Lean Elab Command in
elab "#check_cover_members" : command => do
  liftTermElabM do
    let state ← Fren.getState
    let joint := state.globals.get! `cover_members.joint
    unless (joint.props.filter (·.kind == .cover)).size == 2 do
      throwError "named conjunction covers were split into independent queries"
    let (results, _, _) ← Fren.checkComp joint #[.cover]
    unless results.size == 2 && results.all (·.verdict == Fren.Core.Verdict.fail) do
      throwError "an impossible conjunction acquired separate witnesses"
    let observed := state.globals.get! `cover_members.observations
    let (results, _, _) ← Fren.checkComp observed #[.cover]
    unless results.size == 3 && results.all (fun r => r.verdict == .pass &&
        r.memberValues.any (fun member => member.value? == some true && member.evaluated? == some true)) do
      throwError "a named cover lost its actual held-member observations"
    let emptyInfo := state.globals.get! `cover_members.empty
    let (results, _, _) ← Fren.checkComp emptyInfo
    unless guardedEmptyAccepted emptyInfo.props results do
      throwError "guarded empty expectations or their passing results were lost"
    -- The oracle must reject omissions in either producer, independent of order.
    for name in #[`disjunction, `uniqueness] do
      unless !guardedEmptyAccepted (emptyInfo.props.filter (·.name != name)) results &&
          !guardedEmptyAccepted emptyInfo.props (results.filter (fun r => r.kind != .expect || r.prop? != some name)) do
        throwError "guarded empty oracle accepted a missing {name}"
    let noExpects := emptyInfo.props.filter (·.kind != .expect)
    let noResults := results.filter (·.kind != .expect)
    let disjunction := emptyInfo.props.filter (fun p => p.kind == .expect && p.name == `disjunction)
    let disjunctionResult := results.filter (fun r => r.kind == .expect && r.prop? == some `disjunction)
    unless !guardedEmptyAccepted noExpects results &&
        !guardedEmptyAccepted emptyInfo.props noResults &&
        !guardedEmptyAccepted noExpects noResults &&
        !guardedEmptyAccepted (noExpects ++ disjunction ++ disjunction) results &&
        !guardedEmptyAccepted emptyInfo.props (noResults ++ disjunctionResult ++ disjunctionResult) &&
        guardedEmptyAccepted emptyInfo.props.reverse results.reverse do
      throwError "guarded empty oracle accepted omissions or depends on order"
#check_cover_members

-- fren-covers: lang::clause_partition, lang::distributed_guard

/--
warning: cover goal `guarded` has a trigger

help: write the scenario as a conjunction, such as `c? and d?` for `when c?, d?`
note: `trivial_cover` is `warn` by default
help: to allow it, `set_option fren.lint.trivial_cover "allow"`
-/
#guard_msgs in
run_cmd Fren.reportLints
