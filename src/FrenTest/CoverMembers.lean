-- keep-sorted start
import Fren.Check
import Fren.Elab
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
    unless (emptyInfo.props.filter (·.kind == .expect)).all (fun p => p.branchGroups.size == 1 && p.branchGroups.all (fun group => group.members.isEmpty && group.guard?.isSome)) do
      throwError "guarded empty blocks lost activation metadata"
    let (results, _, _) ← Fren.checkComp emptyInfo
    unless results.all (·.verdict == .pass) do
      throwError "inactive empty blocks should hold"
#check_cover_members
