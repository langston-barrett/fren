-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang
mod named_predicate_expansion
fn inner?(a?, b?) := and { first: a?, second: b? }
fn nested?(a?, b?) := and { child: inner?(a?, b?) }
fn transparent?(a?, b?) := inner?(a?, b?)
expect nested_case(a?, b?) {
  expect output: nested?(a?, b?)
}
expect transparent_case(a?, b?) {
  expect output: transparent?(a?, b?)
}
#guard_msgs in
fn guarded?(g?, a?, b?) := let first? := a? in when g?, one { first?, b? }
expect guarded_case(g?, a?, b?) {
  expect output: guarded?(g?, a?, b?)
}
expect primitive_case(a?, b?) {
  expect output: a? iff b?
}
open Lean Elab Command in
elab "#check_expansion" : command => do
  let state ← Fren.getState
  for (path, expected) in #[
      (`named_predicate_expansion.nested_case,
        #["output.named_predicate_expansion::nested?@1.child.named_predicate_expansion::inner?@1.first",
          "output.named_predicate_expansion::nested?@1.child.named_predicate_expansion::inner?@1.second"]),
      (`named_predicate_expansion.transparent_case,
        #["output.named_predicate_expansion::transparent?@1.named_predicate_expansion::inner?@1.first",
          "output.named_predicate_expansion::transparent?@1.named_predicate_expansion::inner?@1.second"])] do
    let some info := state.globals.find? path | throwError "missing computation {path}"
    let actual := info.props.filter (·.kind == .expect) |>.map (fun p => Fren.Core.showPath p.name)
    unless actual == expected do throwError "unexpected predicate paths: {actual}; expected {expected}"
    let some primitive := state.globals.find? `named_predicate_expansion.primitive_case
      | throwError "missing primitive computation"
    let group := (primitive.props.filter (·.kind == .expect))[0]!.branchGroups[0]!
    unless group.members.map (fun member => Fren.Core.showPath member.name) == #["output.1", "output.2"] do
      throwError "primitive member paths do not use dotted identities"
    liftTermElabM do
      let some guarded := state.globals.find? `named_predicate_expansion.guarded_case
        | throwError "missing guarded computation"
      let some group := (guarded.props.filter (·.kind == .expect))[0]!.branchGroups[0]?
        | throwError "missing guarded branch group"
      let some active := group.guard? | throwError "missing activation guard"
      let arguments := #[mkConst ``Bool.false, mkConst ``Bool.true, mkConst ``Bool.true]
      let inactive ← Meta.mkEq (mkConst ``Bool.false) (mkConst ``Bool.true)
      unless ← Meta.isDefEq (active.beta arguments) inactive do
        throwError "branch activation lost the leading guard"
#check_expansion
