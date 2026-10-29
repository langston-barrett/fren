-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang
mod boolean_contract_test
set_option fren.lint.eq_op "allow"
set_option fren.lint.dead_code "allow"
fn healthy?(x?, y?) := and { first: x?, second: y? }
#guard_msgs in
fn choose?(x?, y?): (r?) {
 assume inputs: and { first: x?, second: y? }
 ensure result: and { both: healthy?(r?, x?), copy: r? iff y? }
}
fn actual?(x?, y?): (r?) {
 assume inputs: and { first: x?, second: y? }
 out r? := x? and y?
 ensure result: healthy?(r?, x?)
}
expect use_contract(x?, y?) {
 assume inputs: x? and y?
 expect result: choose?(x?, y?)
 expect defined: actual?(x?, y?)
}
open Lean Elab Command in
elab "#check_contract_leaves" : command => do
  let some contract := (← Fren.getState).contracts.get? `boolean_contract_test.choose?
    | throwError "missing split contract"
  unless contract.pres.size == 2 && contract.posts.size == 3 do
    throwError "contract blocks or named predicate members were not split"
#check_contract_leaves
#fren_check
