-- keep-sorted start
import FrenTest.GenericLib
-- keep-sorted end
open Fren.Lang

-- An instance of an imported generic function without a body that the
-- library does not apply: its contract is checked with the component that
-- first applies it, and reported there, as the `fren` command reports it
-- (`lang::instance_site`).
mod client
use lib::other
pub enum One { A }
comp c {
    in x: One
    in n: Int
    pub det out y: One := other(x)
    expect anything: n = 42
}
/--
error: the postconditions of `lib::other<client::One>` cannot all hold

note: for the arguments
          x = One::A
      no value of `lib::other<client::One>` satisfies `diff`
note: an uninterpreted function's postconditions are assumed wherever it is applied, so if they cannot hold, every check that applies it would pass
help: weaken one of them, or add a precondition that rules these arguments out
---
info: is false for this input
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
