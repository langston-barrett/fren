-- keep-sorted start
import FrenTest.GenericMid
-- keep-sorted end
open Fren.Lang

-- An instance that an imported module applies, but that no run of checks
-- has checked, since that module has none: checked here, with the first
-- item that this run checks and that uses it (`lang::instance_site`).
mod unchecked_client
use lib::other
use mid::One
proc c(x: One, n: Int): (det y: One) {
    out y := other(x)
    expect anything: n = 42
}

/--
error: the postconditions of `lib::other<mid::One>` cannot all hold

note: for the arguments
          x = One::A
      no value of `lib::other<mid::One>` satisfies `diff`
note: an uninterpreted function's postconditions are assumed wherever it is applied, so if they cannot hold, every check that applies it would pass
help: weaken one of them, or add a precondition that rules these arguments out
---
info: is false for this input
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
