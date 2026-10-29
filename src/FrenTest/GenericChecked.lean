-- keep-sorted start
import FrenTest.GenericMid
-- keep-sorted end
open Fren.Lang

-- A run that checks only some items: the instance that an unchecked item,
-- `c1`, uses first is checked with the first item that the run checks and
-- that uses it, `c2`, and by no later run (`lang::instance_site`).
mod checked_client
use lib::other
use mid::One
proc c1(x: One): (det y: One) { out y := other(x) }
proc c2(x: One, n: Int): (det y: One) {
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
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check c2

-- Already checked: `c1`'s run does not check it again.
/-- info: fren: 2 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check c1
