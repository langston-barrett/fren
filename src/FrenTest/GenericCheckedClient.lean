-- keep-sorted start
import FrenTest.GenericChecked
-- keep-sorted end
open Fren.Lang

-- An instance that a run in an imported module has checked is not checked
-- again (`lang::instance_site`).
mod checked_again
use lib::other
use mid::One
proc c3(x: One): (det y: One) { out y := other(x) }

/-- info: fren: 2 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
