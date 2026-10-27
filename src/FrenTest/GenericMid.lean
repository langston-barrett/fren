-- keep-sorted start
import FrenTest.GenericLib
-- keep-sorted end
open Fren.Lang

-- A module that applies an imported generic function without a body at an
-- instance of its own, and that no `#fren_check` checks: its instance's
-- contract is checked by the first run that checks an item that uses it
-- (`lang::instance_site`), in `GenericUnchecked`.
mod mid
use lib::other
pub enum One { A }
comp mid { in x: One pub det out y: One := other(x) }
