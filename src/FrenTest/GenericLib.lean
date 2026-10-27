-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A library's generic function without a body, whose contract fails at its
-- type parameter's sort: checked here at the instance that this module
-- applies, `Int`, where it holds (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
-- `GenericClient` applies it at another instance.
mod lib
pub fn other<T>(x: T): T
    ensure diff: other(x) != x
proc use_int(x: Int): (det y: Int) { out y := other(x) expect moved: y != x }

/-- info: fren: 4 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
