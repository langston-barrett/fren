-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- With `fren.runChecks` off, `#fren_check` checks nothing and reports
-- nothing, not even a failing check, as `lake build` elaborates Fren's own
-- requirements (`Reqs/Lean#options`); a path it names must still resolve.
mod run_checks_test

pub proc wrong(x: Int): (y: Int) {
    ensure r: y = x
    ensure s: y = x + 1
}

set_option fren.runChecks false in
#guard_msgs in #fren_check

set_option fren.runChecks false in
#guard_msgs in #fren_check wrong

/-- error: cannot find `missing` in this scope -/
#guard_msgs in
set_option fren.runChecks false in
#fren_check missing

-- On by default: the same check fails.
/--
error: `run_checks_test::wrong` is not realizable

note: for the input
          x = 0
      no outputs satisfy `r` and `s`
help: weaken one of them, or add an `assume` that rules this input out
---
info: fren: 0 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in #fren_check wrong
