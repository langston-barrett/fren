-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A static error stops `#fren_check` (`Reqs/View#static-errors`), unless
-- `#guard_msgs` expects it, so that a test can show errors and checks.
mod static_errors_test

/--
error: nonlinear arithmetic is not supported

note: the solver decides only linear integer arithmetic
help: one side of `*` must mention no variable and no uninterpreted function, such as `2 * x` or `(MAX - MIN) * x`
-/
#guard_msgs in
comp squared {
    in x: Int
    pub out y: Int
    ensure q: y = x * x
}

pub comp conflict {
    in x: Int
    pub out y: Int
    ensure a: y = x
    ensure b: y = x + 1
}
/--
error: `static_errors_test::conflict` is not realizable

note: for the input
          x = 0
      no outputs satisfy `a` and `b`
help: weaken one of them, or add an `assume` that rules this input out
---
info: `a` forces y = 0, but `b` forces y = 1
---
info: conflicts with `a`
---
info: fren: 0 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
