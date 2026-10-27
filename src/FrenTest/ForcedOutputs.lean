-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- `fren.examples` bounds the notes of guarantees that force an output to
-- different values, as `fren check --examples` does (`Reqs/Lean#options`).

proc pinned(x: Int): (y: Int) {
    ensure low: y = x
    ensure high: y = x + 1
}

/--
error: `pinned` is not realizable

note: for the input
          x = 0
      no outputs satisfy `low` and `high`
help: weaken one of them, or add an `assume` that rules this input out
---
info: `low` forces y = 0, but `high` forces y = 1
---
info: `high` forces y = 1, but `low` forces y = 0
---
info: fren: 0 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option fren.examples 2 in
#fren_check

/--
error: `pinned` is not realizable

note: for the input
          x = 0
      no outputs satisfy `low` and `high`
help: weaken one of them, or add an `assume` that rules this input out
---
info: conflicts with `high`
---
info: conflicts with `low`
---
info: fren: 0 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option fren.examples 0 in
#fren_check
