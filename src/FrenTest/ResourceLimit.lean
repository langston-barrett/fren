-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- A query that reaches `fren.resourceLimit` is inconclusive, as under
-- `fren check --resource-limit` (`Reqs/Cli#limits`).
set_option fren.timeout 0
set_option fren.resourceLimit 1

comp limited {
    in x: Int
    pub out y: Int
    ensure r: y = x + 1
    expect bigger: y > x
}

/--
warning: could not decide whether `limited` is realizable: RESOURCEOUT

note: the solver gave up, so this check neither passed nor failed
help: raise the time limit with `--timeout`, or simplify the constraints involved
---
warning: could not decide whether `limited::bigger` holds: RESOURCEOUT

note: the solver gave up, so this check neither passed nor failed
help: raise the time limit with `--timeout`, or simplify the constraints involved
---
warning: could not decide whether `limited::r` is redundant: RESOURCEOUT

note: the solver gave up, so this check neither passed nor failed
help: raise the time limit with `--timeout`, or simplify the constraints involved
---
info: fren: 0 passed, 0 failed, 3 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
