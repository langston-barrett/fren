-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Each solver query, and each step that builds or reads a model, has Lean's
-- heartbeat limit to itself (`Reqs/View#check-results`), so a procedure does
-- not reach it only by having many clauses, as `lang::operator_rules` did
-- (#710).
-- Under one limit for the whole procedure, this one's check took between
-- 200 and 400 thousand heartbeats and stopped at 100; it passes at 50.
-- Heartbeat counts move with Lean and lean-smt: if an upgrade makes these
-- tests fail, adjust the number of clauses or the limit, keeping each
-- procedure's total far above the limit and each step below it.
proc many(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
}

/-- info: fren: 16 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
set_option maxHeartbeats 100 in
#fren_check

-- And a cover goal after them, whose goal and witness are built under a
-- limit of their own.
proc many_covered(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
    cover reached: x = 2 and y = 3
}

-- And a clause that fails after them is reported with its counterexample,
-- which is confirmed and rendered under a limit of its own, not as the
-- limit reached.
proc many_failing(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
    expect bad: when x = 1 and y = 2, z = x
}

/--
info: cover goal `many_covered::reached` is met

witness: x = 2, y = 3, z = 5
---
error: expectation `many_failing::bad` does not hold

counterexample: x = 1, y = 2, z = 3
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: fren: 50 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option maxHeartbeats 100 in
#fren_check
