-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- fren-covers: check::runs_premises
-- A `#fren_check` that names only a caller still checks the procedure that
-- it calls, for its evidence, though it reports nothing of it
-- (`check::runs_premises`): `never` has no outputs, so the caller's checks
-- that rest on its realizability are inconclusive, as `fren check` says.
mod evidence_premises_test

proc never(x: Int): (y: Int) {
    ensure above: y > x
    ensure below: y < x
}

proc caller(x: Int): (z: Int) {
    call c := never(x)
    ensure q: z = c.y
    expect wrong: z = 5
}

/--
warning: the realizability of `evidence_premises_test::caller` rests on the realizability of `evidence_premises_test::never`, which did not pass

note: its proof has the realizability of `evidence_premises_test::never` among its hypotheses, which may not hold, so it may hold vacuously (`Reqs/Evidence`)
help: make the check it rests on pass
---
warning: `evidence_premises_test::caller::wrong` rests on the realizability of `evidence_premises_test::never`, which did not pass

note: its proof has the realizability of `evidence_premises_test::never` among its hypotheses, which may not hold, so it may hold vacuously (`Reqs/Evidence`)
help: make the check it rests on pass
---
info: fren: 0 passed, 0 failed, 2 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check caller

-- A refinement claim's checks rest on its abstraction's realizability: a
-- `#fren_check` that names only the global expectation still checks the
-- abstraction, and the procedure that it calls, for their evidence.
proc precise(x: Int): (y: Int) {
    ensure r: y = x + 1
}

proc vacuous(x: Int): (z: Int) {
    call n := never(x)
    ensure r: z = n.y
}

expect claimed(x: Int) {
    call c := precise(x)
    refines c vacuous(x)
}

/--
warning: `evidence_premises_test::claimed::refines_1` rests on the realizability of `evidence_premises_test::vacuous`, which did not pass

note: its proof has the realizability of `evidence_premises_test::vacuous` among its hypotheses, which may not hold, so it may hold vacuously (`Reqs/Evidence`)
help: make the check it rests on pass
---
info: fren: 1 passed, 0 failed, 1 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check claimed
