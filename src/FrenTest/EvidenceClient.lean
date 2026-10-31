-- keep-sorted start
import FrenTest.EvidenceLib
-- keep-sorted end
open Fren.Lang

-- fren-covers: check::runs_premises
-- The checks of a caller in a module that imports `EvidenceLib` rest on the
-- evidence of `echo`'s realizability that its `#fren_check` kept: the
-- caveat `Random`, so `#fren_check` reports no verdict for them, as for
-- checks set to random testing (`check::runs_premises`, `check::hosted_runs`).
mod evidence_client
use evidence_lib::echo

proc caller(x: Int): (z: Int) {
    call c := echo(x)
    ensure q: z = c.y + 1
    expect bigger: z > x
}

/--
info: the checks of `evidence_client::caller` that rest on checks set to random testing are run by `fren check`, not in Lean (`Reqs/Evidence#lean`)
---
info: fren: 1 passed, 0 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check caller
