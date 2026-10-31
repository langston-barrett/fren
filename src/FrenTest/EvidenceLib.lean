-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- fren-covers: check::runs_premises
-- A library whose procedure `echo` is set to random testing: `#fren_check`
-- keeps the evidence of its realizability, the caveat `Random`, in the
-- environment, for the modules that import this one (`EvidenceClient`).
mod evidence_lib

set_option fren.evidence "random" in
pub proc echo(x: Int): (y: Int) {
    ensure r: y = x
}

/--
info: the checks of `evidence_lib::echo` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the redundancy checks of `evidence_lib::echo` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver and enumeration decide them: set `fren.evidence` to `"solver"` or `"enumerated"` to have them run
---
info: fren: 0 passed, 0 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check echo
