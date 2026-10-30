-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Checks set to testing (`Reqs/Check#checking-by-testing`) are not run in
-- Lean, which has no evaluator: `#fren_check` says that `fren check` runs
-- them, and asks the solver only about the rest.
mod evidence_test

pub proc word(text: String): (det accepted?) {
    ensure rule: accepted? iff text.matches?(r"[a-z]+")

    expect plain: when text = "ab", accepted?
    set_option fren.evidence "random" in
    expect wrong: when text.contains?("x"), not accepted?
}

set_option fren.evidence "random" in
pub proc all_tested(n: Int): (big?) {
    ensure r: big? iff n > 3
    expect wrong: when n = 4, not big?
}

set_option fren.evidence "random" in
expect global_tested(a_n: Int) {
    call a := all_tested(a_n)
    expect global_tested: when a.n = 4, a.big?
}

/--
info: the checks of `evidence_test::word` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the vacuity checks of `evidence_test::word` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver and enumeration decide them: set `fren.evidence` to `"solver"` or `"enumerated"` to have them run
---
info: the checks of `evidence_test::all_tested` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the vacuity and redundancy checks of `evidence_test::all_tested` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver and enumeration decide them: set `fren.evidence` to `"solver"` or `"enumerated"` to have them run
---
info: the checks of `evidence_test::global_tested` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the vacuity checks of `evidence_test::global_tested` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver and enumeration decide them: set `fren.evidence` to `"solver"` or `"enumerated"` to have them run
---
info: fren: 5 passed, 0 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check

/--
error: invalid evidence `maybe`

note: `"random"` has the checks tested on random behaviours instead of asked of the solver, `"enumerated"` has them decided by enumerating behaviours, smallest first, `"enumerated+random"` tests them too where enumeration is not complete, and `"solver"` is the default
-/
#guard_msgs in
set_option fren.evidence "maybe" in
pub proc bad(x?): (y?) { ensure r: y? iff x? }

/--
error: invalid evidence `enumerated+tested`

note: `"random"` has the checks tested on random behaviours instead of asked of the solver, `"enumerated"` has them decided by enumerating behaviours, smallest first, `"enumerated+random"` tests them too where enumeration is not complete, and `"solver"` is the default
note: `"tested"` was renamed to `"random"`; write `"enumerated+random"`
-/
#guard_msgs in
set_option fren.evidence "enumerated+tested" in
pub proc retired(x?): (y?) { ensure r: y? iff x? }

/--
error: `fren.evidence` cannot be set for a guarantee

note: it can be set before a procedure, an expectation or global expectation, a cover goal, a call or a `det` variable
-/
#guard_msgs in
pub proc misplaced(x?): (y?) {
    set_option fren.evidence "random" in
    ensure r: y? iff x?
}

/--
error: `fren.lint.nonminimal_bool` cannot be set before a member

note: before a member, `set_option` sets only `fren.evidence`; other options are set before the procedure
-/
#guard_msgs in
pub proc other_option(x?): (y?) {
    set_option fren.lint.nonminimal_bool "allow" in
    ensure r: y? iff x?
}
