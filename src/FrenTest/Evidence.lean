-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- Checks set to testing (`Reqs/Check#checking-by-testing`) are not run in
-- Lean, which has no evaluator: `#fren_check` says that `fren check` runs
-- them, and asks the solver only about the rest.
mod evidence_test

pub comp word {
    in text: String
    pub det out accepted?

    req rule: accepted? iff text.matches?(r"[a-z]+")

    expect plain: when text = "ab", accepted?
    set_option fren.evidence "tested" in
    expect wrong: when text.contains?("x"), not accepted?
}

set_option fren.evidence "tested" in
pub comp all_tested {
    in n: Int
    pub out big?
    req r: big? iff n > 3
    expect wrong: when n = 4, not big?
}

set_option fren.evidence "tested" in
expect global_tested: forall (a: all_tested), when a.n = 4, a.big?

/--
info: the checks of `evidence_test::word` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the checks of `evidence_test::all_tested` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the checks of `evidence_test::global_tested` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: fren: 5 passed, 0 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check

/--
error: invalid evidence `maybe`

note: `"tested"` has the checks tested instead of asked of the solver, and `"solver"` is the default
-/
#guard_msgs in
set_option fren.evidence "maybe" in
pub comp bad { in x? pub out y? req r: y? iff x? }

/--
error: `fren.evidence` cannot be set for a requirement

note: it can be set before a component, an expectation or global expectation, an instance or a `det out`
-/
#guard_msgs in
pub comp misplaced {
    in x?
    pub out y?
    set_option fren.evidence "tested" in
    req r: y? iff x?
}

/--
error: `fren.lint.nonminimal_bool` cannot be set before a member

note: before a member, `set_option` sets only `fren.evidence`; other options are set before the component
-/
#guard_msgs in
pub comp other_option {
    in x?
    pub out y?
    set_option fren.lint.nonminimal_bool "allow" in
    req r: y? iff x?
}
