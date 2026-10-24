-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- Refinement (`Reqs/Lang/Refinement`), decided by the solver, failing, set
-- to testing, and proved in Lean.
mod refinement_test

pub comp precise {
    in x: Int
    pub out y: Int
    req r: y = x + 1
}

pub comp rough {
    in x: Int
    pub out y: Int
    assume small: x < 100
    req above: y > x
}

pub comp wrong {
    in x: Int
    pub out y: Int
    req below: y < x
}

refine by_solver: precise refines rough
refine fails: precise refines wrong

set_option fren.evidence "tested" in
refine by_testing: precise refines rough

refine by_proof: precise refines rough by
  intro x px py _
  refine ⟨trivial, fun ⟨_, _⟩ => ?_⟩
  omega

pub comp other { in x: Int pub out z: Int req r: z = x }

/--
error: `refinement_test::other` cannot refine `refinement_test::rough`: it has no variable `y`

note: each input of `refinement_test::rough` must be an input of `refinement_test::other`, and each output a public output, of the same type
-/
#guard_msgs in
refine bad: other refines rough

/--
error: expectation `refinement_test::fails::below` does not hold

counterexample: x = -1, precise.x = -1, precise.y = 0
help: strengthen the requirements so that it follows, or correct the expectation
---
info: the checks of `refinement_test::by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: fren: 10 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
