-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Refinement (`Reqs/Lang/Refinement`), decided by the solver, failing, set
-- to testing, and proved in Lean, without bindings and with them.
mod refinement_test

pub proc precise(x: Int): (y: Int) {
    ensure r: y = x + 1
}

pub proc rough(x: Int): (y: Int) {
    assume small: x < 100
    ensure above: y > x
}

pub proc wrong(x: Int): (y: Int) {
    ensure below: y < x
}

refine by_solver: precise refines rough
refine fails: precise refines wrong

set_option fren.evidence "tested" in
refine by_testing: precise refines rough

-- The proof is Lean, so its names need not be Fren identifiers.
refine by_proof: precise refines rough by
  intro x₁ px py _
  refine ⟨trivial, fun ⟨_, _⟩ => ?_⟩
  omega

-- Set to testing, with an instance in the abstract component whose binding
-- has an index: Lean asks the solver nothing about it, not even that
-- binding's definedness, so it adds nothing to the summary.
pub proc helper(v: Int): (w: Int) {
    ensure r: w = v
}

pub proc first(q: Seq<Int>): (y: Int) {
    assume nonempty: q != []
    call h := helper(q[0])
    ensure r: y = h.w
}

pub proc exact(q: Seq<Int>): (y: Int) {
    assume nonempty: q != []
    ensure r: y = q[0]
}

set_option fren.evidence "tested" in
refine same: exact refines first

-- With bindings (`Reqs/Lang/Refinement#bindings`): `shifted` names its
-- variables differently, and `stops` refines `forbidding` through an
-- abstraction function.
pub proc shifted(v: Int): (w: Int) {
    ensure r: w = v + 1
}

refine bound_by_solver: shifted refines rough { x := v, y := w }
refine bound_fails: shifted refines wrong { x := v, y := w }

set_option fren.evidence "tested" in
refine bound_by_testing: shifted refines rough { x := v, y := w }

refine bound_by_proof: shifted refines rough { x := v, y := w } by
  intro v sv sw _
  refine ⟨trivial, fun ⟨_, _⟩ => ?_⟩
  omega

pub enum Level { Allow, Warn, Forbid }

pub proc forbidding(forbidden?): (stops?) {
    ensure r: stops? iff forbidden?
}

pub proc stops(level: Level): (failures: Int) {
    ensure f: failures = (if level = Level::Forbid then 1 else 0)
}

refine abstraction: stops refines forbidding { forbidden? := level = Level::Forbid, stops? := failures > 0 }

pub proc other(x: Int): (z: Int) { ensure r: z = x }

/--
error: `refinement_test::other` cannot refine `refinement_test::rough`: it has no variable `y`

note: each parameter of `refinement_test::rough` must be a parameter of `refinement_test::other`, and each output a result, of the same type, or one that widens: an output may be a `Nat` for an `Int`, and a parameter an `Int` for a `Nat`
help: or bind it to an expression over the variables of `refinement_test::other`, as in `{ y := ... }`
-/
#guard_msgs in
refine bad: other refines rough

/--
error: `refinement_test::rough` has no variable `q`

note: a refinement binds variables of the refined procedure; those of `refinement_test::rough` are `x` and `y`
help: a variable with a similar name exists: `x`
-/
#guard_msgs in
refine bad_name: shifted refines rough { q := v, y := w }

/--
error: a binding of a parameter of `refinement_test::rough` may only mention parameters of `refinement_test::shifted`, but `w` is an output

note: the parameters of `refinement_test::rough` are chosen by the environment, before `refinement_test::shifted` chooses its outputs
help: bind an output of the refined procedure to it instead
-/
#guard_msgs in
refine bad_mention: shifted refines rough { x := w, y := w }

/--
error: expectation `refinement_test::fails::below` does not hold

counterexample: x = 0, precise.x = 0, precise.y = 1
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: the checks of `refinement_test::by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the checks of `refinement_test::same` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
error: expectation `refinement_test::bound_fails::below` does not hold

counterexample: v = 0, shifted.v = 0, shifted.w = 1
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: the checks of `refinement_test::bound_by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: fren: 28 passed, 2 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
