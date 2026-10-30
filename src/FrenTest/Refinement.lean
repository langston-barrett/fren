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
    -- Keep the failing refinement's witness unique: the diagnostic test
    -- checks rendered values, independently of the solver's model choice.
    ensure below: x != 0 or y < x
}

expect by_solver(x: Int) {
    assume small: x < 100
    call precise := precise(x)
    refines precise rough(x)
}
expect fails(x: Int) {
    call precise := precise(x)
    refines precise wrong(x)
}

set_option fren.evidence "random" in
expect by_testing(x: Int) {
    assume small: x < 100
    call precise := precise(x)
    refines precise rough(x)
}

-- The proof is Lean, so its names need not be Fren identifiers.
expect by_proof(x: Int) {
    assume small: x < 100
    call precise := precise(x)
    refines precise rough(x) by
      intros
      simp_all
      omega
}

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

set_option fren.evidence "random" in
expect same(q: Seq<Int>) {
    assume nonempty: q != []
    call exact := exact(q)
    refines exact first(q)
}

-- With bindings (`Reqs/Lang/Refinement#bindings`): `shifted` names its
-- variables differently, and `stops` refines `forbidding` through an
-- abstraction function.
pub proc shifted(v: Int): (w: Int) {
    ensure r: w = v + 1
}

expect bound_by_solver(v: Int) {
    assume small: v < 100
    call shifted := shifted(v)
    refines shifted rough(v)
}
expect bound_fails(v: Int) {
    call shifted := shifted(v)
    refines shifted wrong(v)
}

set_option fren.evidence "random" in
expect bound_by_testing(v: Int) {
    assume small: v < 100
    call shifted := shifted(v)
    refines shifted rough(v)
}

expect bound_by_proof(v: Int) {
    assume small: v < 100
    call shifted := shifted(v)
    refines shifted rough(v) by
      intros
      simp_all
      omega
}

pub enum Level { Allow, Warn, Forbid }

pub proc forbidding(forbidden?): (stops?) {
    ensure r: stops? iff forbidden?
}

pub proc stops(level: Level): (failures: Int) {
    ensure f: failures = (if level = Level::Forbid then 1 else 0)
}

expect abstraction(level: Level) {
    call stops := stops(level)
    expect r: (stops.failures > 0) iff level = Level::Forbid
}

-- Result names are independent; result types still have to widen.
pub proc other(x: Int): (z: Int) { ensure r: z = x }
expect renamed(x: Int) {
    call other := other(x)
    refines other rough(x - 1)
}

pub proc natural(x: Int): (y: Nat) { ensure r: y = (if x > 0 then 1 else 0) }
/-- error: refinement result type mismatch at `y`: call result `z` cannot flow to the specification result -/
#guard_msgs in
expect bad(x: Int) {
    call other := other(x)
    refines other natural(x)
}

/--
error: type mismatch: expected `Int`, found `Bool`

note: specification parameter `x` has type `Int`
help: to turn a `Bool` into an `Int`, write `if b? then 1 else 0`
-/
#guard_msgs in
expect bad_argument(x: Int) {
    call other := other(x)
    refines other rough(true)
}

/--
error: expectation `refinement_test::fails::refines_1` does not hold

counterexample: x = 0, precise.y = 1
help: correct the expectation, or assume what it needs
---
info: the checks of `refinement_test::by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: the checks of `refinement_test::same` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
error: expectation `refinement_test::bound_fails::refines_1` does not hold

counterexample: v = 0, shifted.w = 1
help: correct the expectation, or assume what it needs
---
info: the checks of `refinement_test::bound_by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: fren: 39 passed, 2 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
