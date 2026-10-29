-- fren-covers: refinement::positional_refinement, refinement::block_refinement, refinement::refinement_computed_local
import Fren.Elab

open Fren.Lang
set_option fren.lint.unused_variables "allow"
set_option fren.lint.unused_assumption "allow"
set_option fren.lint.constant_output "allow"
set_option fren.lint.definable_output "allow"
set_option fren.lint.assertions_on_constants "allow"
set_option fren.lint.duplicate_constraint "allow"

mod hosted_refines

proc concrete(x: Nat): (y: Nat) { ensure value: y = x }
proc abstract(x: Int): (renamed: Int) {
  let doubled: Int := x + x
  ensure value: renamed + renamed = doubled
}

-- Both flows widen, results are positional, and private lets are computed.
expect positional(n: Nat) {
  call c := concrete(n)
  refines c abstract(n) by
    intro n cx cy h
    simp_all
}
example (n cx cy : Nat) :
    Fren.Generated.hosted_refines.positional.expect.refines_1 n cx cy =
      ((cy : Int) + cy = (n : Int) + n) := rfl

-- Definitions of public results become claims, even without ensures.
proc defined(x: Int): (renamed: Int) { out renamed := x + 1 }
expect definition(n: Nat) {
  call c := concrete(n)
  refines c defined(n)
}
example (n cx cy : Nat) :
    Fren.Generated.hosted_refines.definition.expect.refines_1 n cx cy =
      ((cy : Int) = (n : Int) + 1) := rfl

-- Neither an abstract assumption nor a similarly named private let is a premise.
proc impossible(x: Int): (r: Int) {
  assume unavailable: false
  let y: Int := x + 1
  ensure impossible: r = y
}
expect no_spec_assumptions(n: Nat) {
  call c := concrete(n)
  refines c impossible(n)
}
example (n cx cy : Nat) :
    Fren.Generated.hosted_refines.no_spec_assumptions.expect.refines_1 n cx cy =
      ((cy : Int) = (n : Int) + 1) := rfl

-- Several results follow declaration order rather than their names.
proc pair(x: Int): (first: Int, second: Int) {
  ensure one: first = x
  ensure two: second = x + 1
}
proc swapped(x: Int): (second: Int, first: Int) {
  ensure one: second = x
  ensure two: first = x + 1
}
expect positional_pair(n: Int) {
  call c := pair(n)
  refines c swapped(n) by
    intros
    simp_all
}

-- Ordinary block assumptions are available to optional proofs.
expect block_assumptions(n: Nat) {
  assume excluded: false
  call c := concrete(n)
  refines c defined(n) by
    intros
    simp_all
}

/-- error: refinement result type mismatch at `y`: call result `renamed` cannot flow to the specification result -/
#guard_msgs in
expect narrowing(n: Int) {
  call c := defined(n)
  refines c concrete(0)
}

/-- error: `refines` is accepted only in global expectation blocks -/
#guard_msgs in
proc wrong(n: Nat) { call c := concrete(n) refines c abstract(n) }

/-- error: `c` is not a call in this global expectation block -/
#guard_msgs in
expect missing(n: Nat) { refines c abstract(n) }

proc hidden(x: Int): (r: Int) { exists h: Int ensure value: r = h }
/-- error: specification `exists` variable `h` is not supported by `refines` -/
#guard_msgs in
expect unsupported(n: Nat) { call c := concrete(n) refines c hidden(n) }

/-- error: top-level `refine` has been removed; use `refines c spec(args)` in a global expectation block -/
#guard_msgs in
refine old: concrete refines concrete

/-- error: a refinement proof must not contain `sorry` -/
#guard_msgs in
expect bogus(n: Nat) { call c := concrete(n) refines c abstract(n) by sorry }

-- A tactic failure must reject the member, even if its claim is true.
/--
error: deliberately bad refinement proof
n c.x c.y : Nat
⊢ ∀ (n c.x c.y : Nat), c.x = n ∧ c.y = c.x → ↑c.y + ↑c.y = ↑n + ↑n
-/
#guard_msgs in
expect failed_proof(n: Nat) {
  call c := concrete(n)
  refines c abstract(n) by
    fail "deliberately bad refinement proof"
}

proc false_spec(x: Int): (r: Int) {
  assume excluded: false
  ensure impossible: false
}
-- If spec assumptions were introduced, contradiction would succeed.
/--
error: specification assumptions are unavailable
n c.x c.y n✝ c.x✝ c.y✝ : Nat
x✝ : c.x✝ = n✝ ∧ c.y✝ = c.x✝
⊢ false = true
-/
#guard_msgs in
expect proof_has_no_spec_assumptions(n: Nat) {
  call c := concrete(n)
  refines c false_spec(n) by
    intros
    first | contradiction | fail "specification assumptions are unavailable"
}

-- Later call meanings must not enter the proof context.
/--
error: later call meanings are unavailable
n c.x c.y : Nat
later.x later.r : Int
n✝ c.x✝ c.y✝ : Nat
later.x✝ later.r✝ : Int
x✝ : c.x✝ = n✝ ∧ c.y✝ = c.x✝
⊢ false = true
-/
#guard_msgs in
expect proof_has_no_later_calls(n: Nat) {
  call c := concrete(n)
  refines c false_spec(n) by
    intros
    first | contradiction | fail "later call meanings are unavailable"
  call later := false_spec(n)
}

/--
error: type mismatch: expected `Nat`, found `Int`

note: specification parameter `x` has type `Nat`
note: an `Int` is never narrowed to a `Nat`, and `a - b` and `-a` are `Int`s, even of `Nat`s
-/
#guard_msgs in
expect input_narrowing(n: Int) { call c := concrete(0) refines c concrete(n) }

/-- error: `refines` is accepted only in global expectation blocks -/
#guard_msgs in
fn wrong_function(x: Int): (r: Int) { refines c abstract(x) out r := x }

proc no_results(x: Int) {}
/-- error: refinement result count mismatch: specification has 0, call has 1 -/
#guard_msgs in
expect result_arity(n: Nat) { call c := concrete(n) refines c no_results(n) }

-- Synthetic claim names must not collide with explicit expectations.
expect fresh_names(n: Nat) {
  call c := concrete(n)
  expect refines_1: c.y = n
  refines c abstract(n)
  refines c abstract(n)
}
example (n cx cy : Nat) :
    Fren.Generated.hosted_refines.fresh_names.expect.refines_2 n cx cy =
      Fren.Generated.hosted_refines.fresh_names.expect.refines_3 n cx cy := rfl
