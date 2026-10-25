-- keep-sorted start
import Fren
-- keep-sorted end

-- Lean-only behaviour of the cardinality operators: `exactly_one?` and
-- `at_most_one?` generate the sum of `if a then 1 else 0` over their
-- arguments, compared with 1, which is what lean-smt is given, with no
-- definition of its own to unfold.

open Fren.Lang

mod cardinality_test

comp modes {
  in a?
  in b?
  in x: Int
  pub out one?
  pub out some?

  req r: one? iff exactly_one?(a?, b?, x > 0)
  req s: some? iff at_most_one?(a?)
}

/--
info: @[reducible] def cardinality_test.modes.req.r : Bool → Bool → Int → Bool → Bool → Prop :=
fun a? b? x one? some? =>
  one? = true ↔ (((if a? = true then 1 else 0) + if b? = true then 1 else 0) + if x > 0 then 1 else 0) = 1
-/
#guard_msgs in
#print cardinality_test.modes.req.r

/--
info: @[reducible] def cardinality_test.modes.req.s : Bool → Bool → Int → Bool → Bool → Prop :=
fun a? b? x one? some? => some? = true ↔ (if a? = true then 1 else 0) ≤ 1
-/
#guard_msgs in
#print cardinality_test.modes.req.s

-- The sum means what `List.count` of the `true` arguments does.
example (a b c : Bool) :
    ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : Int) = ([a, b, c].count true : Nat) := by
  cases a <;> cases b <;> cases c <;> decide
