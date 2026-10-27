-- keep-sorted start
import Fren.Elab
-- keep-sorted end

-- Lean-only behaviour of the cardinality operators: `exactly_one?` and
-- `at_most_one?` generate the sum of `if a then 1 else 0` over their
-- arguments, compared with 1, which is what lean-smt is given, with no
-- definition of its own to unfold.

open Fren.Lang

mod cardinality_test

-- `at_most_one?(a?)` is always `true`, deliberately.
set_option fren.lint.nonminimal_bool "allow" in
proc modes(a?, b?, x: Int): (one?, some?) {
  ensure r: one? iff exactly_one?(a?, b?, x > 0)
  ensure s: some? iff at_most_one?(a?)
}

/--
info: @[reducible] def Fren.Generated.cardinality_test.modes.ensure.r : Bool → Bool → Int → Bool → Bool → Prop :=
fun a? b? x one? some? =>
  one? = true ↔ (((if a? = true then 1 else 0) + if b? = true then 1 else 0) + if x > 0 then 1 else 0) = 1
-/
#guard_msgs in
#print cardinality_test.modes.ensure.r

/--
info: @[reducible] def Fren.Generated.cardinality_test.modes.ensure.s : Bool → Bool → Int → Bool → Bool → Prop :=
fun a? b? x one? some? => some? = true ↔ (if a? = true then 1 else 0) ≤ 1
-/
#guard_msgs in
#print cardinality_test.modes.ensure.s

-- The sum means what `List.count` of the `true` arguments does, for any
-- number of arguments.
theorem cardinality_sum_eq_count (bs : List Bool) :
    (bs.map fun b => if b then (1 : Int) else 0).sum = (bs.count true : Nat) := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [ih] <;> omega
