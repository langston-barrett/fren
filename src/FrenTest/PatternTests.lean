-- keep-sorted start
import Fren
-- keep-sorted end

-- Lean-only behaviour of pattern tests: `is` is a keyword only where
-- `Fren.Lang` is open, and `e is P` generates the test of each of its
-- pattern's alternatives.

/-- Outside `Fren.Lang`, `is` is an ordinary identifier. -/
def FrenTest.is : Nat := 1

open Fren.Lang

mod pattern_test

pub enum Shape { Circle(Int), Rect(Int, Int), Empty }

set_option fren.lint.irrefutable_is "allow" in
comp kinds {
  in s: Shape
  pub out round?
  pub out boxy?
  pub out any?

  req round: round? iff s is Shape::Circle(_)
  req boxy: boxy? iff s is Shape::Rect(_, _) | Shape::Empty
  req any: any? iff s is _
}

-- The scrutinee is equal to the variant built from its own payload, as in
-- the test of a `match` arm.
/--
info: @[reducible] def pattern_test.kinds.req.round : pattern_test.Shape → Bool → Bool → Bool → Prop :=
fun s round? boxy? any? => round? = true ↔ s = pattern_test.Shape.Circle (pattern_test.Shape.Circle.x0 s)
-/
#guard_msgs in
#print pattern_test.kinds.req.round

-- An or-pattern is the disjunction of its alternatives' tests.
/--
info: @[reducible] def pattern_test.kinds.req.boxy : pattern_test.Shape → Bool → Bool → Bool → Prop :=
fun s round? boxy? any? =>
  boxy? = true ↔
    s = pattern_test.Shape.Rect (pattern_test.Shape.Rect.x0 s) (pattern_test.Shape.Rect.x1 s) ∨
      s = pattern_test.Shape.Empty
-/
#guard_msgs in
#print pattern_test.kinds.req.boxy

-- `_` matches every value.
/--
info: @[reducible] def pattern_test.kinds.req.any : pattern_test.Shape → Bool → Bool → Bool → Prop :=
fun s round? boxy? any? => any? = true ↔ true = true
-/
#guard_msgs in
#print pattern_test.kinds.req.any

-- A pattern test and a chained comparison bind as comparisons, which do not
-- chain with each other, so a fix that writes one where the other's operand
-- is, in either front end, puts it in parentheses (`Fren.Core.BKind.slots`).
#guard ({ text := "s is A(_)", prec := Fren.Core.BKind.patternTest.prec } : Fren.Core.BText).inSlot
  (Fren.Core.BKind.chain #["<=", "<"]).slots[1]! == "(s is A(_))"
#guard ({ text := "0 <= x < 9", prec := (Fren.Core.BKind.chain #["<=", "<"]).prec } : Fren.Core.BText).inSlot
  Fren.Core.BKind.patternTest.slots[0]! == "(0 <= x < 9)"
