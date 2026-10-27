-- keep-sorted start
import Fren.Impl
-- keep-sorted end
open Fren.Lang

-- A name declared with `!` is the name without it, in Lean as in Fren: an
-- `impl` maps it by that name, and the generated definitions bind it.
mod shadowing_test

set_option fren.lint.non_snake_case "allow"

pub const RATE: Int := 2
pub enum Shape { Circle(Int), Square }

pub proc scaled(RATE!: Int, s: Shape): (y: Int) {
    ensure r: y = match s { Shape::Circle(RATE!) => RATE, _ => RATE }
}

pub fn bump(RATE!: Int): Int := RATE + 1

/--
info: @[reducible] def Fren.Generated.shadowing_test.scaled.ensure.r : Int → shadowing_test.Shape → Int → Prop :=
fun RATE s y =>
  y =
    if s = shadowing_test.Shape.Circle (shadowing_test.Shape.Circle.x0 s) then shadowing_test.Shape.Circle.x0 s
    else RATE
-/
#guard_msgs in #print shadowing_test.scaled.ensure.r

/--
info: @[reducible] def Fren.Generated.shadowing_test.bump : Int → Int :=
fun RATE => RATE + 1
-/
#guard_msgs in #print shadowing_test.bump

impl payload: scaled for (n : Int) { RATE := n, s := shadowing_test.Shape.Square, y := n } by
  intro n _
  simp [fren_spec]

/-- error: `s!` is a Lean token, so it cannot be declared

note: Lean reads `s!` as a token of its own, not as `s` followed by `!`
help: rename the declaration -/
#guard_msgs in
proc token(s!: Int): (y: Int) { ensure r: y = s }

-- The fix for `!=` is offered only where `=` directly follows the `!`.
/--
error: cannot find `x!` in this scope

note: `!` is written only where a name is declared, to shadow another
help: for `!=`, write a space before the `!`
help: for the name `x`, remove the `!`
-/
#guard_msgs in
proc compare(x: Int): (p?) { ensure r: p? iff x!=1 }

/--
error: cannot find `x!` in this scope

note: `!` is written only where a name is declared, to shadow another
help: for the name `x`, remove the `!`
-/
#guard_msgs in
proc bare(x: Int): (p?) { ensure r: p? iff x! }
