-- keep-sorted start
import Fren.Elab
-- keep-sorted end

-- Lean-only behaviour of nested, literal and range patterns: what a `match`
-- generates.

open Fren.Lang

mod nested_pattern

pub enum Shape { Circle(Int), Empty }
pub enum Reply { Ok(Shape), Err(Int) }

const MAX: Int := 2 * 5

proc tests(r: Reply, n: Int, s: String): (x: Int, y: Int, z: Int) {
  ensure nested: x = match r {
    Reply::Ok(Shape::Circle(radius)) => radius,
    Reply::Err(0) => 1,
    _ => 2,
  }
  ensure ranges: y = match n {
    ..=-1 => 0,
    0..MAX => 1,
    _ => 2,
  }
  ensure strings: z = match s {
    "a" => 1,
    _ => 2,
  }
}

-- A nested pattern tests the payload, read with the selector, after the
-- variant; a literal is an equality.
/--
info: @[reducible] def Fren.Generated.nested_pattern.tests.ensure.nested : nested_pattern.Reply →
  Int → String → Int → Int → Int → Prop :=
fun r n s x y z =>
  x =
    if
        r = nested_pattern.Reply.Ok (nested_pattern.Reply.Ok.x0 r) ∧
          nested_pattern.Reply.Ok.x0 r =
            nested_pattern.Shape.Circle (nested_pattern.Shape.Circle.x0 (nested_pattern.Reply.Ok.x0 r)) then
      nested_pattern.Shape.Circle.x0 (nested_pattern.Reply.Ok.x0 r)
    else
      if r = nested_pattern.Reply.Err (nested_pattern.Reply.Err.x0 r) ∧ nested_pattern.Reply.Err.x0 r = 0 then 1 else 2
-/
#guard_msgs in
#print nested_pattern.tests.ensure.nested

-- A range is comparisons with its bounds, a constant's by its value, and
-- `0..MAX` excludes `MAX`.
/--
info: @[reducible] def Fren.Generated.nested_pattern.tests.ensure.ranges : nested_pattern.Reply →
  Int → String → Int → Int → Int → Prop :=
fun r n s x y z => y = if n ≤ -1 then 0 else if 0 ≤ n ∧ n ≤ 9 then 1 else 2
-/
#guard_msgs in
#print nested_pattern.tests.ensure.ranges

/--
info: @[reducible] def Fren.Generated.nested_pattern.tests.ensure.strings : nested_pattern.Reply →
  Int → String → Int → Int → Int → Prop :=
fun r n s x y z => z = if s = Fren.Str.lit "a" then 1 else 2
-/
#guard_msgs in
#print nested_pattern.tests.ensure.strings
