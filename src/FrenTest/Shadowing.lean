-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- A name declared with `!` is the name without it, in Lean as in Fren: an
-- `impl` maps it by that name, and the generated definitions bind it.
mod shadowing_test

set_option fren.lint.non_snake_case "allow"

pub const RATE: Int := 2
pub enum Shape { Circle(Int), Square }

pub comp scaled {
    in RATE!: Int
    in s: Shape
    pub out y: Int

    req r: y = match s { Shape::Circle(RATE!) => RATE, _ => RATE }
}

pub fn bump(RATE!: Int): Int := RATE + 1

/--
info: @[reducible] def shadowing_test.scaled.req.r : Int → shadowing_test.Shape → Int → Prop :=
fun RATE s y =>
  y =
    if s = shadowing_test.Shape.Circle (shadowing_test.Shape.Circle.x0 s) then shadowing_test.Shape.Circle.x0 s
    else RATE
-/
#guard_msgs in #print shadowing_test.scaled.req.r

/--
info: @[reducible] def shadowing_test.bump : Int → Int :=
fun RATE => RATE + 1
-/
#guard_msgs in #print shadowing_test.bump

impl payload: scaled for (n : Int) { RATE := n, s := shadowing_test.Shape.Square, y := n } by
  intro n _
  simp [fren_spec]

-- `Fren.Core.leanBangTokens` is every token of Lean's, here, that is an
-- identifier followed by `!`, which both front ends reject as a declaration.
open Lean Elab Command in
#guard_msgs in
#eval show CommandElabM Unit from do
  let isIdent (t : String) := t.front.isAlpha && (t.dropEnd 1).all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '?'
  let toks := (Lean.Parser.getTokenTable (← getEnv)).values.filter fun t => t.length > 1 && t.endsWith "!" && isIdent t
  unless toks.qsort (· < ·) == Fren.Core.leanBangTokens.toArray.qsort (· < ·) do
    throwError "Lean's tokens that are an identifier and `!` are {toks.qsort (· < ·)}"

/-- error: `s!` is a Lean token, so it cannot be declared

note: Lean reads `s!` as a token of its own, not as `s` followed by `!`
help: rename the declaration -/
#guard_msgs in
comp token { in s!: Int pub out y: Int req r: y = s }
