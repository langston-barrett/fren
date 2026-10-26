-- keep-sorted start
import Fren.Elab
-- keep-sorted end
open Fren.Lang

-- A `let` or `where` becomes Lean's `have`, one for each definition, and a
-- `where` clause goes around the expression it follows (`Reqs/Generated`).
mod heating

pub comp heater {
  in temp: Int
  pub out on?

  ensure heat: on? iff cold? where limit := 18, cold? := temp < limit
  expect warm: let hot? := temp > 30 in when hot?, not on?
}

/--
info: @[reducible] def heating.heater.ensure.heat : Int → Bool → Prop :=
fun temp on? =>
  have «limit@0» := 18;
  have «cold?@1» := decide (temp < «limit@0»);
  on? = true ↔ «cold?@1» = true
-/
#guard_msgs in
#print heating.heater.ensure.heat

/--
info: @[reducible] def heating.heater.expect.warm : Int → Bool → Prop :=
fun temp on? =>
  have «hot?@0» := decide (temp > 30);
  «hot?@0» = true → ¬on? = true
-/
#guard_msgs in
#print heating.heater.expect.warm
