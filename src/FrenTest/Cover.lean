-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A cover goal generates `p.cover.n`, and, once `#fren_check` finds its
-- witness, the theorem `p.cover.n.met`, proved by `decide`
-- (`Reqs/Generated#cover-goals`).
mod cover_test

pub enum Mode { Off, Heat }

pub comp heater {
    in temp: Int
    pub out mode: Mode
    out margin: Int

    ensure r: mode = (if temp < 18 then Mode::Heat else Mode::Off)
    ensure m: margin = 18 - temp

    cover heating: mode = Mode::Heat and margin > 2
}

/--
info: @[reducible] def cover_test.heater.cover.heating : Int → cover_test.Mode → Int → Prop :=
fun temp mode margin => mode = cover_test.Mode.Heat ∧ margin > 2
-/
#guard_msgs in #print cover_test.heater.cover.heating

#guard_msgs (drop info) in #fren_check heater

/--
info: cover_test.heater.cover.heating.met :
  ∃ temp mode margin,
    (cover_test.heater.assumes temp mode margin ∧ cover_test.heater.ensures temp mode margin) ∧
      cover_test.heater.cover.heating temp mode margin
-/
#guard_msgs in #check cover_test.heater.cover.heating.met

-- An abstract type: the witness is under some interpretation, which the
-- `∃` cannot state, so no theorem is added.
pub type Name

pub comp named {
    in n: Name
    in m: Name
    pub out same?

    ensure r: same? iff n = m

    cover distinct: not same?
}

#guard_msgs (drop info) in #fren_check named

/-- error: Unknown constant `cover_test.named.cover.distinct.met` -/
#guard_msgs in #check cover_test.named.cover.distinct.met

-- Proved in the kernel, not on the solver's word.
/-- info: 'cover_test.heater.cover.heating.met' does not depend on any axioms -/
#guard_msgs in #print axioms cover_test.heater.cover.heating.met
