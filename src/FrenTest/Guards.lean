-- keep-sorted start
import Fren
-- keep-sorted end

-- Lean-only behaviour of guards: Lean's term-mode `match` has no guards,
-- so a `match` with guards generates `if`s that test each arm's pattern
-- and guard together, falling through to the arms after it; where its
-- arms without guards are not exhaustive and no arm is taken, an index out
-- of range of the empty sequence, `Fren.Seq.nth ∅ 0`, as a table without
-- a `_` row has (`Reqs/Generated`).

open Fren.Lang

mod guard_test

enum Mode { Off, Heat }

comp pick {
  in m: Mode
  in t: Int
  pub out y: Int
  pub out z: Int

  ensure r: y = match m { Mode::Off if t > 0 => 1, Mode::Off => 2, Mode::Heat => 3 }
  ensure s: z = match t { n if n > 0 => 1, n if n <= 0 => 2 }
}

/--
info: @[reducible] def Fren.Generated.guard_test.pick.ensure.r : guard_test.Mode → Int → Int → Int → Prop :=
fun m t y z => y = if m = guard_test.Mode.Off ∧ t > 0 then 1 else if m = guard_test.Mode.Off then 2 else 3
-/
#guard_msgs in
#print guard_test.pick.ensure.r

/--
info: @[reducible] def Fren.Generated.guard_test.pick.ensure.s : guard_test.Mode → Int → Int → Int → Prop :=
fun m t y z => z = if t > 0 then 1 else if t ≤ 0 then 2 else ∅.nth 0
-/
#guard_msgs in
#print guard_test.pick.ensure.s

-- The solver proves an `impl` of a component with guards.
#guard_msgs in
impl pick_impl: pick for (m : guard_test.Mode) (t : Int) {
  m := m, t := t,
  y := if m = guard_test.Mode.Heat then 3 else if t > 0 then 1 else 2,
  z := if t > 0 then 1 else 2,
}
