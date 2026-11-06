-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Each solver query, and each step that builds or reads a model, has Lean's
-- heartbeat limit to itself (`Reqs/View#check-results`), so a procedure does
-- not reach it only by having many clauses, as `lang::operator_rules` did
-- (#710).
-- Under one limit for the whole procedure, this one's check took between
-- 200 and 400 thousand heartbeats and stopped at 100; it passes at 50.
-- Heartbeat counts move with Lean and lean-smt: if an upgrade makes these
-- tests fail, adjust the number of clauses or the limit, keeping each
-- procedure's total far above the limit and each step below it.
proc many(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
}

/-- info: fren: 16 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
set_option maxHeartbeats 100 in
#fren_check

-- And a cover goal after them, whose goal and witness are built under a
-- limit of their own.
proc many_covered(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
    cover reached: x = 2 and y = 3
}

-- And a clause that fails after them is reported with its counterexample,
-- which is confirmed and rendered under a limit of its own, not as the
-- limit reached.
proc many_failing(x: Int, y: Int): (z: Int) {
    ensure r: z = x + y
    expect c1: z - y = x
    expect c2: z - x = y
    expect c3: x + y = z
    expect c4: y + x = z
    expect c5: z + 1 > x + y
    expect c6: z - 1 < x + y
    expect c7: 2 * z = 2 * x + 2 * y
    expect c8: z + z = x + x + y + y
    expect c9: z >= x + y
    expect c10: z <= x + y
    expect c11: when x > 0, z > y
    expect c12: when y > 0, z > x
    expect bad: when x = 1 and y = 2, z = x
}

/--
info: cover goal `many_covered::reached` is met

witness: x = 2, y = 3, z = 5
---
error: expectation `many_failing::bad` does not hold

counterexample: x = 1, y = 2, z = 3
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: fren: 50 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option maxHeartbeats 100 in
#fren_check

open Lean

mod instance_heartbeats

pub fn other<T>(x: T): (r: T) { ensure diff: other(x) != x }
proc caller(x: Int): (y: Int) { out y := x }

-- Observe the budget at type instantiation, before the nested check can
-- start a budget of its own. Both the generic and foreign paths must give
-- Bool and Int separate starts; resetting only the nested checks fails.
-- Apply the runtime limit after elaborating the test term.
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    withOptions (fun o => maxHeartbeats.set o 100) do
      let st ← Fren.getState
      let some c := st.bodies.get? `instance_heartbeats.other | throwError "missing other"
      let some b := st.comps.get? `instance_heartbeats.caller | throwError "missing caller"
      for foreign in [false, true] do
        withCurrHeartbeats do
          let starts ← IO.mkRef (#[] : Array Nat)
          let hooks : Fren.ElabHooks := { Fren.elabHooks with
            leanType := fun ty => do
              let start := (← readThe Lean.Core.Context).initHeartbeats
              starts.modify (·.push start)
              Lean.Core.checkMaxHeartbeats "instance contract"
              Fren.elabHooks.leanType ty }
          let instances := #[#[Fren.Core.Ty.bool], #[Fren.Core.Ty.int]]
          let (rs, _, _, _) ← if foreign then
            Fren.checkComp b #[.realizable] none (some hooks) #[]
              (instances.map fun ts => (`instance_heartbeats.other, ts))
          else Fren.checkComp c #[.realizable] none (some hooks) instances
          unless rs.size == (if foreign then 3 else 2) && rs.all (·.verdict == .pass) do
            throwError "missing instance results"
          let starts ← starts.get
          unless starts.size == 2 && starts[0]! < starts[1]! do
            throwError "instance construction reused a heartbeat budget"
