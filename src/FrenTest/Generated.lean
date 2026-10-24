-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang


-- Lean-only behaviour that ui tests can't express: Fren's keywords are scoped
-- to `Fren.Lang`, and generated declarations are ordinary Lean definitions.
mod check

pub enum Verdict { Pass, Fail, Inconclusive }

use self::Verdict::{Pass, Fail, Inconclusive}

pub comp exit {
  in ran?
  in worst: Verdict
  pub out code: Int

  req not_run: unless ran?, code = 2
  req failed: when ran? and worst = Fail, code = 1
  req inconclusive: when ran? and worst = Inconclusive, code = 3
  req passed: when ran? and worst = Pass, code = 0

  expect zero_means_pass: when code = 0, ran? and worst = Pass
}

-- Generated declarations are ordinary Lean definitions.
/--
info: @[reducible] def check.exit.req.failed : Bool → check.Verdict → Int → Prop :=
fun ran? worst code => ran? = true ∧ worst = check.Verdict.Fail → code = 1
-/
#guard_msgs in
#print check.exit.req.failed

/--
info: @[reducible] def check.exit.reqs : Bool → check.Verdict → Int → Prop :=
fun ran? worst code =>
  check.exit.req.not_run ran? worst code ∧
    check.exit.req.failed ran? worst code ∧
      check.exit.req.inconclusive ran? worst code ∧ check.exit.req.passed ran? worst code
-/
#guard_msgs in
#print check.exit.reqs

/-- info: @[reducible] def check.exit.assumes : Bool → check.Verdict → Int → Prop :=
fun ran? worst code => True -/
#guard_msgs in
#print check.exit.assumes

-- An instance's variables follow the comp's own, named `w.x`.
comp always_runs {
  in worst: Verdict
  pub out code: Int

  inst e: exit { ran? := true, worst }

  req same: code = e.code
}

/--
info: @[reducible] def check.always_runs.inst.e : check.Verdict → Int → Bool → check.Verdict → Int → Prop :=
fun worst code e.ran? e.worst e.code =>
  (e.ran? = true ∧ e.worst = worst) ∧ check.exit.assumes e.ran? e.worst e.code ∧ check.exit.reqs e.ran? e.worst e.code
-/
#guard_msgs in
#print check.always_runs.inst.e

-- A constant is a definition of its type; a global expectation is a
-- proposition over its binders' variables. Only Lean code uses `FAILED`,
-- which `dead_code` does not see.
set_option fren.lint.dead_code "allow" in
const FAILED: Int := 2 - 1

/-- info: @[reducible] def check.FAILED : Int :=
2 - 1 -/
#guard_msgs in
#print check.FAILED

expect deterministic: forall (a b: exit),
  when a.ran? = b.ran? and a.worst = b.worst, a.code = b.code

/--
info: @[reducible] def check.deterministic : Prop :=
∀ (a.ran? : Bool) (a.worst : check.Verdict) (a.code : Int) (b.ran? : Bool) (b.worst : check.Verdict) (b.code : Int),
  (check.exit.assumes a.ran? a.worst a.code ∧ check.exit.reqs a.ran? a.worst a.code) ∧
      check.exit.assumes b.ran? b.worst b.code ∧ check.exit.reqs b.ran? b.worst b.code →
    a.ran? = b.ran? ∧ a.worst = b.worst → a.code = b.code
-/
#guard_msgs in
#print check.deterministic

-- The definition reduces to the value.
example : check.FAILED = 1 := by decide

/-- info: fren: 15 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check

