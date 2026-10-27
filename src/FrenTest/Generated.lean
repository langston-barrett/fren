-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang


-- Lean-only behaviour that ui tests can't express: Fren's keywords are scoped
-- to `Fren.Lang`, and generated declarations are ordinary Lean definitions.
mod check

pub enum Verdict { Pass, Fail, Inconclusive }

use self::Verdict::{Pass, Fail, Inconclusive}

pub proc exit(ran?, worst: Verdict): (code: Int) {
  ensure not_run: unless ran?, code = 2
  ensure failed: when ran? and worst = Fail, code = 1
  ensure inconclusive: when ran? and worst = Inconclusive, code = 3
  ensure passed: when ran? and worst = Pass, code = 0

  expect zero_means_pass: when code = 0, ran? and worst = Pass
}

-- Generated declarations are ordinary Lean definitions.
/--
info: @[reducible] def Fren.Generated.check.exit.ensure.failed : Bool → check.Verdict → Int → Prop :=
fun ran? worst code => ran? = true ∧ worst = check.Verdict.Fail → code = 1
-/
#guard_msgs in
#print check.exit.ensure.failed

/--
info: @[reducible] def Fren.Generated.check.exit.ensures : Bool → check.Verdict → Int → Prop :=
fun ran? worst code =>
  check.exit.ensure.not_run ran? worst code ∧
    check.exit.ensure.failed ran? worst code ∧
      check.exit.ensure.inconclusive ran? worst code ∧ check.exit.ensure.passed ran? worst code
-/
#guard_msgs in
#print check.exit.ensures

/-- info: @[reducible] def Fren.Generated.check.exit.assumes : Bool → check.Verdict → Int → Prop :=
fun ran? worst code => True -/
#guard_msgs in
#print check.exit.assumes

-- An instance's variables follow the comp's own, named `w.x`.
proc always_runs(worst: Verdict): (code: Int) {
  call e := exit(true, worst)

  ensure same: code = e.code
}

/--
info: @[reducible] def Fren.Generated.check.always_runs.call.e : check.Verdict → Int → Bool → check.Verdict → Int → Prop :=
fun worst code e.ran? e.worst e.code =>
  (e.ran? = true ∧ e.worst = worst) ∧
    check.exit.assumes e.ran? e.worst e.code ∧ check.exit.ensures e.ran? e.worst e.code
-/
#guard_msgs in
#print check.always_runs.call.e

-- A constant is a definition of its type; a global expectation's
-- expectation is a proposition over its parameters and calls' variables, as
-- a procedure's is. Only Lean code uses `FAILED`,
-- which `dead_code` does not see.
set_option fren.lint.dead_code "allow" in
const FAILED: Int := 2 - 1

/-- info: @[reducible] def Fren.Generated.check.FAILED : Int :=
2 - 1 -/
#guard_msgs in
#print check.FAILED

expect deterministic(a_ran?, a_worst: Verdict, b_ran?, b_worst: Verdict) {
  call a := exit(a_ran?, a_worst)
  call b := exit(b_ran?, b_worst)
  expect deterministic: when a.ran? = b.ran? and a.worst = b.worst, a.code = b.code
}

/--
info: @[reducible] def Fren.Generated.check.deterministic.expect.deterministic : Bool →
  check.Verdict → Bool → check.Verdict → Bool → check.Verdict → Int → Bool → check.Verdict → Int → Prop :=
fun a_ran? a_worst b_ran? b_worst a.ran? a.worst a.code b.ran? b.worst b.code =>
  a.ran? = b.ran? ∧ a.worst = b.worst → a.code = b.code
-/
#guard_msgs in
#print check.deterministic.expect.deterministic

-- The definition reduces to the value.
example : check.FAILED = 1 := by decide

-- `div` and `mod` are Lean's `/` and `%` on `Int`, by the divisor's value as
-- a numeral, and the methods of `Int` are conditionals.
const STRIDE: Int := 2 * 2

proc arith(x: Int, y: Int): (q: Int, r: Int, a: Int) {
  ensure quotient: q = x div -STRIDE
  ensure remainder: r = x mod 3
  ensure absolute: a = (x - y).abs.min(y.max(0))
}

/--
info: @[reducible] def Fren.Generated.check.arith.ensure.quotient : Int → Int → Int → Int → Int → Prop :=
fun x y q r a => q = -(x / 4)
-/
#guard_msgs in
#print check.arith.ensure.quotient

/--
info: @[reducible] def Fren.Generated.check.arith.ensure.absolute : Int → Int → Int → Int → Int → Prop :=
fun x y q r a =>
  a =
    if (if x - y < 0 then -(x - y) else x - y) ≤ if y ≥ 0 then y else 0 then if x - y < 0 then -(x - y) else x - y
    else if y ≥ 0 then y else 0
-/
#guard_msgs in
#print check.arith.ensure.absolute

-- Euclidean, as in SMT-LIB, so that a negative divisor is a negated
-- quotient, or the same remainder, by a numeral.
example : (-7 : Int) / 2 = -4 ∧ (-7 : Int) % 2 = 1 ∧ (7 : Int) / -2 = -3 ∧ (7 : Int) % -2 = 1 := by decide
example (x : Int) (k : Nat) : x / -(k : Int) = -(x / k) ∧ x % -(k : Int) = x % k :=
  ⟨Int.ediv_neg x k, Int.emod_neg x k⟩

-- A chained comparison, which Lean does not have, is the conjunction of
-- its comparisons, with the same term for each operand between two. On
-- strings, `>` is written as `Fren.Str.lt` with its operands swapped.
proc ranged(i: Int, n: Int, s: String): (inside?, lower?) {
  ensure inside: inside? iff 0 <= i < n <= 10
  ensure lower: lower? iff "z" > s >= "a"
}

/--
info: @[reducible] def Fren.Generated.check.ranged.ensure.inside : Int → Int → String → Bool → Bool → Prop :=
fun i n s inside? lower? => inside? = true ↔ (0 ≤ i ∧ i < n) ∧ n ≤ 10
-/
#guard_msgs in
#print check.ranged.ensure.inside

/--
info: @[reducible] def Fren.Generated.check.ranged.ensure.lower : Int → Int → String → Bool → Bool → Prop :=
fun i n s inside? lower? => lower? = true ↔ Fren.Str.lt s (Fren.Str.lit "z") ∧ Fren.Str.le (Fren.Str.lit "a") s
-/
#guard_msgs in
#print check.ranged.ensure.lower

-- An ordered enumeration's values compare by their positions, which are
-- conditionals on its variants, as the `fren` command writes them, and
-- `min` and `max` are conditionals on the positions.
pub ordered enum Level { Low, Middle, High }

proc leveled(a: Level, b: Level): (above?, top: Level) {
  ensure above: above? iff Level::Low < a <= b
  ensure highest: top = a.max(b)
}

/--
info: @[reducible] def Fren.Generated.check.leveled.ensure.above : check.Level → check.Level → Bool → check.Level → Prop :=
fun a b above? top =>
  above? = true ↔
    ((if check.Level.Low = check.Level.Low then 0 else if check.Level.Low = check.Level.Middle then 1 else 2) <
        if a = check.Level.Low then 0 else if a = check.Level.Middle then 1 else 2) ∧
      (if a = check.Level.Low then 0 else if a = check.Level.Middle then 1 else 2) ≤
        if b = check.Level.Low then 0 else if b = check.Level.Middle then 1 else 2
-/
#guard_msgs in
#print check.leveled.ensure.above

/--
info: @[reducible] def Fren.Generated.check.leveled.ensure.highest : check.Level → check.Level → Bool → check.Level → Prop :=
fun a b above? top =>
  top =
    if
        (if a = check.Level.Low then 0 else if a = check.Level.Middle then 1 else 2) ≥
          if b = check.Level.Low then 0 else if b = check.Level.Middle then 1 else 2 then
      a
    else b
-/
#guard_msgs in
#print check.leveled.ensure.highest

-- The positions are the constructors' indices, so both front ends order
-- the variants as they are declared.
example (l : check.Level) :
    (if l = .Low then (0 : Int) else if l = .Middle then 1 else 2) = l.ctorIdx := by
  cases l <;> rfl

/-- info: fren: 25 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check

