-- keep-sorted start
import FrenCli.Quick
-- keep-sorted end

/-! A test in which a check has no value, as where its evaluation runs out
of fuel (`outOfFuel`) or reads a part that has no value, counts toward no
tested pass (`eval::reaches`): it neither refutes nor reaches the check,
so that testing leaves the check inconclusive, and it is counted apart, for
the warning `F0617` (`eval::unreached`). At a tiny fuel, a check that full
fuel evaluates has no value. The fixtures `test/cli/results/f0617_*` show
the same, end to end, for a part with no value, at each kind of check. -/

namespace Fren.Test.OutOfFuel

open FrenCli.Eval

/-- `not not not not true`, which needs five units of fuel. -/
def deep : Atom := { label := `deep, pfx := .anonymous, e := (List.range 4).foldl (fun e _ => .not e) (.lit (.bool true)) }

def cex : Unit → Fren.Core.Detail := fun _ => .none

-- A value, a test, a pass; or, refuted, a failure.
#guard deep.eval {} (fun _ => none) == some true
#guard (({} : Tally).test false (some true) (some true) cex).tests == 1
#guard verdictOf .expect (({} : Tally).test false (some true) (some true) cex) == .pass
#guard verdictOf .expect (({} : Tally).test false (some true) (some false) cex) == .fail
-- No value: no test, so no pass, and a test without a value.
#guard (({} : Tally).test false (some true) none cex).tests == 0
#guard (({} : Tally).test false (some true) none cex).valueless == 1
#guard verdictOf .expect (({} : Tally).test false (some true) none cex) == .inconclusive
#guard (({} : Tally).test false (some true) none cex).unreached 1 == .Valueless
-- Nor where the trigger fails, whatever the value.
#guard (({} : Tally).test true (some false) (some false) cex).tests == 0
#guard (({} : Tally).test true (some false) none cex).valueless == 0
#guard (({} : Tally).test true (some false) none cex).unreached 1 == .Untriggered
-- A trigger without a value does not hold, but it is not false either:
-- the test is counted as one without a value, whatever the check's.
#guard (({} : Tally).test true none (some true) cex).tests == 0
#guard (({} : Tally).test true none (some false) cex).refuted?.isNone
#guard (({} : Tally).test true none (some true) cex).valueless == 1
#guard (({} : Tally).test true none (some true) cex).unknownTrigger == 1
-- `F0617` at the trigger, which is what had no value.
#guard (({} : Tally).test true none none cex).unreached 1 == .TriggerValueless
-- One false trigger and one without a value: `F0617` at the trigger, not `F0612`.
#guard ((({} : Tally).test true (some false) none cex).test true none none cex).unreached 2 == .TriggerValueless
-- A trigger that held once, with the check without a value: `F0617` at the check.
#guard ((({} : Tally).test true none none cex).test true (some true) none cex).unreached 2 == .Valueless

/-- At a tiny fuel, read at run time so that the evaluation is not done
ahead: `deep` has no value, and a test of it neither refutes nor reaches
it, so testing leaves it inconclusive. It panics, so it runs in a process
of its own, without `LEAN_ABORT_ON_PANIC` (`panicGuard` in
`FrenTestMain`). -/
def tinyFuel : IO (Array String) := do
  let fuel := (← IO.monoMsNow) % 1 + 3
  let value := deep.eval {} (fun _ => none) fuel
  unless value.isNone do return #[s!"`deep` has the value {value} at fuel {fuel}"]
  let t := ({} : Tally).test false (some true) value cex
  unless t.tests == 0 && t.valueless == 1 && verdictOf .expect t == .inconclusive do
    return #["a test that ran out of fuel counted toward a pass"]
  return #[]

end Fren.Test.OutOfFuel
