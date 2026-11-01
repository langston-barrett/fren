-- keep-sorted start
import FrenCli.Quick
-- keep-sorted end

/-! A test whose evaluation runs out of fuel (`outOfFuel`) counts toward no
tested pass (`eval::reaches`): at a tiny fuel, a check that full fuel
evaluates has no value, and the test neither refutes nor reaches it, so
that testing leaves the check inconclusive. -/

namespace Fren.Test.OutOfFuel

open FrenCli.Eval

/-- `not not not not true`, which needs five units of fuel. -/
def deep : Atom := { label := `deep, pfx := .anonymous, e := (List.range 4).foldl (fun e _ => .not e) (.lit (.bool true)) }

def cex : Unit → Fren.Core.Detail := fun _ => .none

-- A value, a test, a pass; or, refuted, a failure.
#guard deep.eval {} (fun _ => none) == some true
#guard (({} : Tally).test false true (some true) cex).tests == 1
#guard verdictOf .expect (({} : Tally).test false true (some true) cex) == .pass
#guard verdictOf .expect (({} : Tally).test false true (some false) cex) == .fail
-- No value: no test, so no pass.
#guard (({} : Tally).test false true none cex).tests == 0
#guard verdictOf .expect (({} : Tally).test false true none cex) == .inconclusive
-- Nor where the trigger fails, whatever the value.
#guard (({} : Tally).test true false (some false) cex).tests == 0

/-- At a tiny fuel, read at run time so that the evaluation is not done
ahead: `deep` has no value, and a test of it neither refutes nor reaches
it, so testing leaves it inconclusive. It panics, so it runs in a process
of its own, without `LEAN_ABORT_ON_PANIC` (`panicGuard` in
`FrenTestMain`). -/
def tinyFuel : IO (Array String) := do
  let fuel := (← IO.monoMsNow) % 1 + 3
  let value := deep.eval {} (fun _ => none) fuel
  unless value.isNone do return #[s!"`deep` has the value {value} at fuel {fuel}"]
  let t := ({} : Tally).test false true value cex
  unless t.tests == 0 && verdictOf .expect t == .inconclusive do
    return #["a test that ran out of fuel counted toward a pass"]
  return #[]

end Fren.Test.OutOfFuel
