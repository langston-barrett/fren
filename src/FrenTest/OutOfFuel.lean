-- keep-sorted start
import FrenCli.Quick
-- keep-sorted end

/-! A test in which a check has no value, as where its evaluation runs out
of fuel (`outOfFuel`) or reads a part that has no value, counts toward no
tested pass (`eval::reaches`): it neither refutes nor reaches the check,
so that testing leaves the check inconclusive, and it is counted apart, for
the warning `F0617` (`eval::unreached`). At a tiny fuel, a check that full
fuel evaluates has no value. Fuel is counted in steps of the semantics,
applications of a structural recursion (`Reqs/Eval#fuel`), so how deeply
the expression around them is nested, and whether the recursion's body is
compiled (`Spec.withCompiledRecs`), do not change which evaluations run
out, nor do the quantifiers and `match`es around them; checking that a
value is of a subset type spends one unit for each invariant. The
fixtures `test/cli/results/f0617_*` show the same, end to end, for a part
with no value, at each kind of check. -/

namespace Fren.Test.OutOfFuel

open FrenCli.Eval

/-- `e` within `n` negations. -/
def nots (n : Nat) (e : Ex) : Ex := (List.range n).foldl (fun e _ => .not e) e

/-- The body of `down(n) := if n <= 0 then true else down(n - 1)`, with
the application within `2 * k` negations, which do not change its value. -/
def downBody (k : Nat) : Ex :=
  .ite (.bin .le (.bound `n) (.lit (.int 0))) (.lit (.bool true))
    (nots (2 * k) (.app `down #[.bin .sub (.bound `n) (.lit (.int 1))]))

/-- `down` with the body `downBody k`, compiled or not. -/
def downInterp (k : Nat) (compiled : Bool) : Interp :=
  let sp : Spec := { recDefs := ({} : Lean.NameMap _).insert `down (#[`n], downBody k) }
  let sp := if compiled then sp.withCompiledRecs fun _ => none else sp
  { recDefs := sp.recDefs.find? }

/-- `down(3)` within 64 negations: it applies `down` four times, one
within another, so it needs four units of fuel, however deeply it, or
`down`'s body, is nested. -/
def deep : Atom := { label := `deep, pfx := .anonymous, e := nots 64 (.app `down #[.lit (.int 3)]) }

/-- Each way of evaluating `deep` whose step count must not differ:
`down`'s body nested shallowly or deeply, compiled or not. -/
def interps : List Interp := [downInterp 0 false, downInterp 0 true, downInterp 500 false, downInterp 500 true]

/-- `down(3)` within 32 negations, within a `match` on a quantifier's
bound name, within 32 more: neither the quantifier nor the `match`
spends fuel, so it needs four units, as `deep` does. -/
def throughBinders : Atom :=
  let arm : Pat × Option Ex × Ex := (.wild, none, nots 32 (.app `down #[.lit (.int 3)]))
  let body : Ex := .match (.bound `i) #[arm] 0 #[0] none none
  let dom : Ex := .seqLit #[.lit (.int 1), .lit (.int 2)]
  { label := `throughBinders, pfx := .anonymous
    e := nots 32 (.quant 0 0 true #[`i] #[some dom] #[{ ty := .int }] body) }

/-- The subset types of the integers `Pos`, whose invariant is
`pos?(x) := x > 0`, and `Down`, whose invariant is `down?(x) := down(x)`. -/
def posTy : Fren.Core.PTy := { ty := .int, invariants := #[{ name := `pos, predicate := `pos? }] }
def downTy : Fren.Core.PTy := { ty := .int, invariants := #[{ name := `down, predicate := `down? }] }

/-- `I`, with the definitions of `pos?` and `down?`. -/
def withInvariants (I : Interp) : Interp :=
  { I with defs := fun f =>
      if f == `pos? then some (#[`x], .bin .gt (.bound `x) (.lit (.int 0)), .bool)
      else if f == `down? then some (#[`x], .app `down #[.bound `x], .bool) else none }

/-- That `5` is a `Pos`: checking the invariant is one step, so it needs
one unit of fuel. -/
def positive : Atom := { label := `positive, pfx := .anonymous, e := .typed posTy #[] (.lit (.int 5)) }

/-- That `3` is a `Down`: one step for the invariant, whose body reads
`down` at one unit less, and four for `down(3)`, so it needs five. -/
def downward : Atom := { label := `downward, pfx := .anonymous, e := .typed downTy #[] (.lit (.int 3)) }

def cex : Unit → Fren.Core.Detail := fun _ => .none

/-- Why testing reached the check of `t`, or did not (`eval::unreached`),
where `found` tests found what it is about: `unreachedOf` of its counts,
as `Tally.warning` reads them. -/
def unreached (t : Tally) (found : Nat) : Unreached :=
  unreachedOf found (t.tests + t.valueless) t.unknownTrigger t.tests

-- A value, a test, a pass; or, refuted, a failure.
#guard interps.all fun I => deep.eval I (fun _ => none) == some true
#guard interps.all fun I => deep.eval I (fun _ => none) 4 == some true
#guard interps.all fun I => throughBinders.eval I (fun _ => none) 4 == some true
#guard positive.eval (withInvariants {}) (fun _ => none) 1 == some true
#guard interps.all fun I => downward.eval (withInvariants I) (fun _ => none) 5 == some true
#guard (({} : Tally).test false (some true) (some true) cex).tests == 1
#guard verdictOf .expect (({} : Tally).test false (some true) (some true) cex) == .pass
#guard verdictOf .expect (({} : Tally).test false (some true) (some false) cex) == .fail
-- No value: no test, so no pass, and a test without a value.
#guard (({} : Tally).test false (some true) none cex).tests == 0
#guard (({} : Tally).test false (some true) none cex).valueless == 1
#guard verdictOf .expect (({} : Tally).test false (some true) none cex) == .inconclusive
#guard unreached (({} : Tally).test false (some true) none cex) 1 == .Valueless
-- Nor where the trigger fails, whatever the value.
#guard (({} : Tally).test true (some false) (some false) cex).tests == 0
#guard (({} : Tally).test true (some false) none cex).valueless == 0
#guard unreached (({} : Tally).test true (some false) none cex) 1 == .Untriggered
-- A trigger without a value does not hold, but it is not false either:
-- the test is counted as one without a value, whatever the check's.
#guard (({} : Tally).test true none (some true) cex).tests == 0
#guard (({} : Tally).test true none (some false) cex).refuted?.isNone
#guard (({} : Tally).test true none (some true) cex).valueless == 1
#guard (({} : Tally).test true none (some true) cex).unknownTrigger == 1
-- `F0617` at the trigger, which is what had no value.
#guard unreached (({} : Tally).test true none none cex) 1 == .TriggerValueless
-- One false trigger and one without a value: `F0617` at the trigger, not `F0612`.
#guard unreached ((({} : Tally).test true (some false) none cex).test true none none cex) 2 == .TriggerValueless
-- The check as a whole had a value where its trigger had none but it held.
#guard (({} : Tally).test true none (some true) cex).valued == 1
#guard (({} : Tally).test true none none cex).valued == 0
-- A trigger that held once, with the check without a value: `F0617` at the check.
#guard unreached ((({} : Tally).test true none none cex).test true (some true) none cex) 2 == .Valueless

/-- At a tiny fuel, read at run time so that the evaluation is not done
ahead: with one unit too few, `deep` has no value, in each of `interps`,
and a test of it neither refutes nor reaches it, so testing leaves it
inconclusive. With one unit too few, `throughBinders`, `positive` and
`downward` have no value either. It panics, so it runs in a process of
its own, without `LEAN_ABORT_ON_PANIC` (`panicGuard` in `FrenTestMain`). -/
def tinyFuel : IO (Array String) := do
  let fuel := (← IO.monoMsNow) % 1 + 3
  let mut failures := #[]
  for I in interps do
    let value := deep.eval I (fun _ => none) fuel
    unless value.isNone do failures := failures.push s!"`deep` has the value {value} at fuel {fuel}"
    let t := ({} : Tally).test false (some true) value cex
    unless t.tests == 0 && t.valueless == 1 && verdictOf .expect t == .inconclusive do
      failures := failures.push "a test that ran out of fuel counted toward a pass"
    let value := throughBinders.eval I (fun _ => none) fuel
    unless value.isNone do failures := failures.push s!"`throughBinders` has the value {value} at fuel {fuel}"
    let value := downward.eval (withInvariants I) (fun _ => none) (fuel + 1)
    unless value.isNone do failures := failures.push s!"`downward` has the value {value} at fuel {fuel + 1}"
  let value := positive.eval (withInvariants {}) (fun _ => none) (fuel - 3)
  unless value.isNone do failures := failures.push s!"`positive` has the value {value} at fuel {fuel - 3}"
  return failures

end Fren.Test.OutOfFuel
