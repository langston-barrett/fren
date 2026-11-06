-- keep-sorted start
import FrenCore.Check.Types
-- keep-sorted end

/-!
# Model confirmation and testing hooks

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-- What the truths of a query's hypotheses, in order, and of its goal, at
the values read from a model, contradict (`model::report`): the first
hypothesis that is false, or else the goal, if it is true; none if
neither. A truth that the evaluator does not know is none. -/
def contradiction? (hyps : Array (Name × Option Bool)) (goal : Option Bool) : Option Contradiction :=
  match hyps.find? (·.2 == some false) with
  | some (h, _) => some (.hypothesis h)
  | none => if goal == some true then some .goal else none

/-- Whether a model of a query contradicts a formula that applies no
recursive function, of `formulas`, each with its truth at the model and
whether it applies one, or the goal, `goal`, likewise: a bug in Fren,
which the report of the model shows (`Reqs/Models#reporting`), not
evidence about the functions' contracts. Both front ends decide it here,
over the query's own hypotheses. -/
def plainContradiction (formulas : Array (Name × Option Bool × Bool)) (goal : Option Bool × Bool) : Bool :=
  let plain (v : Option Bool × Bool) : Option Bool := if v.2 then none else v.1
  (contradiction? (formulas.map fun (n, v) => (n, plain v)) (plain goal)).isSome

/-- Whether an application's value is known in a model's confirmation,
where `args` says whether each argument's value is known, and `body`
whether the body's is at them: evaluation is strict, so not where an
argument's is unknown, even one that the body never reads
(`model::known_application`). Both front ends' evaluators decide by it. -/
def appliedKnown (args : List Bool) (body : Bool) : Bool := args.all id && body

/-- Whether an `if`'s value is known in a model's confirmation, where `cond`
is its condition's truth, `none` being unknown, `yes` and `no` say whether
its branches' values are known, and `same` whether they are equal: the
branch taken's, or, where the condition is unknown, both branches', if they
are equal (`model::known_if`). Both front ends' evaluators decide by it. -/
def iteKnown (cond : Option Bool) (yes no same : Bool) : Bool :=
  match cond with
  | some true => yes
  | some false => no
  | none => yes && no && same

/-- The truth of realizability's output goal during model confirmation
(`eval::outputs_goal`): finding legal outputs can refute the model, but
not finding any leaves the goal unknown, even over a finite carrier. -/
def outputGoalTruth : Option Bool → Option Bool
  | some true => some true
  | _ => none

/-- Set by `fren_fuzz_frontends --confirm`, which runs both front ends in
its own process, so that they misread models as `FREN_MISREAD_MODELS`
makes them (`misreadModels`). -/
initialize misreadSet : IO.Ref Bool ← IO.mkRef false

/-- Whether the readers of both front ends misread every integer of a
model that a check reports as one more than it is, a bug that the ui tests inject, with
the environment variable `FREN_MISREAD_MODELS`, to see that confirmation
catches it (`Reqs/Models#testing`), and that the fuzzer's `--confirm`
mode injects (`misreadSet`). -/
def misreadModels : BaseIO Bool := do
  return (← misreadSet.get) || (← IO.getEnv "FREN_MISREAD_MODELS").isSome

/-- Whether both front ends take the first model of every query that has
one as contradicted, and so ask every such query again (`askedAgain`):
set by the environment variable `FREN_ASK_AGAIN`, which only `fren_test`'s
`uiAskAgain` job sets, for the ui tests of `test/ui/ask_again`, so that
asking again is tested whatever models the solver gives
(`Reqs/Models#testing`). Any other run, such as the fuzzer's, has it only
where its caller sets it by hand. -/
def askAgainForced : BaseIO Bool := return (← IO.getEnv "FREN_ASK_AGAIN").isSome

end Fren.Core
