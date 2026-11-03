-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Asking a query again (`Reqs/Models#asking-again`)

`Fren.Core.askedAgain` with stand-ins for confirmation and for the query
asked again, so that the rule is tested whatever the solver's models are:
`test/ui/checks/model_premise.fren` exercises it only while cvc5 gives that
spec a contradicted model. The state counts the queries asked again.
-/

namespace FrenTest.AskedAgain

open Lean (Name)
open Fren.Core (Outcome askedAgain)

/-- A model of one variable, `x`, at `v`. -/
def model (v : Nat) : Array (Name × Nat) := #[(`x, v)]

/-- What `askedAgain` keeps of `first`, where a model is contradicted at
`x = 0` and the query asked again answers `again`, with the number of
queries asked again. -/
def run (first again : Outcome Nat) : Option (Array (Name × Nat)) × Nat :=
  let contradicted (m : Array (Name × Nat)) : StateM Nat Bool := pure (m.any (·.2 == 0))
  let ask : StateM Nat (Outcome Nat) := do modify (· + 1); pure again
  let (o, n) := (askedAgain first contradicted (some ask)).run 0
  ((match o with | .sat m => some m | _ => none), n)

-- A model that is not contradicted: nothing is asked again.
#guard run (.sat (model 1)) (.sat (model 2)) == (some (model 1), 0)
-- A contradicted model, and a second that is not: the second is kept.
#guard run (.sat (model 0)) (.sat (model 2)) == (some (model 2), 1)
-- A contradicted second model: the first is kept, for its report.
#guard run (.sat (model 0)) (.sat (model 0)) == (some (model 0), 1)
-- A second answer that is not `Sat`, or has no model: the first is kept.
#guard run (.sat (model 0)) .unsat == (some (model 0), 1)
#guard run (.sat (model 0)) (.unknown "timeout") == (some (model 0), 1)
#guard run (.sat (model 0)) (.sat #[]) == (some (model 0), 1)
-- No model, or an answer that is not `Sat`: nothing is asked again.
#guard run (.sat #[]) (.sat (model 2)) == (some #[], 0)
#guard run .unsat (.sat (model 2)) == (none, 0)

-- A backend that cannot ask again: the first is kept.
#guard ((askedAgain (m := Id) (.sat (model 0)) (fun _ => pure true) none) matches .sat #[(`x, 0)])

/-- `askedAgainThen`'s answer, as `run`, where the evaluation of the
recursive functions does not confirm a model at `x = 2`, and the answers
evaluated. -/
def runThen (first again : Outcome Nat) : Option (Array (Name × Nat)) × Array Nat :=
  let contradicted (m : Array (Name × Nat)) : StateM (Array Nat) Bool := pure (m.any (·.2 == 0))
  let ask : StateM (Array Nat) (Outcome Nat) := pure again
  let evaluated (o : Outcome Nat) : StateM (Array Nat) (Outcome Nat) := do
    let .sat m := o | return o
    modify (·.append (m.map (·.2)))
    return if m.any (·.2 == 2) then .unknown "recursion" else o
  let (o, seen) := (Fren.Core.askedAgainThen first contradicted (some ask) evaluated).run #[]
  ((match o with | .sat m => some m | _ => none), seen)

-- The second model is not contradicted but its recursion is unconfirmed:
-- the answer is the second's evaluation, inconclusive, and the first,
-- contradicted model is never evaluated, in both front ends.
#guard runThen (.sat (model 0)) (.sat (model 2)) == (none, #[2])
-- The second model is kept, and confirmed.
#guard runThen (.sat (model 0)) (.sat (model 1)) == (some (model 1), #[1])
-- The second is not kept: the first is evaluated, and reported.
#guard runThen (.sat (model 0)) .unsat == (some (model 0), #[0])
-- Not asked again: only the first is evaluated.
#guard runThen (.sat (model 2)) (.sat (model 1)) == (none, #[2])

end FrenTest.AskedAgain
