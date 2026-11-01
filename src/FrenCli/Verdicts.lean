-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# The evaluator's decisions (`Reqs/Eval`)

The decisions of `fren eval`, `fren quickcheck` and model confirmation, as
functions of what was found, apart from the search and the evaluator, so
that `Impls.Eval` can prove them against the comps of `eval`.
-/

namespace FrenCli.Eval

open Fren.Core (CheckKind Verdict)

/-- `eval::Status`. -/
inductive Status where
  | Inadmissible
  | Violates
  | Meets
  deriving BEq, DecidableEq, Repr

/-- The status of a behaviour (`eval::status`). -/
def statusOf (assumes insts reqs : Bool) : Status :=
  if !(assumes && insts) then .Inadmissible else if reqs then .Meets else .Violates

/-- The exit code of `fren eval` (`eval::eval_exit`); an unknown status is
not `Meets`. -/
def evalExit (ran complete : Bool) (status? : Option Status) (expectFalse : Bool) : UInt32 :=
  if !ran then 2 else if !complete then 3 else if status? == some .Meets && !expectFalse then 0 else 1

/-- Whether a test that found what a check is about reaches it: where the
check's trigger, if any, whose value is `trigger`, holds, and the check,
whose value is `value`, has one (`eval::reaches`). A trigger that has no
value does not hold. -/
def reached (found hasTrigger : Bool) (trigger value : Option Bool) : Bool :=
  found && (!hasTrigger || trigger == some true) && value.isSome

/-- Whether a test that found what a check is about counts toward
`unreached`'s `triggered`: its trigger, if any, whose value is `trigger`,
is not false (`eval::reaches`). -/
def counted (found hasTrigger : Bool) (trigger : Option Bool) : Bool :=
  found && (!hasTrigger || trigger != some false)

/-- Whether a test that found what a check is about found its trigger
without a value (`eval::reaches`). -/
def triggerUnknown (found hasTrigger : Bool) (trigger : Option Bool) : Bool :=
  found && hasTrigger && trigger.isNone

/-- `eval::Unreached`. -/
inductive Unreached where
  | Reached
  | Untested
  | Untriggered
  | Valueless
  | TriggerValueless
  deriving BEq, DecidableEq, Repr

/-- Why testing reached a check, or did not (`eval::unreached`), from the
tests that found what it is about, those of them in which its trigger, if
any, was not false, those of them in which the trigger had no value, and
those in which the trigger held and the check had a value. -/
def unreachedOf (found triggered unknown decided : Nat) : Unreached :=
  if decided > 0 then .Reached
  else if found == 0 then .Untested
  else if triggered == 0 then .Untriggered
  else if unknown < triggered then .Valueless
  else .TriggerValueless

/-- `eval::UnreachedWarning`. -/
inductive UnreachedWarning where
  | Silent
  | Untriggered
  | Valueless
  | TriggerValueless
  deriving BEq, DecidableEq, Repr

/-- The warning shown at a check, from the counts of `unreachedOf`
(`eval::unreached_warning`): the warning for why no test reached it, but
beside the procedure's `F0610` (`untested`), none but that of an
assumption that had no value as a whole in any test (`valued` is the
tests in which it had one). -/
def unreachedWarning (found triggered unknown decided valued : Nat) (untested assumption : Bool) : UnreachedWarning :=
  let explains := assumption && valued == 0
  match unreachedOf found triggered unknown decided with
  | .Untriggered => if untested then .Silent else .Untriggered
  | .Valueless => if untested && !explains then .Silent else .Valueless
  | .TriggerValueless => if untested && !explains then .Silent else .TriggerValueless
  | _ => .Silent

/-- The verdict of testing a check, from whether some test refuted it, how
many reached it, and, for realizability, whether the search saw every
output of the input that refuted it (`eval::test_verdict`). -/
def testVerdict (kind : CheckKind) (refuted : Bool) (tests : Nat) (exhausted : Bool := false) : Verdict :=
  if refuted then (if kind == .realizable && !exhausted then .inconclusive else .fail)
  else if tests > 0 then .pass else .inconclusive

/-- What one assignment of a procedure's outputs makes of its constraints
(`eval::Assigned`): some is `false`; none is, and every one has a value;
or a definition, or a constraint that no other rules out, has no value. -/
inductive Assigned where
  | Ruled
  | Satisfied
  | Undefined
  deriving BEq, DecidableEq, Repr

/-- Whether the search saw every output of an input (`eval::outputs_seen`):
each output without a definition has finitely many values, `sizes`, all of
which the search tries, there are `count` assignments of them, at most
`limit`, and each is ruled out, `assignments`. -/
def outputsSeen (sizes : Array (Option Nat)) (count : Nat) (assignments : Array Assigned) (limit : Nat := 4096) :
    Bool :=
  sizes.all (·.isSome) && count ≤ limit && assignments.size == count && assignments.all (· == .Ruled)

/-- `eval::Confirmation`. -/
inductive Confirmation where
  | Confirmed
  | Refuted
  | Undecided
  deriving BEq, DecidableEq, Repr

/-- Whether a model confirms its answer (`eval::confirm`). -/
def confirmation (hypFalse goalTrue allKnown : Bool) : Confirmation :=
  if hypFalse || goalTrue then .Refuted else if allKnown then .Confirmed else .Undecided

/-- A check's verdict, given the least confirmed of its models
(`eval::confirmed_verdict`). -/
def confirmedVerdict (solver : Verdict) (result : Confirmation) : Verdict :=
  if result == .Refuted then .inconclusive else solver

/-! ## Backjumping

A search's *conflict set*, for a variable that has run out of candidates,
is the set of the variables before it whose values its failure depends on
(`Reqs/Eval#backjumping`). It is a `Nat` whose bit `j` is set when the
variable at position `j` of those that the search chooses is in it. -/

/-- The conflict set of the variable at position `i` of those that the
search chooses, when it has run out of candidates (`eval::conflict`):
`equated` is the set of the variables that the expressions it is equated
with read, and `rejections` are, for each candidate it tried, the set of
the variables that what rejected the candidate reads. Only the variables
before it are kept. -/
def conflictOf (i : Nat) (equated : Nat) (rejections : List Nat) : Nat :=
  rejections.foldl (· ||| ·) equated % 2 ^ i

/-- Whether the search, going back from a variable that has run out of
candidates with the conflict set `c`, resumes at the variable at position
`k`, trying its next candidate (`eval::backjump`): `k` is the last member
of `c`. The search goes back past every variable after it without trying
their other candidates, and, if `c` is empty, fails. -/
def resumesAt (c k : Nat) : Bool := c.testBit k && c < 2 ^ (k + 1)

/-! Both as they run: `2 ^ i` is computed with big integers, `1 <<< i`
by a shift, and they are equal (`Nat.one_shiftLeft`). -/

def conflictOfImpl (i : Nat) (equated : Nat) (rejections : List Nat) : Nat :=
  rejections.foldl (· ||| ·) equated % (1 <<< i)

@[csimp] theorem conflictOf_eq_impl : @conflictOf = @conflictOfImpl := by
  funext i equated rejections
  simp [conflictOf, conflictOfImpl, Nat.one_shiftLeft]

def resumesAtImpl (c k : Nat) : Bool := c.testBit k && c < 1 <<< (k + 1)

@[csimp] theorem resumesAt_eq_impl : @resumesAt = @resumesAtImpl := by
  funext c k
  simp [resumesAt, resumesAtImpl, Nat.one_shiftLeft]

end FrenCli.Eval
