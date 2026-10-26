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

/-- Whether a test that found what a check is about reaches it
(`eval::reaches`). -/
def reached (found hasTrigger trigger : Bool) : Bool := found && (!hasTrigger || trigger)

/-- The verdict of testing a check, from whether some test refuted it and
how many reached it (`eval::test_verdict`). -/
def testVerdict (kind : CheckKind) (refuted : Bool) (tests : Nat) : Verdict :=
  if refuted then (if kind == .realizable then .inconclusive else .fail)
  else if tests > 0 then .pass else .inconclusive

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

end FrenCli.Eval
