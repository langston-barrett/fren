-- keep-sorted start
import FrenCli.Verdicts
import Impls.Check
import Reqs.Eval
-- keep-sorted end
open Fren.Lang

/-!
# The evaluator's decisions (`Reqs/Eval`)

The decisions in `FrenCli.Verdicts` implement the comps of `eval`: for
whatever the search and the evaluator found, the status, verdict, exit code
or confirmation is as required. Each obligation is proved by `decide`, or,
over a number of tests, by cases on whether there were any.
-/

namespace Fren.Impls

open Fren.Core (CheckKind Verdict)
open FrenCli.Eval (Status Confirmation statusOf evalExit reached testVerdict confirmation confirmedVerdict)

def toStatus : Status → eval.Status
  | .Inadmissible => .Inadmissible
  | .Violates => .Violates
  | .Meets => .Meets

instance : Fren.Finite Status := ⟨[.Inadmissible, .Violates, .Meets], by intro x; cases x <;> simp⟩

impl status_of: eval::status for (a i r : Bool) {
  assumes? := a,
  insts? := i,
  reqs? := r,
  status := toStatus (statusOf a i r),
} by
  intro a i r _
  cases a <;> cases i <;> cases r <;> decide

/-- A status as `eval::eval_exit` sees it: an unknown one is not `Meets`. -/
def toStatus? : Option Status → eval.Status
  | some s => toStatus s
  | none => .Violates

impl eval_exit_code: eval::eval_exit for (ran complete : Bool) (s : Option Status) (ef : Bool) {
  ran? := ran,
  complete? := complete,
  status := toStatus? s,
  expect_false? := ef,
  code := (evalExit ran complete s ef).toNat,
} by
  intro ran complete s ef _
  cases ran <;> cases complete <;> cases ef <;> rcases s with _ | _ | _ | _ <;> decide

impl reaches_check: eval::reaches for (f h t : Bool) {
  found? := f,
  has_trigger? := h,
  trigger? := t,
  reached? := reached f h t,
} by
  intro f h t _
  cases f <;> cases h <;> cases t <;> decide

-- Over the number of tests, so `decide` does not apply: only whether
-- there were any matters.
impl test_verdict_of: eval::test_verdict for (k : CheckKind) (refuted : Bool) (n : Nat) {
  kind := toCheckKind k,
  refuted? := refuted,
  n_tests := (n : Int),
  verdict := toVerdict (testVerdict k refuted n),
} by
  intro k refuted n _
  rcases n with _ | n
  · cases k <;> cases refuted <;> decide
  · have : n + 1 > 0 := Nat.succ_pos n
    cases k <;> cases refuted <;> simp_all [fren_spec, testVerdict, toVerdict, toCheckKind] <;> first | omega | decide

def toConfirmation : Confirmation → eval.Confirmation
  | .Confirmed => .Confirmed
  | .Refuted => .Refuted
  | .Undecided => .Undecided

instance : Fren.Finite Confirmation := ⟨[.Confirmed, .Refuted, .Undecided], by intro x; cases x <;> simp⟩

impl confirm_model: eval::confirm for (h g a : Bool) {
  hyp_false? := h,
  goal_true? := g,
  all_known? := a,
  result := toConfirmation (confirmation h g a),
} by
  intro h g a _
  cases h <;> cases g <;> cases a <;> decide

impl confirmed: eval::confirmed_verdict for (v : Verdict) (c : Confirmation) {
  solver := toVerdict v,
  result := toConfirmation c,
  verdict := toVerdict (confirmedVerdict v c),
} by
  intro v c _
  cases v <;> cases c <;> decide

trusted eval::sound: "a counterexample from testing is a behaviour that the evaluator found to meet the component and to falsify the check, so it is genuine if the evaluator is right; `fren check` passes such a check only on an `Unsat` answer, which comes with no model to confirm, so this rests on the solver and Fren's translation being sound on `Unsat`, which is trusted, not checked"

end Fren.Impls
