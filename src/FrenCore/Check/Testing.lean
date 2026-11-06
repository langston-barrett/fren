-- keep-sorted start
import FrenCore.Check.ReportFormat
-- keep-sorted end

/-!
# Testing messages and check summaries

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- The help of a warning from testing: from `fren check`, testing a check
set to testing, running `fren check` would not help (`Reqs/Check#checking-by-testing`). -/
def testingHelp (byCheck : Bool) (decide : String) : String :=
  if byCheck then "help: raise `--tests`; the checks set to random testing are not asked of the solver"
  else s!"help: run `fren check` to {decide}, or raise `--tests`"

/-- Testing found no outputs for an admissible input (`eval::test_verdict`). -/
def noOutputsMsg (subject : String) (input : Assignment) (byCheck : Bool := false) : Msg :=
  { code? := some "F0609", headline := s!"testing found no outputs of {subject} for the input {showAssignment input}"
    label? := some "possibly not realizable"
    notes := #["note: the search tries only some values, so outputs may still exist",
      if byCheck then testingHelp true "" else "help: run `fren check` to decide whether it is realizable"] }

/-- No test reached a procedure's checks (`eval::test_verdict`). -/
def untestedMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0610", headline := s!"testing found no admissible behaviour of {subject} in {tests} tests"
    label? := some "untested"
    notes := #["note: so none of its checks were tested",
      testingHelp byCheck "decide whether its assumptions and guarantees can hold"] }

/-- Testing found admissible behaviours, but none in which a check's
trigger held (`eval::reaches`). -/
def untriggeredMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0612", headline := s!"testing never reached {subject} in {tests} tests: its trigger held in none of them"
    label? := some "never held"
    notes := #["note: where the trigger is false the constraint holds by its trigger alone, so those tests say nothing about it",
      testingHelp byCheck "decide it"] }

/-- Testing found what a check is about, with its trigger, if any, not
false, and in some of those tests the trigger held, but the check had no
value in any of them (`eval::unreached`). -/
def valuelessMsg (subject : String) (tests : Nat) (byCheck : Bool := false) (hasTrigger : Bool := false) : Msg :=
  { code? := some "F0617", headline := s!"testing never reached {subject} in {tests} tests: it had no value in any of them{if hasTrigger then " in which its trigger held" else ""}"
    label? := some "no value"
    notes := #["note: where an index is out of range, a function has no value that the evaluator knows, no case of a table or `match` is taken, or evaluation runs out of fuel, the check has no value, so the test says nothing about it",
      if byCheck then "help: guard the part that has no value, or set `fren.evidence` to `\"solver\"` to have the solver check it"
      else "help: run `fren check` to decide it, or guard the part that has no value"] }

/-- Testing found what a check is about, but its trigger had no value in
every one of those tests in which it was not false (`eval::unreached`). -/
def triggerValuelessMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0617", headline := s!"testing never reached {subject} in {tests} tests: its trigger had no value in any of them in which it was not false"
    label? := some "no value"
    notes := #["note: where an index is out of range, a function has no value that the evaluator knows, no case of a table or `match` is taken, or evaluation runs out of fuel, the trigger has no value, so it does not hold, and the test says nothing about the check",
      if byCheck then "help: guard the part of the trigger that has no value, or set `fren.evidence` to `\"solver\"` to have the solver check it"
      else "help: run `fren check` to decide it, or guard the part of the trigger that has no value"] }

/-- Testing found admissible behaviours, but none in which a cover goal
held (`Reqs/Eval#fren-quickcheck`). -/
def unwitnessedMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0616", headline := s!"testing found no behaviour in which cover goal {subject} holds in {tests} tests"
    label? := some "no witness found"
    notes := #["note: the search tries only some values, so such a behaviour may still exist",
      testingHelp byCheck "decide whether it can be met"] }

/-- The severity of the summary of a run (`view::summary`): always
information, whatever the results. -/
def summarySeverity (_results : Array CheckResult) : Severity := .info

/-- Which count of the summary a result is in (`view::counted`). -/
inductive Bucket where
  | passed
  | failed
  | inconclusive
  | redundant
  deriving Inhabited, BEq, DecidableEq, Repr

def bucketOf (kind : CheckKind) (verdict : Verdict) : Bucket :=
  if kind == .redundancy && verdict == .fail then .redundant
  else match verdict with
    | .pass => .passed
    | .fail => .failed
    | .inconclusive => .inconclusive

/-- Whether a result is a redundant constraint, counted apart from other
failures, which are errors (`view::summary`). -/
def CheckResult.isRedundant (r : CheckResult) : Bool := bucketOf r.kind r.verdict == .redundant

/-- What both front ends say instead of checking, after a static error
(`Reqs/View#static-errors`). It does not count them: the `fren` command
stops at a parse error, where Lean goes on and may find more. -/
def couldNotHeadline (what := "check") : String :=
  s!"could not {what} due to previous errors"

def summary (results : Array CheckResult) (byTesting : Nat := 0) (byBound : Nat := 0) : String :=
  let count (b : Bucket) := (results.filter fun r => bucketOf r.kind r.verdict == b).size
  let parts := (if byTesting == 0 then [] else [s!"{byTesting} by random testing"])
    ++ (if byBound == 0 then [] else [s!"{byBound} by bounded enumeration"])
  let tested := if parts.isEmpty then "" else s!" ({", ".intercalate parts})"
  s!"fren: {count .passed} passed{tested}, {count .failed} failed, {count .inconclusive} inconclusive, \
    {count .redundant} redundant"

end Fren.Core
