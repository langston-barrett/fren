-- keep-sorted start
import FrenCli.MutateOutcome
import Impls.Check
import Impls.Cli
import Reqs.Mutate
-- keep-sorted end
open Fren.Lang

/-!
# What becomes of a mutant (`Reqs/Mutate`)

The decisions in `FrenCli.MutateOutcome` implement the comps of `mutate`.
Each obligation is proved by `decide`, given the variables of
`mutate::exit`'s instance.
-/

namespace Fren.Impls

open FrenCli.Mutate (Outcome killsCheck outcome missed exitCode)

def toMutantOutcome : Outcome → mutate.Outcome
  | .killed => .Killed
  | .survived => .Survived
  | .equivalent => .Equivalent
  | .unviable => .Unviable

impl mutant_kill: mutate::kill for (b a : Fren.Core.Verdict) {
  before := toVerdict b,
  after := toVerdict a,
  kills? := killsCheck b a,
} by
  intro b a _
  cases b <;> cases a <;> decide

impl mutant_outcome: mutate::outcome for (v k e : Bool) {
  viable? := v,
  killed? := k,
  equivalent? := e,
  outcome := toMutantOutcome (outcome v k e),
} by
  intro v k e _
  cases v <;> cases k <;> cases e <;> decide

impl mutant_missed: mutate::missed for (s t : Bool) {
  by_solver? := s,
  by_testing? := t,
  missed? := missed s t,
} by
  intro s t _
  cases s <;> cases t <;> decide

/-- The most severe level that `exitCode` gives `cli::exit`. -/
def mutateWorst (s i : Bool) : Option Fren.Core.Severity := if i then some .error else if s then some .warning else none

-- The instance's variables are given by the code.
impl mutate_exit: mutate::exit for (r s i : Bool) {
  ran? := r,
  survived? := s,
  internal? := i,
  code := (exitCode r s i).toNat,
} by
  intro r s i _
  refine ⟨toLevel (mutateWorst s i), r, toLevel (mutateWorst s i), (FrenCli.exitCode r (mutateWorst s i)).toNat, ?_, ?_, ?_⟩ <;>
    cases r <;> cases s <;> cases i <;> decide

end Fren.Impls
