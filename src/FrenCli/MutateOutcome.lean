-- keep-sorted start
import FrenCli.Exit
-- keep-sorted end

/-!
# What becomes of a mutant (`Reqs/Mutate#killing-mutants`)

The decisions of `fren mutate`, apart from the checks themselves, so that
`Impls` can link them to their requirements without the solver.
-/

namespace FrenCli.Mutate

open Fren.Core (Verdict)

/-- What became of a mutant (`mutate::Outcome`). -/
inductive Outcome where
  | killed
  | survived
  | equivalent
  | unviable
  deriving BEq, Inhabited, Repr

/-- A check kills a mutant when it passes on the spec and fails on the
mutant (`mutate::kill`). -/
def killsCheck (before after : Verdict) : Bool := before == .pass && after == .fail

/-- A mutant's outcome (`mutate::outcome`): `viable` if it has no static
errors, `killed` if some check kills it, and `equivalent` if the solver
shows that it means what the spec means. -/
def outcome (viable killed equivalent : Bool) : Outcome :=
  if !viable then .unviable else if killed then .killed else if equivalent then .equivalent else .survived

/-- With `--by both`, testing misses a mutant that the solver's checks kill
(`mutate::missed`). -/
def missed (bySolver byTesting : Bool) : Bool := bySolver && !byTesting

/-- The exit code of `fren mutate` (`mutate::exit`), given whether it ran,
whether some mutant survived or was missed, and whether some internal
error was reported. -/
def exitCode (ran survived internal : Bool) : UInt32 :=
  FrenCli.exitCode ran (if internal then some .error else if survived then some .warning else none)

end FrenCli.Mutate
