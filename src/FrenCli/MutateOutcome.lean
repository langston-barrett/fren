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

/-- Whether a mutant's checks of an item run again, given the item's
fingerprint `fp` in the spec and `fp'` in the mutant
(`Reqs/Mutate#killing-mutants`, `mutate::skip`): only if the mutant changes
what they read. -/
def rechecks (fp fp' : String) : Bool := fp != fp'

/-- Combines the answers to whether parts are equivalent: `some false` if
some part differs, `none` if some part is unknown, else `some true`. -/
def both (a b : Option Bool) : Option Bool :=
  if a == some false || b == some false then some false else if a.isNone || b.isNone then none else some true

/-- The mutants of a procedure, or of a constant or function, by
outcome. -/
structure Tally where
  killed : Nat := 0
  survived : Nat := 0
  equivalent : Nat := 0
  unviable : Nat := 0
  /-- Killed by the solver but not by testing. -/
  missed : Nat := 0

def Tally.add (t : Tally) : Outcome → Tally
  | .killed => { t with killed := t.killed + 1 }
  | .survived => { t with survived := t.survived + 1 }
  | .equivalent => { t with equivalent := t.equivalent + 1 }
  | .unviable => { t with unviable := t.unviable + 1 }

def Tally.merge (a b : Tally) : Tally :=
  { killed := a.killed + b.killed, survived := a.survived + b.survived, equivalent := a.equivalent + b.equivalent
    unviable := a.unviable + b.unviable, missed := a.missed + b.missed }

/-- The share of the mutants that could be killed that were
(`Reqs/Mutate#output`), as a whole percentage, rounded down; `none` if none
could be. -/
def Tally.rate? (t : Tally) : Option Nat :=
  let n := t.killed + t.survived
  if n == 0 then none else some (100 * t.killed / n)

end FrenCli.Mutate
