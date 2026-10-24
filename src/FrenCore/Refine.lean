-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Refinement (`Reqs/Lang/Refinement`)

The rules of `refine r: c refines a` that both front ends share: which
variables of `a` the interface accepts, which checks run on the
refinement, and the messages.
-/

open Lean

namespace Fren.Core

/-- Whether `c` has the variable of `a` in the interface
(`refinement::interface`): an input as an input, an output as a public
output, of the same type. -/
def interfaceAccepted (input inConcrete concreteInput concretePub sameType : Bool) : Bool :=
  inConcrete && sameType && (if input then concreteInput else !concreteInput && concretePub)

/-- Whether a check of kind `k` runs on a refinement (`refinement::checks`). -/
def refinementRuns : CheckKind → Bool
  | .inst | .expect | .definedness => true
  | _ => false

/-- A variable of the abstract comp that the concrete comp lacks, or has
with another role or type (`refinement::interface`). -/
def interfaceMsg (concrete abstract x : Name) (why : String) : Msg :=
  { code? := some "F0412"
    headline := s!"`{showComp concrete}` cannot refine `{showComp abstract}`: {why}"
    label? := some s!"`{x}` does not match"
    notes := #[s!"note: each input of `{showComp abstract}` must be an input of `{showComp concrete}`, and each output a public output, of the same type"] }

end Fren.Core
