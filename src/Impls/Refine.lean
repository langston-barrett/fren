-- keep-sorted start
import Impls.Check
import Reqs.Refine
-- keep-sorted end
open Fren.Lang

/-!
# Refinement (`Reqs/Lang/Refinement`)

The rules in `FrenCore.Refine` implement the comps of `refine`, by `decide`.
-/

namespace Fren.Impls

open Fren.Core (CheckKind interfaceAccepted refinementRuns)

impl interface_rule: refinement::interface for (i c ci p t : Bool) {
  input? := i,
  in_concrete? := c,
  concrete_input? := ci,
  concrete_pub? := p,
  same_type? := t,
  accepted? := interfaceAccepted i c ci p t,
} by
  intro i c ci p t _
  cases i <;> cases c <;> cases ci <;> cases p <;> cases t <;> decide

impl checks_rule: refinement::checks for (k : CheckKind) {
  kind := toCheckKind k,
  runs? := refinementRuns k,
} by
  intro k _
  cases k <;> decide

end Fren.Impls
