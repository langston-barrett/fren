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

open Fren.Core (CheckKind interfaceAccepted refineBindingsAccepted refineMentionOk refinementRuns repeatsOf_eq_zero)

impl interface_rule: refinement::interface for (i c ci p ta tc : Bool) {
  input? := i,
  in_concrete? := c,
  concrete_input? := ci,
  concrete_pub? := p,
  a_widens? := ta,
  c_widens? := tc,
  accepted? := interfaceAccepted i c ci p ta tc,
} by
  intro i c ci p ta tc _
  cases i <;> cases c <;> cases ci <;> cases p <;> cases ta <;> cases tc <;> decide

-- One name, bound `n` times. Over `Nat`, so a proof by cases.
impl binding_rule: refinement::binding for (v : Bool) (n : Nat) {
  variable? := v,
  n := n,
  accepted? := refineBindingsAccepted (if v then #[`x] else #[]) (Array.replicate n `x),
} by
  intro v n _
  cases v <;> rcases n with _ | _ | n <;> simp [fren_spec, refineBindingsAccepted, repeatsOf_eq_zero] <;> omega

impl mention_rule: refinement::mention for (i ci p : Bool) {
  input? := i,
  concrete_input? := ci,
  concrete_pub? := p,
  allowed? := refineMentionOk i ci p,
} by
  intro i ci p _
  cases i <;> cases ci <;> cases p <;> decide

impl checks_rule: refinement::checks for (k : CheckKind) {
  kind := toCheckKind k,
  runs? := refinementRuns k,
} by
  intro k _
  cases k <;> decide

end Fren.Impls
