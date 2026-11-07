-- keep-sorted start
import Lean
-- keep-sorted end

/-! # Decisions attached to rewritten propositions -/

open Lean Meta

namespace Fren.Decisions

/-- The proposition and its decision in a Boolean decision or conditional.
The dictionary is not another occurrence of the source proposition. -/
def positions? (e : Expr) : Option (Nat × Nat) :=
  if e.isAppOfArity ``Decidable.decide 2 then some (0, 1)
  else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then some (1, 2) else none

/-- Rebuild the whole decision after its proposition changes. Inferring
the old instance's type alone can miss a stale decision in a child. -/
def refresh (e : Expr) : MetaM Expr := do
  let some (p, d) := positions? e | return e
  let args := e.getAppArgs
  let proposition := args[p]!
  let expected := mkApp (mkConst ``Decidable) proposition
  let decision? ← try synthInstance? expected catch _ => pure none
  let decision := decision?.getD (mkApp (mkConst ``Classical.propDecidable) proposition)
  return mkAppN e.getAppFn (args.set! d decision)

end Fren.Decisions
