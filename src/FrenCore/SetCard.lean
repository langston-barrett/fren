-- keep-sorted start
import FrenCore.Generics
import FrenCore.Quantifier
-- keep-sorted end

/-! Finite set cardinalities: cvc5's native cardinality solver can exhaust
a finite element sort, or return a model that fails confirmation (#820).
Both front ends instead count membership at every listed value, up to
the same bound as a finite quantifier (`lang::set_card_expansion`). -/

namespace Fren.Core

/-- The complete element count of a set or relation, using the same type
count as quantifiers (`lang::instance_values`). A relation counts pairs. -/
def setCardCount (count : Ty → Option Nat) : Ty → Option Nat
  | .set a => count a
  | .rel a b => do return (← count a) * (← count b)
  | _ => none

/-- Expand exactly the listed universes within the quantifier bound
(`lang::set_card_expansion`), before either reader builds its terms. -/
def setCardExpansion (count : Option Nat) : Option Nat :=
  count.filter (· ≤ maxInstances)

/-- A reader must build the complete Core count. A missing or short list
is an internal error, never a reason to fall back to native cardinality. -/
def checkedSetCardValues (expected : Nat) (values? : Option (Array α)) : Except String (Array α) :=
  match values? with
  | some vs => if vs.size == expected then .ok vs else
      .error s!"set cardinality expected {expected} values, but built {vs.size}"
  | none => .error s!"set cardinality expected {expected} values, but could not build them"

/-- Sum the indicators of membership in the listed universe. The front
ends supply only their representation's constructors. -/
def sumSetMembersM [Monad m] (values : Array α) (zero : β)
    (indicator : α → m β) (add : β → β → m β) : m β :=
  values.foldlM (fun acc v => do add acc (← indicator v)) zero

end Fren.Core
