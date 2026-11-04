-- keep-sorted start
import FrenCore.Quantifier
-- keep-sorted end

/-! Finite set cardinalities: cvc5's native cardinality solver can exhaust
a finite element sort, or return a model that fails confirmation (#820).
Both front ends instead count membership at every listed value, up to
the same bound as a finite quantifier (`lang::set_card_expansion`). -/

namespace Fren.Core

/-- The complete list of elements to count, if it fits the expansion
bound; `none` retains native set cardinality. -/
def setCardExpansion (values? : Option (Array α)) : Option (Array α) :=
  values?.filter fun vs => vs.size ≤ maxInstances

/-- Sum the indicators of membership in the listed universe. The front
ends supply only their representation's constructors. -/
def sumSetMembersM [Monad m] (values : Array α) (zero : β)
    (indicator : α → m β) (add : β → β → m β) : m β :=
  values.foldlM (fun acc v => do add acc (← indicator v)) zero

end Fren.Core
