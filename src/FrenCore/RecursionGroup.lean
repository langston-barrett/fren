-- keep-sorted start
import FrenCore.Matching
import FrenCore.Recursion
-- keep-sorted end

namespace Fren.Core

/-- Members marked by their own bodies, in declaration order. -/
def groupMarked (flags : List Bool) : List Int :=
  flags.zipIdx.filterMap fun (marked, i) => if marked then some i else none

/-- Propagate a body's flags backwards through the raw call graph. The
finite closure computes its own bound and includes the initially marked
members (`lang::group_dependencies`). -/
def groupInherited (flags : List Bool) (uses : List GroupUse) : List Int :=
  let calls := uses.map fun u => (u.callee, u.caller)
  (((Matching.closure (groupMarked flags) calls (fun _ => true)).2.getD []).map Prod.fst)

end Fren.Core
