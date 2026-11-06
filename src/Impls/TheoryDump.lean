-- keep-sorted start
import FrenCore.TheoryDump
import Reqs.Cli
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls.TheoryDump

-- Both front ends use this classification for their opaque clause headers.
impl theory_clause_role: cli::theory_clause_role for (defined : Bool) (keyword : String) {
  defined? := defined,
  keyword := keyword,
  is_domain? := Fren.Core.theoryDumpRole defined keyword == .domain,
  is_theorem? := Fren.Core.theoryDumpRole defined keyword == .theorem,
  is_axiom? := Fren.Core.theoryDumpRole defined keyword == .axiom,
  is_goal? := Fren.Core.theoryDumpRole defined keyword == .goal,
} by
  intro defined keyword
  cases defined <;> simp [fren_spec, Fren.Core.theoryDumpRole, Fren.Str.lit] <;> split <;> simp_all


end Fren.Impls.TheoryDump
