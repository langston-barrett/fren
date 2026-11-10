import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.Types

open Fren.Lang

#fren_md "StaticSemantics.md"

#fren_check

namespace Spec.Language.StaticSemantics

open spec.names spec.types in
example : spec.statics.direct_item? Int (.Call F .Empty) F = true := by decide

-- A match with two arms for one constructor does not have distinct arms.
open spec.names spec.types spec.surface in
example :
    spec.statics.arms_distinct? Int (.Extend (.Extend .Empty ⟨F, 1⟩) ⟨F, 2⟩) = false := by
  decide

open spec.names spec.types spec.surface in
example :
    spec.statics.arms_distinct? Int (.Extend .Empty ⟨F, 1⟩) = true := by
  decide

end Spec.Language.StaticSemantics

set_option fren.requireEvidence "trusted" in
#fren_trace
