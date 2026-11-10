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

end Spec.Language.StaticSemantics

set_option fren.requireEvidence "trusted" in
#fren_trace
