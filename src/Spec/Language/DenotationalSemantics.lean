import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.StaticSemantics

open Fren.Lang

#fren_md "DenotationalSemantics.md"

#fren_check

namespace Spec.Language.DenotationalSemantics

open spec.names spec.types in
example : spec.denotation.value_valid? SYMB (.Nominal LIGHT LIGHT_RED) = true := by decide

open spec.names spec.types in
example : spec.denotation.value_valid? SYMB (.Nominal SIGNAL LIGHT_RED) = false := by decide

end Spec.Language.DenotationalSemantics

set_option fren.requireEvidence "trusted" in
#fren_trace
