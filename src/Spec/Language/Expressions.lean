import Fren.Impl
import Fren.Literate
import Spec.Language.Types

open Fren.Lang

#fren_md "Expressions.md"

#fren_check

namespace Spec.Language.Expressions

open spec.types in
example : spec.expressions.value_valid? SYMBOLS (.Nominal LIGHT LIGHT_RED) = true := by decide

open spec.types in
example : spec.expressions.value_valid? SYMBOLS (.Nominal SIGNAL LIGHT_RED) = false := by decide

open spec.types in
example : spec.expressions.direct_item? Int (.Call F .Empty) F = true := by decide

end Spec.Language.Expressions
