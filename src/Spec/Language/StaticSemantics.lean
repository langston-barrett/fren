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

-- A local has the size that the size context gives its level.
open spec.names spec.surface in
example :
    spec.statics.form_size Int (.Extend (.Extend .Empty .Same) .Unknown) (.Local 0) = .Same := by
  decide

-- A unary operator has the size `unknown`, though its operand's level is `smaller`.
open spec.names spec.surface in
example :
    spec.statics.form_size Int (.Extend .Empty .Smaller) (.Unary .Neg 0) = .Unknown := by
  decide

-- A local whose level is outside the size context has the size `unknown`.
open spec.names spec.surface in
example :
    spec.statics.form_size Int (.Extend .Empty .Smaller) (.Local 1) = .Unknown := by
  decide

-- A call and a let have the size `unknown`, even over a `smaller` level.
open spec.names spec.types spec.surface in
example :
    spec.statics.form_size Int (.Extend .Empty .Smaller) (.Call F (.Extend .Empty 0)) = .Unknown := by
  decide

open spec.names spec.surface in
example :
    spec.statics.form_size Int (.Extend .Empty .Smaller) (.Let .none 0 0) = .Unknown := by
  decide

-- An argument is guarded only when it is a local of size `smaller`.
open spec.names spec.surface in
example :
    spec.statics.guarded? Int (.Extend (.Extend .Empty .Same) .Smaller) (.Local 1) = true := by
  decide

-- The decreasing parameter itself has the size `same`, so it guards no call.
open spec.names spec.surface in
example :
    spec.statics.guarded? Int (.Extend (.Extend .Empty .Same) .Smaller) (.Local 0) = false := by
  decide

end Spec.Language.StaticSemantics

set_option fren.requireEvidence "trusted" in
#fren_trace
