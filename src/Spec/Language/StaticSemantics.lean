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

-- The size context of two parameters has `same` at the decreasing one.
open spec.names spec.surface in
example :
    spec.statics.parameter_sizes (.Extend (.Extend .Empty .Integer) .Boolean) 0 =
      .Extend (.Extend .Empty .Same) .Unknown := by
  decide

-- A call is guarded when the argument at the callee's decreasing parameter is a `smaller` local.
open spec.names spec.surface in
example :
    spec.statics.argument_guarded? (.Extend (.Extend .Empty .Same) .Smaller)
      (.Extend .Empty (.some 1)) 0 = true := by
  decide

-- An argument that is no local guards no call.
open spec.names spec.surface in
example :
    spec.statics.argument_guarded? (.Extend (.Extend .Empty .Same) .Smaller)
      (.Extend .Empty .none) 0 = false := by
  decide

-- A let whose value is a local gives its own local the value's size.
open spec.names spec.types spec.surface in
example :
    spec.statics.calls_guarded? (.Extend .Empty ⟨F, 0⟩) (.Extend .Empty .Smaller)
      (.Let (.some 0) (.Call F (.Extend .Empty (.some 1)))) = true := by
  decide

-- A function that calls itself on its own parameter is not structurally recursive.
open spec.names spec.types spec.surface in
example :
    spec.statics.group_passes? (.Extend .Empty
      ⟨F, .Extend .Empty .Integer, .Checked, .Call F (.Extend .Empty (.some 0))⟩) = false := by
  decide

-- A group of a function with no parameters has no choice of decreasing parameters.
open spec.names spec.types spec.surface in
example :
    spec.statics.choices (.Extend .Empty ⟨F, .Empty, .Checked, .Leaf⟩) = .Empty := by
  decide

-- A function in no recursive group passes unless its mark opts it out.
open spec.names spec.types spec.surface in
example :
    spec.statics.passes_alone? ⟨F, .Empty, .Checked, .Call SIGNAL .Empty⟩ = true := by
  decide

open spec.names spec.types spec.surface in
example :
    spec.statics.passes_alone? ⟨F, .Empty, .Unchecked, .Leaf⟩ = false := by
  decide

-- One `unchecked` mark opts the whole group out.
open spec.names spec.types spec.surface in
example :
    spec.statics.opted_out? (.Extend (.Extend .Empty
      ⟨F, .Empty, .Unchecked, .Leaf⟩) ⟨SIGNAL, .Empty, .Checked, .Leaf⟩) = true := by
  decide

-- The written calls of the table of `F(x₀)`: one call, whose argument is the local 0.
open spec.names spec.types spec.surface in
example :
    spec.statics.written_calls (.Extend (.Extend .Empty
      ⟨.Local 0, .Extend .Empty .Integer, .Integer⟩)
      ⟨.Call F (.Extend .Empty 0), .Extend .Empty .Integer, .Integer⟩) =
      .Both (.Both .Leaf .Leaf) (.Call F (.Extend .Empty (.some 0))) := by
  decide

end Spec.Language.StaticSemantics

set_option fren.requireEvidence "trusted" in
#fren_trace
