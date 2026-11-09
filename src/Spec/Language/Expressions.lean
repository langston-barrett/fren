import Fren.Impl
import Fren.Literate
import Spec.Language.Types

open Fren.Lang

#fren_md "Expressions.md"

namespace Spec.Language.Expressions

-- A shared simp set keeps each finite example on the same exact definitions.
attribute [local simp] Spec.Language.Types.forall_below_flat Spec.Language.Types.exists_below_flat Fin.forall_fin_succ
  Fin.exists_fin_succ Fren.Seq.ofList Fren.Seq.unit Fren.Seq.len Fren.Seq.toList
  Fren.Seq.nth Fren.Seq.instAppend Fren.Seq.instEmptyCollection Fren.Str.lit and_assoc


example : spec.types.MATCH_ARMS_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_EMPTY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MATCH_ALL_BODIES_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.COVERAGE_SEPARATE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.DUPLICATES_SEPARATE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_ARITY_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CALL_ARGUMENT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONSTRUCTOR_NOT_CALLABLE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.FUNCTION_NOT_VALUE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONSTRUCTOR_TYPE_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARENTHESES_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.CONTEXT_ALIGNMENT_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARAMETER_ORDER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.PARAMETER_SUFFIX_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.IMPLICIT_BOOLEAN_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.MISSING_ANNOTATION_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.EXPLICIT_NOT_OVERWRITTEN_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.VALUE_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.WRONG_VALUE_OWNER_EXAMPLE := by
  simp [fren_spec] <;> decide

example : spec.types.DIRECT_CALLEE_EXAMPLE := by
  simp [fren_spec] <;> decide

end Spec.Language.Expressions
