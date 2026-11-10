import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.DenotationalSemantics

open Fren.Lang

#fren_md "DynamicSemantics.md"

#fren_check

pub mod spec::dynamics

open spec.surface spec.types spec.denotation spec.dynamics in
impl values_agree_proof: values_agree for (unop : UnaryOp) (op : BinaryOp) (left right result : Value) {
  unop := unop, op := op, left := left, right := right, result := result, holds? := true
} by
  intro unop op left right result _
  simp only [values_agree.ensures, values_agree.ensure.output, values_agree.ensure.unary,
    values_agree.ensure.binary]
  refine ⟨trivial, ?_, ?_⟩
  · cases unop <;> cases left <;> simp [fren_spec, unary_value, unary_meaning?] <;>
      first | grind | (intro h; subst h; simp) | (intro h; exact h.symm)
  · cases op <;> cases left <;> cases right <;>
      simp [fren_spec, binary_value, integer_value, boolean_value, binary_meaning?,
        integer_meaning?, boolean_meaning?] <;>
      first | grind | (intro h; subst h; simp) | (intro h; exact h.symm)

open spec.names spec.types spec.denotation spec.dynamics in
impl evaluation_examples_proof: evaluation_examples { holds? := true } by
  intro _
  simp only [evaluation_examples.ensures, evaluation_examples.ensure.output,
    evaluation_examples.ensure.bound, evaluation_examples.ensure.unbound,
    evaluation_examples.ensure.uncomputed]
  decide

set_option fren.requireEvidence "trusted" in
#fren_trace
