-- keep-sorted start
import FrenCore.SentenceBridge
import Impls.Theories
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls.SentenceBridge

open Fren.Core Fren.Core.SentenceBridge

interp lang::bridge_has_parameter? := hasParameter
interp lang::bridge_reference := reference
interp lang::bridge_parameter_term := TheoryTerm.variable
interp lang::bridge_query_term := TheoryTerm.query

impl bridge_reference_step: lang::bridge_reference_step for (ps : List (Lean.Name × Ty)) (n : Lean.Name) {
  variables := ps,
  name := n,
  parameter? := hasParameter ps n,
  term := reference ps n,
} by
  intro ps n _
  cases ps <;> simp [fren_spec, hasParameter, reference]

interp lang::BridgeChoice := TheoryTerm × Ty
interp lang::BridgeChoices := List (TheoryTerm × Ty)
interp lang::bridge_choices_empty? := fun (xs : List (TheoryTerm × Ty)) => xs.isEmpty
interp lang::bridge_choices_rest := fun (xs : List (TheoryTerm × Ty)) => xs.tail
interp lang::bridge_choices_first := fun (xs : List (TheoryTerm × Ty)) => xs.headD default
interp lang::bridge_no_choice := fun (_ : List (TheoryTerm × Ty)) => (default : TheoryTerm × Ty)

impl bridge_unique_step: lang::bridge_unique_step for (xs : List (TheoryTerm × Ty)) {
  choices := xs,
  accepted? := (unique? xs).isSome,
  value := (unique? xs).getD default,
} by
  intro xs _
  cases xs with
  | nil => simp [fren_spec, unique?]
  | cons x xs => cases xs <;> simp [fren_spec, unique?]

end Fren.Impls.SentenceBridge
