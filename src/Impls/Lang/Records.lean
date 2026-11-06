-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- The variants of `vs` for which `p` holds are all of them exactly when
there are as many. -/
theorem ofList_filter_eq (vs : List Lean.Name) (p : Lean.Name → Bool) :
    Fren.FinSet.ofList (vs.filter p) = Fren.FinSet.ofList vs ↔ (vs.filter p).length = vs.length := by
  rw [Fren.FinSet.ext_iff]
  simp only [Fren.FinSet.mem_ofList, List.mem_filter]
  have hle := List.length_filter_le p vs
  have hlt := @List.length_filter_lt_length_iff_exists _ p vs
  constructor
  · intro h
    have : ¬ (vs.filter p).length < vs.length := fun hl =>
      let ⟨x, hx, hp⟩ := hlt.mp hl; hp ((h x).mpr hx).2
    omega
  · intro h x
    refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
    cases hp : p x
    · have := hlt.mpr ⟨x, hx, by simp [hp]⟩
      omega
    · rfl

-- For every literal, with the check that both front ends use.
impl record_literal: lang::record_literal for (fields given : Array Lean.Name) {
  fields := Fren.FinSet.ofArray fields,
  given := Fren.FinSet.ofArray given,
  n_repeated := Fren.Core.repeatsOf given,
  accepted? := Fren.Core.recordLiteralAccepted fields given,
} by
  intro fields given _
  have : Fren.FinSet.ofArray given = Fren.FinSet.ofArray fields ↔ (∀ g ∈ given, g ∈ fields) ∧ ∀ f ∈ fields, f ∈ given := by
    rw [Fren.FinSet.ext_iff]
    simp only [Fren.FinSet.mem_ofArray]
    exact ⟨fun h => ⟨fun g hg => (h g).mp hg, fun f hf => (h f).mpr hf⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩
  simp only [fren_spec, Fren.Core.recordLiteralAccepted, this, Bool.and_eq_true, Array.all_eq_true',
    Array.contains_iff_mem, beq_iff_eq]
  simp

-- For every update, whether the updated value is of a record, `r`, with
-- the check that both front ends use.
impl record_update: lang::record_update for (r : Bool) (fields given : Array Lean.Name) {
  record? := r,
  fields := Fren.FinSet.ofArray fields,
  given := Fren.FinSet.ofArray given,
  n_repeated := Fren.Core.repeatsOf given,
  accepted? := Fren.Core.recordUpdateAccepted r fields given,
} by
  intro r fields given _
  simp only [fren_spec, Fren.Core.recordUpdateAccepted, Fren.FinSet.subset_def, Fren.FinSet.mem_ofArray,
    Bool.and_eq_true, Array.all_eq_true', Array.contains_iff_mem, beq_iff_eq]
  simp

impl field_init: lang::field_init for (f : Bool) (n : Nat) {
  field? := f,
  n := n,
  accepted? := Fren.Core.fieldInitOk f n,
} by
  intro f n _
  cases f <;> simp [fren_spec, Fren.Core.fieldInitOk] <;> omega

end Fren.Impls
