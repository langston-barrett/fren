-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

-- For every name: `checkVarName` reads the suffix from the name itself, with
-- the meaning of `ends_with?` that Fren fixes.
impl bool_naming: lang::bool_naming for (s : String) (a : lang.Annot) {
  name := s,
  annot := a,
  accepted? := (Fren.Core.checkVarName (.mkSimple s) (isBool? a)).isOk,
} by
  intro s a _
  have hs : Fren.Core.nameText (.mkSimple s) = s := rfl
  cases h : Fren.Str.endsWith s "?" <;> cases a <;>
    simp [fren_spec, Fren.Core.checkVarName, Fren.Core.checkVarKind, isBool?, hs, h, Except.isOk, Except.toBool] <;> rfl

interp lang::DeclaredName := Lean.Name

/-- A list's distinct members are as many as it has exactly when none
repeats. -/
theorem nub_length_eq_iff {α : Type} [DecidableEq α] :
    ∀ (l : List α), (Fren.FinSet.nub l).length = l.length ↔ l.Nodup
  | [] => by simp [Fren.FinSet.nub]
  | a :: l => by
    have ih := nub_length_eq_iff l
    have hle : (Fren.FinSet.nub l).length ≤ l.length :=
      Fren.FinSet.length_le_of_nodup (Fren.FinSet.nodup_nub l) fun _ hx => Fren.FinSet.mem_nub.mp hx
    unfold Fren.FinSet.nub
    by_cases h : a ∈ Fren.FinSet.nub l
    · have ha : a ∈ l := Fren.FinSet.mem_nub.mp h
      simp only [h, if_true, List.length_cons, List.nodup_cons, ha, not_true_eq_false, false_and, iff_false]
      omega
    · have ha : a ∉ l := fun m => h (Fren.FinSet.mem_nub.mpr m)
      simp [h, List.nodup_cons, ha, ih]

/-- A list's set of members has as many as the list exactly when none
repeats. -/
theorem card_ofList_eq_length_iff {α : Type} [DecidableEq α] (l : List α) :
    (Fren.FinSet.ofList l).card = (l.length : Int) ↔ l.Nodup := by
  rw [Fren.FinSet.card_ofList, Int.natCast_inj]
  exact nub_length_eq_iff l

-- For every list of declared names, with the check that both front ends use.
impl distinct_names: lang::distinct_names for (names : Array Lean.Name) {
  count := names.size,
  names := Fren.FinSet.ofArray names,
  accepted? := (Fren.Core.repeatsAt names).isEmpty,
} by
  intro names _
  have := @card_ofList_eq_length_iff _ (fun a b => Classical.propDecidable (a = b)) names.toList
  simp only [Array.length_toList] at this
  simp only [fren_spec, Fren.FinSet.ofArray, Array.isEmpty_iff, Fren.Core.repeatsAt_eq_empty]
  exact this.symm

end Fren.Impls
