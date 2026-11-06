-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Guarded arms -/

/-- What an arm does at a value, from whether its pattern matches it and
whether its guard holds there (`lang::ArmAt`). -/
def toArmAt : Bool × Bool → lang.ArmAt
  | (false, _) => .NoMatch
  | (true, false) => .GuardFails
  | (true, true) => .Taken

/-- The position of the first arm whose pattern matches and whose guard
holds, `-1` if none. -/
def firstTakenIdx (arms : List (Bool × Bool × Int)) : Int :=
  ((arms.findIdx? fun a => a.1 && a.2.1).map Int.ofNat).getD (-1)

theorem toArmAt_taken (a : Bool × Bool) : toArmAt a = .Taken ↔ (a.1 && a.2) = true := by
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [toArmAt]

/-- `firstCase`, when whether each case is taken is known, takes the first
that is. -/
theorem firstCase_find (l : List α) (p : α → Bool) (f : α → β) :
    Fren.Core.firstCase l (fun a => some (if p a then some (f a) else none)) = some ((l.find? p).map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [Fren.Core.firstCase, h, ih]

theorem find?_eq_findIdx? (l : List α) (p : α → Bool) : l.find? p = (l.findIdx? p).bind (l[·]?) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, List.findIdx?_cons]
    · simp [h, List.findIdx?_cons, ih]
      cases l.findIdx? p <;> simp

theorem firstTakenIdx_indexOf (arms : List (Bool × Bool × Int)) :
    firstTakenIdx arms = Fren.Seq.indexOf (Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)))
      (Fren.Seq.unit lang.ArmAt.Taken) 0 := by
  rw [indexOf_single, firstTakenIdx, List.findIdx?_map]
  congr 3
  funext a
  rcases a with ⟨_ | _, _ | _, _⟩ <;> rfl

impl guarded_match: lang::guarded_match for (arms : List (Bool × Bool × Int)) (k : Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  bodies := Fren.Seq.ofList (arms.map (·.2.2)),
  k := k,
  first := firstTakenIdx arms,
  value := ((Fren.Core.firstCase arms fun a => some (if a.1 && a.2.1 then some a.2.2 else none)).join).getD 0,
} by
  intro arms k _
  simp only [fren_spec]
  refine ⟨firstTakenIdx_indexOf arms, fun h0 => ?_⟩
  · simp only [firstTakenIdx, firstCase_find, find?_eq_findIdx?]
    cases hi : arms.findIdx? (fun a => a.1 && a.2.1) with
    | none => simp [firstTakenIdx, hi] at h0
    | some i =>
      obtain ⟨hlt, _, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      rw [Fren.Seq.nth_of_lt _ _ (by simp) (by simpa using hlt)]
      simp [List.getElem?_eq_getElem hlt]

end Fren.Impls
