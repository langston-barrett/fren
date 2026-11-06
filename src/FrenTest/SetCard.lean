-- keep-sorted start
import Fren.FinSet
import FrenCore.SetCard
-- keep-sorted end

-- fren-covers: lang::set_card_expansion

/-! The cardinality lowering's mathematical identity, for every finite
universe and set, and its shared count and enumeration-integrity guards. -/

namespace FrenTest.SetCard

open Fren

private def sigs (name : Lean.Name) : Option Core.DataSig :=
  if name == `Four then some { isRecord := true, unbounded := false, ctors := #[Array.replicate 4 .bool] }
  else if name == `Eight then some { isRecord := true, unbounded := false, ctors := #[Array.replicate 8 .bool] }
  else if name == `Seventeen then some { isRecord := false, unbounded := false, ctors := #[#[], #[.record `Four []]] }
  else if name == `Beyond then some { isRecord := false, unbounded := false, ctors := #[#[], #[.record `Eight []]] }
  else if name == `Generic then some { isRecord := false, unbounded := false, ctors := #[#[.param 0 `T]] }
  else if name == `Recursive then some { isRecord := false, unbounded := true, ctors := #[#[], #[.enum `Recursive []]] }
  else none

#guard Core.setCardExpansion (Core.setCardCount (·.valueCount sigs) (.set (.record `Eight []))) == some 256
#guard Core.setCardCount (·.valueCount sigs) (.set (.enum `Beyond [])) == some 257
#guard Core.setCardExpansion (Core.setCardCount (·.valueCount sigs) (.set (.enum `Beyond []))) == none
#guard Core.setCardCount (·.valueCount sigs) (.rel (.record `Four []) (.enum `Seventeen [])) == some 272
#guard Core.setCardExpansion (Core.setCardCount (·.valueCount sigs) (.rel (.record `Four []) (.enum `Seventeen []))) == none
#guard Core.setCardCount (·.valueCount sigs) (.set (.enum `Generic [.int])) == none
#guard Core.setCardCount (·.valueCount sigs) (.set (.enum `Generic [.abstract `A])) == none
#guard Core.setCardCount (·.valueCount sigs) (.set (.enum `Recursive [])) == none

#guard Core.setCardExpansion none == none
#guard Core.setCardExpansion (some 256) == some 256
#guard Core.setCardExpansion (some 257) == none
#guard Core.setCardCount (fun _ => some 16) (.rel .bool .bool) == some 256
#guard Core.setCardCount (fun t => if t == .bool then some 16 else some 17) (.rel .bool .int) == some 272
#guard Core.setCardCount (fun _ => none) (.set .int) == none
#guard (Core.checkedSetCardValues 2 (some #[true, false])).isOk
#guard !(Core.checkedSetCardValues 2 (some #[true])).isOk
#guard !(Core.checkedSetCardValues 2 (some #[true, true, false])).isOk
#guard !(Core.checkedSetCardValues (α := Bool) 2 none).isOk

private theorem nub_eq_of_nodup [DecidableEq α] (l : List α) (h : l.Nodup) : FinSet.nub l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp h
    simp [FinSet.nub, ih hl, ha]

private theorem sum_members_aux [DecidableEq α] (l : List α) (s : FinSet α) (z : Int) :
    l.foldl (fun n v => n + if v ∈ s then 1 else 0) z =
      z + (l.filter (fun v => decide (v ∈ s))).length := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih =>
    by_cases h : a ∈ s <;> simp [List.foldl_cons, h, ih] <;> omega

/-- With a complete, nonrepeating universe, the sum that both readers
emit is exactly `FinSet.card`, for every set of that element type. -/
theorem sum_members_card [DecidableEq α] (values : Array α)
    (distinct : values.toList.Nodup) (complete : ∀ v, v ∈ values.toList) (s : FinSet α) :
    Id.run (Core.sumSetMembersM values (0 : Int)
      (fun v => pure (if v ∈ s then 1 else 0)) (fun a b => pure (a + b))) = s.card := by
  let members := values.toList.filter (fun v => decide (v ∈ s))
  have hs : s = FinSet.ofList members := by
    apply FinSet.ext
    intro v
    simp [members, complete v]
  have hc : s.card = (members.length : Int) := by
    rw [hs, FinSet.card_ofList, nub_eq_of_nodup _ (distinct.filter _)]
  rw [hc]
  simp only [Core.sumSetMembersM, ← Array.foldlM_toList]
  simpa [members] using sum_members_aux values.toList s 0

end FrenTest.SetCard
