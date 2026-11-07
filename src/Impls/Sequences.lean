import Fren.Seq

/-! Sequence representation facts used by the instantiation impls. -/

namespace Fren.Impls

/-- Mapping a sequence is its first image followed by the mapped tail,
for lists of every length. -/
theorem seqMapParts {α β : Type} [Inhabited α] [DecidableEq α]
    (f : α → β) (ts : List α) :
    Fren.Seq.ofList (ts.map f) =
      if Fren.Seq.ofList ts = ∅ then ∅ else
      Fren.Seq.unit (f ((Fren.Seq.ofList ts).nth 0)) ++
        Fren.Seq.ofList (((Fren.Seq.ofList ts).slice 1 (Fren.Seq.ofList ts).len).toList.map f) := by
  change ts.map f = if ts = [] then [] else
    [f ((Fren.Seq.ofList ts).nth 0)] ++
      (((Fren.Seq.ofList ts).slice 1 (Fren.Seq.ofList ts).len).toList.map f)
  cases ts with
  | nil => rfl
  | cons t ts =>
    have first : (Fren.Seq.ofList (t :: ts)).nth 0 = t := by
      rw [Fren.Seq.nth_of_lt (Fren.Seq.ofList (t :: ts)) 0 (by omega) (by
        change (0 : Int) < ((t :: ts).length : Int)
        simp only [List.length_cons]
        omega)]
      rfl
    have tail : ((Fren.Seq.ofList (t :: ts)).slice 1 (Fren.Seq.ofList (t :: ts)).len).toList = ts := by
      cases ts with
      | nil => rfl
      | cons u us =>
        unfold Fren.Seq.slice
        rw [if_pos (by
          change (0 : Int) ≤ 1 ∧ 1 < ((t :: u :: us).length : Int) ∧ 0 < ((t :: u :: us).length : Int)
          simp only [List.length_cons]
          omega)]
        change ((t :: u :: us).drop 1).take (t :: u :: us).length = u :: us
        simp only [List.drop_succ_cons, List.drop_zero]
        exact List.take_of_length_le (by simp only [List.length_cons]; omega)
    rw [if_neg (List.cons_ne_nil t ts), first, tail]
    rfl

end Fren.Impls
