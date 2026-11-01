import Fren

open scoped Fren.Lang

/-! Generated generic functions: a generic `match` can be split, and an
application's `Inhabited` instance is the one Lean finds, so that `simp`
rewrites with a hypothesis about it. -/

#fren_md "GenericMatch.fren"

-- `split` on a generic matcher (its splitter takes the same parameters).
example (s : Shape String) : area String s = 0 ∨ ∃ w h, s = .Box w h := by
  unfold area
  split
  · rename_i w h; exact Or.inr ⟨w, h, rfl⟩
  · exact Or.inl rfl

-- A hypothesis about `is_box?` at `String` rewrites its application within
-- `big_box?`, whose instance is `String.instInhabited`, not
-- `inferInstance` around it.
example (s : Shape String) (h : is_box? String s = false) : big_box? String s = false := by
  simp only [big_box?, h]
  simp
