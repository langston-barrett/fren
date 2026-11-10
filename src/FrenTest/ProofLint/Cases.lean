module

/-!
Cases for the proof linters: what each must and must not report.

`FrenTest.ProofLint` lists the simp lemmas below that `simpNF` and `simpLoop`
must report; every other simp lemma here must pass. A line that ends in the
comment `-- unsqueezed` holds a tactic that the unsqueezed-tactic linter must
report, and no other line may be reported. The module is no lint target
itself.
-/

namespace FrenTest.ProofLint.Cases

public def twice (n : Nat) : Nat := n + n
def same (n : Nat) : Nat := n
def mix (a b : Nat) : Nat := a + b
def up (n : Nat) : Nat := n + 1
def next (n : Nat) : Nat := n + 1
@[reducible] def again (n : Nat) : Nat := twice n

/-! ## Simp lemmas that pass -/

@[simp] theorem twice_zero : twice 0 = 0 := rfl
@[simp] theorem same_eq (n : Nat) : same n = n := rfl
@[simp] theorem twice_pos (n : Nat) (h : 0 < n) : 0 < twice n := by unfold twice; omega
@[simp] theorem twice_ne (n : Nat) : twice n ≠ twice (n + 1) := by unfold twice; omega
@[simp] theorem twice_le_iff (a b : Nat) : twice a ≤ twice b ↔ a ≤ b := by unfold twice; omega
-- Not a renaming of its left-hand side: `a` occurs twice on the right.
@[simp] theorem mix_twice (a : Nat) : mix a a = twice a := rfl

public section
@[simp] theorem twice_one : twice 1 = 2 := by unfold twice; omega
end

/-! ## Simp lemmas that `simpNF` reports -/

-- The left-hand side is not in normal form: simp rewrites `same n` first.
@[simp] theorem twice_same (n : Nat) : twice (same n) = n + n := rfl
-- Redundant: `same_eq` twice proves it, and rewrites the argument first.
@[simp] theorem same_same (n : Nat) : same (same n) = n := rfl
-- Both sides are the same term once the reducible `again` unfolds.
@[simp] theorem again_eq (n : Nat) : again n = twice n := rfl
-- One conjunct of two is not in normal form.
@[simp] theorem twice_both (n : Nat) : twice 2 = 4 ∧ twice (0 + n) = n + n :=
  ⟨rfl, by unfold twice; omega⟩

public section
@[simp] theorem twice_zero_add (n : Nat) : twice (0 + n) = n + n := by unfold twice; omega
end

/-! ## Simp lemmas that `simpLoop` reports -/

-- The right-hand side is the left-hand side with `a` and `b` exchanged.
@[simp] theorem mix_comm (a b : Nat) : mix a b = mix b a := Nat.add_comm a b
-- Each undoes the other.
@[simp] theorem up_eq (n : Nat) : up n = next n := rfl
@[simp] theorem next_eq (m : Nat) : next m = up m := rfl

/-! ## Unsqueezed tactics -/

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp -- unsqueezed
  exact h

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp only [Nat.add_zero]
  exact h

example (a : Nat) : a + 0 = a := by simp

example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp at h -- unsqueezed
  exact h

example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp_all -- unsqueezed
  done

example (a b : Nat) (h : a = b) : twice a = b + a := by
  dsimp [twice] -- unsqueezed
  omega

example (a b : Nat) (h : a = b) : a + 0 = b := by
  try simp -- unsqueezed
  exact h

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp <;> exact h -- unsqueezed

example (a b : Nat) (h : a = b) : a + 0 = b ∧ b + 0 = a := by
  constructor <;> simp [h]

example (a b : Nat) (h : a = b) : a + 0 = b ∧ b + 0 = a := by
  constructor
  · simp [h]
  · simp -- unsqueezed
    omega

example (a b : Nat) (h : a = b) : a + 0 = b ∧ b + 0 = a := by
  constructor
  case left => simp [h]
  next => first | simp [h] | omega

example (a b : Nat) (h : a = b) : a + 0 = b ∧ b + 0 = a := by
  refine ⟨?_, ?_⟩
  all_goals simp -- unsqueezed
  all_goals omega

example (a b : Nat) (h : a = b) : a + 0 = b ∧ b + 0 = a := by
  have first : a + 0 = b := by simp [h]
  exact ⟨first, by simp [h]⟩

example (n : Nat) : n + 0 = n ∨ n = 0 := by
  cases n with
  | zero => simp
  | succ k =>
    simp -- unsqueezed
    done

example (n : Nat) : n + 0 = n := by
  match n with
  | 0 => simp
  | k + 1 => { simp }

example (n : Nat) : n + 0 = n := by
  if h : n = 0 then simp [h] else simp

example (a b : Nat) (h : a = b) : a + 0 = b := by
  conv => lhs; simp
  exact h

example (a b : Nat) (h : a = b) : a + 0 = b := by
  (simp; exact h) -- unsqueezed

example (a b : Nat) (h : a = b) : a + 0 = b := by
  show a + 0 = b
  simpa using h

-- No `grind` is left unfinished in a proof that compiles, so these two are
-- only parsed: the linter reads syntax and the proofs are never run.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · grind
  · grind only

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> first | grind | exact hq

end FrenTest.ProofLint.Cases
