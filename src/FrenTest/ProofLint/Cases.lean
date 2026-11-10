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
def spin (n : Nat) : Nat := n
def port (a b : Nat) : Nat := a + b
def star (a b : Nat) : Nat := a + b
def q1 (n : Nat) : Nat := n
def q2 (n : Nat) : Nat := n
def q3 (n : Nat) : Nat := n
def q4 (n : Nat) : Nat := n
def r1 (n : Nat) : Nat := n
def r2 (n : Nat) : Nat := n
def r3 (n : Nat) : Nat := n
def r4 (n : Nat) : Nat := n
def r5 (n : Nat) : Nat := n
@[reducible] def again (n : Nat) : Nat := twice n
def turn (n _k : Nat) : Nat := n
def grow (_n : Nat) : Nat := 0

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
-- Two rewrites and no finding.
@[simp] theorem twice_pair : twice 3 = 6 ∧ twice 4 = 8 := ⟨rfl, rfl⟩

/-! ## Simp lemmas that `simpNF` reports -/

-- The left-hand side is not in normal form: simp rewrites `same n` first.
@[simp] theorem twice_same (n : Nat) : twice (same n) = n + n := rfl
-- Redundant: `same_eq` twice proves it, and rewrites the argument first.
@[simp] theorem same_same (n : Nat) : same (same n) = n := rfl
-- Both sides are the same term once the reducible `again` unfolds.
@[simp] theorem again_eq (n : Nat) : again n = twice n := rfl
-- Two rewrites, each with its own finding. The first never applies: simp
-- cannot find `n` from `twice 2`. The second is not in normal form.
@[simp] theorem twice_both (n : Nat) : twice 2 = 4 ∧ twice (0 + n) = n + n :=
  ⟨rfl, by unfold twice; omega⟩

-- `same_eq` proves it too. With this lemma in the simp set its higher
-- priority wins, so only a run without it shows the competition.
@[simp high] theorem same_zero : same 0 = 0 := rfl

public section
@[simp] theorem twice_zero_add (n : Nat) : twice (0 + n) = n + n := by unfold twice; omega
end

-- Two rewrites with a finding of the same kind each: their identities differ.
@[simp] theorem same_pair : same (same 1) = 1 ∧ same (same 2) = 2 := ⟨rfl, rfl⟩

/-! ## Simp lemmas that `simpLoop` reports -/

-- Two rewrites, of which only the second loops: its findings name its
-- left-hand side after `@`, and the first rewrite has none.
@[simp] theorem turn_both (n : Nat) : turn n 0 = n ∧ turn n 1 = turn (turn n 1) 1 := ⟨rfl, rfl⟩
-- Simp runs out of steps here before it runs out of depth.
@[simp] theorem grow_eq (n : Nat) : grow n = grow (n + 1 + 1 + 1 + 1) := rfl

-- The right-hand side is the left-hand side with `a` and `b` exchanged.
@[simp] theorem mix_comm (a b : Nat) : mix a b = mix b a := Nat.add_comm a b
-- Each undoes the other, so each is redundant too: without `up_eq` simp
-- leaves `up n` alone and rewrites the right-hand side `next n` to it. Only
-- the right-hand side changes, and every such lemma loops with the one that
-- changes it, so `simpNF` must check past simp's failure on the whole set.
@[simp] theorem up_eq (n : Nat) : up n = next n := rfl
@[simp] theorem next_eq (m : Nat) : next m = up m := rfl
-- Growing: the right-hand side contains an instance of the left-hand side.
@[simp] theorem spin_eq (n : Nat) : spin n = spin (spin n) := rfl
-- A cycle under instantiation: `port_eq` at `a a` undoes `star_self`, which
-- does not undo `port_eq` in general, so only `star_self` is reported.
@[simp] theorem port_eq (a b : Nat) : port a b = star a b := rfl
@[simp] theorem star_self (a : Nat) : star a a = port a a := rfl
-- A cycle of `cycleLength` lemmas, the longest that the search follows.
@[simp] theorem q1_eq (n : Nat) : q1 n = q2 n := rfl
@[simp] theorem q2_eq (n : Nat) : q2 n = q3 n := rfl
@[simp] theorem q3_eq (n : Nat) : q3 n = q4 n := rfl
@[simp] theorem q4_eq (n : Nat) : q4 n = q1 n := rfl

/-! ## A loop beyond the bound of the cycle search

A cycle of five lemmas, one more than the search follows: `simpLoop` reports
each because simp runs away on its left-hand side, and `simpNF` because simp
fails there. -/

@[simp] theorem r1_eq (n : Nat) : r1 n = r2 n := rfl
@[simp] theorem r2_eq (n : Nat) : r2 n = r3 n := rfl
@[simp] theorem r3_eq (n : Nat) : r3 n = r4 n := rfl
@[simp] theorem r4_eq (n : Nat) : r4 n = r5 n := rfl
@[simp] theorem r5_eq (n : Nat) : r5 n = r1 n := rfl

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

-- Each branch of a tactic `if` must close its goal, whatever follows the
-- `if`: Lean rejects a branch that leaves it open ("unsolved goals"), as it
-- does for a `match` alternative. So the last tactic of a branch is terminal.
example (n : Nat) : n + 0 = n ∧ n = n := by
  constructor
  if h : n = 0 then simp [h] else simp
  rfl

example (n m : Nat) (h : m + 0 = n) : n + 0 = n ∧ m = n := by
  constructor
  if c : n = 0 then
    simp at h -- unsqueezed
    simp
  else simp
  exact h

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
