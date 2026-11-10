module

public import FrenOirToSmt.Translate

public section
namespace FrenOirToSmt
open FrenLir

/-- The decimal digits that `Symbol.render` writes for an index. -/
private def digits (i : Nat) : List Char := Nat.toDigits 10 i

private theorem digits_inj {i j : Nat} : digits i = digits j ↔ i = j :=
  ⟨fun h => Nat.repr_inj.mp (by simp only [Nat.repr_eq_ofList_toDigits]; exact congrArg String.ofList h),
    congrArg digits⟩

private theorem isDigit_of_mem_digits {i : Nat} {c : Char} (h : c ∈ digits i) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- A separator that occurs in neither prefix splits both lists at the same place. -/
private theorem split_at {c : Char} {l₁ l₂ r₁ r₂ : List Char} (h₁ : c ∉ l₁) (h₂ : c ∉ l₂) :
    l₁ ++ c :: r₁ = l₂ ++ c :: r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp
    | cons y l₂ => simp [List.ne_of_not_mem_cons h₂]
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp [Ne.symm (List.ne_of_not_mem_cons h₁)]
    | cons y l₂ =>
      simp [ih (List.not_mem_of_not_mem_cons h₁) (List.not_mem_of_not_mem_cons h₂), and_assoc]

private theorem digits_separated {i j i' j' : Nat} :
    digits i ++ '_' :: digits j = digits i' ++ '_' :: digits j' ↔ i = i' ∧ j = j' := by
  have fresh : ∀ k, '_' ∉ digits k := fun k h => by
    have := isDigit_of_mem_digits h
    contradiction
  rw [split_at (fresh i) (fresh i'), digits_inj, digits_inj]

/-- The characters of a rendered symbol: the family letter, the decimal
indices and, for a function or local, the component letter. -/
private def Symbol.chars : Symbol → List Char
  | .sort i => 'E' :: digits i
  | .constructor i j => 'C' :: (digits i ++ '_' :: digits j)
  | .function i .value => 'F' :: (digits i ++ ['v'])
  | .function i .domain => 'F' :: (digits i ++ ['d'])
  | .parameter i => 'P' :: digits i
  | .local i .value => 'L' :: (digits i ++ ['v'])
  | .local i .domain => 'L' :: (digits i ++ ['d'])

private theorem Symbol.toList_render (s : Symbol) : s.render.toList = s.chars := by
  have spelled {text : String} (h : s.render = text) (chars : text.toList = s.chars) :
      s.render.toList = s.chars := h ▸ chars
  rcases s with i | ⟨i, j⟩ | ⟨i, _ | _⟩ | i | ⟨i, _ | _⟩
  · exact spelled (text := "E" ++ i.repr) rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "C" ++ i.repr ++ "_" ++ j.repr) rfl
      (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "F" ++ i.repr ++ "v") rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "F" ++ i.repr ++ "d") rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "P" ++ i.repr) rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "L" ++ i.repr ++ "v") rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])
  · exact spelled (text := "L" ++ i.repr ++ "d") rfl (by simp [Symbol.chars, digits, Nat.repr_eq_ofList_toDigits])

private theorem Symbol.chars_inj {a b : Symbol} : a.chars = b.chars ↔ a = b := by
  rcases a with i | ⟨i, j⟩ | ⟨i, _ | _⟩ | i | ⟨i, _ | _⟩ <;>
    rcases b with i' | ⟨i', j'⟩ | ⟨i', _ | _⟩ | i' | ⟨i', _ | _⟩ <;>
    simp [Symbol.chars, digits_inj, digits_separated]

/-- Distinct symbols have distinct rendered names, within a family and across families. -/
@[simp] theorem Symbol.render_inj {a b : Symbol} : a.render = b.render ↔ a = b :=
  ⟨fun h => Symbol.chars_inj.mp (by rw [← Symbol.toList_render, ← Symbol.toList_render, h]), congrArg _⟩

/-- Rendering is injective, in the form that `grind` takes. -/
@[grind inj] theorem Symbol.render_injective : Function.Injective Symbol.render :=
  fun _ _ => Symbol.render_inj.mp

/-- A rendered name starts with one of the five family letters. -/
theorem Symbol.render_front (s : Symbol) :
    ∃ c rest, s.render.toList = c :: rest ∧ c ∈ ['E', 'C', 'F', 'P', 'L'] := by
  rw [Symbol.toList_render]
  rcases s with i | ⟨i, j⟩ | ⟨i, _ | _⟩ | i | ⟨i, _ | _⟩ <;> exact ⟨_, _, rfl, by decide⟩

end FrenOirToSmt
