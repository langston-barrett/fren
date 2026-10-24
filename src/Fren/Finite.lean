/-!
# Finite types for `decide`

`Finite α` lists every value of `α`. Fren generates an instance for each
enum. With `Fren.Lang` open, `decide` can then handle `∀` and `∃` over
`Bool`, Fren enums, and any type given an instance, which is how `impl`
obligations over such types are proved by evaluation.
-/

namespace Fren

class Finite (α : Type) where
  all : List α
  complete : ∀ x, x ∈ all

instance : Finite Bool := ⟨[false, true], by intro x; cases x <;> decide⟩

namespace Lang

scoped instance decForall {α : Type} [Finite α] (p : α → Prop) [DecidablePred p] :
    Decidable (∀ x, p x) :=
  decidable_of_iff (∀ x ∈ Finite.all, p x) ⟨fun h x => h x (Finite.complete x), fun h x _ => h x⟩

scoped instance decExists {α : Type} [Finite α] (p : α → Prop) [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (∃ x ∈ Finite.all, p x)
    ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, Finite.complete x, h⟩⟩

end Lang

end Fren
