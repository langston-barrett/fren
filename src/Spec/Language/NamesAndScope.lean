import Fren.Impl
import Fren.Literate
import FrenBase.Binding

open Fren.Lang

#fren_md "NamesAndScope.md"

#fren_check

namespace Spec.Language.NamesAndScope

/-- Obligation for the planned actual nearest-name search. The result must
identify the first equal spelling, not merely an in-bounds slot. This defines
requirements and supplies no search implementation or universal proof. -/
def NearestName (find : List String → String → Option Nat) : Prop :=
  (∀ names query i, find names query = some i ↔
    FrenBase.Binding.lookup names i = some query ∧
      ∀ j, j < i → FrenBase.Binding.lookup names j ≠ some query) ∧
  (∀ names query, find names query = none ↔ query ∉ names)

/-- An already-proved production fact, independent of name search. -/
theorem fresh_slot (names : List String) (name : String) :
    FrenBase.Binding.lookup (name :: names) 0 = some name :=
  FrenBase.Binding.lookup_fresh names name

/-- Entering a binder moves older slots; it does not change their entries. -/
theorem older_slot (names : List String) (name : String) (i : Nat) :
    FrenBase.Binding.lookup (name :: names) (i + 1) =
      FrenBase.Binding.lookup names i :=
  FrenBase.Binding.lookup_older names name i

-- Trailing tests: concrete production slot controls, not a name resolver.
#guard FrenBase.Binding.lookup ["x", "y", "x"] 0 == some "x"
#guard FrenBase.Binding.lookup ["x", "y", "x"] 1 == some "y"
#guard FrenBase.Binding.lookup ["y", "x"] 1 == some "x"
#guard FrenBase.Binding.lookup (["x"] : List String) 1 == none

end Spec.Language.NamesAndScope
