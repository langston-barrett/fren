-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## The prelude (`Reqs/Lang/Prelude#meaning`) -/

-- For every path, with the symbol that the `fren` command gives a user's
-- type (`FrenCli.dataSortSym`).
impl prelude_sort: lang::prelude_sort for (s : String) {
  path := s,
  sort := Fren.Core.userSortSym s,
} by
  intro s _
  have h : Fren.Core.leanSortNames = #["Option", "Except"] := by
    simp [Fren.Core.leanSortNames, Fren.Core.leanTypes, Lean.Name.getString!]
  by_cases ho : s = "Option" <;> by_cases he : s = "Except" <;>
    simp_all [fren_spec, Fren.Core.userSortSym, Fren.Str.lit]

end Fren.Impls
