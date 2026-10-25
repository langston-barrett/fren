-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

/-!
An item for `LiterateImported` to import and check. It is not checked here,
so this module reports nothing.
-/

mod dep
pub comp dep_gate { in a? pub out b? req same: b? iff a? expect never: when a?, not b? }
