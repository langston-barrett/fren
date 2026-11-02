-- keep-sorted start
import Fren.Literate
import Reqs.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

-- The requirements are in Models.md, which is also a chapter of the manual.
-- `model::known` is `lang::eval`'s structural recursion with the rules of
-- confirmation, one arm for each form as `eval` has, whose compilation
-- alone takes 160M of the default 200M heartbeats (`Reqs/Lang/Semantics`).
set_option maxHeartbeats 600000 in
#fren_md "Models.md"
