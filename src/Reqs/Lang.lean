-- `Fren`'s modules rather than `Fren`, which imports only them: importing
-- it would wait for its own build too, on the build's critical path.
-- `lake test` checks that the list is `Fren`'s.
-- keep-sorted start
import Fren.Check
import Fren.Impl
import Fren.Literate
import Fren.Spec
import Fren.Trace
import Fren.View
-- keep-sorted end
open Fren.Lang

-- The requirements are in the chapters of the manual under Lang/, which
-- share the module `lang`.
#fren_md "Lang/Overview.md"
#fren_md "Lang/Lexical.md"
#fren_md "Lang/Types.md"
#fren_md "Lang/Items.md"
#fren_md "Lang/Components.md"
#fren_md "Lang/Decidability.md"
#fren_md "Lang/Patterns.md"
#fren_md "Lang/Let.md"
#fren_md "Lang/Expressions.md"
