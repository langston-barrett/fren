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

-- The requirements are in Lang/Calls.md, which is also a chapter of the manual.
#fren_md "Lang/Calls.md"
