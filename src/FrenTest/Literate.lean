-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- `#fren_md` positions messages in the Markdown file.
/--
error: Literate.md:15:11: expectation `lit::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: Literate.md:18:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "Literate.md"

-- A Markdown file with no `fren` blocks is an empty spec.
#guard_msgs in
#fren_md "LiterateProse.md"
