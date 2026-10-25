-- keep-sorted start
import FrenTest.LiterateDep
-- keep-sorted end
open Fren.Lang

-- An imported item's syntax has positions in another module's text, which
-- neither this file nor a chapter has, so a message about it is placed at the
-- check: from a chapter, at the chapter's `#fren_check`.
/--
error: LiterateImported.md:4:0: expectation `dep::dep_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: LiterateImported.md:4:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "LiterateImported.md"

-- And from the Lean file, at its `#fren_check`.
/--
error: expectation `dep::dep_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check dep::dep_gate
