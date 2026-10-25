-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- A check in one chapter places a message about another chapter's item by
-- that chapter's text: its file and line are the first chapter's, not the
-- second's (#17).
#guard_msgs in
#fren_md "LiterateFirst.md"

/--
error: LiterateFirst.md:14:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: LiterateSecond.md:6:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "LiterateSecond.md"

-- A check in the Lean file names the chapter and its position in the text.
/--
error: LiterateFirst.md:14:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
