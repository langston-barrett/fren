-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- An item of the Lean file, checked by a chapter that another chapter reads:
-- its message is placed at its own position, not relabelled by either
-- chapter.
comp nested_gate { in a? pub out b? req same: b? iff a? expect never: when a?, not b? }

-- The inner chapter also checks its own item and the outer chapter's, which
-- the outer chapter declares before reading it: each is named with the
-- chapter that declares it, by its path from this file, once.
/--
error: expectation `nested_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
error: chapters/LiterateOuter.md:13:11: expectation `outer::outer_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
error: chapters/LiterateInner.md:12:11: expectation `outer::inner_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/LiterateInner.md:15:0: fren: 9 passed, 3 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "chapters/LiterateOuter.md"

-- After both chapters, a check in the Lean file still places the inner
-- chapter's item by its own text.
/--
error: expectation `nested_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
error: chapters/LiterateOuter.md:13:11: expectation `outer::outer_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
error: chapters/LiterateInner.md:12:11: expectation `outer::inner_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: fren: 9 passed, 3 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
