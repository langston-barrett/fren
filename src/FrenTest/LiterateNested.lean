-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- An item of the Lean file, checked by a chapter that another chapter reads:
-- its message is placed at its own position, not relabelled by either
-- chapter.
comp nested_gate { in a? pub out b? req same: b? iff a? expect never: when a?, not b? }

/--
error: expectation `nested_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: LiterateOuter.md:4:0: LiterateInner.md:6:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "LiterateOuter.md"
