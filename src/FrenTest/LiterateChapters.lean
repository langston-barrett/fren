-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- An item of the Lean file itself, which the second chapter checks too.
comp lean_gate { in a? pub out b? ensure same: b? iff a? expect never: when a?, not b? }

-- A check in one chapter places a message about another chapter's comp,
-- global expectation, refinement or item set to testing by that chapter's text: its file
-- and line are the first chapter's, not the second's (#17).
#guard_msgs in
#fren_md "LiterateFirst.md"

-- The Lean file's item is placed at its own position, not the chapter's.
/--
error: expectation `lean_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:14:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: LiterateFirst.md:21:9: the checks of `chapters::by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
error: LiterateFirst.md:18:7: expectation `chapters::arithmetic` does not hold

counterexample: (any values)
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:46:7: expectation `chapters::fails::below` does not hold

counterexample: x = 0, precise.x = 0, precise.y = 1
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: LiterateSecond.md:6:0: fren: 10 passed, 4 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "LiterateSecond.md"

-- A check in the Lean file names the chapter and its position in the text.
/--
error: expectation `lean_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:14:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: LiterateFirst.md:21:9: the checks of `chapters::by_testing` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
error: LiterateFirst.md:18:7: expectation `chapters::arithmetic` does not hold

counterexample: (any values)
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:46:7: expectation `chapters::fails::below` does not hold

counterexample: x = -1, precise.x = -1, precise.y = 0
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: fren: 10 passed, 4 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
