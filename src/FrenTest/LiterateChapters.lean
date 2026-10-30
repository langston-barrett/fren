-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- An item of the Lean file itself, which the second chapter checks too.
proc lean_gate(a?): (b?) { ensure same: b? iff a? expect never: when a?, not b? }

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
error: LiterateFirst.md:11:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: LiterateFirst.md:18:9: the checks of `chapters::by_testing` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: LiterateFirst.md:18:9: the redundancy checks of `chapters::by_testing` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver decides them: set `fren.evidence` to `"solver"` to have them run
---
error: LiterateFirst.md:15:7: expectation `chapters::arithmetic` does not hold

counterexample: (any values)
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:36:4: expectation `chapters::fails::refines_1` does not hold

counterexample: x = 0, concrete.y = 1
help: correct the expectation, or assume what it needs
---
info: LiterateSecond.md:6:0: fren: 11 passed, 4 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "LiterateSecond.md"

-- A check in the Lean file names the chapter and its position in the text.
/--
error: expectation `lean_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:11:11: expectation `chapters::gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: LiterateFirst.md:18:9: the checks of `chapters::by_testing` set to random testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)
---
info: LiterateFirst.md:18:9: the redundancy checks of `chapters::by_testing` are not run by random testing

note: testing searches for counterexamples, not for witnesses: a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken
help: the solver decides them: set `fren.evidence` to `"solver"` to have them run
---
error: LiterateFirst.md:15:7: expectation `chapters::arithmetic` does not hold

counterexample: (any values)
help: strengthen the guarantees so that it follows, or correct the expectation
---
error: LiterateFirst.md:36:4: expectation `chapters::fails::refines_1` does not hold

counterexample: x = 0, concrete.y = 1
help: correct the expectation, or assume what it needs
---
info: fren: 11 passed, 4 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
