-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- A denied `undecidable` in a Markdown spec, caught by `#guard_msgs`, does
-- not stop a later `#fren_check` (`Reqs/View#static-errors`), but its
-- component is still never checked
-- (`Reqs/Lint/Decidability#undecidable-constructs`): only the other one is.
/--
error: LiterateUndecidable.md:9:54: this is outside the decidable core: a relational operator over a type that is not finite quantifies over its values

help: relate values of finite types, such as enums, or opt out where reachability is the point
note: `undecidable` is `deny` by default
help: to allow it, `set_option fren.lint.undecidable "allow"`
---
error: LiterateUndecidable.md:9:54: this is outside the decidable core: the solver does not reliably combine counting with relational operators

help: say what the members are, with `in` and `subset`, rather than how many there are
-/
#guard_msgs in
#fren_md "LiterateUndecidable.md"

pub proc gate(a?): (b?) { ensure same: b? iff a? }

/-- info: fren: 2 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
