-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- A setting of the Lean file is in effect at the items of a chapter it
-- reads, so `unused_lint_setting` does not report it; the chapter's own
-- settings are told apart from the Lean file's, so its unused one is still
-- reported.
set_option fren.lint.upper_case_acronyms "allow"

/--
warning: chapters/LiterateSettings.md:14:0: this lint setting is in effect at no item

help: remove this `set_option`
help: `fren fix` can fix this
note: `unused_lint_setting` is `warn` by default
help: to allow it, `set_option fren.lint.unused_lint_setting "allow"`
-/
#guard_msgs in
#fren_md "chapters/LiterateSettings.md"

-- A chapter's setting that replaces the reader's before any item is named
-- in the message about the reader's.
/--
warning: chapters/LiterateReplacing.md:7:0: this lint setting is replaced before any item

note: `set_option fren.lint.dead_code "allow"` replaces it before any item
note: `set_option fren.lint.dead_code "allow"` undoes this `deny`: `dead_code` is not an error at the items that follow
help: remove this `set_option`
help: `fren fix` can fix this
note: `unused_lint_setting` is `warn` by default
help: to allow it, `set_option fren.lint.unused_lint_setting "allow"`
-/
#guard_msgs in
#fren_md "chapters/LiterateReplacing.md"
