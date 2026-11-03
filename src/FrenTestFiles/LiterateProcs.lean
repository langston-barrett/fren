-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- `proc_without_outputs` counts the paths of each file apart, a spec read
-- by `#fren_md` among them, and each file's procedures wait for its own
-- end. A procedure of the Lean file that only a later item calls is not
-- reported at a chapter read in between, nor is a chapter's procedure that
-- only its later item calls reported at the chapter it reads in between.
-- So nothing is reported here, and nothing at the end of the file.
set_option fren.lint.proc_without_outputs "warn"

proc lean_claim(x: Int) { expect e: x + 1 > x }

#guard_msgs in
#fren_md "chapters/LiterateProcsOuter.md"

pub proc lean_caller(x: Int): (y: Int) {
    call c := lean_claim(x)
    out y := x
}
