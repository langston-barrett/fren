-- keep-sorted start
import Fren.Literate
-- keep-sorted end
open Fren.Lang

-- A Markdown spec's fences are read as CommonMark reads them
-- (`Reqs/Markdown#code-blocks`), and the front ends report a block that is
-- never closed (`F0167`) and an info string that looks like `fren` but is
-- not (`F0168`), at the fence, as the `fren` command does in the snapshots
-- `test/cli/syntax/f0167_unclosed_block.fren` and
-- `test/cli/syntax/f0168_near_fren.fren`.
/--
error: LiterateUnclosed.md:6:0: this code block is never closed

note: a block that opens at a fence of 3 backticks closes at a line of at least 3 backticks and nothing else, so the rest of the file is part of this `fren` block
help: close it with a line of backticks
-/
#guard_msgs in
#fren_md "LiterateUnclosed.md"

-- The block after the inline code is read, and the block tagged
-- `fren,ignore` is not.
/--
error: LiterateNearFren.md:14:0: `fren,ignore` is not a kind of block that Fren reads

note: Fren reads a block whose info string is exactly `fren`, and every other block is prose
help: write `fren` to make it part of the spec
-/
#guard_msgs in
#fren_md "LiterateNearFren.md"
