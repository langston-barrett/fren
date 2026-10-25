-- keep-sorted start
import FrenTest.LiterateDep
-- keep-sorted end
open Fren.Lang

-- A nested chapter in a subdirectory of its reader, and one that it reaches
-- through `..`, are named by their paths from this file, with `..`
-- resolved. The imported item is placed at the nested chapter's check.
/--
error: chapters/deep/LiterateDeep.md:12:11: expectation `deep_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/deep/LiterateDeep.md:17:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
---
error: chapters/LiterateShared.md:9:11: expectation `shared_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/deep/LiterateDeep.md:18:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
---
error: chapters/deep/LiterateDeep.md:19:0: expectation `dep::dep_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/deep/LiterateDeep.md:19:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "chapters/LiterateReader.md"

-- A top-level chapter that checks the nested chapters' items names each by
-- the chapter that declares it, and its summaries by itself.
/--
error: chapters/deep/LiterateDeep.md:12:11: expectation `deep_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/LiterateSibling.md:4:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
---
error: chapters/LiterateShared.md:9:11: expectation `shared_gate::never` does not hold

counterexample: a? = true, b? = true
help: strengthen the requirements so that it follows, or correct the expectation
---
info: chapters/LiterateSibling.md:5:0: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_md "chapters/LiterateSibling.md"

-- A message about an item with no position is named with the chapter that
-- declares it, without a position, and placed at the check; one about the
-- Lean file's item carries no name.
/-- info: chapters/deep/LiterateDeep.md: about an item with no position -/
#guard_msgs in
run_cmd Fren.logAbout `deep_gate .missing m!"about an item with no position" .information

comp lean_gate { in a? pub out b? req same: b? iff a? }

/-- info: about an item with no position -/
#guard_msgs in
run_cmd Fren.logAbout `lean_gate .missing m!"about an item with no position" .information

-- From a chapter, the same, and placed at the outermost `#fren_md`.
/--
info: chapters/deep/LiterateDeep.md: about an item with no position
---
info: about an item with no position
-/
#guard_msgs in
#fren_md "chapters/LiterateNoPosition.md"

-- `.`, `..` and repeated separators are resolved, and the components are
-- joined with `/` on every system.
#guard Fren.relativeTo "src/T" "src/T/a/../b.md" == "b.md"
#guard Fren.relativeTo "src/T" "src/T/./a/b.md" == "a/b.md"
#guard Fren.relativeTo "src/T" "src/U/x.md" == "../U/x.md"
#guard Fren.relativeTo "src/T" "src/T/../T/a.md" == "a.md"
#guard Fren.relativeTo "src//T" "src/T//a.md" == "a.md"
#guard Fren.relativeTo "." "./a/../b.md" == "b.md"
-- A `..` that leaves the base, and one at the root, which stays there.
#guard Fren.relativeTo "src/T" "src/T/../../x.md" == "../../x.md"
#guard Fren.relativeTo "/r" "/r/../../x.md" == "../x.md"
#guard Fren.pathComponents "/../x.md" == ["", "x.md"]
-- An absolute path from a relative base shares no root with it, and is kept
-- whole; from an absolute base, it is relative.
#guard Fren.relativeTo "src/T" "/abs/x.md" == "/abs/x.md"
#guard Fren.relativeTo "/a/b" "/a/b/c.md" == "c.md"
