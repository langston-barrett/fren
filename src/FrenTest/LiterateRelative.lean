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

-- `.` and `..` are resolved, and the result is built from components, with
-- the system's separator.
#guard Fren.relativeTo "src/T" "src/T/a/../b.md" == System.mkFilePath ["b.md"]
#guard Fren.relativeTo "src/T" "src/T/./a/b.md" == System.mkFilePath ["a", "b.md"]
#guard Fren.relativeTo "src/T" "src/U/x.md" == System.mkFilePath ["..", "U", "x.md"]
#guard Fren.relativeTo "src/T" "src/T/../T/a.md" == System.mkFilePath ["a.md"]
