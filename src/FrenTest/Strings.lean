-- keep-sorted start
import FrenCore.Regex
import FrenCore.Str
-- keep-sorted end

/-!
# String methods at the edges

The same equations as `test/ui/lang/strings_edges.fren`, which the solver checks,
here against `Fren.Str`, which the evaluator and implementations use: a
mismatch between the two meanings fails one of them.
-/

open Fren.Str

#guard «at» "abc" 1 = "b"
#guard «at» "abc" 3 = "" && «at» "abc" (-1) = ""
#guard slice "abcd" 1 2 = "bc"
#guard slice "abc" 2 5 = "c"
#guard slice "abc" 3 1 = "" && slice "abc" (-1) 2 = "" && slice "abc" 0 0 = ""
#guard indexOf "abcabc" "c" 3 = 5 && indexOf "abc" "bc" 0 = 1
#guard indexOf "abc" "d" 0 = -1 && indexOf "abc" "b" (-1) = -1
#guard indexOf "abc" "" 3 = 3 && indexOf "abc" "" 4 = -1
#guard replace "abcb" "b" "x" = "axcb" && replace "abc" "d" "x" = "abc"
#guard replace "abc" "" "x" = "xabc"
#guard replaceAll "abcb" "b" "x" = "axcx" && replaceAll "aaa" "aa" "b" = "ba"
#guard replaceAll "abc" "" "x" = "abc"
#guard contains "" "" && contains "abc" ""

-- Patterns, as `test/ui/lang/patterns.fren` checks them with the solver.
#guard «matches» "aaa" "a{2,3}" && !«matches» "a" "a{2,3}" && «matches» "ab" "(a|b)+"
#guard «matches» "a.b" "a\\.b" && !«matches» "axb" "a\\.b" && «matches» "?" "\\?"
#guard «matches» "-" "[a-]" && «matches» "q" "[^a-p]" && !«matches» "a" "[^a-p]"
