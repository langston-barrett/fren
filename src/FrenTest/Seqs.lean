-- keep-sorted start
import Fren.Seq
import FrenCore.Str
-- keep-sorted end

/-!
# Sequence methods at the edges

`Fren.Seq`'s operations on ordinary values and at SMT-LIB's edges, and, for
each method that strings share, agreement with `Fren.Str` on the sequence
of a string's characters.
-/

open Fren.Seq

/-- The sequence of integers in `l`. -/
private def ints (l : List Int) : Fren.Seq Int := ofList l

/-- The sequence of the characters of `s`. -/
private def chars (s : String) : Fren.Seq Char := ofList s.toList

-- Construction, membership and printing.
#guard (∅ : Fren.Seq Int) = ints [] && (default : Fren.Seq Int) = ints []
#guard ints [1] ++ ints [2, 3] = ints [1, 2, 3]
#guard unit (5 : Int) = ints [5]
#guard (2 : Int) ∈ ints [1, 2] && (3 : Int) ∉ ints [1, 2]
#guard reprStr (ints [1, 2]) = "[1, 2]"

-- Length and elements.
#guard len (ints []) = 0 && len (ints [1, 2, 3]) = 3
#guard nth (ints [1, 2]) 1 = 2
#guard nth (ints [1, 2]) 5 = 0 && nth (ints [1, 2]) 2 = 0 && nth (ints [1, 2]) (-1) = 0
#guard «at» (ints [1, 2]) 1 = ints [2]
#guard «at» (ints [1, 2]) 2 = ints [] && «at» (ints [1, 2]) (-1) = ints []

-- Slices.
#guard slice (ints [1, 2, 3, 4]) 1 2 = ints [2, 3]
#guard slice (ints [1, 2, 3]) 1 5 = ints [2, 3]
#guard slice (ints [1, 2, 3]) 3 1 = ints [] && slice (ints [1, 2, 3]) (-1) 2 = ints []
#guard slice (ints [1, 2, 3]) 0 0 = ints [] && slice (ints [1, 2, 3]) 0 (-1) = ints []

-- Searching.
#guard indexOf (ints [1, 2, 3, 1, 2, 3]) (ints [3]) 3 = 5 && indexOf (ints [1, 2, 3]) (ints [2, 3]) 0 = 1
#guard indexOf (ints [1, 2, 3]) (ints [4]) 0 = -1 && indexOf (ints [1, 2, 3]) (ints [2]) (-1) = -1
#guard indexOf (ints [1, 2]) (ints []) 2 = 2 && indexOf (ints [1, 2]) (ints []) 3 = -1
#guard startsWith (ints [1, 2]) (ints [1]) && startsWith (ints [1, 2]) (ints []) && !startsWith (ints [1, 2]) (ints [2])
#guard endsWith (ints [1, 2]) (ints [2]) && endsWith (ints [1, 2]) (ints []) && !endsWith (ints [1, 2]) (ints [1])
#guard !startsWith (ints [1]) (ints [1, 2]) && !endsWith (ints [2]) (ints [1, 2])
#guard contains (ints [1, 2, 3]) (ints [2, 3]) && !contains (ints [1, 2, 3]) (ints [1, 3])
#guard contains (ints []) (ints []) && contains (ints [1]) (ints []) && !contains (ints []) (ints [1])

-- Replacing, updating and reversing.
#guard replace (ints [1, 2, 3, 2]) (ints [2]) (ints [9]) = ints [1, 9, 3, 2]
#guard replace (ints [1, 2, 3]) (ints [4]) (ints [9]) = ints [1, 2, 3]
#guard replace (ints [1, 2]) (ints []) (ints [9]) = ints [9, 1, 2]
#guard replace (ints [1, 2, 3]) (ints [2, 3]) (ints []) = ints [1]
#guard update (ints [1, 2]) 1 9 = ints [1, 9]
#guard update (ints [1]) 3 9 = ints [1] && update (ints [1]) 1 9 = ints [1] && update (ints [1]) (-1) 9 = ints [1]
#guard rev (ints [1, 2, 3]) = ints [3, 2, 1] && rev (ints []) = ints []

-- Agreement with `Fren.Str` on the characters of a string.
#guard len (chars "abc") = Fren.Str.len "abc" && len (chars "") = Fren.Str.len ""
#guard (slice (chars "abcd") 1 2).toList = (Fren.Str.slice "abcd" 1 2).toList
#guard (slice (chars "abc") 2 5).toList = (Fren.Str.slice "abc" 2 5).toList
#guard (slice (chars "abc") 3 1).toList = (Fren.Str.slice "abc" 3 1).toList
#guard (slice (chars "abc") (-1) 2).toList = (Fren.Str.slice "abc" (-1) 2).toList
#guard («at» (chars "abc") 1).toList = (Fren.Str.at "abc" 1).toList
#guard («at» (chars "abc") 3).toList = (Fren.Str.at "abc" 3).toList
#guard indexOf (chars "abcabc") (chars "c") 3 = Fren.Str.indexOf "abcabc" "c" 3
#guard indexOf (chars "abc") (chars "d") 0 = Fren.Str.indexOf "abc" "d" 0
#guard indexOf (chars "abc") (chars "") 3 = Fren.Str.indexOf "abc" "" 3
#guard indexOf (chars "abc") (chars "") 4 = Fren.Str.indexOf "abc" "" 4
#guard indexOf (chars "abc") (chars "b") (-1) = Fren.Str.indexOf "abc" "b" (-1)
#guard startsWith (chars "abc") (chars "ab") = Fren.Str.startsWith "abc" "ab"
#guard startsWith (chars "abc") (chars "b") = Fren.Str.startsWith "abc" "b"
#guard endsWith (chars "abc") (chars "bc") = Fren.Str.endsWith "abc" "bc"
#guard endsWith (chars "abc") (chars "b") = Fren.Str.endsWith "abc" "b"
#guard contains (chars "abc") (chars "bc") = Fren.Str.contains "abc" "bc"
#guard contains (chars "abc") (chars "ac") = Fren.Str.contains "abc" "ac"
#guard contains (chars "") (chars "") = Fren.Str.contains "" ""
#guard (replace (chars "abcb") (chars "b") (chars "x")).toList = (Fren.Str.replace "abcb" "b" "x").toList
#guard (replace (chars "abc") (chars "d") (chars "x")).toList = (Fren.Str.replace "abc" "d" "x").toList
#guard (replace (chars "abc") (chars "") (chars "x")).toList = (Fren.Str.replace "abc" "" "x").toList
