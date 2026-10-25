-- keep-sorted start
import FrenCore.Regex
-- keep-sorted end

/-!
Matching by derivatives (`Fren.Core.Re.matchD`) stays fast on nested
repetitions, whose derivatives would double at each character if equal
branches of a union were kept apart.
-/

open Fren.Core

/-- A string of `n` copies of `c`, then `rest`. -/
def manyThen (n : Nat) (c : Char) (rest : String) : String := String.ofList (List.replicate n c) ++ rest

#guard Fren.Str.matches (manyThen 60 'a' "") "(a*)*"
#guard !Fren.Str.matches (manyThen 60 'a' "b") "(a*)*"
#guard Fren.Str.matches (manyThen 60 'x' "") "([a-z]+)*"
#guard !Fren.Str.matches (manyThen 60 'x' "0") "([a-z]+)*"
#guard Fren.Str.matches (manyThen 60 'a' "") "(a|a)*(a*)*"
#guard !Fren.Str.matches (manyThen 60 'a' "!") "((a*)*b)*"
