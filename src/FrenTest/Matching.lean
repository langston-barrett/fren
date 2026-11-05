-- keep-sorted start
import FrenCore.Matching
import FrenCore.Obligations
-- keep-sorted end

namespace FrenTest.Matching

open Fren.Core.Matching

def value : Term := .atom "Int:1"

-- A constant, a let, a where and a defined output all disappear. Each
-- reference is resolved in its definition's scope, before any shadowing.
def aliases : List (String × Term) :=
  [("out", .ref "where"), ("where", .ref "let"), ("let", .ref "CONST"), ("CONST", value)]

#guard same aliases (.ref "out") value
#guard same [("x", .ref "x"), ("x", value)] (.ref "x") value
#guard same [("x", .ref "free"), ("free", value)] (.ref "x") value
#guard same [("free", value), ("x", .ref "free")] (.ref "x") (.ref "free") == false
#guard normalize (definitions aliases) (.ref "missing") == .ref "missing"

-- A function's symbol, a type, an operator and argument order remain
-- syntax even if their values could be equal in an interpretation.
#guard same [("f", value)] (.app "f" .nil) value == false
#guard same [] (.atom "Int:1") (.atom "Nat:1") == false
#guard same [] (.app "+" (.cons value (.cons (.atom "Int:0") .nil))) value == false
#guard same [] (.app "f" (.cons value (.cons (.atom "Int:2") .nil)))
  (.app "f" (.cons (.atom "Int:2") (.cons value .nil))) == false
#guard same aliases (.app "f<Int>" (.cons (.ref "out") .nil)) (.app "f<Int>" (.cons value .nil))
#guard same aliases (.app "f<Int>" .nil) (.app "f<Nat>" .nil) == false

-- The lookup bound to normalization is used by both front ends' shared
-- obligations substitution too, where the first binding wins.
#guard Fren.Core.Sx.subst #[("x", .atom "first"), ("x", .atom "second")] (.atom "x") == .atom "first"

def reached (roots : List Nat) (edges : List (Nat × Nat)) (brings : Nat → Bool := fun _ => true) : Option (List Nat) :=
  (closure roots edges brings).2.map (List.map Prod.fst)

#guard reached [] [(0, 1)] == some []
#guard reached [9, 9] [] == some [9]
#guard reached [0] [(0, 1), (0, 1), (1, 2), (2, 0), (8, 9)] == some [0, 1, 2]
#guard reached [0] [(0, 1), (1, 2)] (· != 1) == some [0]

-- The reported bound comes from the same call as the traversal result.
-- Count all distinct vertices, including unreachable ones and filtered seeds.
#guard closure ([] : List Nat) [] (fun _ => true) == (1, some [])
#guard closure [9, 9] [] (fun _ => true) == (2, some [(9, ())])
#guard closure [0] [(0, 1), (0, 1), (1, 2), (2, 0), (8, 9)] (fun _ => true) ==
  (6, some [(0, ()), (1, ()), (2, ())])
#guard closure [0] [(0, 1), (1, 2)] (fun _ => false) == (4, some [])

-- More than the small bounded graphs used in examples: the final
-- frontier is processed even when it adds no vertex.
def chain : List (Nat × Nat) := (List.range 64).map fun n => (n, n + 1)
#guard reached [0] chain == some (List.range 65)
#guard (closure [0] chain (fun _ => true)).1 == 66
#guard (Fren.Core.closeApps (fun _ => true) (successors chain) 64 [0] [0] []).run == none

end FrenTest.Matching
