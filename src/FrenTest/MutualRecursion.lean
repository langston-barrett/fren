import Impls.Recursion

/-! The termination model for #604, before surface groups are enabled.
fren-covers: lang::structural_group, lang::structural_group_search
-/

namespace FrenTest.MutualRecursion

open Fren.Core

private def chosen (ns : List Int) (us : List GroupUse) : Option (List Int) :=
  (recursionGroup ns us).map (List.map (·.decreasing))

-- The caller decreases at its own position, the callee at another one.
-- Non-selected arguments impose no restriction.
private def cross : List GroupUse :=
  [{ caller := 0, callee := 1, form := .applied, args := [.other, .payload 0] },
   { caller := 1, callee := 0, form := .applied, args := [.payload 1, .other] }]

#guard chosen [2, 2] cross == some [0, 1]
#guard chosen [2, 2] (cross.reverse) == some [0, 1]
#guard chosen [2, 2] (cross ++ [{ caller := 0, callee := 0, form := .applied, args := [.payload 0] }]) == some [0, 1]
-- Every edge must agree on each member's one decreasing parameter.
#guard chosen [2, 2] (cross ++ [{ caller := 0, callee := 1, form := .applied, args := [.payload 1, .other] }]) == none
#guard chosen [2, 2] (cross.map fun u => { u with form := .inClosure }) == none
#guard chosen [2, 2] (cross.map fun u => { u with form := .passed }) == none
#guard chosen [2, 2] (cross.map fun u => { u with args := [.other, .other] }) == none

-- A longer cycle can select a different position at every member.
#guard chosen [3, 1, 2]
  [{ caller := 0, callee := 1, form := .applied, args := [.payload 2] },
   { caller := 1, callee := 2, form := .applied, args := [.other, .payload 0] },
   { caller := 2, callee := 0, form := .applied, args := [.other, .other, .payload 1] }] == some [2, 0, 1]

-- With no calls, choose the first position; all members still need one.
#guard chosen [3, 2, 1] [] == some [0, 0, 0]
#guard chosen [] [] == some []
#guard chosen [] [{ caller := 0, callee := 0, form := .applied, args := [.payload 0] }] == none
#guard chosen [0] [] == none
#guard chosen [-1] [] == none

-- Bounds are semantic, not an accidental consequence of indexing defaults.
#guard !structuralGroup [{ count := 1, decreasing := 1 }] []
#guard !structuralGroup [{ count := 1, decreasing := -1 }] []
#guard !structuralGroup [{ count := 1, decreasing := 0 }]
  [{ caller := -1, callee := 0, form := .applied, args := [.payload 0] }]
#guard !structuralGroup [{ count := 1, decreasing := 0 }]
  [{ caller := 0, callee := 1, form := .applied, args := [.payload 0] }]
#guard !structuralGroup [{ count := 1, decreasing := 0 }]
  [{ caller := 0, callee := 0, form := .applied, args := [] }]

-- The adapter keeps the first successful position and the exact failure
-- use/position. Impls.Recursion.selfRecursion_eq proves this generally.
#guard selfRecursion 3 [] == .notRecursive
#guard selfRecursion 3 [{ form := .applied, args := [.name, .payload, .payload] }] == .structural 1
#guard selfRecursion 2
  [{ form := .applied, args := [.payload, .name] },
   { form := .applied, args := [.name, .payload] }] == .notStructural 1 0
#guard selfRecursion 2
  [{ form := .applied, args := [.name, .payload] },
   { form := .applied, args := [.payload, .name] }] == .notStructural 1 1
#guard selfRecursion 2
  [{ form := .applied, args := [.payload, .payload] },
   { form := .passed }] == .notStructural 1 0

end FrenTest.MutualRecursion
