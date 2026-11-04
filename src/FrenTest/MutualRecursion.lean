import Impls.Recursion

/-! The termination model for #604, before surface groups are enabled.
fren-covers: lang::structural_group, lang::structural_group_search -/

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

-- Keep the singleton rule and the precise first-failure diagnostics. Each
-- argument has all four origins, with applications in and outside closures
-- and passed functions. This includes no common position across uses.
private def oldRecursion (n : Nat) (uses : List RecUse) : Recursion :=
  if uses.isEmpty then .notRecursive
  else match (List.range n).find? (firstFailure uses · |>.isNone) with
    | some i => .structural i
    | none =>
      let fs := (List.range n).map fun i => (firstFailure uses i).getD 0
      let k := fs.foldl max 0
      .notStructural k (fs.idxOf k)

private def allUses : List RecUse := do
  let form ← [.applied, .inClosure, .passed]
  let a ← [.payload, .itself, .name, .expr]
  let b ← [.payload, .itself, .name, .expr]
  pure { form, args := [a, b] }

#guard ([0, 1, 2, 3].all fun n =>
  selfRecursion n [] == oldRecursion n [] &&
  allUses.all (fun a => selfRecursion n [a] == oldRecursion n [a]) &&
  allUses.all (fun a => allUses.all fun b => selfRecursion n [a, b] == oldRecursion n [a, b]))

end FrenTest.MutualRecursion
