import Impls.Recursion

/-! The shared termination model and generated mutual definitions for #604.
fren-covers: lang::structural_group, lang::structural_group_search
fren-covers: lang::group_member, lang::group_scope
fren-covers: lang::group_dependencies, lang::group_search_positions, lang::group_search_prefix
-/

namespace FrenTest.MutualRecursion

open Fren.Core

#guard groupMemberAccepted true false false false
#guard !groupMemberAccepted false false false false
#guard !groupMemberAccepted true true false false
#guard !groupMemberAccepted true false true false
#guard !groupMemberAccepted true false false true
#guard groupVisible ["first", "later"] 0 "later"
#guard !groupVisible ["first", "later"] 2 "later"
#guard !groupVisible ["first", "later"] (-1) "later"
#guard !groupVisible ["first", "later"] 0 "outside"
#guard groupTarget? ["first", "later"] 0 "later" == some 1
#guard groupInherited [] [] == []
#guard Id.run do
  let inherited := groupInherited [false, false, true, false]
    [{ caller := 0, callee := 1, form := .applied, args := [] },
     { caller := 1, callee := 2, form := .applied, args := [] },
     { caller := 2, callee := 0, form := .applied, args := [] }]
  return [0, 1, 2].all inherited.contains && !inherited.contains 3

private def chosen (ns : List Int) (us : List GroupUse) : Option (List Int) :=
  (recursionGroup ns us).map (List.map (·.decreasing))

-- The caller decreases at its own position, the callee at another one.
-- Non-selected arguments impose no restriction.
private def cross : List GroupUse :=
  [{ caller := 0, callee := 1, form := .applied, args := [.other, .payload 0] },
   { caller := 1, callee := 0, form := .applied, args := [.payload 1, .other] }]

-- Candidate domains and prefix rejection are production helpers, not
-- supplied validity flags. Unconstrained members have a single choice.
#guard groupPositionCount 3 [] 0 == 1
#guard groupPositionCount 0 [] 0 == 0
#guard groupPositionCount (-1) [] 0 == 0
#guard groupPositionCount 3 cross 0 == 3
#guard groupPositionCount 3 cross 2 == 1
#guard groupPrefixCompatible [] cross
#guard groupPrefixCompatible [{ count := 2, decreasing := 0 }] cross
#guard !groupPrefixCompatible [{ count := 2, decreasing := 0 }, { count := 2, decreasing := 0 }] cross
#guard groupPrefixCompatible [{ count := 2, decreasing := 0 }, { count := 2, decreasing := 1 }] cross
#guard !groupPrefixCompatible [] (cross.map fun u => { u with form := .inClosure })

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

-- Generated declarations reduce through both members in Lean itself.
namespace FrenTest.MutualDefinitions
open Fren.Lang

mod mutual_definitions

pub enum MutualTree { End, Next(MutualTree) }
mutual {
  pub fn mutual_first(t: MutualTree): Int := match t {
    MutualTree::End => 0,
    MutualTree::Next(rest) => 1 + mutual_later(rest),
  }
  pub fn mutual_later(t: MutualTree): Int := match t {
    MutualTree::End => 0,
    MutualTree::Next(rest) => 1 + mutual_first(rest),
  }
}

example : mutual_definitions.mutual_first
    (mutual_definitions.MutualTree.Next
      (mutual_definitions.MutualTree.Next mutual_definitions.MutualTree.End)) = 2 := rfl

set_option fren.lint.undecidable "allow" in
pub fn outside_helper(x: Int): Int :=
  if (forall (i: Int), when 0 <= i < x, i >= 0) then 0 else 1

set_option fren.lint.unused_variables "allow" in
mutual {
  pub fn inherited_first(t: MutualTree, x: Int): Int := match t {
    MutualTree::End => 0,
    MutualTree::Next(rest) => inherited_later(rest, x),
  }
  pub fn inherited_later(t: MutualTree, x: Int): Int := match t {
    MutualTree::End => outside_helper(x),
    MutualTree::Next(rest) => inherited_first(rest, x),
  }
  pub fn isolated(t: MutualTree): Int := 0
}

run_cmd do
  let state ← Fren.getState
  unless state.outsideCoreItems.contains `mutual_definitions.inherited_first &&
      state.outsideCoreItems.contains `mutual_definitions.inherited_later &&
      !state.outsideCoreItems.contains `mutual_definitions.isolated do
    Lean.throwError "group core classification did not follow the call graph"
  let env ← Lean.getEnv
  for (name, expected) in [(`inherited_first, true), (`inherited_later, true), (`isolated, false)] do
    let some info := state.defined.get? (`mutual_definitions ++ name)
      | Lean.throwError "missing group definition {name}"
    unless Lean.isNoncomputable env info.decl == expected do
      Lean.throwError "group computability did not follow the call graph at {name}"

end FrenTest.MutualDefinitions
