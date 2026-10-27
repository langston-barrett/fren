-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Items named as Lean's own declarations are, declared apart from them in
-- `Fren.Generated`, and how Lean code names each (`Reqs/Generated#names`).
-- The ui test `test/ui/lang/lean_names.fren` checks both front ends.
pub enum Option! { None, Some(Int) }
pub enum Tree { Leaf, Node(Tree, Int) }
pub struct List { x: Int }
pub fn max(a: Int, b: Int): Int := a.max(b)

proc c(x: Option, t: Tree, l: List): (y: Int) {
    ensure r: y = max(l.x, 0)
    expect some: when x = Option::Some(3), x != Option::None
    expect tree: when t = Tree::Node(Tree::Leaf, 1), t != Tree::Leaf
}

#guard_msgs (drop info) in #fren_check

-- The item's declarations are in `Fren.Generated`, apart from Lean's.
/-- info: Fren.Generated.Option.Some (x0 : Int) : Fren.Generated.Option -/
#guard_msgs in #check Option.Some
/-- info: @some : {α : Type u_1} → α → _root_.Option α -/
#guard_msgs in #check @_root_.Option.some
/-- info: Fren.Generated.Tree.Node (x0 : Tree) (x1 : Int) : Tree -/
#guard_msgs in #check Tree.Node

-- `Option` alone names both Lean's and the item's, as `max` does. Lean
-- takes the one that elaborates:
#guard_msgs in example : Option := Option.None
#guard_msgs in example : Option Nat := some 1

-- Where both do, the name is ambiguous, and Lean code writes
-- `Fren.Generated.max` for the item's and `Max.max` for Lean's.
/--
error: Ambiguous term
  max
Possible interpretations:
  Fren.Generated.max 1 2 : Int

  Max.max 1 2 : Int
-/
#guard_msgs (whitespace := lax) in example : Int := max 1 2
#guard_msgs in example : Fren.Generated.max 1 2 = 2 := by simp [Fren.Generated.max]
#guard_msgs in example : Max.max (1 : Int) 2 = 2 := by decide
#guard_msgs in example : Fren.Generated.Option := Option.Some 3
#guard_msgs in example : _root_.Option Nat := some 3
#guard_msgs in example : _root_.List Nat := [1]
#guard_msgs in example : Fren.Generated.List := List.«{}» 1

-- Proofs name the generated definitions as before.
#guard_msgs in example : c.ensures (Option.Some 3) .Leaf (List.«{}» 2) 2 := by simp [fren_spec, Fren.Generated.max]

-- In a Lean namespace, an item's declarations are under it, and opened
-- there.
namespace Inner

pub enum Ordering { Lt, Eq, Gt }

#guard_msgs in example : Inner.Fren.Generated.Ordering := Ordering.Lt
#guard_msgs in example : _root_.Ordering := .lt

end Inner
