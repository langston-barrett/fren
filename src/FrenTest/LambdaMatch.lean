-- fren-covers: lang::match_vector, lang::match_vector_coverage, lang::match_namespace
import Fren

open scoped Fren.Lang

-- Concrete frontend examples and kernel evaluation of generated matches.
#fren_md "../../test/ui/lang/lambda_match.fren"

example : area (.Square 3) = 12 := by decide
example : first_some Int .none (.some 42) = .some 42 := by decide
example : triple true false true = 0 := by decide
example : depth (.Next .Leaf) .Leaf = 1 := by decide
example : depth_right .Leaf (.Next .Leaf) = 1 := by decide
example : fork_depth (.Right (.Left .End)) .Leaf = 2 := by decide
example (x y : Shape) : compare_shapes x y = match x, y with
    | .Square a, .Square b => a + b
    | .Rect a b, _ => a + b
    | _, .Rect a b => a - b := by
  cases x <;> cases y <;> rfl

-- Compare actual vector usefulness against all four concrete worlds.
-- Each of the nine rectangles is formed from wildcard/true/false in each
-- column. The 81 pairs include correlated holes and full row coverage.
def vectorCoverageConforms : Bool := Id.run do
  let columns : Array Fren.Core.Pat := #[.wild false, .bool true, .bool false]
  let rows := columns.flatMap fun a => columns.map fun b => #[a, b]
  let accepts (p : Fren.Core.Pat) (b : Bool) := match p with
    | .wild _ => true
    | .bool a => a == b
    | _ => false
  for first in rows do
    for second in rows do
      let (sigs, ty, patterns) := Fren.Core.matchVector (fun _ => #[]) #[.bool, .bool] #[first, second]
      let uncovered := Fren.Core.useful sigs [ty] (patterns.map fun p => [p]) [.wild false]
      let actual := [false, true].any fun a => [false, true].any fun b =>
        !((accepts first[0]! a && accepts first[1]! b) || (accepts second[0]! a && accepts second[1]! b))
      if uncovered != actual then return false
  return true

#guard vectorCoverageConforms

#fren_md "../../test/ui/lang/multi_match_names.fren"
#guard !Fren.Core.identifierAccepted (Fren.Core.matchVectorPath.toString (escape := false))
example : select .A true = 0 := by decide
example : select .B false = 1 := by decide
