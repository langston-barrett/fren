-- keep-sorted start
import FrenCli.Confirm
-- keep-sorted end

/-! Tests of the evaluator's copying budget (`Reqs/Eval#expansion-limit`).
In particular a shared expression is charged at every occurrence, before
a traversal expands its sharing into copies. -/

namespace FrenTest.Expansion

open FrenCli FrenCli.Eval
open Fren.Core (expansionBudget)

-- Empty work needs no budget; a node needs exactly one unit.
#guard expansionBudget (fun (_ : Nat) => []) 0 [] == some 0
#guard expansionBudget (fun (_ : Nat) => []) 0 [0] == none
#guard expansionBudget (fun (_ : Nat) => []) 1 [0] == some 0

-- The two identical children are separate visits, even when shared.
def children : Nat → List Nat
  | 0 => []
  | n + 1 => [n, n]

#guard expansionBudget children 6 [2] == none
#guard expansionBudget children 7 [2] == some 0
#guard expansionBudget children 8 [2] == some 1
-- A cyclic input must stop without trying to finish counting it.
#guard expansionBudget (fun (n : Nat) => [n]) 100 [0] == none

/-- The remaining budget after reserving a copy, without changing it. -/
def leftAfter (n : Nat) (e : Ex) : Option Nat :=
  ((copying e id).run { expansionLeft := n }).toOption.map (·.2.expansionLeft)

def leaf : Ex := .bound `x

-- `children` used by semantic queries omits strict arguments. Copying
-- must include them, including repetitions of the same argument.
#guard leftAfter 3 (.strict #[leaf, leaf] leaf) == none
#guard leftAfter 4 (.strict #[leaf, leaf] leaf) == some 0
-- Constants' closed bodies stay shared, even when the body is large.
#guard leftAfter 1 (.const `closed (.strict #[leaf, leaf] leaf)) == some 0

-- Higher-order substitution charges both its traversal and each closure
-- body before substitution; the latter may have shared arguments too.
def closureSubstitution (n : Nat) : Option Nat :=
  ((Ex.app `f #[leaf]).substFns [(`f, #[`x], .bin .add leaf leaf)] |>.run
    { expansionLeft := n }).toOption.map (·.2.expansionLeft)

#guard closureSubstitution 4 == none
#guard closureSubstitution 5 == some 0

/-- Starting a new source item resets the budget, including when reading
continues from the state of a previous file. -/
def resets : Bool := Id.run do
  let .ok items := readItems "fn identity(n: Int): Int := n\n".toList.toArray | return false
  let .ok st := lowerFrom { expansionLeft := 0 } #[items] {} | return false
  return st.expansionLeft < Fren.Core.maxExpansionNodes

#guard resets

/-- Expanding named predicate members temporarily changes the definition
being applied. Restoring that lexical state must not refund the copies. -/
def predicateSpends : Bool := Id.run do
  let .ok items := readItems "pub fn both?(x?) := and { first: x?, second: x? }\n".toList.toArray | return false
  let .ok st := lowerAll #[items] {} | return false
  let expression := Expr.app default #[{ name := "both?", span := default }] #[.bool default true]
  let .ok (_, after) := (lowerPredicateClauses {} expression).run { st with expansionLeft := 1000 }
    | return false
  return after.expansionLeft < 1000

#guard predicateSpends

end FrenTest.Expansion
