-- keep-sorted start
import FrenCli.Run
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

/-- Hidden locals can duplicate earlier locals, as nested function calls
can duplicate arguments. The entire substitution shares one allowance. -/
def refinementSpends (budget : Nat) : Bool := Id.run do
  let mut locals : Array (Lean.Name × Ex) := #[(`root, .lit (.int 1))]
  let mut last := `root
  for i in [0:12] do
    let name := Lean.Name.mkNum `local i
    locals := locals.push (name, .bin .add (.var last) (.var last))
    last := name
  match (inlineRefinementLocals locals (.var last)).run { expansionLeft := budget } with
  | .error (.expansionLimit _) => true
  | _ => false

#guard refinementSpends 64

-- Resource failures are structured, acquire their item's location, and
-- are the only reading failures that follow the resource acceptance rule.
#guard (ReadError.expansionLimit none).stopsCommand
#guard !(ReadError.invalid Fren.Core.expansionLimitMsg).stopsCommand
#guard
  match (ReadError.expansionLimit none).at { file := 3, span := { start := 7, stop := 11 }, path := `outer.item } with
  | .expansionLimit (some site) => site.file == 3 && site.span.start == 7 && site.path == `outer.item
  | _ => false

/-- A diamond of local definitions preserves its two variable mentions
without duplicating them exponentially. This also exercises the shape
construction that precedes the evaluator's reading. -/
def mentionSharing : Bool := Id.run do
  let path (name : String) : Expr := .path default #[{ name, span := default }]
  let mkVar (name : String) (definition : Option Expr := none) : CVar :=
    { name := .mkSimple name, role := .input, isPub := true, ty := .int, span := default, defn? := definition }
  let mut vars := #[mkVar "n", mkVar "m"]
  let mut last := "n"
  for i in [0:12] do
    let name := s!"hidden_{i}"
    let body := if i == 0 then Expr.bin default "+" (path "n") (path "m")
      else Expr.bin default "+" (path last) (path last)
    vars := vars.push (mkVar name (some body))
    last := name
  let .ok (mentions, _) := (mentionedNames { vars, place := .prop } (path last)).run {} | return false
  return mentions == [.var "n", .var "m"]

#guard mentionSharing

/-- Refinement translation shares local definitions with fresh SMT lets;
a chain has linear output size and cannot capture a caller's same-named
variable. The UI regression checks the latter semantically too. -/
def refinementSharing : Bool := Id.run do
  let mut text := "pub proc abstract_value(n: Int): (answer: Int) {\n"
  let mut last := "n"
  for i in [0:12] do
    let name := s!"hidden_{i}"
    text := text ++ s!"let {name}: Int := {last} + {last}\n"
    last := name
  text := text ++ s!"ensure value: answer = {last}\n}\n"
  text := text ++ "pub proc concrete(n: Int): (answer: Int) { out answer := n * 4096 }\nexpect probe(hidden_0: Int) { call c := concrete(hidden_0)\nrefines c abstract_value(hidden_0) }\n"
  let state := elabText {} 0 text.toList.toArray
  if state.diags.any (·.severity == .error) then return false
  let some claim := state.globals[0]?.bind fun c => c.props[0]? | return false
  return claim.smt.length < 10000 && claim.smt.contains "#refines1#local.hidden_0"

#guard refinementSharing

end FrenTest.Expansion
