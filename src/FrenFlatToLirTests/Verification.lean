module

public import FrenFlatToLirTests.Fixtures

public section
namespace FrenFlatToLirTests
open FrenLir FrenEval

/-- Test-only structural observation, visiting BOTH branches without evaluating
any guard. This is an audit of retained scopes, not OIR condition generation. -/
structure Leaf where
  condition : Term
  origin : Option Origin
  guards : List (Term × Bool)
  binders : List (FrenAst.Token × FrenExpr.Ty × Term × Term)
  deriving Repr

def leaves : Nat → Verification → Option Origin → List (Term × Bool) →
    List (FrenAst.Token × FrenExpr.Ty × Term × Term) → List Leaf
  | 0, _, _, _, _ => []
  | n + 1, v, origin, guards, binders =>
    match v with
    | .empty => []
    | .check condition => [⟨condition, origin, guards, binders⟩]
    | .both a b => leaves n a origin guards binders ++ leaves n b origin guards binders
    | .branch condition a b =>
      leaves n a origin (guards ++ [(condition, true)]) binders ++
        leaves n b origin (guards ++ [(condition, false)]) binders
    | .letE binder ty value domain body =>
      leaves n body origin guards (binders ++ [(binder, ty, value, domain)])
    | .at o body => leaves n body (some o) guards binders

def nonzeroLeaves (b : Body) : List Leaf :=
  (leaves 400 b.term.verification none [] []).filter fun leaf => match leaf.condition with
    | .binary .ne _ (.int 0) => true | _ => false

def structuralAudit (c : Compiled) : Bool := Id.run do
  for name in ["unused", "guarded", "lazyAnd", "lazyOr", "skipped"] do
    let some b := body? c.program name | return false
    let [leaf] := nonzeroLeaves b | return false
    if !leaf.guards.isEmpty || !leaf.binders.isEmpty then return false
    let some origin := leaf.origin | return false
    if origin.owner != key name || origin.context != b.source.context then return false
    match origin.expression with
    | .binary _ token .div _ => if token.text != "div" then return false
    | _ => return false
  for (name, polarity) in [("conditional", true), ("constantBranch", true), ("safeCall", false), ("selected", true)] do
    let some b := body? c.program name | return false
    let [leaf] := nonzeroLeaves b | return false
    if leaf.guards.map Prod.snd != [polarity] || !leaf.binders.isEmpty then return false
  return true

private def editVerification : Nat → (Verification → Verification) → Verification → Verification
  | 0, _, v => v
  | n + 1, edit, v =>
    let go := editVerification n edit
    edit (match v with
      | .both a b => .both (go a) (go b)
      | .branch c a b => .branch c (go a) (go b)
      | .letE binder ty v d b => .letE binder ty v d (go b)
      | .at o b => .at o (go b)
      | other => other)

private def editTerm : Nat → (Term → Term) → Term → Term
  | 0, _, t => t
  | n + 1, edit, t =>
    let go := editTerm n edit
    edit (match t with
      | .unary op a => .unary op (go a)
      | .binary op a b => .binary op (go a) (go b)
      | .ite c a b => .ite (go c) (go a) (go b)
      | .app sig component args => .app sig component (args.map go)
      | .letE binder ty v d b => .letE binder ty (go v) (go d) (go b)
      | .at o b => .at o (go b)
      | other => other)

/-- These mutate actual retained verification nodes. The old checkpoint's
short-circuit and unused-let formulas are explicit killed mutants. -/
def verificationMutants (c : Compiled) : IO Unit := do
  let edits : List (String × Array Value × (Verification → Verification) × Bool) := [
    ("strictCall", #[.int 0], (fun v => match v with
      | .both _ (.check (.app sig .domain args)) => .check (.app sig .domain args)
      | other => other), false),
    ("guarded", #[.int 0], (fun v => match v with
      | .check (.binary .ne _ (.int 0)) => .empty
      | other => other), false),
    ("unused", #[.int 0], (fun v => match v with
      | .both _ (.letE binder ty value domain body) => .letE binder ty value domain body
      | other => other), false),
    ("lazyAnd", #[.bool false], (fun v => match v with
      | .at o (.both a b) => match o.expression with
        | .binary _ _ .and _ => .at o (.both a (.branch (.local .bool 0 .value) b .empty))
        | _ => v
      | other => other), false),
    ("lazyOr", #[.bool true], (fun v => match v with
      | .at o (.both a b) => match o.expression with
        | .binary _ _ .or _ => .at o (.both a (.branch (.local .bool 0 .value) .empty b))
        | _ => v
      | other => other), false),
    ("conditional", #[.bool false], (fun v => match v with
      | .branch _ a b => .both a b
      | other => other), true)]
  for (name, args, edit, expected) in edits do
    let some b := body? c.program name | throw (IO.userError "missing verification mutant body")
    let changed := {b with term := {b.term with verification := editVerification 400 edit b.term.verification}}
    require (changed.wellSorted c.program.mir.source) "verification mutant must retain scope/sorts/origins"
    let env := args.toList.reverse.map fun v => (v, true)
    require (observe 400 symbols env changed.term.defined == some (.bool (!expected)))
      "independent domain control accepted dropped/unguarded/trace-selected obligations"
  let some b := body? c.program "shadow" | throw (IO.userError "missing slot mutant body")
  let edit := fun t => match t with
    | .at o (.local .int 0 .value) =>
      if o.context.length == 3 then .at o (.local .int 1 .value) else t
    | other => other
  let changed := {b with term := {b.term with value := editTerm 400 edit b.term.value}}
  require (changed.wellSorted c.program.mir.source) "same-type slot mutant must remain well-sorted"
  require (observations changed #[.int 4] == some (.int 10, true)) "independent lexical-slot value"

end FrenFlatToLirTests
