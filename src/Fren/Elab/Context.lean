-- keep-sorted start
import Fren.Elab.Syntax
-- keep-sorted end

/-! # Hosted elaboration: context -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Comps -/

/-- The placeholder of the abstract type or function at `path`. -/
def placeholderOf (path : Name) : TermElabM AbstractInfo := do
  let some a := (← getState).abstracts.get? path | throwError "internal error: unknown abstract item `{path}`"
  return a

/-- A binder of a `match` pattern, a quantifier's bound name, or a name of a
`let` or `where` (`isDef`), in scope. -/
structure MatchBinder where
  name : Name
  /-- Its value: the selector applied to the scrutinee, the local of the
  `have` that defines the name, or for a bound name, a local that each
  instance replaces with a value. -/
  term : Term
  type : Expr
  /-- Its scrutinee or definition, and the number of binders in scope
  there: mentioning it counts as mentioning what that mentions. A bound
  name has none, and mentions nothing. -/
  scrutinee : Option Syntax
  outer : Nat
  isDef : Bool := false
  /-- For a name, its written type, which is expected of its definition. -/
  annot? : Option Core.Ty := none
  /-- For a name, the indexes of its definition, each with the term that it
  is in range, guarded only within the definition: a mention puts them
  under its own guards (`Reqs/Lang/Let#meaning`). -/
  obligations : Array (Syntax × Term) := #[]
  /-- Likewise, the questions about the rows of its definition's tables. -/
  tableObligations : Array (Syntax × Core.TableGoal × Term) := #[]
  /-- A bound name of a type that is not listed, of an unbounded quantifier,
  which Lean's `∀` or `∃` binds: within the body, it mentions itself, as a
  variable does. -/
  unbounded : Bool := false
  /-- A closure's parameter, which its `fun` binds: what an `Expr` within
  its body mentions of it is closed over it, as of a definition
  (`quantTerm`). -/
  closure : Bool := false
  /-- For a binder in a defined function's body, the position of the
  parameter that it is bound from a payload of, directly or nested
  (`lang::structural_recursion`). -/
  payloadOf? : Option Nat := none

/-- A clause of the contract of the function at `path`, whose parameters
are `params`: whether it is a postcondition (`lang::contract_application`). -/
structure ContractCx where
  path : Name
  post : Bool
  params : Array Name
  deriving Inhabited

/-- What expression translation needs to know about the comp. -/
structure ExprCtx where
  modName : Name
  vars : Array Var
  /-- The procedure's calls, in order. -/
  insts : Array Name
  place : Core.Place
  /-- For a binding, the index of its call. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array MatchBinder := #[]
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a defined function's body, if it may recurse
  (`lang::structural_recursion`): its parameters' names, its type, and the
  local that stands for it. -/
  selfRec? : Option (Array Name × Core.FnTy × Term) := none
  /-- In a higher-order function's body or contract, its function
  parameters: each one's name, type and term
  (`Reqs/Lang/HigherOrder#function-parameters`). -/
  fnParams : Array (Name × Core.FnTy × Term) := #[]
  /-- In a closure's body, which applies no uninterpreted function. -/
  inClosure : Bool := false
  /-- In a clause of a function's contract, the function. -/
  contract? : Option ContractCx := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- Something here gives `{}` its type (`Reqs/Lang/Expressions#sets`). -/
  emptyOk : Bool := false
  /-- The Fren type expected here, as the `fren` command's `expected?`: a
  declared type, or a sibling's. Only parentheses, a conditional's branches
  and a `match`'s arms pass it on; `{}` and `[]` check themselves against
  it (`Reqs/Lang/Types#checking-and-synthesis`). -/
  expected? : Option Core.Ty := none
  /-- A `Nat` is expected here, so an integer literal is one
  (`lang::literal_type`). -/
  natOk : Bool := false
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array Term := #[]
  /-- Whether to record the indexes and tables of this expression for their
  checks, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, or of `and`, whose chain
  `membership_chain` looks at from its top: that operator, or `""`. -/
  chain : String := ""
  /-- The expression this one is part of, if any: where a `match` is, for
  the match lints. -/
  parent? : Option Syntax := none
  /-- This expression is the `else` branch of an `if`, whose chain
  `if_chain_match` looks at from its top. -/
  inElse : Bool := false
  /-- In a definition of a `let` or `where`, the names of it and of the
  later definitions of its clause that hide nothing, each with whether it
  is its own: a mention of one is used before its definition
  (`lang::definition_order`). -/
  pending : Array (Name × Bool) := #[]
  /-- In a definition of a `let` or `where` that nothing mentions, which
  counts for nothing: what it may mention, linear arithmetic and the
  decidable core are not checked in it (`Reqs/Lang/Let#meaning`). -/
  unmentioned : Bool := false
  /-- What the chain of `and` that this expression is an operand of, or is,
  is a part of, for its pattern tests (`lang::test_scope`). Only `and`,
  `is` and parentheses read it, and only their operands see it. -/
  testContext : Core.TestContext := .standalone
  /-- For an operand of a chain of `and`, its position in the chain and the
  chain's number of operands. -/
  testAt? : Option (Nat × Nat) := none
  /-- The members' expressions of the guards of the quantifiers over
  elements around this expression, by where they are
  (`LocalState.elemMembers`). -/
  elemGuards : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- Within the body of a quantifier over elements: whether it is a
  `forall`; and the quantifiers that are directly its body, or the body of
  one of those (`Core.ElementNesting`). -/
  elemKind? : Option Bool := none
  elemDirect : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- The bound names of the quantifiers over elements, of the same kind,
  that this expression is directly the body of, which its quantifier may
  mention (`Core.ElementVerdict.mentionsBound`). -/
  elemChain : Array Name := #[]
  /-- Translating a defined function's body a second time, for its Lean
  definition, where a `match` is Lean's own where it can be
  (`Reqs/Generated#matches`). -/
  leanMatch : Bool := false
  /-- Translating a structural recursion's body for its Lean definition,
  where a `match` whose arms are propositions is a Lean `match` of their
  `decide`s, so that Lean's structural recursion sees through it
  (`lang::recursive_match`). -/
  leanBoolArms : Bool := false

/-- What the binder `b` is, for a declaration that hides it (`Core.bindingLocals`). -/
def MatchBinder.what (b : MatchBinder) : Name × Core.BindingKind :=
  (b.name, if b.scrutinee.isNone then .boundName else if b.isDef then .definition else .patternBinder)

def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option MatchBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : MatchBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name) ++ cx.fnParams.map (·.1)

/-- The function parameter named `n`, with its type and term, if no binder
or variable hides it (`Reqs/Lang/HigherOrder#function-parameters`). -/
def ExprCtx.fnParam? (cx : ExprCtx) (n : Name) : Option (Core.FnTy × Term) :=
  if (cx.binder? n).isSome || cx.vars.any (·.name == n) then none
  else (cx.fnParams.find? (·.1 == n)).map fun (_, t, x) => (t, x)

/-- The names that the pattern tests translated since `LocalState.bound`
had `mark` names bind. -/
def boundSince (mark : Nat) : TermElabM (Array MatchBinder) :=
  return ((← getLocal).bound.extract mark).map fun (name, term, type, sc, outer) =>
    { name, term := ⟨term⟩, type, scrutinee := some sc, outer }

/-- Runs `x`, and returns with its result the names that the pattern tests
that it translates bind (`LocalState.bound`), which it removes: those of
the condition of a `when` or `if` (`lang::test_scope`). -/
def withBound (x : TermElabM α) : TermElabM (α × Array MatchBinder) := do
  let mark := (← getLocal).bound.size
  let r ← x
  let new ← boundSince mark
  modifyLocal fun l => { l with bound := l.bound.extract 0 mark }
  return (r, new)

/-- Whether the path `p` names a variant. -/
def isVariant (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← segNames (pathSegs p)
  return (← getState).table.resolvePath cx.modName names cx.shadowing matches .ok (.variant ..)

/-- Whether the path `p`, applied, builds a variant or a newtype rather
than applying a function. -/
def isConstruction (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← segNames (pathSegs p)
  let s ← getState
  match s.table.resolvePath cx.modName names cx.shadowing with
  | .ok (.variant ..) => return true
  | .ok (.item { kind := .recordItem, path, .. }) => return s.newtypes.contains path
  | _ => return false

/-- The defined function that the path `p`, applied, applies, if any. -/
def definedFn? (cx : ExprCtx) (p : Syntax) : TermElabM (Option DefinedInfo) := do
  let names ← segNames (pathSegs p)
  let s ← getState
  let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
  return s.defined.get? path

/-- The paths of the functions that `e` applies (`unused_assumption`). -/
partial def appliedPaths (e : Syntax) : Array Syntax :=
  if e.isOfKind ``Lang.appExpr then e[2].getSepArgs.foldl (· ++ appliedPaths ·) #[e[0]]
  else e.getArgs.foldl (· ++ appliedPaths ·) #[]

/-- The uninterpreted functions that `e` applies, as links of
`unused_assumption` (`Core.fnLink`). -/
def appliedFns (cx : ExprCtx) (e : Syntax) : TermElabM (Array Name) := do
  let s ← getState
  (appliedPaths e).filterMapM fun p => do
    let some names ← try some <$> segNames (pathSegs p) catch _ => pure none | return none
    let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
    return if s.defined.contains path then none else some (Core.fnLink path)


end Fren
