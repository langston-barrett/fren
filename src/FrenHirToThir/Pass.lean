module

public import FrenModule.Core
public import FrenDiag

/-! HIR→THIR on the expression core: a pure function of an HIR module. It
reads nothing upstream (no source text, no syntax tree, no re-resolution) and
writes a THIR module whose every node carries its value type and whose
references are decided: an item in value position becomes a constructor, a
call's callee becomes a function.

Each body is typed by one fold (`Expr.fold`) whose algebra is `step`; the
carrier is a function of the typing context, so a `let` body is run in the
extended context. The algebra runs children left to right and checks each as
soon as it is typed, so the first error is at a determined node. -/

public section
namespace FrenHirToThir.Pass

open FrenExpr FrenModule.Core

/-- Why typing failed. -/
inductive Reason where
  | mismatch (expected found : Ty)
  /-- An item in value position that is not a constructor. -/
  | notValue (id : FrenBase.ItemId)
  /-- A callee that is a local, or an item that is not a function. -/
  | notCallable (callee : Ref)
  | arity (expected found : Nat)
  | danglingLocal (index : Nat)
  | matchNotEnum (found : Ty)
  | emptyMatch
  | patternNotConstructor (id : FrenBase.ItemId)
  /-- A parameter without a written type and without the `?` suffix. -/
  | missingAnnotation
  deriving Repr, BEq, DecidableEq

/-- A type error: the item and the origin (in that item's table) it blames. -/
structure TypeError where
  item : FrenBase.ItemId
  origin : OriginId
  reason : Reason
  deriving Repr, BEq, DecidableEq

abbrev Result := Except TypeError

/-- What one body's typing reads: its item, the module's function signatures
and constructor owners. -/
structure Env where
  item : FrenBase.ItemId
  signatures : Array (FrenBase.ItemId × Array Ty × Ty)
  ctorOwner : FrenBase.ItemId → Option FrenBase.ItemId

/-- Local types, nearest first (index zero is the nearest binder). -/
abbrev Ctx := List Ty

/-- The fold's carrier: a typed body as a function of its context. -/
abbrev Typing := Ctx → Result (Expr .thir)

namespace Env

def fail (env : Env) (o : OriginId) (r : Reason) : Result α := .error ⟨env.item, o, r⟩

def expect (env : Env) (o : OriginId) (expected found : Ty) : Result Unit :=
  if found.compatible expected then .ok () else env.fail o (.mismatch expected found)

def signature (env : Env) (id : FrenBase.ItemId) : Option (Array Ty × Ty) :=
  (env.signatures.find? (·.1 == id)).map (·.2)

def ctorType (env : Env) (id : FrenBase.ItemId) : Option Ty := (env.ctorOwner id).map .enum

end Env

private def node (o : OriginId) (ty : Ty) (n : ExprF .thir (Expr .thir)) : Expr .thir := ⟨o, ty, n⟩

private theorem thirTyped : Phase.Typed .thir := by decide
private theorem thirSurface : Phase.Surface .thir := Or.inr rfl

/-- The typing algebra. Children are suspended `Typing`s, run here in written
order; every check runs as soon as the child it concerns is typed. -/
def step (env : Env) (o : OriginId) (_ : Ann .hir) (n : ExprF .hir Typing) : Typing := fun ctx =>
  match n with
  | .bool v => pure (node o .bool (.bool v))
  | .int v => pure (node o .int (.int v))
  | .var i => match ctx[i]? with
    | some ty => pure (node o ty (.var i))
    | none => env.fail o (.danglingLocal i)
  | .item _ id => match env.ctorType id with
    | some ty => pure (node o ty (.ctor thirTyped id))
    | none => env.fail o (.notValue id)
  | .ctor g _ => absurd g (by decide)
  | .call g _ _ => absurd g (by decide)
  | .apply _ callee args => do
    let (fn, params, result) ← match callee with
      | .item id => match env.signature id with
        | some (params, result) => pure (id, params, result)
        | none => env.fail o (.notCallable callee)
      | .local _ => env.fail o (.notCallable callee)
    unless args.size == params.size do env.fail o (.arity params.size args.size)
    let mut out := #[]
    for h : i in [:args.size] do
      let arg ← args[i] ctx
      env.expect arg.origin (params[i]?.getD .bool) arg.ann
      out := out.push arg
    pure (node o result (.call thirTyped fn out))
  | .unary op e => do
    let e ← e ctx
    let some ty := FrenExpr.unary op e.ann
      | env.fail e.origin (.mismatch (unaryOperand op) e.ann)
    pure (node o ty (.unary op e))
  | .binary op l r => do
    let l ← l ctx
    let expected : Ty := binaryOperand op l.ann
    env.expect l.origin expected l.ann
    let r ← r ctx
    let some ty := FrenExpr.binary op l.ann r.ann
      | env.fail r.origin (.mismatch expected r.ann)
    pure (node o ty (.binary op l r))
  | .ite c y n => do
    let c ← c ctx
    env.expect c.origin .bool c.ann
    let y ← y ctx
    let n ← n ctx
    env.expect n.origin y.ann n.ann
    pure (node o y.ann (.ite c y n))
  | .letE b v body => do
    let v ← v ctx
    if b.suffix then env.expect b.origin .bool v.ann
    let body ← body (v.ann :: ctx)
    pure (node o body.ann (.letE b v body))
  | .matchE s arms => do
    let s ← s ctx
    let .enum _ := s.ann | env.fail s.origin (.matchNotEnum s.ann)
    let mut common : Option Ty := none
    let mut out := #[]
    for (pat, body) in arms do
      let some pt := env.ctorType pat.ctor | env.fail pat.origin (.patternNotConstructor pat.ctor)
      env.expect pat.origin s.ann pt
      let body ← body ctx
      match common with
      | some expected => env.expect body.origin expected body.ann
      | none => common := some body.ann
      out := out.push (pat, body)
    let some ty := common | env.fail o .emptyMatch
    pure (node o ty (.matchE s out))
  | .paren _ e => do
    let e ← e ctx
    pure (node o e.ann (.paren thirSurface e))

/-- Type one body against its expected result type. -/
def typeBody (env : Env) (ctx : Ctx) (expected : Ty) (body : Expr .hir) : Result (Expr .thir) := do
  let out ← Expr.fold (step env) body ctx
  env.expect out.origin expected out.ann
  pure out

/-- The `?` suffix requires `Bool`; an unwritten type requires the suffix. -/
def checkParams (item : FrenBase.ItemId) (params : Array Param) : Result Unit := do
  for q in params do
    unless q.annotated || q.suffix do throw ⟨item, q.origin, .missingAnnotation⟩
    if q.suffix && q.type != .bool then throw ⟨item, q.origin, .mismatch .bool q.type⟩

/-- Parameters extend the context in written order: the last is index zero. -/
def paramContext (params : Array Param) : Ctx := params.toList.reverse.map (·.type)

/-- Type a whole module: every signature first, in declaration order, then
every body in declaration order (unused functions and every member included). -/
def typeModule (m : Hir) : Result Thir := do
  for item in m.items do
    match item with
    | .function f _ => checkParams f.id f.params
    | .check c _ => checkParams c.id c.params
    | .enum _ _ => pure ()
  let signatures := m.functions.map fun f => (f.id, f.params.map (·.type), f.result)
  let ctorOwner := m.ctorOwner
  let items ← m.items.mapM fun
    | .enum e os => pure (.enum e os)
    | .function f os => do
      let env : Env := ⟨f.id, signatures, ctorOwner⟩
      let body ← typeBody env (paramContext f.params) f.result f.body
      pure (.function {f with body} os)
    | .check c os => do
      let env : Env := ⟨c.id, signatures, ctorOwner⟩
      let members ← c.members.mapM fun mem => do
        pure {mem with body := ← typeBody env (paramContext c.params) .bool mem.body}
      pure (.check {c with members} os)
  pure ⟨m.id, items⟩

/-- The span a type error blames, from the item's origin table. -/
def TypeError.span (m : Module E) (e : TypeError) : Option FrenSource.Span := do
  let item ← m.items.find? (·.id == e.item)
  let origin ← item.origins[e.origin]?
  origin.span

/-- Render as the existing walking diagnostics do: a mismatch is `F0304`. -/
def TypeError.headline : TypeError → String
  | ⟨_, _, .mismatch expected found⟩ =>
    s!"type mismatch: expected `{expected.display}`, found `{found.display}`"
  | ⟨_, _, .notValue id⟩ => s!"`{id.render}` is not a value"
  | ⟨_, _, .notCallable (.item id)⟩ => s!"`{id.render}` is not a function"
  | ⟨_, _, .notCallable (.local _)⟩ => "a local variable is not a function"
  | ⟨_, _, .arity expected found⟩ => s!"expected {expected} arguments, found {found}"
  | ⟨_, _, .danglingLocal i⟩ => s!"local index {i} has no binder"
  | ⟨_, _, .matchNotEnum found⟩ => s!"match requires an enum, found `{found.display}`"
  | ⟨_, _, .emptyMatch⟩ => "cannot infer an empty match result"
  | ⟨_, _, .patternNotConstructor id⟩ => s!"`{id.render}` is not a constructor"
  | ⟨_, _, .missingAnnotation⟩ => "omitted annotation requires a Bool suffix"

def TypeError.code : TypeError → Option String
  | ⟨_, _, .mismatch _ _⟩ => some "F0304"
  | _ => none

/-- A diagnostic, when the blamed origin has a span. -/
def TypeError.diagnostic (m : Module E) (e : TypeError) : Option FrenDiag.Diagnostic :=
  (e.span m).map fun span => ⟨e.code, e.headline, span⟩

end FrenHirToThir.Pass
