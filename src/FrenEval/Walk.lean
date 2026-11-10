module

public import FrenEval.Program

public section
namespace FrenEval
open FrenAst FrenModule

inductive Failure where
  | undefined (span : FrenSource.Span) (operator : BinaryOp)
  | exhausted (span : FrenSource.Span)
  | invalid (span : FrenSource.Span) (detail : String)
  | unsupported (span : FrenSource.Span) (detail : String)
  deriving Repr, BEq

abbrev Outcome := Except Failure Value
/-- Let slots retain outcomes in the incoming lexical environment. A failure
is propagated only when its slot is read; parameters start as successful slots. -/
abbrev Environment := FrenBase.Binding.Context Outcome

/-- The actual binary demand decision, before visiting the right expression.
Only and/or with a deciding Boolean left value skip that visit. -/
@[expose] def shortCircuit : BinaryOp → Value → Option Value
  | .and, .bool false => some (.bool false)
  | .or, .bool true => some (.bool true)
  | _, _ => none

theorem shortCircuit_and_false : shortCircuit .and (.bool false) = some (.bool false) := rfl
theorem shortCircuit_or_true : shortCircuit .or (.bool true) = some (.bool true) := rfl

theorem shortCircuit_strict (op : BinaryOp) (v : Value)
    (ha : op ≠ .and) (ho : op ≠ .or) : shortCircuit op v = none := by
  cases op <;> cases v <;> simp_all [shortCircuit]

private def spanOf (t : Typed) (e : Expr) : FrenSource.Span :=
  (FrenHirToThir.anchor e t.resolved.scope.name).span

private def primitive (span : FrenSource.Span) (op : BinaryOp) (r : PrimitiveResult) : Outcome :=
  r.mapError fun
    | .undefined => .undefined span op
    | .operands => .unsupported span "primitive operand types"

/-- Positional arguments are reversed once to match nearest-first contexts.
No caller environment is part of this operation. -/
def arguments (t : Typed) (body : TypedBody) (values : Array Value) : Except Failure Environment := do
  let span := spanOf t body.expression
  unless values.size == body.context.length do
    throw (.invalid span s!"expected {body.context.length} arguments, found {values.size}")
  let slots := body.context.reverse.toArray
  for i in [:values.size] do
    let some value := values[i]? | throw (.invalid span "missing argument")
    let some (token, ty) := slots[i]? | throw (.invalid span "missing parameter")
    unless value.type == ty && value.valid t do
      throw (.invalid token.span s!"argument {i + 1} requires a valid {ty.display} value")
  return values.toList.reverse.map Except.ok

private def checked (t : Typed) (body : TypedBody) (value : Value) : Outcome :=
  if value.type = body.type ∧ value.valid t = true then .ok value
  else .error (.unsupported (spanOf t body.expression) "result disagrees with retained body type")

private theorem checked_type (t : Typed) (body : TypedBody) (input output : Value)
    (h : checked t body input = .ok output) : output.type = body.type ∧ output.valid t = true := by
  unfold checked at h
  split at h
  · rename_i good
    cases Except.ok.inj h
    exact good
  · contradiction

/-- One unit per visited expression, including entry into a callee body.
Siblings each receive the remaining depth; this is not a total step budget.
All branches of this function terminate structurally on depth. -/
def walk : Nat → Typed → TypedBody → Environment → Expr → Outcome
  | 0, t, _, _, e => .error (.exhausted (spanOf t e))
  | depth + 1, t, body, env, e => do
    let visit := fun slots child => walk depth t body slots child
    let span := spanOf t e
    match e with
    | .bool _ b => return .bool b
    | .integer _ n => return .int n
    | .name path =>
      let some ref := t.resolved.referenceAt path.head.slice
        | throw (.unsupported span "missing resolved occurrence")
      match ref.target with
      | .local index =>
        let some value := FrenBase.Binding.lookup env index
          | throw (.invalid span s!"missing local slot {index}")
        value
      | .item id =>
        let some (.enum owner) := FrenHirToThir.constructorType t.resolved id
          | throw (.unsupported span "callable designator is not a value")
        return .enum owner id
      | _ => throw (.unsupported span "type designator is not a value")
    | .paren _ child _ => visit env child
    | .unary token op child =>
      (unary op (← visit env child)).mapError (fun _ => .unsupported token.span "unary operand type")
    | .binary left token op right =>
      let l ← visit env left
      match shortCircuit op l with
      | some value => return value
      | none => primitive token.span op (binary op l (← visit env right))
    | .ifE _ condition _ yes _ no =>
      let .bool selected ← visit env condition
        | throw (.unsupported span "non-Boolean condition")
      visit env (if selected then yes else no)
    | .letE _ _ _ value _ rest =>
      -- Bind the complete outcome, not a monadically demanded value. The
      -- definition uses the incoming slots and this edge's remaining depth.
      let outcome := visit env value
      visit (outcome :: env) rest
    | .matchE _ scrutinee _ arms _ =>
      let .enum _ ctor ← visit env scrutinee
        | throw (.unsupported span "non-enum scrutinee")
      let some (_, _, arm, _) := FrenHirToThir.selectArm arms
          (fun (pattern, _, _, _) => FrenHirToThir.patternConstructor t.resolved pattern) ctor
        | throw (.unsupported span "no arm for canonical constructor")
      visit env arm
    | .call callee _ args _ _ =>
      -- A callable occurrence supplies a signature, never an evaluated Value.
      let some (.callable sig) := FrenHirToThir.occurrenceType body callee
        | throw (.unsupported (spanOf t callee) "callee is not a callable designator")
      let some target := t.bodies.find? (fun b => b.owner == sig.id && b.member.isNone)
        | throw (.unsupported span "missing resolved function body")
      let mut values := #[]
      for arg in args do values := values.push (← visit env arg)
      let slots ← arguments t target values
      checked t target (← walk depth t target slots target.expression)

/-- The Language's false-and/true-or facts constrain the actual recursive
walker, for any right expression (including failures and exhaustion). -/
theorem walk_and_false (depth : Nat) (t : Typed) (body : TypedBody) (env : Environment)
    (left right : Expr) (token : FrenAst.Token)
    (h : walk depth t body env left = .ok (.bool false)) :
    walk (depth + 1) t body env (.binary left token .and right) = .ok (.bool false) := by
  simp [walk, h, shortCircuit, Bind.bind, Except.bind, pure, Except.pure]

theorem walk_or_true (depth : Nat) (t : Typed) (body : TypedBody) (env : Environment)
    (left right : Expr) (token : FrenAst.Token)
    (h : walk depth t body env left = .ok (.bool true)) :
    walk (depth + 1) t body env (.binary left token .or right) = .ok (.bool true) := by
  simp [walk, h, shortCircuit, Bind.bind, Except.bind, pure, Except.pure]

/-- Reading a resolved local returns its complete stored outcome, including
all failure constructors and their original provenance. -/
theorem walk_local (depth : Nat) (t : Typed) (body : TypedBody) (env : Environment)
    (path : FrenAst.Path) (ref : Reference) (index : Nat) (outcome : Outcome)
    (hr : t.resolved.referenceAt path.head.slice = some ref) (ht : ref.target = .local index)
    (hv : FrenBase.Binding.lookup env index = some outcome) :
    walk (depth + 1) t body env (.name path) = outcome := by
  simp [walk, hr, ht, hv]

/-- Strict operators propagate the exact right failure once the left succeeds;
this includes iff and equality/inequality, unlike and/or's skipped cases. -/
theorem walk_strict_failure (depth : Nat) (t : Typed) (body : TypedBody) (env : Environment)
    (left right : Expr) (token : FrenAst.Token) (op : BinaryOp) (value : Value) (failure : Failure)
    (hl : walk depth t body env left = .ok value) (hs : shortCircuit op value = none)
    (hr : walk depth t body env right = .error failure) :
    walk (depth + 1) t body env (.binary left token op right) = .error failure := by
  simp [walk, hl, hs, hr, Bind.bind, Except.bind]

/-- This is the Language's let outcome-binding equation, at the explicitly
chosen operational depth. No failure of the definition is raised at binding. -/
theorem walk_let (depth : Nat) (t : Typed) (body : TypedBody) (env : Environment)
    (keyword name assign inside : FrenAst.Token) (value rest : Expr) :
    walk (depth + 1) t body env (.letE keyword name assign value inside rest) =
      walk depth t body (walk depth t body env value :: env) rest := by
  rw [walk]

structure Request where
  owner : FrenBase.ItemId
  member : Option String := none
  deriving Repr, BEq

/-- Retained body identity includes the full original member (assume/expect,
label and spans). A Boolean here is a concrete value, never a solver verdict. -/
structure Evaluation where
  body : TypedBody
  outcome : Outcome
  deriving Repr

/-- Derived convenience depth, not a proof of universal evaluation completeness.
The multiplier comes from the actual signature count. Static graph/coverage
correspondence and this bound's sufficiency remain open. -/
def defaultDepth (p : Program) : Nat :=
  (p.typed.bodies.foldl (fun n b => max n (b.expression.tokens.length + 1)) 1) *
    (p.typed.signatures.size + 1)

def evaluate (p : Program) (request : Request) (values : Array Value)
    (depth : Nat := defaultDepth p) : Except Failure Evaluation := do
  let t := p.typed
  let some body := t.bodies.find? (fun b =>
      b.owner == request.owner && b.member.map (·.label.text) == request.member)
    | throw (.invalid t.resolved.scope.name.span "requested body/check member not found")
  let outcome := do
    let env ← arguments t body values
    checked t body (← walk depth t body env body.expression)
  return ⟨body, outcome⟩

theorem evaluate_deterministic (p : Program) (request : Request) (values : Array Value)
    (depth : Nat) (a b : Evaluation) (ha : evaluate p request values depth = .ok a)
    (hb : evaluate p request values depth = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

/-- Successful results have the retained body's actual type and a real
constructor inventory entry. This output check does not prove traversal
soundness or that every admitted evaluation succeeds. -/
theorem evaluate_type (p : Program) (request : Request) (values : Array Value)
    (depth : Nat) (evaluation : Evaluation) (value : Value)
    (h : evaluate p request values depth = .ok evaluation)
    (hv : evaluation.outcome = .ok value) :
    value.type = evaluation.body.type ∧ value.valid p.typed = true := by
  unfold evaluate at h
  dsimp only at h
  split at h
  · cases Except.ok.inj h
    dsimp only at hv
    simp only [Bind.bind, Except.bind] at hv
    split at hv
    · contradiction
    · split at hv
      · contradiction
      · exact checked_type _ _ _ _ hv
  · contradiction

theorem evaluate_selected (p : Program) (request : Request) (values : Array Value)
    (depth : Nat) (evaluation : Evaluation)
    (h : evaluate p request values depth = .ok evaluation) :
    evaluation.body ∈ p.typed.bodies ∧ evaluation.body.owner = request.owner ∧
      evaluation.body.member.map (·.label.text) = request.member := by
  unfold evaluate at h
  dsimp only at h
  split at h
  · rename_i _ body found
    cases Except.ok.inj h
    have hs := Array.find?_some (p := fun b : TypedBody =>
      b.owner == request.owner && b.member.map (·.label.text) == request.member) found
    have selected := Bool.and_eq_true_iff.mp hs
    exact ⟨Array.mem_of_find?_eq_some found, eq_of_beq selected.1, eq_of_beq selected.2⟩
  · contradiction

end FrenEval
