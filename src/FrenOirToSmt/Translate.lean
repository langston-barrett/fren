module

public import FrenOirToSmt.Types

public section
namespace FrenOirToSmt
open FrenOir FrenLir FrenModule

/-- Each namespace is disjoint; source text never enters an SMT identifier. -/
inductive Symbol where
  | sort (index : Nat)
  | constructor (owner index : Nat)
  | function (index : Nat) (component : Component)
  | parameter (index : Nat)
  | local (depth : Nat) (component : Component)
  deriving Repr, BEq, DecidableEq

@[expose] def Symbol.render : Symbol → String
  | .sort i => s!"E{i}"
  | .constructor i j => s!"C{i}_{j}"
  | .function i .value => s!"F{i}v"
  | .function i .domain => s!"F{i}d"
  | .parameter i => s!"P{i}"
  | .local i .value => s!"L{i}v"
  | .local i .domain => s!"L{i}d"

@[expose] def integer (i : Int) : String :=
  if i < 0 then s!"(- {i.natAbs})" else toString i.natAbs

def enumIndex (p : FrenOir.Program) (id : FrenBase.ItemId) : Except Failure Nat :=
  match p.enumerations.findIdx? (·.id == id) with
  | some i => .ok i
  | none => .error (.invalid "missing nominal enum")

private def sort (p : FrenOir.Program) : FrenExpr.Ty → Except Failure String
  | .bool => .ok "Bool"
  | .int => .ok "Int"
  | .enum id => return (Symbol.sort (← enumIndex p id)).render

def functionName (p : FrenOir.Program) (sig : Signature) (component : Component) : Except Failure String := do
  let some i := p.definitions.findIdx? (·.signature == sig)
    | throw (.invalid "missing canonical function signature")
  return (Symbol.function i component).render

def application (name : String) (args : List String) : String :=
  if args.isEmpty then name else "(" ++ String.intercalate " " (name :: args) ++ ")"

/-- The environment is nearest first. Pair entries are the value/domain names
of a local; parameters have literal true domains. Let bindings are simultaneous
SMT lets, evaluated outside the new binding's own scope. -/
@[expose] def term : Nat → FrenOir.Program → List (String × String) → Term → Except Failure String
  | 0, _, _, _ => .error (.resourceExhausted "SMT term translation depth")
  | n + 1, p, env, t => do
    let visit := term n p env
    match t with
    | .bool b => return if b then "true" else "false"
    | .int i => return integer i
    | .constructor owner id =>
      let i ← enumIndex p owner
      let some e := p.enumerations[i]? | throw (.invalid "missing enum declaration")
      let some j := e.constructors.findIdx? (·.1 == id) | throw (.invalid "missing nominal constructor")
      return (Symbol.constructor i j).render
    | .local _ slot component =>
      let some (v, d) := env[slot]? | throw (.invalid "open logical local")
      return match component with | .value => v | .domain => d
    | .unary op a => return application (match op with | .not => "not" | .neg => "-") [← visit a]
    | .binary op a b =>
      let left ← visit a
      let right ← visit b
      let name := match op with
        | .and => "and" | .or => "or" | .iff | .eq => "=" | .ne => "distinct"
        | .add => "+" | .sub => "-" | .mul => "*" | .div => "div" | .mod => "mod"
        | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
      return application name [left, right]
    | .ite c a b => return application "ite" [← visit c, ← visit a, ← visit b]
    | .app sig component args => return application (← functionName p sig component) (← args.mapM visit)
    | .letE _ _ v d body =>
      let value ← visit v
      let domain ← visit d
      let vname := (Symbol.local env.length .value).render
      let dname := (Symbol.local env.length .domain).render
      let rest ← term n p ((vname, dname) :: env) body
      return s!"(let (({vname} {value}) ({dname} {domain})) {rest})"
    | .at _ a => visit a

private def parameters (p : FrenOir.Program) (ps : Array TypedParameter) :
    Except Failure (String × List (String × String)) := do
  let mut binders := #[]
  let mut env := []
  for i in [:ps.size] do
    let some param := ps[i]? | throw (.invalid "missing parameter")
    let name := (Symbol.parameter i).render
    binders := binders.push s!"({name} {← sort p param.type})"
    env := (name, "true") :: env
  return (String.intercalate " " binders.toList, env)

private def dependencies : Nat → Term → Except Failure (List FrenBase.ItemId)
  | 0, _ => .error (.resourceExhausted "definition dependency depth")
  | n + 1, t => do
    let go := dependencies n
    match t with
    | .bool _ | .int _ | .constructor .. | .local .. => return []
    | .unary _ a | .at _ a => go a
    | .binary _ a b => return (← go a) ++ (← go b)
    | .ite c a b => return (← go c) ++ (← go a) ++ (← go b)
    | .app sig _ args => return sig.id :: (← args.mapM go).flatten
    | .letE _ _ v d b => return (← go v) ++ (← go d) ++ (← go b)

/-- Exact definitions in a stable topological order, also for forward calls.
No recursive axiom, dropped unused body or guessed totality is introduced. -/
def prelude (p : FrenOir.Program) : Except Failure String := do
  let mut lines := ["(set-logic ALL)"]
  for i in [:p.enumerations.size] do
    let some e := p.enumerations[i]? | throw (.invalid "missing enum")
    if e.constructors.isEmpty then throw (.unsupported "empty nominal enum")
    let ctors := (List.range e.constructors.size).map (fun j => s!"({(Symbol.constructor i j).render})")
    lines := lines ++ [s!"(declare-datatype {(Symbol.sort i).render} ({String.intercalate " " ctors}))"]
  let mut pending := p.definitions.toList
  let mut doneIds : List FrenBase.ItemId := []
  for _ in [:p.definitions.size] do
    let mut selected := none
    for d in pending do
      let ds := (← dependencies 10000 d.value) ++ (← dependencies 10000 d.domain)
      if selected.isNone && ds.all doneIds.contains then selected := some d
    let some d := selected | throw (.unsupported "cyclic or missing function definition")
    let (binders, env) ← parameters p d.signature.parameters
    for component in [Component.value, .domain] do
      let name ← functionName p d.signature component
      let result ← if component == .domain then pure "Bool" else sort p d.signature.result
      let body ← term 10000 p env (if component == .domain then d.domain else d.value)
      lines := lines ++ [s!"(define-fun {name} ({binders}) {result} {body})"]
    doneIds := doneIds ++ [d.signature.id]
    pending := pending.filter (fun other => other.signature.id != d.signature.id)
  return String.intercalate "\n" lines ++ "\n"

def script (p : FrenOir.Program) (textPrelude : String) (q : FrenOir.Question) : Except Failure String := do
  let (_, env) ← parameters p (q.parameters.map (·.source))
  let mut declarations := []
  for i in [:q.parameters.size] do
    let some param := q.parameters[i]? | throw (.invalid "missing query parameter")
    declarations := declarations ++ [s!"(declare-const {(Symbol.parameter i).render} {← sort p param.source.type})"]
  let formula ← term 10000 p env q.search
  return textPrelude ++ String.intercalate "\n" declarations ++ s!"\n(assert {formula})\n(check-sat)\n"

theorem distinct_components (i : Nat) : Symbol.function i .value ≠ .function i .domain := by
  intro h; cases h

theorem parameter_domain (i : Nat) :
    term (i + 1) p [("P0", "true")] (.local ty 0 .domain) = .ok "true" := rfl

end FrenOirToSmt
