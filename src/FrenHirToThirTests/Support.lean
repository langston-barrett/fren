module

public import FrenHirToThir

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir FrenExpr

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def resolved (text : String) : IO Resolved := do
  let .ok doc := FrenParse.parseFile ⟨47⟩ text | throw (IO.userError s!"parse failed: {text}")
  let .ok r := FrenAstToHir.resolve doc | throw (IO.userError s!"resolve failed: {text}")
  return r

def typed (text : String) : IO Typed := do
  let r ← resolved text
  match check r with
  | .ok t =>
    require (t.resolved == r && t.resolved.document.emit == text) "erasure/source changed"
    return t
  | .error d => throw (IO.userError s!"unexpected typing failure: {repr d}\n{text}")

def rejected (text : String) : IO FrenDiag.Diagnostic := do
  let r ← resolved text
  let .error d := check r | throw (IO.userError s!"ill-typed tree accepted: {text}")
  require (!d.headline.isEmpty) "empty diagnostic"
  return d

def bodyAt (t : Typed) (i : Nat) : IO TypedBody :=
  match t.bodies[i]? with
  | some b => pure b
  | none => throw (IO.userError s!"missing body {i}")

def signature (t : Typed) : IO Signature :=
  match t.signatures[0]? with
  | some s => pure s
  | none => throw (IO.userError "missing first signature")

def parameter (s : Signature) : IO TypedParameter :=
  match s.parameters[0]? with
  | some p => pure p
  | none => throw (IO.userError "missing first parameter")

def key (name : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "m" |>.named name

def valueTypes (body : TypedBody) : Array FrenExpr.Ty := body.occurrences.filterMap fun o =>
  match o.type with | .value ty => some ty | _ => none

def nameOccurrences (body : TypedBody) : Array TypedOccurrence := body.occurrences.filter fun o =>
  match o.expression with | .name _ => true | _ => false

/-- Local data is checked against the selected raw index and exact token
context. This is an audit of output, not an alternate resolver. -/
def localsRetained (t : Typed) : Bool := t.bodies.all fun b =>
  b.occurrences.all fun o => match o.expression with
    | .name p => match t.resolved.referenceAt p.head.slice with
      | some r => match r.target, o.type with
        | .local i, .value ty =>
          r.context == o.context.map Prod.fst && localType o.context i == some ty
        | .item _, _ => true
        | _, _ => false
      | none => false
    | _ => true

def sameResult [BEq ε] [BEq α] (left right : Except ε α) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

end FrenHirToThirTests
