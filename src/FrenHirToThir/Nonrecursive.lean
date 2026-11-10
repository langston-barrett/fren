module

public import FrenHirToThir.Coverage
public import FrenHirToThir.Termination

public section
namespace FrenHirToThir
open FrenAst FrenModule

structure CallEdge where
  caller : FrenBase.ItemId
  callee : FrenBase.ItemId
  span : FrenSource.Span
  deriving Repr, BEq

/-- Read actual call nodes and their typed callee signatures. The parser
currently admits adjacent named calls only. Bare names, locals and annotations
create no edge. As with coverage, the precondition is genuine successful check
output. Checks cannot be called, so their calls create no function graph edges. -/
def callEdges (t : Typed) : Except WalkingFailure (Array CallEdge) := do
  let mut edges := #[]
  for body in t.bodies do
    if body.member.isNone then
      for occurrence in body.occurrences do
        if let .call callee _ _ _ _ := occurrence.expression then
          let span := (anchor callee t.resolved.scope.name).span
          let some (.callable sig) := occurrenceType body callee
            | throw (.invalidMetadata span)
          edges := edges.push ⟨body.owner, sig.id, span⟩
  return edges

/-- Breadth-first search from one declared function. Each canonical function
is enqueued once. A simple return path has at most the number of declarations
edges; the bound is derived from actual signatures, not supplied adjacency or
an acyclicity flag. Requires genuine `check` output and
`callEdges t = .ok edges`, so all targets are declared functions. Paths and
edges are scanned in stable array order. -/
def cycleFrom (t : Typed) (edges : Array CallEdge) (start : FrenBase.ItemId) :
    Option WalkingFailure := Id.run do
  let mut queue := #[(start, #[start])]
  let mut visited := #[start]
  let mut cursor := 0
  for _ in [:t.signatures.size] do
    let some (current, path) := queue[cursor]? | return none
    cursor := cursor + 1
    for edge in edges do
      if edge.caller == current then
        if edge.callee == start then return some (.cycle edge.span (path.push start))
        unless visited.contains edge.callee do
          visited := visited.push edge.callee
          queue := queue.push (edge.callee, path.push edge.callee)
  return none

/-- The functions that `start` reaches by one call or more, in the order
found. Each function is enqueued once, so the queue holds at most one entry
more than there are declarations. Same preconditions as `cycleFrom`. -/
def reached (t : Typed) (edges : Array CallEdge) (start : FrenBase.ItemId) :
    Array FrenBase.ItemId := Id.run do
  let mut queue := #[start]
  let mut found := #[]
  let mut cursor := 0
  for _ in [:t.signatures.size + 1] do
    let some current := queue[cursor]? | return found
    cursor := cursor + 1
    for edge in edges do
      if edge.caller == current then
        unless found.contains edge.callee do
          found := found.push edge.callee
          queue := queue.push edge.callee
  return found

/-- The recursive group of `start`, in declaration order: the functions that
`start` reaches and that reach it. It is empty when `start` is not recursive. -/
def recursiveGroup (t : Typed) (edges : Array CallEdge) (start : FrenBase.ItemId) :
    Array FrenBase.ItemId :=
  let fromStart := reached t edges start
  (t.signatures.map (·.id)).filter fun item =>
    fromStart.contains item && (reached t edges item).contains start

/-- The de Bruijn level of a written argument or let value that is a local, at
the given number of locals in scope. Parentheses are not a form of the Core. -/
def localLevel (t : Typed) (depth : Nat) : Expr → Option Nat
  | .paren _ body _ => localLevel t depth body
  | .name path =>
    match t.resolved.referenceAt path.head.slice with
    | some reference =>
      match reference.target with
      | .local index => if index < depth then some (depth - 1 - index) else none
      | _ => none
    | none => none
  | _ => none

/-- The written calls of an expression of a function body, as the termination
check reads them. Fuel is the terminal count plus one, as in `infer`; the
precondition is genuine successful check output, whose callees are typed. -/
def writtenCalls (t : Typed) (body : TypedBody) :
    Nat → Nat → Expr → Except WalkingFailure (Termination.Calls FrenBase.ItemId)
  | 0, _, e => .error (.invalidMetadata (anchor e t.resolved.scope.name).span)
  | fuel + 1, depth, e => do
    let visit := writtenCalls t body fuel
    match e with
    | .name _ | .bool _ _ | .integer _ _ => return .leaf
    | .paren _ inner _ => visit depth inner
    | .unary _ _ inner => visit depth inner
    | .binary left _ _ right => return .both (← visit depth left) (← visit depth right)
    | .call callee _ args _ _ =>
      let some (.callable sig) := occurrenceType body callee
        | throw (.invalidMetadata (anchor e t.resolved.scope.name).span)
      let mut calls := Termination.Calls.leaf
      for arg in args do
        calls := .both calls (← visit depth arg)
      return .both calls (.call sig.id (args.toList.map (localLevel t depth)))
    | .ifE _ condition _ yes _ no =>
      return .both (← visit depth condition) (.both (← visit depth yes) (← visit depth no))
    | .letE _ _ _ value _ inner =>
      return .both (← visit depth value)
        (.bind (localLevel t depth value) (← visit (depth + 1) inner))
    | .matchE _ scrutinee _ arms _ =>
      let mut calls := Termination.Calls.leaf
      for (_, _, inner, _) in arms do
        calls := .both calls (← visit depth inner)
      return .both (← visit depth scrutinee) calls

/-- What the termination check reads of one declared function. No source form
writes the mark `unchecked`, so every function is `checked`. -/
def functionOf (t : Typed) (span : FrenSource.Span) (item : FrenBase.ItemId) :
    Except WalkingFailure (Termination.Function FrenBase.ItemId FrenExpr.Ty) := do
  let some sig := t.signatures.find? (·.id == item) | throw (.invalidMetadata span)
  let some body := t.bodies.find? fun body => body.member.isNone && body.owner == item
    | throw (.invalidMetadata span)
  let calls ← writtenCalls t body (body.expression.tokens.length + 1) body.context.length
    body.expression
  return ⟨item, sig.parameters.toList.map (·.type), false, calls⟩

/-- The termination check of the recursive group of `start`, given the cycle
that `cycleFrom` found through it. A group that fails gets the check's
diagnostic. A group that passes keeps the cycle: lowering and every later pass
accept no recursion yet, so it is still rejected, as recursion that is not
supported and not as a failure of the check. -/
def judgeRecursion (t : Typed) (edges : Array CallEdge) (start : FrenBase.ItemId) :
    WalkingFailure → WalkingFailure
  | .cycle span path =>
    let group := recursiveGroup t edges start
    match group.mapM (functionOf t span) with
    | .error failure => failure
    | .ok functions =>
      if Termination.groupPassesNow functions.toList then .cycle span path
      else
        let reason := match functions.find? (·.parameters.isEmpty) with
          | some function => .noParameters function.item
          | none => .unguarded
        .termination span group reason
  | failure => failure

/-- Requires genuine successful check output. Every function, including
unused functions, is a root. Thus self loops and every mutually recursive
component are rejected, while shared acyclic callees and forward calls pass.
The failure says whether the recursive group fails the termination check. -/
def validateNonrecursive (t : Typed) : ValidationResult := do
  let edges ← callEdges t
  for sig in t.signatures do
    if let some failure := cycleFrom t edges sig.id then
      throw (judgeRecursion t edges sig.id failure)
  return ()

@[expose] def WalkingNonrecursive (t : Typed) : Prop := validateNonrecursive t = .ok ()

end FrenHirToThir
