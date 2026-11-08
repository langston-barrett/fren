module

public import FrenHirToThir.Coverage

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

/-- Requires genuine successful check output. Every function, including
unused functions, is a root. Thus self loops and every mutually recursive
component are rejected, while shared acyclic callees and forward calls pass. -/
def validateNonrecursive (t : Typed) : ValidationResult := do
  let edges ← callEdges t
  for sig in t.signatures do
    if let some failure := cycleFrom t edges sig.id then throw failure
  return ()

@[expose] def WalkingNonrecursive (t : Typed) : Prop := validateNonrecursive t = .ok ()

end FrenHirToThir
