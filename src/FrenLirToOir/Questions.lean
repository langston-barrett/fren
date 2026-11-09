module

public import FrenLirToOir.Traversal

public section
namespace FrenLirToOir
open FrenLir FrenOir FrenModule

private def parameter (p : FrenLir.Program) (v : TypedParameter) : Result Parameter := do
  let domain ← match v.type with
    | .bool => pure Domain.boolean
    | .int => pure Domain.integer
    | .enum id => do
      let some e := p.declarations.findSome? (fun d => match d with
        | .enumeration e => if e.id == id then some e else none
        | _ => none) | throw (.invalidInput "missing nominal parameter domain")
      pure (Domain.enumeration id (e.constructors.map Prod.fst))
  return ⟨v, domain⟩

private def checkedQuestion (p : FrenLir.Program) (defs : Array Definition) (q : FrenOir.Question) :
    Result FrenOir.Question := do
  -- Traverse the same term depth before the Option-valued sort checker, so
  -- exhaustion has its own error instead of being mistaken for ill-sorting.
  let search := q.search
  let calls ← applications 10000 search
  unless Term.infer 10000 p.mir.source q.context search == some .bool do
    throw (.invalidInput "ill-sorted contextual question")
  unless calls.all (fun id => defs.any (fun d => d.signature.id == id)) do
    throw (.unsupported "application without actual definition equations")
  return {q with dependencies := q.dependencies ++ (calls.toArray.map Dependency.definition)}

private def partialReason : String :=
  "mutually partial assumptions: contextual definedness dependency rule unresolved"

/-- Source identity selects the complete assumption check group, including
trivial parameter-domain checks. No solver result selects these edges. -/
private def assumptionEdges (qs : Array FrenOir.Question) (assumptions : Array Body) : Array Dependency :=
  qs.filterMap fun q =>
    if q.kind == .assumptionDefinedness && assumptions.any (fun b => q.subject == some b.source)
    then some (.question q.id) else none

private def unresolvedEdges (qs : Array FrenOir.Question) (edges : Array Dependency) : Bool :=
  edges.any fun e => match e with
    | .question id => qs[id]?.any (fun q => q.readiness != .ready)
    | _ => false

private def emitBody (p : FrenLir.Program) (defs : Array Definition)
    (qs : Array FrenOir.Question) (kind : Kind) (parameters : Array Parameter)
    (request : Option Nat) (b : Body) (hypotheses : Array Body)
    (edges : Array Dependency) (readiness : Readiness) : Result (Array FrenOir.Question) := do
  let ls ← leaves b
  let start := qs.size
  let mut out := qs
  for leaf in ls do
    unless leaf.origin.owner == b.source.owner && leaf.origin.member == b.source.member &&
        b.source.occurrences.any (fun o => o.expression == leaf.origin.expression &&
          o.context == leaf.origin.context) do
      throw (.invalidInput "domain check has wrong source occurrence")
    let mut localEdges := #[]
    for path in leaf.prerequisites do
      let some index := ls.findIdx? (fun l => l.path == path)
        | throw (.invalidInput "missing contextual definedness prerequisite")
      unless start + index < out.size do
        throw (.invalidInput "cyclic contextual definedness prerequisite")
      localEdges := localEdges.push (.question (start + index))
    let q : FrenOir.Question := ⟨out.size, kind, b.source.owner, parameters, b.source.context,
      request, some b.source, some leaf.origin, leaf.path, hypotheses, leaf.frames,
      leaf.condition, edges ++ localEdges, readiness⟩
    out := out.push (← checkedQuestion p defs q)
  return out

/-- One group per assumption per owner, shared by Sat and all goal requests.
Other partial assumptions remain hypotheses with explicit cyclic edges; their
questions and all dependent requests are marked unresolved, never discharged.
A single partial assumption may use its independently total siblings safely. -/
private def emitAssumptions (p : FrenLir.Program) (defs : Array Definition)
    (qs : Array FrenOir.Question) (r : FrenLir.CheckRequest) (parameters : Array Parameter) :
    Result (Array FrenOir.Question) := do
  let mut out := qs
  let mut groups : Array (TypedBody × Nat × Nat) := #[]
  for b in r.assumptions do
    let start := out.size
    out ← emitBody p defs out .assumptionDefinedness parameters none b #[] #[] .ready
    groups := groups.push (b.source, start, out.size)
  -- Fill edges only after every group has an ID, preserving unresolved cycles.
  for (b, first, last) in groups do
    let some body := r.assumptions.find? (fun a => a.source == b)
      | throw (.invalidInput "missing assumption body")
    let others := if structurallyTotal body then #[] else r.assumptions.filter (fun a => a.source != b)
    let edges := assumptionEdges out others
    let state := if others.all structurallyTotal then Readiness.ready else .unresolved partialReason
    for i in [first:last] do
      let some q := out[i]? | throw (.invalidInput "missing assumption question")
      let updated := {q with
        hypotheses := others
        dependencies := q.dependencies ++ edges
        readiness := state}
      out := out.set! i (← checkedQuestion p defs updated)
  return out

private def emitSearch (p : FrenLir.Program) (defs : Array Definition)
    (qs : Array FrenOir.Question) (r : FrenLir.CheckRequest) (index : Nat)
    (parameters : Array Parameter) (kind : Kind) (subject : Option TypedBody)
    (condition : Term) (edges : Array Dependency) (state : Readiness) : Result (Array FrenOir.Question) := do
  let q : FrenOir.Question := ⟨qs.size, kind, r.source.owner, parameters, r.source.context,
    some index, subject, none, [], r.assumptions, [], condition, edges, state⟩
  return qs.push (← checkedQuestion p defs q)

/-- Question-building helper, in declaration/child/request order. The Program
producer calls it only on actual successful lowering with all equations. -/
def questions (p : FrenLir.Program) (defs : Array Definition) : Result (Array FrenOir.Question) := do
  let mut qs := #[]
  for declaration in p.declarations do
    match declaration with
    | .enumeration _ => pure ()
    | .function sig body =>
      let parameters ← sig.parameters.mapM (parameter p)
      qs ← emitBody p defs qs .functionDefinedness parameters none body #[] #[] .ready
    | .block block _ =>
      for index in [:p.requests.size] do
        let some r := p.requests[index]? | throw (.invalidInput "missing request")
        if r.source.owner != block.owner then continue
        let parameters ← r.source.parameters.mapM (parameter p)
        match r.question with
        | .assumptionsSatisfiable =>
          qs ← emitAssumptions p defs qs r parameters
          let edges := assumptionEdges qs r.assumptions
          let state := if unresolvedEdges qs edges then .unresolved partialReason else .ready
          qs ← emitSearch p defs qs r index parameters .assumptionsSatisfiable none (.bool true) edges state
        | .validity goal =>
          let edges := assumptionEdges qs r.assumptions
          let state := if unresolvedEdges qs edges then .unresolved partialReason else .ready
          let start := qs.size
          qs ← emitBody p defs qs .goalDefinedness parameters (some index) goal r.assumptions edges state
          let domains := (List.range (qs.size - start)).toArray.map (fun i => Dependency.question (start + i))
          qs ← emitSearch p defs qs r index parameters .validity (some goal.source) goal.term.value (edges ++ domains) state
  return qs

end FrenLirToOir
