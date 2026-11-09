module

public import FrenLir.Walking

public section
namespace FrenLir
open FrenModule

/-- Executable scoped sort checker for the actual logical terms. Failure of
this bounded structural check rejects production; it has no solver meaning.
Origins are checked in the same context as their term, including under lets. -/
def Term.infer : Nat → Typed → TypeContext → Term → Option FrenExpr.Ty
  | 0, _, _, _ => none
  | n + 1, t, ctx, term => do
    let infer := Term.infer n t ctx
    match term with
    | .bool _ => some .bool
    | .int _ => some .int
    | .constructor owner id =>
      if id.parent == some owner && t.resolved.scope.items.any (fun i =>
          i.id == id && i.kind == .constructor) then some (.enum owner) else none
    | .local ty i component =>
      if ctx[i]?.map Prod.snd != some ty then none
      else some (if component == .domain then .bool else ty)
    | .unary op a => FrenExpr.unary op (← infer a)
    | .binary op a b => FrenExpr.binary op (← infer a) (← infer b)
    | .ite c a b =>
      if (← infer c) != .bool then none
      else
        let ty ← infer a
        if (← infer b) == ty then some ty else none
    | .app sig component args =>
      if !t.signatures.contains sig then none
      else if (← args.mapM infer) != sig.parameters.toList.map (·.type) then none
      else some (if component == .domain then .bool else sig.result)
    | .letE binder ty value domain body =>
      if (← infer value) != ty || (← infer domain) != .bool then none
      else Term.infer n t ((binder, ty) :: ctx) body
    | .at origin value =>
      if origin.context != ctx then none else infer value

/-- Every written occurrence belongs to this exact source body. Synthetic
logical guards have no invented source occurrence; their marked children
retain the written expressions and binder contexts that produced them. -/
def Term.originsValid : Nat → TypedBody → Term → Bool
  | 0, _, _ => false
  | n + 1, b, term =>
    let valid := Term.originsValid n b
    match term with
    | .bool _ | .int _ | .constructor .. | .local .. => true
    | .unary _ a => valid a
    | .binary _ a c => valid a && valid c
    | .ite c a d => valid c && valid a && valid d
    | .app _ _ args => args.all valid
    | .letE _ _ v d rest => valid v && valid d && valid rest
    | .at o a => o.owner == b.owner && o.member == b.member &&
      b.occurrences.any (fun occurrence => occurrence.expression == o.expression &&
        occurrence.context == o.context) && valid a

@[expose] def Body.wellSorted (t : Typed) (b : Body) : Bool :=
  -- A deliberately conservative check budget. Exceeding it rejects output.
  Term.originsValid 10000 b.source b.term.value && Term.originsValid 10000 b.source b.term.defined &&
  Term.infer 10000 t b.source.context b.term.value == some b.source.type &&
    Term.infer 10000 t b.source.context b.term.defined == some .bool

@[expose] def Declaration.source : Declaration → FrenMir.Declaration
  | .enumeration e => .enumeration e
  | .function sig b => .function ⟨sig, b.source⟩
  | .block b _ => .block b

@[expose] def Question.source : Question → FrenMir.Question
  | .assumptionsSatisfiable => .assumptionsSatisfiable
  | .validity b => .validity b.source

/-- Retention and scope certificate checked by the real producer, independently
of its expression traversal. This does not establish semantic simulation. -/
@[expose] def Program.wellFormed (p : Program) : Bool :=
  p.declarations.map Declaration.source == p.mir.declarations &&
  p.declarations.all (fun d => match d with
    | .enumeration _ => true
    | .function _ b => b.wellSorted p.mir.source
    | .block source bs => bs.map Body.source == source.members && bs.all (·.wellSorted p.mir.source)) &&
  p.requests.map CheckRequest.source == p.mir.requests &&
  p.requests.all (fun r =>
    r.assumptions.map Body.source == r.source.assumptions &&
    r.question.source == r.source.question &&
    r.demand.map Body.source == r.source.demand.map FrenMir.Demand.root &&
    (r.assumptions ++ r.demand).all (·.wellSorted p.mir.source) &&
    (match r.question with | .assumptionsSatisfiable => true | .validity g => g.wellSorted p.mir.source))

end FrenLir
