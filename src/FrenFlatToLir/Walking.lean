module

public import FrenLir
public import FrenThirToMir

public section
namespace FrenFlatToLir
open FrenAst FrenModule FrenLir

abbrev Result := Except FrenDiag.Diagnostic

private def failure (t : Typed) (e : Expr) (detail : String) : FrenDiag.Diagnostic :=
  ⟨none, "walking LIR: " ++ detail, (FrenHirToThir.anchor e t.resolved.scope.name).span⟩

private def valueType (t : Typed) (b : TypedBody) (ctx : TypeContext) (e : Expr) : Result FrenExpr.Ty := do
  let some occ := b.occurrences.find? (fun o => o.expression == e && o.context == ctx)
    | throw (failure t e "missing typed lexical occurrence")
  let .value ty := occ.type | throw (failure t e "callable used as value")
  return ty

/-- The walking MIR fragment is already first order. This is direct logical
lowering, not a claim that mono/closure/flat passes have run. Depth failure is
an explicit producer error, never a false formula or a satisfiability result. -/
private def expression : Nat → Typed → TypedBody → TypeContext → Expr → Result Lowered
  | 0, t, _, _, e => .error (failure t e "lowering depth exhausted")
  | depth + 1, t, b, ctx, e => do
    let ty ← valueType t b ctx e
    let visit := expression depth t b ctx
    let lowered ← match e with
    | .bool _ v => pure ⟨.bool v, .bool true⟩
    | .integer _ v => pure ⟨.int v, .bool true⟩
    | .name path => do
      let some ref := t.resolved.referenceAt path.head.slice
        | throw (failure t e "missing reference")
      unless ref.context == ctx.map Prod.fst && ref.role == .expression do
        throw (failure t e "reference context mismatch")
      match ref.target with
      | .local i =>
        unless (ctx[i]?.map Prod.snd) == some ty do throw (failure t e "local type mismatch")
        pure ⟨.local ty i .value, .local ty i .domain⟩
      | .item id =>
        let some (.enum owner) := FrenHirToThir.constructorType t.resolved id
          | throw (failure t e "non-constructor item")
        pure ⟨.constructor owner id, .bool true⟩
      | _ => throw (failure t e "type used as value")
    | .paren _ child _ => visit child
    | .unary _ op child => do
      let a ← visit child
      pure ⟨.unary op a.value, a.defined⟩
    | .binary left _ op right => pure (Lowered.binary op (← visit left) (← visit right))
    | .ifE _ c _ yes _ no => pure (Lowered.branch (← visit c) (← visit yes) (← visit no))
    | .letE _ binder _ value _ rest => do
      let v ← visit value
      let vt ← valueType t b ctx value
      let body ← expression depth t b ((binder, vt) :: ctx) rest
      pure (Lowered.bind binder vt v body)
    | .call callee _ args _ _ => do
      let some occurrence := b.occurrences.find? (fun o => o.expression == callee && o.context == ctx)
        | throw (failure t e "missing callable occurrence")
      let .callable sig := occurrence.type | throw (failure t e "non-callable target")
      unless t.signatures.contains sig do throw (failure t e "missing canonical signature")
      let values ← args.toList.mapM visit
      pure (Lowered.call sig values)
    | .matchE _ scrutinee _ arms _ => do
      let s ← visit scrutinee
      let .enum owner ← valueType t b ctx scrutinee
        | throw (failure t e "non-enum scrutinee")
      let mut branches : List (Term × Lowered) := []
      for (pattern, _, arm, _) in arms do
        let some ref := t.resolved.referenceAt pattern.head.slice
          | throw (failure t e "missing constructor pattern")
        let .item id := ref.target | throw (failure t e "non-constructor pattern")
        unless ref.role == .pattern && ref.context == ctx.map Prod.fst &&
            FrenHirToThir.constructorType t.resolved id == some (.enum owner) do
          throw (failure t e "pattern ownership/context mismatch")
        branches := branches ++ [(.binary .eq s.value (.constructor owner id), ← visit arm)]
      let some (_, last) := branches.getLast? | throw (failure t e "empty match")
      -- Admission proved exhaustive coverage. The final arm is the fallback;
      -- no fabricated default value/domain enters this nominal enum domain.
      let selected := branches.dropLast.foldr (fun (guard, arm) rest =>
        Lowered.branch ⟨guard, .bool true⟩ arm rest) last
      pure ⟨selected.value, both s.defined selected.defined⟩
    return lowered.mark ⟨b.owner, b.member, e, ctx⟩

private def body (t : Typed) (b : TypedBody) : Result Body := do
  return ⟨b, ← expression (b.expression.tokens.length + 1) t b b.context b.expression⟩

private def declaration (t : Typed) : FrenMir.Declaration → Result Declaration
  | .enumeration e => pure (.enumeration e)
  | .function f => return .function f.signature (← body t f.definition)
  | .block b => return .block b (← b.members.mapM (body t))

private def request (t : Typed) (r : FrenMir.CheckRequest) : Result CheckRequest := do
  let assumptions ← r.assumptions.mapM (body t)
  let question : Question ← match r.question with
    | .assumptionsSatisfiable => pure .assumptionsSatisfiable
    | .validity g => do
      let goal ← body t g
      pure (Question.validity goal)
  let demand ← r.demand.mapM fun d => body t d.root
  return ⟨r, assumptions, question, demand⟩

/-- There is no public unchecked Typed/Theory entry. MIR is produced here from
its actual admission witness, so edited theories cannot bypass the boundary. -/
def produce (p : FrenThirDesugar.Program) : Result Program := do
  let mir ← FrenThirToMir.produce p
  let declarations ← mir.declarations.mapM (declaration mir.source)
  let requests ← mir.requests.mapM (request mir.source)
  let out : Program := ⟨mir, declarations, requests⟩
  if out.wellFormed then return out
  else throw (failure mir.source (.bool mir.source.resolved.scope.name true) "output scope/retention check failed")

def fromSource (file : FrenSource.FileId) (source : String) :
    Except FrenHirToThir.StaticFailure Program := do
  let p ← FrenThirDesugar.fromSource file source
  (produce p).mapError FrenHirToThir.StaticFailure.typing

theorem deterministic (p : FrenThirDesugar.Program) (a b : Program)
    (ha : produce p = .ok a) (hb : produce p = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

theorem retains_mir (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenThirToMir.produce p = .ok out.mir := by
  unfold produce at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i mir hm
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · cases Except.ok.inj h
          exact hm
        · contradiction

theorem wellFormed (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.wellFormed = true := by
  unfold produce at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · rename_i good
          cases Except.ok.inj h
          exact good
        · contradiction

theorem admission (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenHirToThir.checkWalking p.input = .ok out.mir.source :=
  FrenThirToMir.admission p out.mir (retains_mir p out h)

theorem retains_source (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.mir.source = p.typed :=
  FrenThirToMir.retains p out.mir (retains_mir p out h)

theorem declaration_retention_check (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    (out.declarations.map Declaration.source == out.mir.declarations) = true := by
  have hw := wellFormed p out h
  simp only [Program.wellFormed, Bool.and_eq_true_iff] at hw
  exact hw.1.1.1

theorem request_retention_check (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    (out.requests.map CheckRequest.source == out.mir.requests) = true := by
  have hw := wellFormed p out h
  simp only [Program.wellFormed, Bool.and_eq_true_iff] at hw
  exact hw.1.2

theorem rejected (file : FrenSource.FileId) (source : String) (d : FrenHirToThir.StaticFailure)
    (h : FrenThirDesugar.fromSource file source = .error d) : fromSource file source = .error d := by
  simp [fromSource, h, Bind.bind, Except.bind]

end FrenFlatToLir
