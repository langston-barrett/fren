-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: closures -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A closure, as a Lean `fun`, with its body's obligations, each at its
reference, with its table's question if it is one, as a predicate of the
closure's parameters (`closureTerm`). -/
structure ClosureTerm where
  term : Term
  obligations : Array (Syntax × Option Core.TableGoal × Term) := #[]
  deriving Inhabited

open Lang in
/-- The closure whose parameters are `params`, of their types, and whose
body is `body`, of the type `r?` if it is known, where `toTerm` translates
its body: a Lean `fun`, its parameters' types and its body's
(`Reqs/Lang/HigherOrder#meaning`). Its parameters are declared as a
quantifier's bound names are, but not where `synthetic`, as those of a
function's name are, and its body's indexes, tables and applications with
preconditions are checked for every value of them. -/
def closureTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (params : Array (Syntax × Core.Ty))
    (body : Syntax) (r? : Option Core.Ty) (synthetic : Bool) : TermElabM (ClosureTerm × Array Core.Ty × Core.Ty) := do
  let mut named : Array (Name × Name × Core.Ty × Expr) := #[]
  for (x, t) in params, i in [0:params.size] do
    -- `_`, which declares no name (`closureParamIdent`), as a synthetic one.
    let bn ← if synthetic || x.getId.toString.startsWith "#_" then pure x.getId else do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what) ++ named.map fun (bn, _) => (bn, Core.BindingKind.boundName)) cx.selfFn.isSome
      let y ← declare x cx.modName locals
      liftMsg y (Core.checkVarName y.getId (some (t == .bool)))
      lintName .binder y.getId y
      pure y.getId
    -- Named apart from every local around it, as a bound name at its
    -- position is (`Core.boundSymbol`): one binder has each position along
    -- a path. The solver never sees it.
    let local_ := Name.mkSimple (Core.boundSymbol (bn.toString (escape := false)) (cx.binders.size + i))
    named := named.push (bn, local_, t, ← leanTypeOf t)
  withLocalDeclsD (named.map fun (_, l, _, ty) => (l, fun _ => pure ty)) fun _ => do
    let new := named.mapIdx fun i (bn, l, _, ty) =>
      ({ name := bn, term := ⟨mkIdent l⟩, «type» := ty, scrutinee := none, outer := cx.binders.size + i, unbounded := true
         closure := true } : MatchBinder)
    let outer := (← getLocal).indexes
    let outerTables := (← getLocal).tables
    modifyLocal fun l => { l with indexes := #[], tables := #[] }
    let site : Core.ExprSite := if r?.isSome then .typedClosureBody else .untypedClosureBody
    let t ← toTerm { cx with binders := cx.binders ++ new, expected? := site.expected r? none, natOk := false, inClosure := true
                             emptyOk := site.checked false false } body
    let rt := (← frenTypeOf? t).getD .bool
    -- Its obligations, each a predicate of its parameters, which the
    -- application puts at each application of the function parameter
    -- (`lang::closure_obligation`).
    let over (g : Term) : TermElabM Term := named.foldrM (init := g) fun (_, l, _, ty) acc => do
      `(fun ($(mkIdent l) : $(← exprToSyntax ty)) => $acc)
    let raw : Array (Syntax × Option Core.TableGoal × Term) := (← getLocal).indexes.map (fun (ref, g) => (ref, none, g))
      ++ (← getLocal).tables.map fun (ref, q, g) => (ref, some q, g)
    let obls ← raw.mapM fun (ref, q?, g) => return (ref, q?, ← over g)
    modifyLocal fun l => { l with indexes := outer, tables := outerTables }
    let rty ← exprToSyntax (← leanTypeOf (r?.getD rt))
    let lam ← named.foldrM (init := ← `(($t : $rty))) fun (_, l, _, ty) acc => do
      `(fun ($(mkIdent l) : $(← exprToSyntax ty)) => $acc)
    return ({ term := lam, obligations := obls }, named.map (·.2.2.1), rt)

/-- Records the use `u`, written at `ref`, of the defined function `f`, whose
parameters are `ps`, in its own body; an error if with it the uses are not a
structural recursion (`lang::structural_recursion`). -/
def noteRecUse (ref : Syntax) (f : Name) (ps : Array Name) (u : Core.RecUse) : TermElabM Unit := do
  -- Once for each use written: an expression elaborated again, such as a
  -- `match`'s arms for Lean's `match` or a `match`'s scrutinee where a
  -- closure refers to an arm's binder, is not another use.
  let range? := ref.getRange?
  if range?.isSome && (← getLocal).recUses.any (·.1.getRange? == range?) then return
  modifyLocal fun l => { l with recUses := l.recUses.push (ref, u) }
  let uses := (← getLocal).recUses
  if let .notStructural _ i := Core.selfRecursion ps.size (uses.toList.map (·.2)) then
    -- A function always has a parameter; without one, the message names the function.
    throwErrorAt ref (Core.nonStructuralMsg f (ps[i]?.getD f) u.form (u.args[i]?.getD .expr)).text

/-- Resolve a group member without bypassing ordinary shadowing or privacy. -/
def groupTarget? (cx : ExprCtx) (segs : Array Syntax) : TermElabM (Option Nat) := do
  let l ← getLocal
  let some caller := l.groupCaller? | return none
  let .ok (.item { kind := .fnItem, path, .. }) :=
      (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing | return none
  return Core.groupTarget? (l.groupFns.toList.map (·.1)) caller path

/-- Record the caller-relative origins, then ask the shared group search. -/
def noteGroupUse (ref : Syntax) (callee : Nat) (form : Core.RecForm) (args : List Core.GroupArg) : TermElabM Unit := do
  let l ← getLocal
  let some caller := l.groupCaller? | return
  let range? := ref.getRange?
  if range?.isSome && l.groupUses.any (fun (r, u) => u.caller == caller && r.getRange? == range?) then return
  let uses := l.groupUses.push (ref, { caller, callee, form, args })
  modifyLocal fun l => { l with groupUses := uses }
  if (Core.recursionGroup (l.groupFns.toList.map fun (_, ft, _) => ft.params.size) (uses.toList.map (·.2))).isNone then
    throwErrorAt ref Core.groupTerminationMsg.text

/-- `redundant_type_annotations` and `redundant_closure` on the closure `e`, given for a function parameter whose parameters' types
are `ps` where they are known before the closure, and whose result's is
`r?` (`lint::redundant_type_annotations`, `lint::redundant_closure`). -/
def lintClosure (cx : ExprCtx) (ps : Array (Option Core.Ty)) (r? : Option Core.Ty) (e : Syntax) : TermElabM Unit := do
  let params := e[1].getSepArgs
  let names := params.mapIdx fun k p => Core.nameText (declaredIdent (closureParamIdent p k)).1.getId
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  -- `redundant_type_annotations` (`lint::redundant_type_annotations`).
  for p in params, p? in ps, n in names do
    if p[1].isNone then continue
    unless Core.redundantTypeAnnotation true p?.isSome do continue
    let msg := Core.redundantTypeAnnotationMsg (if !p[0].isIdent then "_" else n) (exactText p[1][1])
    recordLint .redundantTypeAnnotations p[1][1] (if fixable then msg.note Core.fixHelp else msg)
  -- `unused_variables` on its parameters (`lint::unused_closure_params`).
  let mentioned := (pathMentions e[3]).map (·.getRoot)
  for p in params, n in names do
    unless Core.closureParamOptedOut n || mentioned.contains (Name.mkSimple n) do
      recordLint .unusedVariables (declaredIdent p[0]).1 (Core.unusedClosureParamMsg (Name.mkSimple n))
  -- `redundant_closure` (`lint::redundant_closure`).
  let body := unparen e[3]
  unless body.isOfKind ``Lang.appExpr do return
  let segs := pathSegs body[0]
  let args := (body[2].getSepArgs.map fun a => (soleName? a).bind fun y => names.idxOf? (Core.nameText y)).toList
  let some rt := r? | return
  let some pts := ps.mapM id | return
  let (callee, exact) : Core.Callee × Bool :=
    if segs.size == 1 && names.contains (Core.nameText segs[0]!.getId) then (.other, false)
    else if let some (ft, _) := (if segs.size == 1 then cx.fnParam? segs[0]!.getId else none) then
      (.fnParameter, ft.params == pts && ft.result == rt)
    else (.other, false)
  let (callee, exact) ← if callee != .other || (segs.size == 1 && names.contains (Core.nameText segs[0]!.getId)) then
      pure (callee, exact)
    else match (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing with
      | .ok (.item { kind := .fnItem, path, .. }) =>
        match (← getState).defined.find? path with
        | some d =>
          pure (if d.typeParams.isEmpty && d.hoParams.isEmpty then
            (.defined, d.declared == pts && d.result == rt && (d.ptys.1.push d.ptys.2).all (!·.restricted)) else (.other, false))
        | none => pure (.other, false)
      | _ => pure (.other, false)
  unless Core.redundantClosure names.size args true callee exact do return
  let msg := Core.redundantClosureMsg (exactText body[0])
  recordLint .redundantClosure e (if fixable then msg.note Core.fixHelp else msg)

/-- Records what the application of the higher-order function `path` gives
its parameter at `k`, the closure or function's name `e`, for
`needless_higher_order` (`lint::needless_higher_order`): its text, and the
names that a closure's body has free (`closureFreeNames`), of which a
function's name is one, or that it is a lambda match. -/
def noteFnArg (path : Name) (k : Nat) (e : Syntax) : TermElabM Unit := do
  let range? := e.getRange?
  if (← getLocal).fnArgs.any fun (a, r) => r.getRange? == range? && a.index == k then return
  let u := unparen e
  let (lambdaMatch, names) : Bool × Array String :=
    if u.isOfKind ``Lang.closureExpr then (false, closureFreeNames u)
    else
      let p := if u.getNumArgs == 1 && u[0].isOfKind ``Lang.fren_path then u[0] else u
      if p.isOfKind ``Lang.fren_path then (false, #[(pathSegs p).foldl (fun acc s => acc ++ "::" ++ Core.nameText s.getId) ""])
      -- `fnArgTerm` accepts nothing else but a lambda match.
      else (true, #[])
  modifyLocal fun l => { l with fnArgs := l.fnArgs.push ({ path, index := k, text := exactText e, lambdaMatch, names }, e) }

open Lang in
/-- A closure, or the name of a function, `e`, given for the function
parameter of type `ft`, as its function's signature declares it, of the
higher-order function `f`, whose parameters' types are `ps` where they are
known and whose result's is `r?` if it is known: its term, its
parameters' types and its body's (`Reqs/Lang/HigherOrder#arguments`). The
name of a function `g` is the closure `|x1, ..., xn| g(x1, ..., xn)`. -/
def fnArgTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (f : String) (ft : Core.FnTy)
    (ps : Array (Option Core.Ty)) (r? : Option Core.Ty) (e : Syntax) : TermElabM (ClosureTerm × Array Core.Ty × Core.Ty) := do
  let e := unparen e
  if e.isOfKind ``Lang.lambdaMatchExpr then
    let some types := ps.mapM id | throwErrorAt e (Core.closureParamUnknownMsg f).text
    let names := types.mapIdx fun j _ => mkIdentFrom e (Name.mkSimple s!"#match{j}")
    let body ← explicitLambdaMatch e names
    return ← closureTerm toTerm cx ((names.map (·.raw)).zip types) body r? true
  if e.isOfKind ``Lang.closureExpr then
    let params := e[1].getSepArgs
    if let some msg := Core.argumentMsg? ft (.closure params.size) then throwErrorAt e msg.text
    -- Distinct names (`lang::distinct_names`).
    let declared := params.mapIdx fun k p => (declaredIdent (closureParamIdent p k)).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then throwErrorAt params[k]![0] (Core.dupBoundMsg declared[k]!).text
    let named ← (params.zipIdx.zip ps).mapM fun ((p, k), p?) => do
      -- Its written type is the function type's (`lang::function_argument`).
      let t ← match (if p[1].isNone then none else some p[1][1]), p? with
        | some ty, some q => do
          let a := ((← coreTy? (← elabPType cx.modName ty).1)).getD .bool
          unless a == q do
            throwErrorAt ty (Core.typeMismatchMsg q a (some s!"note: this parameter of the closure for `{f}` has type `{q.show}`")).text
          pure q
        | some ty, none => pure (((← coreTy? (← elabPType cx.modName ty).1)).getD .bool)
        | none, some q => pure q
        | none, none => throwErrorAt p[0] (Core.closureParamUnknownMsg f).text
      return (closureParamIdent p k, t)
    lintClosure cx ps r? e
    return ← closureTerm toTerm cx named e[3] r? false
  let p := if e.getNumArgs == 1 && e[0].isOfKind ``Lang.fren_path then e[0] else e
  unless p.isOfKind ``Lang.fren_path do throwErrorAt e ((Core.argumentMsg? ft .other).getD default).text
  -- A function parameter, or a defined function, but not an uninterpreted
  -- one (`lang::function_argument`).
  let segs := pathSegs p
  -- The function itself, in its own body, not applied.
  if let some callee ← groupTarget? cx segs then noteGroupUse p callee .passed []
  if let some (ps, _, _) := cx.selfRec? then
    if segs.size == 1 && cx.selfFn == some segs[0]!.getId then
      noteRecUse p (cx.modName ++ segs[0]!.getId) ps { form := .passed }
  let isParam := segs.size == 1 && (cx.fnParam? segs[0]!.getId).isSome
  unless isParam do
    match (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing with
    | .ok (.item { kind := .fnItem, path, .. }) =>
      let shape : Core.ArgShape := if (← getState).defined.contains path then .definedName else .uninterpretedName
      if let some msg := Core.argumentMsg? ft shape path then throwErrorAt e msg.text
    | _ => throwErrorAt e ((Core.argumentMsg? ft .other).getD default).text
  let some tys := ps.mapM id | throwErrorAt e (Core.closureParamUnknownMsg f).text
  let xs := (List.range tys.size).toArray.map fun k => mkIdentFrom p (Name.mkSimple s!"#{k}")
  let args ← xs.mapM fun x => pathExpr p x.getId
  let tmpl ← `(fren_expr| f(x))
  let call := (tmpl.raw.setArg 0 p).setArg 2 (Syntax.mkSep args (mkAtom ","))
  closureTerm toTerm cx ((xs.map (·.raw)).zip tys) call r? true


end Fren
