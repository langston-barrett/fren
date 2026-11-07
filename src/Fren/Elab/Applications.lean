-- keep-sorted start
import Fren.Elab.Closures
import Fren.Elab.Paths
-- keep-sorted end

/-! # Hosted elaboration: applications -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- An application `e` of the higher-order function `d` at `path`, whose
name is written `p`, to `elems` (`Reqs/Lang/HigherOrder#applications`):
its definition applied to its value arguments and then its closures, in
order, which unfolding reduces as the `fren` command unfolds them. -/
def hoAppTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e p : Syntax) (path : Name) (d : DefinedInfo)
    (elems : Array Syntax) (expected? : Option Core.Ty) : TermElabM Term := do
  unless elems.size == d.nParams do throwError (Core.arityMsg path d.nParams elems.size).text
  let f := Core.showPath path
  let synth ← elems.mapM (synthesizes cx)
  let run : StateT (Array Term × Array (Option ClosureTerm)) TermElabM (Array Core.Ty) :=
    Core.inferHigherOrder d.typeParams d.hoParams d.result synth expected?
      (throwErrorAt e (Core.cannotInferCallMsg f).text : TermElabM Unit)
      (fun k x? => do
        let t ← (toTerm { cx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk := x? == some Core.Ty.nat
                                  expected? := Core.ExprSite.functionArgument.expected x? none } elems[k]! : TermElabM Term)
        modify fun (ts, cs) => (ts.set! k t, cs)
        frenTypeOf? t)
      (fun k x t => (liftMsg elems[k]!
        (Core.checkType x t (some s!"note: argument {k + 1} of `{f}` has type `{x.show}`")) : TermElabM Unit))
      (fun k ps r? => do
        let .function ft := d.hoParams[k]! | return none
        let (c, pts, rt) ← (fnArgTerm toTerm cx f ft ps r? elems[k]! : TermElabM _)
        noteFnArg path k elems[k]!
        modify fun (ts, cs) => (ts.set! k c.term, cs.set! k (some c))
        return some (pts, rt))
      (fun k ft (_, rt) => (liftMsg elems[k]!
        (Core.checkType ft.result rt (some s!"note: the closure for argument {k + 1} of `{f}` returns `{ft.result.show}`")) : TermElabM Unit))
  let (targs, ts, closures) ← do
    let (targs, (ts, cs)) ← run.run (elems.map fun _ => default, elems.map fun _ => none)
    pure (targs, ts, cs)
  for a in elems, t in ts, k in [0:ts.size] do
    if d.hoParams[k]! matches .value _ then noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
  -- Its value arguments, then its closures (`Reqs/Generated#higher-order-functions`).
  let inOrder := (ts.zip d.hoParams).filterMap (fun (t, q) => if q matches .value _ then some t else none)
    ++ (ts.zip d.hoParams).filterMap fun (t, q) => if q matches .function _ then some t else none
  let generic := !d.typeParams.isEmpty
  notePreconditions cx p path inOrder (if generic then some (d.typeParams, targs) else none)
  -- Each closure's obligations, at each application of its function
  -- parameter in the unfolded body (`lang::closure_obligation`).
  if cx.noteIndexes then
    for c? in closures.filter Option.isSome, (decl, uses) in d.oblDecls do
      let some c := c? | continue
      for (ref, q?, pred) in c.obligations do
        let g ← if generic then `(@$(mkCIdent decl) $(← usesTerms uses path d.typeParams targs)* $inOrder* $pred)
          else `(@$(mkCIdent decl) $(uses.map fun u => ⟨(mkCIdent u).raw⟩)* $inOrder* $pred)
        modifyLocal fun l => { l with vias := l.vias.push (ref.getPos?, path) }
        match q? with
        | some q => modifyLocal fun l => { l with tables := l.tables.push (ref, q, g) }
        | none => modifyLocal fun l => { l with indexes := l.indexes.push (ref, g) }
  if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
  if generic then return ← `(@$(mkCIdentFrom p d.decl) $(← usesTerms d.uses path d.typeParams targs)* $inOrder*)
  `(@$(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $inOrder*)

open Lang in
/-- `p(args)`: a method, a variant with a payload, or a function applied.
`toTerm` translates its parts, and `parent?` is the expression around it. -/
def appTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax)
    (p : TSyntax ``fren_path) (args : Syntax.TSepArray `fren_expr ",") (expected? : Option Core.Ty := none) :
    TermElabM Term := do
  if let some (recv, m) := methodApp? cx e then
    let recv ← pathExpr p recv
    if m.toString == "matches?" then lintPattern cx parent? e recv args.getElems
    return ← methodTerm toTerm cx e p recv m.toString args.getElems cx.natOk
  let segs := pathSegs p
  if segs.size == 1 && (cx.vars.any (·.name == segs[0]!.getId) || (cx.binder? segs[0]!.getId).isSome) then
    throwErrorAt p (Core.varNotAFunctionMsg segs[0]!.getId).text
  if segs.size == 1 && cx.selfFn == some segs[0]!.getId then
    let f := cx.modName ++ segs[0]!.getId
    let some (ps, ft, fx) := cx.selfRec? | throwErrorAt p (Core.recursiveMsg f).text
    -- An application of itself, which must be structural recursion
    -- (`lang::structural_recursion`), typed as a function parameter's.
    unless args.getElems.size == ft.params.size do throwError (Core.arityMsg f ft.params.size args.getElems.size).text
    noteRecUse p f ps { form := if cx.inClosure then .inClosure else .applied
                        args := args.getElems.toList.zipIdx.map fun (a, i) => cx.recArg a i }
    let ts ← (args.getElems.zip ft.params).zipIdx.mapM fun ((a, t), k) => do
      let x ← toTerm { cx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk := false, expected? := Core.ExprSite.functionArgument.expected (some t) none } a
      if let some found ← frenTypeOf? x then
        liftMsg a (Core.checkType t found (some s!"note: argument {k + 1} of `{Core.showPath f}` has type `{t.show}`"))
      return x
    let ps := cx.vars.map (·.ptype)
    for a in args.getElems, t in ts, i in [0:ts.size] do
      noteObligation cx .argument a (ps[i]?.getD default) t
    if cx.noteIndexes then
      let vals ← ts.mapM fun t => Term.elabTerm t none
      let gs ← cx.guards.mapM elabProp
      modifyLocal fun l => { l with recApps := l.recApps.push (p, vals, gs) }
    return ← `($fx $ts*)
  -- A function parameter (`Reqs/Lang/HigherOrder#function-parameters`).
  if segs.size == 1 then
    if let some (ft, fx) := cx.fnParam? segs[0]!.getId then
      let f := segs[0]!.getId
      unless args.getElems.size == ft.params.size do throwError (Core.arityMsg f ft.params.size args.getElems.size).text
      let ts ← (args.getElems.zip ft.params).zipIdx.mapM fun ((a, t), k) => do
        let x ← toTerm { cx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk := false, expected? := Core.ExprSite.functionArgument.expected (some t) none } a
        if let some found ← frenTypeOf? x then
          liftMsg a (Core.checkType t found (some s!"note: argument {k + 1} of `{f}` has type `{t.show}`"))
        return x
      return ← `($fx $ts*)
  if let some c := cardinalityApp? e then return ← cardinalityTerm toTerm cx c args.getElems
  -- In its own contract, the function is applied to its parameters, in a
  -- postcondition (`lang::contract_application`); it is not yet in scope.
  let own? := cx.contract?.filter fun k => segs.size == 1 && segs[0]!.getId == Name.mkSimple k.path.getString!
  if let some k := own? then
    -- Each argument as written: a name of one segment, not hidden by a
    -- binder, or another expression.
    let written := args.getElems.map fun a =>
      let a := unparen a
      let a := if a.getNumArgs == 1 then a[0] else a
      if a.isOfKind ``Lang.fren_path && (pathSegs a).size == 1 && (cx.binder? (pathSegs a)[0]!.getId).isNone then
        some (pathSegs a)[0]!.getId
      else none
    let toParams := Core.appliesToParams written k.params
    unless Core.contractApplicationAccepted (if k.post then .postcondition else .precondition) true toParams do
      throwErrorAt p (Core.contractSelfMsg k.path !k.post).text
  -- A variable shadows a function, as it does any other item.
  let r ← match own? with
    | some k => pure (.item { kind := .fnItem, path := k.path, isPub := true, owner := cx.modName })
    | none => resolveWritten cx.modName (pathSegs p) cx.shadowing cx.noteIndexes
  if let .item { kind := .recordItem, path, .. } := r then
    -- A newtype, built from its value (`Reqs/Lang/Expressions#newtypes`).
    let some n := (← getState).newtypes.get? path | throwErrorAt p (Core.constructionMsg path false).text
    unless args.getElems.size == 1 do throwError (Core.arityMsg path 1 args.getElems.size "value").text
    let a := args.getElems[0]!
    let t ← toTerm { cx with emptyOk := Core.ExprSite.newtypeValue.checked false false, natOk := n.under.isConstOf ``Nat } a
    -- Its value is checked as the `fren` command checks it (`Core.checkType`).
    if let (true, some u) := (← synthesizes cx a, ← coreTy? n.under) then
      if let some found ← frenTypeOf? t then
        liftMsg a (Core.checkType u found (some s!"note: the value of `{Core.showPath path}` has type `{u.show}`"))
    if cx.noteIndexes then
      let synth ← synthesizes cx a
      modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .wraps path.toString synth) }
    noteObligation cx .construction a (partPType n.shape 0 0) t
    return ← `($(mkCIdentFrom p n.ctor) $t)
  if let .variant en idx := r then
    -- A variant with a payload, built from its values.
    let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
    let v := en.path ++ en.variants[idx]!
    let n := (info.payloads[idx]?.map (·.size)).getD 0
    if let some msg := Core.variantMentionMsg? v n true then throwError msg.text
    unless args.getElems.size == n do throwError (Core.arityMsg v n args.getElems.size "value").text
    let note (k : Nat) (ty : String) := s!"note: value {k + 1} of the payload of `{Core.showPath v}` has type `{ty}`"
    -- Of a generic enumeration, with its type arguments, which are inferred
    -- (`Reqs/Lang/Generics#type-arguments`).
    if let some c ← construction? cx e then
      let go (x? : Option Core.Ty) := toTerm { cx with emptyOk := Core.ExprSite.payload.checked false false, natOk := false, expected? := Core.ExprSite.payload.expected x? none }
      let (ts, targs) ← constructionTerms go cx expected? e c args.getElems (Core.showPath v) fun k t => note k t.show
      -- Each value's obligation, of its type with the enumeration's arguments.
      for a in args.getElems, t in ts, k in [0:ts.size] do
        noteObligation cx .payload a (partPType info.shape idx k targs) t
      return ← ctorApp (info.ctor idx) (info.leanArgs (← targs.mapM leanTypeOf)) ts p
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.ExprSite.payload.checked false false, natOk := info.payloads[idx]![k]!.isConstOf ``Nat,
                                expected? := Core.ExprSite.payload.expected (← coreTy? info.payloads[idx]![k]!) none } a
      checkDeclared a t info.payloads[idx]![k]! (note k)
      noteObligation cx .payload a (partPType info.shape idx k) t
      return t
    return ← `($(mkCIdentFrom p (info.ctor idx)) $args*)
  let .item { kind := .fnItem, path, .. } := r | throwErrorAt p (Core.notAFunctionMsg r).text
  unless cx.unmentioned do noteItemCore path
  -- A variable, written as its name, that is the argument at the
  -- decreasing parameter of a structural recursion
  -- (`lang::induction_candidate`).
  let writtenArgs := args.getElems.map fun a =>
    let a := unparen a
    let a := if a.getNumArgs == 1 then a[0] else a
    if a.isOfKind ``Lang.fren_path && (pathSegs a).size == 1 then some (pathSegs a)[0]!.getId else none
  if let some x := Core.inductionArgument? (((← getState).defined.get? path).bind (·.decreasing?))
      writtenArgs (cx.vars.map (·.name)) (fun x => (cx.binder? x).isSome) then
    modifyLocal fun l => { l with inductionArgs := l.inductionArgs.push x }
  if let some d := ((← getState).defined.get? path).filter (!·.hoParams.isEmpty) then
    return ← hoAppTerm toTerm cx e p path d args.getElems expected?
  if let some d := (← getState).defined.get? path then
    let argStxs := args.getElems
    -- Its definition, applied to the placeholders it uses; its arguments
    -- may mention anything (`lang::argument`).
    unless args.getElems.size == d.nParams do throwError (Core.arityMsg path d.nParams args.getElems.size).text
    if !d.typeParams.isEmpty then
      -- A generic function, at the instance whose type arguments are
      -- inferred, as the `fren` command infers them
      -- (`Reqs/Lang/GenericFunctions#applications`).
      let elems := args.getElems
      let synth ← elems.mapM (synthesizes cx)
      let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
        Core.inferCall d.typeParams d.declared d.result synth expected?
          (throwErrorAt e (Core.cannotInferCallMsg (Core.showPath path)).text : TermElabM Unit)
          (fun k x? => do
            let natOk := x? == some Core.Ty.nat
            let t ← (toTerm { cx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk, expected? := Core.ExprSite.functionArgument.expected x? none }
              elems[k]! : TermElabM Term)
            modify (·.set! k t)
            frenTypeOf? t)
          (fun k x f => (liftMsg elems[k]!
            (Core.checkType x f (some s!"note: argument {k + 1} of `{Core.showPath path}` has type `{x.show}`")) : TermElabM Unit))
      let (targs, ts) ← run.run (elems.map fun _ => default)
      for a in elems, t in ts, k in [0:ts.size] do
        noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
      notePreconditions cx p path ts (some (d.typeParams, targs))
      recordGenericUse path targs
      if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
      return ← `(@$(mkCIdentFrom p d.decl) $(← usesTerms d.uses path d.typeParams targs)* $ts*)
    let tys := paramTypes (← instantiateForall (← getConstInfo d.decl).type (d.uses.map mkConst))
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk := tys[k]!.isConstOf ``Nat, expected? := Core.ExprSite.functionArgument.expected (← coreTy? tys[k]!) none } a
      checkDeclared a t tys[k]! fun ty => s!"note: argument {k + 1} of `{Core.showPath path}` has type `{ty}`"
      noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
      return t
    notePreconditions cx p path args
    -- Its body's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
    return ← `(@$(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*)
  if cx.inClosure then throwErrorAt p (Core.closureUninterpretedMsg path).text
  if cx.selfFn.isSome then throwErrorAt p (Core.appliesUninterpretedMsg path).text
  modifyLocal fun l => { l with inductionAbstract := true }
  let a ← placeholderOf path
  if !a.typeParams.isEmpty then
    -- A generic function without a body, at the instance whose type
    -- arguments are inferred, as for a defined one: its placeholder applied
    -- to them and their `Inhabited` instances
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`). Outputs
    -- may not occur in its arguments (`inst::mention`).
    let acx := if cx.place == .prop then { cx with place := .argument } else cx
    let elems := args.getElems
    unless elems.size == a.declared.size do throwError (Core.arityMsg path a.declared.size elems.size).text
    let synth ← elems.mapM (synthesizes acx)
    let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
      Core.inferCall a.typeParams a.declared a.result synth expected?
        (throwErrorAt e (Core.cannotInferCallMsg (Core.showPath path)).text : TermElabM Unit)
        (fun k x? => do
          let natOk := x? == some Core.Ty.nat
          let t ← (toTerm { acx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk, expected? := Core.ExprSite.functionArgument.expected x? none }
            elems[k]! : TermElabM Term)
          modify (·.set! k t)
          frenTypeOf? t)
        (fun k x f => (liftMsg elems[k]!
          (Core.checkType x f (some s!"note: argument {k + 1} of `{Core.showPath path}` has type `{x.show}`")) : TermElabM Unit))
    let (targs, ts) ← run.run (elems.map fun _ => default)
    for x in elems, t in ts, k in [0:ts.size] do
      noteObligation acx .argument x (a.ptys.1[k]?.getD default) t
    notePreconditions cx p path ts (some (a.typeParams, targs))
    recordGenericUse path targs
    let tyArgs ← targs.flatMapM fun t => do
      let ty := typeSyntax (← leanTypeOf t)
      return #[ty, ← `(_)]
    return ← `(@$(mkCIdentFrom p a.placeholder) $tyArgs* $ts*)
  let a' := a
  let nParams := (← getConstInfo a.placeholder).type.getForallArity
  unless args.getElems.size == nParams do throwError (Core.arityMsg path nParams args.getElems.size).text
  -- Outputs may not occur in arguments (`inst::mention`); assumptions and
  -- bindings exclude them already.
  let acx := if cx.place == .prop then { cx with place := .argument } else cx
  let tys := paramTypes (← getConstInfo a.placeholder).type
  let args ← args.getElems.zipIdx.mapM fun (a, k) => do
    let t ← toTerm { acx with emptyOk := Core.ExprSite.functionArgument.checked false false, natOk := tys[k]!.isConstOf ``Nat, expected? := Core.ExprSite.functionArgument.expected (← coreTy? tys[k]!) none } a
    checkDeclared a t tys[k]! fun ty => s!"note: argument {k + 1} of `{Core.showPath path}` has type `{ty}`"
    noteObligation acx .argument a (a'.ptys.1[k]?.getD default) t
    return t
  notePreconditions cx p path args
  `($(mkCIdentFrom p a.placeholder) $args*)


end Fren
