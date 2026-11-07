-- keep-sorted start
import Fren.Elab.AbstractTypes
import Fren.Elab.Contracts
-- keep-sorted end

/-! # Hosted elaboration: functions -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Command elaboration passes its state's recursion limit to Core and
Term elaboration; changing the scope's option alone does not raise it.
Leave room for representation wrappers until Core admits the source tree. -/
def withEvaluationHeadroom (action : CommandElabM α) : CommandElabM α := do
  let before ← MonadRecDepth.getMaxRecDepth
  let raised := max before (16 * Core.Enumeration.maxEvalDepth)
  try
    modify fun state => { state with maxRecDepth := raised }
    withScope (fun scope => { scope with opts := maxRecDepth.set scope.opts raised }) action
  finally
    modify fun state => { state with maxRecDepth := before }

/-- Elaborates the function `stx`, a `fnCmd`, as written or as a function
written with a block lowers to (`elabFnBlock`): `orig` is the command as
written, whose lexemes, layout and lines are checked. -/
def elabFunctionCore (stx orig : Syntax) (uses : Array Syntax := #[]) : CommandElabM Unit :=
    withEvaluationHeadroom do
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
  checkLexemes orig
  checkParsed orig
  lintItem orig
  lintTrailingCommas orig
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  liftMsg nameStx (Core.checkFnName n)
  checkFresh modName n nameStx
  lintName .function n nameStx
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  -- The `use`s of its block, and the scope that its paths resolve in, as
  -- a procedure's (`Reqs/Lang/Items#function-blocks`).
  for m in uses do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if uses.isEmpty then modName else path
  let stx ← liftTermElabM <| anonymousMatchFunction stx
  let params := stx[5].getSepArgs
  let body? := if stx[8].isNone then none else some (withWhere stx[8][1] stx[8][2])
  let clauses := stx[9].getArgs
  -- Its type parameters, which are abstract types within it, whether it
  -- is defined or not (`lang::generic_function`).
  let tpStxs := if stx[3].isNone then #[] else stx[3][0][1].getSepArgs
  let tps ← elabTypeParams scope tpStxs
  if !tps.isEmpty then
    liftTermElabM do
      for p in tps, k in [0:tps.size] do declarePlaceholder (Core.typeParamPath path k p) (mkSort Level.one) true
    modifyLocal fun l => { l with fnTypeParams := some (path, tps) }
  let contract := !clauses.isEmpty
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Syntax) := !p[1].isNone ||
    (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (declaredIdent (pathSegs q)[0]!).1.getId.toString.endsWith "?"
  let nNamed := (params.filter named).size
  unless Core.functionParamsAccepted body?.isSome contract params.size nNamed do
    let bad := params.find? (named · != (body?.isSome || contract)) |>.getD nameStx
    throwErrorAt bad (Core.functionParamsMsg path body?.isSome contract).text
  let decl ← generatedName path
  -- A generic function's signature, with its type parameters as
  -- `Core.Ty.param`, each inferred at applications from it
  -- (`lang::generic_signature`).
  let signature (params : Array Expr) (result : Expr) : TermElabM (Array Core.Ty × Core.Ty) := do
    let asParams (t : Expr) : TermElabM Core.Ty := return ((← coreTy? t).getD .bool).asParams path tps
    let declared ← params.mapM asParams
    let resultTy ← asParams result
    if let some k := Core.firstUnmentioned? declared resultTy tps.size then
      throwErrorAt tpStxs[k]! (Core.unmentionedTypeParamMsg n tps[k]!).text
    return (declared, resultTy)
  -- Without a body, a placeholder, which takes a `Type` and its `Inhabited`
  -- instance for each type parameter first, if it is generic: each
  -- instance is an unknown function of its own
  -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
  let placeholder (params : Array Expr) (ptys : Array Core.PTy) (result : Expr) (rp : Core.PTy) : TermElabM Unit := do
    let (declared, resultTy) ← signature params result
    let type ← withTypeParams path tps (← mkArrowN params result)
    declarePlaceholder path type false (ptys, rp) (← resultFact? result rp) tps declared resultTy (rp.asParams path tps)
  let some body := body? | do
    liftTermElabM do
      if contract then
        let vars := (← paramVarsHo scope path params false).1
        lintFnBools n nameStx (vars.map (·.type))
        let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
        placeholder (vars.map (·.type)) (vars.map (·.ptype)) result rp
        modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
        let (vars, props, sites) ← elabContract scope path n decl false vars clauses
        recordBody path nameStx decl vars sites props path
      else
        let pps ← params.mapM fun p => do lintRelTypes scope p[0]; elabPType scope p[0]
        let params := pps.map (·.1)
        lintFnBools n nameStx params
        -- As for a variable, with the result type (`lang::bool_naming`).
        let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
        placeholder params (pps.map (·.2)) result rp
    if contract then
      lintDeclared .function n nameStx
      lintLines .function n nameStx orig
    record (.itemCore path (!(← getLocal).outsideCore))
    record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
    -- A trait's method is never dead (`lint::dead_item`).
    unless isPub do recordItem (if (← getLocal).inTrait then .method else .function) path nameStx
    modifyLocal fun l => { l with fnTypeParams := none }
  liftTermElabM do
    -- The parameters, declared like a procedure's parameters, and the function
    -- parameters (`Reqs/Lang/HigherOrder#function-parameters`).
    let (vars, fnPs) ← paramVarsHo scope path params true
    lintFnBools n nameStx (vars.map (·.type))
    let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
    -- Each type parameter is inferred at applications from the signature
    -- (`lang::generic_signature`), where a function parameter's type
    -- stands for its parameters' and its result's.
    let asParams (t : Expr) : TermElabM Core.Ty := return ((← coreTy? t).getD .bool).asParams path tps
    let declared ← vars.mapM (asParams ·.type)
    let resultTy ← asParams result
    let fnDeclared := fnPs.flatMap fun (_, _, _, ft, _) => (ft.asParams path tps).params.push (ft.asParams path tps).result
    if let some k := Core.firstUnmentioned? (declared ++ fnDeclared) resultTy tps.size then
      throwErrorAt tpStxs[k]! (Core.unmentionedTypeParamMsg n tps[k]!).text
    -- Each function parameter is an uninterpreted function, of its
    -- placeholder, for the function's own checks.
    for (_, x, _, _, lty) in fnPs do declarePlaceholder (path ++ x) lty false
    let fnVars := fnPs.map fun (_, x, _, ft, lty) => (x, ft, lty, placeholderName (path ++ x))
    let phs : Array Expr := fnVars.map fun p => Lean.mkConst p.2.2.2
    modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
    -- A first-order function, generic or not, may apply itself, in a
    -- structural recursion (`lang::self_application`,
    -- `lang::structural_recursion`): within the body, a local of its type
    -- stands for it, which its definitions replace with themselves. A
    -- generic one's solver form takes its type parameters' types and
    -- `Inhabited` instances first, and applies itself at the placeholders
    -- of its own (`addRecursiveDefs`).
    let selfName := n.appendAfter "#self"
    let recursive := Core.selfApplicable (!tps.isEmpty) (!fnPs.isEmpty)
    let tpConsts := (typeParamPlaceholders path tps).map (Lean.mkConst ·)
    let selfTy := vars.foldr (fun v acc => .forallE v.name v.type acc .default) result
    let withSelf {α : Type} (k : Option Expr → TermElabM α) : TermElabM α :=
      if recursive then withLocalDeclD selfName selfTy fun s => k (some s) else k none
    let (lam, tables, obls, leanLam?, recLeanLam?, recIdx?, selfApps) ← withLocalDeclsD (fnVars.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
        withSelf fun self? => withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let all := fvs ++ fnFvs
      -- A generic one's at its own type parameters, abstract types there.
      let selfRec? := if recursive then some (vars.map (·.name),
        ({ params := declared.map (·.asAbstract path tps), result := resultTy.asAbstract path tps } : Core.FnTy),
        (⟨(mkIdent selfName).raw⟩ : Term)) else none
      -- The body is checked against the result type (`lang::checked`).
      let cx : ExprCtx := { modName := scope, vars, insts := #[], place := .prop
                            selfFn := if (← getLocal).inSubset then none else some n, natOk := result.isConstOf ``Nat
                            expected? := Core.ExprSite.functionBody.expected (← coreTy? result) none, emptyOk := Core.ExprSite.functionBody.checked false false
                            fnParams := fnVars.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)), selfRec? }
      discard (takeIndexes fvs)
      modifyLocal fun l => { l with recUses := #[], recApps := #[], recMatches := #[] }
      let t ← toTerm cx body
      let uses := (← getLocal).recUses
      -- Existing self-recursion is a singleton structural group.
      let recursion := Core.selfRecursion vars.size (uses.toList.map (·.2))
      let structural := recursion matches .structural _
      if structural then
        if let some m := (← getLocal).recMatches[0]? then throwErrorAt m (Core.recursiveMatchMsg path).text
      noteObligation cx .body body rp t
      -- Its tables, the applications of functions with preconditions, and
      -- its subset types' obligations, for their checks; its indexes are
      -- not checked.
      -- A structural recursion's applications of itself are of its solver
      -- form there (`DefinedInfo.recursive`).
      let selfFor (x : Expr) : Expr := match self? with
        | some s => x.replaceFVar s (mkAppN (Lean.mkConst (solverName decl)) tpConsts)
        | none => x
      let tables := (← takeIndexes fvs (fun (x : Expr) => selfFor (x.replaceFVars fnFvs phs))).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
      checkDeclared body t result fun ty => s!"note: `{n}` returns `{ty}`"
      -- A `Bool` body is decided, classically if need be: equality on an
      -- abstract type has no other `Decidable` instance.
      let elabValue (t : Term) : TermElabM Expr := do
        if result.isConstOf ``Bool then
          let p ← elabProp t
          let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
            | .some i => pure i
            | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
          pure (mkApp2 (mkConst ``Decidable.decide) p inst)
        else elabProp t result
      let value ← elabValue t
      -- The Lean definition's value, where the body has a `match` or a
      -- pattern test: the body translated again, with each `match` Lean's
      -- where it can be (`Reqs/Generated#matches`). What that translation
      -- records and reports is dropped, as the first's stands; where it
      -- fails, the definition is the solver's.
      let leanValue? ← if !structural && (body.find? fun x => isMatchLike x || x.isOfKind ``Lang.isExpr).isNone then pure none else
        keepingNames <| withDeclName (leanDeclName decl) do
          let saved ← saveState
          try
            let t' ← toTerm { cx with leanMatch := true, leanBoolArms := structural } body
            -- But the metavariables, which the terms of the types that `t'`
            -- is written with stand for (`exprToSyntax`).
            let mctx ← getMCtx
            saved.restore
            setMCtx mctx
            -- A structural recursion's `Bool` body is a `Bool`, a Lean
            -- `match` of its arms' `decide`s, rather than decided again.
            let v ← if structural && result.isConstOf ``Bool then elabProp t' result else elabValue t'
            some <$> (instantiateMVars v)
          catch _ =>
            saved.restore
            pure none
      -- For each function parameter, its closures' obligations: over the
      -- parameters and a predicate of the closure's parameters
      -- (`lang::closure_obligation`).
      let unfolded ← if fnFvs.isEmpty then pure value else unfoldForSites value
      let obls ← fnFvs.mapM fun f => do
        let pty ← forallTelescope (← inferType f) fun xs _ => mkForallFVars xs (mkSort .zero)
        withLocalDeclD `p pty fun pr => do
          let gs ← siteGoals f pr [] unfolded
          let body := if gs.isEmpty then Lean.mkConst ``True else gs.pop.foldr mkAnd gs.back!
          mkLambdaFVars (all.push pr) body
      -- A structural recursion's Lean definition is a Lean `match`, which
      -- `lang::recursive_match` makes sure there is: over itself first.
      let recLean? ← if !structural then pure none else
        match leanValue?, self? with
        | some v, some s => pure (some (← mkLambdaFVars #[s] (← mkLambdaFVars all v)))
        | _, _ => throwErrorAt nameStx s!"internal error: no Lean definition of the structural recursion `{n}`"
      return (selfFor (← mkLambdaFVars all value), tables, obls, ← leanValue?.mapM (mkLambdaFVars all ·), recLean?,
        (match recursion with | .structural i => some i | _ => none),
        ← (← getLocal).recApps.mapM fun (r, args, gs) => do
          return (r, ← args.mapM fun x => do mkLambdaFVars fvs (selfFor (← instantiateMVars x)),
            ← gs.mapM fun x => do mkLambdaFVars fvs (selfFor (← instantiateMVars x))))
    lintBools body (← hidesIn { modName := scope, vars, insts := #[], place := .prop, selfFn := some n })
    -- A parameter that only the contract mentions is used too.
    let mentioned := (pathMentions body ++ clauses.flatMap fun c => pathMentions (withWhere c[3] c[4])).map (·.getRoot)
    let mentioned := if fnPs.isEmpty then mentioned
      else mentioned ++ appliedNames body ++ clauses.flatMap fun c => appliedNames (withWhere c[3] c[4])
    -- In order, a function parameter among the others.
    let paramRefs := Id.run do
      let mut out := vars.map fun v => (v.name, v.ref)
      for (j, x, ref, _, _) in fnPs do out := out.insertIdxIfInBounds j (x, ref)
      return out
    for (x, ref) in Core.unmentioned paramRefs mentioned do
      recordLint .unusedVariables ref (Core.unusedParamMsg x)
    -- A generic structural recursion's take every type parameter's
    -- placeholder and that of its `Inhabited` instance, which its solver
    -- form takes first (`addRecursiveDefs`).
    let uses ← usesOf (#[lam] ++ if recLeanLam?.isSome then tpConsts else #[])
    -- Where its Lean definition is a Lean `match`, the solver's is beside it
    -- (`DefinedInfo.solver?`).
    -- A structural recursion's body as the solver reads it, with the
    -- defined functions it applies unfolded, as a query's are.
    let recBody? ← if recLeanLam?.isNone then pure none else do
      let st ← getState
      let ds := st.defined.foldl (init := ({} : NameSet)) fun acc _ d => acc.insert d.decl
      some <$> Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined st lam ds.contains (keepLastArm := true) (keepEvaluation := true)))
    let recValue ← IO.mkRef (none : Option Expr)
    let solver? ← match recLeanLam?, leanLam? with
      | some recLean, _ =>
        let v ← addRecursiveDefs nameStx uses decl recLean (typeParamPlaceholders path tps)
        unless tps.isEmpty do recValue.set (some v)
        pure (some (solverName decl))
      | none, none => addUsesDef uses decl lam; pure none
      | none, some leanLam =>
        let saved ← saveState
        try
          -- As many names as `addUsesDef uses decl lam` would take.
          keepingNames (addLeanDef uses decl leanLam)
          addUsesDef uses (solverName decl) lam (compile := false)
          modifyEnv (addNoncomputable · (solverName decl))
          pure (some (solverName decl))
        catch _ =>
          saved.restore
          addUsesDef uses decl lam
          pure none
    let oblDecls ← (obls.zip fnVars).mapM fun (o, x, _) => do
      let name := decl ++ `obligation ++ x
      let ouses ← usesOf #[o]
      addUsesDef ouses name o
      return (name, ouses)
    let ptys := Id.run do
      let mut out := vars.map (·.ptype)
      for (j, _, _, ft, _) in fnPs do out := out.insertIdxIfInBounds j (.plain ft.result)
      return out
    let hoParams := Id.run do
      let mut out := declared.map Core.HoParam.value
      for (j, _, _, ft, _) in fnPs do out := out.insertIdxIfInBounds j (.function (ft.asParams path tps))
      return if fnPs.isEmpty then #[] else out
    let (namedMembers, namedBranchGroups, namedMemberGroups) ← if resultTy == .bool && (← getLocal).recUses.isEmpty then
        predicateMetadata scope vars fnVars body else pure (#[], #[], #[])
    unless isPub do
      for (j, x, ref, _, _) in fnPs do
        let r : Core.HofParamRecord :=
          { path, index := j, name := x, generic := !tps.isEmpty, level := ← lintLevel .needlessHigherOrder }
        modifyLocal fun l => { l with hofParams := l.hofParams.push (r, ref) }
    let source? := some (← keptFileName (← getFileName), ← getFileMap)
    record (.definedInfo { path, decl, uses, nParams := vars.size + fnPs.size, ptys := (ptys, rp)
                           guarded := (← getLocal).guardedUsed, typeParams := tps
                           declared := if hoParams.isEmpty then declared else hoParams.map (·.ty), result := resultTy, hoParams
                           oblDecls, solver?, namedMembers, namedBranchGroups, namedMemberGroups, source?, recursive := recLeanLam?.isSome, recBody?, recValue? := ← recValue.get, decreasing? := recIdx?
                           evalBody? := if recLeanLam?.isSome then none else some lam
                           fact? := ← if recIdx?.isSome then (← resultFact? result rp).mapM instantiateMVars else pure none })
    let (_, props, sites) ← if contract then elabContract scope path n decl true vars clauses fnVars (paramRefs.map (·.1)) else pure (vars, #[], #[])
    let selfSites ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let k := (← getState).contracts.get? path
      let mut out := #[]
      for (ref, args, gs) in selfApps do
        let args := args.map (·.beta fvs)
        let gs := gs.map (·.beta fvs)
        for p in (k.map (·.pres)).getD #[] do
          let g := gs.foldr (fun g b => mkForall `h .default g b) (p.at args)
          out := out.push (n, Core.IndexPlace.body, ref, some (Core.TableGoal.precondition path p.name), ← mkLambdaFVars fvs g)
      return out
    recordBody path nameStx decl vars (tables.map (fun (r, q, g) => (n, .body, r, q, g)) ++ sites ++ selfSites) props path
  lintDeclared .function n nameStx
  lintLines .function n nameStx orig
  record (.itemCore path (!(← getLocal).outsideCore))
  record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem (if (← getLocal).inTrait then .method else .function) path nameStx (defined := true)
  modifyLocal fun l => { l with fnTypeParams := none }
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))


/-- A function without a block: uninterpreted, or with a body. -/
@[command_elab Lang.fnCmd] def elabFunction : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  elabFunctionCore stx stx


end Fren
