-- keep-sorted start
import Fren.Elab.Blocks
import FrenCore.RecursionGroup
-- keep-sorted end

/-! # Hosted elaboration: mutual functions -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A signature registered before any body of a structural group. -/
structure MutualFunction where
  source : Syntax
  memberStx : Syntax
  path : Name
  decl : Name
  temporary : Name
  scope : Name
  vars : Array Var
  result : Expr
  resultP : Core.PTy
  leanValue : Expr := default
  solverValue : Expr := default
  tables : Array (Syntax × Option Core.TableGoal × Expr) := #[]
  declarations : Array (Name × Syntax) := #[]
  guarded : Bool := false
  outsideCore : Bool := false
  deriving Inhabited

/-- Explicit structural groups have forward scope only within the block.
Bodies are read against all signatures, then generated simultaneously. -/
def elabMutualCore (stx : Syntax) : CommandElabM Unit := do
  lintItem stx
  lintTrailingCommas stx
  let module := (← getLocal).currentModule
  let mut functions : Array MutualFunction := #[]
  modifyLocal fun l => { l with groupFns := #[], groupUses := #[] }
  let sources ← stx[2].getArgs.mapM fun source => do
    let (fn, uses) ← if source.isOfKind ``Lang.fnBlockCmd then lowerFnBlock source else pure (source, #[])
    unless fn.isOfKind ``Lang.fnCmd do throwErrorAt source Core.groupMemberMsg.text
    checkLexemes source
    checkParsed source
    return (source, ← liftTermElabM (anonymousMatchFunction fn), uses)
  -- Names are in scope even while parameter binders are checked, so a
  -- parameter hiding a later member needs the usual shadowing marker.
  for (_, fn, _) in sources do
    let name := fn[2]
    let n ← itemSegName name
    liftMsg name (Core.checkNoBang n)
    liftMsg name (Core.checkFnName n)
    checkFresh module n name
    let path := module ++ n
    let generic := !fn[3].isNone
    let higher := fn[5].getSepArgs.any fun p => p[1].getArgs.any fun t => t.isOfKind ``Lang.fnType
    unless Core.groupMemberAccepted (!fn[8].isNone) generic higher (!fn[9].getArgs.isEmpty) do
      throwErrorAt name Core.groupMemberMsg.text
    record (.item { item := { kind := .fnItem, path, isPub := !fn[0].isNone, owner := module }, ref := name })
  for (source, fn, uses) in sources do
    let name := fn[2]
    let n ← itemSegName name
    let path := module ++ n
    let decl ← generatedName path
    let temporary := decl ++ `groupSignature
    let params := fn[5].getSepArgs
    let named (p : Syntax) := !p[1].isNone ||
      (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (declaredIdent (pathSegs q)[0]!).1.getId.toString.endsWith "?"
    unless Core.functionParamsAccepted true false params.size (params.filter named).size do
      let bad := params.find? (!named ·) |>.getD name
      throwErrorAt bad (Core.functionParamsMsg path true false).text
    modifyLocal fun l => { l with currentItem := path }
    startDeclared
    for m in uses do
      if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
      else for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
    let scope := if uses.isEmpty then module else path
    let f ← liftTermElabM do
      let (vars, fnPs) ← paramVarsHo scope path params true
      unless fnPs.isEmpty do throwErrorAt name Core.groupMemberMsg.text
      lintFnBools n name (vars.map (·.type))
      let (result, rp) ← varPType scope name (if fn[7].isNone then none else some fn[7][1])
      let type := vars.foldr (fun v acc => .forallE v.name v.type acc .default) result
      addDecl (.axiomDecl { name := temporary, levelParams := [], type, isUnsafe := false })
      let declared ← vars.mapM fun v => return (← coreTy? v.type).getD .bool
      let resultTy := (← coreTy? result).getD .bool
      record (.definedInfo {
        path, decl := temporary, uses := #[], nParams := vars.size
        ptys := (vars.map (·.ptype), rp), declared, result := resultTy, recursive := true, solver? := some temporary })
      modifyLocal fun l => { l with groupFns := l.groupFns.push (path, { params := declared, result := resultTy }, temporary) }
      return ({
        source, memberStx := fn, path, decl, temporary, scope, vars, result, resultP := rp
        declarations := (← getLocal).declaredNames } : MutualFunction)
    functions := functions.push f
  if functions.isEmpty then return
  for f in functions, caller in [0:functions.size] do
    modifyLocal fun l => { l with
      groupCaller? := some caller, currentItem := f.path
      recMatches := #[], recUses := #[], outsideCore := false, guardedUsed := false, declaredNames := f.declarations }
    let body := withWhere f.memberStx[8][1] f.memberStx[8][2]
    let f ← withRef f.source <| liftTermElabM do
      let ft := (← getLocal).groupFns[caller]!.2.1
      let cx : ExprCtx := {
        modName := f.scope, vars := f.vars, insts := #[], place := .prop
        selfFn := some (Name.mkSimple f.path.getString!), selfRec? := some (f.vars.map (·.name), ft, ⟨(mkCIdent f.temporary).raw⟩)
        natOk := f.result.isConstOf ``Nat
        expected? := Core.ExprSite.functionBody.expected (some ft.result) none
        emptyOk := Core.ExprSite.functionBody.checked false false }
      withLocalDeclsD (f.vars.map fun v => (v.name, fun _ => pure v.type)) fun xs => do
        discard (takeIndexes xs)
        let t ← toTerm cx body
        if let some bad := (← getLocal).recMatches[0]? then throwErrorAt bad (Core.recursiveMatchMsg f.path).text
        checkDeclared body t f.result fun ty => s!"note: `{f.path.getString!}` returns `{ty}`"
        noteObligation cx .body body f.resultP t
        let elabValue (term : Term) : TermElabM Expr := if f.result.isConstOf ``Bool then do
            let p ← elabProp term
            let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
              | .some i => pure i
              | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
            pure (mkApp2 (mkConst ``Decidable.decide) p inst)
          else elabProp term f.result
        let value ← elabValue t
        let tables ← takeIndexes xs
        let leanValue ← keepingNames <| withDeclName (leanDeclName f.decl) do
          let saved ← saveState
          let t' ← toTerm { cx with leanMatch := true, leanBoolArms := true } body
          let mctx ← getMCtx
          saved.restore
          setMCtx mctx
          let v ← if f.result.isConstOf ``Bool && (← typeOf t').isConstOf ``Bool then
              elabProp t' f.result
            else elabValue t'
          mkLambdaFVars xs (← instantiateMVars v)
        lintBools body (← hidesIn cx)
        for (x, ref) in Core.unmentioned (f.vars.map fun v => (v.name, v.ref)) ((pathMentions body).map (·.getRoot)) do
          recordLint .unusedVariables ref (Core.unusedParamMsg x)
        return { f with leanValue, solverValue := ← mkLambdaFVars xs (← instantiateMVars value), tables,
                        guarded := (← getLocal).guardedUsed, outsideCore := (← getLocal).outsideCore }
    functions := functions.set! caller f
    lintName .function (Name.mkSimple f.path.getString!) f.memberStx[2]
    lintDeclared .function (Name.mkSimple f.path.getString!) f.memberStx[2]
    lintLines .function (Name.mkSimple f.path.getString!) f.memberStx[2] f.source
  let l ← getLocal
  let some positions := Core.recursionGroup (l.groupFns.toList.map fun (_, ft, _) => ft.params.size)
      (l.groupUses.toList.map (·.2)) | throwErrorAt stx Core.groupTerminationMsg.text
  let outside := Core.groupInherited (functions.toList.map (·.outsideCore)) (l.groupUses.toList.map (·.2))
  let guarded := Core.groupInherited (functions.toList.map (·.guarded)) (l.groupUses.toList.map (·.2))
  modifyLocal fun l => { l with groupCaller? := none }
  liftTermElabM do
    let uses ← usesOf (functions.flatMap fun f => #[f.leanValue, f.solverValue, f.result])
    let args := uses.map Lean.mkConst
    let replaceGroup (solver : Bool) (e : Expr) : Expr := e.replace fun
      | .const c _ => (functions.find? (·.temporary == c)).map fun f =>
          if solver then mkConst (solverName f.decl) else mkAppN (mkConst f.decl) args
      | _ => none
    let mut predefs := #[]
    for f in functions do
      let mut value := replaceGroup false f.leanValue
      -- Generalize matchers over the same placeholders as their definitions.
      let tmp := leanDeclName f.decl
      for m in value.foldConsts #[] (fun c acc => if c.getPrefix == tmp && !acc.contains c then acc.push c else acc) do
        let some info ← Meta.getMatcherInfo? m | throwError "internal error: missing group matcher"
        let .defnInfo ci ← getConstInfo m | throwError "internal error: missing group matcher definition"
        let m' := f.decl ++ Name.mkSimple m.getString!
        let mUses ← usesOf #[ci.type, ci.value]
        let (mty, mval) ← withUses mUses fun xs => do
          return (← mkForallFVars xs (replaceUses mUses xs ci.type), ← mkLambdaFVars xs (replaceUses mUses xs ci.value))
        addDecl (.defnDecl { name := m', levelParams := ci.levelParams, type := mty, value := mval, hints := ci.hints, safety := .safe })
        Meta.Match.addMatcherInfo m' { info with numParams := info.numParams + mUses.size }
        setInlineAttribute m'
        enableRealizationsForConst m'
        value := value.replace fun e => match e with
          | .const c ls => if c == m then some (mkAppN (.const m' ls) (mUses.map Lean.mkConst)) else none
          | _ => none
      let type := f.vars.foldr (fun v acc => .forallE v.name v.type acc .default) f.result
      let (type, generalized) ← withUses uses fun xs => do
        return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs value))
      let mentions ← (generalized.foldConsts #[] fun c acc => if functions.any (·.decl == c) then acc else acc.push c).mapM (liftM <| mentionOf ·)
      let kind := if f.result.isProp then ValueKind.proposition else .data
      let computeKind := if definitionForm kind mentions == .compiled then .regular else .noncomputable
      predefs := predefs.push {
        ref := f.source, kind := .def, levelParams := [], modifiers := { computeKind }
        declName := f.decl, binders := .missing, type, value := generalized, termination := .none }
    let noncomputableMembers := Core.groupInherited (predefs.toList.map fun p =>
      match p.modifiers.computeKind with | .noncomputable => true | _ => false) (l.groupUses.toList.map (·.2))
    predefs := predefs.mapIdx fun i p => if noncomputableMembers.contains i then
      { p with modifiers := { p.modifiers with computeKind := .noncomputable } } else p
    addPreDefinitions ({}, {}) predefs
    for f in functions do
      let type := f.vars.foldr (fun v acc => .forallE v.name v.type acc .default) f.result
      let value := mkAppN (mkConst f.decl) args
      addDecl (.defnDecl { name := solverName f.decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      compileGenerated (solverName f.decl) type value
    for f in functions, position in positions, index in [0:functions.size] do
      modifyLocal fun l => { l with outsideCore := outside.contains index, guardedUsed := guarded.contains index }
      let st ← getState
      let ds := st.defined.foldl (init := ({} : NameSet)) fun acc _ d => acc.insert d.decl
      let body ← Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined st (replaceGroup true f.solverValue) ds.contains))
      let declared ← f.vars.mapM fun v => return (← coreTy? v.type).getD .bool
      record (.definedInfo {
        path := f.path, decl := f.decl, uses, nParams := f.vars.size
        ptys := (f.vars.map (·.ptype), f.resultP), declared, result := (← coreTy? f.result).getD .bool
        guarded := guarded.contains index
        recursive := true, solver? := some (solverName f.decl), recBody? := some body
        decreasing? := some position.decreasing.toNat, fact? := ← resultFact? f.result f.resultP
        source? := some (← keptFileName (← getFileName), ← getFileMap) })
      let tables := f.tables.map fun (r, q, g) => (Name.mkSimple f.path.getString!, Core.IndexPlace.body, r, q, replaceGroup true g)
      recordBody f.path f.memberStx[2] f.decl f.vars tables #[] (some f.path)
      record (.itemCore f.path (!outside.contains index))
  for f in functions do
    unless !f.memberStx[0].isNone do recordItem .function f.path f.memberStx[2] (defined := true)
    elabCommand (← `(attribute [fren_spec] $(mkCIdent f.decl)))
  modifyLocal fun l => { l with groupFns := #[], groupUses := #[], groupCaller? := none }

@[command_elab Lang.mutualCmd] def elabMutual : CommandElab := recordingErrors fun stx => do
  let env ← getEnv
  try elabMutualCore stx
  catch ex =>
    -- A rejected group publishes none of its provisional signatures.
    let failed ← getLocal
    setEnv env
    -- Its lint observations survive, as the CLI's keepLints retains them.
    modifyLocal fun l => { l with
      lintReports := failed.lintReports, used := failed.used, usedItems := failed.usedItems
      useRecords := failed.useRecords, items := failed.items, declaredNames := failed.declaredNames
      seenSettings := failed.seenSettings, hofParams := failed.hofParams, fnArgs := failed.fnArgs }
    throw ex

end Fren
