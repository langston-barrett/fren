-- keep-sorted start
import Fren.Check
import Lean.Elab.Tactic
-- keep-sorted end

/-! Structural induction proofs for recursive contracts. Solver steps use the
same trust setting as other hosted checks. Every generated case must close. -/

open Lean Meta Elab Tactic

namespace Fren

/-- The modular assumption for one dependency clause, including its input domain. -/
def recursiveDependencyType (path : Name) (p : ClauseInfo) : MetaM Expr := do
  let st ← getState
  let some b := st.bodies.get? path | throwError "missing recursive dependency body"
  let some k := st.contracts.get? path | throwError "missing recursive dependency contract"
  withLocalDeclsD (b.vars.map fun v => (v.name, fun _ => pure v.type)) fun xs => do
    let pres := ((b.vars.zip xs).filterMap fun (v, x) => v.fact?.map (·.beta #[x]))
      ++ k.pres.map (·.at xs)
    mkForallFVars xs (pres.foldr (fun h body => mkForall `h .default h body) (p.at xs))

/-- Only unconditional theorems discharge a modular dependency outright. -/
def hasRecursiveDependencyProof (p : ClauseInfo) (type : Expr) : MetaM Bool := do
  let some info := (← getEnv).find? (p.decl ++ `holds) | return false
  isDefEq info.type type

/-- Add contracts at both written and reflected applications, then discharge
the case. Self contracts come only from smaller arguments' induction facts. -/
elab "fren_recursive_case" self:ident ihName:(ident)? : tactic => do
  let initial ← getMainGoal
  initial.withContext do
    let g := initial
    let strongIH ← ihName.mapM fun n => getFVarId n
    let st ← getState
    let mut fs := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && (← isProp d.type) then
        if d.type.isForall then
          if !(← isProp d.type.bindingDomain!) then continue
        fs := fs.push d.type
    -- Generalized induction hypotheses are instantiated at the actual
    -- recursive arguments. No quantifier over function inputs reaches SMT.
    let initialHyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail then acc.push d.toExpr else acc
    let hyps ← fs.mapM fun f => return (`hypothesis, ← unfoldDefined f)
    let goal ← unfoldDefined (← g.getType)
    let actual (e : Expr) := e.replace fun t => st.defined.foldl (init := none) fun acc _ d =>
      if d.solver?.any t.isConstOf then some (mkConst d.decl) else acc
    let facts ← recursiveQueryFacts hyps goal fun d solverApp guards => do
      let guards := guards.map actual
      withLocalDeclsD (guards.map fun p => (`guard, fun _ => pure p)) fun _ => do
        let app := actual solverApp
        if d.decl != self.getId then
          let some k := st.contracts.get? d.path | return true
          for p in k.posts do
            let type ← recursiveDependencyType d.path p
            if ← hasRecursiveDependencyProof p type then continue
            let mut found := false
            for h in initialHyps do
              if ← isDefEq (← inferType h) type then found := true; break
            unless found do return false
          return true
        let mut names := #[]
        let mut fnType := (← getConstInfo d.decl).type
        while fnType.isForall do
          names := names.push fnType.bindingName!
          fnType := fnType.bindingBody!
        let args := app.getAppArgs
        let some k := st.contracts.get? d.path | return false
        let domain := ((st.bodies.get? d.path).map fun b =>
          (b.vars.zip args).filterMap fun (v, x) => v.fact?.map (·.beta #[x])).getD #[]
        let pres := domain ++ k.pres.map (·.at args)
        let expected := pres.foldr (fun p b => mkForall `h .default p b)
          (mkAndN (k.posts.map (·.at args)).toList)
        let expected := actual (← unfoldDefined expected)
        for ih in initialHyps do
          let mut proof := ih
          let mut ty ← inferType ih
          if strongIH == some ih.fvarId! then
            let some i := d.decreasing? | continue
            -- Captured placeholders precede the function's declared parameters.
            let arg := args[d.uses.size + i]!
            proof := mkApp proof arg
            ty ← inferType proof
            let bound ← mkFreshExprMVar ty.bindingDomain!
            let argType ← inferType arg
            let sizeDef := mkIdent (argType.getAppFn.constName!.str "_sizeOf_1")
            let saved ← saveState
            try
              -- Selector matches are split only inside this one decrease
              -- obligation, never across the independent solver equations.
              let env ← getEnv
              let selectors := (arg.getUsedConstants ++ guards.flatMap (·.getUsedConstants)).filter fun n =>
                match env.find? n with
                | some (.defnInfo _) => argType.getAppFn.constName!.isPrefixOf n
                | _ => false
              let selectors := selectors.map mkIdent
              let (goals, _) ← Lean.Elab.runTactic bound.mvarId! (← `(tactic|
                (try simp_all +arith [WellFoundedRelation.rel, InvImage, sizeOf, $sizeDef:ident, $[$selectors:ident],*])
                <;> (repeat' first | split)
                <;> (try simp_all +arith [sizeOf, $sizeDef:ident])))
              unless goals.isEmpty do
                throwError "not a smaller recursive argument"
              proof := mkApp proof (← instantiateMVars bound)
              ty ← inferType proof
            catch _ =>
              saved.restore
              continue
          while ty.isForall do
            if ← isProp ty.bindingDomain! then break
            let some i := names.idxOf? ty.bindingName! | break
            let some arg := args[i]? | break
            proof := mkApp proof arg
            ty := ty.bindingBody!.instantiate1 arg
          if ← isDefEq (actual (← unfoldDefined ty)) expected then
            return true
        return false
    let facts := facts.map fun (n, f) => (n, actual f)
    -- As in the hosted backend, the trusted solver receives the finite
    -- encoding as local hypotheses. Self contracts above require induction
    -- evidence; equations stay guarded, with no constructor case product.
    withLocalDeclsD (facts.map fun (n, f) => (n, fun _ => pure f)) fun _ => do
      let hs ← (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail then return acc
        if d.type.isForall then
          if !(← isProp d.type.bindingDomain!) then return acc
        return acc.push d.toExpr
      let opts ← getOptions
      let timeout := fren.timeout.get opts
      let query ← mkFreshExprMVar (← g.getType)
      match ← Smt.smt { trust := true, timeout := some (if timeout == 0 then 30 else min 30 timeout)
                        extraSolverOptions := Core.solverOptions true true ++ resourceLimitOptions opts }
          query.mvarId! hs with
      | .unsat .. =>
        g.assign (← instantiateMVars query)
        replaceMainGoal []
      | .sat .. => throwError "recursive induction case is not implied by its one-step equations and induction hypotheses"
      | .unknown reason => throwError "recursive induction case is inconclusive: {reason}"

end Fren
