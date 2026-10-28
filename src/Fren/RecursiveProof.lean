-- keep-sorted start
import Fren.Check
import Lean.Elab.Tactic
-- keep-sorted end

/-! Structural induction proofs for recursive contracts. Solver steps use the
same trust setting as other hosted checks. Every generated case must close. -/

open Lean Meta Elab Tactic

namespace Fren

/-- Collect ground applications, without instantiating quantified inputs. -/
partial def recursiveProofApps (heads : Array Name) (e : Expr) : Array Expr :=
  if e.hasLooseBVars then #[] else
    (if heads.contains (e.getAppFn.constName?.getD .anonymous) && e.isApp then #[e] else #[])
      ++ match e with
      | .app .. => e.getAppArgs.flatMap (recursiveProofApps heads)
      | .forallE _ p q _ => recursiveProofApps heads p ++ recursiveProofApps heads q
      | .mdata _ b => recursiveProofApps heads b
      | _ => #[]

/-- Split only the new equations, retaining constructor guards in each case. -/
partial def splitRecursiveEquations (names : Array Name) (g : MVarId) : MetaM (List MVarId) :=
  g.withContext do
    for d in (← getLCtx) do
      if names.contains d.userName then
        if let some goals ← splitLocalDecl? g d.fvarId then
          return (← goals.mapM (splitRecursiveEquations names)).flatten
    return [g]

/-- Reflect only the original applications. Splitting the resulting matches
exposes their payloads before collecting contract applications; those new
applications receive facts, but never enter this equation pass again. -/
elab "fren_recursive_equations" : tactic => do
  let initial ← getMainGoal
  initial.withContext do
    let st ← getState
    let heads := st.defined.foldl (init := #[]) fun acc _ d => if d.recursive then acc.push d.decl else acc
    let mut fs := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && (← isProp d.type) then
        if d.type.isForall then
          if !(← isProp d.type.bindingDomain!) then continue
        fs := fs.push d.type
    fs := fs.push (← initial.getType)
    let apps := (fs.flatMap (recursiveProofApps heads)).toList.eraseDups.toArray
    let mut g := initial
    let mut equations := #[]
    for app in apps do
      let some head := app.getAppFn.constName? | continue
      let r ← unfold app head
      unless r.expr == app do
        let proof ← r.getProof
        let name ← mkFreshUserName `equation
        let next ← g.assert name (← mkEq app r.expr) proof
        let (id, next) ← next.intro1P
        g := next
        equations := equations.push (← next.withContext id.getUserName)
    replaceMainGoal (← splitRecursiveEquations equations g)

/-- Add contracts at both written and reflected applications, then discharge
the case. Self contracts come only from smaller arguments' induction facts. -/
elab "fren_recursive_case" self:ident : tactic => do
  let initial ← getMainGoal
  initial.withContext do
    let mut g := initial
    let st ← getState
    let heads := st.defined.foldl (init := #[]) fun acc _ d => if d.recursive then acc.push d.decl else acc
    let mut fs := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && (← isProp d.type) then
        if d.type.isForall then
          if !(← isProp d.type.bindingDomain!) then continue
        fs := fs.push d.type
    fs := fs.push (← g.getType)
    let apps := (fs.flatMap (recursiveProofApps heads)).toList.eraseDups.toArray
    -- Generalized induction hypotheses are instantiated at the actual
    -- recursive arguments. No quantifier over function inputs reaches SMT.
    let initialHyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail then acc.push d.toExpr else acc
    for app in apps do
      let some d := st.defined.foldl (init := none) (fun acc _ d =>
        if app.getAppFn.isConstOf d.decl then some d else acc) | continue
      let mut names := #[]
      let mut fnType := (← getConstInfo d.decl).type
      while fnType.isForall do
        names := names.push fnType.bindingName!
        fnType := fnType.bindingBody!
      let args := app.getAppArgs
      for ih in initialHyps do
        let mut proof := ih
        let mut ty ← inferType ih
        let mut changed := false
        if ((← getLCtx).get! ih.fvarId!).userName == `recursive_ih then
          if d.decl != self.getId then continue
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
            let (goals, _) ← Lean.Elab.runTactic bound.mvarId! (← `(tactic| simp_all +arith only [WellFoundedRelation.rel, InvImage, sizeOf, $sizeDef:ident]))
            unless goals.isEmpty do throwError "not a smaller recursive argument"
            proof := mkApp proof (← instantiateMVars bound)
            ty ← inferType proof
            changed := true
          catch _ =>
            saved.restore
            continue
        while ty.isForall do
          if ← isProp ty.bindingDomain! then break
          let some i := names.idxOf? ty.bindingName! | break
          let some arg := args[i]? | break
          proof := mkApp proof arg
          ty := ty.bindingBody!.instantiate1 arg
          changed := true
        if changed && (ty.find? (· == app)).isSome && (← isProp ty) then
          let next ← g.assert (← mkFreshUserName `induction_fact) ty proof
          let (_, next) ← next.intro1
          g := next
      if let some k := st.contracts.get? d.path then
        for post in k.posts do
          let thm := post.decl ++ `holds
          if (← getEnv).contains thm then
            let proof := mkAppN (mkConst thm) (args.extract d.uses.size)
            let ty ← deltaExpand (← inferType proof) fun n =>
              (k.pres ++ k.posts).any (·.decl == n)
            let ty ← zetaReduce (← Lean.Core.betaReduce ty)
            let next ← g.assert (← mkFreshUserName `contract_fact) ty proof
            let (_, next) ← next.intro1
            g := next
    g.withContext do
      let hs ← (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail then return acc
        if d.type.isForall then
          if !(← isProp d.type.bindingDomain!) then return acc
        return acc.push d.toExpr
      let opts ← getOptions
      let timeout := fren.timeout.get opts
      match ← Smt.smt { trust := true, timeout := some (if timeout == 0 then 30 else min 30 timeout)
                        extraSolverOptions := Core.solverOptions true true ++ resourceLimitOptions opts }
          g hs with
      | .unsat .. => replaceMainGoal []
      | .sat .. => throwError "recursive induction case is not implied by its one-step equations and induction hypotheses"
      | .unknown reason => throwError "recursive induction case is inconclusive: {reason}"

end Fren
