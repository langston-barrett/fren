-- keep-sorted start
import Fren.Check
import Lean.Elab.Tactic
-- keep-sorted end

/-! Structural induction proofs for recursive contracts. Solver steps use the
same trust setting as other hosted checks. Every generated case must close. -/

open Lean Meta Elab Tactic

namespace Fren

/-- Collect ground applications in the original case, before adding equations. -/
partial def recursiveProofApps (heads : Array Name) (e : Expr) : Array Expr :=
  if e.hasLooseBVars then #[] else
    (if heads.contains (e.getAppFn.constName?.getD .anonymous) && e.isApp then #[e] else #[])
      ++ match e with
      | .app .. => e.getAppArgs.flatMap (recursiveProofApps heads)
      | .forallE _ p q _ => recursiveProofApps heads p ++ recursiveProofApps heads q
      | .mdata _ b => recursiveProofApps heads b
      | _ => #[]

/-- Give the solver one-step equations proved by Lean's equation lemmas,
alongside the case equalities and structural induction hypotheses. -/
elab "fren_recursive_case" self:ident : tactic => do
  let initial ← getMainGoal
  initial.withContext do
    let mut g := initial
    let st ← getState
    let heads := st.defined.foldl (init := #[]) fun acc _ d => if d.recursive then acc.push d.decl else acc
    let mut fs := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && (← isProp d.type) then fs := fs.push d.type
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
            let next ← g.assert (← mkFreshUserName `contract_fact) (← inferType proof) proof
            let (_, next) ← next.intro1
            g := next
    for app in apps do
      let some head := app.getAppFn.constName? | continue
      if head == self.getId then continue
      let r ← unfold app head
      unless r.expr == app do
        let proof ← r.getProof
        let next ← g.assert (← mkFreshUserName `equation) (← mkEq app r.expr) proof
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
