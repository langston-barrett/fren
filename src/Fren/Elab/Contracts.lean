-- keep-sorted start
import Fren.Elab.Predicates
-- keep-sorted end

/-! # Hosted elaboration: contracts -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A clause `e` of the contract of the function at `path`, whose
parameters are `vars` and whose function parameters `fnVars`, and of whose
value `value?` is, for an uninterpreted function: its definition, over
the parameters and then the function parameters, the definition of its
postcondition of the value, the questions about it, and for a
higher-order function, its definition for the function's own checks, in
which each function parameter is its placeholder. -/
structure ContractClauseResult where
  body : Expr
  ofValue? : Option Expr
  sites : Array (Syntax × Option Core.TableGoal × Expr)
  checked? : Option Expr
  branchGroups : Array (Core.BranchGroup Expr)
  memberGroups : Array (Core.MemberGroup Expr)
  deriving Inhabited

def contractClause (modName path : Name) (post : Bool) (vars : Array Var) (fnVars : Array (Name × Core.FnTy × Expr × Name))
    (value? : Option (Name × Var)) (e : Syntax) (params : Array Name) :
    TermElabM ContractClauseResult :=
  withLocalDeclsD (fnVars.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
  withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
    let phs : Array Expr := fnVars.map fun p => Lean.mkConst p.2.2.2
    let cx : ExprCtx := { modName, vars, insts := #[], place := .prop
                          contract? := some { path, post, params }
                          fnParams := fnVars.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)) }
    discard (takeIndexes fvs)
    let t ← toTerm cx e
    checkDeclared e t (mkConst ``Bool) fun _ => "note: a clause of a contract is a `Bool`"
    let body ← elabProp t
    -- The function applied to its parameters, at its own type parameters,
    -- whatever term gives their `Inhabited` instances.
    let isApp (ph : Name) : TermElabM (Expr → Bool) := do
      let nTypes := 2 * ((← placeholderOf path).typeParams.size)
      return fun t => t.isAppOfArity ph (nTypes + fvs.size) && t.getAppArgs.extract nTypes == fvs
    let ofFnParams (x : Expr) : Expr := x.replaceFVars fnFvs phs
    -- A postcondition's questions are about the value, as its
    -- realizability is, not about the function applied to its parameters,
    -- whose contract is this one: assumed of it, the clause that a
    -- question leaves out would decide it (`check::disjointness`).
    let tables ← match post, value? with
      | true, some (ph, v) => withLocalDeclD v.name v.type fun x => do
        let app ← isApp ph
        takeIndexes (fvs.push x) fun e => (ofFnParams e).replace fun t => if app t then some x else none
      | _, _ => takeIndexes fvs ofFnParams
    let tables := tables.filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
    let checked? ← if fnVars.isEmpty then pure none else some <$> mkLambdaFVars fvs (ofFnParams body)
    -- A postcondition of the value, for realizability: the function
    -- applied to its parameters is the value.
    let ofValue? ← match post, value? with
      | true, some (ph, v) => withLocalDeclD v.name v.type fun x => do
        let app ← isApp ph
        some <$> mkLambdaFVars (fvs.push x) (body.replace fun t => if app t then some x else none)
      | _, _ => pure none
    let branchGroups ← clauseBranchGroups cx .anonymous e (fvs ++ fnFvs)
    let memberGroups ← clauseMemberGroups cx .anonymous e (fvs ++ fnFvs)
    return { body := ← mkLambdaFVars (fvs ++ fnFvs) body, ofValue?, sites := tables, checked?, branchGroups, memberGroups }

/-- Elaborates the clauses of the contract of the function `n` at `path`,
whose parameters are `vars` and whose definitions are named under `decl`,
and records the contract (`Reqs/Lang/Items#contracts`). Gives each clause
as a constraint of the function's body's procedure, named after the function
and the clause, a postcondition only if the function is defined; and the
questions about the tables and applications in them: a precondition's
under the other preconditions, a postcondition's under all of them. -/
def elabContract (modName path n decl : Name) (defined : Bool) (vars : Array Var) (clauses : Array Syntax)
    (fnVars : Array (Name × Core.FnTy × Expr × Name) := #[]) (params : Array Name := vars.map (·.name)) :
    TermElabM (Array Var × Array PropInfo × Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)) := do
  let clauses ← clauses.flatMapM fun clause => do
    let source := withWhere clause[3] clause[4]
    if !predicateConjunction source then return #[clause]
    let leaves ← predicateLeafSources clause[1].getId source
    return leaves.map fun (name, ref, body) =>
      mkNode clause.getKind #[clause[0], mkIdentFrom ref name, clause[2], body, mkNullNode]
  -- The clauses' names share one namespace with the parameters
  -- (`lang::distinct_names`).
  let names := vars.map (·.name) ++ clauses.map fun c => (declaredIdent c[1]).1.getId
  if let some k := (Core.repeatsAt names)[0]? then
    if k ≥ vars.size then throwErrorAt clauses[k - vars.size]![1] (Core.dupClauseMsg names[k]!).text
  -- An uninterpreted function's value, an output of its contract's procedure,
  -- for its realizability (`Reqs/Check#contracts-of-uninterpreted-functions`):
  -- named after the function, unless a parameter is.
  let value? : Option (Name × Var) ← if defined then pure none else do
    let a ← placeholderOf path
    let name := Core.contractValueName n (vars.map (·.name))
    -- A generic function's, at its own type parameters, for every type
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
    let own := (typeParamPlaceholders path a.typeParams).map (Lean.mkConst ·)
    let ty ← forallTelescope (← instantiateForall (← getConstInfo a.placeholder).type own) fun _ r => pure r
    -- With its result's type, which it is realized in.
    let fact? ← factPred? ty a.ptys.2
    pure (some (a.placeholder, ({ name, role := .output, isPub := true, «type» := ty, ref := mkIdent name
                                  ptype := a.ptys.2, fact? } : Var)))
  let mut pres : Array ClauseInfo := #[]
  let mut posts : Array ClauseInfo := #[]
  let mut props : Array PropInfo := #[]
  let mut sites : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr) := #[]
  for c in clauses do
    let kw := if c[0].isAtom then c[0] else c[0][0]
    let post := kw.getAtomVal.trimAscii.toString == "ensure"
    let x := c[1]
    liftMsg x (Core.checkNoBang x.getId)
    let cn ← if let .original .. := x.getHeadInfo then segName x else pure x.getId
    if let .original .. := x.getHeadInfo then lintName .constraint cn x
    if cn.toString.endsWith "?" then throwErrorAt x (Core.propNameMsg cn).text
    let e := withWhere c[3] c[4]
    -- A higher-order function's clauses take its function parameters
    -- after the others; for its checks, each is the uninterpreted function
    -- of its placeholder (`Reqs/Lang/HigherOrder#function-parameters`).
    let res ← contractClause modName path post vars fnVars value? e params
    lintBools e (← hidesIn { modName, vars, insts := #[], place := .prop })
    lintContractClause { modName, vars, insts := #[], place := .prop, contract? := some { path, post, params }
                         fnParams := fnVars.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)) } post cn n params e
    -- Expand a named predicate using typed templates twice: once in the
    -- real contract (which applies the function), and once in its checking
    -- procedure (which represents the function's value by an output).
    let (rawLeaves, checkedLeaves, extraSites) ←
      withLocalDeclsD (fnVars.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
      withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
        let all := fvs ++ fnFvs
        let owner := n ++ cn
        let cx : ExprCtx := {
          modName, vars, insts := #[], place := .prop
          contract? := some { path, post, params }
          fnParams := fnVars.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)) }
        let withNames (member : Core.BranchMember Expr) := { member with name := Name.mkSimple (owner.toString (escape := false) ++ "." ++ member.name.toString (escape := false)) }
        let branches := res.branchGroups.map fun g => { g with owner, members := g.members.map withNames }
        let observations := res.memberGroups.map fun g => { g with owner, members := g.members.map withNames }
        let raw : PropInfo := {
          kind := if post then .ensure else .assume, name := owner, ref := x
          body := res.body, trigger? := none, triggerRef? := none, decl := decl ++ cn, branchGroups := branches, memberGroups := observations }
        let (rawLeaves, _, _) ← expandPredicateConstraint cx raw e all
        let phs : Array Expr := fnVars.map fun p => Lean.mkConst p.2.2.2
        let makeChecked (checkFvs : Array Expr) (value : Option Expr) := do
          let convert (template : Expr) : TermElabM Expr := do
            let body := (template.beta all).replaceFVars fnFvs phs
            let body ← match value, value? with
              | some output, some (placeholder, _) => do
                let nTypes := 2 * ((← placeholderOf path).typeParams.size)
                pure <| body.replace fun term =>
                  if term.isAppOfArity placeholder (nTypes + fvs.size) && term.getAppArgs.extract nTypes == fvs then some output else none
              | _, _ => pure body
            mkLambdaFVars checkFvs body
          let checkedBranches ← branches.mapM fun group => do
            let members ← group.members.mapM fun member => do
              return { member with
                formula := ← convert member.formula
                valueFormula? := ← member.valueFormula?.mapM convert
                evaluationGuard? := ← member.evaluationGuard?.mapM convert }
            return { group with members, guard? := ← group.guard?.mapM convert }
          let checkedObservations ← observations.mapM fun group => do
            let members ← group.members.mapM fun member => do
              return { member with
                formula := ← convert member.formula
                valueFormula? := ← member.valueFormula?.mapM convert
                evaluationGuard? := ← member.evaluationGuard?.mapM convert }
            return { group with members }
          let checked : PropInfo := { raw with
            body := ← convert res.body
            branchGroups := checkedBranches, memberGroups := checkedObservations }
          let (leaves, _, sites) ← expandPredicateConstraint cx checked e checkFvs
          return (rawLeaves, leaves, sites)
        if post then
          if let some (_, v) := value? then
            return ← withLocalDeclD v.name v.type fun output => makeChecked (fvs.push output) (some output)
        makeChecked fvs none
    for raw in rawLeaves, checked in checkedLeaves do
      let ownerPrefix := n.toString (escape := false) ++ "."
      let name := if raw.name == n ++ cn then cn else
        Name.mkSimple ((((raw.name.toString (escape := false)).dropPrefix? ownerPrefix).map (·.toString)).getD (raw.name.toString (escape := false)))
      let uses ← usesOf #[raw.body]
      let k : ClauseInfo := { name, decl := decl ++ name, uses }
      addUsesDef uses k.decl raw.body
      if post then posts := posts.push k else pres := pres.push k
      props := props.push { checked with decl := k.decl }
    sites := sites ++ res.sites.map (fun (r, q, g) => (n ++ cn, if post then Core.IndexPlace.body else .assume, r, q, g))
      ++ extraSites.map fun (name, _, ref, question, goal) => (name, if post then .body else .assume, ref, question, goal)
  record (.contractInfo { path, pres, posts, defined })
  -- A defined function's contract has nothing to realize, nor an
  -- uninterpreted function's without postconditions.
  let some (_, v) := value?.filter fun _ => !posts.isEmpty
    | return (vars, props.filter (defined || ·.kind == .assume), sites)
  -- Every other formula over the parameters is over the value too, which
  -- it does not mention.
  let withValue (e : Expr) : TermElabM Expr :=
    lambdaBoundedTelescope e vars.size fun xs b => withLocalDeclD v.name v.type fun x => mkLambdaFVars (xs.push x) b
  let props' ← props.mapM fun p => do
    if p.kind == .ensure then return p
    let branches ← p.branchGroups.mapM fun group => do
      let members ← group.members.mapM fun member => do
        return { member with
          formula := ← withValue member.formula
          valueFormula? := ← member.valueFormula?.mapM withValue
          evaluationGuard? := ← member.evaluationGuard?.mapM withValue }
      return { group with members, guard? := ← group.guard?.mapM withValue }
    let observations ← p.memberGroups.mapM fun group => do
      let members ← group.members.mapM fun member => do
        return { member with
          formula := ← withValue member.formula
          valueFormula? := ← member.valueFormula?.mapM withValue
          evaluationGuard? := ← member.evaluationGuard?.mapM withValue }
      return { group with members }
    return { p with body := ← withValue p.body, branchGroups := branches, memberGroups := observations }
  -- A postcondition's questions are over the value already.
  let sites' ← sites.mapM fun (n, place, r, q, g) =>
    return (n, place, r, q, ← if place == .body then pure g else withValue g)
  return (vars.push v, props', sites')


end Fren
