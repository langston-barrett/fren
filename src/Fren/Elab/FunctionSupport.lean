-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: function support -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `fn_params_excessive_bools` on the function `n`, declared at `nameStx`,
whose parameters have the types `params` (`lint::fn_params_excessive_bools`). -/
def lintFnBools (n : Name) (nameStx : Syntax) (params : Array Expr) : TermElabM Unit := do
  let nBools := (params.filter (·.isConstOf ``Bool)).size
  if Core.fnParamsExcessiveBools nBools then
    recordLint .fnParamsExcessiveBools nameStx (Core.fnParamsExcessiveBoolsMsg n nBools)

open Lang in
/-- The parameters `params` of the function `path`, all named, declared like
a procedure's parameters. -/
def paramVars (modName path : Name) (params : Array Syntax) : TermElabM (Array Var) := do
  let paramIds ← params.mapM fun p => do
    let some q := typePath? p[0] | throwErrorAt p[0] (Core.functionParamsMsg path true).text
    pure (pathSegs q)[0]!
  for x in paramIds do unless x.getId.toString.startsWith "#match" do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := paramIds.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt paramIds[k]! (Core.dupParamMsg declared[k]!).text
  let mut vars : Array Var := #[]
  for p in params, x0 in paramIds do
    let x ← declare x0 modName
    lintName .variable x.getId x
    let (ty, ptype) ← varPType modName x (if p[1].isNone then none else some p[1][1])
    let fact? ← factPred? ty ptype
    vars := vars.push { name := x.getId, role := .input, isPub := true, «type» := ty, ref := x, ptype, fact? }
  return vars

/-- `e` with defined functions unfolded, their applications to closures
reduced, and without `have`s, as the solver sees it (`Fren.unfoldDefined`):
where the applications of a function parameter are. -/
def unfoldForSites (e : Expr) : TermElabM Expr := do
  let s ← getState
  let ds := s.defined.foldl (init := ({} : NameSet)) fun acc _ d =>
    d.oblDecls.foldl (fun a (o, _) => a.insert o) (acc.insert d.decl)
  let ds := s.contracts.foldl (init := ds) fun acc _ k => (k.pres ++ k.posts).foldl (·.insert ·.decl) acc
  Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined s e ds.contains))

/-- The obligations that the predicate `p` holds at each application of
the function parameter `f` within `e`, under the guards and binders
`frames` around `e` and those within it (`Core.siteGoal`,
`lang::closure_obligation`). -/
partial def siteGoals (f p : Expr) (frames : List (Core.SiteFrame Expr (Expr × Name × Expr))) (e : Expr) :
    MetaM (Array Expr) := do
  let bind := fun ((fv, n, ty) : Expr × Name × Expr) (acc : Expr) => Expr.forallE n ty (acc.abstract #[fv]) .default
  let goal (args : Array Expr) : Expr :=
    Core.siteGoal mkNot (fun c a => Expr.forallE `h c a .default) bind frames (mkAppN p args)
  let args := e.getAppArgs
  let under (o : Core.GuardedOperand) (c x : Expr) := siteGoals f p (frames ++ [.guard o c]) x
  if e.getAppFn == f then return #[goal args] ++ (← args.flatMapM (siteGoals f p frames))
  match e with
  | .app .. =>
    if e.isAppOfArity ``ite 5 then
      return (← siteGoals f p frames args[1]!) ++ (← under .thenBranch args[1]! args[3]!) ++ (← under .elseBranch args[1]! args[4]!)
    if e.isAppOfArity ``And 2 then return (← siteGoals f p frames args[0]!) ++ (← under .andRight args[0]! args[1]!)
    if e.isAppOfArity ``Or 2 then return (← siteGoals f p frames args[0]!) ++ (← under .orRight args[0]! args[1]!)
    (#[e.getAppFn] ++ args).flatMapM (siteGoals f p frames)
  | .forallE n ty b bi =>
    if !b.hasLooseBVars then return (← siteGoals f p frames ty) ++ (← under .whenBody ty b)
    withLocalDecl n bi ty fun x => siteGoals f p (frames ++ [.binder (x, n, ty)]) (b.instantiate1 x)
  | .lam n ty b bi => withLocalDecl n bi ty fun x => siteGoals f p (frames ++ [.binder (x, n, ty)]) (b.instantiate1 x)
  | .mdata _ b => siteGoals f p frames b
  | _ => return #[]

/-- The function type `ty`, a defined function's parameter's
(`Reqs/Lang/HigherOrder#function-types`), and its Lean arrow: its
parameters' and result's types are neither `Nat`s, subset types nor
function types (`lang::function_type_parts`). -/
def fnParamType (modName : Name) (ty : Syntax) : TermElabM (Core.FnTy × Expr) := do
  let parts := ty[2].getSepArgs.push ty[5]
  let mut tys := #[]
  let mut lean := #[]
  for part in parts do
    if hasFnType part then
      if let some msg := Core.fnPartMsg? .function then throwErrorAt part msg.text
    let (t, pt) ← elabPType modName part
    let k : Core.FnPart := if t.isConstOf ``Nat then .nat else if pt.pat?.isSome then .pattern else .plain
    if let some msg := Core.fnPartMsg? k then throwErrorAt part msg.text
    tys := tys.push ((← coreTy? t).getD .bool)
    lean := lean.push t
  return ({ params := tys.pop, result := tys.back! }, ← mkArrowN lean.pop lean.back!)

/-- The parameters of the function at `path`, as `paramVars` declares them,
but for its function parameters, which only a defined function has
(`lang::function_type_place`): each with its position, name, type and
Lean type. -/
def paramVarsHo (modName path : Name) (params : Array Syntax) (defined : Bool) :
    TermElabM (Array Var × Array (Nat × Name × Syntax × Core.FnTy × Expr)) := do
  let paramIds ← params.mapM fun p => do
    let some q := typePath? p[0] | throwErrorAt p[0] (Core.functionParamsMsg path true).text
    pure (pathSegs q)[0]!
  for x in paramIds do unless x.getId.toString.startsWith "#match" do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := paramIds.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt paramIds[k]! (Core.dupParamMsg declared[k]!).text
  let mut vars : Array Var := #[]
  let mut fns := #[]
  for p in params, x0 in paramIds, j in [0:params.size] do
    let x ← declare x0 modName
    lintName .variable x.getId x
    if !p[1].isNone && p[1][1].isOfKind ``Lang.fnType then
      unless defined do checkFnTypeSite .uninterpretedParameter p[1][1]
      let (ft, lty) ← fnParamType modName p[1][1]
      fns := fns.push (j, x.getId, x, ft, lty)
      continue
    let (ty, ptype) ← varPType modName x (if p[1].isNone then none else some p[1][1])
    let fact? ← factPred? ty ptype
    vars := vars.push { name := x.getId, role := .input, isPub := true, «type» := ty, ref := x, ptype, fact? }
  return (vars, fns)

/-- The names of one segment that `e` applies as functions, anywhere within
it: a function parameter is mentioned by applying it. -/
partial def appliedNames (e : Syntax) : Array Name :=
  let own := if e.isOfKind ``Lang.appExpr && (pathSegs e[0]).size == 1 then #[(pathSegs e[0])[0]!.getId] else #[]
  own ++ e.getArgs.flatMap appliedNames

/-- What each application of a function whose result has the declared type
`rp`, of the Lean type `result`, brings: what its result's type does, a
`Nat`'s among it, over an `Int`, as the solver sees a function into `Nat`
(`Fren.natResult`). None if the type brings nothing beyond a `Nat`'s. -/
def resultFact? (result : Expr) (rp : Core.PTy) : TermElabM (Option Expr) := do
  if (rp.cons (← getState).shapeOf).isNone then return none
  factPred? (if result.isConstOf ``Nat then mkConst ``Int else result) rp (rp.ty == .nat)

abbrev CompIndexes := Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)


end Fren
