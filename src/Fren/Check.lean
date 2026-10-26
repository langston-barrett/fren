-- keep-sorted start
import Fren.Lint
import Fren.Model
import Fren.SmtTranslate
import FrenCore.Check
import FrenCore.Ty
import Smt
-- keep-sorted end

/-!
# Checks (the controller)

Runs the shared check algorithms (`FrenCore.Check`) on a comp from the model,
with lean-smt (cvc5) as the backend. Formulas are Lean propositions over free
variables standing for the comp's variables. Nothing here logs messages or
changes the model; `Fren.View` presents the results. Results are trusted from
the solver (`trust := true`).
-/

open Lean Meta

namespace Fren

export Core (CheckKind Verdict CheckResult)

register_option fren.timeout : Nat := {
  defValue := 10
  descr := "time limit in seconds for each SMT query made by Fren"
}

register_option fren.resourceLimit : Nat := {
  defValue := 0
  descr := "limit on cvc5's work for each SMT query made by Fren, in its resource units; 0 means none"
}

/-- The cvc5 option that sets `fren.resourceLimit`, unless it is 0, as
`fren check --resource-limit` sets it (`Reqs/Cli#limits`). -/
def resourceLimitOptions (opts : Options) : List (String × String) :=
  match fren.resourceLimit.get opts with
  | 0 => []
  | n => [("rlimit-per", toString n)]

/-- Values for `Bool` variables come back as `True`/`False`. -/
def fromModel (ty : Expr) (val : Expr) : Expr :=
  if ty.isConstOf ``Bool then
    if val.isConstOf ``True then mkConst ``Bool.true
    else if val.isConstOf ``False then mkConst ``Bool.false
    else val
  else val

/-- A value of type `ty` as Fren builds it (`Reqs/View`), such as
`Mode::Heat`, `Shape::Circle(2)`, `Point { x := 1, y := 2 }` or `Ms(5)`. -/
partial def render (ty : Expr) (val : Expr) : MetaM String := do
  -- A value of an abstract type, a local standing for it (`checkComp`).
  if let .fvar id := ty then
    return s!"{(← id.getUserName).getString!}#{← ppExpr val}"
  let val := fromModel ty val
  if let .lit (.strVal s) := val then return s.quote
  -- A pair, a member of a relation.
  if ty.isAppOfArity ``Prod 2 && val.isAppOfArity ``Prod.mk 4 then
    return s!"({← render ty.appFn!.appArg! val.appFn!.appArg!}, {← render ty.appArg! val.appArg!})"
  -- A sequence, as a literal.
  if ty.isAppOfArity ``Fren.Seq 1 then
    let rec elems (e : Expr) : Array Expr := match_expr e with
      | HAppend.hAppend _ _ _ _ a b => elems a ++ elems b
      | Fren.Seq.unit _ x => #[x]
      | _ => #[]
    let shown ← (elems val).mapM (render ty.appArg!)
    return "[" ++ ", ".intercalate shown.toList ++ "]"
  -- A set, as a literal, with its members sorted.
  if ty.isAppOfArity ``Fren.FinSet 1 then
    let rec members (e : Expr) : Array Expr := match_expr e with
      | Union.union _ _ a b => members a ++ members b
      | Singleton.singleton _ _ _ x => #[x]
      | Insert.insert _ _ _ x s => #[x] ++ members s
      | _ => #[]
    let shown ← (members val).mapM (render ty.appArg!)
    return "{" ++ ", ".intercalate (shown.toList.eraseDups.mergeSort (· < ·)) ++ "}"
  let st ← getState
  -- A newtype, as Fren builds it: `Ms(5)`.
  if let some n := st.newtypeOf? ty then
    if val.isAppOfArity n.ctor 1 then return s!"{n.path.getString!}({← render n.under val.appArg!})"
  if let .const c _ := val.getAppFn then
    let args := val.getAppArgs
    if let some e := st.enumOfDecl? c.getPrefix then
      let v := s!"{e.path.getString!}::{c.getString!}"
      let some idx := e.variants.idxOf? (Name.mkSimple c.getString!) | return v
      let tys := e.payloads[idx]?.getD #[]
      if args.isEmpty || args.size != tys.size then return v
      let vals ← (tys.zip args).mapM fun (t, a) => render t a
      return s!"{v}({", ".intercalate vals.toList})"
    if let some r := st.recordOfDecl? c.getPrefix then
      if c == recordCtor r.decl && args.size == r.fields.size then
        let fs ← (r.fields.zip args).mapM fun ((f, t), a) => return s!"{f} := {← render t a}"
        return s!"{r.path.getString!} \{ {", ".intercalate fs.toList} }"
  return toString (← ppExpr val)

/-- `e` with the definitions of defined functions unfolded, so that the
solver sees their bodies, and without `let`s and `have`s, which a record
update binds its updated value with, and `let` and `where` become
(`Reqs/Lang/Let#meaning`), and lean-smt does not translate: last, since a
defined function's body may have one. -/
def unfoldDefined (e : Expr) : MetaM Expr := do
  let s ← getState
  if s.defined.isEmpty && s.contracts.isEmpty then return ← Meta.zetaReduce e
  let ds := s.defined.foldl (init := ({} : NameSet)) fun acc _ d => acc.insert d.decl
  -- And the clauses of contracts, which the questions about applications
  -- and the facts about them apply.
  let ds := s.contracts.foldl (init := ds) fun acc _ k => (k.pres ++ k.posts).foldl (·.insert ·.decl) acc
  Meta.zetaReduce (← Lean.Core.betaReduce (← Meta.deltaExpand e ds.contains))

/-- The answers to a component's queries so far, by hypotheses, goal and
whether a model was wanted: some checks of a component ask the same
query, which is answered once, as in the binary (`Reqs/Cli#solver-queries`). -/
abbrev QueryCache := IO.Ref (Std.HashMap (Array Expr × Expr × Bool) (Core.Outcome Expr))

/-- That `x`, a `Nat` or an `Int`, is at least 0. -/
def atLeast0 (x : Expr) : MetaM Expr := do
  if (← inferType x).isConstOf ``Nat then mkAppM ``LE.le #[mkNatLit 0, x]
  else mkAppM ``LE.le #[← mkNumeral (mkConst ``Int) 0, x]

/-- `n` as the solver knows it (`Core.smtName`): lean-smt names a local or a
bound variable after its user name, and cvc5 rejects one named after a
theory's symbol, such as `abs`. -/
def smtUserName (n : Name) : Name :=
  let s := n.toString (escape := false)
  if Core.theorySymbols.contains s then .mkSimple (Core.smtName s) else n

/-- `e` with its binders named as the solver knows them (`smtUserName`). -/
def smtBinders (e : Expr) : MetaM Expr :=
  Lean.Core.transform e (post := fun
    | .lam n t b bi => return .done (.lam (smtUserName n) t b bi)
    | .forallE n t b bi => return .done (.forallE (smtUserName n) t b bi)
    | .letE n t v b nd => return .done (.letE (smtUserName n) t v b nd)
    | e => return .done e)

/-- The lean-smt backend, for a comp whose variables are the free variables
`fvs`, and whose variables other than its `in`s have second copies `primes`
(`Core.primed`), answering from `cache` the queries asked before. `facts` are
what its `Nat` variables bring, of both copies, which every query assumes,
and `outFacts` those of its outputs, which realizability's `∃` asserts too;
`appsOf` finds the applications of uninterpreted functions into `Nat` or
with postconditions in a formula, whose facts, by `factsOf`, each query
assumes of its own (`Reqs/Check`). With `modelOptional`, a model that lean-smt cannot read, as
it cannot some values of abstract types, is left out rather than making the
answer unknown: a cover goal passes on `sat`, with or without one. Such an
answer is not cached. -/
def leanBackend (c : CompInfo) (fvs primes : Array Expr) (cache : QueryCache) (facts : Array Expr := #[])
    (outFacts : Array Expr := #[]) (appsOf : Expr → Array Expr := fun _ => #[])
    (factsOf : Expr → MetaM (Array (Name × Expr)) := fun _ => pure #[]) (modelOptional : Bool := false) :
    Core.Backend MetaM Expr Expr :=
  let copied := c.vars.zip fvs |>.filter fun (v, _) => (Core.Symbol.ofRole v.role).copied
  let vars := c.vars.zip fvs ++ (copied.zip primes).map fun ((v, _), p) =>
    ({ v with name := Core.primed v.name }, p)
  let varOf? (n : Name) := vars.find? (·.1.name == n)
  -- The answer, and whether to cache it: not if it leaves out a model that
  -- lean-smt could not read.
  let ask (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) : MetaM (Core.Outcome Expr × Bool) :=
    withoutModifyingState do
    -- With the `have`s of `let`s and `where` clauses substituted, so that an
    -- application to a name mentions no bound variable.
    let appFacts ← Core.appFacts appsOf factsOf (← hyps.mapM fun (n, t) => return (n, ← zetaReduce t))
      (← zetaReduce goal)
    let hyps ← (facts.map (`nat, ·) ++ appFacts ++ hyps).mapM fun (n, t) => return (n, ← unfoldDefined t)
    let goal ← smtBinders (← unfoldDefined goal)
    let hyps ← hyps.mapM fun (n, t) => return (n, ← smtBinders t)
    withLocalDeclsD (hyps.map fun (n, t) => (n, fun _ => pure t)) fun hs => do
    -- The locals named as the solver knows them, as their binders are.
    let lctx := (← getLCtx).foldl (init := ← getLCtx) fun l d => l.setUserName d.fvarId (smtUserName d.userName)
    withLCtx lctx (← getLocalInstances) do
      let timeout := fren.timeout.get (← getOptions)
      -- A relation's `domain` or `range` over an infinite type is a
      -- projection, which needs higher-order logic (`cli::logic`); lean-smt
      -- sets `ALL`, which the option overrides.
      let projects (e : Expr) := (e.find? fun x => x.isConstOf ``Fren.FinSet.domain || x.isConstOf ``Fren.FinSet.range).isSome
      let logic := if projects goal || hyps.any (projects ·.2) then [("force-logic", "HO_ALL")] else []
      -- Each attempt on a goal of its own.
      let solve (model : Bool) : MetaM (Core.Outcome Expr) := do
        let mv ← mkFreshExprMVar goal
        -- The options of a spec that uses strings and sets, as in the binary (`cli::logic`).
        match ← Smt.smt { trust := true, model, timeout := some timeout
                          extraSolverOptions := Core.solverOptions true true ++ logic ++ resourceLimitOptions (← getOptions) }
                  mv.mvarId! hs with
        | .sat (some m) =>
          return .sat <| m.values.filterMap fun (k, v) =>
            (vars.find? (·.2 == k)).map fun (var, _) => (var.name, v)
        | .sat none => return .sat #[]
        | .unsat .. => return .unsat
        | .unknown r => return .unknown r
      -- Only the solver's own failures are an unknown answer.
      try return (← solve wantModel, true)
      catch ex =>
        let failed : Core.Outcome Expr := .unknown (← ex.toMessageData.toString)
        unless wantModel && modelOptional do return (failed, true)
        try return (← solve false, false) catch _ => return (failed, true)
  { query := fun hyps goal wantModel => do
      -- The same formulas, in the same local context and with the same
      -- options, are the same query.
      let key := (hyps.map (·.2), goal, wantModel)
      if let some o := (← cache.get)[key]? then return o
      let (o, cacheable) ← ask hyps goal wantModel
      if cacheable then cache.modify (·.insert key o)
      return o
    falseF := mkConst ``False
    notF := mkNot
    conj := fun ps => mkAndN ps.toList
    existsOutputs := fun body =>
      -- The comp's own outputs, not their second copies.
      -- Defined outputs are substituted, never searched for.
      -- The outputs' `Nat`s are at least 0, with the requirements.
      ((c.vars.zip fvs).filter fun (v, _) => v.role == .output && v.defn?.isNone).foldrM (init := mkAndN (outFacts.toList ++ [body]))
        fun (_, x) b => do mkAppM ``Exists #[← mkLambdaFVars #[x] b]
    pin := fun n val => do
      let some (v, fv) := varOf? n | return none
      let val := fromModel v.type val
      if ← isDefEq (← inferType val) v.type then return some (← mkEq fv val)
      -- A `Nat`, which the solver gives as an `Int`.
      if v.type.isConstOf ``Nat then
        if let some i := val.int? then
          if 0 ≤ i then return some (← mkEq fv (mkNatLit i.toNat))
      return none
    render := fun n val => do
      let some (v, _) := varOf? n | return toString (← ppExpr val)
      render v.type val
    prime := fun f => f.replaceFVars (copied.map (·.2)) primes
    samePrimed := fun n =>
      match varOf? n, varOf? (Core.primed n) with
      | some (v, x), some (_, x') => mkApp3 (mkConst ``Eq [1]) v.type x x'
      | _, _ => mkConst ``True
    -- The definitions mention no defined output (`CompInfo.defs`).
    subst := fun ds f =>
      let ds := ds.filterMap fun (n, e) => (varOf? n).map (·.2, e)
      f.replaceFVars (ds.map (·.1)) (ds.map (·.2)) }

/-- The result type of the function type `t`, after its parameters. -/
def resultType : Expr → Expr
  | .forallE _ _ b _ => resultType b
  | t => t

/-- `t`, a function type, with its result type `Nat` made `Int`. -/
def intResult : Expr → Expr
  | .forallE n d b bi => .forallE n d (intResult b) bi
  | _ => mkConst ``Int

/-- Like `withUses`, but a function whose result is a `Nat` becomes a local
`f` whose result is an `Int`, and its placeholder stands for
`fun xs => Fren.natResult (f xs)`: lean-smt would assert of a function
into `Nat` a quantified axiom, which each application's hypothesis replaces
(`natApps`). Gives what each placeholder stands for, and the local of each
function, with its number of parameters and whether its result is a
`Nat`. -/
def withNatUses {α : Type} (uses : Array Name) (k : Array Expr → Array (Name × Expr × Nat × Bool) → MetaM α) :
    MetaM α :=
  go 0 #[] #[]
where
  go (i : Nat) (reps : Array Expr) (fns : Array (Name × Expr × Nat × Bool)) : MetaM α := do
    if h : i < uses.size then
      let ty := replaceUses uses reps (← getConstInfo uses[i]).type
      let bi := if isInhabitedName uses[i] then .instImplicit else .default
      let nat := ty.isForall && (resultType ty).isConstOf ``Nat
      Meta.withLocalDecl (Name.mkSimple uses[i].getString!) bi (if nat then intResult ty else ty) fun x => do
        let fns := if ty.isForall then fns.push (uses[i], x, ty.getForallArity, nat) else fns
        if !nat then return ← go (i + 1) (reps.push x) fns
        let r ← Meta.forallTelescope ty fun xs _ => do mkLambdaFVars xs (mkApp (mkConst ``Fren.natResult) (mkAppN x xs))
        go (i + 1) (reps.push r) fns
    else k reps fns

/-- The placeholders that the checks of `c` use: those of its formulas and
of its questions' goals, which apply the clauses of contracts to the
placeholders they use, and those that the postconditions of the
uninterpreted functions among them use, which their applications' facts
state (`Core.appFacts`), in declaration order. -/
def checkUses (c : CompInfo) : MetaM (Array Name) := do
  let s ← getState
  let mut uses ← usesOf (c.uses.map (mkConst ·) ++ c.indexes.map (·.2.2.2.2))
  repeat
    let more := uses.foldl (init := uses) fun acc u =>
      let posts := s.abstracts.foldl (init := #[]) fun ps _ a =>
        if a.placeholder == u then ((s.contracts.get? a.path).map (·.posts)).getD #[] else ps
      posts.foldl (fun acc k => k.uses.foldl (fun acc v => if acc.contains v then acc else acc.push v) acc) acc
    if more.size == uses.size then break
    uses ← usesOf (more.map (mkConst ·))
  return uses

/-- The applications of the functions `fs`, each with its number of
parameters, to all of them, in `e`, that mention no bound variable, each
once, added to `acc`. None of a check's formulas applies a function under a
binder: a `match` is a chain of `if`s over selectors, a global
expectation's binders are locals, defined functions, whose bodies apply no
uninterpreted function, and the clauses of contracts, which the `fren`
command's queries apply as functions too, are unfolded only after the
facts are found, and under realizability's `∃`, an application's
arguments mention no output (`lang::argument`). An application is met before its arguments, and they
from left to right, as `natAppFacts` orders them. -/
partial def natApps (fs : Array (Expr × Nat)) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e with
  | .app .. =>
    let full := fs.contains (e.getAppFn, e.getAppNumArgs)
    let acc := if full && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
    e.getAppArgs.foldl (fun acc a => natApps fs a acc) acc
  | .lam _ d b _ | .forallE _ d b _ => natApps fs b (natApps fs d acc)
  | .letE _ t v b _ => natApps fs b (natApps fs v (natApps fs t acc))
  | .mdata _ b | .proj _ _ b => natApps fs b acc
  | _ => acc

/-- `∃ xs, body`, over the free variables `xs`, in order. -/
def mkExistsFVars (xs : List Expr) (body : Expr) : MetaM Expr := do
  match xs with
  | [] => return body
  | x :: rest => mkAppM ``Exists #[← mkLambdaFVars #[x] (← mkExistsFVars rest body)]

/-- A proof of `∃ xs, body` from values `vs` of `xs`, if `decide` proves
`body` of them. -/
partial def proveExists (xs vs : List Expr) (body : Expr) : MetaM (Option Expr) := do
  match xs, vs with
  | [], [] =>
    let inst ← synthInstance (mkApp (mkConst ``Decidable) body)
    let r ← withAtLeastTransparency .default <| whnf (mkApp2 (mkConst ``Decidable.decide) body inst)
    unless r.isConstOf ``Bool.true do return none
    return some (mkApp3 (mkConst ``of_decide_eq_true) body inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) r))
  | x :: xs, v :: vs =>
    let p ← mkLambdaFVars #[x] (← mkExistsFVars xs body)
    let some pf ← proveExists xs vs (body.replaceFVar x v) | return none
    return some (← mkAppOptM ``Exists.intro #[none, some p, some v, some pf])
  | _, _ => return none

/-- `p.cover.n.met`, that some behaviour of `c` meets the cover goal `g`,
proved by `decide` from the witness `model` of its query
(`Reqs/Generated#cover-goals`): only for a comp that uses no abstract types
or functions, and when every value is a closed term of its variable's
type. A variable that the model leaves out is `default`. The caller adds
it (`addCoverWitness`), so that comps can be checked in parallel. -/
def coverWitness (c : CompInfo) (fvs : Array Expr) (g : PropInfo) (model : Array (Name × Expr)) :
    MetaM (Option Declaration) := do
  let name := g.decl ++ `met
  if !c.uses.isEmpty || (← getEnv).contains name then return none
  -- Any failure, including a runtime one such as running out of
  -- heartbeats in `decide`, only means that there is no theorem.
  tryCatchRuntimeEx (do
    let vals ← (c.vars.zip fvs).mapM fun (v, _) => do
      match model.find? (·.1 == v.name) with
      | some (_, val) => return fromModel v.type val
      | none => mkAppOptM ``Inhabited.default #[some v.type, none]
    for (v, val) in c.vars.zip vals do
      if val.hasFVar || val.hasMVar || !(← isDefEq (← inferType val) v.type) then return none
    let body := mkAnd (c.meaningDecl fvs) (mkAppN (mkConst g.decl) fvs)
    let type ← mkExistsFVars fvs.toList body
    let some value ← proveExists fvs.toList vals.toList body | return none
    let value ← instantiateMVars value
    return some (.thmDecl { name, levelParams := [], type, value }))
    fun _ => pure none

/-- Adds the theorem `coverWitness` gave; failing, as there, only means that
there is no theorem. -/
def addCoverWitness (d : Declaration) : CoreM Unit :=
  tryCatchRuntimeEx (addDecl d) fun _ => pure ()

/-- All selected checks for one comp, in reporting order, with the theorems
that its cover goals are met (`coverWitness`), for the caller to add. -/
def checkComp (c : CompInfo) (kinds : Array CheckKind := Core.CheckKind.all) :
    MetaM (Array CheckResult × Array Declaration) := do
  let c := { c with uses := ← checkUses c }
  -- The contract of an uninterpreted function, whose value is an output.
  let contract := c.fn?.isSome && c.vars.any (·.role == .output)
  -- The abstract types and functions become locals, which lean-smt
  -- declares as sorts and uninterpreted functions (`check::Interpretations`).
  withNatUses c.uses fun ufs fns => do
  let rep (e : Expr) : MetaM Expr := Lean.Core.betaReduce (replaceUses c.uses ufs e)
  let c := { c with vars := ← c.vars.mapM fun v => return { v with type := ← rep v.type } }
  withLocalDeclsD (c.vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
  let copied := c.vars.filter fun v => (Core.Symbol.ofRole v.role).copied
  withLocalDeclsD (copied.map fun v => (Core.primed v.name, fun _ => pure v.type)) fun primes => do
    let beta (e : Expr) : MetaM Expr := return (← rep e).beta fvs
    -- The indexes, and the questions about tables.
    let indexes := c.indexes.filter (·.2.2.2.1.isNone)
    let tables := c.indexes.filter (·.2.2.2.1.isSome)
    let named (ps : Array PropInfo) := ps.mapM fun p => return (p.name, ← beta p.body)
    let comp : Core.Comp Expr := {
      path := c.path
      vars := c.vars.map fun v =>
        { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
      assumes := ← named c.assumes
      -- A defined function's postconditions are claims of its own
      -- (`check::postcondition`), and the hypotheses of nothing; an
      -- uninterpreted function's, of its value, its contract's guarantees
      -- (`Reqs/Check#contracts-of-uninterpreted-functions`).
      reqs := ← if c.fn?.isNone || contract then named c.ensures else pure #[]
      posts := ← if c.fn?.isSome && !contract then named c.ensures else pure #[]
      fn? := c.fn?
      expects := ← named c.expects
      covers := ← named c.covers
      insts := ← c.insts.mapM fun i => return {
        name := i.name, comp := i.comp, bindings := ← beta i.bindings, behaviour := ← beta i.behaviour
        assumes := ← i.assumes.mapM fun (n, a) => return (n, ← beta a) }
      triggers := ← (c.ensures ++ c.expects).filterMapM fun p => p.trigger?.mapM fun t => return (p.name, ← beta t)
      -- Numbered in order within each item.
      indexes := ← indexes.mapIdxM fun j (n, place, _, _, goal) => do
        let k := (indexes.extract 0 j).filter (·.1 == n) |>.size
        return { prop := n, k, place, goal := ← beta goal }
      tables := ← tables.mapIdxM fun j (n, place, _, q, goal) => do
        let k := (tables.extract 0 j).filter (·.1 == n) |>.size
        return { site := { prop := n, k, place, goal := ← beta goal }, goal := q.getD (.completeness .table) }
      defs := ← c.defs.filterMapM fun (d, e) => do
        let some i := c.vars.findIdx? (·.name == d) | return none
        let e ← beta e
        return some (d, ← mkEq fvs[i]! e, e) }
    -- An uninterpreted function's contract, as both front ends build it
    -- (`Core.contractComp`).
    let comp : Core.Comp Expr := match contract, c.fn?, c.vars.back? with
      | true, some f, some v =>
        Core.contractComp c.path f (c.vars.pop.map fun (x : Var) => x.name) v.name comp.assumes comp.reqs comp.tables
      | _, _, _ => comp
    -- What the `Nat` variables bring (`lang::nat_variable`): each, of both
    -- copies, is at least 0. Each query's applications bring their own
    -- (`Core.appFacts`).
    let natVars (outputs : Bool) := (c.vars.zip fvs).filter fun (v, _) =>
      v.type.isConstOf ``Nat && match Core.natBrought (v.role == .output) v.defn?.isSome with
        | .nothing => false
        | .guarantee => outputs
        | .assumption => !outputs
    let outFacts ← (natVars true).mapM (atLeast0 ·.2)
    let facts ← (natVars false).mapM (atLeast0 ·.2)
    let copiedFvs := (c.vars.zip fvs).filter (fun (v, _) => (Core.Symbol.ofRole v.role).copied) |>.map (·.2)
    let all := facts ++ outFacts
    let facts := all ++ (all.map (·.replaceFVars copiedFvs primes)).filter (!all.contains ·)
    -- What stands for the abstract types and functions, by which a formula
    -- uses them (`Core.coverInterpreted`).
    let useIds := ufs.foldl (fun acc u => (collectFVars acc u)) {} |>.fvarIds
    let interprets (e : Expr) : Bool := e.hasAnyFVar useIds.contains
    let full := { comp with typesInterpreted := c.vars.any fun v => interprets v.type }
    -- Only the `fren` command runs the checks set to testing (`check::by_testing`).
    let (comp, kinds) := comp.untested c.tested kinds
    let cache : QueryCache ← IO.mkRef {}
    -- The models of the cover goals' queries, by goal, for their theorems.
    let models ← IO.mkRef (#[] : Array (Expr × Array (Name × Expr)))
    -- The functions whose applications bring facts: those into `Nat`, and
    -- the uninterpreted ones with postconditions (`Core.appFacts`).
    let st ← getState
    let postsOf (u : Name) : Array ClauseInfo :=
      st.abstracts.foldl (init := #[]) fun ps _ a =>
        if a.placeholder == u then ((st.contracts.get? a.path).map (·.posts)).getD #[] else ps
    let presOf (u : Name) : Array ClauseInfo :=
      st.abstracts.foldl (init := #[]) fun ps _ a =>
        if a.placeholder == u then ((st.contracts.get? a.path).map (·.pres)).getD #[] else ps
    let factFns := fns.filter fun (u, _, _, nat) => nat || !(postsOf u).isEmpty
    let factsOf (app : Expr) : MetaM (Array (Name × Expr)) := do
      let some (u, _, _, nat) := factFns.find? (·.2.1 == app.getAppFn) | return #[]
      let args := app.getAppArgs
      let pres ← (presOf u).mapM fun k => rep (k.at args)
      let implies (ps : Array Expr) (q : Expr) : Expr := ps.foldr (fun p acc => mkForall `h .default p acc) q
      let posts := Core.postconditionFacts implies pres (← (postsOf u).mapM fun k => return (k.name, ← rep (k.at args)))
      let natFact ← if nat then pure #[(`nat, ← atLeast0 app)] else pure #[]
      return natFact ++ posts
    let bk (k : CheckKind) :=
      let b := leanBackend c fvs primes cache facts outFacts (natApps (factFns.map fun (_, x, n, _) => (x, n)) ·) factsOf
        (modelOptional := k == .cover)
      if k != .cover then b else
      { b with query := fun hyps goal wantModel => do
          let o ← b.query hyps goal wantModel
          if let .sat model := o then models.modify (·.push (goal, model))
          return o }
    let results := Core.withInterpreted full interprets (← Core.checkComp bk comp kinds)
    let mut witnesses := #[]
    for g in c.covers do
      let passed := results.any fun r => r.kind == .cover && r.prop? == some g.name && r.verdict == .pass
      let goal := mkNot (← beta g.body)
      if let some (_, model) := (← models.get).find? (·.1 == goal) then
        if passed then
          if let some d ← coverWitness c fvs g model then witnesses := witnesses.push d
    return (results, witnesses)

end Fren
