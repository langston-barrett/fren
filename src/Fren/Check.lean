-- keep-sorted start
import Fren.Lint
import Fren.Model
import Fren.SeqElems
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

register_option fren.examples : Nat := {
  defValue := 1
  descr := "the most notes of guarantees that force an output to different values that Fren shows for each unrealizable component"
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
    -- By the last segment of its sort's name, as the `fren` command has it
    -- (`renderAbstract?`): a generic function's type parameter is named by
    -- its whole path (`withNatUses`), and shown by its name.
    let sort := (← id.getUserName).getString!
    return s!"{(sort.splitOn "::").getLast?.getD sort}#{← ppExpr val}"
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
    -- A generic type's constructor is applied to its type arguments first,
    -- which a value is shown without (`Reqs/Lang/Generics#printing`); its
    -- payload's or fields' types have the type's arguments.
    let targs := ty.getAppArgs
    if let some e := st.enumOfDecl? c.getPrefix then
      let args := val.getAppArgs.extract e.params.size
      let some idx := e.ctorIdx? c | return s!"{e.path.getString!}::{c.getString!}"
      let v := s!"{e.path.getString!}::{e.variants[idx]!}"
      let tys := (e.payloadsAt targs)[idx]?.getD #[]
      if args.isEmpty || args.size != tys.size then return v
      let vals ← (tys.zip args).mapM fun (t, a) => render t a
      return s!"{v}({", ".intercalate vals.toList})"
    if let some r := st.recordOfDecl? c.getPrefix then
      let args := val.getAppArgs.extract r.params.size
      if c == r.ctor && args.size == r.fields.size then
        let fs ← ((r.fieldsAt targs).zip args).mapM fun ((f, t), a) => return s!"{f} := {← render t a}"
        return s!"{r.path.getString!} \{ {", ".intercalate fs.toList} }"
  return toString (← ppExpr val)

/-- `e` with the definitions of defined functions unfolded, so that the
solver sees their bodies, and without `let`s and `have`s, which a record
update binds its updated value with, and `let` and `where` become
(`Reqs/Lang/Let#meaning`), and lean-smt does not translate: last, since a
defined function's body may have one. -/
def unfoldDefined (e : Expr) : MetaM Expr := do
  let s ← getState
  -- A pattern type's obligation is its proposition (`Fren.typeObligation`).
  let ds := s.defined.foldl (init := ({} : NameSet).insert ``Fren.typeObligation) fun acc _ d => acc.insert d.decl
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

/-- The result type of the function type `t`, after its parameters. -/
def resultType : Expr → Expr
  | .forallE _ _ b _ => resultType b
  | t => t

/-- `t`, a function type, with its result type `Nat` made `Int`. -/
def intResult : Expr → Expr
  | .forallE n d b bi => .forallE n d (intResult b) bi
  | _ => mkConst ``Int

/-- The applications in `e` of the generic functions without a body
`generics`, each by its placeholder, with the number of type arguments and
`Inhabited` instances that it takes first: each instance once, as its
placeholder and those arguments, added to `acc`. Two applications are at
one instance when their type arguments are equal, whatever terms give
their instances. -/
partial def instancesIn (generics : Array (Name × Nat × Bool)) (e : Expr) (acc : Array (Name × Array Expr) := #[]) :
    Array (Name × Array Expr) :=
  match e with
  | .app .. =>
    let args := e.getAppArgs
    let acc := match e.getAppFn with
      | .const u _ => match generics.find? (·.1 == u) with
        | some (_, m, _) =>
          let pre := args.extract 0 m
          let same (x : Name × Array Expr) := x.1 == u && x.2.size == m
            && (List.range (m / 2)).all fun i => x.2[2 * i]! == pre[2 * i]!
          if args.size ≥ m && !pre.any (·.hasLooseBVars) && !acc.any same then acc.push (u, pre) else acc
        | none => acc
      | _ => acc
    args.foldl (fun acc x => instancesIn generics x acc) (instancesIn generics e.getAppFn acc)
  | .lam _ d b _ | .forallE _ d b _ => instancesIn generics b (instancesIn generics d acc)
  | .letE _ t v b _ => instancesIn generics b (instancesIn generics v (instancesIn generics t acc))
  | .mdata _ b | .proj _ _ b => instancesIn generics b acc
  | _ => acc

/-- `e` with each application of an instance `insts` of a generic function
of `generics` an application of that instance's local of `xs`
(`withInstances`). -/
partial def replaceInstances (generics : Array (Name × Nat × Bool)) (insts : Array (Name × Array Expr))
    (xs : Array Expr) (e : Expr) : Expr :=
  e.replace fun t =>
    match t.getAppFn with
    | .const u _ => do
      let (_, m, nat) ← generics.find? (·.1 == u)
      let args := t.getAppArgs
      guard (args.size ≥ m)
      let j ← insts.findIdx? fun (v, pre) => v == u && (List.range (m / 2)).all fun i => pre[2 * i]! == args[2 * i]!
      let app := mkAppN xs[j]! ((args.extract m).map (replaceInstances generics insts xs))
      return if nat then mkApp (mkConst ``Fren.natResult) app else app
    | _ => none

/-- Runs `k` with a local for each instance `insts` of a generic function
of `generics` (`instancesIn`), in order: the solver sees each instance as an
unknown function of its own (`lang::uninterpreted_instance`), declared, as
the `fren` command declares it, before the variables. An instance whose
result is a `Nat` is a local into `Int`, as `withNatUses` makes one. -/
def withInstances {α : Type} (generics : Array (Name × Nat × Bool)) (insts : Array (Name × Array Expr))
    (types : Array (Option Expr)) (k : Array Expr → MetaM α) : MetaM α :=
  go 0 #[]
where
  go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < insts.size then
      let (u, pre) := insts[i]
      let nat := (generics.find? (·.1 == u)).any (·.2.2)
      -- Its signature, `Core.instanceSig`'s, where the elaborator gives it.
      let ty ← match types[i]?.join with
        | some t => pure t
        | none => instantiateForall (← getConstInfo u).type pre
      let name := Name.mkSimple s!"{u.getString!}<{i}>"
      Meta.withLocalDeclD name (if nat then intResult ty else ty) fun x => go (i + 1) (xs.push x)
    else k xs

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
def leanBackend (c : CompInfo) (fvs primes : Array Expr) (cache : QueryCache) (facts : Array (Name × Expr) := #[])
    (outFacts : Array Expr := #[]) (appsOf : Expr → Array Expr := fun _ => #[])
    (factsOf : Expr → MetaM (Array (Name × Expr)) := fun _ => pure #[]) (modelOptional : Bool := false)
    (bounded : Bool := false) (instances : Expr → Expr := id) (finiteModel : Bool := false) :
    Core.Backend MetaM Expr Expr :=
  let copied := c.vars.zip fvs |>.filter fun (v, _) => (Core.Symbol.ofRole v.role).copied
  let vars := c.vars.zip fvs ++ (copied.zip primes).map fun ((v, _), p) =>
    ({ v with name := Core.primed v.name }, p)
  let varOf? (n : Name) := vars.find? (·.1.name == n)
  -- The answer to the query of `hyps` and `goal`, as the solver knows them,
  -- whose model also has the values of the locals `extra`, by their names,
  -- and whether to cache it: not if it leaves out a model that lean-smt
  -- could not read.
  let askSmt (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) (extra : Array Expr := #[]) :
      MetaM (Core.Outcome Expr × Bool) := do
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
      -- lean-smt's defaults for its proofs, which Fren does not ask for,
      -- back to cvc5's, as the binary leaves them: without simplification,
      -- cvc5 cannot decide some queries that it decides with it (#173).
      -- lean-smt reads an unsat core of every `unsat`, so it keeps those.
      let cvc5Defaults := [("simplification", "batch"), ("enum-inst", "false"), ("enum-inst-interleave", "false"),
        ("cegqi-midpoint", "false")]
      -- A component whose queries may quantify over a collection's
      -- elements sets `fmf-bound` (`Core.boundedOptions`).
      let bounded := if bounded then Core.boundedOptions else []
      -- Each attempt on a goal of its own.
      let solve (model : Bool) : MetaM (Core.Outcome Expr) := do
        let mv ← mkFreshExprMVar goal
        -- The options of a spec that uses strings and sets, as in the binary (`cli::logic`).
        -- lean-smt asserts its hints in reverse order, and cvc5's answer
        -- can depend on the order (#173), so they are given reversed, to be
        -- asserted in the binary's order.
        match ← Smt.smt { trust := true, model, timeout := some timeout
                          -- `fmf-bound` right after the options both front ends set, as the
                          -- binary sets it.
                          extraSolverOptions := Core.solverOptions true true ++ bounded
                            ++ (if finiteModel then Core.finiteModelOptions else []) ++ logic ++ cvc5Defaults
                            ++ resourceLimitOptions (← getOptions) }
                  mv.mvarId! hs.reverse with
        | .sat (some m) =>
          return .sat <| m.values.filterMap fun (k, v) =>
            match (vars.find? (·.2 == k)).map (·.1.name) with
            | some n => some (n, v)
            | none => if extra.contains k then some (k.fvarId!.name, v) else none
        | .sat none => return .sat #[]
        | .unsat .. => return .unsat
        | .unknown r => return .unknown r
      -- Only the solver's own failures are an unknown answer.
      try return (← solve wantModel, true)
      catch ex =>
        let failed : Core.Outcome Expr := .unknown (← ex.toMessageData.toString)
        unless wantModel && modelOptional do return (failed, true)
        try return (← solve false, false) catch _ => return (failed, true)
  -- With its quantifiers over elements expanded (`Fren.Elems.withExpanded`):
  -- at the index set, with the lengths of their sequences in the model;
  -- and, if that has a model, again at every position, with the lengths
  -- pinned to the model's, whose model is real
  -- (`Reqs/Lang/ElementQuantifiers#expansion`), as the binary's
  -- `solveExpanded` asks.
  let askElems (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) : MetaM (Core.Outcome Expr × Bool) := do
    let first ← Elems.withExpanded hyps goal none fun ex => do
      let (o, c) ← askSmt ex.hyps ex.goal (wantModel || !ex.lengths.isEmpty) (ex.lengths.map (·.1))
      let .sat m := o | return ((o, c), none)
      let ids := ex.locals.map (·.fvarId!.name)
      let model := m.filter fun (n, _) => !ids.contains n
      if ex.lengths.isEmpty then return ((.sat model, c), none)
      let pins := ex.lengths.filterMap fun (l, q) => do
        let (_, v) ← m.find? (·.1 == l.fvarId!.name)
        let k ← v.int?
        guard (0 ≤ k)
        pure (q, k.toNat)
      -- A length that the model does not give, as the binary answers it.
      unless pins.size == ex.lengths.size do return ((.unknown Core.elementUnconfirmedReason, c), none)
      return ((.sat model, c), some pins)
    match first with
    | .error n => return (.unknown (Core.elementLimitReason n), true)
    | .ok (r, none) => return r
    | .ok (_, some pins) =>
      match ← Elems.withExpanded hyps goal (some pins) fun ex => askSmt ex.hyps ex.goal wantModel with
      | .error n => return (.unknown (Core.elementLimitReason n), true)
      | .ok (.unsat, c) => return (.unknown Core.elementUnconfirmedReason, c)
      | .ok r => return r
  let ask (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) : MetaM (Core.Outcome Expr × Bool) :=
    withoutModifyingState do
    -- With the `have`s of `let`s and `where` clauses substituted, so that an
    -- application to a name mentions no bound variable.
    let appFacts ← Core.appFacts appsOf factsOf (← hyps.mapM fun (n, t) => return (n, ← zetaReduce t))
      (← zetaReduce goal)
    let hyps ← (facts ++ appFacts ++ hyps).mapM fun (n, t) => return (n, ← unfoldDefined t)
    let goal ← smtBinders (← unfoldDefined goal)
    let hyps ← hyps.mapM fun (n, t) => return (n, ← smtBinders t)
    -- Each instance of a generic function without a body, a local of its
    -- own (`withInstances`), before any quantifier over elements is
    -- expanded.
    let goal := instances goal
    let hyps := hyps.map fun (n, t) => (n, instances t)
    if Elems.hasMark goal || hyps.any (Elems.hasMark ·.2) then askElems hyps goal wantModel
    else askSmt hyps goal wantModel
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
    -- `x = C (sel₀ x) …`, as a pattern test is (`patTerm`), of a variable
    -- whose type is an enumeration, as the `fren` command's
    -- `variantOfValue` decides.
    pinVariant := fun n val => do
      let some (v, x) := varOf? n | return none
      let ty := v.type
      let some e := (← getState).enumOf? ty | return none
      let .const c _ := val.getAppFn | return none
      let some idx := e.ctorIdx? c | return none
      -- A generic type's constructor takes its type arguments first, and
      -- its selectors take them, and an `Inhabited` instance of each,
      -- implicitly, which `mkAppM` finds.
      let targs := ty.getAppArgs
      let arity := (e.payloads[idx]?.map (·.size)).getD 0
      let sels ← (Array.range arity).mapM fun k => mkAppM (e.sel idx k) #[x]
      let k : Core.Variant := { name := s!"{e.path.getString!}::{e.variants[idx]!}", arity }
      return some (k, ← mkEq x (mkAppN (e.ctorConst idx) (targs ++ sels)))
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

/-- The generic function without a body whose placeholder is `u`, if `u`
is one's (`AbstractInfo.typeParams`). -/
def genericOf? (u : Name) : MetaM (Option AbstractInfo) := do
  return (← getState).abstracts.foldl (init := none) fun acc _ a =>
    acc <|> if a.placeholder == u && !a.typeParams.isEmpty then some a else none

/-- Whether `u` is the placeholder of a generic function without a body. -/
def isGenericPlaceholder (u : Name) : MetaM Bool := return (← genericOf? u).isSome

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
      -- A generic function without a body stays itself: each of its
      -- instances becomes a local of its own in each query
      -- (`withInstances`).
      if ← isGenericPlaceholder uses[i] then return ← go (i + 1) (reps.push (mkConst uses[i])) fns
      let ty := replaceUses uses reps (← getConstInfo uses[i]).type
      let bi := if isInhabitedName uses[i] then .instImplicit else .default
      let nat := ty.isForall && (resultType ty).isConstOf ``Nat
      -- A generic function's type parameter is a sort named by its whole
      -- path, as the `fren` command names it (`Core.typeParamPath`): a
      -- parametric datatype's own parameter may have its name.
      let name := if (Core.typeParamName? uses[i]).isSome
        then Name.mkSimple ("::" ++ Core.showPath (uses[i].replacePrefix `Fren.Abstract .anonymous))
        else Name.mkSimple uses[i].getString!
      Meta.withLocalDecl name bi (if nat then intResult ty else ty) fun x => do
        let fns := if ty.isForall then fns.push (uses[i], x, ty.getForallArity, nat) else fns
        if !nat then return ← go (i + 1) (reps.push x) fns
        let r ← Meta.forallTelescope ty fun xs _ => do mkLambdaFVars xs (mkApp (mkConst ``Fren.natResult) (mkAppN x xs))
        go (i + 1) (reps.push r) fns
    else k reps fns

/-- The contract `c` of the generic function `f` without a body, at its
instance with the type arguments `targs`: its parameters, value and
clauses at the instance's types, with their types' constraints there, named
after the instance (`Core.instanceName`), as the `fren` command makes it
(`instantiate`), for the check of its realizability there
(`lang::generic_contract`). -/
def instanceContract (hooks : ElabHooks) (c : CompInfo) (f : Name) (targs : Array Core.Ty) : MetaM CompInfo := do
  let some a := (← getState).abstracts.get? f | return c
  let targExprs ← targs.flatMapM fun t => do
    let ty ← hooks.leanType t
    return #[ty, ← synthInstance (mkApp (mkConst ``Inhabited [Level.one]) ty)]
  let atI := atInstance f a.typeParams targExprs
  let vars ← c.vars.mapM fun v => do
    let ptype := Core.instanceResult (v.ptype.asParams f a.typeParams) targs
    return { v with type := atI v.type, ptype, fact? := ← hooks.fact ptype false }
  let props := c.props.map fun p => { p with body := atI p.body, trigger? := p.trigger?.map atI }
  let indexes := c.indexes.map fun (n, pl, r, q, g) => (n, pl, r, q, atI g)
  let defs := c.defs.map fun (d, e) => (d, atI e)
  let uses ← usesOf (props.map (·.body) ++ indexes.map (·.2.2.2.2) ++ defs.map (·.2))
  return { c with vars, props, indexes, defs, uses, fn? := some (Core.instanceName f targs)
                  finiteModel := targs.any (·.hasTypeParam) }

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
parameters, to all of them, in `e`, each once, added to `acc`. An
application that mentions a bound variable, of an unbounded quantifier's
`∀` or `∃` (`Reqs/Lang/Quantifiers#unbounded-quantifiers`), is closed over
the binders around it, `bs`, outermost first, as a `fun`: its facts hold
for every value of them (`closedFacts`). Elsewhere, none of a check's
formulas applies a function under a binder: a `match` is a chain of `if`s
over selectors, a global expectation's binders are locals, defined
functions, whose bodies apply no uninterpreted function, and the clauses of
contracts, which the `fren` command's queries apply as functions too, are
unfolded only after the facts are found, and under realizability's `∃`,
an application's arguments mention no output (`lang::argument`). An
application is met before its arguments, and they from left to right, as
`natAppFacts` orders them. -/
partial def natApps (fs : Array (Expr × Nat)) (e : Expr) (acc : Array Expr := #[])
    (bs : Array (Name × Expr × BinderInfo) := #[]) : Array Expr :=
  match e with
  | .app .. =>
    let full := fs.contains (e.getAppFn, e.getAppNumArgs)
    let closed := bs.foldr (fun (n, d, bi) b => .lam n d b bi) e
    let a := if e.hasLooseBVars then closed else e
    let acc := if full && !a.hasLooseBVars && !acc.contains a then acc.push a else acc
    e.getAppArgs.foldl (fun acc x => natApps fs x acc bs) acc
  | .lam n d b bi | .forallE n d b bi => natApps fs b (natApps fs d acc bs) (bs.push (n, d, bi))
  | .letE n t v b _ => natApps fs b (natApps fs v (natApps fs t acc bs) bs) (bs.push (n, t, .default))
  | .mdata _ b | .proj _ _ b => natApps fs b acc bs
  | _ => acc

/-- The facts of `app`, by `factsOf`, where `app` is an application closed
over the binders around it as a `fun` (`natApps`): each holds for every
value of the binders that it mentions, as `∀`. -/
def closedFacts (factsOf : Expr → MetaM (Array (Name × Expr))) (app : Expr) : MetaM (Array (Name × Expr)) := do
  unless app.isLambda do return ← factsOf app
  lambdaTelescope app fun xs body => do
    (← factsOf body).mapM fun (n, f) => return (n, ← mkForallFVars (xs.filter (f.containsFVar ·.fvarId!)) f)

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

/-- What enumerates the checks of a comp set to enumeration
(`Reqs/Check#checking-by-enumeration`), given the comp, its formulas, the
locals of its variables, and of the abstract types and functions that it
uses, with the functions among them, and the kinds of check to run:
`Fren.Enumerate`'s, which needs the elaborator. -/
abbrev EnumHook := CompInfo → Core.Comp Expr → Array Expr → Array Expr → Array (Name × Expr × Nat × Bool) →
  Array CheckKind → MetaM (Except Core.Msg Core.Enumeration.Enumerated)

/-- All selected checks for one comp, in reporting order, with the theorems
that its cover goals are met (`coverWitness`), for the caller to add, and
what enumerating the checks set to enumeration found, by `enumerate`. -/
partial def checkComp (c : CompInfo) (kinds : Array CheckKind := Core.CheckKind.all) (enumerate? : Option EnumHook := none)
    (hooks? : Option ElabHooks := none) (own : Array (Array Core.Ty) := #[])
    (foreign : Array (Name × Array Core.Ty) := #[]) :
    MetaM (Array CheckResult × Array Declaration × Option (Except Core.Msg Core.Enumeration.Enumerated)) := do
  let c := { c with uses := ← checkUses c }
  -- As elaborated, for its contract's instances (`instanceContract`).
  let elaborated := c
  let st0 ← getState
  -- The generic functions without a body that it uses, each with the
  -- number of type arguments and instances that it takes first.
  let generics ← c.uses.filterMapM fun u => return (← genericOf? u).map fun a => (a, 2 * a.typeParams.size)
  -- The contract of an uninterpreted function, whose value is an output.
  let contract := c.fn?.isSome && c.vars.any (·.role == .output)
  -- The abstract types and functions become locals, which lean-smt
  -- declares as sorts and uninterpreted functions (`check::Interpretations`).
  withNatUses c.uses fun ufs fns => do
  let rep (e : Expr) : MetaM Expr := Lean.Core.betaReduce (replaceUses c.uses ufs e)
  -- The instances of the generic functions without a body that its
  -- formulas apply, once the defined functions and clauses that they apply
  -- are unfolded, and those that the clauses of each apply at it, each a
  -- local of its own (`withInstances`).
  let gens := generics.map fun (a, m) => (a.placeholder, m, Core.instanceNat a.result)
  let formulas := c.props.map (·.body) ++ c.defs.map (·.2) ++ c.indexes.map (·.2.2.2.2)
    ++ c.insts.flatMap fun i => #[i.bindings, i.behaviour] ++ i.assumes.map (·.2)
  let mut insts := #[]
  if !gens.isEmpty then
    for e in formulas do insts := instancesIn gens (← unfoldDefined (← rep e)) insts
  let mut done := 0
  while done < insts.size do
    let (u, pre) := insts[done]!
    done := done + 1
    let some (a, _) := generics.find? (·.1.placeholder == u) | continue
    let k := st0.contracts.get? a.path
    for cl in ((k.map (·.pres)).getD #[]) ++ ((k.map (·.posts)).getD #[]) do
      insts := instancesIn gens (← unfoldDefined (← rep (cl.atInst a.path a.typeParams pre #[]))) insts
  -- Each instance's signature and result type's constraint, at its type
  -- arguments (`lang::uninterpreted_instance`), as the elaborator gives
  -- them, over the locals.
  let consts := (c.uses.zip ufs).filter (·.2.isFVar)
  let unrep (e : Expr) : Expr := e.replaceFVars (consts.map (·.2)) (consts.map (mkConst ·.1))
  let sigs : Array (Option (Expr × Option Expr)) ← insts.mapM fun (u, pre) => do
    let some hooks := hooks? | return none
    let some (a, m) := generics.find? (·.1.placeholder == u) | return none
    let some tys ← ((List.range (m / 2)).toArray.mapM fun i => hooks.coreTy (unrep pre[2 * i]!)) <&> (·.mapM id)
      | return none
    let (ps, r) := Core.instanceSig a.declared a.result tys
    let nat := Core.instanceNat a.result
    let ty ← mkArrowN (← ps.mapM hooks.leanType) (← if nat then pure (mkConst ``Int) else hooks.leanType r)
    let fact? ← (← hooks.fact (Core.instanceResult a.resultP tys) nat).mapM rep
    return some (← rep ty, fact?)
  withInstances gens insts (sigs.map (·.map (·.1))) fun ixs => do
  let instances := replaceInstances gens insts ixs
  let c := { c with vars := ← c.vars.mapM fun v => return { v with type := ← rep v.type } }
  withLocalDeclsD (c.vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
  let copied := c.vars.filter fun v => (Core.Symbol.ofRole v.role).copied
  withLocalDeclsD (copied.map fun v => (Core.primed v.name, fun _ => pure v.type)) fun primes => do
    let beta (e : Expr) : MetaM Expr := return (← rep e).beta fvs
    -- The indexes, and the questions about tables.
    let indexes := c.indexes.filter (·.2.2.2.1.isNone)
    -- Each case's reachability questions, which a `let` or `where` name
    -- gives at each mention, merged (`Core.mergeReach`).
    let tables ← (c.indexes.filterMap fun (n, place, r, q?, g) => q?.map fun q => ((n, place, r.getPos?), q, g)).mapM
      fun (k, q, g) => return (k, q, ← beta g)
    let tables := (Core.mergeReach Lean.mkAnd tables).map fun ((n, place, _), q, g) => (n, place, q, g)
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
        assumes := ← i.assumes.mapM fun (n, a) => return (n, ← beta a), typed := i.typed }
      triggers := ← (c.ensures ++ c.expects).filterMapM fun p => p.trigger?.mapM fun t => return (p.name, ← beta t)
      -- Numbered in order within each item.
      indexes := ← indexes.mapIdxM fun j (n, place, _, _, goal) => do
        let k := (indexes.extract 0 j).filter (·.1 == n) |>.size
        return { prop := n, k, place, goal := ← beta goal, patTy? := obligationTy? goal }
      tables := tables.mapIdx fun j (n, place, q, goal) =>
        let k := (tables.extract 0 j).filter (·.1 == n) |>.size
        { site := { prop := n, k, place, goal }, goal := q }
      defs := ← c.defs.filterMapM fun (d, e) => do
        let some i := c.vars.findIdx? (·.name == d) | return none
        let e ← beta e
        return some (d, ← mkEq fvs[i]! e, e) }
    -- An uninterpreted function's contract, as both front ends build it
    -- (`Core.contractComp`).
    -- A generic one's is checked once, at its type parameters
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
    let generic := c.fn?.any fun f => ((st0.abstracts.get? f).map (!·.typeParams.isEmpty)).getD false
    let comp : Core.Comp Expr := match contract, c.fn?, c.vars.back? with
      | true, some f, some v =>
        Core.contractComp c.path f (c.vars.pop.map fun (x : Var) => x.name) v.name comp.assumes comp.reqs comp.tables generic
      | _, _, _ => comp
    -- What the `Nat` variables bring (`lang::nat_variable`): each, of both
    -- copies, is at least 0. Each query's applications bring their own
    -- (`Core.appFacts`).
    let varFacts (outputs : Bool) : MetaM (Array (Name × Expr)) := do
      let vs := (c.vars.zip fvs).filter fun (v, _) => match Core.natBrought (v.role == .output) v.defn?.isSome with
        | .nothing => false
        | .guarantee => outputs
        | .assumption => !outputs
      vs.flatMapM fun (v, x) => do
        let nat ← if v.type.isConstOf ``Nat then pure #[(`nat, ← atLeast0 x)] else pure #[]
        let ty ← v.fact?.mapM fun p => return (`type, ← rep (p.beta #[x]))
        return nat ++ ty.toArray
    let outFacts ← varFacts true
    let facts ← varFacts false
    let copiedFvs := (c.vars.zip fvs).filter (fun (v, _) => (Core.Symbol.ofRole v.role).copied) |>.map (·.2)
    let all := facts ++ outFacts
    let facts := all ++ (all.map fun (n, f) => (n, f.replaceFVars copiedFvs primes)).filter (!all.contains ·)
    let outFacts := outFacts.map (·.2)
    -- The applications of functions into pattern types, and the reads of
    -- recursive enumerations' payloads, that bring a constraint, each with
    -- its predicate (`Reqs/Check`).
    let st ← getState
    -- A generic enumeration's selector takes its type arguments and their
    -- `Inhabited` instances before the value, and so does its predicate.
    let typedApps : Array (Expr × Nat × Expr × Nat) :=
      fns.filterMap (fun (u, x, n, _) =>
        (st.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == u then some a else none).bind fun a =>
          a.fact?.map fun p => (x, n, p, 0))
      ++ st.enums.foldl (init := #[]) fun acc _ e =>
        acc ++ e.readFacts.map fun (sel, p) => (mkConst sel, 1 + 2 * e.params.size, p, 2 * e.params.size)
    -- Whether its queries may quantify over a collection's elements, read
    -- from the types, as the `fren` command's `State.bounded` reads it:
    -- its variables' types' constraints, the obligations it asks, and the
    -- results of the functions it uses.
    let quantifies (e : Expr) := (e.find? fun x => x.isForall && !x.isArrow).isSome
    let bounded := c.guarded || c.vars.any (fun v => v.fact?.isSome && (v.ptype.cons st.shapeOf).any (·.quantifies))
      || c.indexes.any (fun (_, _, _, _, g) => (obligationTy? g).isSome && quantifies g)
      || c.insts.any (fun i => i.assumes.any fun (n, a) => i.typed.any (·.1 == n) && quantifies a)
      || c.uses.any fun u => st.abstracts.foldl (init := false) fun acc _ a =>
        acc || (a.placeholder == u && (a.ptys.2.cons st.shapeOf).any (·.quantifies))
    -- What stands for the abstract types and functions, by which a formula
    -- uses them (`Core.coverInterpreted`).
    let useIds := ufs.foldl (fun acc u => (collectFVars acc u)) {} |>.fvarIds
    -- And a generic function without a body, which stays itself.
    let interprets (e : Expr) : Bool :=
      e.hasAnyFVar useIds.contains || generics.any fun (a, _) => (e.find? (·.isConstOf a.placeholder)).isSome
    let full := { comp with typesInterpreted := c.vars.any fun v => interprets v.type }
    -- Only the `fren` command runs the checks set to testing (`check::by_testing`),
    -- and enumeration those set to enumeration (`check::by_evidence`).
    let enumerated ← if c.enumerated.any then (enumerate?.mapM fun f => f c full fvs ufs fns kinds) else pure none
    let (comp, kinds) := full.untested (c.tested.union c.enumerated) kinds
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
    let factFns := fns.filter fun (u, x, _, nat) => nat || !(postsOf u).isEmpty || typedApps.any (·.1 == x)
    let implies (ps : Array Expr) (q : Expr) : Expr := ps.foldr (fun p acc => mkForall `h .default p acc) q
    -- Of an application of a generic function without a body, at its
    -- instance (`lang::uninterpreted_instance`): its clauses and its result
    -- type's constraint with the type arguments for the type parameters.
    let genericFacts (a : AbstractInfo) (m : Nat) (app : Expr) : MetaM (Array (Name × Expr)) := do
      let args := app.getAppArgs
      let (targs, vals) := (args.extract 0 m, args.extract m)
      let nat := Core.instanceNat a.result
      -- Over an `Int`, as the solver sees a function into `Nat`.
      let v := if nat then mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) app else app
      -- The constraint of its instance's result type, which the
      -- elaborator gives at the instance.
      let j? := insts.findIdx? fun (u, pre) => u == a.placeholder
        && (List.range (m / 2)).all fun i => pre[2 * i]! == targs[2 * i]!
      let fact? : Option (Option Expr) := match j? with
        | some j => (sigs[j]?.join).map fun (x : Expr × Option Expr) => x.2
        | none => none
      let typeFact ← match fact?.join <|> (if hooks?.isSome then none else (a.fact?.map (atInstance a.path a.typeParams targs))) with
        | some p => pure #[(`type, ← rep (p.beta #[v]))]
        | none => pure #[]
      let k := st0.contracts.get? a.path
      let pres ← ((k.map (·.pres)).getD #[]).mapM fun c => rep (c.atInst a.path a.typeParams targs vals)
      let posts ← ((k.map (·.posts)).getD #[]).mapM fun c => return (c.name, ← rep (c.atInst a.path a.typeParams targs vals))
      let natFact ← if nat then pure #[(`nat, ← atLeast0 app)] else pure #[]
      return natFact ++ typeFact ++ Core.postconditionFacts implies pres posts
    -- An application's `nat`, then its `type`, then its postconditions'.
    let factsOf (app : Expr) : MetaM (Array (Name × Expr)) := do
      if let some (a, m) := generics.find? (app.getAppFn.isConstOf ·.1.placeholder) then return ← genericFacts a m app
      let typeFact ← match typedApps.find? (·.1 == app.getAppFn) with
        | some (_, _, p, k) => pure #[(`type, ← rep (p.beta ((app.getAppArgs.extract 0 k).push app)))]
        | none => pure #[]
      let some (u, _, _, nat) := factFns.find? (·.2.1 == app.getAppFn) | return typeFact
      let args := app.getAppArgs
      let pres ← (presOf u).mapM fun k => rep (k.at args)
      let posts := Core.postconditionFacts implies pres (← (postsOf u).mapM fun k => return (k.name, ← rep (k.at args)))
      let natFact ← if nat then pure #[(`nat, ← atLeast0 app)] else pure #[]
      return natFact ++ typeFact ++ posts
    let bk (k : CheckKind) :=
      let heads := factFns.map (fun (_, x, n, _) => (x, n)) ++ typedApps.map (fun (x, n, _, _) => (x, n))
        ++ generics.map fun (a, m) => (mkConst a.placeholder, m + a.declared.size)
      let b := leanBackend c fvs primes cache facts outFacts (natApps heads ·) (closedFacts factsOf)
        (modelOptional := k == .cover) bounded instances (finiteModel := generic || c.finiteModel)
      if k != .cover then b else
      { b with query := fun hyps goal wantModel => do
          let o ← b.query hyps goal wantModel
          if let .sat model := o then models.modify (·.push (goal, model))
          return o }
    let examples := fren.examples.get (← getOptions)
    let results := Core.withInterpreted full interprets (← Core.checkComp bk comp kinds (some examples) interprets)
    -- The contract of a generic function without a body, where its check
    -- at its type parameters' sorts does not pass: its check at each
    -- instance that the spec applies (`lang::generic_contract`).
    let results ← match generic, c.fn?, hooks?, results.find? (·.kind == .realizable) with
      | true, some f, some hooks, some r =>
        if r.verdict == .pass then pure results else do
        let mut instResults := #[]
        for targs in own do
          let ic ← instanceContract hooks elaborated f targs
          let (rs, _, _) ← checkComp ic #[.realizable] none hooks?
          instResults := instResults ++ rs.filter (·.kind == .realizable)
        let checked := Core.genericContract (·.verdict) r instResults
        pure (results.foldl (init := #[]) fun acc x => if x.kind == .realizable then acc ++ checked else acc.push x)
      | _, _, _, _ => pure results
    -- The instances whose contracts this item's checks check, of functions
    -- declared in modules that this one imports (`lang::instance_site`),
    -- where the function's check at its type parameters' sorts does not
    -- pass, reported at the item, without notes at the clauses, which
    -- another file has.
    let mut results := results
    if let some hooks := hooks? then
      for (f, targs) in foreign do
        let some b := st0.bodies.get? f | continue
        let (rs, _, _) ← checkComp b #[.realizable]
        unless rs.any fun r => r.kind == .realizable && r.verdict != .pass do continue
        let ic ← instanceContract hooks b f targs
        let (rs, _, _) ← checkComp ic #[.realizable] none hooks?
        results := results ++ (rs.filter (·.kind == .realizable)).map fun r => { r with clashes := #[] }
    let mut witnesses := #[]
    for g in c.covers do
      let passed := results.any fun r => r.kind == .cover && r.prop? == some g.name && r.verdict == .pass
      let goal := mkNot (← beta g.body)
      if let some (_, model) := (← models.get).find? (·.1 == goal) then
        if passed then
          if let some d ← coverWitness c fvs g model then witnesses := witnesses.push d
    return (results, witnesses, enumerated)

end Fren
