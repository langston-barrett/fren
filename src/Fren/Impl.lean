-- keep-sorted start
import Fren.Check
import Fren.Elab
-- keep-sorted end

/-!
# `impl`: linking procedures to Lean code

`impl n: c for (xs) { x := t, ... }` interprets each parameter and result
of procedure `c` as a Lean term over the binders `xs`, and adds a theorem `n`
stating that the interpretation satisfies `c` (`Reqs/Impl`, module `impls`):

  `∀ xs, c.assumes ins outs default → ∃ hidden, c.defs ins outs hidden ∧ c.ensures ins outs hidden ∧ c.call.w ... ∧ ...`

where `hidden` are `c`'s private variables and its calls' variables, which
assumptions never mention, and `c.defs` is there only if `c` has defined
outputs. The proof is the one written after `by`; without
one, `decide` (evaluated by the kernel), then the solver, whose success adds
the statement as an axiom.
-/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of this
-- file's many indexes. This rule, tried first, proves it at once, and fails
-- at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

namespace Lang

syntax fren_impl_map := ident " := " term

/-- `(x y : T)`. Only explicit binders: `{` starts the terms. -/
syntax fren_impl_binder := "(" ident+ " : " term ")"

/-- `impl n: c for (xs) { x := t, ... } [by tac]`: the terms satisfy procedure `c`. -/
scoped syntax (name := implCmd) "impl " ident " : " fren_path (" for " fren_impl_binder+)?
  " { " sepBy(fren_impl_map, ", ", ", ", allowTrailingSep) " }" (" by " Lean.Parser.Tactic.tacticSeq)? : command

/-- `interp p := t [by tac]`: the Lean meaning of abstract type or function
`p`, and for a function with postconditions or whose result type brings a
constraint, the proof that `t` meets them. -/
scoped syntax (name := interpCmd) "interp " fren_path " := " term (" by " Lean.Parser.Tactic.tacticSeq)? : command

end Lang

/-- What an `interp` names (`impls::Interpreted`). -/
inductive Interpreted where
  | abstractType
  | function
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether an `interp` is accepted, from what it names, how many
interpretations of it there already are, whether its term has the required
type, and for a function, whether the abstract types of its signature are
interpreted (`impls::interpretation`). -/
def interpAccepted (what : Interpreted) (earlier : Nat) (typed typesInterpreted : Bool) : Bool :=
  what != .other && earlier == 0 && typed && (what != .function || typesInterpreted)

/-- Whether an `impl` is accepted, from the abstract types and functions its
procedure uses, and those interpreted (`impls::interpreted`). -/
def interpretedAccepted (used interpreted : Array Name) : Bool := used.all interpreted.contains

/-- The interpretations of the placeholders `uses`, as constants, or the
first item that has none. -/
def interpsOf (uses : Array Name) : MetaM (Except Name (Array Expr)) := do
  let s ← getState
  let mut used := #[]
  for u in uses do
    let some a := s.abstracts.foldl (init := none) fun acc _ a => if a.placeholder == u then some a else acc
      | return .error u
    used := used.push a.path
  -- An abstract type's `Inhabited` instance is the interpretation's own.
  let own := used.filter (!isInhabitedName ·)
  let interpreted := s.interps.foldl (init := #[]) fun acc p _ => acc.push p
  unless interpretedAccepted own interpreted do
    return .error ((own.find? (!interpreted.contains ·)).getD .anonymous)
  let mut ι := #[]
  for p in used do
    if isInhabitedName p then
      let some t := (used.idxOf? (p.getPrefix)).bind (ι[·]?) | return .error p
      let some inst ← synthInstance? (mkApp (Lean.mkConst ``Inhabited [Level.one]) t) | return .error p
      ι := ι.push inst
    else if let some d := s.interps.get? p then ι := ι.push (Lean.mkConst d)
  return .ok ι

/-- The verdict on an `impl`'s obligation, whether to report a
counterexample, and whether the statement is added as an axiom
(`impls::obligation`). `decideQ` is `unsat` if `decide` proves it, `sat` if it
evaluates to false and `unknown` if it does not apply. -/
def implVerdict (written writtenOk : Bool) (decideQ smtQ : Core.Answer) : Core.Verdict × Bool × Bool :=
  if written then (if writtenOk then .pass else .fail, false, false)
  else match decideQ with
    | .unsat => (.pass, false, false)
    | .sat => (.fail, true, false)
    | .unknown => if smtQ == .unsat then (.pass, false, true) else (.inconclusive, false, false)

/-- Whether an `impl`'s statement is added, as a theorem or an axiom
(`impls::statement`). -/
def implAdded (verdict : Core.Verdict) : Bool := verdict == .pass

/-- Whether an added `impl` holds only because no values of its binders
satisfy its procedure's assumptions (`impls::vacuity`). `found` is whether
trying every value of finite binders (`finite`) finds some that do, and
`smtQ` is the solver's answer to whether none do, asked otherwise. -/
def implVacuous (added finite found : Bool) (smtQ : Core.Answer) : Bool :=
  added && (if finite then !found else smtQ == .unsat)

/-- Whether an `impl` is evidence for its procedure (`impls::vacuity`). -/
def implEvidence (added vacuous : Bool) : Bool := added && !vacuous

/-- Whether a variable may be given `n` terms by an `impl`
(`impls::mapping`): each parameter and result exactly once, anything else
never. -/
def mappingOk (role : Core.Role) (isPub : Bool) (n : Nat) : Bool :=
  n == if role == .input || (role == .output && isPub) then 1 else 0

/-- Whether an `impl` that gives terms for `names` is accepted, where `vars`
are the procedure's variables (name, role and visibility). -/
def mappingAccepted (vars : Array (Name × Core.Role × Bool)) (names : Array Name) : Bool :=
  names.all (fun n => vars.any (·.1 == n)) && vars.all fun (v, r, p) => mappingOk r p (names.count v)

/-- Checks the names an `impl` maps (`mappingAccepted`), explaining the
first problem. -/
def checkMapping (c : CompInfo) (names : Array Name) : Except (Option Nat × String) Unit := do
  if mappingAccepted (c.vars.map fun v => (v.name, v.role, v.isPub)) names then return
  let comp := Core.showComp c.path
  let again := Core.repeatsAt names
  for n in names, i in [0:names.size] do
    match c.vars.find? (·.name == n) with
    | none => throw (some i, s!"`{comp}` has no variable `{n}`")
    | some v =>
      if v.role == .output && !v.isPub then
        throw (some i, s!"`{n}` is a private variable of `{comp}`\n\nnote: private variables are internal: the obligation only says they exist")
      if v.role != .input && v.role != .output then
        throw (some i, s!"`{n}` belongs to call `{n.getRoot}` of `{comp}`\n\nnote: calls are internal: the obligation only says their variables exist")
      if again.contains i then throw (some i, s!"`{n}` is mapped multiple times")
  let missing := c.vars.filter fun v =>
    (v.role == .input || (v.role == .output && v.isPub)) && !names.contains v.name
  unless missing.isEmpty do
    let ns := ", ".intercalate (missing.toList.map fun v => s!"`{v.name}`")
    throw (none, s!"missing {ns} of `{comp}`\n\nnote: every parameter and result is given a term")
  throw (none, s!"internal error: the terms for `{comp}` are rejected without a reason")

/-- `decide p`, evaluated: `some (true | false)`, or `none` if `p` is not
decidable or the evaluation gets stuck. -/
def evalDecide (p : Expr) : MetaM (Option Bool) := do
  try
    let .some inst ← trySynthInstance (mkApp (mkConst ``Decidable) p) | return none
    let r ← withTransparency .all <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)
    if r.isConstOf ``Bool.true then return some true
    if r.isConstOf ``Bool.false then return some false
    return none
  catch _ => return none

/-- Every value of `ty`, from its `Fren.Finite` instance. -/
def finiteValues (ty : Expr) : MetaM (Option (Array Expr)) := do
  -- A function type is never listed, and searching for an instance for one
  -- can leave universe metavariables behind.
  if (← whnf ty).isForall then return none
  try
    let .some inst ← trySynthInstance (mkApp (mkConst ``Fren.Finite) ty) | return none
    let mut l ← whnf (mkApp2 (mkConst ``Fren.Finite.all) ty inst)
    let mut vals := #[]
    while l.isAppOfArity ``List.cons 3 do
      vals := vals.push (← whnf l.appFn!.appArg!)
      l ← whnf l.appArg!
    return if l.isAppOfArity ``List.nil 1 then some vals else none
  catch _ => return none

/-- Every combination of values of the binders `xs`, if they are all finite
and there are at most `limit` combinations. -/
def assignments (xs : Array Expr) (limit : Nat := 4096) : MetaM (Option (Array (Array Expr))) := do
  let mut domains := #[]
  for x in xs do
    let some vs ← finiteValues (← inferType x) | return none
    domains := domains.push vs
  if domains.foldl (· * ·.size) 1 > limit then return none
  return some <| domains.foldl (init := #[#[]]) fun acc vs => acc.flatMap fun c => vs.map c.push

/-- Values of the binders `xs` for which `p` is false, if they are all
finite and there are not too many combinations. -/
def counterexample (xs : Array Expr) (p : Expr) : MetaM (Option (Array Expr)) := do
  let some combos ← assignments xs | return none
  for vals in combos do
    if (← evalDecide (p.replaceFVars xs vals)) == some false then return some vals
  return none

/-- The statement of an `impl` and what reporting needs from it. -/
structure Obligation where
  stmt : Expr
  /-- `decideQ` for `implVerdict`. -/
  decideQ : Core.Answer
  /-- A failure: binder names and values, and the requirements they falsify. -/
  failure? : Option (Array (Name × String) × Array Name) := none
  /-- That no values of the binders satisfy the assumptions. -/
  never : Expr
  /-- For finite binders, whether some values satisfy the assumptions. -/
  found? : Option Bool
  deriving Inhabited

open Lang in
/-- Builds the obligation of `impl` for procedure `c` with binders `binders`
and maps `maps`, and, unless the `impl` has a written proof (`written`),
evaluates it with `decide` if possible. -/
def mkObligation (c : CompInfo) (binders : Array Syntax) (maps : Array Syntax) (written : Bool) :
    TermElabM Obligation := do
  -- The interpretations of the abstract types and functions it uses.
  let ι ← match ← interpsOf c.uses with
    | .ok ι => pure ι
    | .error p => throwError s!"`{Core.showComp c.path}` uses `{Core.showComp p}`, which has no interpretation\n\n\
        help: give it one with `interp {Core.showComp p} := ...` before this `impl`"
  let c : CompInfo := { c with vars := c.vars.map fun (v : Var) => { v with «type» := replaceUses c.uses ι v.type } }
  elabBinders binders fun xs => do
    -- The procedure's variables: mapped terms, or bound below
    let mut args : Array (Option Expr) := #[]
    for v in c.vars do
      match maps.find? (·[0].getId == v.name) with
      | some m =>
        let t ← withoutErrToSorry <| withSynthesize <| elabTermEnsuringType m[2] v.type
        let t ← instantiateMVars t
        if t.hasMVar || t.hasSorry then throwErrorAt m[2] "could not elaborate this term"
        -- An `Int` bound to an `Int`, not a `Nat` widened, keeps it one (`lint::manual_nat`).
        if v.type.isConstOf ``Int && !(t.isAppOfArity ``Nat.cast 3 || t.isAppOfArity ``Int.ofNat 1) then
          modifyLocal fun l => { l with natKept := l.natKept.push (c.path, Core.nameText v.name) }
        args := args.push (some t)
      | none => args := args.push none
    let hidden := (c.vars.zip args).filterMap fun (v, a) => if a.isNone then some v else none
    withLocalDeclsD (hidden.map fun v => (v.name, fun _ => pure v.type)) fun hs => do
      let mut full := #[]
      let mut withDefaults := #[]
      let mut k := 0
      for v in c.vars, a in args do
        match a with
        | some t => full := full.push t; withDefaults := withDefaults.push t
        | none =>
          full := full.push hs[k]!
          withDefaults := withDefaults.push (← mkAppOptM ``Inhabited.default #[v.type, none])
          k := k + 1
      let assumes := mkAppN (mkConst (c.decl ++ `assumes)) (ι ++ withDefaults)
      let reqs := mkAppN (mkConst (c.decl ++ `ensures)) (ι ++ full)
      let defs := if c.defs.isEmpty then [] else [mkAppN (mkConst (c.decl ++ `defs)) (ι ++ full)]
      let body := mkAndN (defs ++ reqs :: c.insts.toList.map fun i => mkAppN (Lean.mkConst i.decl) (ι ++ full))
      let ex ← hs.foldrM (init := body) fun h acc => do mkAppM ``Exists #[← mkLambdaFVars #[h] acc]
      synthesizeSyntheticMVarsNoPostponing
      let inner ← instantiateMVars (← mkArrow assumes ex)
      let stmt ← instantiateMVars (← mkForallFVars xs inner)
      if stmt.hasMVar || stmt.hasLevelMVar then throwError "could not elaborate the statement{indentExpr stmt}"
      -- Whether the assumptions can hold: if not, the statement says nothing.
      let assumes ← instantiateMVars assumes
      let never ← mkForallFVars xs (mkNot assumes)
      let found? ← (← assignments xs).mapM fun combos =>
        combos.anyM fun vals => return (← evalDecide (assumes.replaceFVars xs vals)) == some true
      if written then return { stmt, decideQ := .unknown, never, found? }
      let some ok ← evalDecide stmt | return { stmt, decideQ := .unknown, never, found? }
      if ok then return { stmt, decideQ := .unsat, never, found? }
      -- Find values that falsify it, and name the requirements they falsify.
      let some vals ← counterexample xs inner | return { stmt, decideQ := .sat, never, found? }
      let names ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName
      let shown ← (xs.zip vals).mapM fun (x, v) => do return render (← inferType x) v
      let shown ← shown.mapM id
      let falsified ← if !hs.isEmpty then pure #[] else
        c.ensures.filterM fun p => do
          let r := mkAppN (mkConst p.decl) (ι ++ full)
          return (← evalDecide ((← mkArrow assumes r).replaceFVars xs vals)) == some false
      return { stmt, decideQ := .sat, failure? := some (names.zip shown, falsified.map (·.name)), never, found? }

/-- The Lean definitions Fren generated for comps. -/
def generatedDecls : MetaM NameSet := do
  let mut ns : NameSet := {}
  for (_, c) in (← getState).comps do
    ns := ns.insert (c.decl ++ `assumes) |>.insert (c.decl ++ `ensures)
    for p in c.props do ns := ns.insert p.decl
    unless c.defs.isEmpty do ns := ns.insert (c.decl ++ `defs)
    for (d, _) in c.defs do ns := ns.insert (c.decl ++ `def ++ d)
    for i in c.insts do ns := ns.insert i.decl
  for (_, d) in (← getState).defined do ns := ns.insert d.decl
  for (_, k) in (← getState).contracts do
    for c in k.pres ++ k.posts do ns := ns.insert c.decl
  return ns

/-- Asks the solver to prove `stmt`, with Fren's generated definitions, and
the interpretations if `interps`, unfolded, and the implementation's treated
as uninterpreted. -/
def solverAnswer (stmt : Expr) (interps := false) : MetaM Core.Answer := do
  -- A binder of a function type is beyond the solver's first-order logic,
  -- and lean-smt's preprocessing fails on one.
  if ← forallTelescopeReducing stmt fun xs _ => xs.anyM fun x => return (← whnf (← inferType x)).isForall then
    return .unknown
  let mut gen ← generatedDecls
  if interps then
    for (_, d) in (← getState).interps do gen := gen.insert d
  let stmt ← Meta.deltaExpand stmt gen.contains
  -- Without the `let`s of record updates and the `have`s of `let`s and
  -- `where` clauses, which lean-smt does not translate.
  let stmt ← Meta.zetaReduce (← Core.betaReduce stmt)
  let mv ← mkFreshExprMVar stmt
  try
    match ← Smt.smt { trust := true, timeout := some (fren.timeout.get (← getOptions))
                      extraSolverOptions := resourceLimitOptions (← getOptions) } mv.mvarId! #[] with
    | .unsat .. => return .unsat
    | .sat .. => return .sat
    | .unknown _ => return .unknown
  catch _ => return .unknown

open Lang in
@[command_elab Lang.implCmd] def elabImpl : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
  openGenerated
  noteSettingsSeen
  let nameStx := stx[1]
  let declName := (← getCurrNamespace) ++ nameStx.getId
  let r ← resolvePath (← getLocal).currentModule (pathSegs stx[3])
  let .item { kind := .compItem, path, .. } := r
    | throwErrorAt stx[3] (Core.notACompMsg r).text
  let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
  let compStr := Core.showComp path
  let binders ← if stx[4].isNone then pure #[] else stx[4][1].getArgs.mapM fun b =>
    `(bracketedBinder| ($(b[1].getArgs.map (⟨·⟩))* : $(⟨b[3]⟩)))
  let maps := stx[6].getSepArgs
  match checkMapping c (maps.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (some i, msg) => throwErrorAt maps[i]![0] msg
  | .error (none, msg) => throwErrorAt nameStx msg
  let ob ← liftTermElabM <| mkObligation c binders maps (!stx[8].isNone)
  -- Records an added statement as evidence, unless it holds only because
  -- the assumptions never do.
  let recordEvidence (isAxiom : Bool) : CommandElabM Unit := do
    let smtQ ← if ob.found?.isSome then pure .unknown else liftTermElabM (solverAnswer ob.never (interps := true))
    let vacuous := implVacuous true ob.found?.isSome (ob.found?.getD false) smtQ
    if implEvidence true vacuous then
      record (.implInfo (ImplInfo.mk declName path isAxiom))
    else
      logWarningAt nameStx s!"`{nameStx.getId}` holds only because no values of its binders satisfy the assumptions of `{compStr}`\n\n\
        note: it is not evidence for `{compStr}`\n\
        help: check the terms it gives the inputs, and the interpretations they use"
  -- A written proof
  if !stx[8].isNone then
    let tac : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[8][1]⟩
    let errorsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
    let pf ← liftTermElabM do
      let pf ← elabTermEnsuringType (← `(by $tac)) ob.stmt
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars pf
    let errors := (← get).messages.toList.filter (·.severity == .error) |>.length
    let (verdict, _, _) := implVerdict true (errors == errorsBefore && !pf.hasMVar) .unknown .unknown
    if implAdded verdict then
      liftCoreM <| addDecl (.thmDecl { name := declName, levelParams := [], «type» := ob.stmt, value := pf })
      recordEvidence false
    return
  let smtQ ← if ob.decideQ == .unknown then liftTermElabM (solverAnswer ob.stmt) else pure .unknown
  let (verdict, namesFailures, isAxiom) := implVerdict false false ob.decideQ smtQ
  if implAdded verdict then
    if isAxiom then
      liftCoreM <| addDecl (.axiomDecl { name := declName, levelParams := [], «type» := ob.stmt, isUnsafe := false })
      recordEvidence true
      return
    else
      let pf ← liftTermElabM do
        let inst ← synthInstance (mkApp (mkConst ``Decidable) ob.stmt)
        return mkApp3 (mkConst ``of_decide_eq_true) ob.stmt inst
          (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      liftCoreM <| addDecl (.thmDecl { name := declName, levelParams := [], «type» := ob.stmt, value := pf })
    recordEvidence false
    return
  match verdict with
  | .pass => pure ()
  | .fail =>
    let subject := s!"`{nameStx.getId}` does not implement `{compStr}`"
    match namesFailures, ob.failure? with
    | true, some (vals, falsified) =>
      let at_ := Core.showAssignment vals
      if falsified.isEmpty then logErrorAt nameStx s!"{subject} when {at_}"
      else
        let verb := if falsified.size == 1 then "is" else "are"
        logErrorAt nameStx s!"{subject}: {Core.showNames falsified} {verb} false when {at_}"
    | _, _ => logErrorAt nameStx s!"{subject}: `decide` evaluates its statement to false"
  | .inconclusive =>
    logWarningAt nameStx s!"could not prove that `{nameStx.getId}` implements `{compStr}`\n\nnote: `decide` does not apply, and the solver did not prove it, without unfolding the Lean functions that the implementation applies\nhelp: write a proof after `by`"

/-- The statement that the interpretation `decl` of the function at `path`
gives values of its result type, if it brings a constraint `typed?`, a
predicate over the abstract types it names, at every argument, and meets
the postconditions of its contract `k` wherever its arguments meet the
preconditions, over the interpretations of the abstract types and
functions that the contract and the result type use
(`Reqs/Impl#interpretations`). -/
def contractStatement (path : Name) (placeholder : Name) (interp : Expr) (k : ContractInfo)
    (typed? : Option (Array Name × Expr) := none) : MetaM Expr := do
  let uses := (k.pres ++ k.posts).foldl (init := (typed?.map (·.1)).getD #[]) fun acc c =>
    c.uses.foldl (fun acc u => if acc.contains u then acc else acc.push u) acc
  -- A generic function's type parameters are the interpretation's own: it
  -- gives each instance a function of its own
  -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
  let a? := (← getState).abstracts.get? path
  let tps := (a?.map (·.typeParams)).getD #[]
  let own := typeParamPlaceholders path tps
  -- The function's own interpretation is `interp`, which is not recorded
  -- until it is proved.
  let others := uses.filter fun u => u != placeholder && !own.contains u
  let ι ← match ← interpsOf others with
    | .ok ι => pure ι
    | .error p => throwError s!"the contract of `{Core.showComp path}` uses `{Core.showComp p}`, which has no interpretation\n\n\
        help: interpret `{Core.showComp p}` first"
  forallTelescope (← inferType interp) fun xs r => do
    let targs := xs.extract 0 own.size
    let ι := uses.map fun u =>
      if u == placeholder then interp
      else match own.idxOf? u with
        | some j => targs[j]!
        | none => ((others.idxOf? u).map (ι[·]!)).getD interp
    let atArgs (c : ClauseInfo) := (replaceUses uses ι (c.at (xs.extract own.size))).headBeta
    -- Over an `Int`, as the solver sees a function into `Nat`.
    let typed := typed?.toList.map fun (_, pred) =>
      let app := mkAppN interp xs
      let v := if r.isConstOf ``Nat then mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) app else app
      (replaceUses own targs (replaceUses uses ι pred)).beta #[v]
    let post := mkAndN (k.posts.map atArgs).toList
    let posts ← if k.posts.isEmpty then pure [] else
      pure [← k.pres.foldrM (fun c acc => mkArrow (atArgs c) acc) post]
    mkForallFVars xs (mkAndN (typed ++ posts))

/-- How an interpretation proves its function's postconditions and its
result type's constraint (`impls::ContractProof`). -/
inductive ContractProofKind where
  | notNeeded
  | theorem
  | axiom
  | unproved
  deriving Inhabited, BEq, DecidableEq, Repr

/-- How an interpretation proves its function's postconditions and its
result type's constraint, from whether it has any, whether it has a
written proof, whether that
elaborates without an error and whether it uses `sorry`, and the answers
of `decide` and the solver, each asked only when the earlier ones prove
nothing (`impls::interpretation_contract`). -/
def contractProofOf (posts written writtenOk usesSorry : Bool) (decideQ smtQ : Core.Answer) : ContractProofKind :=
  if !posts then .notNeeded
  else if written then (if writtenOk && !usesSorry then .theorem else .unproved)
  else match decideQ with
    | .unsat => .theorem
    | .sat => .unproved
    | .unknown => if smtQ == .unsat then .axiom else .unproved

/-- Whether an interpretation is added (`impls::interpretation_contract`):
unless its postconditions are unproved. -/
def contractRecorded (k : ContractProofKind) : Bool := k != .unproved

/-- How a contract's statement was proved (`proveContract`): a proof, or
the solver's answer, an axiom. -/
inductive ContractProof where
  | proof (pf : Expr)
  | solver

open Lang in
/-- Proves that `t`, the interpretation of the function at `path`, whose
placeholder is `placeholder`, gives values of its result type `ty?`, if it
brings a constraint `typed?`, and meets its postconditions
(`contractStatement`): one statement, proved by the interpretation's
tactics if it has any, and otherwise by `decide` or by the solver, which
makes it an axiom; or reports that it is not, as for an `impl`, an error,
and a proof that uses `sorry` is none. -/
def proveContract (stx : Syntax) (path placeholder : Name) (t : Expr) (k : ContractInfo)
    (typed? : Option (Array Name × Expr) := none) (ty : String := "") : CommandElabM (Option ContractProof) := do
  let stmt ← liftTermElabM <| contractStatement path placeholder t k typed?
  let subject := s!"the interpretation of `{Core.showComp path}`"
  -- What it is to prove, with the verb in the third person or not.
  let claim (third : Bool) : String :=
    let give := if third then "gives" else "give"
    let meet := if third then "meets" else "meet"
    match typed?.isSome, k.posts.isEmpty with
    | true, true => s!"{give} values of its result type `{ty}`"
    | true, false => s!"{give} values of its result type `{ty}` and {meet} its postconditions"
    | false, _ => s!"{meet} its postconditions"
  let them := if typed?.isSome && k.posts.isEmpty then "it" else "them"
  -- Every application assumes its result type's constraint.
  let assumed := if typed?.isSome then s!"\nnote: each application of `{Core.showComp path}` is assumed to give one" else ""
  if !stx[4].isNone then
    let tac : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[4][1]⟩
    let errorsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
    let pf ← liftTermElabM do
      let pf ← elabTermEnsuringType (← `(by $tac)) stmt
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars pf
    let errors := (← get).messages.toList.filter (·.severity == .error) |>.length
    let writtenOk := errors == errorsBefore && !pf.hasMVar
    match contractProofOf true true writtenOk pf.hasSorry .unknown .unknown with
    | .theorem => return some (.proof pf)
    | _ =>
      -- An error in the tactics is reported already.
      if writtenOk then
        logErrorAt stx[4] s!"the proof that {subject} {claim true} uses `sorry`\n\n\
          note: an interpretation that is not proved to {claim false} adds nothing"
      return none
  let decided ← liftTermElabM (evalDecide stmt)
  let decideQ : Core.Answer := match decided with | some true => .unsat | some false => .sat | none => .unknown
  let smtQ ← if decideQ == .unknown then liftTermElabM (solverAnswer stmt (interps := true)) else pure .unknown
  match contractProofOf true false false false decideQ smtQ with
  | .theorem =>
    let pf ← liftTermElabM do
      let inst ← synthInstance (mkApp (mkConst ``Decidable) stmt)
      return mkApp3 (mkConst ``of_decide_eq_true) stmt inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    return some (.proof pf)
  | .axiom => return some .solver
  | _ =>
    if decideQ == .sat then
      logErrorAt stx[1] s!"{subject} does not {claim false}: `decide` evaluates the statement to false\n{assumed}\n\
        help: correct the interpretation, or the {if k.posts.isEmpty then "result type" else "contract"}"
    else
      logErrorAt stx[1] s!"could not prove that {subject} {claim true}\n\n\
        note: `decide` does not apply, and the solver did not prove {them}{assumed}\n\
        help: write a proof after `by`"
    return none

open Lang in
@[command_elab Lang.interpCmd] def elabInterp : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
  openGenerated
  let segs := pathSegs stx[1]
  let r ← resolvePath (← getLocal).currentModule segs
  let defined := (← getState).defined
  let (what, path) := match r with
    | .item { kind := .typeItem, path, .. } => (Interpreted.abstractType, path)
    -- A defined function's body gives its meaning.
    | .item { kind := .fnItem, path, .. } => (if defined.contains path then .other else .function, path)
    | r => (.other, r.path)
  if what == .other then throwErrorAt stx[1] (Core.wrongKindMsg "an abstract type or an uninterpreted function" r).text
  let s ← getState
  let earlier := if s.interps.contains path then 1 else 0
  if earlier > 0 then
    throwErrorAt stx[1] s!"`{Core.showComp path}` is already interpreted\n\n\
      note: each abstract type and function has one interpretation, which every `impl` uses"
  let some a := s.abstracts.get? path | throwError "internal error: unknown abstract item `{path}`"
  let decl ← generatedName path
  let term ← liftTermElabM do
    -- The type the term must have: the function's, over the interpretations
    -- of its abstract types.
    let (expected, typesInterpreted) ← match ← interpsOf a.deps with
      | .ok ι => pure (replaceUses a.deps ι (← getConstInfo a.placeholder).type, true)
      | .error p =>
        if what == .function then
          throwErrorAt stx[1] s!"`{Core.showComp path}` mentions `{Core.showComp p}`, which has no interpretation\n\n\
            help: interpret `{Core.showComp p}` first"
        pure (mkSort (.succ .zero), false)
    let t ← withoutErrToSorry <| withSynthesize <| elabTermEnsuringType stx[3] expected
    let t ← instantiateMVars t
    if t.hasMVar || t.hasSorry then throwErrorAt stx[3] "could not elaborate this term"
    -- An abstract type has at least one value.
    let typed ← if what == .abstractType then do
        let r ← trySynthInstance (mkApp (Lean.mkConst ``Inhabited [.succ .zero]) t)
        pure (r matches LOption.some _)
      else pure true
    unless typed do
      throwErrorAt stx[3] "an abstract type's interpretation must have an `Inhabited` instance\n\n\
        note: an abstract type has at least one value"
    unless interpAccepted what earlier typed typesInterpreted do
      throwErrorAt stx[1] "internal error: the interpretation is rejected without a reason"
    return (expected, t)
  let (expected, t) := term
  -- A function's postconditions, and its result type's constraint, which
  -- every application assumes, proved of the term in one statement before
  -- anything is added: an interpretation that does not meet them adds
  -- nothing (`Reqs/Impl#interpretations`).
  let k := ((← getState).contracts.get? path).getD { path, pres := #[], posts := #[], defined := false }
  let typed? := a.fact?.map (a.deps, ·)
  let proof? ← if k.posts.isEmpty && typed?.isNone then pure none else do
    let some p ← proveContract stx path a.placeholder t k typed? a.ptys.2.text | return
    pure (some (k, p))
  liftTermElabM do
    addDecl (.defnDecl { name := decl, levelParams := [], «type» := expected, value := t, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
  record (.interpInfo path decl)
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  -- `decl.ensures`, stated of `decl`, which is `t`.
  if let some (k, p) := proof? then
    let name := decl ++ `ensures
    let stmt ← liftTermElabM <| contractStatement path a.placeholder (mkConst decl) k typed?
    liftCoreM <| addDecl <| match p with
      | .proof value => .thmDecl { name, levelParams := [], «type» := stmt, value }
      | .solver => .axiomDecl { name, levelParams := [], «type» := stmt, isUnsafe := false }

end Fren
