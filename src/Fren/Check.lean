-- keep-sorted start
import Fren.Known
import Fren.Lint
import Fren.Model
import Fren.SeqElems
import Fren.SmtTranslate
import Fren.SolverSorts
import FrenCore.Check
import FrenCore.Goals
import FrenCore.Induction
import FrenCore.Obligations
import FrenCore.SolverTime
import FrenCore.Ty
import Smt
-- keep-sorted end

/-!
# Checks (the controller)

Runs the shared check algorithms (`FrenCore.Check`) on a procedure from the model,
with lean-smt (cvc5) as the backend. Formulas are Lean propositions over free
variables standing for the procedure's variables. Nothing here logs messages or
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
  descr := "the most notes of guarantees that force an output to different values that Fren shows for each unrealizable procedure"
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

/-- The cvc5 option that silences its diagnostics, as the binary's
`solveScript` sets it. cvc5 warns on stderr when a model's value of a
quantified formula cannot be evaluated (`Could not evaluate ... in
getValue.`), which the model then holds as that formula: the warning is not
an outcome, and only cvc5's own diagnostics are silenced. -/
def quietOptions : List (String × String) := [("verbosity", "-1")]

/-- Whether lean-smt's answer says that the query reached its time limit,
whose time `Core.timeQuery` records, as the binary's `solveScript` does. -/
def smtTimedOut : Smt.Result → Bool
  | .unknown reason => Core.timedOutExplanation reason
  | _ => false

/-- The canonical name (`Core.ItemSymbol.text`) of each symbol that lean-smt
gives a spec's types, constructors and selectors, by
the name that it gives it, for the obligations dump (`Core.dump`). -/
def dumpSymbols (st : State) : Std.HashMap String String := Id.run do
  let mut out : Std.HashMap String String := {}
  for (_, e) in st.enums do
    if e.lean?.isSome then continue
    out := out.insert (toString e.decl) (Core.ItemSymbol.datatype e.path).text
    for v in e.variants, idx in [0:e.variants.size] do
      out := out.insert (toString (e.ctor idx)) (Core.ItemSymbol.variant e.path v).text
      for k in [0:((e.payloads[idx]?.map (·.size)).getD 0)] do
        out := out.insert (toString (e.sel idx k)) (Core.ItemSymbol.payload e.path v k).text
  for (_, r) in st.records do
    out := out.insert (toString r.decl) (Core.ItemSymbol.datatype r.path).text
    let ctor := if r.params.isEmpty then recordCtor r.decl else genericRecordCtor r.decl
    out := out.insert (toString ctor) (Core.ItemSymbol.record r.path).text
    for (f, _) in r.fields do
      out := out.insert (toString (ctor ++ f)) (Core.ItemSymbol.field r.path f).text
  -- A newtype, which `fren check` erases, as its underlying type, and its
  -- constructor and its field, as lean-smt names its selector, erased
  -- (`Core.erasedSymbol`). Only a newtype whose underlying type, through
  -- any newtypes, is `Int`, `Nat`, `Bool` or `String` gets that type's sort;
  -- any other keeps lean-smt's name, so that its dumps differ.
  -- A newtype over a newtype is the underlying type of that one.
  let rec base (fuel : Nat) (t : Expr) : Expr := match fuel, t.constName?.bind st.newtypeOfDecl? with
    | k + 1, some m => base k m.under
    | _, _ => t
  for (_, n) in st.newtypes do
    let u := base st.newtypes.size n.under
    let under? := if u.isConstOf ``Int || u.isConstOf ``Nat then some "Int"
      else if u.isConstOf ``Bool then some "Bool"
      else if u.isConstOf ``String then some "String" else none
    if let some u := under? then out := out.insert (toString n.decl) u
    out := out.insert (toString n.ctor) Core.erasedSymbol
    out := out.insert (toString (n.ctor ++ Name.mkSimple "0")) Core.erasedSymbol
  return out

/-- Why a dump's script is missing where lean-smt showed no query and
threw nothing (`queryShown`). -/
def noQueryShown : String := "lean-smt showed no query"

/-- What `act` logs is dropped, and the script of the query that lean-smt
shows in it with `showQuery`, after its `query:`, is given, or the
error that it threw, as an `(error ...)` command. With `showQuery`,
lean-smt returns once it has shown the query, before it gives it to the
solver (`Smt.smt`), so nothing is asked. The messages logged before it are
kept even if `act` throws what `catch` does not catch, such as reaching a
heartbeat limit. -/
def queryShown (act : MetaM α) : MetaM (Option α × String) := do
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let (a?, failed?, logged) ← tryFinally
    (do
      let (a?, failed?) ← try pure (some (← act), none) catch ex => do
        pure (none, some (Core.errorScript (← ex.toMessageData.toString)))
      return (a?, failed?, (← getThe Core.State).messages))
    (modifyThe Core.State fun s => { s with messages := saved })
  -- The query that lean-smt showed, even if it threw after showing it.
  for m in logged.toList do
    let text ← m.data.toString
    if let some rest := (text.splitOn "query:\n")[1]? then return (a?, rest)
  -- Neither a query nor an error, as where preprocessing closes the goal
  -- before lean-smt shows the query: the dump shows that too.
  return (a?, failed?.getD (Core.errorScript noQueryShown))

/-- Values for `Bool` variables come back as `True`/`False`. -/
def fromModel (ty : Expr) (val : Expr) : Expr :=
  if ty.isConstOf ``Bool then
    if val.isConstOf ``True then mkConst ``Bool.true
    else if val.isConstOf ``False then mkConst ``Bool.false
    else val
  else val

/-- Restore the declared types of reconstructed model values and functions.
SMT propositions represent Bool values, and integers represent Nat values. -/
partial def modelValue (ty value : Expr) : MetaM Expr := do
  if let .forallE _ expectedDomain result _ := ty.consumeMData then
    if let .lam name modelDomain body _ := value.consumeMData then
      return ← withLocalDeclD name expectedDomain fun x => do
        -- lean-smt reconstructs Boolean domains as propositions. Restore
        -- the declared Bool binder and pass its truth proposition to the
        -- reconstructed body, just as codomains are restored below.
        let modelArgument := if expectedDomain.isConstOf ``Bool && modelDomain.isSort then
          mkApp2 (mkConst ``Eq [Level.zero]) (mkConst ``Bool) x |>.app (mkConst ``Bool.true)
          else x
        let mapped ← modelValue (result.instantiate1 x) (body.instantiate1 modelArgument)
        mkLambdaFVars #[x] mapped
  if ty.isConstOf ``Bool && (← isProp value) then
    let decision ← match ← trySynthInstance (mkApp (mkConst ``Decidable) value) with
      | .some found => pure found
      | _ => pure (mkApp (mkConst ``Classical.propDecidable) value)
    return mkApp2 (mkConst ``Decidable.decide) value decision
  if ty.isConstOf ``Nat then
    if let some i := intValue? value then
      if 0 ≤ i then return mkNatLit i.toNat
  return fromModel ty value

/-- The total SMT value of a partial source table/match is free at its
empty-sequence fallback, despite involving no declared uninterpreted function. -/
partial def hasUnspecifiedRead (formula : Expr) : MetaM Bool := do
  if formula.isAppOfArity ``Fren.Seq.nth 4 then
    if (← whnf formula.getAppArgs[2]!).isAppOfArity ``List.nil 1 then return true
  formula.foldlM (fun found child => if found then pure true else hasUnspecifiedRead child) false

/-- A model's value of type `ty`, as the Fren value that it stands for
(`Reqs/Models#reading`): a term of literals and constructors, with a
sequence as `Fren.Seq.ofList` and a set as `Fren.FinSet.ofList` of a list
literal, and a `Bool` or `Nat` as one. A part that it does not recognise is
kept as the solver's, so what `render` shows is always what `confirmModel`
evaluates. If `misread`, each integer is read as one more than it is: the
bug that `FREN_MISREAD_MODELS` injects (`Fren.Core.misreadModels`). -/
partial def readValue (misread : Bool) (ty val : Expr) : MetaM Expr := do
  -- A value of an abstract type, a local standing for it (`checkComp`).
  if ty.isFVar then return val
  let val := fromModel ty val
  let int (i : Int) : Int := if misread then i + 1 else i
  if ty.isConstOf ``Int then
    if let some i := intValue? val then return toExpr (int i)
  if ty.isConstOf ``Nat then
    if let some i := intValue? val then return mkNatLit (int i).toNat
  -- A pair, a member of a relation.
  if ty.isAppOfArity ``Prod 2 && val.isAppOfArity ``Prod.mk 4 then
    let (a, b) := (ty.appFn!.appArg!, ty.appArg!)
    return mkApp4 (.const ``Prod.mk [0, 0]) a b (← readValue misread a val.appFn!.appArg!)
      (← readValue misread b val.appArg!)
  let list (elem : Expr) (xs : Array Expr) : MetaM Expr := do
    mkListLit elem (← xs.mapM (readValue misread elem)).toList
  -- A sequence: the solver's concatenation of units.
  if ty.isAppOfArity ``Fren.Seq 1 then
    let rec elems (e : Expr) : Option (Array Expr) := match_expr e with
      | HAppend.hAppend _ _ _ _ a b => return (← elems a) ++ (← elems b)
      | Fren.Seq.unit _ x => some #[x]
      | EmptyCollection.emptyCollection _ _ => some #[]
      | Fren.Seq.ofList _ l => l.listLit?.map (·.2.toArray)
      | _ => none
    if let some xs := elems val then return mkApp2 (.const ``Fren.Seq.ofList [0]) ty.appArg! (← list ty.appArg! xs)
  -- A set: the solver's union of singletons.
  if ty.isAppOfArity ``Fren.FinSet 1 then
    let rec members (e : Expr) : Option (Array Expr) := match_expr e with
      | Union.union _ _ a b => return (← members a) ++ (← members b)
      | Singleton.singleton _ _ _ x => some #[x]
      | Insert.insert _ _ _ x s => return #[x] ++ (← members s)
      | EmptyCollection.emptyCollection _ _ => some #[]
      | Fren.FinSet.ofList _ l => l.listLit?.map (·.2.toArray)
      -- As reduction leaves a list's class.
      | Quot.mk _ _ l => l.listLit?.map (·.2.toArray)
      | _ => none
    if let some xs := members val then return mkApp2 (.const ``Fren.FinSet.ofList [0]) ty.appArg! (← list ty.appArg! xs)
  let st ← getState
  if let some n := st.newtypeOf? ty then
    if val.isAppOfArity n.ctor 1 then return mkApp val.appFn! (← readValue misread n.under val.appArg!)
  if let .const c _ := val.getAppFn then
    -- A generic type's constructor is applied to its type arguments first.
    let targs := ty.getAppArgs
    if let some e := st.enumOfDecl? c.getPrefix <|> st.enumOf? ty then
      if let some idx := e.ctorIdx? c then
        let tys := (e.payloadsAt targs)[idx]?.getD #[]
        let all := val.getAppArgs
        let args := all.extract e.params.size
        if args.size == tys.size then
          return mkAppN val.getAppFn ((all.extract 0 e.params.size) ++ (← (tys.zip args).mapM fun (t, a) => readValue misread t a))
    if let some r := st.recordOfDecl? c.getPrefix then
      let all := val.getAppArgs
      let args := all.extract r.params.size
      if c == r.ctor && args.size == r.fields.size then
        return mkAppN val.getAppFn ((all.extract 0 r.params.size)
          ++ (← ((r.fieldsAt targs).zip args).mapM fun ((_, t), a) => readValue misread t a))
  return val

/-- The default value of the type `ty` (`model::default_value`), as
the `fren` command's `Spec.defaultVal` gives it: `false`, `0`, `""`, `[]` and `{}`;
a newtype's underlying type's; and a record's, or an enumeration's first
variant whose payload has one, with the default values of its fields or
payload. An enumeration within its own payload, which `seen` holds, and an
abstract type have none. -/
partial def defaultValue (ty : Expr) (seen : List Name := []) : MetaM (Option Expr) := do
  if ty.isConstOf ``Bool then return some (mkConst ``Bool.false)
  if ty.isConstOf ``Int then return some (toExpr (0 : Int))
  if ty.isConstOf ``Nat then return some (mkNatLit 0)
  if ty.isConstOf ``String then return some (mkStrLit "")
  if ty.isAppOfArity ``Fren.Seq 1 then
    return some (mkApp2 (.const ``Fren.Seq.ofList [0]) ty.appArg! (← mkListLit ty.appArg! []))
  if ty.isAppOfArity ``Fren.FinSet 1 then
    return some (mkApp2 (.const ``Fren.FinSet.ofList [0]) ty.appArg! (← mkListLit ty.appArg! []))
  let st ← getState
  if let some n := st.newtypeOf? ty then
    return (← defaultValue n.under seen).map (mkApp (mkConst n.ctor))
  let targs := ty.getAppArgs
  if let some r := st.recordOf? ty then
    if seen.contains r.decl then return none
    let some fs ← (r.fieldsAt targs).mapM (defaultValue ·.2 (r.decl :: seen)) <&> (·.mapM id) | return none
    return some (mkAppN (mkConst r.ctor (← getLevels ty)) (targs ++ fs))
  if let some e := st.enumOf? ty then
    if seen.contains e.decl then return none
    for tys in e.payloadsAt targs, idx in [0:e.variants.size] do
      let some ps ← tys.mapM (defaultValue · (e.decl :: seen)) <&> (·.mapM id) | continue
      return some (mkAppN (e.ctorConst idx) (targs ++ ps))
  return none
where
  getLevels (ty : Expr) : MetaM (List Level) := return match ty.getAppFn with
    | .const _ ls => ls
    | _ => []

/-- Whether a failure in Lean with the message `msg` is a limit of Lean's,
its maximum recursion depth or heartbeats, reached: if `runtime` or the
message says so. -/
def limitReached (msg : String) (runtime : Bool) : Bool :=
  runtime || (msg.splitOn "maximum recursion depth").length > 1 ||
    (msg.splitOn "maximum number of heartbeats").length > 1

/-- What a failure in Lean of `what`, such as checking a procedure, with
the message `msg`, is reported as: a limit of Lean's, its maximum
recursion depth or heartbeats, reached, which the user may raise, if
`runtime` or the message says so; else an internal error, a bug in Fren. -/
def failureMsg (what msg : String) (runtime : Bool) : Core.Msg :=
  if limitReached msg runtime then
    { code? := none, headline := s!"{what} in Lean reached a limit: {msg}"
      notes := #["note: Lean stopped at one of its limits; raising it, with `set_option maxRecDepth` or `set_option maxHeartbeats` before `#fren_check`, may let the check finish"] }
  else Core.Msg.internal s!"{what} in Lean failed: {msg}"

/-- A sequence or a set that `render` cannot read: an internal error,
since the `fren` command would show its literal. -/
def unreadableValue (val : Expr) : MetaM String :=
  throwError "internal error: cannot show the value `{val}` as a literal; this is a bug in Fren"

/-- A value of type `ty` as Fren builds it (`Reqs/View`), such as
`Mode::Heat`, `Shape::Circle(2)`, `Point { x := 1, y := 2 }` or `Ms(5)`:
the Fren value that `readValue` reads (`Reqs/Models#reading`). -/
partial def render (ty : Expr) (val : Expr) : MetaM String := do
  show_ ty (← readValue (← Core.misreadModels) ty val)
where
  show_ (ty val : Expr) : MetaM String := do
  -- A value of an abstract type, a local standing for it (`checkComp`).
  if let .fvar id := ty then
    -- By the last segment of its sort's name, as the `fren` command has it
    -- (`renderAbstract?`): a generic function's type parameter is named by
    -- its whole path (`withNatUses`), and shown by its name.
    let sort := (← id.getUserName).getString!
    return s!"{(sort.splitOn "::").getLast?.getD sort}#{← ppExpr val}"
  if let .lit (.strVal s) := val then return s.quote
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then
    if let some i := intValue? val then return toString i
  -- A pair, a member of a relation.
  if ty.isAppOfArity ``Prod 2 && val.isAppOfArity ``Prod.mk 4 then
    return s!"({← show_ ty.appFn!.appArg! val.appFn!.appArg!}, {← show_ ty.appArg! val.appArg!})"
  -- A sequence, as a literal. One that is not written so is an internal
  -- error, never shown as another value nor as Lean shows it (`Reqs/View`).
  if ty.isAppOfArity ``Fren.Seq 1 then
    if val.isAppOfArity ``Fren.Seq.ofList 2 then
      if let some (_, xs) := val.appArg!.listLit? then
        let shown ← xs.toArray.mapM (show_ ty.appArg!)
        return "[" ++ ", ".intercalate shown.toList ++ "]"
    return ← unreadableValue val
  -- A set, as a literal, with its members sorted; likewise.
  if ty.isAppOfArity ``Fren.FinSet 1 then
    if val.isAppOfArity ``Fren.FinSet.ofList 2 then
      if let some (_, xs) := val.appArg!.listLit? then
        let shown ← xs.toArray.mapM (show_ ty.appArg!)
        return "{" ++ ", ".intercalate (shown.toList.eraseDups.mergeSort (· < ·)) ++ "}"
    return ← unreadableValue val
  let st ← getState
  -- A newtype, as Fren builds it: `Ms(5)`.
  if let some n := st.newtypeOf? ty then
    if val.isAppOfArity n.ctor 1 then return s!"{n.path.getString!}({← show_ n.under val.appArg!})"
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
      let vals ← (tys.zip args).mapM fun (t, a) => show_ t a
      return s!"{v}({", ".intercalate vals.toList})"
    if let some r := st.recordOfDecl? c.getPrefix then
      let args := val.getAppArgs.extract r.params.size
      if c == r.ctor && args.size == r.fields.size then
        let fs ← ((r.fieldsAt targs).zip args).mapM fun ((f, t), a) => return s!"{f} := {← show_ t a}"
        return s!"{r.path.getString!} \{ {", ".intercalate fs.toList} }"
  return toString (← ppExpr val)

/-- The compiled Lean evaluation path used by enumeration and model confirmation. -/
unsafe def compileValuesUnsafe (α : Type) [Inhabited α] (ty : Expr) (fs : Array Expr) : MetaM (Array α) := do
  if fs.isEmpty then return #[]
  let arr ← mkArrayLit ty fs.toList
  evalExpr (Array α) (mkApp (mkConst ``Array [0]) ty) arr

@[implemented_by compileValuesUnsafe]
opaque compileValues (α : Type) [Inhabited α] (ty : Expr) (fs : Array Expr) : MetaM (Array α)

/-- `e` with the definitions of defined functions unfolded, so that the
solver sees their bodies, and without `let`s and `have`s, which a record
update binds its updated value with, and `let` and `where` become
(`Reqs/Lang/Let#meaning`), and lean-smt does not translate: last, since a
defined function's body may have one. The last arm of a complete `match` is
its body (`Fren.lastArm`), unless `keepLastArm`, as a model's confirmation
reads it (`atModel`). -/
def unfoldDefined (e : Expr) (keepLastArm := false) (keepRelationObligations := false) : MetaM Expr := do
  let s ← getState
  -- A subset type's obligation is its proposition (`Fren.typeObligation`).
  let init := ({} : NameSet).insert ``Fren.typeObligation
  let init := if keepRelationObligations then init else init.insert ``Fren.relationObligation
  let ds := s.defined.foldl (init := init) fun acc _ d =>
    d.oblDecls.foldl (fun a (o, _) => a.insert o) (acc.insert d.decl)
  -- And the clauses of contracts, which the questions about applications
  -- and the facts about them apply.
  let ds := s.contracts.foldl (init := ds) fun acc _ k => (k.pres ++ k.posts).foldl (·.insert ·.decl) acc
  Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined s e ds.contains keepLastArm))

/-- Unfold definitions for evaluation while retaining strict arguments.
`lastArm` keeps an unused argument unknown where its value is unknown,
even after unfolding has erased its read from the function's body. Named
clauses are formulas, so their unused parameters impose no strict read. -/
def unfoldStrict (e : Expr) : MetaM Expr := do
  let s ← getState
  let definitions := s.defined.toArray.map (·.2)
  let clauses := s.contracts.foldl (init := ({} : NameSet)) fun acc _ k =>
    (k.pres ++ k.posts).foldl (fun acc p => acc.insert p.decl) acc
  let unfolded ← Meta.transform e (pre := fun x => do
    let .const c ls := x.getAppFn | return .continue
    let d? := definitions.find? fun d => d.decl == c || d.solver? == some c
    if d?.any (·.recursive) then return .continue
    let own := d?.isSome || clauses.contains c || c == ``Fren.typeObligation
      || definitions.any fun d => d.oblDecls.any (·.1 == c)
    unless own do return .continue
    let name := (d?.bind (·.solver?)).getD c
    let app := mkAppN (mkConst name ls) x.getAppArgs
    let some body ← Meta.delta? app (· == name) | return .continue
    let mut body := body
    if d?.isSome then
      for arg in x.getAppArgs do body ← mkAppM ``Fren.lastArm #[arg, body]
    return .visit body)
  Meta.zetaReduce (← Lean.Core.betaReduce unfolded)

/-- The procedure's variables, and the second copies of the copied ones,
each with its local and its value in `model`, as `readValue` reads it, or
its type's default value if the model leaves it free
(`Reqs/Models#free-values`); none for one that has neither. Misread if
`misread`, as only the reader of a model that a check reports is under
`FREN_MISREAD_MODELS` (`Reqs/Models#testing`). -/
def modelValues (c : CompInfo) (fvs primes : Array Expr) (model : Array (Name × Expr)) (misread : Bool := false) :
    MetaM (Array (Expr × Option Expr)) := do
  let copied := c.vars.zip fvs |>.filter fun (v, _) => (Core.Symbol.ofRole v.role).copied
  let vars := c.vars.zip fvs ++ (copied.zip primes).map fun ((v, _), p) =>
    ({ v with name := Core.primed v.name }, p)
  vars.mapM fun (v, x) => do
    match model.find? (·.1 == v.name) with
    | some (_, val) => return (x, some (← readValue misread v.type val))
    -- Only the procedure's own variables without a definition are free: a
    -- defined one's, or a call's, value follows from the others.
    | none => if v.name.isAtomic && v.defn?.isNone then return (x, ← defaultValue v.type) else return (x, none)

/-- `e` with each decision that its definitions got classically, as a
generic function's body gets one for its type parameter
(`Reqs/Lang/GenericFunctions#meaning`), replaced by the instance that Lean
finds for it, where it finds one that is not classical: at an instance of
a generic function, unfolded, `Classical.propDecidable (a = b)` over the
values of an enumeration is its own `DecidableEq`, which enumeration can
compile. -/
def computableDecisions (e : Expr) : MetaM Expr :=
  if (e.find? (·.isConstOf ``Classical.propDecidable)).isNone then pure e else
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``Classical.propDecidable 1 then
      let p := x.appArg!
      if !p.hasLooseBVars then
        if let some inst ← (try Meta.synthInstance? (mkApp (mkConst ``Decidable) p) catch _ => pure none) then
          if (inst.find? (·.isConstOf ``Classical.propDecidable)).isNone then return .done inst
    return .continue)

/-- An instance of a structural recursion: its solver form, and the type
arguments and `Inhabited` instances that it takes first, none but for a
generic one's (`DefinedInfo.solverTypeArgs`). Two are the same instance when
their type arguments are, whatever terms give their instances, as
`instancesIn` decides. -/
abbrev RecInstance := Name × Array Expr

/-- Whether `a` and `b` are the same instance (`RecInstance`). -/
def RecInstance.same (a b : RecInstance) : Bool :=
  a.1 == b.1 && a.2.size == b.2.size && (List.range (a.2.size / 2)).all fun i => a.2[2 * i]! == b.2[2 * i]!

/-- Of the application `e` of the solver form `c` of a structural recursion
that takes `m` type arguments and instances first: its instance, and its
other arguments. -/
def recInstanceOf (c : Name) (m : Nat) (e : Expr) : RecInstance × Array Expr :=
  let args := e.getAppArgs
  ((c, args.extract 0 m), args.extract m)

/-- `e`, of the generic structural recursion `d`, at the instance whose type
arguments and `Inhabited` instances are `pre` (`atInstance`): itself, of a
function that is not generic. -/
def DefinedInfo.atRecInstance (d : DefinedInfo) (pre : Array Expr) (e : Expr) : Expr :=
  if pre.isEmpty then e else atInstance d.path d.typeParams pre e

mutual
/-- `e` with each application of a generic structural recursion, of its
definition or its solver form, at an instance whose type arguments mention
no local, an application of a structural recursion of its own at that
instance (`specializedRecursion`), which Lean can compile: the generic one
decides the equality of its type parameters' values classically, which has
no code, and the instance's decides it with the type argument's own
instance, as `computableDecisions` replaces it. Enumeration and the
confirmation of a model evaluate these (`Reqs/Lang/Recursion#generic-recursion`).
An application that cannot be specialized is left as it is. -/
partial def specializeRecursions (e : Expr) : MetaM Expr := do
  let gens := (← getState).defined.toArray.filterMap fun (_, d) =>
    if d.recursive && d.recValue?.isSome && d.uses.size == d.solverTypeArgs.size then some d else none
  if gens.isEmpty then return e
  if (e.find? fun x => gens.any fun d => x.isConstOf d.decl || d.solver?.any x.isConstOf).isNone then return e
  Meta.transform e (post := fun t => do
    let .const c _ := t.getAppFn | return .continue
    let some d := gens.find? fun d => d.decl == c || d.solver? == some c | return .continue
    let args := t.getAppArgs
    let m := d.solverTypeArgs.size
    if args.size < m then return .continue
    -- The definition takes its placeholders, which are its type parameters'
    -- here, in the order of the solver form's.
    let pre := if c == d.decl then d.solverTypeArgs.map (args[·]!) else args.extract 0 m
    if pre.any (fun x => x.hasFVar || x.hasMVar) then return .continue
    match ← specializedRecursion d pre with
    | some n => return .done (mkAppN (mkConst n) (args.extract m))
    | none => return .continue)

/-- The structural recursion of its own of the generic one `d` at the
instance whose type arguments and `Inhabited` instances are `pre`
(`specializeRecursions`): its name, once added, or none if Lean does not
accept it. The name is the instance's own, so that an existing declaration
of it is this instance, never another's. -/
partial def specializedRecursion (d : DefinedInfo) (pre : Array Expr) : MetaM (Option Name) := do
  -- Named after the type arguments and instances themselves, written out
  -- whole, so that two instances never share a name.
  let name := d.decl.str s!"#at{pre.toList.map toString}"
  if (← getEnv).contains name then return some name
  let some v := d.recValue? | return none
  try
    let selfApp := mkAppN (mkConst d.decl) (d.uses.map mkConst)
    let type ← inferType (d.atRecInstance pre selfApp)
    withLocalDeclD `self type fun self => do
      let body := d.atRecInstance pre (v.replace fun t => if t == selfApp then some self else none)
      let body ← specializeRecursions (← computableDecisions body)
      let body := body.replaceFVar self (mkConst name)
      let preDef : Lean.Elab.PreDefinition :=
        { ref := .missing, kind := .def, levelParams := [], modifiers := {}, declName := name, binders := .missing
          type, value := body, termination := .none }
      (Lean.Elab.addPreDefinitions ({}, {}) #[preDef] : Lean.Elab.TermElabM Unit).run'
      return some name
  catch _ => return none
end

/-- The types that `actual`, a model value's type, has where `declared`, its
variable's, has a local that is a type, added to `acc`, each once: what
lean-smt reads a sort of a type parameter as. -/
partial def matchSorts (declared actual : Expr) (acc : Array (FVarId × Expr)) : Array (FVarId × Expr) :=
  if declared.isFVar then
    if acc.any (·.1 == declared.fvarId!) || actual.hasFVar then acc else acc.push (declared.fvarId!, actual)
  else if declared.isApp && actual.isApp && declared.getAppNumArgs == actual.getAppNumArgs then
    (declared.getAppArgs.zip actual.getAppArgs).foldl (fun acc (d, a) => matchSorts d a acc) acc
  else acc

/-- Whether `e` is an index, which may be out of range, or a quotient or
remainder by other than a nonzero numeral: an operation whose value in
Lean's definitions differs from Fren's where Fren's semantics gives none,
and the solver's interpretation does
(`Reqs/Models#how-the-front-ends-evaluate`). The elaborator writes `div`
and `mod` only by a nonzero numeral (`divTerm`).

A generated selector of a payload is total in the same way, by a
`| _ => default` arm (`Reqs/Generated`), and is deliberately not here: a
read of a payload is evaluated only where the model's value has the
variant that a `match` arm or a pattern test matched, since every such read
is under that test's `ite`, which Lean does not evaluate on the branch not
taken; and a `match` that may take no arm reads the empty sequence, which
is an index. -/
def partialOp (e : Expr) : Bool :=
  e.isAppOfArity ``Fren.Seq.nth 4 ||
    (e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``HMod.hMod 6) && !(Enumerate.countLit? e.appArg!).any (· != 0)

/-- Whether a part of `e` is `found`, directly unless `within`, or within the
definitions of the spec's functions and clauses that it applies, and their
auxiliary definitions, such as their `match`es. With `propositions`, only
propositions match: a function type may have a quantifier's syntax too. -/
partial def readsWhere (found : Expr → Bool) (e : Expr) (within := false) (propositions := false) : MetaM Bool := do
  let s ← getState
  let own := s.defined.foldl (init := #[``Fren.typeObligation]) fun acc _ d => acc.push d.decl ++ d.oblDecls.map (·.1)
  let own := s.contracts.foldl (init := own) fun acc _ k => acc ++ (k.pres ++ k.posts).map (·.decl)
  let rec go (e : Expr) (direct : Bool) (seen : NameSet) : MetaM (Bool × NameSet) := do
    if direct && (e.find? found).isSome then
      if !propositions then return (true, seen)
      let hit ← IO.mkRef false
      let _ ← Meta.transform e (pre := fun x => do
        if found x && (← isProp x) then hit.set true
        return .continue)
      if ← hit.get then return (true, seen)
    let mut seen := seen
    for c in e.getUsedConstants do
      if seen.contains c || !own.any (·.isPrefixOf c) then continue
      seen := seen.insert c
      let some v := (← getEnv).find? c |>.bind (·.value?) | continue
      let (r, seen') ← go v true seen
      if r then return (true, seen')
      seen := seen'
    return (false, seen)
  return (← go e (!within) {}).1

/-- Whether `e` applies one of `targets`, directly or within the
functions and clauses that it applies. -/
def readsAny (targets : Array Name) (e : Expr) : MetaM Bool :=
  readsWhere (fun x => x.constName?.any targets.contains) e

/-- The type of each value of a sort, of an abstract type or a type
parameter, within `val`, a value of the type `ty` as `readValue` reads it,
with the sort's local, added to `acc`, each sort once: what lean-smt reads
the sort as, a `Fin n`. -/
partial def valueSorts (ty val : Expr) (acc : Array (FVarId × Expr)) : MetaM (Array (FVarId × Expr)) := do
  if ty.isFVar then
    if acc.any (·.1 == ty.fvarId!) then return acc
    let actual ← instantiateMVars (← inferType val)
    return if actual.hasFVar then acc else acc.push (ty.fvarId!, actual)
  if !ty.hasFVar then return acc
  if ty.isAppOfArity ``Prod 2 && val.isAppOfArity ``Prod.mk 4 then
    return ← valueSorts ty.appArg! val.appArg! (← valueSorts ty.appFn!.appArg! val.appFn!.appArg! acc)
  if (ty.isAppOfArity ``Fren.Seq 1 && val.isAppOfArity ``Fren.Seq.ofList 2)
      || (ty.isAppOfArity ``Fren.FinSet 1 && val.isAppOfArity ``Fren.FinSet.ofList 2) then
    let some (_, xs) := val.appArg!.listLit? | return acc
    return ← xs.foldlM (fun acc x => valueSorts ty.appArg! x acc) acc
  let st ← getState
  let .const c _ := val.getAppFn | return acc
  let targs := ty.getAppArgs
  if let some e := st.enumOfDecl? c.getPrefix <|> st.enumOf? ty then
    if let some idx := e.ctorIdx? c then
      let tys := (e.payloadsAt targs)[idx]?.getD #[]
      let args := val.getAppArgs.extract e.params.size
      if args.size == tys.size then
        return ← (tys.zip args).foldlM (fun acc (t, a) => valueSorts t a acc) acc
  if let some r := st.recordOfDecl? c.getPrefix then
    let args := val.getAppArgs.extract r.params.size
    if c == r.ctor && args.size == r.fields.size then
      return ← ((r.fieldsAt targs).zip args).foldlM (fun acc ((_, t), a) => valueSorts t a acc) acc
  return acc

/-- The types that lean-smt reads the sorts of the types of `values`'
variables as (a `Fin n`), where a value's type, or a part of the value,
shows one (`matchSorts`, `valueSorts`):
the sorts of the abstract types and of a generic function's type
parameters, which are locals of the check (`withNatUses`). -/
def sortTypes (values : Array (Expr × Option Expr)) : MetaM (Array (FVarId × Expr)) := do
  let mut sortTys : Array (FVarId × Expr) := #[]
  for (x, v?) in values do
    let some v := v? | continue
    sortTys := matchSorts (← instantiateMVars (← inferType x)) (← instantiateMVars (← inferType v)) sortTys
    -- And within the value, whose type `readValue` writes at the declared
    -- types, a sort's local, as of a sequence's elements.
    sortTys ← valueSorts (← instantiateMVars (← inferType x)) v sortTys
  return sortTys

/-- `e` with each local that is a sort, of an abstract type or a type
parameter, at the type that `sortTys` gives it (`sortTypes`), or else
`Nat`, and each local `Inhabited` instance of one with that type's. -/
def atSorts (sortTys : Array (FVarId × Expr)) (e : Expr) : MetaM Expr := do
  let xs := (collectFVars {} e).fvarIds
  let mut sorts : Array FVarId := #[]
  for x in xs do
    if (← instantiateMVars (← x.getType)).isSort then sorts := sorts.push x
  if sorts.isEmpty then return e
  let tyOf (x : FVarId) : Expr := ((sortTys.find? (·.1 == x)).map (·.2)).getD (mkConst ``Nat)
  let mut from_ : Array Expr := sorts.map .fvar
  let mut to : Array Expr := sorts.map tyOf
  for x in xs do
    let t ← instantiateMVars (← x.getType)
    if t.isAppOfArity ``Inhabited 1 && (t.getArg! 0).isFVar && sorts.contains (t.getArg! 0).fvarId! then
      from_ := from_.push (.fvar x)
      to := to.push (← synthInstance (mkApp (mkConst ``Inhabited [1]) (tyOf (t.getArg! 0).fvarId!)))
  return e.replaceFVars from_ to

/-- Whether `x` may retain an unused unbounded binder, or quantify over a
type that mentions one of `tys`, the types that `atSorts` gives the sorts:
Lean would decide it over the model's values of the sort alone, which
Fren's semantics does not. The caller also checks that `x` is a
proposition, since a function type is also a `forallE`
(`Reqs/Models#how-the-front-ends-evaluate`). -/
def quantifiesOver (tys : Array Expr) (x : Expr) : Bool :=
  if x.isAppOfArity ``Fren.unusedQuantifier 2 then true else
  let mentions (t : Expr) := tys.any fun ty => (t.find? (fun part => part.consumeMData == ty.consumeMData)).isSome
  match x with
  -- Not an implication, whose body never reads its hypothesis's proof.
  | .forallE _ t b _ =>
    (b.hasLooseBVar 0 || tys.any (fun ty => t.consumeMData == ty.consumeMData)) && mentions t
  | _ => x.isAppOfArity ``Exists 2 && mentions x.appFn!.appArg!

-- Source annotations do not turn a vacuous quantifier into an implication.
#guard quantifiesOver #[.mdata {} (mkConst ``Nat)]
  (.forallE `unused (mkConst ``Nat) (mkConst ``True) .default)

#guard quantifiesOver #[mkConst ``Nat]
  (mkApp2 (mkConst ``Fren.unusedQuantifier) (mkConst ``Nat) (mkConst ``True))

/-- A quantifier over a model's sort is unknown, rather than decided over
its finite stand-in. Encode just that operand as an unspecified Boolean,
so the known-value rules may still decide the surrounding formula. -/
def unknownQuantifiers (tys : Array Expr) (e : Expr) : MetaM Expr := do
  if (e.find? (quantifiesOver tys)).isNone then return e
  let bool := mkConst ``Bool
  let empty ← mkAppOptM ``EmptyCollection.emptyCollection #[some (mkApp (mkConst ``Fren.Seq [0]) bool), none]
  let unknown := mkApp4 (mkConst ``Fren.Seq.nth [0]) bool (mkConst ``instInhabitedBool) empty (mkIntLit 0)
  let prop ← mkEq unknown (mkConst ``Bool.true)
  Meta.transform e (pre := fun x => do
    -- A function type is also a `forallE`, but is not a proposition.
    if quantifiesOver tys x && (← isProp x) then return .done prop
    return .continue)

/-- `e` at the values `values` (`modelValues`), as confirmation evaluates
it (`Reqs/Models#confirmation`): each variable without a value read as
unknown, an index of the empty sequence (`Enumerate.isUnspecified`), as the
`fren` command's evaluator reads a variable that its environment lacks, and
each sort, of an abstract type or a type parameter, at the type that the
model's values give it (`atSorts`); if it then has no local, such as an
uninterpreted function's: as it applies the defined functions and clauses,
and with them unfolded, retaining strict arguments (`unfoldStrict`), with
each decision that Lean finds an instance for computable, and each generic
structural recursion at its instance, as enumeration has them
(`computableDecisions`, `specializeRecursions`), each with each index, an
unspecified value too, read as `Enum.nthOr`, which `decideAll` leaves
unknown out of range (`Enumerate.knownOf`), as the `fren` command's
evaluator does. A quantifier over a sort is an unknown operand
(`unknownQuantifiers`); none if one remains hidden within a recursion, or
if a `partialOp` remains within a definition that is not unfolded; one that
still applies a structural recursion's solver form after specialization,
which is not compiled, is `e` itself, and none if it has a `partialOp`
at all, an unknown variable too. Specialized recursions take the general
path, whose known-value rules can decide a formula beside an unknown. -/
def atModel (values : Array (Expr × Option Expr)) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let sortTys ← sortTypes values
  let mut standIns := #[]
  let mut sourceVars := collectFVars {} e
  for (x, _) in values do sourceVars := collectFVars sourceVars (← instantiateMVars (← inferType x))
  for x in sourceVars.fvarIds do
    if (← instantiateMVars (← x.getType)).isSort then
      standIns := standIns.push (((sortTys.find? (·.1 == x)).map (·.2)).getD (mkConst ``Nat))
  let given := values.filterMap fun (x, v?) => v?.map (x, ·)
  -- A variable without a value, unknown: at its type at the sorts, which
  -- must have an `Inhabited` instance, as every type that a sequence's
  -- elements may have does, or else it stays, and `e` is not evaluated.
  let unknowns ← values.filterMapM fun (x, v?) => do
    if v?.isSome then return none
    try
      let ty ← atSorts sortTys (← instantiateMVars (← inferType x))
      let inst ← synthInstance (mkApp (mkConst ``Inhabited [1]) ty)
      let empty ← mkAppOptM ``EmptyCollection.emptyCollection #[some (mkApp (mkConst ``Fren.Seq [0]) ty), none]
      return some (x, mkApp4 (mkConst ``Fren.Seq.nth [0]) ty inst empty (← mkNumeral (mkConst ``Int) 0))
    catch _ => return none
  let given := given ++ unknowns
  -- Without `let`s, which bind lazily, as `lang::eval`'s do: a definition
  -- that the body never reads is not evaluated.
  let some e ← try some <$> atSorts sortTys (← Meta.zetaReduce (e.replaceFVars (given.map (·.1)) (given.map (·.2))))
    catch _ => pure none | return none
  if e.hasFVar || e.hasMVar then return none
  let prepare (p : Expr) := do
    specializeRecursions (← computableDecisions (← unknownQuantifiers standIns p))
  let unfolded ← prepare (← unfoldDefined e (keepLastArm := true))
  -- Without a sort or an erased binder, the original application already
  -- preserves strict reads. Avoid unfolding it a second time in that case.
  let needsStrict ← if standIns.isEmpty then readsWhere (·.isAppOfArity ``Fren.unusedQuantifier 2) e else pure true
  let applied ← prepare (← if needsStrict then unfoldStrict e else pure e)
  -- A quantifier still hidden in a recursion cannot be replaced here.
  if needsStrict && (← readsWhere (quantifiesOver standIns) unfolded (propositions := true)) then return none
  let recursive := (← getState).defined.foldl (init := #[]) fun acc _ d =>
    if d.recursive then acc ++ d.solver?.toArray else acc
  if (unfolded.find? fun x => x.constName?.any recursive.contains).isSome then
    if ← readsWhere partialOp applied then return none
    return some (e, e)
  if (unfolded.find? fun x => partialOp x && !x.isAppOf ``Fren.Seq.nth).isSome then return none
  if ← readsWhere partialOp unfolded (within := true) then return none
  let read (e : Expr) : MetaM Expr := return (← Enumerate.readIndexes e (unspecified := true)).1
  return some (← read applied, ← read unfolded)

/-- The truth of each proposition of `ps` that has one, as `atModel` gives
it, applied and unfolded: by the compiled evaluation of the unfolded one's
decision, unknown where either reads an index out of range
(`Enumerate.knownOf`), the applied one in an argument that a body does not
read, since evaluation is strict, as the `fren` command's is; none for one
that cannot be decided. -/
def decideAll (ps : Array (Option (Expr × Expr))) : MetaM (Array (Option Bool)) := do
  let decideOf (p : Expr) : MetaM Expr := return mkApp2 (mkConst ``Decidable.decide) p (← Enumerate.decidableOf p)
  let optBool := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
  let decision (applied p : Expr) : MetaM Expr := do
    let v ← mkAppOptM ``Option.some #[mkConst ``Bool, ← decideOf p]
    let known ← #[applied, p].filterMapM fun e => do
      if Enumerate.hasIndex e then some <$> Enumerate.knownOf decideOf e else pure none
    if known.isEmpty then return v
    mkAppM ``cond #[known.foldl (mkApp2 (mkConst ``and)) (mkConst ``Bool.true), v,
      ← mkAppOptM ``Option.none #[mkConst ``Bool]]
  let ds ← ps.mapM fun p? => do
    let some (applied, p) := p? | return none
    try some <$> decision applied p catch _ => return none
  let known := ds.filterMap id
  -- All at once, and one at a time where that fails.
  let values ← try pure (some (← compileValues (Option Bool) optBool known)) catch _ => pure none
  let mut k := 0
  let mut out := #[]
  for d? in ds do
    match d? with
    | none => out := out.push none
    | some d =>
      match values with
      | some vs => out := out.push (vs[k]?.join)
      | none => out := out.push (← try pure ((← compileValues (Option Bool) optBool #[d])[0]?.join) catch _ => pure none)
      k := k + 1
  return out

/-- What `model`, a counterexample or witness of the query of `hyps` and
`goal`, contradicts in Fren's semantics, which the generated definitions
compute, at the values that `render` shows (`Reqs/Models#confirmation`): the
first hypothesis that is false there, or the goal, if it is true; none if
neither, or if Lean cannot evaluate them. -/
def confirmModel (c : CompInfo) (fvs primes : Array Expr) (hyps : Array (Name × Expr)) (goal : Expr)
    (model : Array (Name × Expr)) : MetaM (Option Core.Contradiction) := do
  let values ← modelValues c fvs primes model (← Core.misreadModels)
  let truths ← decideAll ((← hyps.mapM (atModel values ·.2)).push (← atModel values goal))
  return Core.contradiction? (hyps.zipWith (fun (n, _) t => (n, t)) truths) truths.back?.join

/-- Whether `model` is contradicted in a formula that applies none of the
recursive functions `recs`: a bug in Fren, which the report of the model
shows (`Reqs/Models#reporting`), not evidence about the functions'
contracts (`Reqs/Lang/Recursion`). Read without the injected misread, as
the recursive confirmation is. -/
def plainContradiction (c : CompInfo) (fvs primes : Array Expr) (hyps : Array (Name × Expr)) (goal : Expr)
    (model : Array (Name × Expr)) (recs : Array Name) : MetaM Bool := do
  let values ← modelValues c fvs primes model
  let formulas := (hyps.map (·.2)).push goal
  let recursive ← formulas.mapM (readsAny recs ·)
  -- A formula that applies a recursive function is not evaluated here.
  let truths ← decideAll (← (formulas.zip recursive).mapM fun (e, r) => if r then pure none else atModel values e)
  let atK (k : Nat) : Option Bool × Bool := ((truths[k]?).join, recursive[k]?.getD false)
  return Core.plainContradiction (hyps.mapIdx fun k (n, _) => (n, atK k)) (atK hyps.size)

/-- Evaluate a model using real definitions, before reporting a recursive
counterexample: the value of each of `hyps` at it, and then the goal's
negation's, or none where evaluation fails, which is not confirmation
(`Core.counterexampleReported`). -/
def confirmRecursiveModel (c : CompInfo) (fvs primes : Array Expr)
    (hyps : Array (Name × Expr)) (goal : Expr) (model : Array (Name × Expr)) : MetaM (Option (Array Bool)) := do
  try
    let read ← modelValues c fvs primes model
    -- A missing value is unknown here too, never an arbitrary default.
    -- The same evaluation confirms ordinary and recursive models.
    let ps := (hyps.map (·.2)).push (mkNot goal)
    return (← decideAll (← ps.mapM (atModel read))).mapM id
  catch _ => return none

/-- The structural recursions in the state, each by its solver form. -/
def recursiveInfos : MetaM (Array (Name × DefinedInfo)) := do
  return (← getState).defined.toArray.filterMap fun (_, d) => if d.recursive then d.solver?.map (·, d) else none

/-- The instances (`RecInstance`) of the structural recursions `recs` that
`e` applies, each once, added to `acc`: a generic one's, by its
applications' type arguments, which mention no bound variable. Each
subterm is visited once, however often `e` shares it, as `foldConsts`
visits it: a formula unfolded from definitions shares its subterms, and
visiting each once for each path to it took exponentially many steps,
such as nearly all of a query's heartbeats in `lint::chainable_comparison`. -/
partial def recInstancesIn (recs : Array (Name × DefinedInfo)) (e : Expr) (acc : Array RecInstance) : Array RecInstance :=
  ((go e).run ({}, acc)).2.2
where
  add (i : RecInstance) : StateM (Std.HashSet Expr × Array RecInstance) Unit :=
    modify fun (seen, acc) => (seen, if acc.any i.same then acc else acc.push i)
  go (e : Expr) : StateM (Std.HashSet Expr × Array RecInstance) Unit := do
    match e with
    | .const c _ => if recs.any (fun (r, d) => r == c && d.solverTypeArgs.isEmpty) then add (c, #[])
    | .app .. | .lam .. | .forallE .. | .letE .. | .mdata .. | .proj .. =>
      if (← get).1.contains e then return
      modify fun (seen, acc) => (seen.insert e, acc)
      match e with
      | .app .. =>
        let args := e.getAppArgs
        match e.getAppFn with
        | .const c _ =>
          if let some (_, d) := recs.find? (·.1 == c) then
            let m := d.solverTypeArgs.size
            if m == 0 then add (c, #[])
            else if args.size ≥ m && !(args.extract 0 m).any (·.hasLooseBVars) then add (recInstanceOf c m e).1
        | f => go f
        args.forM go
      | .lam _ d b _ | .forallE _ d b _ => go d; go b
      | .letE _ t v b _ => go t; go v; go b
      | .mdata _ b | .proj _ _ b => go b
      | _ => pure ()
    | _ => pure ()

/-- `r x` within `n` conjunctions of a term with itself, shared: `2 ^ n`
paths to it, but `n + 1` subterms. -/
private def sharedConjunctions : Nat → Expr
  | 0 => mkApp (mkConst `r) (mkConst `x)
  | n + 1 => let e := sharedConjunctions n; mkApp2 (mkConst ``And) e e

-- A traversal that visited `r x` once for each path to it would never end.
#guard (recInstancesIn #[(`r, { path := `r, decl := `r, uses := #[], nParams := 1, recursive := true })]
  (sharedConjunctions 64) #[]).map (·.1) == #[`r]

/-- The recursive symbols a query uses, including dependencies needed by
its defining equations, each at the instances that it applies, the
dependencies of a generic one's at the instance
(`Reqs/Lang/Recursion#generic-recursion`). Each becomes an uninterpreted
local. -/
def recursiveSolvers (es : Array Expr) : MetaM (Array RecInstance) := do
  let recs ← recursiveInfos
  if recs.isEmpty then return #[]
  let mut work := es.foldl (fun acc e => recInstancesIn recs e acc) #[]
  let mut out : Array RecInstance := #[]
  -- Each is visited once, and an instance's body applies only itself and
  -- the instances of functions declared before it, so this ends.
  while !work.isEmpty do
    let some i := work.back? | break
    work := work.pop
    if out.any i.same then continue
    out := out.push i
    if let some (_, d) := recs.find? (·.1 == i.1) then
      if let some b := d.recBody? then
        work := recInstancesIn recs (d.atRecInstance i.2 b) work
  return out

/-- The answers to a procedure's queries so far, by hypotheses, goal and
whether a model was wanted: some checks of a procedure ask the same
query, which is answered once, as in the binary (`Reqs/Cli#solver-queries`). -/
abbrev QueryCache := IO.Ref (Std.HashMap (Array Expr × Expr × Bool) (Core.Outcome Expr × Array Name))

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

/-- Recursive symbols are local uninterpreted functions, one for each
instance that a query applies (`RecInstance`). A result in Nat uses an Int
symbol with ground range facts, as other opaque functions do. -/
partial def withRecursiveDefs {α : Type} [Inhabited α] (recs : Array RecInstance)
    (k : Array Expr → (Expr → Expr) → MetaM α) : MetaM α := go 0 #[] #[]
where
  go (i : Nat) (fs reps : Array Expr) : MetaM α := do
    if h : i < recs.size then
      let (c, pre) := recs[i]
      let ty ← instantiateForall (← getConstInfo c).type pre
      let nat := (resultType ty).isConstOf ``Nat
      -- Named by the function's whole path, as the `fren` command names its
      -- symbol (`Core.ItemSymbol.item`), so that two functions of one name in
      -- two modules are apart, and apart from every variable; an instance at
      -- type arguments by its position among them too.
      let path? := (← getState).defined.foldl (init := none) fun acc _ d =>
        acc <|> if d.recursive && d.solver? == some c then some d.path else none
      let base := match path? with
        | some p => (Core.ItemSymbol.item p).text
        | none => c.getPrefix.getString!
      let name := if pre.isEmpty then Name.mkSimple base else Name.mkSimple s!"{base}<{i}>"
      withLocalDeclD name (if nat then intResult ty else ty) fun f => do
        let rep ← if !nat then pure f else Meta.forallTelescope ty (fun xs _ => mkLambdaFVars xs (mkApp (mkConst ``Fren.natResult) (mkAppN f xs)))
        go (i + 1) (fs.push f) (reps.push rep)
    else k fs (sub reps)
  sub (reps : Array Expr) (e : Expr) : Expr :=
    e.replace fun t => match t.getAppFn with
      | .const c _ => do
        let args := t.getAppArgs
        let j ← recs.findIdx? fun (r, pre) => r == c && args.size ≥ pre.size && RecInstance.same (r, pre) (c, args.extract 0 pre.size)
        return mkAppN reps[j]! ((args.extract recs[j]!.2.size).map (sub reps))
      | _ => none

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

/-- Ground equations and contract facts for recursive applications. The queue
keeps each application's depth, how many equations away from the query it
is, through contracts, and an application brings an equation only where its
depth is less than `unfoldings` (`Core.recursiveFacts`). `allowPosts` lets
induction proofs require evidence for a self-contract before using or
expanding it. -/
partial def recursiveQueryFacts (hyps : Array (Name × Expr)) (goal : Expr)
    (allowPosts : DefinedInfo → Expr → Array Expr → MetaM Bool := fun _ _ _ => pure true)
    (unfoldings : Nat := 1) : MetaM (Array (Name × Expr)) := do
  let st ← getState
  let recs := st.defined.toArray.filterMap fun (_, d) =>
    if d.recursive then d.solver?.map (·, d) else none
  -- Membership is checked at every subterm below. Index the symbols once,
  -- so unrelated recursive definitions do not multiply the walk's cost.
  let recs := recs.foldl (init := ({} : NameMap DefinedInfo)) fun acc (n, d) =>
    if acc.contains n then acc else acc.insert n d
  if recs.isEmpty then return #[]
  let mut work := #[]
  for f in hyps.map (·.2) |>.push goal do
    work := work ++ (← scan recs f #[] 0 #[])
  let mut out := #[]
  let mut seen : Array (Expr × Array Expr × Nat) := #[]
  let mut done := 0
  while done < work.size do
    let (app, gs, depth, ancestors) := work[done]!
    done := done + 1
    let key := (app, gs, depth)
    if seen.contains key || ancestors.contains app then continue
    seen := seen.push key
    let .const c _ := app.getAppFn | continue
    let some d := recs.get? c | continue
    let ancestors := ancestors.push app
    -- A generic one's at the instance that the application applies, its
    -- type arguments first (`Reqs/Lang/Recursion#generic-recursion`).
    let ((_, pre), args) := recInstanceOf c d.solverTypeArgs.size app
    let atI := d.atRecInstance pre
    if d.result == .nat then out := out.push ((`nat, ← atLeast0 app), gs)
    -- Newly reflected type facts need the same solver forms as explicit
    -- clauses: their subset helpers may have executable Lean matches.
    -- An application that `scan` found has nothing bound, so only the
    -- declared result type decides (`Core.recursiveResultFact`): whether
    -- it has a fact is the shared decision's input, which the binary
    -- extracts from the declared type too, and the fact itself is read
    -- after it.
    if Core.recursiveResultFact d.fact?.isSome then
      if let some fact := d.fact? then
        let value := if d.result == .nat then
          mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) app else app
        out := out.push ((`type, ← unfoldDefined ((atI fact).beta #[value])), gs)
    let k := st.contracts.get? d.path
    let domain := ((st.bodies.get? d.path).map fun b => (b.vars.zip args).filterMap fun (v, x) => v.fact?.map fun f => (atI f).beta #[x]).getD #[]
    let pres ← ((k.map (·.pres)).getD #[]).mapM fun c => unfoldDefined (atI (c.at args))
    let pres := (← domain.mapM unfoldDefined) ++ pres
    let posts ← ((k.map (·.posts)).getD #[]).mapM fun c => return (c.name, ← unfoldDefined (atI (c.at args)))
    let implies (ps : Array Expr) (q : Expr) := ps.foldr (fun p b => mkForall `h .default p b) q
    for (name, f) in (if ← allowPosts d app gs then Core.postconditionFacts implies pres posts else #[]) do
      out := out.push ((name, f), gs)
      work := work ++ (← scan recs f gs depth ancestors)
    if (Core.recursiveFacts depth (unfoldings := unfoldings)).2 then
      if let some body := d.recBody? then
        let body ← unfoldDefined ((atI body).beta args)
        out := out.push ((`equation, ← mkEq app body), gs)
        work := work ++ (← scan recs body gs (depth + 1) ancestors)
  -- Each fact once, where it is first found, under its weakest paths, as
  -- the binary asserts it.
  let implies (gs : Array Expr) (f : Expr) := gs.foldr (fun g b => mkForall `h .default g b) f
  -- A linear tree of many guard paths reaches Lean's recursion limit
  -- before the solver sees the facts; keep their connective depth small.
  let conj (gs : Array Expr) := if gs.isEmpty then mkConst ``True else balanced mkAnd gs
  let disj (ps : List (Array Expr)) :=
    if ps.isEmpty then mkConst ``False else balanced mkOr (ps.toArray.map conj)
  return (Core.mergeGuarded Core.guardsWithin out.toList).toArray.map fun ((n, f), ps) =>
    (n, Core.guardedFact implies disj f ps)
where
  scan (recs : NameMap DefinedInfo) (e : Expr) (gs : Array Expr)
      (depth : Nat) (ancestors : Array Expr) : MetaM (Array (Expr × Array Expr × Nat × Array Expr)) := do
    -- A formula without a recursive symbol has no application to find:
    -- `find?` visits each shared subterm once, where the descent below
    -- would visit it once for each path to it.
    let recursive (e : Expr) : Bool := match e with
      | .const n _ => recs.contains n
      | _ => false
    if (e.find? recursive).isNone then return #[]
    -- Descend through binders to find closed applications, but never export
    -- an application or a guard containing a binder-local variable.
    let own := if (Core.recursiveFacts depth e.hasLooseBVars).1 && recursive e.getAppFn && e.isApp then
      #[(e, gs.filter (!·.hasLooseBVars), depth, ancestors)] else #[]
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
      let args := e.getAppArgs
      let guard := if e.isAppOfArity ``And 2 then args[0]! else mkNot args[0]!
      return own ++ (← scan recs args[0]! gs depth ancestors)
        ++ (← scan recs args[1]! (gs.push guard) depth ancestors)
    else if e.isAppOfArity ``ite 5 then
      let args := e.getAppArgs
      return own ++ (← scan recs args[1]! gs depth ancestors)
        ++ (← scan recs args[3]! (gs.push args[1]!) depth ancestors)
        ++ (← scan recs args[4]! (gs.push (mkNot args[1]!)) depth ancestors)
    else match e with
    | .app .. =>
      -- Instance and proof arguments are elaboration artifacts, not
      -- evaluated applications. In particular, a conditional's Decidable
      -- instance must not leak branch applications outside their guards.
      let info ← getFunInfo e.getAppFn
      let args := e.getAppArgs.zipIdx.filter fun (_, i) =>
        !(info.paramInfo[i]?.any fun p => p.isInstance || p.isProp)
      return own ++ (← args.flatMapM fun (arg, _) => scan recs arg gs depth ancestors)
    | .forallE _ p q _ =>
      let guards := if !p.hasLooseBVars && (← isProp p) then gs.push p else gs
      return (← scan recs p gs depth ancestors) ++ (← scan recs q guards depth ancestors)
    | .lam _ p q _ => return (← scan recs p gs depth ancestors) ++ (← scan recs q gs depth ancestors)
    | .mdata _ b => scan recs b gs depth ancestors
    | _ => return own

/-- The value in a function's own contract is its body, once. Applications
inside that body remain opaque, with their own ground facts. -/
def contractBody (c : CompInfo) (fvs : Array Expr) (e : Expr) : MetaM Expr := do
  let st ← getState
  let some f := c.fn? | return e
  let some d := st.defined.get? f | return e
  let some body := d.recBody? | return e
  let some solver := d.solver? | return e
  -- A generic one's at its own type parameters, which the check has as
  -- locals of its own: the instance that its parameters' types give.
  let m := d.solverTypeArgs.size
  return e.replace fun t =>
    if t.getAppFn.isConstOf solver && t.getAppNumArgs == m + fvs.size && t.getAppArgs.extract m == fvs then
      some ((d.atRecInstance (t.getAppArgs.extract 0 m) body).beta fvs)
    else none

/-- The head of a goal, as `Core.introduceGoal` reads it
(`Reqs/Cli#goal-introduction`), with each binder in front, a bound name or a
premise, made a local of the state: `∀ x, b` and `p → b`, a premise if its
type is a proposition, as lean-smt's own introduction tells them apart,
and `let x := v; b`, with `v` substituted. -/
def leanGoalHead (e : Expr) : StateT LocalContext MetaM (Core.GoalHead Expr Expr) := do
  match e.consumeMData with
  | .forallE n t b bi =>
    let lctx ← get
    let prop ← withLCtx lctx (← getLocalInstances) (Meta.isProp t)
    let id ← mkFreshFVarId
    set (lctx.mkLocalDecl id n t bi)
    let x := Expr.fvar id
    return if prop then .premise x (b.instantiate1 x) else .universal x (b.instantiate1 x)
  | .letE _ _ v b _ => return .definition (b.instantiate1 v)
  | _ => return .other

/-- `b` with each of its steps, a query or building or reading a model, under
Lean's heartbeat limit of its own, as each query has a time limit of its own
(`fren.timeout`): a procedure never reaches the limit only by having many
clauses, which the `fren` command, with no such limit, checks
(`Reqs/View#check-results`). -/
def Core.Backend.ownHeartbeats (b : Core.Backend MetaM Expr Expr) : Core.Backend MetaM Expr Expr :=
  { b with
    query := fun hyps goal wantModel => withCurrHeartbeats (b.query hyps goal wantModel)
    modelBool? := b.modelBool?.map fun f model formula => withCurrHeartbeats (f model formula)
    existsOutputs := fun body => withCurrHeartbeats (b.existsOutputs body)
    pin := fun n val => withCurrHeartbeats (b.pin n val)
    pinVariant := fun n val => withCurrHeartbeats (b.pinVariant n val)
    render := fun n val => withCurrHeartbeats (b.render n val)
    confirm? := b.confirm?.map fun f hyps goal model => withCurrHeartbeats (f hyps goal model) }

/-- The lean-smt backend, for a procedure whose variables are the free variables
`fvs`, and whose variables other than its parameters have second copies `primes`
(`Core.primed`), answering from `cache` the queries asked before. `facts` are
what its `Nat` variables bring, of both copies, which every query assumes,
and `outFacts` those of its outputs, which realizability's `∃` asserts too;
`appsOf` finds the applications of uninterpreted functions into `Nat` or
with postconditions in a formula, whose facts, by `factsOf`, each query
assumes of its own (`Reqs/Check`), and of the applications in those facts,
in at most `rounds` rounds (`Core.appFactsWith`). With `modelOptional`, a model that lean-smt cannot read, as
it cannot some values of abstract types, is left out rather than making the
answer unknown: a cover goal passes on `sat`, with or without one. Such an
answer is not cached. -/
def leanBackend (c : CompInfo) (fvs primes : Array Expr) (cache : QueryCache) (facts : Array (Name × Expr) := #[])
    (outFacts : Array Expr := #[]) (appsOf : Expr → Array Expr := fun _ => #[])
    (factsOf : Expr → MetaM (Array (Name × Expr)) := fun _ => pure #[]) (modelOptional : Bool := false)
    (bounded : Bool := false) (instances : Expr → Expr := id) (finiteModel : Bool := false)
    (snapshots? : Option (IO.Ref (Array Smt.Model)) := none)
    (fnOf : Expr → Option Name := fun _ => none) (applied? : Option (IO.Ref (Array Name)) := none)
    (rounds : Nat := 1) (script? : Option (IO.Ref String) := none) (sortHooks? : Option ElabHooks := none) :
    Core.Backend MetaM Expr Expr :=
  let copied := c.vars.zip fvs |>.filter fun (v, _) => (Core.Symbol.ofRole v.role).copied
  let vars := c.vars.zip fvs ++ (copied.zip primes).map fun ((v, _), p) =>
    ({ v with name := Core.primed v.name }, p)
  let varOf? (n : Name) := vars.find? (·.1.name == n)
  -- The answer to the query of `hyps` and `goal`, as the solver knows them,
  -- whose model also has the values of the locals `extra`, by their names,
  -- and whether to cache it: not if it leaves out a model that lean-smt
  -- could not read.
  let askSmt (requery : Bool) (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) (extra : Array Expr := #[]) :
      MetaM (Core.Outcome Expr × Bool) := do
    -- Each recursive symbol is opaque to the solver.
    let recs ← recursiveSolvers (hyps.map (·.2) |>.push goal)
    withRecursiveDefs recs fun recFvs sub => do
    let hyps := hyps.map fun (n, t) => (n, sub t)
    let goal := sub goal
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
      -- Asked again, for a model that confirmation contradicts, after
      -- them, so that they are overridden (`Core.askedAgain`).
      let requeryOptions := if requery then Core.requeryOptions else []
      -- A procedure whose queries may quantify over a collection's
      -- elements sets `fmf-bound` (`Core.boundedOptions`).
      let bounded := if bounded then Core.boundedOptions else []
      -- The goal's leading binders introduced, as the binary introduces
      -- them (`Core.introduceGoal`): its bound names and premises are
      -- locals, which lean-smt declares as constants and asserts as hints,
      -- and it is told not to introduce any itself.
      let (intro, lctx) ← (Core.introduceGoal leanGoalHead goal).run (← getLCtx)
      withLCtx lctx (← getLocalInstances) do
      let goal := intro.goal
      -- The premises after the hypotheses, as the binary asserts them.
      let premises := intro.premises
      withSolverCollectionSorts sortHooks? (#[goal] ++ premises ++ hs ++ recFvs) fun sortHints => do
      -- With `script?`, the query's script, as lean-smt writes it, kept
      -- there, and nothing asked (`Fren.Core.obligationsOf`).
      if let some r := script? then
        let mv ← mkFreshExprMVar goal
        let (_, text) ← queryShown do
          Smt.smt { trust := true, showQuery := true, embeddings := true, intros := false } mv.mvarId!
            (premises.reverse ++ hs.reverse ++ recFvs ++ sortHints)
        r.set text
        return (.unknown "not asked", false)
      -- Each attempt on a goal of its own.
      let solve (model : Bool) : MetaM (Core.Outcome Expr) := do
        let mv ← mkFreshExprMVar goal
        -- The options of a spec that uses strings and sets, as in the binary (`cli::logic`).
        -- lean-smt asserts its hints in reverse order, and cvc5's answer
        -- can depend on the order (#173), so they are given reversed, to be
        -- asserted in the binary's order.
        -- lean-smt's embeddings, of `Bool`s into propositions and of `Nat`s
        -- into `Int`s, revert a recursive definition's `let` and give it
        -- back as a `have`, which they cannot then introduce
        -- (`withRecursiveDefs`).
        -- The time of a query that reaches its time limit is recorded
        -- (`Core.solverCredit`).
        match ← Core.timeQuery timeout smtTimedOut <|
            Smt.smt { trust := true, model, timeout := some timeout, embeddings := true, intros := false
                      -- `fmf-bound` right after the options both front ends set, as the
                      -- binary sets it.
                      -- lean-smt's logic, `ALL`, quantifies (`Core.quantifierOptions`).
                      extraSolverOptions := Core.solverOptions true true ++ bounded
                        ++ (if finiteModel then Core.finiteModelOptions else []) ++ Core.quantifierOptions "ALL"
                        ++ logic ++ cvc5Defaults ++ requeryOptions
                        ++ resourceLimitOptions (← getOptions) ++ quietOptions }
              mv.mvarId! (premises.reverse ++ hs.reverse ++ recFvs ++ sortHints) with
        | .sat (some m) =>
          let values := m.values.filterMap fun (k, v) =>
            match (vars.find? (·.2 == k)).map (·.1.name) with
            | some n => some (n, v)
            | none => if extra.contains k then some (k.fvarId!.name, v) else none
          let token ← match snapshots? with
            | none => pure #[]
            | some snapshots =>
              let index := (← snapshots.get).size
              snapshots.modify (·.push m)
              pure #[((Name.mkSimple "#member_model"), mkNatLit index)]
          return .sat (values ++ token)
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
  let askElems (requery : Bool) (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) : MetaM (Core.Outcome Expr × Bool) := do
    let first ← Elems.withExpanded hyps goal none fun ex => do
      let (o, c) ← askSmt requery ex.hyps ex.goal (wantModel || !ex.lengths.isEmpty) (ex.lengths.map (·.1))
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
      match ← Elems.withExpanded hyps goal (some pins) fun ex => askSmt requery ex.hyps ex.goal wantModel with
      | .error n => return (.unknown (Core.elementLimitReason n), true)
      | .ok (.unsat, c) => return (.unknown Core.elementUnconfirmedReason, c)
      | .ok r => return r
  -- `unfolded?` is `hyps`'s and `goal`'s formulas already unfolded, by
  -- `unfoldDefined`, which a query that may be recursive does first.
  let ask (requery : Bool) (hyps : Array (Name × Expr)) (goal : Expr) (wantModel : Bool) (unfolded? : Option (Array Expr × Expr) := none) :
      MetaM ((Core.Outcome Expr × Bool) × Array Name × Array Name) :=
    withoutModifyingState do
    -- With the `have`s of `let`s and `where` clauses substituted, so that an
    -- application to a name mentions no bound variable. And the functions
    -- whose contracts those facts have, but its own function's, in its
    -- own contract (`Core.appFactsWith`).
    -- And those of the applications in those facts, once their clauses
    -- are unfolded (`Core.closeApps`).
    let factAppsOf (f : Expr) : MetaM (Array Expr) := return appsOf (← unfoldDefined f)
    let some (appFacts, fns) ← Core.appFactsWith appsOf factsOf fnOf factAppsOf rounds
        (← hyps.mapM fun (n, t) => return (n, ← zetaReduce t)) (← zetaReduce goal) c.fn?
      | throwError Core.factRoundsMsg
    let unfoldedHyps ← match unfolded? with
      | some (us, _) => pure (hyps.zipWith (fun (n, _) u => (n, u)) us)
      | none => hyps.mapM fun (n, t) => return (n, ← unfoldDefined t)
    let appFacts ← appFacts.mapM fun (n, t) => return (n, ← unfoldDefined t)
    let unfoldedFacts ← facts.mapM fun (n, t) => return (n, ← unfoldDefined t)
    -- The recursive functions that the facts of its applications apply,
    -- by path, whose models are never confirmed
    -- (`Core.recursiveCounterexample`).
    let st ← getState
    let factRecs := appFacts.foldl (init := #[]) fun acc (_, t) =>
      t.foldConsts acc fun k acc =>
        match st.defined.foldl (init := none) fun r _ d => r <|> if d.recursive && d.solver? == some k then some d.path else none with
        | some p => if acc.contains p then acc else acc.push p
        | none => acc
    -- Reflected with the hypotheses (`Core.recursionFormulas`).
    let hyps ← (Core.recursionFormulas unfoldedFacts appFacts unfoldedHyps).mapM
      fun (n, t) => return (n, ← contractBody c fvs t)
    let goal ← contractBody c fvs (← match unfolded? with | some (_, g) => pure g | none => unfoldDefined goal)
    -- Deeper in the check of a function generated for induction
    -- (`lang::unfoldings`).
    let reflected ← recursiveQueryFacts hyps goal (unfoldings := Core.unfoldings (c.fn?.any Core.isInductionFn))
    -- A large local context becomes a linear telescope when lean-smt
    -- preprocesses it. Keep the reflected facts in one balanced formula.
    let hyps := if reflected.isEmpty then hyps else
      #[(Name.mkSimple "#recursive_facts", balanced mkAnd (reflected.map (·.2)))] ++ hyps
    let goal ← smtBinders goal
    let hyps ← hyps.mapM fun (n, t) => return (n, ← smtBinders t)
    -- Each instance of a generic function without a body, a local of its
    -- own (`withInstances`), before any quantifier over elements is
    -- expanded.
    let goal := instances goal
    let hyps := hyps.map fun (n, t) => (n, instances t)
    -- A script is of the query with its quantifiers over elements, as the
    -- `fren` command's is (`FrenCli.queryText`).
    if script?.isNone && (Elems.hasMark goal || hyps.any (Elems.hasMark ·.2)) then
      return (← askElems requery hyps goal wantModel, fns, factRecs)
    else return (← askSmt requery hyps goal wantModel, fns, factRecs)
  Core.Backend.ownHeartbeats <|
  { query := fun hyps goal wantModel => do
      -- The same formulas, in the same local context and with the same
      -- options, are the same query.
      let key := (hyps.map (·.2), goal, wantModel)
      -- The functions whose contracts a query's facts have, for its check
      -- (`Core.withApplies`), whether or not it was asked before.
      let record (fns : Array Name) : MetaM Unit := do
        if let some r := applied? then
          r.modify fun acc => fns.foldl (init := acc) fun acc f => if acc.contains f then acc else acc.push f
      if let some (o, fns) := (← cache.get)[key]? then record fns; return o
      let hasRecursion := (← getState).defined.foldl (init := false) fun yes _ d => yes || d.recursive
      -- The formulas unfolded once, for both the recursive symbols and the query.
      let unfolded? ← if hasRecursion then
          pure (some (← hyps.mapM (unfoldDefined ·.2), ← unfoldDefined goal))
        else pure none
      let recs ← match unfolded? with
        | some (us, g) => recursiveSolvers (us.push g)
        | none => pure #[]
      -- Even a query that needs only sat/unsat must obtain its inputs to
      -- confirm a recursive model, as the CLI's confirming backend does.
      let getModel := wantModel || !recs.isEmpty
      -- The solver's answer, asked with `Core.requeryOptions` if
      -- `requery`, and whether it can be cached. A fact that applies a
      -- recursive function is never confirmed, a conservative choice: the
      -- check fails only under that function's contract, as the binary's
      -- backend decides it too, in its query, before it confirms.
      let answer (requery : Bool) : MetaM ((Core.Outcome Expr × Bool) × Array Name) := do
        let ((o, cacheable), fns, factRecs) ← ask requery hyps goal getModel unfolded?
        let o := match o with
          | .sat _ =>
            if !factRecs.isEmpty && !Core.recursiveCounterexample (!recs.isEmpty) true true then
              .unknown (Core.recursiveReason factRecs)
            else o
          | o => o
        return ((o, cacheable), fns)
      -- The functions whose contracts the query's facts apply, which `ask`
      -- finds in its hypotheses and goal, whatever `requery` is: those of
      -- the query asked again are these.
      let ((first, cacheable), fns) ← answer false
      record fns
      let st ← getState
      let recursive := st.defined.foldl (init := #[]) fun acc _ d =>
        if d.recursive then (acc.push d.decl) ++ d.solver?.toArray else acc
      -- A model that contradicts a formula that applies no recursive
      -- function is asked for again (`Core.askedAgain`), read without the
      -- injected misread, as the `fren` command reads every model to
      -- confirm it: of every query that obtains a model, as the `fren`
      -- command obtains one of every query. The recursive confirmation
      -- below is of the answer that it keeps, as the `fren` command's is.
      let againOk ← IO.mkRef true
      let o ← Core.askedAgainThen first (fun model => plainContradiction c fvs primes hyps goal model recursive)
          (if !getModel then none else some do
            let ((o, ok), _) ← answer true
            againOk.set ok
            pure o)
        (forced := ← Core.askAgainForced) fun o => match o with
        | .sat model => do
          if recs.isEmpty then pure o else
          -- Each of its own formulas, as the solver has it: whether it
          -- applies a recursive function, and its value at the model.
          let infos ← recursiveInfos
          let applies (e : Expr) : Bool := !(recInstancesIn infos e #[]).isEmpty
          let (us, g) := unfolded?.getD (hyps.map (·.2), goal)
          let vals ← confirmRecursiveModel c fvs primes hyps goal model
          let own := us.mapIdx fun i u => (applies u, vals.bind (·[i]?))
          let goalF := (applies g, (vals.bind (·[us.size]?)).map (!·))
          if Core.counterexampleReported own goalF false then pure o
          else do
            -- A formula without recursion that the model contradicts is
            -- the report's internal error, not the contracts'.
            if ← plainContradiction c fvs primes hyps goal model recursive then pure o else
            let names := recs.filterMap fun (r, _) => st.defined.foldl (init := none) fun acc _ d =>
              if d.solver? == some r then some d.path else acc
            pure (.unknown (Core.recursiveReason names))
        | _ => pure o
      let o := if wantModel then o else match o with | .sat _ => .sat #[] | _ => o
      if cacheable && (← againOk.get) then cache.modify (·.insert key (o, fns))
      return o
    modelBool? := snapshots?.map fun snapshots => fun model formula => do
      let some (_, token) := model.find? (·.1 == Name.mkSimple "#member_model") | return none
      let some index := token.rawNatLit? <|> token.nat? | return none
      let some captured := (← snapshots.get)[index]? | return none
      let formula := instances (← unfoldDefined (← zetaReduce formula))
      -- Interpret the formula using the exact captured sort/function/value
      -- interpretation. No new solver query or variable-only pinning is used.
      try
        return ← captured.ctx.runMetaM do
          let entries ← captured.entries.mapM fun (key, value) => do
            let expected ← inferType key
            let expected := expected.replace fun term => (captured.sorts.find? (·.1 == term)).map (·.2)
            return (key, ← modelValue expected value)
          let interpreted := formula.replace fun e => (entries.find? (·.1 == e)).map (·.2)
          let value ← reduce interpreted
          if value.isConstOf ``True then return some true
          if value.isConstOf ``False then return some false
          if value.hasFVar || value.hasMVar then return none
          match ← trySynthInstance (mkApp (mkConst ``Decidable) value) with
          | .some decision =>
            let decided ← reduce (mkApp2 (mkConst ``Decidable.decide) value decision)
            if decided.isConstOf ``Bool.true then return some true
            if decided.isConstOf ``Bool.false then return some false
            return none
          | _ => return none
      catch _ => return none
    falseF := mkConst ``False
    notF := mkNot
    conj := fun ps => mkAndN ps.toList
    existsOutputs := fun body =>
      -- The procedure's own outputs, not their second copies.
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
    confirm? := some fun hyps goal model => confirmModel c fvs primes hyps goal model
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
      -- And an abstract type or function by its whole path too, as the `fren`
      -- command names it (`Core.ItemSymbol.item`), so that two of one name in
      -- two modules are apart, and apart from every variable.
      let name := if isInhabitedName uses[i] then Name.mkSimple uses[i].getString!
        else Name.mkSimple ("::" ++ Core.showPath (uses[i].replacePrefix `Fren.Abstract .anonymous))
      Meta.withLocalDecl name bi (if nat then intResult ty else ty) fun x => do
        let fns := if ty.isForall then fns.push (uses[i], x, ty.getForallArity, nat) else fns
        -- An abstract type, or a type parameter's sort, whose `Inhabited`
        -- instance the formulas do not use, has one as a local instance
        -- all the same: an expansion over the elements of a sequence of it
        -- indexes the sequence (`Reqs/Lang/ElementQuantifiers#expansion`).
        if ty.isType && !uses.contains (inhabitedName uses[i]) then
          return ← Meta.withLocalDecl (Name.mkSimple "#inhabited") .instImplicit
            (mkApp (mkConst ``Inhabited [Level.one]) x) fun _ => go (i + 1) (reps.push x) fns
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
state (`Core.appFactsWith`), in declaration order. -/
def checkUses (c : CompInfo) : MetaM (Array Name) := do
  let s ← getState
  let mut uses ← usesOf (c.uses.map (mkConst ·) ++ c.indexes.map (·.2.2.2.2)
    ++ c.vars.filterMap (·.fact?))
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
unfolded only after the query's own applications are found, and under
realizability's `∃`, an application's arguments mention no output
(`lang::argument`). The applications of a fact (`Core.closeApps`) are
found once its clauses are unfolded, so there a clause's quantifiers bind
as an unbounded quantifier's do, and a fact of an application under a
binder is a `∀` over it (`closedFacts`). An
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

/-- `e` without the binders of its `fun`s that it does not mention: an
application that `natApps` closes over the binders around it, closed over
those that it mentions alone, as its facts are (`closedFacts`), so that
the same application found under other binders, as in a fact of another
(`Core.closeApps`), is the same, as the `fren` command's are (`natApps`
of its elaborator). Without it, lean-smt also fails on the query, with
cvc5's "Symbol '->' not declared as a variable", for a reason not yet
known: in realizability's query of `test/ui/checks/quantifier_facts.fren`'s
`nats`, the application `fun ok? i => h i` of its goal, closed over the
`∃`'s `ok?` too, beside `fun i => h i` of its own fact (#493). -/
partial def pruneLams : Expr → Expr
  | .lam n d b bi =>
    let b := pruneLams b
    if b.hasLooseBVar 0 then .lam n d b bi else b.lowerLooseBVars 1 1
  | e => e

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
(`Reqs/Generated#cover-goals`): only for a procedure that uses no abstract types
or functions, and when every value is a closed term of its variable's
type. A variable that the model leaves out is `default`. The caller adds
it (`addCoverWitness`), so that procedures can be checked in parallel. -/
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

/-- What enumerates the checks of a procedure set to enumeration
(`Reqs/Check#checking-by-enumeration`), given the procedure, its formulas, the
locals of its variables, and of the abstract types and functions that it
uses, with the functions among them, and the kinds of check to run:
`Fren.Enumerate`'s, which needs the elaborator. -/
abbrev EnumHook := CompInfo → Core.Comp Expr → Array Expr → Array Expr → Array (Name × Expr × Nat × Bool) →
  Array CheckKind → MetaM (Except Core.Msg Core.Enumeration.Enumerated)

/-- All selected checks for one procedure, in reporting order, with the theorems
that its cover goals are met (`coverWitness`), for the caller to add,
what enumerating the checks set to enumeration found, by `enumerate`, and
the messages about the checks that the method their evidence sets does not
run (`F0654`). -/
partial def checkComp (c : CompInfo) (kinds : Array CheckKind := Core.CheckKind.all) (enumerate? : Option EnumHook := none)
    (hooks? : Option ElabHooks := none) (own : Array (Array Core.Ty) := #[])
    (foreign : Array (Name × Array Core.Ty) := #[]) (obligations? : Option (IO.Ref (Array (Array Core.Obligation))) := none) :
    MetaM (Array CheckResult × Array Declaration × Option (Except Core.Msg Core.Enumeration.Enumerated) × Array Core.Msg) := do
  let kinds := Core.kindsRun c.subset?.isSome c.subsetInvariant?.isSome kinds
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
    -- And those that the clauses of the functions that it uses apply, whose
    -- facts the queries may have where a fact applies them
    -- (`Core.closeApps`), as the `fren` command declares every instance.
    let clauses := st0.abstracts.foldl (init := #[]) fun acc _ a =>
      if a.typeParams.isEmpty && c.uses.contains a.placeholder then
        acc ++ (((st0.contracts.get? a.path).map fun k => k.pres ++ k.posts).getD #[])
      else acc
    for cl in clauses do insts := instancesIn gens (← unfoldDefined (← rep (cl.at #[]))) insts
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
      laws := ← c.laws.mapM fun (n, l) => return (n, ← rep l)
      lawsOf := c.lawsOf
      -- A defined function's postconditions are claims of its own
      -- (`check::postcondition`), and the hypotheses of nothing; an
      -- uninterpreted function's, of its value, its contract's guarantees
      -- (`Reqs/Check#contracts-of-uninterpreted-functions`).
      reqs := ← if c.fn?.isNone || contract then named c.ensures else pure #[]
      posts := ← if c.fn?.isSome && !contract then named c.ensures else pure #[]
      recursive := c.fn?.any fun f => ((st0.defined.get? f).map (·.recursive)).getD false
      fn? := c.fn?
      expects := ← named c.expects
      covers := ← named c.covers
      branchGroups := ← (c.props.flatMap (·.branchGroups)).mapM fun group => do
        let members ← group.members.mapM fun member => do
          return { member with
            formula := ← beta member.formula
            valueFormula? := ← member.valueFormula?.mapM beta
            evaluationGuard? := ← member.evaluationGuard?.mapM beta }
        return { group with members, guard? := ← group.guard?.mapM beta }
      memberGroups := ← (c.props.flatMap (·.memberGroups)).mapM fun group => do
        let members ← group.members.mapM fun member => do
          return { member with
            formula := ← beta member.formula
            valueFormula? := ← member.valueFormula?.mapM beta
            evaluationGuard? := ← member.evaluationGuard?.mapM beta }
        return { group with members }
      insts := ← c.insts.mapM fun i => return {
        name := i.name, comp := i.comp, bindings := ← beta i.bindings, behaviour := ← beta i.behaviour
        assumes := ← i.assumes.mapM fun (n, a) => return (n, ← beta a), typed := i.typed }
      triggers := ← (c.ensures ++ c.expects).filterMapM fun p => p.trigger?.mapM fun t => return (p.name, ← beta t)
      -- Numbered in order within each item.
      indexes := ← indexes.mapIdxM fun j (n, place, _, _, goal) => do
        let k := (indexes.extract 0 j).filter (·.1 == n) |>.size
        return { prop := n, k, place, goal := ← beta goal, subsetTy? := obligationTy? goal, excludeSelf := isLeafObligation goal }
      tables := tables.mapIdx fun j (n, place, q, goal) =>
        let k := (tables.extract 0 j).filter (·.1 == n) |>.size
        { site := { prop := n, k, place, goal, excludeSelf := isLeafObligation goal }, goal := q }
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
          comp.branchGroups comp.memberGroups
      | _, _, _ => comp
    -- What the `Nat` variables bring (`lang::nat_variable`): each, of both
    -- copies, is at least 0. Each query's applications bring their own
    -- (`Core.appFactsWith`).
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
    -- The applications of functions into subset types, and the reads of
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
    -- A partial table/match has an unspecified empty-sequence read as
    -- its fallback. Its interpretation is free even with no declared UF,
    -- so a SAT witness must not stand in for universal inhabitation.
    let unspecified ← if c.subset?.isNone then pure false else
      (comp.reqs.map (·.2) ++ comp.defs.map (·.2.1) ++ facts.map (·.2)).anyM fun formula => do
        let formula ← unfoldDefined formula
        hasUnspecifiedRead formula
    let full := { comp with
      inhabitation := c.subset?.isSome
      typesInterpreted := (c.vars.any fun v => interprets v.type) || facts.any (interprets ·.2) || unspecified }
    -- Only the `fren` command runs the checks set to testing (`check::by_testing`),
    -- and enumeration those set to enumeration (`check::by_evidence`).
    let enumerated ← if c.enumerated.any then (enumerate?.mapM fun f => f c full fvs ufs fns kinds) else pure none
    -- The checks that the method their evidence sets does not run
    -- (`check::method_run`), as the `fren` command shows its subject.
    let global := st0.globals.toList.any fun (p, g) => g.decl == c.decl && p != g.path
    let subject := Core.subjectOf c.path global (c.props[0]?.map (·.name))
    let skipped := full.skippedMsgs subject c.tested c.enumerated kinds
    let kinds0 := kinds
    let (comp, kinds) := full.untested (c.tested.union c.enumerated) kinds
    let cache : QueryCache ← IO.mkRef {}
    let memberModels ← IO.mkRef (#[] : Array Smt.Model)
    -- The models of the cover goals' queries, by goal, for their theorems.
    let models ← IO.mkRef (#[] : Array (Expr × Array (Name × Expr)))
    -- The functions whose applications bring facts: those into `Nat`, and
    -- the uninterpreted ones with postconditions (`Core.appFactsWith`).
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
    -- The function of an application, closed over the binders around it
    -- (`natApps`), whose contract's postconditions its facts have, by its
    -- path (`Core.appFactsWith`): not an instance of a generic function, whose
    -- premise is not applied yet (#522).
    let fnOf (app : Expr) : Option Name :=
      let rec peel : Expr → Expr
        | .lam _ _ b _ => peel b
        | e => e
      let head := (peel app).getAppFn
      if generics.any (head.isConstOf ·.1.placeholder) then none else
      (factFns.find? (·.2.1 == head)).bind fun (u, _, _, _) =>
        if (postsOf u).isEmpty then none
        else some ((st.abstracts.foldl (init := none) fun acc _ a =>
          acc <|> if a.placeholder == u then some a.path else none).getD .anonymous)
    let applied ← IO.mkRef (#[] : Array Name)
    let mkBk (k : CheckKind) (cache : QueryCache) (script? : Option (IO.Ref String) := none) :=
      let heads := factFns.map (fun (_, x, n, _) => (x, n)) ++ typedApps.map (fun (x, n, _, _) => (x, n))
        ++ generics.map fun (a, m) => (mkConst a.placeholder, m + a.declared.size)
      leanBackend c fvs primes cache facts outFacts (fun e => (natApps heads e).map pruneLams)
        (closedFacts factsOf)
        (modelOptional := k == .cover) bounded instances (finiteModel := generic || c.finiteModel)
        (snapshots? := if full.memberGroups.isEmpty then none else some memberModels) fnOf
        (if script?.isSome then none else some applied) (heads.size + 1) script?
        (hooks?.map fun h => { h with leanType := fun t => do rep (← h.leanType t), coreTy := fun t => h.coreTy (unrep t) })
    -- What each of its checks asks, for `set_option fren.dump
    -- "obligations"`, with its query's script as lean-smt would be given
    -- it, from a cache of its own, so that no answer is taken for it
    -- (`Core.obligationsOf`).
    if let some r := obligations? then
      -- A script that cannot be built is an `(error ...)` command, which the
      -- dump shows, so that the dump asks the solver nothing and changes no
      -- verdict; but its work counts towards the item's heartbeats, and a
      -- limit of Lean's that building it reaches, heartbeats or recursion
      -- depth, is the item's failure to check (`Reqs/Cli#obligations`).
      let script (k : CheckKind) (hyps : Array (Name × Expr)) (goal : Expr) : MetaM String := do
        let text ← IO.mkRef ""
        let fresh : QueryCache ← IO.mkRef {}
        try discard <| (mkBk k fresh (some text)).query hyps goal false
        catch ex => text.set (Core.errorScript (← ex.toMessageData.toString))
        text.get
      let fileMap ← getFileMap
      let spanOf (n? : Option Name) : Option String :=
        let ref := (n?.bind fun n => (c.props.find? (·.name == n)).map (·.ref)
          <|> (c.insts.find? (·.name == n)).map (·.ref)).getD c.ref
        (ref.getPos?).map fun p => let q := fileMap.toPosition p; s!"{q.line}:{q.column + 1}"
      -- The locals that stand for its abstract types and functions, and its
      -- recursive functions, are named canonically already (`withNatUses`,
      -- `withRecursiveDefs`).
      let symbols := dumpSymbols st
      try
        let os ← withoutModifyingState <| Core.obligationsOf (mkBk · cache) script full kinds0 c.tested c.enumerated interprets
          spanOf symbols
        r.modify (·.push os)
      -- An item whose questions cannot be built is one `(error ...)`
      -- obligation, as a script that cannot be built is.
      catch ex =>
        let comp := Core.itemName full
        r.modify (·.push #[{ comp, kind := (kinds0[0]?).getD .realizable, part := "questions"
                             script := Core.errorScript (← ex.toMessageData.toString) }])
    let bk (k : CheckKind) :=
      let b := mkBk k cache
      if k != .cover then b else
      { b with query := fun hyps goal wantModel => do
          let o ← b.query hyps goal wantModel
          if let .sat model := o then models.modify (·.push (goal, model))
          return o }
    let examples := fren.examples.get (← getOptions)
    let results := Core.recursiveResults comp.recursive (Core.withInterpreted full interprets (← Core.checkCompLawful bk comp kinds (some examples) interprets
      (some (applied.modifyGet fun a => (a, #[])))))
    -- A claim of a global expectation that its check leaves inconclusive:
    -- the postcondition of each function generated for induction on its
    -- parameters, in order, until one passes (`lang::induction_verdict`).
    let results ← results.mapM fun r => do
      let some (_, fns) := c.inductions.find? fun (n, _) => r.kind == .expect && r.prop? == some n | return r
      -- Not where the solver's model contradicts Fren's semantics, an
      -- internal error that the check reports.
      if r.verdict != .inconclusive || r.detail.modelRefuted then return r
      let mut attempts := #[]
      for f in fns do
        let some (_, _, b) := st0.inductionFns.get? f | continue
        -- With the function among the defined ones only for its own check
        -- (`State.inductionFns`), under a heartbeat limit of its own, as
        -- the nested checks below. An attempt that reaches a limit of
        -- Lean's does not pass, and the claim stays as its check left it.
        let saved ← getState
        modifyEnv (frenExt.modifyState · (·.withInductionFn f))
        let rs? ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (checkComp b #[.postcondition] none hooks?))
          fun ex => do
            if limitReached (← ex.toMessageData.toString) ex.isRuntime then pure none else throw ex
        modifyEnv (frenExt.modifyState · fun _ => saved)
        let some (rs, _, _, _) := rs? | continue
        let some p := rs.find? (·.kind == .postcondition) | continue
        attempts := attempts.push p
        if p.verdict == .pass then break
      match Core.inductionVerdict r.verdict r.detail.modelRefuted (attempts.toList.map (·.verdict)), attempts.find? (·.verdict == .pass) with
      | .pass, some p => return { r with verdict := .pass, detail := .none, applies := p.applies }
      | _, _ => return r
    -- The contract of a generic function without a body, where its check
    -- at its type parameters' sorts does not pass: its check at each
    -- instance that the spec applies (`lang::generic_contract`).
    let results ← match generic, c.fn?, hooks?, results.find? (·.kind == .realizable) with
      | true, some f, some hooks, some r =>
        if r.verdict == .pass then pure results else do
        let mut instResults := #[]
        for targs in own do
          let (rs, _, _, _) ← withCurrHeartbeats do
            checkComp (← instanceContract hooks elaborated f targs) #[.realizable] none hooks?
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
        let (rs, _, _, _) ← withCurrHeartbeats (checkComp b #[.realizable])
        unless rs.any fun r => r.kind == .realizable && r.verdict != .pass do continue
        let (rs, _, _, _) ← withCurrHeartbeats do
          checkComp (← instanceContract hooks b f targs) #[.realizable] none hooks?
        results := results ++ (rs.filter (·.kind == .realizable)).map fun r => { r with clashes := #[] }
    -- Each after the queries, under a heartbeat limit of its own, as each
    -- step of the backend is (`Core.Backend.ownHeartbeats`): each
    -- instance's contract and its nested check above, and each cover goal's
    -- question and witness.
    let mut witnesses := #[]
    for g in c.covers do
      let passed := results.any fun r => r.kind == .cover && r.prop? == some g.name && r.verdict == .pass
      let witness? ← withCurrHeartbeats do
        let goal := mkNot (← beta g.body)
        let some (_, model) := (← models.get).find? (·.1 == goal) | return none
        if passed then coverWitness c fvs g model else return none
      if let some d := witness? then witnesses := witnesses.push d
    return (results, witnesses, enumerated, skipped)

end Fren
