-- keep-sorted start
import Fren.FinSet
import Fren.Finite
import Fren.Model
import Fren.Resolve
import Fren.SimpSet
import Fren.Syntax
import FrenCore.Lexical
import FrenCore.Regex
import FrenCore.Syntax
-- keep-sorted end

/-!
# Elaborators

These are the only code that changes the Fren model. Each records Fren's own
representation of a declaration, then generates ordinary Lean declarations
from it (an `inductive` per enum; a `def` per constant; a `def` per
`assume`/`req`/`expect`, plus `assumes` and `reqs`, per comp; a `def` per
global expectation) so that specs can be used from Lean.
-/

open Lean Elab Command Term Meta

namespace Fren

/-- The identifiers of a `Lang.fren_path`. -/
def pathSegs (p : Syntax) : Array Syntax := p[0].getSepArgs

/-- Checks the name of a module, enum, variant or comp. -/
def checkItemName (what : String) (id : Syntax) : CommandElabM Name := do
  let n ← segName id
  liftMsg id (Core.checkItemName what n)
  return n

/-- Fails if `n` is already declared or imported by name in module `modName`. -/
def checkFresh (modName n : Name) (ref : Syntax) : CommandElabM Unit := do
  liftMsg ref ((← getState).table.checkFresh modName n)

/-- Reports the first identifier of `stx` that Lean read but that is not one
of Fren's (`lang::identifier`), as the `fren` command's lexer does. -/
partial def checkIdentifiers (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | .ident _ raw _ _ =>
    let s := raw.toString
    unless Core.identifierAccepted s do throwErrorAt stx (Core.leanIdentifierMsg s).text
  | .node _ _ args => args.forM checkIdentifiers
  | _ => pure ()

@[command_elab Lang.modCmd] def elabMod : CommandElab := fun stx => do
  checkIdentifiers stx
  let segs := pathSegs stx[2]
  let names ← segs.mapM segName
  let (path, new) ← liftResolve segs ((← getState).table.declareModule names (!stx[0].isNone))
  for i in new do
    let ref := (segs[i.path.components.length - 1]?).getD stx
    lintName .module (Name.mkSimple i.path.getString!) ref
    record (.item { item := i, ref })
  modifyLocal ({ · with currentModule := path })

/-- Imports the path `segs`, written at `ref`, into the current module, or,
with `scope`, into the component of that path. -/
def declareUse (segs : Array Syntax) (glob : Bool) (ref : Syntax) (scope : Option Name := none) : CommandElabM Unit := do
  let modName := (← getLocal).currentModule
  let u ← liftResolve segs ((← getState).table.declareUse modName (← segs.mapM segName) glob (scope.getD modName))
  record (.useDef u)
  recordUse u ref

@[command_elab Lang.useCmd] def elabUse : CommandElab := fun stx => do
  checkIdentifiers stx
  declareUse (pathSegs stx[1]) (!stx[2].isNone) stx[1]

@[command_elab Lang.useGroupCmd] def elabUseGroup : CommandElab := fun stx => do
  checkIdentifiers stx
  for p in stx[3].getSepArgs do
    declareUse (pathSegs stx[1] ++ pathSegs p) false p

/-- The path of a type written as one, or `none` for `Set(T)` and `Rel(A, B)`. -/
def typePath? (ty : Syntax) : Option Syntax :=
  if ty.isOfKind ``Lang.fren_path then some ty
  else if ty.isOfKind ``Lang.setType || ty.isOfKind ``Lang.relType || ty.isOfKind ``Lang.seqType then none
  else some ty[0]

/-- The Lean type of the Fren type `ty`. -/
partial def elabType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (modName : Name) (ty : Syntax) : m Expr := do
  -- `Set(T)`: `"Set" "(" T ")"`; `Rel(A, B)`: `"Rel" "(" A "," B ")"`.
  let some p := typePath? ty |
    if ty.isOfKind ``Lang.relType then
      return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero])
        (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← elabType modName ty[2]) (← elabType modName ty[4]))
    else if ty.isOfKind ``Lang.seqType then return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← elabType modName ty[2])
    else return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (← elabType modName ty[2])
  let ty := p
  let segs := pathSegs ty
  if segs.size == 1 && segs[0]!.getId == `Bool then return Lean.mkConst ``Bool
  if segs.size == 1 && segs[0]!.getId == `Int then return Lean.mkConst ``Int
  if segs.size == 1 && segs[0]!.getId == `String then return Lean.mkConst ``String
  match ← resolvePath modName segs with
  | .item { kind := .enumItem, path, .. } => return Lean.mkConst (← enumDecl path)
  | .item { kind := .recordItem, path, .. } =>
    let some r := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
    return Lean.mkConst r.decl
  | .item { kind := .typeItem, path, .. } => return Lean.mkConst (placeholderName path)
  | r => throwErrorAt ty (Core.notATypeMsg r).text

def varType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM Expr := do
  let n := name.getId
  let t ← ty?.mapM (elabType modName)
  liftMsg name (Core.checkVarName n (t.map (·.isConstOf ``Bool)))
  return t.getD (Lean.mkConst ``Bool)

/-- The paths within the `Set(...)`s and `Rel(...)`s of the type `ty`, and
whether there are any. -/
partial def typeElems (ty : Syntax) : Array Syntax × Bool :=
  match typePath? ty with
  | some p => (#[p], false)
  | none =>
    if ty.isOfKind ``Lang.relType then ((typeElems ty[2]).1 ++ (typeElems ty[4]).1, true)
    else ((typeElems ty[2]).1, true)

/-- The Lean types within the `Fren.FinSet`s and pairs of `t`. -/
partial def elemTypes (t : Expr) : Array Expr :=
  if t.isAppOfArity ``Fren.FinSet 1 || t.isAppOfArity ``Fren.Seq 1 then elemTypes t.appArg!
  else if t.isAppOfArity ``Prod 2 then elemTypes t.appFn!.appArg! ++ elemTypes t.appArg!
  else #[t]

/-- The Lean type of a field or payload, `ty`, checking that it is accepted
(`lang::field_type`): `own` is the type being declared. -/
def fieldType (modName : Name) (ty : Syntax) (own : Option Name) (payload : Bool) (ownName : Name) :
    CommandElabM Expr := do
  let (cores, inSet) := typeElems ty
  let own1 (core : Syntax) := let segs := pathSegs core; segs.size == 1 && segs[0]!.getId == ownName
  let isOwn := cores.any own1
  if isOwn && inSet then throwErrorAt ty (Core.recursiveSetMsg (modName ++ ownName)).text
  if let some decl := own then
    if isOwn then
      unless Core.fieldTypeAccepted false true false payload do
        throwErrorAt ty (Core.recursiveRecordMsg ownName).text
      return Lean.mkConst decl
  let t ← elabType modName ty
  let st ← getState
  let e := ((elemTypes t).find? fun e => e.isConst && st.placeholders.contains e.constName).getD t
  let abstract := e.isConst && st.placeholders.contains e.constName
  unless Core.fieldTypeAccepted abstract false false payload do
    let p := ((← getState).abstracts.foldl (init := none) fun acc _ a =>
      acc <|> if a.placeholder == e.constName then some a.path else none).getD .anonymous
    throwErrorAt ty (Core.abstractFieldMsg p payload inSet).text
  return t

/-- Lean syntax for the Lean type of a Fren type: a constant. -/
partial def typeSyntax (t : Expr) : Term :=
  if t.isAppOfArity ``Fren.FinSet 1 then Unhygienic.run `(Fren.FinSet $(typeSyntax t.appArg!))
  else if t.isAppOfArity ``Fren.Seq 1 then Unhygienic.run `(Fren.Seq $(typeSyntax t.appArg!))
  else if t.isAppOfArity ``Prod 2 then Unhygienic.run `($(typeSyntax t.appFn!.appArg!) × $(typeSyntax t.appArg!))
  else if t.isConst then mkCIdent t.constName!
  -- Not known yet, as the element type of `[]`: Lean infers it.
  else Unhygienic.run `(_)

@[command_elab Lang.enumCmd] def elabEnum : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "enum" nameStx
  checkFresh modName n nameStx
  lintName .enumeration n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let variantStxs := stx[4].getSepArgs
  let mut variants := #[]
  let mut payloads : Array (Array Expr) := #[]
  let mut nRecursive := 0
  let mut unbounded := false
  for v in variantStxs do
    let vn ← checkItemName "variant" v[0]
    if variants.contains vn then throwErrorAt v[0] (Core.dupVariantMsg vn).text
    lintName .variant vn v[0]
    variants := variants.push vn
    let tys := if v[1].isNone then #[] else v[1][1].getSepArgs
    let ts ← tys.mapM fun t => fieldType modName t (some decl) true n
    if ts.any (·.isConstOf decl) then nRecursive := nRecursive + 1
    let st ← getState
    unbounded := unbounded || ts.any fun t => t.isConstOf decl || st.unbounded t
    payloads := payloads.push ts
  unless Core.wellFounded variants.size nRecursive do throwErrorAt nameStx (Core.illFoundedMsg n).text
  let ctors ← (variants.zip payloads).mapM fun (v, ts) => do
    let bs ← ts.mapIdxM fun k t => do
      let ty := if t.isConstOf decl then mkIdent path else typeSyntax t
      `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent (Name.mkSimple s!"x{k}")) : $ty))
    `(Lean.Parser.Command.ctor| | $(mkIdent v):ident $bs:bracketedBinder*)
  elabCommand (← `(inductive $(mkIdentFrom nameStx path):ident where $ctors:ctor* deriving DecidableEq, Repr, Inhabited))
  if payloads.all (·.isEmpty) then
    let vals := variants.map fun v => mkIdent (decl ++ v)
    -- Named after the full path: an anonymous instance is named after `n`
    -- alone, which enumerations in different modules can share.
    elabCommand (← `(instance $(mkIdent (`_root_ ++ decl ++ `instFinite)):ident : Fren.Finite $(mkIdent decl) :=
      ⟨[$vals,*], by intro x; cases x <;> decide⟩))
  -- A selector for each value of each payload, which a `match` reads.
  for v in variants, ts in payloads do
    let ctor := decl ++ v
    let xs := (Array.range ts.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
    for t in ts, k in [0:ts.size] do
      let sel := mkIdent (`_root_ ++ selectorName ctor k)
      let x := xs[k]!
      let cmd ← if variants.size == 1 then
          `(def $sel:ident (v : $(mkCIdent decl)) : $(typeSyntax t) := match v with | $(mkCIdent ctor) $xs* => $x)
        else
          `(def $sel:ident (v : $(mkCIdent decl)) : $(typeSyntax t) := match v with | $(mkCIdent ctor) $xs* => $x | _ => default)
      elabCommand cmd
  record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
  record (.enumInfo { path, decl, variants, payloads, unbounded })
  unless isPub do recordItem .enumeration path nameStx

@[command_elab Lang.structCmd] def elabStruct : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let mut fields : Array (Name × Expr) := #[]
  for f in stx[4].getSepArgs do
    let fn := f[0].getId
    if fields.any (·.1 == fn) then throwErrorAt f[0] (Core.dupFieldMsg fn).text
    lintName .field fn f[0]
    let t ← if f[1].isNone then pure (Lean.mkConst ``Bool) else fieldType modName f[1][1] (some decl) false n
    -- As for a variable (`lang::bool_naming`).
    liftMsg f[0] (Core.checkVarName fn (if f[1].isNone then none else some (t.isConstOf ``Bool)))
    fields := fields.push (fn, t)
  let st ← getState
  let unbounded := fields.any fun (_, t) => st.unbounded t
  let bs ← fields.mapM fun (f, t) => `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent f):ident : $(typeSyntax t)))
  elabCommand (← `(structure $(mkIdentFrom nameStx path):ident where
    $(mkIdent `«{}»):ident :: $bs:structExplicitBinder*
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.recordInfo { path, decl, fields, unbounded })
  unless isPub do recordItem .record path nameStx

/-! ## Comps -/

/-- The placeholder of the abstract type or function at `path`. -/
def placeholderOf (path : Name) : TermElabM AbstractInfo := do
  let some a := (← getState).abstracts.get? path | throwError "internal error: unknown abstract item `{path}`"
  return a

/-- A binder of a `match` pattern in scope. -/
structure MatchBinder where
  name : Name
  /-- Its value: the selector applied to the scrutinee. -/
  term : Term
  type : Expr
  /-- Its scrutinee, and the number of binders in scope there: mentioning
  it counts as mentioning what the scrutinee mentions. -/
  scrutinee : Syntax
  outer : Nat

/-- What expression translation needs to know about the comp. -/
structure ExprCtx where
  modName : Name
  vars : Array Var
  /-- The comp's instances, in order. -/
  insts : Array Name
  place : Core.Place
  /-- For a binding, the index of its instance. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array MatchBinder := #[]
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- Something here gives `{}` its type (`Reqs/Lang/Expressions#sets`). -/
  emptyOk : Bool := false
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array Term := #[]
  /-- Whether to record the indexes of this expression for the definedness
  check, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, whose chain `membership_chain`
  looks at from its top. -/
  inOr : Bool := false

def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option MatchBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : MatchBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name)

/-- Whether the path `p`, applied, builds a variant rather than applying a
function. -/
def isVariant (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← (pathSegs p).mapM segName
  return (← getState).table.resolvePath cx.modName names cx.shadowing matches .ok (.variant ..)

/-- The defined function that the path `p`, applied, applies, if any. -/
def definedFn? (cx : ExprCtx) (p : Syntax) : TermElabM (Option DefinedInfo) := do
  let names ← (pathSegs p).mapM segName
  let s ← getState
  let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
  return s.defined.get? path

/-- The Fren name of the type whose Lean type is `t`. -/
partial def typeName (t : Expr) : TermElabM String := do
  if t.isConstOf ``Bool then return "Bool"
  if t.isConstOf ``Int then return "Int"
  if t.isConstOf ``String then return "String"
  if t.isAppOfArity ``Fren.Seq 1 then return s!"Seq({← typeName t.appArg!})"
  if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then return s!"Rel({← typeName e.appFn!.appArg!}, {← typeName e.appArg!})"
    return s!"Set({← typeName e})"
  let s ← getState
  let some d := t.constName? | return toString t
  if let some e := s.enumOfDecl? d then return Core.showPath e.path
  if let some r := s.recordOfDecl? d then return Core.showPath r.path
  if let some a := s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none then
    return Core.showPath a.path
  return toString d

/-- The Lean type of the Fren expression `t`, elaborated with the comp's
variables in scope. -/
def typeOf (t : Term) : TermElabM Expr := do
  let e ← withoutErrToSorry <| Term.withSynthesize <| elabTerm (← `(open Classical in $t)) none
  whnfR (← instantiateMVars (← inferType e))

/-- The pattern of `s.matches?(p)`, `p`, as a closed `Fren.Core.Re` term
(`Reqs/Lang/Expressions#patterns`). -/
def patternTerm (p : Syntax) : TermElabM Term := do
  let some lit := (if p.getNumArgs == 1 then p[0] else p).isStrLit?
    | throwErrorAt p Core.patternNotLiteralMsg.text
  match Core.parseRe lit with
  | .ok re => exprToSyntax (Lean.toExpr re)
  | .error e => throwErrorAt p e.msg.text

/-- The set of the nonempty `xs`, as `insert` and `singleton`, as `{a, b}`
elaborates, without its ambiguity with structure instances. -/
def finSetLit (xs : Array Term) : TermElabM Term := do
  let mut t ← `(Singleton.singleton $(xs.back!))
  for x in xs.pop.reverse do t ← `(Insert.insert $x $t)
  return t

/-- The element types of the relation type `ty`, if it is one. -/
def relTypes? (ty : Expr) : Option (Expr × Expr) :=
  if ty.isAppOfArity ``Fren.FinSet 1 && ty.appArg!.isAppOfArity ``Prod 2 then
    some (ty.appArg!.appFn!.appArg!, ty.appArg!.appArg!)
  else none

/-- Every value of a finite type, as terms, if there are at most `cap` of
them: a relation's `domain` and `range` are its image under them, which
the solver decides without a projection (`Reqs/Cli`). -/
partial def valuesOf? (ty : Expr) (cap : Nat := 64) : TermElabM (Option (Array Term)) := do
  if ty.isConstOf ``Bool then return some #[← `(true), ← `(false)]
  let s ← getState
  let some d := ty.constName? | return none
  let ctors : Array (Name × Array Expr) ←
    if let some e := s.enumOfDecl? d then
      if e.unbounded then return none
      pure (e.variants.mapIdx fun i v => (e.decl ++ v, e.payloads[i]?.getD #[]))
    else if let some r := s.recordOfDecl? d then
      if r.unbounded then return none
      pure #[(recordCtor r.decl, r.fields.map (·.2))]
    else return none
  let mut out := #[]
  for (c, ts) in ctors do
    let mut combos : Array (Array Term) := #[#[]]
    for t in ts do
      let some vs ← valuesOf? t cap | return none
      combos := combos.flatMap fun pre => vs.map pre.push
      if combos.size > cap then return none
    for args in combos do out := out.push (← `($(mkCIdent c) $args*))
    if out.size > cap then return none
  return some out

/-- Calls the method `m` of the term `t` of Lean type `ty`, with the
arguments `args`, each with its syntax (`lang::method_type`). -/
def callMethod (ref : Syntax) (t : Term) (ty : Expr) (m : String) (args : Array (Term × Syntax)) :
    TermElabM (Term × Expr) := do
  if ty.isAppOfArity ``Fren.Seq 1 then
    let elem := ty.appArg!
    let some method := (Core.Method.ofName? m).filter (·.accepts false false false true)
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false false false true).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    let leanTy : Core.MethodTy → Expr
      | .bool => Lean.mkConst ``Bool | .int => Lean.mkConst ``Int | .elem => elem | _ => ty
    for (a, stx) in args, p in method.params do
      let ta ← typeOf a
      unless ← isDefEq ta (leanTy p) do
        throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
    let a : Term := (args.map (·.1))[0]?.getD t
    let b : Term := (args.map (·.1))[1]?.getD t
    let term ← match method with
      | .len => `(Fren.Seq.len $t)
      | .startsWith => `(Fren.Seq.startsWith $t $a)
      | .endsWith => `(Fren.Seq.endsWith $t $a)
      | .contains => `(Fren.Seq.contains $t $a)
      | .at => `(Fren.Seq.«at» $t $a)
      | .slice => `(Fren.Seq.slice $t $a $b)
      | .indexOf => `(Fren.Seq.indexOf $t $a $b)
      | .replace => `(Fren.Seq.replace $t $a $b)
      | .update => `(Fren.Seq.update $t $a $b)
      | _ => `(Fren.Seq.rev $t)
    return (term, leanTy method.result)
  if let some (a, b) := relTypes? ty then
    let some method := (Core.Method.ofName? m).filter (·.accepts false false true)
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false false true).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    let set (e : Expr) := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) e
    let rel (x y : Expr) := set (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) x y)
    -- The image of the inverse under every value of `other`, if it is finite.
    let project (inv : Term) (other : Expr) (dflt : Term) : TermElabM Term := do
      let some vs ← valuesOf? other | return dflt
      `(Fren.FinSet.image $inv ($(← finSetLit vs) : Fren.FinSet $(typeSyntax other)))
    match method with
      | .card => return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
      | .inverse => return (← `(Fren.FinSet.inverse $t), rel b a)
      | .domain => return (← project (← `(Fren.FinSet.inverse $t)) b (← `(Fren.FinSet.domain $t)), set a)
      | .range => return (← project t a (← `(Fren.FinSet.range $t)), set b)
      | .closure => do
        unless ← isDefEq a b do throwErrorAt ref (Core.closureTypeMsg (← typeName ty)).text
        return (← `(Fren.FinSet.closure $t), ty)
      | _ => do
        let (x, stx) := args[0]!
        let tx ← typeOf x
        unless ← isDefEq tx (set a) do
          throwErrorAt stx s!"type mismatch: expected `{← typeName (set a)}`, found `{← typeName tx}`"
        return (← `(Fren.FinSet.image $t $x), set b)
  unless ty.isConstOf ``String do throwErrorAt ref (Core.noMethodsMsg m (← typeName ty)).text
  let some method := (Core.Method.ofName? m).filter (·.accepts true false)
    | throwErrorAt ref (Core.unknownMethodMsg m "String").text
  unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
  let leanTy : Core.MethodTy → Expr
    | .bool => Lean.mkConst ``Bool | .int => Lean.mkConst ``Int | _ => Lean.mkConst ``String
  for (a, stx) in args, p in method.params do
    -- A pattern is a `Fren.Core.Re`, which `patternTerm` checked.
    if method == .matches then continue
    let ta ← typeOf a
    unless ← isDefEq ta (leanTy p) do
      throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
  let a : Term := (args.map (·.1))[0]?.getD (← `(""))
  let b : Term := (args.map (·.1))[1]?.getD (← `(""))
  let term ← match method with
    | .len => `(Fren.Str.len $t)
    | .startsWith => `(Fren.Str.startsWith $t $a)
    | .endsWith => `(Fren.Str.endsWith $t $a)
    | .contains => `(Fren.Str.contains $t $a)
    -- `toTerm` gives the pattern, as a `Fren.Core.Re`.
    | .matches => `(Fren.Core.Re.matches $a $t)
    | .at => `(Fren.Str.«at» $t $a)
    | .slice => `(Fren.Str.slice $t $a $b)
    | .indexOf => `(Fren.Str.indexOf $t $a $b)
    | .replace => `(Fren.Str.replace $t $a $b)
    | .replaceAll => `(Fren.Str.replaceAll $t $a $b)
    | _ => `(Fren.FinSet.card $t)
  return (term, leanTy method.result)

/-- Reads the field `f` of the term `t` of Lean type `ty`; of a `String` or
a set, calls the method `f`, without arguments. -/
def readField (ref : Syntax) (t : Term) (ty : Expr) (f : Name) : TermElabM (Term × Expr) := do
  if ty.isConstOf ``String || (relTypes? ty).isSome || ty.isAppOfArity ``Fren.Seq 1 then
    return ← callMethod ref t ty f.toString #[]
  if ty.isAppOfArity ``Fren.FinSet 1 then
    unless f == `card do throwErrorAt ref (Core.unknownSetMethodMsg f.toString (← typeName ty)).text
    return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
  let some r := ty.constName?.bind (← getState).recordOfDecl?
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  let some (_, ft) := r.fields.find? (·.1 == f)
    | throwErrorAt ref (Core.noFieldMsg f (Core.showPath r.path) (r.fields.map (·.1))).text
  return (← `($(mkCIdentFrom ref (r.decl ++ f)) $t), ft)

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def pathMentions (e : Syntax) : Array Name :=
  if e.isOfKind ``Lang.appExpr then
    -- `x.m(a)` is a method call, which mentions `x`: a function's name has
    -- no dots.
    let recv := match (pathSegs e[0]).toList with
      | [id] => if id.getId.isAtomic then #[] else
        (id.getId.getPrefix.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
      | _ => #[]
    e[2].getSepArgs.foldl (· ++ pathMentions ·) recv
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size == 1 then
      (segs[0]!.getId.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
    else #[]
  else if e.isOfKind ``Lang.recordExpr then
    e[2].getSepArgs.foldl (init := #[]) fun acc b => acc ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
  else e.getArgs.foldl (· ++ pathMentions ·) #[]

/-- The variables that the defined output `v` stands for: those its
definition mentions, through other definitions, transitively. -/
partial def defDeps (vars : Array Var) (v : Var) (seen : Array Name := #[]) : Array Var := Id.run do
  let some d := v.defn? | return #[v]
  let mut out := #[]
  for n in (pathMentions d).toList.eraseDups do
    let some u := vars.find? (·.name == n) | continue
    if seen.contains u.name then continue
    out := out ++ defDeps vars u (seen.push v.name)
  return out

/-- The cycle of definitions through `start`, if any, each mentioning the
next. -/
partial def defCycle? (vars : Array Var) (start : Name) (path : Array Name := #[]) : Option (Array Name) :=
  match (vars.find? (·.name == start)).bind (·.defn?) with
  | none => none
  | some d =>
    let path := path.push start
    (pathMentions d).toList.eraseDups.findSome? fun n =>
      if n == path[0]! then some path
      else if path.contains n then none
      else defCycle? vars n path

/-- A reference to comp variable `n`, if it is one, checking that it may be
mentioned here (`inst::mention`). -/
def varRef? (cx : ExprCtx) (id : Syntax) (n : Name) : TermElabM (Option Term) := do
  let some v := cx.vars.find? (·.name == n) | return none
  -- A defined output mentions what its definition does.
  for u in defDeps cx.vars v do
    let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
    match Core.checkMention cx.place u.role earlier u.name with
    | .ok () => pure ()
    | .error msg => throwErrorAt id (if u.name == n then msg else Core.throughDefinition n msg).text
  return some (mkIdentFrom id n)

/-- The alternatives of a `match` arm's pattern, none for `_`. -/
def patternAlts (arm : Syntax) : Array Syntax :=
  if arm[0].isOfKind ``Lang.altsPattern then arm[0][1].getSepArgs else #[]

/-- The binders of an alternative, `_` included. -/
def altBinders (alt : Syntax) : Array Syntax :=
  if alt[1].isNone then #[] else alt[1][1].getSepArgs.map (·[0])

/-- The binders of a `match` arm's pattern, `_` included: those of its only
alternative, since those of an or-pattern are all `_`. -/
def patternBinders (arm : Syntax) : Array Syntax :=
  match patternAlts arm with
  | #[a] => altBinders a
  | _ => #[]

open Lang in
/-- The expression that is the name `n`, a path of one segment. -/
def pathExpr (ref : Syntax) (n : Name) : TermElabM Syntax := do
  let tmpl ← `(fren_expr| x)
  return tmpl.raw.setArg 0 (mkNode ``Lang.fren_path #[mkNullNode #[mkIdentFrom ref n]])

/-- For `x.m(a)`, an application of a dotted name whose root is a variable
or binder, the receiver `x` and the method `m`. -/
def methodApp? (cx : ExprCtx) (e : Syntax) : Option (Name × Name) := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  let n := segs[0]!.getId
  guard (!n.isAtomic && ((cx.binder? n.getRoot).isSome || cx.vars.any (·.name.getRoot == n.getRoot)
    -- Otherwise a constant's, whose receiver reports what else it is.
    || (!cx.insts.contains n.getRoot && (Core.Method.ofName? n.getString!).isSome)))
  return (n.getPrefix, Name.mkSimple n.getString!)

/-- How many variables `e` mentions, counted with repetition, where `bs`
are the binders of `e` around the subexpression, each with the count of its
scrutinee. A name that is not a variable, such as a constant, is not counted
(`lang::linear_product`). -/
partial def varsMentioned (cx : ExprCtx) (e : Syntax) (bs : Array (Name × Nat) := #[]) : TermElabM Nat := do
  let sum (es : Array Syntax) (bs : Array (Name × Nat)) := es.foldlM (init := 0) fun n a => return n + (← varsMentioned cx a bs)
  if let some (recv, _) := methodApp? cx e then
    -- A method has a fixed meaning, like a variant.
    return (← varsMentioned cx ((← pathExpr e recv)[0]) bs) + (← sum e[2].getSepArgs bs)
  if e.isOfKind ``Lang.appExpr then
    -- A function's value is unknown, like a variable's; a variant's is not.
    let n ← sum e[2].getSepArgs bs
    -- A defined function's value is linear in its arguments'.
    return if (← isVariant cx e[0]) || (← definedFn? cx e[0]).isSome then n else n + 1
  else if e.isOfKind ``Lang.matchExpr then
    let k ← varsMentioned cx e[1] bs
    e[3].getSepArgs.foldlM (init := k) fun n arm => do
      let new := (patternBinders arm).filter (·.isIdent) |>.map (·.getId, k)
      return n + (← varsMentioned cx arm[2] (bs ++ new))
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size != 1 then return 0
    let n := segs[0]!.getId
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then return ← varsMentioned (cx.at b) b.scrutinee
    -- A defined output counts as its definition (acyclic, so this ends).
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return ← varsMentioned { cx with binders := #[] } d
    return if cx.vars.any (·.name.isPrefixOf n) then 1 else 0
  else sum e.getArgs bs

/-- The applications of uninterpreted functions in `e`. -/
partial def applications (cx : ExprCtx) (e : Syntax) : TermElabM (Array Syntax) := do
  let inner ← e.getArgs.foldlM (init := #[]) fun acc a => return acc ++ (← applications cx a)
  if e.isOfKind ``Lang.appExpr && (methodApp? cx e).isNone then
    if !(← isVariant cx e[0]) && (← definedFn? cx e[0]).isNone then return #[e] ++ inner
  return inner

/-- Whether the Lean type of a Fren type has infinitely many values
(`Reqs/Lang/Decidability#outputs`): an abstract type may, so it counts. -/
partial def infiniteType (ty : Expr) : TermElabM Bool := do
  if ty.isConstOf ``Bool then return false
  if ty.isAppOfArity ``Fren.FinSet 1 then return ← infiniteType ty.appArg!
  if ty.isAppOfArity ``Fren.Seq 1 then return true
  if ty.isAppOfArity ``Prod 2 then return (← infiniteType ty.appFn!.appArg!) || (← infiniteType ty.appArg!)
  let s ← getState
  let some d := ty.constName? | return true
  if let some e := s.enumOfDecl? d then return e.unbounded || (← e.payloads.anyM (·.anyM infiniteType))
  if let some r := s.recordOfDecl? d then return r.unbounded || (← r.fields.anyM (infiniteType ·.2))
  return true

/-- Whether `e` mentions an output of an infinite type, directly, through a
definition or through a binder. -/
partial def mentionsInfiniteOutput (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  for n in pathMentions e do
    if let some b := cx.binder? n then
      if ← mentionsInfiniteOutput (cx.at b) b.scrutinee then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    for u in defDeps cx.vars v do
      if u.role == .output && (← infiniteType u.type) then return true
  return false

/-- Whether `e` is a constant: it mentions no variable, binder or
uninterpreted function. -/
def isConstant (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← varsMentioned cx e) == 0

/-- The definition of `e`, if it names a defined output. -/
partial def definitionOf? (cx : ExprCtx) (e : Syntax) : Option Syntax :=
  if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size == 1 then (cx.vars.find? (·.name == segs[0]!.getId)).bind (·.defn?) else none
  else if e.getNumArgs == 1 then definitionOf? cx e[0]
  else if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then definitionOf? cx e[1]
  else none

/-- Whether `e` is a variable, a field read from one, or an application of
an uninterpreted function, which is as unknown as a variable. -/
partial def isVariable (cx : ExprCtx) (e : Syntax) : Bool :=
  if e.isOfKind ``Lang.fren_path then (pathSegs e).size == 1
  -- A path, as an expression.
  else if e.getNumArgs == 1 then isVariable cx e[0]
  else if e.isOfKind ``Lang.fieldExpr then isVariable cx e[0]
  else if e.isOfKind ``Lang.appExpr then (methodApp? cx e).isNone
  else e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" && isVariable cx e[1]

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (ref : Syntax) (c : Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Syntax) (ground : Bool := false) (finiteRange : Bool := true) (literalOperand : Bool := false) :
    TermElabM Unit := do
  let infinite ← operands.anyM (mentionsInfiniteOutput cx)
  unless Core.inCore c constantArgs comparable infinite ground (finiteRange := finiteRange)
      (literalOperand := literalOperand) do
    modifyLocal fun l => { l with outsideCore := true }
    recordLint .undecidable ref (Core.undecidableMsg c infinite)

/-- Reports `undecidable` if the method `m` of the relation type `ty`, with
`operands`, ranges over a type that is not finite
(`Reqs/Lang/Decidability#relations`). -/
def checkRelational (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (operands : Array Syntax) :
    TermElabM Unit := do
  let some (a, b) := relTypes? ty | return
  let tys ← match Core.Method.ofName? m with
    | some .inverse => pure #[a, b]
    | some .closure | some .image | some .range => pure #[a]
    | some .domain => pure #[b]
    | _ => return
  let finite ← tys.allM fun t => return !(← infiniteType t)
  modifyLocal fun l => { l with relationalUsed := true }
  checkCore cx ref .relational true true operands (← operands.allM (isConstant cx ·)) finite

/-- Records a `card`, of the receiver `recv` of Lean type `ty`: in a comp
that applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (recv : Syntax) : TermElabM Unit := do
  if m == "card" && ty.isAppOfArity ``Fren.FinSet 1 && !(← isConstant cx recv) then
    modifyLocal fun l => { l with countRefs := l.countRefs.push ref }

/-- Reports `undecidable` at each count of the current comp, if it also
applies a relational operator; gives whether it does and whether it counts. -/
def checkCounts [Monad m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m] : m (Bool × Bool) := do
  let l ← getLocal
  if l.relationalUsed then
    for r in l.countRefs do
      modifyLocal fun l => { l with outsideCore := true }
      recordLint .undecidable r (Core.undecidableMsg .relationalCard false)
  return (l.relationalUsed, !l.countRefs.isEmpty)

/-- Records what an instance of `c`, written at `ref`, brings to the current
comp's mix of relational operators and counting. -/
def noteCounts [Monad m] [MonadEnv m] (c : CompInfo) (ref : Syntax) : m Unit :=
  modifyLocal fun l => { l with relationalUsed := l.relationalUsed || c.relational
                                countRefs := if c.counts then l.countRefs.push ref else l.countRefs }

/-- Reads the field `f` of the term `t` of Lean type `ty`, which is the dotted
name `id` up to its `k`th component, checking the decidable core. -/
def readPathField (cx : ExprCtx) (id : Syntax) (parts : List Name) (k : Nat) (t : Term) (ty : Expr) (f : Name) :
    TermElabM (Term × Expr) := do
  let recv := (parts.take k).foldl (· ++ ·) .anonymous
  if ty.isConstOf ``String then checkCore cx id .stringAtom true true #[← pathExpr id recv]
  let r ← readField id t ty f
  if (relTypes? ty).isSome then checkRelational cx id ty f.toString #[← pathExpr id recv]
  if let (true, some m) := (ty.isAppOfArity ``Fren.Seq 1, Core.Method.ofName? f.toString) then
    let p ← pathExpr id recv
    checkCore cx id m.seqConstruct true true #[p] (← isConstant cx p)
  checkRelationalCard cx id ty f.toString (← pathExpr id recv)
  return r

/-- `e.f`, a field read or a method without arguments, of the term `t` for
`e`, checking the decidable core. -/
def fieldTerm (cx : ExprCtx) (e : Syntax) (t : Term) : TermElabM Term := do
  let ty ← typeOf t
  if ty.isConstOf ``String then checkCore cx e .stringAtom true true #[e[0]]
  let r ← readField e[2] t ty e[2].getId
  if let (true, some m) := (ty.isAppOfArity ``Fren.Seq 1, Core.Method.ofName? e[2].getId.toString) then
    checkCore cx e m.seqConstruct true true #[e[0]] (← isConstant cx e[0])
  checkRelational cx e ty e[2].getId.toString #[e[0]]
  checkRelationalCard cx e ty e[2].getId.toString e[0]
  return r.1

/-- Whether `e` is a `++`, which is reported as one construct. -/
def isConcat (e : Syntax) : Bool := e.getNumArgs == 3 && e[1].isAtom && e[1].getAtomVal.trimAscii.toString == "++"

/-- Whether `e` contains a `++` that is not a constant, itself or in a
defined output's definition (acyclic, so this ends). -/
partial def hasConcat (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  if isConcat e && !(← isConstant cx e) then return true
  if e.isOfKind ``Lang.fren_path then
    return ← match definitionOf? cx e with | some d => hasConcat cx d | none => pure false
  e.getArgs.anyM (hasConcat cx)

/-- `e` as `nonminimal_bool` sees it, with ranges in characters from `base`
in `str`. Parentheses are dropped, as by the `fren` command's parser. -/
partial def boolNode (str : String) (base : String.Pos.Raw) (e : Syntax) : Core.BNode Syntax :=
  let off (p : String.Pos.Raw) := (String.Pos.Raw.extract str base p).length
  let range : Core.Range := { start := off (e.getPos?.getD base), stop := off (e.getTailPos?.getD base) }
  let go := boolNode str base
  let atom (i : Nat) := if e[i].isAtom then e[i].getAtomVal.trimAscii.toString else ""
  -- `true` and `false` are also paths.
  if e.isOfKind choiceKind then go ((e.getArgs.find? fun a => a.getNumArgs == 1 && a[0].isAtom).getD e[0]) else
  match e.getNumArgs, atom 0, atom 1 with
  | 3, "(", _ => go e[1]
  | 4, "when", _ | 4, "unless", _ => .mk .when range e #[go e[1], go e[3]]
  | 6, "if", _ => .mk .ite range e #[go e[1], go e[3], go e[5]]
  | 2, "not", _ => .mk .not range e #[go e[1]]
  | 2, "-", _ => .mk .neg range e #[go e[1]]
  | 3, _, op => if op.isEmpty then .mk .atom range e #[] else .mk (.bin op) range e #[go e[0], go e[2]]
  | 1, "true", _ => .mk (.lit true) range e #[]
  | 1, "false", _ => .mk (.lit false) range e #[]
  | _, _, _ => .mk .atom range e #[]

/-- Records the `Bool` expressions in `e` that have a simpler form
(`nonminimal_bool`). -/
def lintBools (e : Syntax) : TermElabM Unit := do
  let some sub := e.getSubstring? false false | return
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  for r in Core.simplerBools src (boolNode sub.str sub.startPos e) do
    recordLint .nonminimalBool r.ref (Core.nonminimalMsg r fixable)

open Lang in
/-- Translates a record literal, where `go` translates its values. -/
def recordTerm (go : Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let r ← resolvePath cx.modName (pathSegs e[0]) cx.shadowing
  let .item { kind := .recordItem, path, .. } := r | throwErrorAt e[0] (Core.wrongKindMsg "a record" r).text
  let some info := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
  let given := e[2].getSepArgs
  match Core.checkFieldInits path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (some i, msg) => throwErrorAt given[i]![0] msg.text
  | .error (none, msg) => throwError msg.text
  let args ← info.fields.mapM fun (f, _) => do
    let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
    if b[1].isNone then go (← `(fren_expr| $(⟨b[0]⟩):ident)) else go b[1][1]
  `($(mkCIdentFrom e[0] (recordCtor info.decl)) $args*)

open Lang in
/-- Translates a `match` into a chain of `if`s that compare its scrutinee
with each arm's variant, built from the scrutinee's own payload, where
`toTerm` translates its parts. -/
def matchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let go := toTerm cx
  let scrutinee := e[1]
  let s ← go scrutinee
  let ty ← typeOf s
  let some info := ty.constName?.bind (← getState).enumOfDecl?
    | throwErrorAt scrutinee (Core.scrutineeMsg (← typeName ty)).text
  let arms := e[3].getSepArgs
  -- Each arm's variants, one for each alternative, or `none` for `_`.
  let mut pats : Array (Option (Array Nat)) := #[]
  for arm in arms do
    let alts := patternAlts arm
    if alts.isEmpty then pats := pats.push none; continue
    let mut idxs := #[]
    for p in alts do
      match ← resolvePath cx.modName (pathSegs p[0]) cx.shadowing with
      | .variant en idx =>
        if en.path != info.path then
          throwErrorAt p (Core.notAVariantOfMsg info.path s!"a variant of `{Core.showPath en.path}`").text
        let v := info.path ++ en.variants[idx]!
        let n := info.payloads[idx]!.size
        if p[1].isNone then
          if n > 0 then throwErrorAt p (Core.unappliedVariantMsg v n).text
        else
          let bs := altBinders p
          if n == 0 then throwErrorAt p (Core.noPayloadMsg v).text
          unless bs.size == n do throwErrorAt p (Core.arityMsg v n bs.size "binder").text
          if alts.size > 1 then
            if let some b := bs.find? (·.isIdent) then throwErrorAt b (Core.orBinderMsg b.getId).text
        idxs := idxs.push idx
      | r => throwErrorAt p (Core.notAVariantOfMsg info.path r.describe).text
    pats := pats.push (some idxs)
  match Core.checkArms info.path info.variants (pats.map (·.map (·.map (info.variants[·]!)))) with
  | .ok () => pure ()
  | .error (some (i, some j), msg) => throwErrorAt (patternAlts arms[i]!)[j]! msg.text
  | .error (some (i, none), msg) => throwErrorAt arms[i]![0] msg.text
  | .error (none, msg) => throwError msg.text
  let mut bodies : Array Term := #[]
  -- An arm is evaluated when its pattern matches and no earlier one does.
  let test (idxs : Array Nat) : TermElabM Term := do
    let tests ← idxs.mapM fun idx => do
      let ctor := info.decl ++ info.variants[idx]!
      let sels ← (Array.range info.payloads[idx]!.size).mapM fun k => `($(mkCIdent (selectorName ctor k)) $s)
      `($s = $(mkCIdent ctor) $sels*)
    tests.pop.foldrM (init := tests.back!) fun t acc => `($t ∨ $acc)
  let mut tests : Array (Option Term) := #[]
  for pat in pats do tests := tests.push (← pat.mapM test)
  let mut earlier : Array Term := #[]
  for arm in arms, pat in pats, t? in tests do
    let guards := cx.guards ++ (← earlier.mapM fun t => `(¬$t)) ++ t?.toArray
    earlier := earlier ++ t?.toArray
    let mut new : Array MatchBinder := #[]
    if let some #[idx] := pat then
      let ctor := info.decl ++ info.variants[idx]!
      for b in patternBinders arm, t in info.payloads[idx]!, k in [0:info.payloads[idx]!.size] do
        unless b.isIdent do continue
        let bn := b.getId
        if new.any (·.name == bn) then throwErrorAt b (Core.dupPatternBinderMsg bn).text
        liftMsg b (Core.checkVarName bn (some (t.isConstOf ``Bool)))
        lintName .binder bn b
        new := new.push { name := bn, term := ← `($(mkCIdent (selectorName ctor k)) $s), «type» := t
                          scrutinee, outer := cx.binders.size }
    bodies := bodies.push (← toTerm { cx with binders := cx.binders ++ new, guards } arm[2])
  -- The first arm that matches; the last arm matches whatever is left.
  let mut out := bodies.back!
  for i in (List.range (bodies.size - 1)).reverse do
    if let some t := tests[i]! then
      out ← `(if $t then $(bodies[i]!) else $out)
  return out

/-- Whether `e` is `{}`, which takes its type from where it is written. -/
def isEmptySet (e : Syntax) : Bool := e.isOfKind ``Lang.setExpr && e[1].getSepArgs.isEmpty

/-- The text that `stx` is written with. -/
def srcText (stx : Syntax) : String := ((stx.reprint.getD "").trimAscii).toString

/-- Strips parentheses from `e`. -/
partial def unparen (e : Syntax) : Syntax :=
  if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then unparen e[1] else e

/-- Whether `e` is the binary operator `op`. -/
def isBinOp (e : Syntax) (op : String) : Bool :=
  e.getNumArgs == 3 && e[1].isAtom && e[1].getAtomVal.trimAscii.toString == op

/-- The disjuncts of a chain of `or`, through parentheses, as the `fren`
command's parser, which drops them, sees it. -/
partial def orDisjuncts (e : Syntax) : Array Syntax :=
  let e := unparen e
  if isBinOp e "or" then orDisjuncts e[0] ++ orDisjuncts e[2] else #[e]

/-- The sequences that `e` indexes, as their text. -/
partial def indexedIn (e : Syntax) : Array String :=
  (if e.isOfKind ``Lang.indexExpr then #[srcText e[0]] else #[]) ++ e.getArgs.flatMap indexedIn

/-- Whether `e` bounds the sequence written `q`: it mentions `q.len`, or
compares `q` with `[]` (`lint::index_after_use`). -/
def boundsSeq (e : Syntax) (q : String) : Bool :=
  let t := (srcText e).replace " " ""
  (t.splitOn s!"{q}.len").length > 1 || (t.splitOn s!"{q}!=[]").length > 1 || (t.splitOn s!"{q}=[]").length > 1

/-- The receiver of `a`, if it reads `len` or `card` without arguments, and
whether it reads `card`. -/
def lengthOf? (a : Syntax) : TermElabM (Option (Syntax × Bool)) := do
  if a.isOfKind ``Lang.fieldExpr then
    let f := a[2].getId
    return if f == `len || f == `card then some (a[0], f == `card) else none
  let p := if a.getNumArgs == 1 then a[0] else a
  unless p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 do return none
  let .str pre m := (pathSegs p)[0]!.getId | return none
  if pre.isAnonymous || !(m == "len" || m == "card") then return none
  return some (← pathExpr a pre, m == "card")

/-- `length_zero` and `card_zero` on the comparison `e` (`lint::length_zero`). -/
def lintLength (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let (a, b) := (e[0], e[2])
  let some c := Core.Comparison.ofOp? e[1].getAtomVal.trimAscii.toString | return
  let some d := (if b.getNumArgs == 1 then b[0] else b).isNatLit? | return
  let (fires, empty) := Core.lengthZero c d
  unless fires do return
  let some (recv, card) ← lengthOf? a | return
  -- Only its type: what elaborating it reports is reported where it is.
  let saved ← getLocal
  let some t ← try some <$> typeOf (← toTerm { cx with noteIndexes := false, concatOk := true } recv) catch _ => pure none
    | modifyLocal fun _ => saved
  modifyLocal fun _ => saved
  unless card == t.isAppOfArity ``Fren.FinSet 1 do return
  let emptyText := if t.isConstOf ``String then "\"\"" else if t.isAppOfArity ``Fren.Seq 1 then "[]" else "{}"
  recordLint (if card then .cardZero else .lengthZero) e (Core.lengthZeroMsg card (srcText recv) emptyText empty)

open Lang in
/-- `a = b`, `a != b` and the orderings; on strings, checks the decidable
core, and writes `a > b` as `b < a`, since lean-smt writes `>` on strings
as `str.>`, which is not SMT-LIB. -/
def compareTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  let op := e[1].getAtomVal.trimAscii.toString
  let string (t : Term) : TermElabM Bool := return (← typeOf t).isConstOf ``String
  lintLength toTerm cx e
  let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
  if op == "=" || op == "!=" then
    -- `++` is in the core against a constant.
    let (x, y) := (← toTerm { cx with concatOk := cb, emptyOk := !isEmptySet b } a,
      ← toTerm { cx with concatOk := ca, emptyOk := !isEmptySet a } b)
    -- A side whose definition has a `++` stands for it, and is reported here.
    let named (s : Syntax) : TermElabM Bool := do return (definitionOf? cx s).isSome && (← hasConcat cx s)
    if ((← named a) || (← named b)) && (← string x) then
      checkCore cx e .stringSearch true true #[] (ca || cb)
    else if !isConcat a && !isConcat b && (← string x) then
      checkCore cx e .stringCompare true (ca || cb || (isVariable cx a && isVariable cx b)) #[] (ca && cb)
    return ← if op == "=" then `($x = $y) else `($x ≠ $y)
  let (x, y) := (← toTerm cx a, ← toTerm cx b)
  unless ← string x do
    return ← match op with
      | "<" => `($x < $y) | "<=" => `($x ≤ $y) | ">" => `($x > $y) | _ => `($x ≥ $y)
  checkCore cx e .stringCompare true (ca || cb) #[a, b] (ca && cb)
  match op with
  | "<" => `($x < $y) | "<=" => `($x ≤ $y) | ">" => `($y < $x) | _ => `($y ≤ $x)

/-- Whether `e` is `[]`, which takes its type from where it is written. -/
def isEmptySeq (e : Syntax) : Bool := e.isOfKind ``Lang.seqExpr && e[1].getSepArgs.isEmpty

/-- `a ++ b`, where `concatOk` says whether the core allows it here. -/
def concatTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (concatOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  -- Sequences: outside the core, unless constant.
  let x ← toTerm { cx with concatOk := true, emptyOk := !isEmptySeq b } a
  if (← typeOf x).isAppOfArity ``Fren.Seq 1 then
    let y ← toTerm { cx with emptyOk := true } b
    unless ← isDefEq (← typeOf y) (← typeOf x) do
      throwErrorAt b s!"type mismatch: expected `{← typeName (← typeOf x)}`, found `{← typeName (← typeOf y)}`"
    checkCore cx e .seqWord true true #[a, b] (← isConstant cx e)
    return ← `(($x ++ $y : $(typeSyntax (← typeOf x))))
  -- Where the core allows it, only its operands' outputs matter.
  if concatOk then checkCore cx e .stringAtom true true #[a, b]
  else checkCore cx e .stringSearch true true #[a, b] (← isConstant cx e)
  let y ← toTerm { cx with concatOk := true } b
  for (t, stx) in [(x, a), (y, b)] do
    let ty ← typeOf t
    unless ty.isConstOf ``String do
      throwErrorAt stx s!"type mismatch: expected `String`, found `{← typeName ty}`"
  `(($x ++ $y : String))

/-- `r.m(args)`, a method call on the receiver `recvStx`, whose method's name
is at `ref` (`Reqs/Lang/Expressions#methods`). -/
def methodTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e ref recvStx : Syntax) (m : String)
    (args : Array Syntax) : TermElabM Term := withRef e do
  let r ← toTerm { cx with concatOk := true } recvStx
  let rty ← typeOf r
  let pattern := m == "matches?" && rty.isConstOf ``String
  -- A sequence method's arguments are typed by its parameters, so `[]` may be one.
  let seq := rty.isAppOfArity ``Fren.Seq 1
  let as ← args.mapM fun a => return (← if pattern then patternTerm a else toTerm { cx with emptyOk := seq } a, a)
  if seq then
    let c := (Core.Method.ofName? m).map (·.seqConstruct) |>.getD .seqWord
    checkCore cx e c true true (#[recvStx] ++ args) ((← args.allM (isConstant cx ·)) && (← isConstant cx recvStx))
      (literalOperand := args.any (·.isOfKind ``Lang.seqExpr))
  if rty.isConstOf ``String then
    let constantArgs ← args.allM (isConstant cx ·)
    let c := (Core.Method.ofName? m).map (·.construct) |>.getD .stringAtom
    checkCore cx e c constantArgs true (#[recvStx] ++ args) (constantArgs && (← isConstant cx recvStx))
  let t := (← callMethod ref r rty m as).1
  checkRelational cx e rty m (#[recvStx] ++ args)
  checkRelationalCard cx e rty m recvStx
  return t

/-- `e`, where a pair `(a, b)` may be written: a member of a set literal, or
the left of `in`. -/
def pairOrTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := do
  if e.isOfKind ``Lang.pairExpr then
    let (x, y) := (← toTerm cx e[1], ← toTerm cx e[3])
    -- Typed, so that a pair of numerals is a pair of `Int`s.
    return ← `((($x, $y) : $(typeSyntax (← typeOf x)) × $(typeSyntax (← typeOf y))))
  toTerm cx e

/-- `{a, b}`, or `{}` where `emptyOk` says that something gives it a type. -/
def setLitTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  let elems := e[1].getSepArgs
  if elems.isEmpty then
    unless emptyOk do throwErrorAt e Core.emptySetTypeMsg.text
    return ← `((∅ : Fren.FinSet _))
  checkCore cx e .setAlgebra true true elems
  let xs ← elems.mapM (pairOrTerm toTerm { cx with emptyOk := true })
  `(($(← finSetLit xs) : Fren.FinSet _))

/-- `x in s`, `s subset t`, `s union t`, `s inter t` and `s minus t`. -/
def setOpTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  checkCore cx e .setAlgebra true true #[a, b]
  if e.isOfKind ``Lang.memberExpr then
    if b.isOfKind ``Lang.setExpr && cx.noteIndexes then
      if let #[m] := b[1].getSepArgs then
        unless m.isOfKind ``Lang.pairExpr do recordLint .singletonMembership e (Core.singletonMembershipMsg (srcText a) (srcText m))
    let (x, s) := (← pairOrTerm toTerm cx a, ← toTerm { cx with emptyOk := true } b)
    let (tx, ts) := (← typeOf x, ← typeOf s)
    if ts.isAppOfArity ``Fren.Seq 1 && (← isDefEq ts.appArg! tx) then
      checkCore cx e .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := b.isOfKind ``Lang.seqExpr)
      return ← `($x ∈ $s)
    let ok ← if ts.isAppOfArity ``Fren.FinSet 1 then isDefEq ts.appArg! tx else pure false
    unless ok do
      let set := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) tx
      throwError (Core.membershipTypeMsg (← typeName set) (← typeName ts) (a.isOfKind ``Lang.pairExpr)).text
    return ← `($x ∈ $s)
  let x ← toTerm { cx with emptyOk := !isEmptySet b } a
  let y ← toTerm { cx with emptyOk := !isEmptySet a } b
  if e.isOfKind ``Lang.joinExpr then
    let (tx, ty) := (← typeOf x, ← typeOf y)
    let some (_, mid) := relTypes? tx | throwErrorAt a (Core.joinTypeMsg (← typeName tx) none).text
    let some (mid', _) := relTypes? ty | throwErrorAt e[2] (Core.joinTypeMsg (← typeName ty) none).text
    unless ← isDefEq mid mid' do throwError (Core.joinTypeMsg (← typeName tx) (some (← typeName ty))).text
    modifyLocal fun l => { l with relationalUsed := true }
    checkCore cx e .relational true true #[a, b] ((← isConstant cx a) && (← isConstant cx b)) (!(← infiniteType mid))
    return ← `(Fren.FinSet.join $x $y)
  if e.isOfKind ``Lang.subsetExpr then `($x ⊆ $y)
  else if e.isOfKind ``Lang.unionExpr then `($x ∪ $y)
  else if e.isOfKind ``Lang.interExpr then `($x ∩ $y)
  else `($x \ $y)

/-- How `guardedTerm` joins its operands. -/
inductive Join where
  | implies
  | and
  | or

/-- `when c, d`, `unless c, d` (`negated`), `c and d` or `c or d`, where `d`
is guarded by `c`, or by `not c` if `negated` (`Reqs/Lang/Expressions#sequences`). -/
def guardedTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (c d : Syntax) (negated : Bool)
    (op : Join := .implies) : TermElabM Term := do
  let e ← getRef
  -- `membership_chain`, at the top of a chain of `or` (`lint::membership_chain`).
  if op matches .or && !cx.inOr && cx.noteIndexes then
    let ds := orDisjuncts e
    let eqs := ds.filterMap fun d => let d := unparen d; if isBinOp d "=" then some (d[0], d[2]) else none
    let lefts := eqs.map (srcText ·.1)
    if Core.membershipChainFires ds.size (eqs.size == ds.size && lefts.all (· == lefts[0]!)) then
      recordLint .membershipChain e (Core.membershipChainMsg lefts[0]! (eqs.map (srcText ·.2)))
  -- `index_after_use` (`lint::index_after_use`).
  if op matches .and && cx.noteIndexes then
    if (indexedIn c).any (fun q => boundsSeq d q && !boundsSeq c q) then recordLint .indexAfterUse e (Core.indexAfterUseMsg (srcText c) (srcText d))
  let cx := { cx with inOr := op matches .or }
  let x ← toTerm cx c
  let g ← if negated then `(¬$x) else pure x
  let y ← toTerm { cx with guards := cx.guards.push g } d
  match op with
  | .implies => `($g → $y)
  | .and => `($x ∧ $y)
  | .or => `($x ∨ $y)

/-- Records the index `q[i]` at `ref`, as the terms `q` and `i`, for the
definedness check (`check::definedness`): its guard implies its bounds. -/
def noteIndex (cx : ExprCtx) (ref : Syntax) (q i : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let bounds ← `(0 ≤ $i ∧ $i < Fren.Seq.len $q)
  let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) bounds
  modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- `[a, b]`, or `[]` where `emptyOk` says that something gives it a type. -/
def seqLitTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  let elems := e[1].getSepArgs
  if elems.isEmpty then
    unless emptyOk do throwErrorAt e Core.emptySeqTypeMsg.text
    return ← `((∅ : Fren.Seq _))
  checkCore cx e .seqArray true true elems
  let xs ← elems.mapM (toTerm { cx with emptyOk := true })
  let mut t ← `(Fren.Seq.unit $(xs.back!))
  for x in xs.pop.reverse do t ← `(Fren.Seq.unit $x ++ $t)
  return t

/-- `q[i]`, indexing a sequence. -/
def indexTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e do
  let q ← toTerm cx e[0]
  let tq ← typeOf q
  unless tq.isAppOfArity ``Fren.Seq 1 do throwErrorAt e[0] (Core.notIndexableMsg (← typeName tq)).text
  let i ← toTerm cx e[2]
  let ti ← typeOf i
  unless ti.isConstOf ``Int do throwErrorAt e[2] s!"type mismatch: expected `Int`, found `{← typeName ti}`"
  checkCore cx e .seqArray true true #[e[0], e[2]]
  -- `Fren.Seq.nth` is `default` out of range, which an abstract type's
  -- placeholder does not have.
  let elem := (← instantiateMVars tq).appArg!
  if (← trySynthInstance (mkApp (Lean.mkConst ``Inhabited [Level.one]) elem)) matches .none then
    throwErrorAt e s!"the Lean front end cannot yet index a sequence of `{← typeName elem}`, which has no default value"
  noteIndex cx e q i
  `(Fren.Seq.nth $q $i)

open Lang in
/-- Translates a Fren expression to a Lean term, resolving names with Fren's
rules. Variables become references to locals of the same name; variants
become references to the generated constructors. -/
partial def toTerm (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let concatOk := cx.concatOk
  let emptyOk := cx.emptyOk
  -- Only `or`'s own operands continue its chain.
  let cx := { cx with concatOk := false, emptyOk := false, inOr := cx.inOr && isBinOp (unparen e) "or" }
  let go := toTerm cx
  match e with
  | `(fren_expr| when $c, $d) => guardedTerm toTerm cx c d false
  | `(fren_expr| unless $c, $d) => guardedTerm toTerm cx c d true
  | `(fren_expr| $a iff $b) => `($(← go a) ↔ $(← go b))
  | `(fren_expr| $a or $b) => guardedTerm toTerm cx a b true (op := .or)
  | `(fren_expr| $a and $b) => guardedTerm toTerm cx a b false (op := .and)
  | `(fren_expr| not $a) => `(¬$(← go a))
  | `(fren_expr| if $c then $a else $b) =>
    let c ← go c
    let x ← toTerm { cx with emptyOk := emptyOk || !isEmptySet b, guards := cx.guards.push c } a
    let y ← toTerm { cx with emptyOk := emptyOk || !isEmptySet a, guards := cx.guards.push (← `(¬$c)) } b
    `(if $c then $x else $y)
  | `(fren_expr| $_ = $_) | `(fren_expr| $_ != $_) | `(fren_expr| $_ < $_) | `(fren_expr| $_ <= $_)
  | `(fren_expr| $_ > $_) | `(fren_expr| $_ >= $_) => compareTerm toTerm cx e
  | `(fren_expr| $_ ++ $_) => concatTerm toTerm cx concatOk e
  | `(fren_expr| $s:str) =>
    liftMsg s (Core.checkStringChars s.getString)
    `(Fren.Str.lit $s)
  | `(fren_expr| $a + $b) => `($(← go a) + $(← go b))
  | `(fren_expr| $a - $b) => `($(← go a) - $(← go b))
  | `(fren_expr| $a * $b) =>
    unless Core.productAccepted (← varsMentioned cx a) (← varsMentioned cx b) do
      throwError Core.nonlinearMsg.text
    `($(← go a) * $(← go b))
  | `(fren_expr| -$a) => `(-$(← go a))
  | `(fren_expr| $_ == $_) | `(fren_expr| $_ && $_) | `(fren_expr| $_ || $_) | `(fren_expr| $_ | $_) =>
    throwErrorAt e[1] (Core.foreignOpMsg e[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| !$_) => throwErrorAt e[0] (Core.foreignOpMsg "!").text
  | `(fren_expr| ($a)) => `(($(← toTerm { cx with concatOk } a)))
  | `(fren_expr| $n:num) => `(($n : Int))
  | `(fren_expr| true) => `(true)
  | `(fren_expr| false) => `(false)
  | `(fren_expr| $p:fren_path) =>
    let segs := pathSegs p
    if h : segs.size = 1 then
      let id := segs[0]
      let n := id.getId
      -- A binder or variable, then any fields read from it.
      let base? ← if let some b := cx.binder? n.getRoot then do
          discard (toTerm (cx.at b) b.scrutinee)
          pure (some ((b.term, b.type), n.components.drop 1))
        else
          let ks := (List.range n.components.length).reverse.map (· + 1)
          match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
          | some (v, k) =>
            let some t ← varRef? cx id v.name | throwError "internal error: no variable `{v.name}`"
            pure (some ((t, v.type), n.components.drop k))
          | none =>
            -- A constant, then the methods applied to its value.
            let root := n.getRoot
            if n.isAtomic || cx.insts.contains root then pure none else
            match (← getState).table.resolvePath cx.modName #[root] cx.shadowing with
            | .ok r@(.item { kind := .constItem, path, .. }) =>
              recordUsedItem r
              let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
              let t ← `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
              pure (some ((t, c.type), n.components.drop 1))
            | _ => pure none
      if let some (base, fields) := base? then
        let parts := n.components
        let first := parts.length - fields.length
        return (← fields.zipIdx.foldlM (init := base) fun (t, ty) (f, j) =>
          readPathField cx id parts (first + j) t ty f).1
      unless n.isAtomic do throwErrorAt segs[0] (Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name))).text
    match ← resolvePath cx.modName segs cx.shadowing with
    | .variant en idx =>
      let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
      let n := (info.payloads[idx]?.map (·.size)).getD 0
      if n > 0 then throwError (Core.unappliedVariantMsg (en.path ++ en.variants[idx]!) n).text
      return mkCIdentFrom e (info.decl ++ en.variants[idx]!)
    | .item { kind := .constItem, path, .. } =>
      let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
      -- Its value, not its generated definition (see `Fren.Model`).
      `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
    | .item { kind := .fnItem, path, .. } => throwError (Core.unappliedMsg path).text
    | r => throwError (Core.notAValueMsg r).text
  | `(fren_expr| $p:fren_path($args,*)) =>
    if let some (recv, m) := methodApp? cx e then
      return ← methodTerm toTerm cx e p (← pathExpr p recv) m.toString args.getElems
    let segs := pathSegs p
    if segs.size == 1 && (cx.vars.any (·.name == segs[0]!.getId) || (cx.binder? segs[0]!.getId).isSome) then
      throwErrorAt p (Core.varNotAFunctionMsg segs[0]!.getId).text
    if segs.size == 1 && cx.selfFn == some segs[0]!.getId then
      throwErrorAt p (Core.recursiveMsg (cx.modName ++ segs[0]!.getId)).text
    -- A variable shadows a function, as it does any other item.
    let r ← resolvePath cx.modName (pathSegs p) cx.shadowing
    if let .variant en idx := r then
      -- A variant with a payload, built from its values.
      let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
      let v := en.path ++ en.variants[idx]!
      let n := (info.payloads[idx]?.map (·.size)).getD 0
      if n == 0 then throwError (Core.noPayloadMsg v).text
      unless args.getElems.size == n do throwError (Core.arityMsg v n args.getElems.size "value").text
      let args ← args.getElems.mapM (toTerm { cx with emptyOk := true })
      return ← `($(mkCIdentFrom p (info.decl ++ en.variants[idx]!)) $args*)
    let .item { kind := .fnItem, path, .. } := r | throwErrorAt p (Core.notAFunctionMsg r).text
    if let some d := (← getState).defined.get? path then
      -- Its definition, applied to the placeholders it uses; its arguments
      -- may mention anything (`lang::argument`).
      unless args.getElems.size == d.nParams do throwError (Core.arityMsg path d.nParams args.getElems.size).text
      let args ← args.getElems.mapM (toTerm { cx with emptyOk := true })
      return ← `($(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*)
    if cx.selfFn.isSome then throwErrorAt p (Core.appliesUninterpretedMsg path).text
    let a ← placeholderOf path
    let nParams := (← getConstInfo a.placeholder).type.getForallArity
    unless args.getElems.size == nParams do throwError (Core.arityMsg path nParams args.getElems.size).text
    -- Outputs may not occur in arguments (`inst::mention`); assumptions and
    -- bindings exclude them already.
    let acx := if cx.place == .prop then { cx with place := .argument } else cx
    let args ← args.getElems.mapM (toTerm { acx with emptyOk := true })
    `($(mkCIdentFrom p a.placeholder) $args*)
  | _ =>
    if e.isOfKind ``Lang.fieldExpr then
      return ← fieldTerm cx e (← toTerm { cx with concatOk := true } e[0])
    else if e.isOfKind ``Lang.methodExpr then
      -- `at` is a keyword of Lean's.
      let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
      let m := if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString
      methodTerm toTerm cx e e[2] e[0] m e[4].getSepArgs
    else if e.isOfKind ``Lang.setExpr then setLitTerm toTerm cx emptyOk e
    else if e.isOfKind ``Lang.memberExpr || e.isOfKind ``Lang.subsetExpr || e.isOfKind ``Lang.unionExpr
        || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr || e.isOfKind ``Lang.joinExpr then setOpTerm toTerm cx e
    else if e.isOfKind ``Lang.pairExpr then throwError Core.pairPlaceMsg.text
    else if e.isOfKind ``Lang.seqExpr then seqLitTerm toTerm cx emptyOk e
    else if e.isOfKind ``Lang.indexExpr then indexTerm toTerm cx e
    else if e.isOfKind ``Lang.recordExpr then recordTerm (toTerm { cx with emptyOk := true }) cx e
    else if e.isOfKind ``Lang.matchExpr then matchTerm toTerm cx e
    else throwError "unsupported Fren expression"

open Lang in
/-- The conditions of a top-level `when`/`unless` chain, as a term, and a
syntax node spanning them. -/
partial def triggerOf (cx : ExprCtx) (e : Syntax) : TermElabM (Option (Term × Syntax)) := do
  let (cond, neg, body) ← match e with
    | `(fren_expr| when $c, $d) => pure (c, false, d)
    | `(fren_expr| unless $c, $d) => pure (c, true, d)
    | `(fren_expr| ($a)) => return ← triggerOf cx a
    | _ => return none
  let c ← toTerm { cx with noteIndexes := false } cond
  let c ← if neg then `(¬$c) else pure c
  match ← triggerOf cx body with
  | none => return some (c, mkNullNode #[e[0], cond])
  | some (t, ref) => return some (← `($c ∧ $t), mkNullNode #[e[0], ref])

/-- Elaborates a proposition. Errors are not recovered from with `sorry`: an
item that does not elaborate makes its comp fail, rather than being checked
as `sorry`. -/
def elabProp (t : Term) (type : Expr := mkSort .zero) : TermElabM Expr := do
  -- Equality on an abstract type has no `Decidable` instance but the
  -- classical one, which `if` may need.
  let t ← `(open Classical in $t)
  let e ← withoutErrToSorry <| withSynthesize <| elabTermEnsuringType t type
  let e ← instantiateMVars e
  if e.hasMVar || e.hasSorry then throwErrorAt t "could not elaborate this expression"
  return e

/-- The indexes recorded since the last call, which it forgets, each with its
goal elaborated, rewritten by `subst`, and closed over `fvs`. -/
def takeIndexes (fvs : Array Expr) (subst : Expr → Expr := id) : TermElabM (Array (Syntax × Expr)) := do
  let xs := (← getLocal).indexes
  modifyLocal fun l => { l with indexes := #[] }
  xs.mapM fun (ref, g) => return (ref, ← mkLambdaFVars fvs (subst (← elabProp g)))

/-- Adds the definition `name` of the closed `value`, generalized over the
placeholders `uses` (`Reqs/Generated#components`). -/
def addUsesDef (uses : Array Name) (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← inferType value
  let (type, value) ← withUses uses fun xs => do
    return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs value))
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  -- Reducible, like `abbrev`, so that instances such as `Decidable` see
  -- through them.
  setReducibleAttribute name

/-! ## Abstract types and functions -/

/-- Declares the placeholder for the abstract type or function at `path`
(`AbstractInfo`). -/
def declarePlaceholder (path : Name) (type : Expr) (isType : Bool) : TermElabM Unit := do
  let placeholder := placeholderName path
  addDecl (.axiomDecl { name := placeholder, levelParams := [], type, isUnsafe := false })
  let s ← getState
  let deps := type.foldConsts #[] fun c acc => if s.placeholders.contains c && !acc.contains c then acc.push c else acc
  record (.abstractInfo { path, placeholder, isType, deps })
  -- An abstract type has a value, so its placeholder has an `Inhabited`
  -- instance, itself a placeholder, which an index of a sequence of it
  -- needs; an implementation gives the interpretation's own.
  if isType then
    let inst := inhabitedName placeholder
    let instType := mkApp (Lean.mkConst ``Inhabited [Level.one]) (Lean.mkConst placeholder)
    addDecl (.axiomDecl { name := inst, levelParams := [], type := instType, isUnsafe := false })
    addInstance inst .global 1000
    record (.abstractInfo { path := inhabitedName path, placeholder := inst, isType := false, deps := #[placeholder] })

@[command_elab Lang.typeCmd] def elabAbstractType : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "abstract type" nameStx
  checkFresh modName n nameStx
  lintName .abstractType n nameStx
  let path := modName ++ n
  liftTermElabM <| declarePlaceholder path (mkSort (.succ .zero)) true
  record (.item { item := { kind := .typeItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .abstractType path nameStx

@[command_elab Lang.fnCmd] def elabFunction : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← segName nameStx
  checkFresh modName n nameStx
  lintName .function n nameStx
  let path := modName ++ n
  let params := stx[4].getSepArgs
  let body? := if stx[7].isNone then none else some stx[7][1]
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Syntax) := !p[1].isNone ||
    (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (pathSegs q)[0]!.getId.toString.endsWith "?"
  let nNamed := (params.filter named).size
  unless Core.functionParamsAccepted body?.isSome params.size nNamed do
    let bad := params.find? (named · != body?.isSome) |>.getD nameStx
    throwErrorAt bad (Core.functionParamsMsg path body?.isSome).text
  let some body := body? | do
    liftTermElabM do
      let params ← params.mapM fun p => elabType modName p[0]
      -- As for a variable, with the result type (`lang::bool_naming`).
      let result ← varType modName nameStx (if stx[6].isNone then none else some stx[6][1])
      declarePlaceholder path (← mkArrowN params result) false
    record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
    unless isPub do recordItem .function path nameStx
  let decl := (← getCurrNamespace) ++ path
  liftTermElabM do
    -- The parameters, declared like a comp's inputs.
    let mut vars : Array Var := #[]
    for p in params do
      let some q := typePath? p[0] | throwErrorAt p[0] (Core.functionParamsMsg path true).text
      let x := (pathSegs q)[0]!
      if vars.any (·.name == x.getId) then throwErrorAt x (Core.dupParamMsg x.getId).text
      lintName .variable x.getId x
      let ty ← varType modName x (if p[1].isNone then none else some p[1][1])
      vars := vars.push { name := x.getId, role := .input, isPub := true, «type» := ty, ref := x }
    let result ← varType modName nameStx (if stx[6].isNone then none else some stx[6][1])
    let lam ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let cx : ExprCtx := { modName, vars, insts := #[], place := .prop, selfFn := some n }
      let t ← toTerm cx body
      -- A `Bool` body is decided, classically if need be: equality on an
      -- abstract type has no other `Decidable` instance.
      let value ← if result.isConstOf ``Bool then do
          let p ← elabProp t
          let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
            | .some i => pure i
            | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
          pure (mkApp2 (mkConst ``Decidable.decide) p inst)
        else elabProp t result
      mkLambdaFVars fvs value
    lintBools body
    for (x, v) in Core.unmentioned (vars.map fun v => (v.name, v)) ((pathMentions body).map (·.getRoot)) do
      recordLint .unusedVariables v.ref (Core.unusedParamMsg x)
    let uses ← usesOf #[lam]
    addUsesDef uses decl lam
    record (.definedInfo { path, decl, uses, nParams := vars.size })
  record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .function path nameStx
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))

/-- An instance whose comp has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Name
  ref : Syntax
  comp : CompInfo
  /-- `fren_binding`s. -/
  bindings : Array Syntax
  /-- Where its variables start among the instantiating comp's. -/
  offset : Nat

/-- Resolves `inst x: p { bs }`: the instantiated comp, the instance's
variables, and the names it binds (`inst::binding`). -/
def resolveInst (modName : Name) (x p : Syntax) (bs : Array Syntax) (offset : Nat) :
    TermElabM (PendingInst × Array Var) := do
  liftMsg x (Core.checkItemName "instance" x.getId)
  let r ← resolvePath modName (pathSegs p)
  let .item { kind := .compItem, path, .. } := r | throwErrorAt p (Core.notACompMsg r).text
  let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
  unless c.decidable do
    modifyLocal fun l => { l with outsideCore := true }
    recordLint .undecidable p (Core.undecidableInstMsg path)
  noteCounts c p
  let own := c.vars.filterMap fun v =>
    if v.role == .input || v.role == .output then some (v.name, v.role) else none
  match Core.checkBindings path own (bs.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (some i, msg) => throwErrorAt bs[i]![0] msg.text
  | .error (none, msg) => throwErrorAt x msg.text
  let w := x.getId
  let vars := c.vars.map fun v =>
    let role := Core.Role.ofInst v.role v.isPub
    { name := w ++ v.name, role, isPub := role == .instOutput, type := v.type, ref := x : Var }
  return ({ name := w, ref := x, comp := c, bindings := bs, offset }, vars)

open Lang in
/-- The equations made by the bindings of an instance, over the comp's
variables `fvs`. -/
def elabBindings (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) : TermElabM Expr := do
  let mut eqs := #[]
  for b in pi.bindings do
    let x := b[0]
    let t ← if b[1].isNone then toTerm cx (← `(fren_expr| $(⟨x⟩):ident)) else toTerm { cx with emptyOk := true } b[1][1]
    unless b[1].isNone do lintBools b[1][1]
    let some idx := cx.vars.findIdx? (·.name == pi.name ++ x.getId)
      | throwError "internal error: no variable for `{x.getId}`"
    let fv := fvs[idx]!
    eqs := eqs.push (← mkEq fv (← elabProp t (← inferType fv)))
  return mkAndN eqs.toList

/-- Elaborates an instance, and the body over `fvs` of the definition `decl`
generated for it. -/
def elabInst (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) (decl : Name) : TermElabM (InstInfo × Expr) := do
  let bindings ← elabBindings cx fvs pi
  let slice := fvs.extract pi.offset (pi.offset + pi.comp.vars.size)
  let behaviour := pi.comp.meaning slice
  return (·, mkAnd bindings (pi.comp.meaningDecl slice)) {
    name := pi.name, comp := pi.comp.path, ref := pi.ref, decl
    bindings := ← mkLambdaFVars fvs bindings
    behaviour := ← mkLambdaFVars fvs behaviour
    assumes := ← pi.comp.assumes.mapM fun a => return (a.name, ← mkLambdaFVars fvs (a.body.beta slice)) }

open Lang in
@[command_elab Lang.compCmd] def elabComp : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "component" nameStx
  checkFresh modName n nameStx
  lintName .component n nameStx
  let path := modName ++ n
  let declBase := (← getCurrNamespace) ++ path
  let members := stx[4].getArgs
  -- Its `use`s, and the scope that its paths resolve in.
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, relationalUsed := false, countRefs := #[] }
  let (ok, generated) ← liftTermElabM do
    let mut ok := true
    let mut generated : Array Name := #[]
    let mut names : NameSet := {}
    -- Variables
    let mut vars : Array Var := #[]
    for m in members do
      let (role, isPub, isDet, x, ty?, defn?) ← match m.getKind with
        | ``Lang.inMember =>
          unless m[3].isNone do
            logErrorAt m[3][0] Core.inputDefinitionMsg.text
            ok := false
          pure (Core.Role.input, true, false, m[1], if m[2].isNone then none else some m[2][1], none)
        | ``Lang.outMember =>
          pure (.output, !m[0].isNone, !m[1].isNone, m[3], if m[4].isNone then none else some m[4][1],
            if m[5].isNone then none else some m[5][1])
        | _ => continue
      if names.contains x.getId then
        logErrorAt x (Core.dupMemberMsg x.getId).text; ok := false; continue
      names := names.insert x.getId
      lintName .variable x.getId x
      if let some c := (← getState).table.shadowedConstant? scope x.getId then
        recordLint .shadowedConstants x (Core.shadowedMsg x.getId c)
      try
        let ty ← varType scope x ty?
        let st ← getState
        unless Core.variableTypeAccepted (role == .output) (st.unbounded ty) defn?.isSome do
          throwErrorAt x (Core.unboundedOutputMsg x.getId (← typeName ty)).text
        vars := vars.push { name := x.getId, role, isPub, isDet, «type» := ty, ref := x, defn? }
      catch ex => logException ex; ok := false
    -- One cycle is reported, as by the `fren` command.
    if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
      logErrorAt v.ref (Core.cyclicDefinitionMsg cycle).text; ok := false
    let ok' := ok
    unless ok' do return (false, #[])
    -- Instances, whose variables follow the comp's own
    let mut pending : Array PendingInst := #[]
    for m in members do
      let `(fren_member| inst $x:ident : $p:fren_path { $bs,* }) := m | continue
      if names.contains x.getId then
        logErrorAt x (Core.dupMemberMsg x.getId).text; ok := false; continue
      names := names.insert x.getId
      lintName .instance x.getId x
      try
        let (pi, ivars) ← resolveInst scope x p bs.getElems vars.size
        pending := pending.push pi
        vars := vars ++ ivars
      catch ex => logException ex; ok := false
    let instNames := pending.map (·.name)
    -- Bindings; assumptions, requirements and expectations
    let decls := vars.map fun v => (v.name, fun _ => pure v.type)
    let varsOk := ok
    let varNames := names
    let (props, insts, uses, values, indexes, propsOk) ← withLocalDeclsD decls fun fvs => do
      let mut good := varsOk
      let mut insts : Array InstInfo := #[]
      let mut indexes : Array (Name × Core.IndexPlace × Syntax × Expr) := #[]
      discard (takeIndexes fvs)
      -- The generated definitions, over `fvs`, added once the placeholders
      -- that they use are known.
      let mut defs : Array (Name × Expr) := #[]
      for pi in pending, k in [0:pending.size] do
        try
          let cx := { modName := scope, vars, insts := instNames, place := .binding, current := k }
          let (i, body) ← elabInst cx fvs pi (declBase ++ `inst ++ pi.name)
          insts := insts.push i
          defs := defs.push (i.decl, body)
          indexes := indexes ++ (← takeIndexes fvs).map fun (r, g) => (pi.name, .binding k, r, g)
        catch ex => logException ex; good := false
      -- Definitions, each after those it mentions, with the earlier ones
      -- substituted, so that each value mentions no defined output.
      let mut values : Array (Name × Expr) := #[]
      let mut todo := vars.filter (·.defn?.isSome)
      let mut defnFvs : Array Expr := #[]
      while !todo.isEmpty do
        let some v := todo.find? fun v => (pathMentions v.defn?.get!).all fun n => !todo.any (·.name == n)
          | break
        todo := todo.filter (·.name != v.name)
        let some idx := vars.findIdx? (·.name == v.name) | continue
        try
          let e := v.defn?.get!
          discard (takeIndexes fvs)
          let value ← withRef e do
            -- A definition assigns once and acyclically, so `++` is in the core in it.
            elabProp (← toTerm { modName := scope, vars, insts := instNames, place := .prop, emptyOk := true, concatOk := true } e) v.type
          indexes := indexes ++ (← takeIndexes fvs).map fun (r, g) => (v.name, .prop, r, g)
          lintBools e
          let value := value.replaceFVars defnFvs (values.map (·.2))
          defs := defs.push (declBase ++ `def ++ v.name, ← mkEq fvs[idx]! value)
          values := values.push (v.name, value)
          defnFvs := defnFvs.push fvs[idx]!
        catch ex => logException ex; good := false
      let mut names := varNames
      let mut props : Array PropInfo := #[]
      for m in members do
        let (kind, x, e) ← match m with
          | `(fren_member| assume $x:ident : $e) => pure (PropKind.assume, x, e)
          | `(fren_member| req $x:ident : $e) => pure (.req, x, e)
          | `(fren_member| expect $x:ident : $e) => pure (.expect, x, e)
          | _ => continue
        if names.contains x.getId then
          logErrorAt x (Core.dupMemberMsg x.getId).text; good := false; continue
        names := names.insert x.getId
        lintName .constraint x.getId x
        try
          if x.getId.toString.endsWith "?" then
            throwErrorAt x (Core.propNameMsg x.getId).text
          let cx := { modName := scope, vars, insts := instNames, place := if kind == .assume then .assume else .prop }
          discard (takeIndexes fvs)
          let body ← elabProp (← toTerm cx e)
          -- An assumption sees defined outputs only as their definitions.
          let subst (b : Expr) := if kind == .assume then b.replaceFVars defnFvs (values.map (·.2)) else b
          let body := subst body
          let place : Core.IndexPlace := if kind == .assume then .assume else .prop
          indexes := indexes ++ (← takeIndexes fvs subst).map fun (r, g) => (x.getId, place, r, g)
          lintBools e
          let trig ← triggerOf cx e
          let trigger? ← trig.mapM fun (t, _) => do mkLambdaFVars fvs (← elabProp t)
          let decl := declBase ++ Name.mkSimple kind.keyword ++ x.getId
          defs := defs.push (decl, body)
          props := props.push {
            kind, name := x.getId, ref := x, body := ← mkLambdaFVars fvs body,
            trigger?, triggerRef? := trig.map (·.2), decl }
        catch ex => logException ex; good := false
      -- `constant_output` and `definable_output` (`lint::output_lints`).
      let lcx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop }
      let reqs := members.filterMap fun m => match m with
        | `(fren_member| req $x:ident : $e) => some (x.getId, e.raw)
        | _ => none
      for v in vars.filter (fun v => v.role == .output && v.name.isAtomic) do
        let about := reqs.filter fun (_, e) => (pathMentions e).contains v.name
        let isX (e : Syntax) : Bool :=
          let e := unparen e
          let p := if e.getNumArgs == 1 then e[0] else e
          p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 && (pathSegs p)[0]!.getId == v.name
        -- The only requirement that mentions it, as `x = e` or `x? iff e`, with `e` other variables'.
        let equation := match about with
          | #[(_, e)] =>
            let e := unparen e
            (isBinOp e "=" || isBinOp e "iff")
              && ((isX e[0] && !(pathMentions e[2]).contains v.name) || (isX e[2] && !(pathMentions e[0]).contains v.name))
          | _ => false
        let nVars ← match v.defn? with | some d => varsMentioned lcx d | none => pure 1
        let (constant, definable) := Core.outputLints v.defn?.isSome nVars about.size equation
        if constant then recordLint .constantOutput v.ref (Core.constantOutputMsg v.name)
        if definable then recordLint .definableOutput v.ref (Core.definableOutputMsg v.name about[0]!.1)
      let uses ← usesOf ((← fvs.mapM fun x => inferType x) ++ defs.map (·.2))
      if good then
        let appD (decl : Name) := mkAppN (Lean.mkConst decl) (uses.map (Lean.mkConst ·) ++ fvs)
        let app (p : PropInfo) := appD p.decl
        unless values.isEmpty do
          defs := defs.push (declBase ++ `defs, mkAndN (values.map fun (d, _) => appD (declBase ++ `def ++ d)).toList)
        defs := defs ++ #[(declBase ++ `assumes, mkAndN (props.filter (·.kind == .assume) |>.map app).toList),
          (declBase ++ `reqs, mkAndN (props.filter (·.kind == .req) |>.map app).toList)]
        for (decl, body) in defs do
          addUsesDef uses decl (← mkLambdaFVars fvs body)
        -- `p.out.d`, a function of the inputs, when the definition mentions
        -- only inputs.
        let inputs := (vars.zip fvs).filter (·.1.role == .input) |>.map (·.2)
        for (d, value) in values do
          let others := fvs.filter (!inputs.contains ·)
          unless others.any (value.containsFVar ·.fvarId!) do
            addUsesDef uses (declBase ++ `out ++ d) (← mkLambdaFVars inputs value)
      let closed ← values.mapM fun (d, v) => return (d, ← mkLambdaFVars fvs v)
      return (props, insts, uses, closed, indexes, good)
    ok := propsOk
    if ok then
      let mut mentioned := #[]
      for m in members do
        match m with
        | `(fren_member| inst $_:ident : $_:fren_path { $bs,* }) =>
          for b in bs.getElems do
            let b := b.raw
            mentioned := mentioned ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
        | `(fren_member| assume $_:ident : $e) | `(fren_member| req $_:ident : $e)
        | `(fren_member| expect $_:ident : $e) => mentioned := mentioned ++ pathMentions e
        | _ => pure ()
      for v in vars do
        if let some d := v.defn? then mentioned := mentioned ++ pathMentions d
      -- A public definition says what the output is, so it is used.
      let own := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
      for (x, v) in Core.unmentioned (own.map fun v => (v.name, v)) mentioned do
        recordLint .unusedVariables v.ref (Core.unusedVariableMsg x false (v.role == .output))
    generated := insts.map (·.decl) ++ props.map (·.decl) ++ #[declBase ++ `assumes, declBase ++ `reqs]
      ++ values.map (declBase ++ `def ++ ·.1) ++ (if values.isEmpty then #[] else #[declBase ++ `defs])
    let env ← getEnv
    generated := generated ++ (values.map (declBase ++ `out ++ ·.1)).filter env.contains
    if ok then
      record (.item { item := { kind := .compItem, path, isPub, owner := modName }, ref := nameStx })
      let (relational, counts) ← checkCounts
      record (.compInfo { path, vars, props, insts, ref := nameStx, decl := declBase, uses, defs := values
                          decidable := !(← getLocal).outsideCore, relational, counts, indexes })
    return (ok, generated)
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with comps := l.comps.push path }

/-! ## Constants and global expectations -/

@[command_elab Lang.constCmd] def elabConst : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← segName nameStx
  liftMsg nameStx (Core.checkConstName n)
  checkFresh modName n nameStx
  lintName .constant n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  liftTermElabM do
    let type ← elabType modName stx[4]
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := (← getState).placeholders.contains type.constName
    unless Core.constantAccepted abstract false do
      throwErrorAt stx[4] (Core.unknownConstantMsg abstract).text
    let value ← elabProp (← toTerm { modName, vars := #[], insts := #[], place := .prop, emptyOk := true } stx[6]) type
    let applies ← applications { modName, vars := #[], insts := #[], place := .prop } stx[6]
    unless Core.constantAccepted abstract !applies.isEmpty do
      throwErrorAt applies[0]! (Core.unknownConstantMsg abstract).text
    lintBools stx[6]
    addDecl (.defnDecl { name := decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
    record (.item { item := { kind := .constItem, path, isPub, owner := modName }, ref := nameStx })
    record (.constInfo { path, decl, type, value })
    unless isPub do recordItem .constant path nameStx
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))

/-- A binder of a global expectation: its name and comp, and where its
variables start among the expectation's. -/
structure Binder where
  name : Name
  ref : Syntax
  comp : CompInfo
  offset : Nat

/-- Elaborates a global expectation into a `CompInfo` whose path is its
module (`Model.Entry.globalInfo`), generating `decl` for it. -/
def elabGlobalInfo (modName n : Name) (nameStx : Syntax) (binderStxs : Array Syntax) (body : Syntax)
    (decl : Name) : TermElabM CompInfo := do
  let mut vars : Array Var := #[]
  let mut binders : Array Binder := #[]
  modifyLocal fun l => { l with outsideCore := false, relationalUsed := false, countRefs := #[] }
  for b in binderStxs do
    let r ← resolvePath modName (pathSegs b[3])
    let .item { kind := .compItem, path, .. } := r | throwErrorAt b[3] (Core.notACompMsg r).text
    let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
    unless c.decidable do
      modifyLocal fun l => { l with outsideCore := true }
      recordLint .undecidable b[3] (Core.undecidableInstMsg path)
    noteCounts c b[3]
    for x in b[1].getArgs do
      let w := x.getId
      liftMsg x (Core.checkItemName "instance" w)
      if binders.any (·.name == w) then throwErrorAt x (Core.dupBinderMsg w).text
      lintName .instance w x
      binders := binders.push { name := w, ref := x, comp := c, offset := vars.size }
      -- Like an instance's, but its inputs are shown in counterexamples.
      vars := vars ++ c.vars.map fun v =>
        let role := Core.Role.ofInst v.role v.isPub
        { name := w ++ v.name, role, isPub := role != .instHidden, type := v.type, ref := x : Var }
  withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
    let cx : ExprCtx := { modName, vars, insts := binders.map (·.name), place := .prop }
    discard (takeIndexes fvs)
    let e ← elabProp (← toTerm cx body)
    let indexes := (← takeIndexes fvs).map fun (r, g) => (n, Core.IndexPlace.prop, r, g)
    lintBools body
    for (w, ref) in Core.unmentioned (binders.map fun b => (b.name, b.ref)) ((pathMentions body).map (·.getRoot)) do
      recordLint .unusedVariables ref (Core.unusedVariableMsg w true false)
    let trig ← triggerOf cx body
    let trigger? ← trig.mapM fun (t, _) => do mkLambdaFVars fvs (← elabProp t)
    let slice (b : Binder) := fvs.extract b.offset (b.offset + b.comp.vars.size)
    let hyps := mkAndN (binders.map fun b => b.comp.meaningDecl (slice b)).toList
    let value ← mkForallFVars fvs (← mkArrow hyps e)
    let uses ← usesOf #[value]
    addUsesDef uses decl value
    let insts ← binders.mapM fun b => do
      return { name := b.name, comp := b.comp.path, ref := b.ref, decl
               bindings := ← mkLambdaFVars fvs (mkConst ``True)
               behaviour := ← mkLambdaFVars fvs (b.comp.meaning (slice b))
               -- Hypotheses, not obligations (`Reqs/Lang/Global`).
               assumes := #[] : InstInfo }
    let prop : PropInfo := {
      kind := .expect, name := n, ref := nameStx, body := ← mkLambdaFVars fvs e
      trigger?, triggerRef? := trig.map (·.2), decl }
    discard checkCounts
    return { path := modName, vars, props := #[prop], insts, ref := nameStx, decl, uses
             decidable := !(← getLocal).outsideCore, indexes }

@[command_elab Lang.globalCmd] def elabGlobal : CommandElab := fun stx => do
  checkIdentifiers stx
  let modName := (← getLocal).currentModule
  let nameStx := stx[1]
  let n ← segName nameStx
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let binders := if stx[3].isNone then #[] else stx[3][1].getArgs
  let info ← liftTermElabM <| elabGlobalInfo modName n nameStx binders stx[4] decl
  record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
  record (.globalInfo path info)
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  modifyLocal fun l => { l with globals := l.globals.push path }

end Fren
