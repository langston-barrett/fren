-- keep-sorted start
import Fren.FinSet
import Fren.Finite
import Fren.Model
import Fren.Resolve
import Fren.SimpSet
import Fren.Syntax
import FrenCore.Checking
import FrenCore.Guards
import FrenCore.Lexical
import FrenCore.Mentions
import FrenCore.Regex
import FrenCore.Syntax
import FrenCore.Ty
import FrenCore.Typing
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

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of this
-- file's hundreds of indexes. This rule, tried first, proves it at once, and fails
-- at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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

open Lang in
/-- Reports the first identifier or integer literal of `stx` that Lean read
but that is not one of Fren's (`lang::identifier`,
`lang::integer_literal`), or prefix `!`, as the `fren` command's lexer
does. -/
partial def checkLexemes (stx : Syntax) : CommandElabM Unit := do
  if let `(fren_expr| !$_) := stx then throwErrorAt stx[0] (Core.foreignOpMsg "!").text
  match stx with
  | .ident _ raw _ _ =>
    let s := raw.toString
    let beforeEq := String.Pos.Raw.get raw.str raw.stopPos == '='
    unless Core.identifierAccepted s do throwErrorAt stx (Core.leanIdentifierMsg s beforeEq).text
  | .node _ k args =>
    if k == numLitKind then
      if let some s := stx.isLit? numLitKind then
        unless Core.integerLiteral s && (Core.integerValue? s).isSome do
          throwErrorAt stx (Core.malformedIntegerMsg s).text
    else args.forM checkLexemes
  | _ => pure ()

open Lang in
/-- Reports the first problem of `stx` that the `fren` command's parser
reports, in source order, before any other check of its item, where Lean's
grammar accepts it:
- a name that is not a single segment. A name may be dotted only where it
  is an expression's whole path, which reads an instance's variable or a
  value's field or method, or where it follows `.`, or names an option;
- a member's `set_option` of an option other than `fren.evidence`;
- an input's definition, `in x := e`, before its expression is read;
- an operator of another language, `==`, `&&`, `||` or `|`, after its
  left operand. -/
partial def checkParsed (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(fren_expr| $a == $_) | `(fren_expr| $a && $_) | `(fren_expr| $a || $_) | `(fren_expr| $a | $_) =>
    checkParsed a
    throwErrorAt stx[1] (Core.foreignOpMsg stx[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| $p:fren_path) => unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
  | `(fren_expr| $p:fren_path($args,*)) =>
    unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
    args.getElems.forM checkParsed
  | _ =>
    if stx.isIdent then discard (segName stx)
    else if stx.isOfKind ``Lang.fren_path then discard (segNames (pathSegs stx))
    else if stx.isOfKind ``Lang.evidenceMember then
      unless stx[1].getId == `fren.evidence do
        throwErrorAt stx[1] (Core.memberOptionMsg stx[1].getId.toString).text
      checkParsed stx[4]
    else if stx.isOfKind ``Lang.inMember then
      checkParsed stx[1]
      checkParsed stx[2]
      unless stx[3].isNone do throwErrorAt stx[3][0] Core.inputDefinitionMsg.text
    else if stx.isOfKind ``Lang.fieldExpr || stx.isOfKind ``Lang.methodExpr then
      stx.getArgs.forM fun a => unless a.isIdent do checkParsed a
    else stx.getArgs.forM checkParsed

@[command_elab Lang.modCmd] def elabMod : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let segs := pathSegs stx[2]
  -- A path that did not parse, as in `mod 2`, which Lean has reported.
  if segs.isEmpty || segs.any (·.getId.isAnonymous) then return
  let names ← segNames segs
  let (path, new) ← liftResolve segs ((← getState).table.declareModule names (!stx[0].isNone))
  for i in new do
    let ref := (segs[i.path.components.length - 1]?).getD stx
    lintName .module (Name.mkSimple i.path.getString!) ref
    if let some msg := Core.moduleInceptionMsg? i.path then recordLint .moduleInception ref msg
    record (.item { item := i, ref })
  modifyLocal ({ · with currentModule := path })

/-- Imports the path `segs`, written at `ref`, into the current module, or,
with `scope`, into the component of that path. -/
def declareUse (segs : Array Syntax) (glob : Bool) (ref : Syntax) (scope : Option Name := none) : CommandElabM Unit := do
  let modName := (← getLocal).currentModule
  let u ← liftResolve segs ((← getState).table.declareUse modName (← segNames segs) glob (scope.getD modName))
  record (.useDef u)
  recordUse u ref

@[command_elab Lang.useCmd] def elabUse : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  declareUse (pathSegs stx[1]) (!stx[2].isNone) stx[1]

@[command_elab Lang.useGroupCmd] def elabUseGroup : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  for p in stx[3].getSepArgs do
    declareUse (pathSegs stx[1] ++ pathSegs p) false p

/-- The path of a type written as one, or `none` for `Set(T)` and `Rel(A, B)`. -/
def typePath? (ty : Syntax) : Option Syntax :=
  if ty.isOfKind ``Lang.fren_path then some ty
  else if ty.isOfKind ``Lang.setType || ty.isOfKind ``Lang.relType || ty.isOfKind ``Lang.seqType then none
  else some ty[0]

/-- The Lean type of the Fren type `ty`. -/
partial def elabType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name) (ty : Syntax) : m Expr := do
  -- `Set(T)`: `"Set" "(" T ")"`; `Rel(A, B)`: `"Rel" "(" A "," B ")"`.
  -- An element type, which is never a `Nat` (`lang::nat_place`).
  let elem (e : Syntax) : m Expr := do
    let t ← elabType modName e
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
    return t
  let some p := typePath? ty |
    if ty.isOfKind ``Lang.relType then
      return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero])
        (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← elem ty[2]) (← elem ty[4]))
    else if ty.isOfKind ``Lang.seqType then return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← elem ty[2])
    else return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (← elem ty[2])
  let ty := p
  let segs := pathSegs ty
  if segs.size == 1 && segs[0]!.getId == `Bool then return Lean.mkConst ``Bool
  if segs.size == 1 && segs[0]!.getId == `Int then return Lean.mkConst ``Int
  if segs.size == 1 && segs[0]!.getId == `Nat then return Lean.mkConst ``Nat
  if segs.size == 1 && segs[0]!.getId == `String then return Lean.mkConst ``String
  match ← resolvePath modName segs with
  | .item { kind := .enumItem, path, .. } => return Lean.mkConst (← enumDecl path)
  | .item { kind := .recordItem, path, .. } =>
    let some r := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
    return Lean.mkConst r.decl
  | .item { kind := .typeItem, path, .. } => return Lean.mkConst (placeholderName path)
  | r => throwErrorAt ty (Core.notATypeMsg r).text

/-- The `Rel(A, B)`s within the type `ty`. -/
partial def relTypes (ty : Syntax) : Array Syntax :=
  (if ty.isOfKind ``Lang.relType then #[ty] else #[]) ++ ty.getArgs.flatMap relTypes

/-- Records `zero_sized_map_values` on each `Rel(A, B)` within the type
`ty` whose `B` is an enumeration of one variant without a payload
(`lint::zero_sized_map_values`). -/
def lintRelTypes [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name)
    (ty : Syntax) : m Unit := do
  for r in relTypes ty do
    let b ← elabType modName r[4]
    let some e := b.constName?.bind (← getState).enumOfDecl? | continue
    if Core.zeroSizedMapValues true e.variants.size (e.payloads.any (!·.isEmpty)) then
      let text (t : Syntax) := ((t.reprint.getD "").trimAscii).toString
      recordLint .zeroSizedMapValues r (Core.zeroSizedMapValuesMsg (text r[2]) (text r[4]) e.variants[0]!.toString)

/-- Where the annotation `: T` of the type `ty` is, from the end of what
precedes it. -/
def annotationRef (ty : Syntax) : Syntax := Id.run do
  let some sub := ty.getSubstring? false false | return ty
  let before := (String.Pos.Raw.extract sub.str 0 sub.startPos).toList.reverse
  let ws := before.takeWhile Char.isWhitespace
  let rest := before.drop ws.length
  let colon := if rest.head? == some ':' then [':'] else []
  let ws' := (rest.drop colon.length).takeWhile Char.isWhitespace
  let n := (ws ++ colon ++ ws').foldl (fun n c => n + c.utf8Size) 0
  return .atom (.synthetic ⟨sub.startPos.byteIdx - n⟩ sub.stopPos) ""

/-- Records `redundant_bool_type` on the declaration of `n` with the type
`ty`, if it is `Bool` (`lint::redundant_bool_type`). -/
def lintBoolType (n : Name) (ty : Syntax) (t : Expr) : TermElabM Unit := do
  if Core.redundantBoolType n (some (t.isConstOf ``Bool)) then
    recordLint .redundantBoolType (annotationRef ty) (Core.redundantBoolTypeMsg n)

def varType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM Expr := do
  let n := name.getId
  let t ← ty?.mapM (elabType modName)
  if let some ty := ty? then lintRelTypes modName ty
  liftMsg name (Core.checkVarName n (t.map (·.isConstOf ``Bool)))
  if let (some ty, some t) := (ty?, t) then lintBoolType n ty t
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
  if t.isConstOf ``Nat then throwErrorAt ty (Core.natPlaceMsg (if payload then .payload else .field)).text
  lintRelTypes modName ty
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

@[command_elab Lang.enumCmd] def elabEnum : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "enum" nameStx
  checkFresh modName n nameStx
  lintName .enumeration n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let variantStxs := stx[4].getSepArgs
  -- Distinct names (`lang::distinct_names`), of names that are single
  -- segments, as the `fren` command parses them.
  for v in variantStxs do discard (segName v[0])
  if let some k := (Core.repeatsAt (variantStxs.map (·[0].getId)))[0]? then
    throwErrorAt variantStxs[k]![0] (Core.dupVariantMsg variantStxs[k]![0].getId).text
  let mut variants := #[]
  let mut payloads : Array (Array Expr) := #[]
  let mut nRecursive := 0
  let mut unbounded := false
  for v in variantStxs do
    let vn ← checkItemName "variant" v[0]
    lintName .variant vn v[0]
    variants := variants.push vn
    let tys := if v[1].isNone then #[] else v[1][1].getSepArgs
    let ts ← tys.mapM fun t => fieldType modName t (some decl) true n
    if ts.any (·.isConstOf decl) then nRecursive := nRecursive + 1
    let st ← getState
    unbounded := unbounded || ts.any fun t => t.isConstOf decl || st.unbounded t
    payloads := payloads.push ts
  unless Core.wellFounded variants.size nRecursive do throwErrorAt nameStx (Core.illFoundedMsg n).text
  -- `enum_variant_names` (`lint::enum_variant_names`, `lint::variant_has_enum_name`).
  if let some msg := Core.enumVariantNamesMsg? n variants then recordLint .enumVariantNames nameStx msg
  for v in variantStxs, vn in variants do
    if let some msg := Core.variantNameMsg? n vn then recordLint .enumVariantNames v[0] msg
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

@[command_elab Lang.structCmd] def elabStruct : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let mut fields : Array (Name × Expr) := #[]
  let fieldStxs := stx[4].getSepArgs
  for f in fieldStxs do discard (segName f[0])
  if let some k := (Core.repeatsAt (fieldStxs.map (·[0].getId)))[0]? then
    throwErrorAt fieldStxs[k]![0] (Core.dupFieldMsg fieldStxs[k]![0].getId).text
  for f in fieldStxs do
    let fn := f[0].getId
    liftMsg f[0] (Core.checkNoBang fn)
    lintName .field fn f[0]
    let t ← if f[1].isNone then pure (Lean.mkConst ``Bool) else fieldType modName f[1][1] (some decl) false n
    -- As for a variable (`lang::bool_naming`).
    liftMsg f[0] (Core.checkVarName fn (if f[1].isNone then none else some (t.isConstOf ``Bool)))
    unless f[1].isNone do liftTermElabM (lintBoolType fn f[1][1] t)
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
  /-- In a refinement's binding, over the concrete comp's variables, which
  binding it is: its mentions follow `refinement::mention` instead. -/
  refining? : Option Core.RefineBinding := none
  /-- The binders in scope, innermost last. -/
  binders : Array MatchBinder := #[]
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a global expectation, whose instances are its binders. -/
  inGlobal : Bool := false
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- Something here gives `{}` its type (`Reqs/Lang/Expressions#sets`). -/
  emptyOk : Bool := false
  /-- A `Nat` is expected here, so an integer literal is one
  (`lang::literal_type`). -/
  natOk : Bool := false
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array Term := #[]
  /-- Whether to record the indexes of this expression for the definedness
  check, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, or of `and`, whose chain
  `membership_chain` looks at from its top: that operator, or `""`. -/
  chain : String := ""
  /-- The expression this one is part of, if any: where a `match` is, for
  the match lints. -/
  parent? : Option Syntax := none
  /-- This expression is the `else` branch of an `if`, whose chain
  `if_chain_match` looks at from its top. -/
  inElse : Bool := false

def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option MatchBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : MatchBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name)

/-- Whether the path `p`, applied, builds a variant rather than applying a
function. -/
def isVariant (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← segNames (pathSegs p)
  return (← getState).table.resolvePath cx.modName names cx.shadowing matches .ok (.variant ..)

/-- The defined function that the path `p`, applied, applies, if any. -/
def definedFn? (cx : ExprCtx) (p : Syntax) : TermElabM (Option DefinedInfo) := do
  let names ← segNames (pathSegs p)
  let s ← getState
  let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
  return s.defined.get? path

/-- The Fren name of the type whose Lean type is `t`. -/
partial def typeName (t : Expr) : TermElabM String := do
  -- A comparison or connective is a `Prop` in Lean, and a `Bool` in Fren.
  if t.isConstOf ``Bool || t.isProp then return "Bool"
  if t.isConstOf ``Int then return "Int"
  if t.isConstOf ``Nat then return "Nat"
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

/-- The Lean type `t` as the Fren type it stands for, as the `fren` command
has it (`Core.Ty`), if it is one: a condition's `Prop` is a `Bool`. -/
partial def coreTy? (t : Expr) : TermElabM (Option Core.Ty) := do
  let t ← instantiateMVars t
  if t.isProp || t.isConstOf ``Bool then return some .bool
  if t.isConstOf ``Int then return some .int
  if t.isConstOf ``Nat then return some .nat
  if t.isConstOf ``String then return some .string
  if t.isAppOfArity ``Fren.Seq 1 then return (← coreTy? t.appArg!).map .seq
  if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then
      let (some a, some b) := (← coreTy? e.appFn!.appArg!, ← coreTy? e.appArg!) | return none
      return some (.rel a b)
    return (← coreTy? e).map .set
  let s ← getState
  let some d := t.constName? | return none
  if let some e := s.enumOfDecl? d then return some (.enum e.path)
  if let some r := s.recordOfDecl? d then return some (.record r.path)
  if let some a := s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none then
    return some (.abstract a.path)
  return none

/-- The Lean type of the Fren expression `t`, elaborated with the comp's
variables in scope. -/
def typeOf (t : Term) : TermElabM Expr := do
  let e ← withoutErrToSorry <| Term.withSynthesize <| elabTerm (← `(open Classical in $t)) none
  whnfR (← instantiateMVars (← inferType e))

/-- The Fren type of the term `t` (`coreTy?`), if it has one. -/
def frenTypeOf? (t : Term) : TermElabM (Option Core.Ty) := do coreTy? (← typeOf t)

/-- Reports `ref`, translated to `t`, unless it may stand where the type
`expected` is needed, as the `fren` command does (`Core.checkType`), with
`why` it is needed. -/
def checkTermType (ref : Syntax) (t : Term) (expected : Core.Ty) (why : Option String := none) : TermElabM Unit := do
  if let some found ← frenTypeOf? t then liftMsg ref (Core.checkType expected found why)

/-- Reports `ref`, translated to `t`, an operand of the arithmetic operator
`op`, unless it is an `Int` or a `Nat` (`Core.checkNumber`). -/
def checkNumberTerm (ref : Syntax) (t : Term) (op : String) : TermElabM Unit := do
  if let some found ← frenTypeOf? t then liftMsg ref (Core.checkNumber op found)

/-- `t`, widened to an `Int` if it is a `Nat` (`lang::widening`): Lean
inserts `↑`. -/
def widenTerm (t : Term) : TermElabM Term := do
  if (← typeOf t).isConstOf ``Nat then `(($t : Int)) else pure t

/-- Checks that `t`, written at `ref` where a `Nat` is expected, is not an
`Int`, with the message that the `fren` command gives, explained by `why`
(`lang::widening`). -/
def checkNat (ref : Syntax) (t : Term) (why : String) : TermElabM Unit := do
  if (← typeOf t).isConstOf ``Int then throwErrorAt ref (Core.narrowingMsg why).text

/-- `ts`, each widened to an `Int` if one is an `Int` and another a `Nat`:
the branches of a conditional or the bodies of a `match`'s arms
(`lang::operator_type`). -/
def widenMixed (ts : Array Term) : TermElabM (Array Term) := do
  let tys ← ts.mapM typeOf
  if tys.any (·.isConstOf ``Int) && tys.any (·.isConstOf ``Nat) then ts.mapM widenTerm else pure ts

/-- Whether each parameter of the function of type `type`, after its first
`skip`, is a `Nat`. -/
def natParams (type : Expr) (skip : Nat := 0) : Array Bool :=
  go type 0 #[]
where
  go : Expr → Nat → Array Bool → Array Bool
    | .forallE _ d b _, k, acc => go b (k + 1) (if k < skip then acc else acc.push (d.isConstOf ``Nat))
    | _, _, acc => acc

/-- Strips parentheses from `e`. -/
partial def unparen (e : Syntax) : Syntax :=
  if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then unparen e[1] else e

/-- The pattern of `s.matches?(p)`, `p`, as a closed `Fren.Core.Re` term
(`Reqs/Lang/Expressions#patterns`). -/
def patternTerm (p : Syntax) : TermElabM Term := do
  let some lit := (let p := unparen p; if p.getNumArgs == 1 then p[0] else p).isStrLit?
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
    let mut widened := #[]
    for (a, stx) in args, p in method.params do
      let a ← if (leanTy p).isConstOf ``Int then widenTerm a else pure a
      let ta ← typeOf a
      unless ← isDefEq ta (leanTy p) do
        throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
      widened := widened.push (a, stx)
    let args := widened
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
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (int := true))
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false (int := true)).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ta.isConstOf ``Int || ta.isConstOf ``Nat do
        throwErrorAt stx s!"type mismatch: expected `Int`, found `{← typeName ta}`"
    -- `min` and `max` of `Nat`s are `Nat`s; otherwise both are widened
    -- (`lang::nat_result`).
    let op : Core.NatOp := match method with | .min => .min | .max => .max | _ => .abs
    let argNat ← args.anyM fun (a, _) => return (← typeOf a).isConstOf ``Nat
    let nat := Core.natResult op (ty.isConstOf ``Nat) argNat false
    let t ← if nat then pure t else widenTerm t
    let args ← if nat then pure args else args.mapM fun (a, stx) => return (← widenTerm a, stx)
    -- Conditionals, so that they stay linear.
    let y : Term := (args.map (·.1))[0]?.getD t
    let term ← match method with
      | .min => `(if $t ≤ $y then $t else $y)
      | .max => `(if $t ≥ $y then $t else $y)
      | _ => `(if $t < 0 then -$t else $t)
    return (term, Lean.mkConst (if nat then ``Nat else ``Int))
  unless ty.isConstOf ``String do throwErrorAt ref (Core.noMethodsMsg m (← typeName ty)).text
  let some method := (Core.Method.ofName? m).filter (·.accepts true false)
    | throwErrorAt ref (Core.unknownMethodMsg m "String").text
  unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
  let leanTy : Core.MethodTy → Expr
    | .bool => Lean.mkConst ``Bool | .int => Lean.mkConst ``Int | _ => Lean.mkConst ``String
  let mut widened := #[]
  for (a, stx) in args, p in method.params do
    -- A pattern is a `Fren.Core.Re`, which `patternTerm` checked.
    if method == .matches then widened := widened.push (a, stx); continue
    let a ← if (leanTy p).isConstOf ``Int then widenTerm a else pure a
    let ta ← typeOf a
    unless ← isDefEq ta (leanTy p) do
      throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
    widened := widened.push (a, stx)
  let args := widened
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
  if ty.isConstOf ``String || ty.isConstOf ``Int || ty.isConstOf ``Nat || (relTypes? ty).isSome || ty.isAppOfArity ``Fren.Seq 1 then
    return ← callMethod ref t ty f.toString #[]
  if ty.isAppOfArity ``Fren.FinSet 1 then
    unless f == `card do throwErrorAt ref (Core.unknownSetMethodMsg f.toString (← typeName ty)).text
    return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
  let some r := ty.constName?.bind (← getState).recordOfDecl?
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  let some (_, ft) := r.fields.find? (·.1 == f)
    | throwErrorAt ref (Core.noFieldMsg f (Core.showPath r.path) (r.fields.map (·.1))).text
  return (← `($(mkCIdentFrom ref (r.decl ++ f)) $t), ft)

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
  else if e.isOfKind ``Lang.updateExpr then
    e[3].getSepArgs.foldl (init := pathMentions e[1]) fun acc b =>
      acc ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
  else if e.isOfKind ``Lang.matchExpr then
    e[3].getSepArgs.foldl (init := pathMentions e[1]) fun acc arm =>
      -- In its arm, a binder's name means the binder, not what it shadows.
      let bound := (patternBinders arm).filter (·.isIdent) |>.map fun b => (declaredIdent b).1.getId
      acc ++ (pathMentions arm[2]).filter (!bound.contains ·.getRoot)
  -- A pattern's paths name variants.
  else if e.isOfKind ``Lang.isExpr then pathMentions e[0]
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
    let ok := match cx.refining? with
      | some rb => rb.checkMention u.role u.isPub u.name
      | none => Core.checkMention cx.place u.role earlier u.name
    match ok with
    | .ok () => pure ()
    | .error msg => throwErrorAt id (if u.name == n then msg else Core.throughDefinition n msg).text
  return some (mkIdentFrom id n)

open Lang in
/-- The expression that is the name `n`, a path of one segment. -/
def pathExpr (ref : Syntax) (n : Name) : TermElabM Syntax := do
  let tmpl ← `(fren_expr| x)
  return tmpl.raw.setArg 0 (mkNode ``Lang.fren_path #[mkNullNode #[mkIdentFrom ref n]])

/-- For `x.m(a)`, an application of a dotted name, the receiver `x` and the
method `m`. Paths are written with `::`, so an applied dotted name is a
method call, as the `fren` command parses it: of a value, or of a variable
read from an instance, as in `w.x.len()`. The only root that is not a
receiver is an instance without variables (unless a binder shadows it).

This does not resolve the root or the method. Elaborating the receiver
reports a root that is not a value, such as a misspelled name or an
enumeration, and elaborating the call reports a method that its type does
not have. -/
def methodApp? (cx : ExprCtx) (e : Syntax) : Option (Name × Name) := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  let n := segs[0]!.getId
  guard (!n.isAtomic && ((cx.binder? n.getRoot).isSome || !cx.insts.contains n.getRoot
    || cx.vars.any (·.name.getRoot == n.getRoot)))
  return (n.getPrefix, Name.mkSimple n.getString!)

/-- The shape of `e`, for what it mentions (`lang::mentions`), where `bs`
are the binders of `e` around the subexpression, each with the shape of its
scrutinee. -/
partial def shapeOf (cx : ExprCtx) (e : Syntax) (bs : Array (Name × Core.MentionShape) := #[]) : TermElabM Core.MentionShape := do
  let parts (k : Core.MentionKind) (es : Array Syntax) : TermElabM Core.MentionShape :=
    return .node k (← es.toList.mapM (shapeOf cx · bs))
  if let some (recv, _) := methodApp? cx e then
    return ← parts .method (#[(← pathExpr e recv)[0]] ++ e[2].getSepArgs)
  if e.isOfKind ``Lang.appExpr then
    let k : Core.MentionKind ← if ← isVariant cx e[0] then pure .construction
      else if (← definedFn? cx e[0]).isSome then pure .defined else pure .uninterpreted
    parts k e[2].getSepArgs
  else if e.isOfKind ``Lang.recordExpr then
    -- A field without `:= e` is `x := x`.
    parts .construction (← e[2].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1])
  else if e.isOfKind ``Lang.updateExpr then
    -- The updated value, and the new values.
    parts .construction (#[e[1]] ++ (← e[3].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1]))
  else if e.isOfKind ``Lang.matchExpr then
    let s ← shapeOf cx e[1] bs
    let arms ← e[3].getSepArgs.toList.mapM fun arm => do
      let new := (patternBinders arm).filter (·.isIdent) |>.map fun b => ((declaredIdent b).1.getId, Core.MentionShape.node .binder [s])
      shapeOf cx arm[2] (bs ++ new)
    return .node .compound (s :: arms)
  else if e.isOfKind ``Lang.isExpr then parts .compound #[e[0]]
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size != 1 then return .leaf .constant
    let n := segs[0]!.getId
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then return .node .binder [← shapeOf (cx.at b) b.scrutinee]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return .node .definedOutput [← shapeOf { cx with binders := #[] } d]
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable else .constant)
  else if e.isAtom || e.isIdent then return .leaf .literal
  else parts .compound e.getArgs

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← shapeOf cx e).mentions

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

/-- Whether `e` is a constant: it mentions no variable or uninterpreted
function (`lang::mentions`). -/
def isConstant (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return !(← mentionsAny cx e)

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

/-- `(e).a.b` or `(e).a.m(x)`, whose name after the `.` is dotted, as the
reads one after another, `((e).a).b` or `((e).a).m(x)`, as the `fren`
command's parser reads it, each name at its own place in the source, so
that an error underlines only the name it is about; `none` for any other
expression. -/
def splitDotted? (e : Syntax) : Option Syntax := do
  guard (e.isOfKind ``Lang.fieldExpr || e.isOfKind ``Lang.methodExpr)
  guard e[2].isIdent
  let n := e[2].getId
  guard !n.isAtomic
  let start := (e[2].getPos? (canonicalOnly := false)).getD 0
  -- Each name, with its place: after the names and dots before it.
  let (_, ids) := n.components.foldl (init := (start, #[])) fun (p, ids) c =>
    let stop : String.Pos.Raw := ⟨p.byteIdx + c.toString.utf8ByteSize⟩
    (⟨stop.byteIdx + 1⟩, ids.push (mkIdentFrom (Syntax.atom (.synthetic p stop) "") c))
  let recv := ids.pop.foldl (init := e[0]) fun (r : Syntax) id => Syntax.node .none ``Lang.fieldExpr #[r, e[1], id]
  return (e.setArg 0 recv).setArg 2 ids.back!

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
def isConcat (e : Syntax) : Bool :=
  let e := unparen e
  e.getNumArgs == 3 && e[1].isAtom && e[1].getAtomVal.trimAscii.toString == "++"

/-- Whether `e` contains a `++` that is not a constant, itself or in a
defined output's definition (acyclic, so this ends). -/
partial def hasConcat (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  if isConcat e && !(← isConstant cx e) then return true
  if e.isOfKind ``Lang.fren_path then
    return ← match definitionOf? cx e with | some d => hasConcat cx d | none => pure false
  if e.isOfKind ``Lang.isExpr then return ← hasConcat cx e[0]
  e.getArgs.anyM (hasConcat cx)

/-- Whether `e` is a comparison: `=`, `!=`, an ordering, `in`, `subset`,
or a pattern test, `e is P`, which does not chain but parses as one. -/
def isComparison (e : Syntax) : Bool :=
  e.getNumArgs == 3 && e[1].isAtom &&
    ["=", "!=", "<", "<=", ">", ">=", "in", "subset", "is"].contains e[1].getAtomVal.trimAscii.toString

/-- The operands and operators of `e`, if it is a chained comparison
(`Reqs/Lang/Expressions#chained-comparisons`): a comparison whose left
operand is one, without parentheses, as `Fren.Lang` parses `a < b <= c`. -/
partial def chainOf? (e : Syntax) : Option (Array Syntax × Array Syntax) :=
  if isComparison e && isComparison e[0] then some (go e) else none
where
  go (e : Syntax) : Array Syntax × Array Syntax :=
    if isComparison e then let (xs, ops) := go e[0]; (xs.push e[2], ops.push e[1]) else (#[e], #[])

/-- The nodes in `e`'s arguments, through lists such as a call's arguments. -/
partial def subNodes (e : Syntax) : Array Syntax :=
  e.getArgs.flatMap fun a =>
    if a.isAtom || a.isIdent || a.isMissing then #[] else if a.isOfKind nullKind then subNodes a else #[a]

/-- Strips parentheses from `e`. -/
partial def unparen (e : Syntax) : Syntax :=
  if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then unparen e[1] else e

/-- `e` as the lints that rewrite it (`Core.ExLint`) and the operator lints
see it, with ranges in characters from `base` in `str`. Parentheses are
dropped, as by the `fren` command's parser. -/
partial def boolNode (str : String) (base : String.Pos.Raw) (e : Syntax) : Core.BNode Syntax :=
  let off (p : String.Pos.Raw) := (String.Pos.Raw.extract str base p).length
  let range : Core.Range := { start := off (e.getPos?.getD base), stop := off (e.getTailPos?.getD base) }
  let go := boolNode str base
  let atom (i : Nat) := if e[i].isAtom then e[i].getAtomVal.trimAscii.toString else ""
  -- `true` and `false` are also paths.
  if e.isOfKind choiceKind then go ((e.getArgs.find? fun a => a.getNumArgs == 1 && a[0].isAtom).getD e[0]) else
  if let some (xs, ops) := chainOf? e then .mk (.chain ops.size) range e (xs.map go) else
  if e.isOfKind ``Lang.methodExpr then
    let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
    let m := if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString
    .mk (.method m) range e (#[go e[0]] ++ e[4].getSepArgs.map go)
  else if e.isOfKind ``Lang.appExpr && (pathSegs e[0]).size == 1 && !(pathSegs e[0])[0]!.getId.isAtomic then
    -- `x.m(a)`: a method call on `x`, which may itself be dotted.
    let id := (pathSegs e[0])[0]!
    let m := id.getId.getString!
    let recvStop := off (id.getTailPos?.getD base) - m.length - 1
    .mk (.method m) range e (#[.mk .atom { range with stop := recvStop } id #[]] ++ e[2].getSepArgs.map go)
  else if e.isOfKind ``Lang.isExpr then .mk .patternTest range e #[go e[0]]
  else
  match e.getNumArgs, atom 0, atom 1 with
  | 3, "(", _ => go e[1]
  | 4, "when", _ => .mk (.when false) range e #[go e[1], go e[3]]
  | 4, "unless", _ => .mk (.when true) range e #[go e[1], go e[3]]
  | 6, "if", _ => .mk .ite range e #[go e[1], go e[3], go e[5]]
  | 2, "not", _ => .mk .not range e #[go e[1]]
  | 2, "-", _ => .mk .neg range e #[go e[1]]
  | 3, _, op => if Core.binaryOps.contains op then .mk (.bin op) range e #[go e[0], go e[2]] else .mk .atom range e (subNodes e |>.map go)
  | 1, "true", _ => .mk (.lit true) range e #[]
  | 1, "false", _ => .mk (.lit false) range e #[]
  | _, _, _ => .mk .atom range e (subNodes e |>.map go)

/-- Whether `e` is in parentheses, `(e')`. -/
def isParen (e : Syntax) : Bool :=
  e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" && !e[1].isOfKind nullKind

/-- Whether `e`, written in `str`, is in parentheses directly around
parentheses, with nothing but whitespace between them. -/
def isDoubleParen (str : String) (e : Syntax) : Bool :=
  let blank (a b : Syntax) := match a.getTailPos?, b.getPos? with
    | some p, some q => (String.Pos.Raw.extract str p q).all Char.isWhitespace
    | _, _ => false
  isParen e && isParen e[1] && blank e[0] e[1] && blank e[1] e[2]

/-- Records `double_parens` in `e`, written in `str` (`lint::double_parens`),
where `inParens` says that `e` is directly in parentheses: once for each
run of pairs, at its outermost. -/
partial def lintParens (fixable : Bool) (str : String) (e : Syntax) (inParens : Bool := false) : TermElabM Unit := do
  if isParen e && !inParens then
    let mut inner := e
    let mut depth := 1
    while isDoubleParen str inner do
      inner := inner[1]
      depth := depth + 1
    if Core.doubleParens depth then
      let msg := Core.doubleParensMsg ((inner.reprint.getD "").trimAscii.toString)
      recordLint .doubleParens e { msg with notes := if fixable then msg.notes.push Core.fixHelp else msg.notes }
  for a in e.getArgs, i in [0:e.getNumArgs] do lintParens fixable str a (i == 1 && isDoubleParen str e)

/-- Records `assertions_on_constants` on the constraint `e`, an `assume`,
`req` or `expect` as `kind` says (`lint::assertions_on_constants`). -/
def lintConstant (cx : ExprCtx) (kind : String) (e : Syntax) : TermElabM Unit := do
  if Core.assertionOnConstant (← mentionsAny cx e) then
    let literal? := match boolNode "" 0 (unparen e) with | .mk (.lit b) .. => some b | _ => none
    recordLint .assertionsOnConstants e (Core.assertionOnConstantMsg kind literal?)

/-- Records the expressions in `e` that the lints that rewrite them
(`Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated. -/
def lintBools (e : Syntax) : TermElabM Unit := do
  let some sub := e.getSubstring? false false | return
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let node := boolNode sub.str sub.startPos e
  for (l, ref, msg) in Core.rewriteReports src node fixable do
    recordLint l ref msg
  let (boolEqs, variants) := ((← getLocal).boolEqs, (← getLocal).variants)
  modifyLocal fun l => { l with boolEqs := #[], variants := #[] }
  let variant? (s : Syntax) := (variants.find? (·.1 == (s.getPos?, s.getTailPos?))).map (·.2)
  for r in Core.opReports src (fun s => boolEqs.contains (s.getPos?, s.getTailPos?)) variant? node do
    let help := fixable && !r.msg.fixes.isEmpty
    recordLint r.lint r.ref { r.msg with notes := r.msg.notes ++ (if help then #[Core.fixHelp] else #[]) }
  for r in Core.arithReports src node do
    recordLint r.lint r.ref { r.msg with notes := r.msg.notes ++ (if fixable then #[Core.fixHelp] else #[]) }
  lintParens fixable sub.str e

/-- The text that `stx` is written with, without what is around it. -/
def exactText (stx : Syntax) : String :=
  match stx.getSubstring? false false with
  | some sub => String.Pos.Raw.extract sub.str sub.startPos sub.stopPos
  | none => ((stx.reprint.getD "").trimAscii).toString

/-- Whether an infix operator follows `stx` (`Core.startsWithOperator`). -/
def followedStx (stx : Syntax) : Bool :=
  match stx.getSubstring? false false with
  | some sub => Core.startsWithOperator (String.Pos.Raw.extract sub.str sub.stopPos ⟨sub.str.utf8ByteSize⟩)
  | none => false

/-- The text that `stx` is written with. -/
def srcText (stx : Syntax) : String := ((stx.reprint.getD "").trimAscii).toString

/-- Records `too_many_lines` on the `what` named `n`, the item `stx`,
counting its lines from its name, `nameStx` (`lint::too_many_lines`). -/
def lintLines (what : Core.Named) (n : Name) (nameStx stx : Syntax) : CommandElabM Unit := do
  let (some sub, some start) := (stx.getSubstring? false false, nameStx.getPos?) | return
  let k := Core.codeLines (String.Pos.Raw.extract sub.str start sub.stopPos)
  if Core.tooManyLines k then recordLint .tooManyLines nameStx (Core.tooManyLinesMsg what n k)

/-- `redundant_bindings` on the binding, or field, `b`, a `fren_binding`
(`lint::redundant_bindings`). -/
def lintRedundant (b : Syntax) (field : Bool) : TermElabM Unit := do
  unless b[1].isNone do
    let name := exactText b[0]
    if Core.redundantBinding (Core.writtenForm name) (Core.writtenForm (exactText b[1][1])) then
      recordLint .redundantBindings b (Core.redundantBindingMsg name field)

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
    if cx.noteIndexes then lintRedundant b true
    if b[1].isNone then go (← `(fren_expr| $(⟨b[0]⟩):ident)) else go b[1][1]
  `($(mkCIdentFrom e[0] (recordCtor info.decl)) $args*)

/-- That the term `s` of the enumeration `info` is one of the variants
`idxs`: equal to the variant built from its own payload. -/
def variantsTest (info : EnumInfo) (s : Term) (idxs : Array Nat) : TermElabM Term := do
  let tests ← idxs.mapM fun idx => do
    let ctor := info.decl ++ info.variants[idx]!
    let sels ← (Array.range info.payloads[idx]!.size).mapM fun k => `($(mkCIdent (selectorName ctor k)) $s)
    `($s = $(mkCIdent ctor) $sels*)
  tests.pop.foldrM (init := tests.back!) fun t acc => `($t ∨ $acc)

open Lang in
/-- The precedence of `e`'s operator, as `lang::operand` uses it: an
expression in parentheses, or a field read, is an atom. -/
def exprPrec (e : Syntax) : Nat :=
  if (e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(") || e.isOfKind ``Lang.fieldExpr then Core.BKind.atom.prec
  else match boolNode "" 0 e with | .mk k .. => k.prec

open Lang in
/-- Where `e`, an operand of `p`, is, as `lang::operand` sees it; `none`
where any expression can be written. -/
def operandSlot (p e : Syntax) : Option Core.Slot :=
  let same (a : Syntax) := a.getPos? == e.getPos? && a.getTailPos? == e.getTailPos?
  let atom (i : Nat) := if p[i].isAtom then p[i].getAtomVal.trimAscii.toString else ""
  let at_ (k : Core.BKind) (idxs : Array Nat) := (idxs.findIdx? (same p[·])).bind (k.slots[·]?.join)
  if p.isOfKind ``Lang.fieldExpr || p.isOfKind ``Lang.methodExpr || p.isOfKind ``Lang.indexExpr then
    if same p[0] then some Core.receiverSlot else none
  else if p.isOfKind ``Lang.matchExpr then
    if same p[1] then some Core.receiverSlot else none
  else if p.isOfKind ``Lang.isExpr then at_ .patternTest #[0]
  -- A chained comparison's operands, not the comparisons within it.
  else if let some (xs, ops) := chainOf? p then (xs.findIdx? same).bind ((Core.BKind.chain ops.size).slots[·]?.join)
  else match p.getNumArgs, atom 0, atom 1 with
    | 3, "(", _ => none
    | 4, "when", _ => at_ (.when false) #[1, 3]
    | 4, "unless", _ => at_ (.when true) #[1, 3]
    | 2, "not", _ => at_ .not #[1]
    | 2, "-", _ => at_ .neg #[1]
    | 3, _, op => if op.isEmpty then none else at_ (.bin op) #[0, 2]
    | _, _, _ => none

/-- The match lints of the `match` `e` on a value of the enumeration
`info`, whose arms name the variants `pats`, or `_` for `none`, where
`slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic#matches`). -/
def lintMatch (cx : ExprCtx) (e : Syntax) (info : EnumInfo) (pats : Array (Option (Array Nat)))
    (slot : Option Core.Slot) : TermElabM Unit := do
  let arms := e[3].getSepArgs
  let infos : Array Core.ArmInfo := arms.map fun arm =>
    let alts := patternAlts arm
    { alts := alts.map exactText, binds := (patternBinders arm).any (·.isIdent), noPayload := alts.all (·[1].isNone)
      body := { text := exactText arm[2], prec := exprPrec arm[2] } }
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable then m.note Core.fixHelp else m
  -- `trivial_match` (`lint::trivial_match`).
  if let #[i] := infos then
    if Core.trivialMatch infos.size i.binds then recordLint .trivialMatch e (Core.trivialMatchMsg (i.body.inSlot slot (followedStx e)))
  -- `needless_match` (`lint::needless_match`).
  let scr := exactText (unparen e[1])
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  for arm in arms, pat in pats do
    let body := unparen arm[2]
    match pat with
    | none =>
      wildcard := true
      scrutineeBack := Core.writtenSame (exactText body) scr
    | some #[idx] =>
      let bs := patternBinders arm
      let binders := bs.map fun b => if b.isIdent then b.getId.toString else "_"
      -- The arm's binders shadow items in its body.
      let shadowing := cx.shadowing ++ (bs.filter (·.isIdent)).map (·.getId)
      let (p, args) := if body.isOfKind ``Lang.appExpr then (body[0], body[2].getSepArgs)
        else (if body.getNumArgs == 1 then body[0] else body, #[])
      let same ← if p.isOfKind ``Lang.fren_path then do
          let names ← (pathSegs p).mapM segName
          pure (match (← getState).table.resolvePath cx.modName names shadowing with
            | .ok (.variant en i) => en.path == info.path && i == idx
            | _ => false)
        else pure false
      unless Core.givesBack same binders (args.map (exactText ∘ unparen)) do givenBack := false
    | some _ => givenBack := false
  let trivial := Core.trivialMatch infos.size (infos[0]?.any (·.binds))
  if Core.needlessMatch givenBack wildcard scrutineeBack trivial then
    let scrutinee : Core.BText := { text := scr, prec := exprPrec (unparen e[1]) }
    recordLint .needlessMatch e (help (Core.needlessMatchMsg (scrutinee.inSlot slot (followedStx e))))
  for g in Core.sameArmGroups infos do
    let (i, msg) := Core.sameArmsMsg infos g slot (followedStx e)
    recordLint .matchSameArms arms[i]! (help msg)
  let scrutinee : Core.BText := { text := exactText e[1], prec := exprPrec e[1] }
  if let some (pre, post) := Core.membershipParts? infos scrutinee slot then
    recordLint .matchLikeMembership e (help (Core.membershipMsg (pre ++ scrutinee.text ++ post)))
  let some w := pats.findIdx? (·.isNone) | return
  let covered := (List.range info.variants.size).filter fun k => !pats.any (·.any (·.contains k))
  unless Core.wildcardSingle covered.length do return
  let k := covered[0]!
  let v := info.variants[k]!
  let siblings ← (arms.flatMap patternAlts).mapM fun p => (pathSegs p[0]).mapM segName
  let n := info.payloads[k]!.size
  let pat? := ((← getState).table.variantPath? cx.modName cx.shadowing info.path v siblings).map fun segs =>
    "::".intercalate (segs.map toString).toList ++ (if n == 0 then "" else s!"({", ".intercalate (List.replicate n "_")})")
  let msg := Core.wildcardMsg (info.path ++ v) pat?
  recordLint .wildcardSingleVariant arms[w]![0] (if pat?.isSome then help msg else msg)

open Lang in
/-- `e`'s shape, for whether it synthesizes a type (`Core.TypeShape`). -/
partial def typeShape (e : Syntax) : Core.TypeShape :=
  if e.isOfKind ``Lang.setExpr || e.isOfKind ``Lang.seqExpr then
    let elems := e[1].getSepArgs
    if elems.isEmpty then .emptyLiteral else .anyPart (elems.toList.map typeShape)
  else if e.isOfKind ``Lang.pairExpr then .pair (typeShape e[1]) (typeShape e[3])
  else if e.isOfKind ``Lang.unionExpr || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr then
    .anyPart [typeShape e[0], typeShape e[2]]
  else if e.isOfKind ``Lang.matchExpr then .anyPart (e[3].getSepArgs.toList.map (typeShape ·[2]))
  else match e with
    | `(fren_expr| $a ++ $b) => .anyPart [typeShape a, typeShape b]
    | `(fren_expr| ($a)) => .anyPart [typeShape a]
    | `(fren_expr| if $_ then $a else $b) => .anyPart [typeShape a, typeShape b]
    | _ => .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (e : Syntax) : Bool := (typeShape e).synthesizes

/-- Whether one of `es` synthesizes a type. -/
def anySynthesizes (es : Array Syntax) : Bool := es.any synthesizes

open Lang in
/-- Translates a record update into the record literal whose other fields
are read from the updated value (`Reqs/Lang/Expressions#record-updates`),
where `toTerm` translates its parts. -/
def updateTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e <| withFreshMacroScope do
  let rv ← toTerm { cx with emptyOk := Core.Position.synthesized.checked false false } e[1]
  let ty ← typeOf rv
  let some info := ty.constName?.bind (← getState).recordOfDecl?
    | throwErrorAt e[1] (Core.updateBaseMsg (← typeName ty)).text
  let given := e[3].getSepArgs
  match Core.checkFieldUpdates info.path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (i, msg) => throwErrorAt given[i]![0] msg.text
  let go := toTerm { cx with emptyOk := Core.Position.declared.checked false false }
  -- `r` bound once, so that nested updates grow linearly.
  let bind := info.fields.size > given.size && !rv.raw.isIdent
  let r ← if bind then `(r) else pure rv
  let args ← info.fields.mapM fun (f, _) => do
    let some b := given.find? (·[0].getId == f) | `($(mkCIdentFrom e[1] (info.decl ++ f)) $r)
    if b[1].isNone then go (← `(fren_expr| $(⟨b[0]⟩):ident)) else go b[1][1]
  let lit ← `($(mkCIdentFrom e (recordCtor info.decl)) $args*)
  if bind then `(let r := $rv; $lit) else pure lit

open Lang in
/-- Translates a `match` into a chain of `if`s that compare its scrutinee
with each arm's variant, built from the scrutinee's own payload, where
`toTerm` translates its parts. -/
def matchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (slot : Option Core.Slot) :
    TermElabM Term := withRef e do
  -- The scrutinee synthesizes its type, and each body is checked against the
  -- whole's, or another's (`lang::checked`).
  let scrutinee := e[1]
  let s ← toTerm { cx with emptyOk := Core.Position.synthesized.checked false false, natOk := false } scrutinee
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
        if let some msg := Core.variantMentionMsg? v n (!p[1].isNone) then throwErrorAt p msg.text
        unless p[1].isNone do
          let bs := altBinders p
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
  if cx.noteIndexes then lintMatch cx e info pats slot
  let mut bodies : Array Term := #[]
  -- An arm is evaluated when its pattern matches and no earlier one does.
  let mut tests : Array (Option Term) := #[]
  for pat in pats do tests := tests.push (← pat.mapM (variantsTest info s))
  let mut earlier : Array Term := #[]
  -- An arm's body is guarded by its being the first arm that matches
  -- (`Core.GuardedOperand.armBody`): no earlier test holds, and its own does.
  -- That is built directly: its negation is never needed, so `guard` would
  -- only return it.
  for arm in arms, pat in pats, t? in tests do
    let guards := cx.guards ++ (← earlier.mapM fun t => `(¬$t)) ++ t?.toArray
    earlier := earlier ++ t?.toArray
    let mut new : Array MatchBinder := #[]
    if let some #[idx] := pat then
      let ctor := info.decl ++ info.variants[idx]!
      -- Distinct names (`lang::distinct_names`); `_` binds nothing.
      let named := (patternBinders arm).filter (·.isIdent)
      -- By the names they declare, without the `!` of shadowing.
      let declared := named.map fun b => (declaredIdent b).1.getId
      if let some k := (Core.repeatsAt declared)[0]? then
        throwErrorAt named[k]! (Core.dupPatternBinderMsg declared[k]!).text
      for b in patternBinders arm, t in info.payloads[idx]!, k in [0:info.payloads[idx]!.size] do
        unless b.isIdent do continue
        let locals := Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
          (cx.binders.map (·.name)) cx.selfFn.isSome cx.inGlobal
        let b ← declare b cx.modName locals
        let bn := b.getId
        liftMsg b (Core.checkVarName bn (some (t.isConstOf ``Bool)))
        lintName .binder bn b
        new := new.push { name := bn, term := ← `($(mkCIdent (selectorName ctor k)) $s), «type» := t
                          scrutinee, outer := cx.binders.size }
    let others := (arms.eraseIdx! bodies.size).map (·[2])
    let emptyOk := Core.Position.shared.checked cx.emptyOk (anySynthesizes others)
    bodies := bodies.push (← toTerm { cx with binders := cx.binders ++ new, guards, emptyOk } arm[2])
  let widened ← widenMixed bodies
  -- The first arm that matches; the last arm matches whatever is left.
  let mut out := widened.back!
  for i in (List.range (bodies.size - 1)).reverse do
    if let some t := tests[i]! then
      out ← `(if $t then $(widened[i]!) else $out)
  return out

open Lang in
/-- Translates `e is P`, which is `match e { P => true, _ => false }`, into
the test of `P`'s alternatives (`Reqs/Lang/Expressions#pattern-tests`). -/
def isTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let scrutinee := e[0]
  let s ← toTerm cx scrutinee
  let ty ← typeOf s
  let some info := ty.constName?.bind (← getState).enumOfDecl?
    | throwErrorAt scrutinee (Core.isScrutineeMsg (← typeName ty)).text
  -- Each alternative's variant and binders; `_` has none.
  let alts := if e[2].isOfKind ``Lang.altsPattern then e[2][1].getSepArgs else #[]
  let mut pats : Array (Nat × Array Syntax) := #[]
  for p in alts do
    match ← resolvePath cx.modName (pathSegs p[0]) cx.shadowing with
    | .variant en idx =>
      if en.path != info.path then
        throwErrorAt p (Core.notAVariantOfMsg info.path s!"a variant of `{Core.showPath en.path}`").text
      let v := info.path ++ en.variants[idx]!
      let n := info.payloads[idx]!.size
      if let some msg := Core.variantMentionMsg? v n (!p[1].isNone) then throwErrorAt p msg.text
      let bs := altBinders p
      unless p[1].isNone || bs.size == n do throwErrorAt p (Core.arityMsg v n bs.size "binder").text
      pats := pats.push (idx, bs)
    | r => throwErrorAt p (Core.notAVariantOfMsg info.path r.describe).text
  let named := pats.map fun (idx, bs) => (info.variants[idx]!, bs.map fun b => if b.isIdent then b.getId else `_)
  match Core.checkPatternTest info.path named with
  | .ok () => pure ()
  | .error ((j, some k), msg) => throwErrorAt pats[j]!.2[k]! msg.text
  | .error ((j, none), msg) => throwErrorAt alts[j]! msg.text
  if pats.isEmpty then `(true) else variantsTest info s (pats.map (·.1))

/-- Whether `e` is the binary operator `op`. -/
def isBinOp (e : Syntax) (op : String) : Bool :=
  e.getNumArgs == 3 && e[1].isAtom && e[1].getAtomVal.trimAscii.toString == op

/-- The operands of a chain of `op`, `or` or `and`, through parentheses, as
the `fren` command's parser, which drops them, sees it. -/
partial def chainOperands (op : String) (e : Syntax) : Array Syntax :=
  let e := unparen e
  if isBinOp e op then chainOperands op e[0] ++ chainOperands op e[2] else #[e]

/-- Whether `e` is `if c then a else b`. -/
def isIte (e : Syntax) : Bool := e.getNumArgs == 6 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "if"

/-- Whether `e` is a `when` or an `unless`. -/
def isConditional (e : Syntax) : Bool :=
  e.getNumArgs == 4 && e[0].isAtom && ["when", "unless"].contains e[0].getAtomVal.trimAscii.toString

/-- The variant that `v` names, if it is a path to one without a payload:
its enumeration, its index and its text. -/
def variantOf? (cx : ExprCtx) (v : Syntax) : TermElabM (Option (Name × Nat × String)) := do
  let v := unparen v
  let p := if v.getNumArgs == 1 then v[0] else v
  unless p.isOfKind ``Lang.fren_path do return none
  let st ← getState
  let .ok (.variant en idx) := st.table.resolvePath cx.modName ((pathSegs p).map (·.getId)) cx.shadowing | return none
  unless (st.enums.get? en.path).any (·.payloads[idx]?.any (·.isEmpty)) do return none
  return some (en.path, idx, srcText p)

/-- `e` as a test of which variant a scrutinee is, if it is one
(`Fren.Core.VariantTest`). -/
partial def variantTest? (cx : ExprCtx) (e : Syntax) : TermElabM (Option Core.VariantTest) := do
  let e := unparen e
  if isBinOp e "or" then
    let some x ← variantTest? cx e[0] | return none
    let some y ← variantTest? cx e[2] | return none
    return x.or y
  if isBinOp e "=" then
    let some (en, i, t) ← variantOf? cx e[2] | return none
    return some { scrutinee := srcText (unparen e[0]), enum := en, variants := #[(i, t)] }
  let s := unparen e[2]
  unless e.isOfKind ``Lang.memberExpr && s.isOfKind ``Lang.setExpr do return none
  let mut out : Array (Nat × String) := #[]
  let mut en? : Option Name := none
  for v in s[1].getSepArgs do
    let some (en, i, t) ← variantOf? cx v | return none
    unless en?.all (· == en) do return none
    en? := some en
    out := out.push (i, t)
  let some en := en? | return none
  return some { scrutinee := srcText (unparen e[0]), enum := en, variants := out }

/-- The tests, the branches and the final `else` of a chain of `if`. -/
partial def ifChain (e : Syntax) : Array Syntax × Array Syntax × Syntax :=
  let e := unparen e
  if isIte e then let (cs, as, z) := ifChain e[5]; (#[e[1]] ++ cs, #[e[3]] ++ as, z) else (#[], #[], e)

/-- The text of `e` as the body of a `match` arm. -/
def armBodyOf (e : Syntax) : String := let e := unparen e; Core.armBody (srcText e) (isConditional e)

/-- `if_chain_match` on the chain of `if` that starts at `e`
(`lint::if_chain_match`). -/
def lintIfChain (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  let (cs, as, z) := ifChain e
  let ts? := Core.sameScrutinee (← cs.mapM (variantTest? cx))
  let ts := ts?.getD #[]
  let enums := (← getState).enums
  let n := ((ts[0]?.bind fun t => enums.get? t.enum).map (·.variants.size)).getD 0
  let (fires, wildcard) := Core.ifChainMatch cs.size ts?.isSome (Core.repeatedVariants ts) (Core.untestedVariants n ts)
  if fires then
    recordLint .ifChainMatch e (Core.ifChainMatchMsg ts (as.map armBodyOf) (if wildcard then some (armBodyOf z) else none))

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
  let a := (splitDotted? a).getD a
  if a.isOfKind ``Lang.fieldExpr then
    let f := a[2].getId
    return if f == `len || f == `card then some (a[0], f == `card) else none
  let p := if a.getNumArgs == 1 then a[0] else a
  unless p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 do return none
  let .str pre m := (pathSegs p)[0]!.getId | return none
  if pre.isAnonymous || !(m == "len" || m == "card") then return none
  return some (← pathExpr a pre, m == "card")

/-- Whether `e` is a set or relation literal, rather than a string or
sequence literal, and its characters or elements, if it is one of those. -/
def literalCount? (e : Syntax) : Option (Bool × Nat) :=
  let e := unparen e
  let e := if e.getNumArgs == 1 then e[0] else e
  if let some v := e.isStrLit? then some (false, v.length)
  else if e.isOfKind ``Lang.seqExpr then some (false, e[1].getSepArgs.size)
  else if e.isOfKind ``Lang.setExpr then some (true, e[1].getSepArgs.size)
  else none

/-- `const_is_empty` on `e`, `a = b` or `a != b`, where one operand is an
empty literal and the other a literal (`lint::const_empty_equation`). -/
def lintEmptyEquation (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let op := e[1].getAtomVal.trimAscii.toString
  let (some (_, m), some (_, n)) := (literalCount? e[0], literalCount? e[2]) | return
  let (fires, value) := Core.constEmptyEquation (op == "=") (max m n)
  if fires && min m n == 0 then recordLint .constIsEmpty e (Core.constIsEmptyMsg value)

/-- `length_zero`, `card_zero` and `absurd_extreme_comparisons` on the
comparison `e` (`lint::length_zero`, `lint::absurd_extreme_comparisons`). -/
def lintLength (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let (a, b) := (unparen e[0], unparen e[2])
  let some c := Core.Comparison.ofOp? e[1].getAtomVal.trimAscii.toString | return
  let nat? (x : Syntax) := let x := unparen x; (if x.getNumArgs == 1 then x[0] else x).isNatLit?
  let lit? (x : Syntax) : Option Int :=
    let x := unparen x
    if x.getNumArgs == 2 && x[0].isAtom && x[0].getAtomVal.trimAscii.toString == "-" then (nat? x[1]).map (-·)
    else (nat? x).map (·)
  -- The length, the literal, and whether the length is on the left.
  let (n, d, left) ← match lit? b, lit? a with
    | some d, _ => pure (a, d, true)
    | none, some d => pure (b, d, false)
    | none, none => return
  let some (recv, card) ← lengthOf? (unparen n) | return
  -- `const_is_empty` (`lint::const_is_empty`), rather than `length_zero`
  -- and `card_zero` on a literal, or `absurd_extreme_comparisons` where it
  -- fires.
  let literal := (literalCount? recv).isSome
  if let some (set, count) := literalCount? recv then
    let r := unparen recv
    -- `[]` and `{}` have no type here, which is an error.
    let untyped := count == 0 && (r.isOfKind ``Lang.seqExpr || r.isOfKind ``Lang.setExpr)
    let (fires, value) := Core.constIsEmpty c d left set count
    if fires && card == set && !untyped then
      recordLint .constIsEmpty e (Core.constIsEmptyMsg value)
      return
  let fires := !literal && (Core.lengthZero c d left).1
  let empty := (Core.lengthZero c d left).2
  let (absurd, value) := Core.absurdComparison c d left
  unless fires || absurd do return
  -- Only its type: what elaborating it reports is reported where it is.
  let saved ← getLocal
  let some t ← try some <$> typeOf (← toTerm { cx with noteIndexes := false, concatOk := true } recv) catch _ => pure none
    | modifyLocal fun _ => saved
  modifyLocal fun _ => saved
  unless card == t.isAppOfArity ``Fren.FinSet 1 do return
  if absurd then
    if card || t.isConstOf ``String || t.isAppOfArity ``Fren.Seq 1 then
      recordLint .absurdExtremeComparisons e (Core.absurdComparisonMsg card value)
    return
  let emptyText := if t.isConstOf ``String then "\"\"" else if t.isAppOfArity ``Fren.Seq 1 then "[]" else "{}"
  recordLint (if card then .cardZero else .lengthZero) e (Core.lengthZeroMsg card (srcText recv) emptyText empty d)

/-- `eq_op` on `e`, if it is an infix operator (`lint::eq_op`), or `when` or
`unless` (`lint::eq_op_conditional`). -/
def lintEqOp (e : Syntax) : TermElabM Unit := do
  if isConditional e then
    let negated := e[0].getAtomVal.trimAscii.toString == "unless"
    let c := exactText (unparen e[1])
    if let some v := Core.eqOpConditional negated (Core.writtenSame c (exactText (unparen e[3]))) then
      recordLint .eqOp e (Core.eqOpConditionalMsg negated v c)
    return
  unless e.getNumArgs == 3 && e[1].isAtom do return
  let some op := Core.InfixOp.ofOp? e[1].getAtomVal.trimAscii.toString | return
  let a := exactText (unparen e[0])
  if let some v := Core.eqOp op (Core.writtenSame a (exactText (unparen e[2]))) then
    recordLint .eqOp e (Core.eqOpMsg op v a)

/-- `same_branches` on `e`, `if c then a else b` (`lint::same_branches`). -/
def lintSameBranches (e a b : Syntax) : TermElabM Unit := do
  let (a, b) := (unparen a, unparen b)
  unless Core.sameBranches (Core.writtenSame (exactText a) (exactText b)) do return
  let some sub := e.getSubstring? false false | return
  let .mk kind .. := boolNode "" 0 a
  recordLint .sameBranches e (Core.sameBranchesMsg (exactText a) kind.prec (String.Pos.Raw.extract sub.str 0 sub.startPos)
    (String.Pos.Raw.extract sub.str sub.stopPos ⟨sub.str.utf8ByteSize⟩))

/-- `duplicate_elements` on the set literal `e` (`lint::duplicate_elements`). -/
def lintDuplicates (e : Syntax) (elems : Array Syntax) : TermElabM Unit := do
  let repeats := Core.repeatedElements (elems.map (exactText <| unparen ·))
  unless Core.duplicateElements repeats.size do return
  let some sub := e.getSubstring? false false | return
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  let off (p : String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos p).length
  let range (s : Syntax) : Core.Range :=
    { start := off (s.getPos?.getD sub.startPos), stop := off (s.getTailPos?.getD sub.startPos) }
  recordLint .duplicateElements e (Core.duplicateElementsMsg src ⟨0, src.size⟩ (elems.map range) repeats)

/-- The receiver of `e` and the name it reads, if it reads a field or calls a
method without arguments. -/
def lastName? (e : Syntax) : TermElabM (Option (Syntax × String)) := do
  if e.isOfKind ``Lang.fieldExpr then return some (e[0], e[2].getId.toString)
  let p := if e.getNumArgs == 1 then e[0] else e
  unless p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 do return none
  let .str pre m := (pathSegs p)[0]!.getId | return none
  if pre.isAnonymous then return none
  return some (← pathExpr e pre, m)

/-- The names that `e` reads one after another, innermost first, each with
its receiver. -/
partial def namesRead (e : Syntax) : TermElabM (Array (Syntax × String)) := do
  match ← lastName? e with
  | some (r, n) => return (← namesRead (unparen r)).push (r, n)
  | none => return #[]

/-- `e` without parentheses, as an operand: its text and precedence. -/
def bareText (e : Syntax) : Core.BText := { text := srcText (unparen e), prec := exprPrec (unparen e) }

/-- Records `redundant_method_chain` on `e`, the end of a chain of names
(`lint::method_chain`), an operand of `parent?`: not on the receiver of a
field read. -/
def lintChain (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax) :
    TermElabM Unit := do
  let inChain := parent?.any fun p =>
    p.isOfKind ``Lang.fieldExpr && p[0].getPos? == e.getPos? && p[0].getTailPos? == e.getTailPos?
  unless cx.noteIndexes && !inChain do return
  let steps ← namesRead e
  let ms := steps.map (Core.Method.ofName? ·.2)
  let shortens (i : Nat) := match ms[i]?, ms[i + 1]? with
    | some (some a), some (some b) => Core.methodChain a b != .keep
    | _, _ => false
  unless (List.range steps.size).any shortens do return
  -- The first receiver that is a relation or a sequence, which has no
  -- fields: the names after it are its methods.
  for (recv, _) in steps, i in [0:steps.size] do
    -- Only its type: elaborating it has no other effect.
    let saved ← saveState
    let t? ← try some <$> typeOf (← toTerm { cx with noteIndexes := false, concatOk := true } recv)
      catch _ => pure none
    saved.restore
    let some t := t? | continue
    let relation := t.isAppOfArity ``Fren.FinSet 1 && t.appArg!.isAppOfArity ``Prod 2
    unless t.isAppOfArity ``Fren.Seq 1 || relation do continue
    let some chain := (ms.extract i).mapM id | return
    let short := Core.shortestChain chain.toList
    if short.length < chain.size then
      let fixed : Core.BText := if short.isEmpty then bareText recv
        else { text := srcText recv ++ String.join (short.map (s!".{·.name}")), prec := Core.BKind.atom.prec }
      recordLint .redundantMethodChain e (Core.methodChainMsg (fixed.inSlot (parent?.bind (operandSlot · e)) (followedStx e)))
    return

/-- Records `trivial_pattern` on `e`, `recv.matches?(args)`, an operand of
`parent?` (`lint::trivial_pattern`). -/
def lintPattern (cx : ExprCtx) (parent? : Option Syntax) (e recv : Syntax) (args : Array Syntax) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let #[p] := args | return
  let p := let p := unparen p; if p.getNumArgs == 1 then p[0] else p
  let some lit := p.isStrLit? | return
  unless (Core.parseRe lit) matches .ok _ do return
  -- `manual_pattern_char_comparison` and `almost_complete_range`
  -- (`lint::manual_pattern_char_comparison`, `lint::almost_complete_range`).
  if let some fixed := Core.charClassPattern? lit then
    recordLint .manualPatternCharComparison p (Core.manualPatternCharComparisonMsg (Core.patternLiteral (srcText p) fixed))
  if let some (fixed, found) := Core.completeRangesPattern? lit then
    recordLint .almostCompleteRange p (Core.almostCompleteRangeMsg found (Core.patternLiteral (srcText p) fixed))
  let some (fix, s) := Core.trivialPattern? lit | return
  let fixed := (Core.trivialPatternText (bareText recv) (srcText recv) fix s).inSlot (parent?.bind (operandSlot · e))
  recordLint .trivialPattern e (Core.trivialPatternMsg fix fixed)

open Lang in
/-- `a = b`, `a != b` and the orderings; on strings, checks the decidable
core, and writes the orderings with `Fren.Str.lt` and `Fren.Str.le`, and
`a > b` as `b < a`, since lean-smt writes `>` on strings as `str.>`,
which is not SMT-LIB. -/
def compareTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  let op := e[1].getAtomVal.trimAscii.toString
  let string (t : Term) : TermElabM Bool := return (← typeOf t).isConstOf ``String
  lintLength toTerm cx e
  let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
  if op == "=" || op == "!=" then
    lintEmptyEquation cx e
    -- `++` is in the core against a constant.
    let (x, y) := (← toTerm { cx with concatOk := cb, emptyOk := Core.Position.compared.checked false (synthesizes b) } a,
      ← toTerm { cx with concatOk := ca, emptyOk := Core.Position.compared.checked false (synthesizes a) } b)
    -- Both sides have one type, after widening, as the `fren` command checks
    -- (`lang::operator_type`).
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then liftMsg e (Core.checkComparable op tx ty)
    -- For `bool_equality`, at the end of the expression.
    let tx ← typeOf x
    if cx.noteIndexes && (tx.isConstOf ``Bool || tx.isProp) then
      modifyLocal fun l => { l with boolEqs := l.boolEqs.push (e.getPos?, e.getTailPos?) }
    -- A side whose definition has a `++` stands for it, and is reported here.
    let named (s : Syntax) : TermElabM Bool := do return (definitionOf? cx s).isSome && (← hasConcat cx s)
    if ((← named a) || (← named b)) && (← string x) then
      checkCore cx e .stringSearch true true #[] (ca || cb)
    else if !isConcat a && !isConcat b && (← string x) then
      checkCore cx e .stringCompare true (ca || cb || (isVariable cx a && isVariable cx b)) #[] (ca && cb)
    return ← if op == "=" then `($x = $y) else `($x ≠ $y)
  -- An ordering compares `Int`s, `Nat`s or `String`s, as the `fren` command
  -- checks (`lang::operator_type`).
  let x ← toTerm cx a
  let tx? ← frenTypeOf? x
  let operandTy : Core.Ty := if tx? == some .string then .string else .int
  if let some tx := tx? then liftMsg a (Core.checkType operandTy tx (Core.opNote op operandTy))
  let y ← toTerm cx b
  checkTermType b y operandTy (Core.opNote op operandTy)
  unless ← string x do
    return ← match op with
      | "<" => `($x < $y) | "<=" => `($x ≤ $y) | ">" => `($x > $y) | _ => `($x ≥ $y)
  checkCore cx e .stringCompare true (ca || cb) #[a, b] (ca && cb)
  match op with
  | "<" => `(Fren.Str.lt $x $y) | "<=" => `(Fren.Str.le $x $y) | ">" => `(Fren.Str.lt $y $x) | _ => `(Fren.Str.le $y $x)

open Lang in
/-- `a < b <= c`, the chained comparison `e` of the operands `xs` and the
operators `ops`, as `a < b ∧ b ≤ c`, with the term for `b` in both
(`Reqs/Lang/Expressions#chained-comparisons`). Each comparison is checked
as if written alone, at the syntax from its left operand to its right, and,
as in that expansion, the comparisons before an operand guard it. -/
def chainTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (xs ops : Array Syntax) :
    TermElabM Term := withRef e do
  let names := ops.map (·.getAtomVal.trimAscii.toString)
  if let .error (k, msg) := Core.checkChain names then throwErrorAt ops[k]! msg.text
  let mut x ← toTerm cx xs[0]!
  -- An `Int`, a `Nat`, widened, or a `String`, and every operand the first's
  -- type, as the `fren` command checks (`lang::operator_type`).
  let t0? := (← frenTypeOf? x).map (·.widen)
  if let some t0 := t0? then
    unless t0 == .string || t0 == .int do liftMsg xs[0]! (Core.checkType .int t0 (Core.opNote names[0]! .int))
  let string := (← typeOf x).isConstOf ``String
  let mut links := #[]
  for op in names, a in xs, b in xs.extract 1, opStx in ops do
    let y ← toTerm { cx with guards := cx.guards ++ links } b
    if let some t0 := t0? then checkTermType b y t0 (Core.opNote op t0)
    -- A node's position is its first token's, and its tail its last's, so
    -- this one spans the comparison, from `a` to `b`, for its messages.
    let link := mkNullNode #[a, opStx, b]
    if string then
      let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
      checkCore cx link .stringCompare true (ca || cb) #[a, b] (ca && cb)
    -- On strings, as `compareTerm` writes them.
    links := links.push (← withRef link <| match op, string with
      | "<", false => `($x < $y) | "<=", false => `($x ≤ $y)
      | ">", false => `($x > $y) | ">=", false => `($x ≥ $y)
      | "<", true => `(Fren.Str.lt $x $y) | "<=", true => `(Fren.Str.le $x $y)
      | ">", true => `(Fren.Str.lt $y $x) | _, _ => `(Fren.Str.le $y $x))
    x := y
  links.extract 1 |>.foldlM (fun acc l => `($acc ∧ $l)) links[0]!

/-- Whether `e` is `[]`, which takes its type from where it is written. -/
def isEmptySeq (e : Syntax) : Bool := e.isOfKind ``Lang.seqExpr && e[1].getSepArgs.isEmpty

/-- `a ++ b`, where `concatOk` says whether the core allows it here. -/
def concatTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (concatOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  -- Each operand is checked against the whole's type, or the other's (`lang::checked`).
  let x ← toTerm { cx with concatOk := true, emptyOk := Core.Position.shared.checked cx.emptyOk (synthesizes b) } a
  -- Sequences: outside the core, unless constant.
  if (← typeOf x).isAppOfArity ``Fren.Seq 1 then
    let y ← toTerm { cx with emptyOk := Core.Position.shared.checked cx.emptyOk (synthesizes a) } b
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then liftMsg b (Core.checkConcatOperands tx ty)
    checkCore cx e .seqWord true true #[a, b] (← isConstant cx e)
    return ← `(($x ++ $y : $(typeSyntax (← typeOf x))))
  -- Where the core allows it, only its operands' outputs matter.
  if concatOk then checkCore cx e .stringAtom true true #[a, b]
  else checkCore cx e .stringSearch true true #[a, b] (← isConstant cx e)
  -- Each operand is a `String`, as the `fren` command checks (`lang::operator_type`).
  checkTermType a x .string (Core.opNote "++" .string)
  let y ← toTerm { cx with concatOk := true, emptyOk := Core.Position.synthesized.checked false false } b
  checkTermType b y .string (Core.opNote "++" .string)
  `(($x ++ $y : String))

/-- `r.m(args)`, a method call on the receiver `recvStx`, whose method's name
is at `ref` (`Reqs/Lang/Expressions#methods`). -/
def methodTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e ref recvStx : Syntax) (m : String)
    (args : Array Syntax) (natOk : Bool := false) : TermElabM Term := withRef e do
  let r ← toTerm { cx with concatOk := true } recvStx
  let rty ← typeOf r
  let pattern := m == "matches?" && rty.isConstOf ``String
  -- A sequence method's arguments are typed by its parameters, so `[]` may be one.
  let seq := rty.isAppOfArity ``Fren.Seq 1
  let position : Core.Position := if seq then .declared else .synthesized
  -- A `Nat` is expected of `min`'s and `max`'s argument where one is of the
  -- whole (`lang::nat_result`).
  let natArg := natOk && rty.isConstOf ``Nat && (m == "min" || m == "max")
  let as ← args.mapM fun a =>
    return (← if pattern then patternTerm a else toTerm { cx with emptyOk := position.checked false false, natOk := natArg } a, a)
  if seq then
    let c := (Core.Method.ofName? m).map (·.seqConstruct) |>.getD .seqWord
    checkCore cx e c true true (#[recvStx] ++ args) ((← args.allM (isConstant cx ·)) && (← isConstant cx recvStx))
      (literalOperand := args.any fun a => (unparen a).isOfKind ``Lang.seqExpr)
  if rty.isConstOf ``String then
    let constantArgs ← args.allM (isConstant cx ·)
    let c := (Core.Method.ofName? m).map (·.construct) |>.getD .stringAtom
    checkCore cx e c constantArgs true (#[recvStx] ++ args) (constantArgs && (← isConstant cx recvStx))
  let t := (← callMethod ref r rty m as).1
  -- `empty_argument` (`lint::empty_argument`).
  if let (some meth, true) := (Core.Method.ofName? m, cx.noteIndexes) then
    let recv := if ref.isOfKind ``Lang.fren_path then ((exactText ref).dropEnd (m.length + 1)).toString else exactText recvStx
    if let some msg := Core.emptyArgumentMsg? meth seq recv (args.map (exactText <| unparen ·)) then
      recordLint .emptyArgument e msg
    -- `negative_position` (`lint::negative_position`).
    if let some msg := Core.negativeArgumentMsg? meth seq recv (args.map (exactText <| unparen ·)) then
      recordLint .negativePosition e msg
  checkRelational cx e rty m (#[recvStx] ++ args)
  checkRelationalCard cx e rty m recvStx
  return t

/-- `e`, where a pair `(a, b)` may be written: a member of a set literal, or
the left of `in`. -/
def pairOrTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := do
  if e.isOfKind ``Lang.pairExpr then
    -- A member is never a `Nat` (`lang::nat_place`).
    let (x, y) := (← widenTerm (← toTerm cx e[1]), ← widenTerm (← toTerm cx e[3]))
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
  if cx.noteIndexes then lintDuplicates e elems
  -- Each element is checked against the literal's element type, or another's (`lang::checked`).
  -- A member is never a `Nat` (`lang::nat_place`).
  let xs ← elems.mapIdxM fun k x => do
    widenTerm (← pairOrTerm toTerm { cx with emptyOk := Core.Position.shared.checked emptyOk (anySynthesizes (elems.eraseIdx! k)) } x)
  `(($(← finSetLit xs) : Fren.FinSet _))

/-- `x in s`, `s subset t`, `s union t`, `s inter t` and `s minus t`. -/
def setOpTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  checkCore cx e .setAlgebra true true #[a, b]
  if e.isOfKind ``Lang.memberExpr then
    if (unparen b).isOfKind ``Lang.setExpr && cx.noteIndexes then
      if let #[m] := (unparen b)[1].getSepArgs then
        unless m.isOfKind ``Lang.pairExpr do recordLint .singletonMembership e (Core.singletonMembershipMsg (srcText a) (srcText m))
    -- The left synthesizes a type, which the right is checked against (`lang::checked`).
    let (x, s) := (← widenTerm (← pairOrTerm toTerm { cx with emptyOk := Core.Position.synthesized.checked false false } a),
      ← toTerm { cx with emptyOk := Core.Position.compared.checked false (synthesizes a) } b)
    let (tx, ts) := (← typeOf x, ← typeOf s)
    if ts.isAppOfArity ``Fren.Seq 1 && (← isDefEq ts.appArg! tx) then
      checkCore cx e .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := (unparen b).isOfKind ``Lang.seqExpr)
      return ← `($x ∈ $s)
    let ok ← if ts.isAppOfArity ``Fren.FinSet 1 then isDefEq ts.appArg! tx else pure false
    unless ok do
      let set := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) tx
      throwError (Core.membershipTypeMsg (← typeName set) (← typeName ts) (a.isOfKind ``Lang.pairExpr)).text
    return ← `($x ∈ $s)
  -- The operands of `join` synthesize their types, those of `subset` give each
  -- other theirs, and those of `union`, `inter` and `minus` are also checked
  -- against the whole's (`lang::checked`).
  let position : Core.Position :=
    if e.isOfKind ``Lang.joinExpr then .synthesized
    else if e.isOfKind ``Lang.subsetExpr then .compared
    else .shared
  let x ← toTerm { cx with emptyOk := position.checked cx.emptyOk (synthesizes b) } a
  let y ← toTerm { cx with emptyOk := position.checked cx.emptyOk (synthesizes a) } b
  -- Their types, as the `fren` command checks them (`lang::operator_type`).
  unless e.isOfKind ``Lang.joinExpr do
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then
      match Core.checkSetOperands e[1].getAtomVal.trimAscii.toString tx ty with
      | .ok () => pure ()
      | .error (k, msg) => throwErrorAt (if k == 0 then a else b) msg.text
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

/-- `when c, d`, `unless c, d`, `c and d` or `c or d`, where `d` is the
`operand`, guarded by `c` or by `not c` (`lang::guard`). -/
def guardedTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (c d : Syntax) (operand : Core.GuardedOperand)
    (op : Join := .implies) : TermElabM Term := do
  let e ← getRef
  let j := match op with | .or => "or" | .and => "and" | .implies => ""
  -- `membership_chain`, at the top of a chain of `or` or of `and` (`lint::membership_chain`).
  if !j.isEmpty && cx.chain != j && cx.noteIndexes then
    let ds := chainOperands j e
    let cmp := if op matches .and then "!=" else "="
    let eqs := ds.filterMap fun d => let d := unparen d; if isBinOp d cmp then some (d[0], d[2]) else none
    let lefts := eqs.map (srcText ·.1)
    let laterIndexes := (eqs.extract 1).any fun (_, v) => !(indexedIn v).isEmpty
    if Core.membershipChainFires ds.size (eqs.size == ds.size && lefts.all (· == lefts[0]!)) laterIndexes then
      recordLint .membershipChain e (Core.membershipChainMsg lefts[0]! (eqs.map (srcText ·.2)) (op matches .and))
  -- `index_after_use` (`lint::index_after_use`).
  if op matches .and && cx.noteIndexes then
    if (indexedIn c).any (fun q => boundsSeq d q && !boundsSeq c q) then recordLint .indexAfterUse e (Core.indexAfterUseMsg (srcText c) (srcText d))
  let cx := { cx with chain := j }
  -- Each operand's type is checked as the `fren` command checks it
  -- (`lang::operator_type`).
  let kw := if operand matches .unlessBody then "unless" else "when"
  let x ← toTerm cx c
  checkTermType c x .bool (if j.isEmpty then some s!"note: the condition of `{kw}` is a `Bool`" else Core.opNote j .bool)
  let g ← operand.guard (pure x) `(¬$x)
  let y ← toTerm { cx with guards := cx.guards.push g } d
  if j.isEmpty then checkTermType e y .bool (some s!"note: the body of `{kw}` is a `Bool`")
  else checkTermType d y .bool (Core.opNote j .bool)
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
  -- Each element is checked against the literal's element type, or another's (`lang::checked`).
  -- An element is never a `Nat` (`lang::nat_place`).
  let xs ← elems.mapIdxM fun k x => do
    widenTerm (← toTerm { cx with emptyOk := Core.Position.shared.checked emptyOk (anySynthesizes (elems.eraseIdx! k)) } x)
  let mut t ← `(Fren.Seq.unit $(xs.back!))
  for x in xs.pop.reverse do t ← `(Fren.Seq.unit $x ++ $t)
  return t

/-- `q[i]`, indexing a sequence. -/
def indexTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e do
  let q ← toTerm cx e[0]
  let tq ← typeOf q
  unless tq.isAppOfArity ``Fren.Seq 1 do throwErrorAt e[0] (Core.notIndexableMsg (← typeName tq)).text
  let i ← widenTerm (← toTerm cx e[2])
  let ti ← typeOf i
  unless ti.isConstOf ``Int do throwErrorAt e[2] s!"type mismatch: expected `Int`, found `{← typeName ti}`"
  checkCore cx e .seqArray true true #[e[0], e[2]]
  -- `negative_position` (`lint::negative_position`).
  if let (true, some k) := (cx.noteIndexes, Core.negativeLiteral? (exactText (unparen e[2]))) then
    recordLint .negativePosition e (Core.negativeIndexMsg (exactText e[0]) k)
  -- `Fren.Seq.nth` is `default` out of range, which an abstract type's
  -- placeholder does not have.
  let elem := (← instantiateMVars tq).appArg!
  if (← trySynthInstance (mkApp (Lean.mkConst ``Inhabited [Level.one]) elem)) matches .none then
    throwErrorAt e s!"the Lean front end cannot yet index a sequence of `{← typeName elem}`, which has no default value"
  noteIndex cx e q i
  `(Fren.Seq.nth $q $i)

/-- The constant that the path of names `names` names, without recording its
use. -/
def constPath? (cx : ExprCtx) (names : Array Name) : TermElabM (Option Name) := do
  let .ok (.item { kind := .constItem, path, .. }) := (← getState).table.resolvePath cx.modName names cx.shadowing
    | return none
  return some path

open Lang in
/-- The value of `e`, if it is an integer constant expression: integer
literals and constants whose values are, combined by `+`, `-`, `*`, `div`,
`mod`, `abs`, `min` and `max`, as the `fren` command computes it
(`Reqs/Lang/Expressions#division-and-remainder`). -/
partial def intConstValue? (cx : ExprCtx) (e : Syntax) : TermElabM (Option Int) := do
  let e := unparen e
  if let some e' := splitDotted? e then return ← intConstValue? cx e'
  let method (recv : Syntax) (m : String) (args : Array Syntax) : TermElabM (Option Int) := do
    let some x ← intConstValue? cx recv | return none
    let some ys := (← args.toList.mapM (intConstValue? cx)).mapM id | return none
    return Core.intConstMethod? m x ys
  if let some (recv, m) := methodApp? cx e then
    return ← method (← pathExpr e[0] recv) m.toString e[2].getSepArgs
  if e.isOfKind ``Lang.methodExpr then
    let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
    return ← method e[0] (if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString) e[4].getSepArgs
  if e.isOfKind ``Lang.fieldExpr then return ← method e[0] e[2].getId.toString #[]
  match e with
  | `(fren_expr| $n:num) => return some n.getNat
  | `(fren_expr| -$a) => return (← intConstValue? cx a).map (- ·)
  | `(fren_expr| $p:fren_path) =>
    let segs := pathSegs p
    -- A constant, then the methods without arguments applied to it.
    let (names, methods) ← if h : segs.size = 1 then
        let n := segs[0].getId
        pure (#[Name.mkSimple n.getRoot.toString], n.components.drop 1)
      else if segs.any (!·.getId.isAtomic) then return none
      else pure (← segNames segs, [])
    if names.size == 1 && ((cx.binder? names[0]!).isSome || cx.vars.any (·.name.getRoot == names[0]!)) then return none
    let some path ← constPath? cx names | return none
    let some v := ((← getState).consts.get? path).bind (·.int?) | return none
    return methods.foldlM (fun x m => Core.intConstMethod? m.toString x []) v
  | _ =>
    if e.getNumArgs == 3 && e[1].isAtom then
      let some x ← intConstValue? cx e[0] | return none
      let some y ← intConstValue? cx e[2] | return none
      return Core.intConstOp? e[1].getAtomVal.trimAscii.toString x y
    return none

open Lang in
/-- The form of the divisor `k` (`lang::divisor`), without its `-` and
parentheses: its form, its value if it is known, and the constant it names,
if any. -/
partial def divisorForm (cx : ExprCtx) (k : Syntax) : TermElabM (Core.DivisorForm × Int × Name) := do
  match unparen k with
  | `(fren_expr| -$a) => let (f, v, c) ← divisorForm cx a; return (f, -v, c)
  | `(fren_expr| $n:num) => return (.literal, n.getNat, .anonymous)
  | `(fren_expr| $p:fren_path) =>
    let segs := pathSegs p
    if segs.any (!·.getId.isAtomic) then return (.other, 0, .anonymous)
    let names ← segNames segs
    if names.size == 1 && ((cx.binder? names[0]!).isSome || cx.vars.any (·.name == names[0]!)) then
      return (.other, 0, .anonymous)
    let some path ← constPath? cx names | return (.other, 0, .anonymous)
    return match ((← getState).consts.get? path).bind (·.int?) with
      | some v => (.knownConstant, v, path)
      | none => (.unknownConstant, 0, path)
  | _ => return (.other, 0, .anonymous)

/-- `a div k` or `a mod k` (`op`), which divides by the value of the divisor
`k` (`lang::divisor`), as the `fren` command does: by a numeral, which
SMT-LIB's linear logics require, so that `x div -k` is `-(x / k)` and
`x mod -k` is `x % k` (`Int.ediv_neg`, `Int.emod_neg`). -/
def divTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (op : String) (natOk : Bool := false) :
    TermElabM Term := withRef e do
  -- A `Nat` is expected of the dividend where one is of the whole
  -- (`lang::nat_result`).
  -- Each operand is checked in order, as the `fren` command checks it
  -- (`lang::operator_type`).
  let x ← toTerm { cx with natOk } e[0]
  checkNumberTerm e[0] x op
  checkTermType e[2] (← toTerm cx e[2]) .int (Core.opNote op .int)
  let (form, value, c) ← divisorForm cx e[2]
  liftMsg e[2] (Core.checkDivisor op form value c)
  -- Of a `Nat` by a positive divisor, Lean's `Nat` division, which agrees
  -- with `Int`'s there; otherwise the dividend is widened.
  if Core.natResult (if op == "mod" then .mod else .div) ((← typeOf x).isConstOf ``Nat) false (value > 0) then
    let k ← `(($(Syntax.mkNumLit (toString value.natAbs)) : Nat))
    return ← if op == "mod" then `($x % $k) else `($x / $k)
  let x ← widenTerm x
  let k ← `(($(Syntax.mkNumLit (toString value.natAbs)) : Int))
  if op == "mod" then `($x % $k) else if value < 0 then `(-($x / $k)) else `($x / $k)

open Lang in
/-- A path in an expression: a binder, a variable or a constant, with the
fields read from it, or a variant. `toTerm` translates its parts, and
`parent?` is the expression around it. -/
def pathTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax)
    (p : TSyntax ``fren_path) : TermElabM Term := do
  let segs := pathSegs p
  if h : segs.size = 1 then
    lintChain toTerm cx parent? e
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
          -- A constant, then the fields read from its value, or the
          -- methods without arguments applied to it.
          let root := n.getRoot
          if n.isAtomic || cx.insts.contains root then pure none else
          match (← getState).table.resolvePath cx.modName #[root] cx.shadowing with
          | .ok (.item { kind := .constItem, .. }) =>
            -- Resolved again, to record its use and any import it uses.
            let .item { kind := .constItem, path, .. } ← resolvePath cx.modName #[mkIdentFrom id root] cx.shadowing
              | pure none
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
    if let some msg := Core.variantMentionMsg? (en.path ++ en.variants[idx]!) n false then throwError msg.text
    if cx.noteIndexes then
      let v := ((e.getPos?, e.getTailPos?), (en.path ++ en.variants[idx]!).toString)
      modifyLocal fun l => { l with variants := l.variants.push v }
    return mkCIdentFrom e (info.decl ++ en.variants[idx]!)
  | .item { kind := .constItem, path, .. } =>
    let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
    -- Its value, not its generated definition (see `Fren.Model`).
    `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
  | .item { kind := .fnItem, path, .. } => throwError (Core.unappliedMsg path).text
  | r => throwError (Core.notAValueMsg r).text

open Lang in
/-- `p(args)`: a method, a variant with a payload, or a function applied.
`toTerm` translates its parts, and `parent?` is the expression around it. -/
def appTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax)
    (p : TSyntax ``fren_path) (args : Syntax.TSepArray `fren_expr ",") : TermElabM Term := do
  if let some (recv, m) := methodApp? cx e then
    let recv ← pathExpr p recv
    if m.toString == "matches?" then lintPattern cx parent? e recv args.getElems
    return ← methodTerm toTerm cx e p recv m.toString args.getElems cx.natOk
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
    if let some msg := Core.variantMentionMsg? v n true then throwError msg.text
    unless args.getElems.size == n do throwError (Core.arityMsg v n args.getElems.size "value").text
    let args ← args.getElems.mapM (toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := false })
    return ← `($(mkCIdentFrom p (info.decl ++ en.variants[idx]!)) $args*)
  let .item { kind := .fnItem, path, .. } := r | throwErrorAt p (Core.notAFunctionMsg r).text
  if let some d := (← getState).defined.get? path then
    -- Its definition, applied to the placeholders it uses; its arguments
    -- may mention anything (`lang::argument`).
    unless args.getElems.size == d.nParams do throwError (Core.arityMsg path d.nParams args.getElems.size).text
    let nats := natParams (← getConstInfo d.decl).type d.uses.size
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := nats[k]?.getD false } a
      if nats[k]?.getD false then checkNat a t s!"note: argument {k + 1} of `{Core.showPath path}` has type `Nat`"
      return t
    return ← `($(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*)
  if cx.selfFn.isSome then throwErrorAt p (Core.appliesUninterpretedMsg path).text
  let a ← placeholderOf path
  let nParams := (← getConstInfo a.placeholder).type.getForallArity
  unless args.getElems.size == nParams do throwError (Core.arityMsg path nParams args.getElems.size).text
  -- Outputs may not occur in arguments (`inst::mention`); assumptions and
  -- bindings exclude them already.
  let acx := if cx.place == .prop then { cx with place := .argument } else cx
  let nats := natParams (← getConstInfo a.placeholder).type
  let args ← args.getElems.zipIdx.mapM fun (a, k) => do
    let t ← toTerm { acx with emptyOk := Core.Position.declared.checked false false, natOk := nats[k]?.getD false } a
    if nats[k]?.getD false then checkNat a t s!"note: argument {k + 1} of `{Core.showPath path}` has type `Nat`"
    return t
  `($(mkCIdentFrom p a.placeholder) $args*)

/-- The operand `a` of the arithmetic operator `op`, an `Int` or a `Nat`, of
which a `Nat` is expected if `natOk`, as the `fren` command checks it
(`lang::operator_type`). -/
def numberOperand (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (op : String) (natOk : Bool)
    (a : Syntax) : TermElabM Term := do
  let x ← toTerm { cx with natOk } a
  checkNumberTerm a x op
  return x

/-- The operand `a` of the logical operator `op`, a `Bool`, as the `fren`
command checks it (`lang::operator_type`). -/
def boolOperand (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (op : String) (a : Syntax) :
    TermElabM Term := do
  let x ← toTerm cx a
  checkTermType a x .bool (Core.opNote op .bool)
  return x

/-- `if c then a else b`, where `toTerm` translates its parts, which are
checked against a type if `emptyOk`, and are `Nat`s if `natOk` is. -/
def iteTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk natOk : Bool) (e c' a b : Syntax) :
    TermElabM Term := do
  if cx.noteIndexes && !cx.inElse then lintIfChain cx e
  if cx.noteIndexes then lintSameBranches e a b
  let c ← toTerm { cx with inElse := false } c'
  checkTermType c' c .bool (some "note: the condition of `if` is a `Bool`")
  let gx ← Core.GuardedOperand.thenBranch.guard (pure c) `(¬$c)
  let gy ← Core.GuardedOperand.elseBranch.guard (pure c) `(¬$c)
  let x ← toTerm { cx with emptyOk := Core.Position.shared.checked emptyOk (synthesizes b), natOk, guards := cx.guards.push gx, inElse := false } a
  let y ← toTerm { cx with emptyOk := Core.Position.shared.checked emptyOk (synthesizes a), natOk, guards := cx.guards.push gy, inElse := true } b
  if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then liftMsg e (Core.checkBranches tx ty)
  let #[x, y] ← widenMixed #[x, y] | unreachable!
  `(if $c then $x else $y)

/-- `a op b`, for `op` one of `+`, `-` and `*`, where `toTerm` translates
the operands. `+` and `*` of `Nat`s are `Nat`s, as Lean's `binop%` gives,
and a `Nat` is expected of the operands where one is of the whole
(`natOk`); `-` is always an `Int`, so that nothing truncates
(`lang::operator_type`). -/
def arithTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (natOk : Bool) (op : String) (a b : Syntax) :
    TermElabM Term := do
  -- Each operand is an `Int` or a `Nat`, as the `fren` command checks
  -- (`lang::operator_type`).
  if op == "-" then return ← `((($(← numberOperand toTerm cx op false a) : Int) - ($(← numberOperand toTerm cx op false b) : Int)))
  if op == "*" then
    unless Core.productAccepted (← mentionsAny cx a) (← mentionsAny cx b) do
      throwError Core.nonlinearMsg.text
  let (x, y) := (← numberOperand toTerm cx op natOk a, ← numberOperand toTerm cx op natOk b)
  if op == "+" then `($x + $y) else `($x * $y)

open Lang in
/-- The expressions that `toTerm` gives no syntax pattern of its own: fields,
methods, `mod`, collections, indexes, records, `match` and `is`, where
`toTerm` translates their parts, `emptyOk` and `natOk` are what is
expected of the whole, and `parent?` is the expression around it. -/
def otherTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (emptyOk natOk : Bool)
    (e : Syntax) : TermElabM Term := do
  if let some e' := splitDotted? e then return ← toTerm cx e'
  if e.isOfKind ``Lang.fieldExpr then
    lintChain toTerm cx parent? e
    return ← fieldTerm cx e (← toTerm { cx with concatOk := true } e[0])
  else if e.isOfKind ``Lang.methodExpr then
    -- `at` is a keyword of Lean's.
    let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
    let m := if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString
    if m == "matches?" then lintPattern cx parent? e e[0] e[4].getSepArgs
    methodTerm toTerm cx e e[2] e[0] m e[4].getSepArgs natOk
  else if e.isOfKind ``Lang.modExpr then divTerm toTerm cx e "mod" natOk
  else if e.isOfKind ``Lang.setExpr then setLitTerm toTerm cx emptyOk e
  else if e.isOfKind ``Lang.memberExpr || e.isOfKind ``Lang.subsetExpr || e.isOfKind ``Lang.unionExpr
      || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr || e.isOfKind ``Lang.joinExpr then setOpTerm toTerm { cx with emptyOk } e
  else if e.isOfKind ``Lang.pairExpr then throwError Core.pairPlaceMsg.text
  else if e.isOfKind ``Lang.seqExpr then seqLitTerm toTerm cx emptyOk e
  else if e.isOfKind ``Lang.indexExpr then indexTerm toTerm cx e
  else if e.isOfKind ``Lang.recordExpr then recordTerm (toTerm { cx with emptyOk := Core.Position.declared.checked false false }) cx e
  else if e.isOfKind ``Lang.matchExpr then matchTerm toTerm { cx with emptyOk, natOk } e (parent?.bind (operandSlot · e))
  else if e.isOfKind ``Lang.isExpr then isTerm toTerm cx e
  else if e.isOfKind ``Lang.updateExpr then updateTerm toTerm cx e
  else throwError "unsupported Fren expression"

open Lang in
/-- Translates a Fren expression to a Lean term, resolving names with Fren's
rules. Variables become references to locals of the same name; variants
become references to the generated constructors. -/
partial def toTerm (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let concatOk := cx.concatOk
  let emptyOk := cx.emptyOk
  let natOk := cx.natOk
  -- An operand of `or` or `and` continues its chain only if it is one too.
  let parent? := cx.parent?
  let cx := { cx with concatOk := false, emptyOk := false, natOk := false, chain := if isBinOp (unparen e) cx.chain then cx.chain else ""
                      parent? := some e, inElse := cx.inElse && isIte (unparen e) }
  let go := toTerm cx
  -- A chained comparison's comparisons are not operators of their own here.
  if cx.noteIndexes && (chainOf? e).isNone then lintEqOp e
  if let some (xs, ops) := chainOf? e then return ← chainTerm toTerm cx e xs ops
  match e with
  | `(fren_expr| when $c, $d) => guardedTerm toTerm cx c d .whenBody
  | `(fren_expr| unless $c, $d) => guardedTerm toTerm cx c d .unlessBody
  | `(fren_expr| $a iff $b) => `($(← boolOperand toTerm cx "iff" a) ↔ $(← boolOperand toTerm cx "iff" b))
  | `(fren_expr| $a or $b) => guardedTerm toTerm cx a b .orRight (op := .or)
  | `(fren_expr| $a and $b) => guardedTerm toTerm cx a b .andRight (op := .and)
  | `(fren_expr| not $a) => `(¬$(← boolOperand toTerm cx "not" a))
  | `(fren_expr| if $c' then $a else $b) => iteTerm toTerm cx emptyOk natOk e c' a b
  | `(fren_expr| $_ = $_) | `(fren_expr| $_ != $_) | `(fren_expr| $_ < $_) | `(fren_expr| $_ <= $_)
  | `(fren_expr| $_ > $_) | `(fren_expr| $_ >= $_) => compareTerm toTerm cx e
  | `(fren_expr| $_ ++ $_) => concatTerm toTerm { cx with emptyOk } concatOk e
  | `(fren_expr| $s:str) =>
    liftMsg s (Core.checkStringChars s.getString)
    `(Fren.Str.lit $s)
  | `(fren_expr| $a + $b) => arithTerm toTerm cx natOk "+" a b
  | `(fren_expr| $a - $b) => arithTerm toTerm cx natOk "-" a b
  | `(fren_expr| $a * $b) => arithTerm toTerm cx natOk "*" a b
  | `(fren_expr| $_ div $_) => divTerm toTerm cx e "div" natOk
  | `(fren_expr| -$a) => `((-($(← numberOperand toTerm cx "-" false a) : Int)))
  | `(fren_expr| $_ == $_) | `(fren_expr| $_ && $_) | `(fren_expr| $_ || $_) | `(fren_expr| $_ | $_) =>
    throwErrorAt e[1] (Core.foreignOpMsg e[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| !$_) => throwErrorAt e[0] (Core.foreignOpMsg "!").text
  | `(fren_expr| $_ <- $_) => throwErrorAt e[1] Core.leftArrowMsg.text
  -- Checked against the whole's type, if it is (`lang::checked`).
  | `(fren_expr| ($a)) => `(($(← toTerm { cx with concatOk, natOk, emptyOk := Core.Position.shared.checked emptyOk false } a)))
  | `(fren_expr| $n:num) => if natOk then `(($n : Nat)) else `(($n : Int))
  | `(fren_expr| true) => `(true)
  | `(fren_expr| false) => `(false)
  | `(fren_expr| $p:fren_path) => pathTerm toTerm cx parent? e p
  | `(fren_expr| $p:fren_path($args,*)) => appTerm toTerm { cx with natOk } parent? e p args
  | _ => otherTerm toTerm cx parent? emptyOk natOk e

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

@[command_elab Lang.typeCmd] def elabAbstractType : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
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

@[command_elab Lang.fnCmd] def elabFunction : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← segName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  checkFresh modName n nameStx
  lintName .function n nameStx
  startDeclared
  let path := modName ++ n
  let params := stx[4].getSepArgs
  let body? := if stx[7].isNone then none else some stx[7][1]
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Syntax) := !p[1].isNone ||
    (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (declaredIdent (pathSegs q)[0]!).1.getId.toString.endsWith "?"
  let nNamed := (params.filter named).size
  unless Core.functionParamsAccepted body?.isSome params.size nNamed do
    let bad := params.find? (named · != body?.isSome) |>.getD nameStx
    throwErrorAt bad (Core.functionParamsMsg path body?.isSome).text
  let some body := body? | do
    liftTermElabM do
      let params ← params.mapM fun p => do lintRelTypes modName p[0]; elabType modName p[0]
      -- As for a variable, with the result type (`lang::bool_naming`).
      let result ← varType modName nameStx (if stx[6].isNone then none else some stx[6][1])
      declarePlaceholder path (← mkArrowN params result) false
    record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
    unless isPub do recordItem .function path nameStx
  let decl := (← getCurrNamespace) ++ path
  liftTermElabM do
    -- The parameters, declared like a comp's inputs.
    let mut vars : Array Var := #[]
    let paramIds ← params.mapM fun p => do
      let some q := typePath? p[0] | throwErrorAt p[0] (Core.functionParamsMsg path true).text
      pure (pathSegs q)[0]!
    for x in paramIds do discard (segName x)
    -- By the names they declare, without the `!` of shadowing.
    let declared := paramIds.map fun x => (declaredIdent x).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt paramIds[k]! (Core.dupParamMsg declared[k]!).text
    for p in params, x0 in paramIds do
      let x ← declare x0 modName
      lintName .variable x.getId x
      let ty ← varType modName x (if p[1].isNone then none else some p[1][1])
      vars := vars.push { name := x.getId, role := .input, isPub := true, «type» := ty, ref := x }
    let result ← varType modName nameStx (if stx[6].isNone then none else some stx[6][1])
    let lam ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let cx : ExprCtx := { modName, vars, insts := #[], place := .prop, selfFn := some n, natOk := result.isConstOf ``Nat }
      let t ← toTerm cx body
      if result.isConstOf ``Nat then checkNat body t s!"note: `{n}` returns `Nat`"
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
  lintDeclared .function n nameStx
  lintLines .function n nameStx stx
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
    let some idx := cx.vars.findIdx? (·.name == pi.name ++ x.getId)
      | throwError "internal error: no variable for `{x.getId}`"
    let natOk := cx.vars[idx]!.type.isConstOf ``Nat
    let t ← if b[1].isNone then toTerm cx (← `(fren_expr| $(⟨x⟩):ident)) else toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk } b[1][1]
    if natOk then
      checkNat (if b[1].isNone then x else b[1][1]) t s!"note: `{x.getId}` of `{Core.showPath pi.comp.path}` has type `Nat`"
    unless b[1].isNone do lintBools b[1][1]
    lintRedundant b false
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

/-- Whether the evidence `value`, written at `ref`, is testing
(`Reqs/Check#checking-by-testing`). -/
def evidenceTested (ref : Syntax) (value : String) : CommandElabM Bool := do
  let some b := Core.evidenceTested? value | throwErrorAt ref (Core.invalidEvidenceMsg value).text
  return b

open Lang in
/-- A member without its `set_option fren.evidence ... in`, and the
setting, if it has one: the innermost, if there are several. -/
partial def unwrapEvidence (m : Syntax) : CommandElabM (Syntax × Option (Bool × Syntax)) := do
  unless m.isOfKind ``Lang.evidenceMember do return (m, none)
  -- Its option is `fren.evidence` (`checkParsed`).
  let b ← evidenceTested m[2] (m[2].isStrLit?.getD "")
  let (inner, set?) ← unwrapEvidence m[4]
  return (inner, set?.getD (b, m))

open Lang in
/-- The members of a comp without their evidence settings, and the checks
that those and the comp's setting `all` set to testing. -/
def testedOf (all : Bool) (raw : Array Syntax) : CommandElabM (Array Syntax × Core.Tested) := do
  let mut members := #[]
  let mut expects := #[]
  let mut insts := #[]
  let mut dets := #[]
  let mut constraints := #[]
  for m0 in raw do
    let (m, set?) ← unwrapEvidence m0
    members := members.push m
    let b? := set?.map (·.1)
    let misplaced (what : String) : CommandElabM Unit := do
      if let some (_, ref) := set? then throwErrorAt ref (Core.misplacedEvidenceMsg what).text
    match m with
    | `(fren_member| expect $x:ident : $_) | `(fren_member| cover $x:ident : $_) => expects := expects.push (x.getId, b?)
    -- By the names they declare, without the `!` of shadowing.
    | `(fren_member| inst $x:ident : $_:fren_path { $_,* }) => insts := insts.push ((declaredIdent x).1.getId, b?)
    | `(fren_member| assume $x:ident : $_) => misplaced "an assumption"; constraints := constraints.push x.getId
    | `(fren_member| req $x:ident : $_) => misplaced "a requirement"; constraints := constraints.push x.getId
    | _ =>
      if m.isOfKind ``Lang.outMember then
        -- `[pub] [det] out x [: T] [:= e]`
        let y := (declaredIdent m[3]).1.getId
        if !m[1].isNone then dets := dets.push (y, b?)
        else misplaced "an output that is not `det`"
        if !m[5].isNone then constraints := constraints.push y
      else misplaced (if m.isOfKind ``Lang.inMember then "an input" else "a `use`")
  return (members, Core.Tested.ofSettings all constraints expects insts dets)

open Lang in
/-- The name that a member declares, if any: a variable, an instance or a
constraint, which share one namespace (`lang::distinct_names`). -/
def memberName? (m : Syntax) : Option Syntax :=
  if m.isOfKind ``Lang.inMember then some m[1]
  else if m.isOfKind ``Lang.outMember then some m[3]
  else match m with
    | `(fren_member| inst $x:ident : $_:fren_path { $_,* }) => some x
    | `(fren_member| assume $x:ident : $_) => some x
    | `(fren_member| req $x:ident : $_) => some x
    | `(fren_member| expect $x:ident : $_) => some x
    | `(fren_member| cover $x:ident : $_) => some x
    | _ => none

open Lang in
@[command_elab Lang.compCmd] def elabComp : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "component" nameStx
  checkFresh modName n nameStx
  lintName .component n nameStx
  startDeclared
  let path := modName ++ n
  let declBase := (← getCurrNamespace) ++ path
  -- The evidence settings, apart from the members they set.
  let (members, tested) ← testedOf (← evidenceTested nameStx (fren.evidence.get (← getOptions))) stx[4].getArgs
  -- Its `use`s, and the scope that its paths resolve in.
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`): variables, instances and
  -- constraints share one namespace.
  let named := members.filterMap memberName?
  for x in named do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k]! (Core.dupMemberMsg declared[k]!).text
  let (ok, generated) ← liftTermElabM do
    let mut ok := true
    let mut generated : Array Name := #[]
    let mut names : NameSet := {}
    -- Variables
    let mut vars : Array Var := #[]
    for m in members do
      let (role, isPub, isDet, x, ty?, defn?) ← match m.getKind with
        -- An input has no definition (`checkParsed`).
        | ``Lang.inMember =>
          pure (Core.Role.input, true, false, m[1], if m[2].isNone then none else some m[2][1], none)
        | ``Lang.outMember =>
          pure (.output, !m[0].isNone, !m[1].isNone, m[3], if m[4].isNone then none else some m[4][1],
            if m[5].isNone then none else some m[5][1])
        | _ => continue
      -- An error in shadowing leaves the variable's meaning clear.
      let x ← try declare x scope
        catch ex => logException ex; ok := false; pure (declaredIdent x).1
      names := names.insert x.getId
      lintName .variable x.getId x
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
      -- An instance named by a literal is not resolved, which would report
      -- its name again; the `fren` command stops at the first report too.
      if let .error msg := Core.checkNotLiteral (declaredIdent x).1.getId then
        logErrorAt x msg.text; ok := false; continue
      let x ← try declare x scope
        catch ex => logException ex; ok := false; pure (declaredIdent x).1
      names := names.insert x.getId
      lintName .instance x.getId x
      try
        let (pi, ivars) ← resolveInst scope x p bs.getElems vars.size
        pending := pending.push pi
        vars := vars ++ ivars
      catch ex => logException ex; ok := false
    let instNames := pending.map (·.name)
    -- An instance that is not resolved is reported once, not again at each
    -- use of it, as by the `fren` command (`Reqs/View#static-errors`).
    let instsOk := ok
    unless instsOk do return (false, #[])
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
            let t ← toTerm { modName := scope, vars, insts := instNames, place := .prop, emptyOk := Core.Position.declared.checked false false, concatOk := true
                             natOk := v.type.isConstOf ``Nat } e
            if v.type.isConstOf ``Nat then checkNat e t s!"note: `{v.name}` has type `Nat`, so its definition must too"
            elabProp t v.type
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
          | `(fren_member| cover $x:ident : $e) => pure (.cover, x, e)
          | _ => continue
        if let .error msg := Core.checkNoBang x.getId then
          logErrorAt x msg.text; good := false; continue
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
          lintConstant cx kind.keyword e
          let trig ← triggerOf cx e
          let trigger? ← trig.mapM fun (t, _) => do mkLambdaFVars fvs (← elabProp t)
          let decl := declBase ++ Name.mkSimple kind.keyword ++ x.getId
          defs := defs.push (decl, body)
          props := props.push {
            kind, name := x.getId, ref := x, body := ← mkLambdaFVars fvs body,
            trigger?, triggerRef? := trig.map (·.2), decl }
        catch ex => logException ex; good := false
      -- `duplicate_constraint` (`lint::duplicate_constraint`).
      let constraints := members.filterMap fun m => match m with
        | `(fren_member| assume $x:ident : $e) => some (Core.ConstraintKind.assume, x.raw, e.raw)
        | `(fren_member| req $x:ident : $e) => some (.req, x.raw, e.raw)
        | `(fren_member| expect $x:ident : $e) => some (.expect, x.raw, e.raw)
        | _ => none
      for (i, j) in Core.repeatedConstraints (constraints.map fun (_, _, e) => exactText (unparen e)) do
        let (k, x, _) := constraints[i]!
        let (k', x', _) := constraints[j]!
        let msg := Core.duplicateConstraintMsg k' k x'.getId.toString
        let fixable := (Core.duplicateConstraint k' k true).2 && (← getLocal).inMarkdown
        recordLint .duplicateConstraint x (if fixable then msg.note Core.fixHelp else msg)
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
        let mentions ← match v.defn? with | some d => mentionsAny lcx d | none => pure true
        let (constant, definable) := Core.outputLints v.defn?.isSome mentions about.size equation
        if constant then recordLint .constantOutput v.ref (Core.constantOutputMsg v.name)
        if definable then recordLint .definableOutput v.ref (Core.definableOutputMsg v.name about[0]!.1)
      -- `case_split_reqs` (`lint::case_split_reqs`): each requirement `when T, y = e`, as its name, where it is
      -- reported, `y`, the operator, `T` and the text of `e`.
      let mut cases : Array (Name × Syntax × String × String × Core.VariantTest × String) := #[]
      for m in members do
        let `(fren_member| req $x:ident : $e) := m | continue
        let e := unparen e.raw
        unless isConditional e && e[0].getAtomVal.trimAscii.toString == "when" do continue
        let body := unparen e[3]
        let op := if isBinOp body "=" then "=" else if isBinOp body "iff" then "iff" else ""
        if op.isEmpty then continue
        let y := unparen body[0]
        let y := if y.getNumArgs == 1 then y[0] else y
        unless y.isOfKind ``Lang.fren_path && (pathSegs y).size == 1 do continue
        let yn := (pathSegs y)[0]!.getId
        unless vars.any (fun v => v.role == .output && v.name == yn) do continue
        let some t ← variantTest? lcx e[1] | continue
        cases := cases.push (x.getId, x, srcText y, op, t, armBodyOf body[2])
      let mut grouped : Array Nat := #[]
      for i in [0:cases.size] do
        if grouped.contains i then continue
        let (_, _, y, op, t, _) := cases[i]!
        let group := (Array.range cases.size).filter fun j =>
          j ≥ i && cases[j]!.2.2.1 == y && cases[j]!.2.2.2.2.1.key == t.key && cases[j]!.2.2.2.2.1.enum == t.enum
        grouped := grouped ++ group
        let cs := group.map fun j => let (n, _, _, _, t, e) := cases[j]!; (n, t, e)
        let ts := cs.map (·.2.1)
        let n := (((← getState).enums.get? t.enum).map (·.variants.size)).getD 0
        if Core.caseSplitReqs cs.size (Core.repeatedVariants ts) then
          recordLint .caseSplitReqs cases[group[1]!]!.2.1 (Core.caseSplitReqsMsg y op cs (Core.untestedVariants n ts))
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
        | `(fren_member| expect $_:ident : $e) | `(fren_member| cover $_:ident : $e) =>
          mentioned := mentioned ++ pathMentions e
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
                          decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied
                          relational, counts, indexes, tested })
    return (ok, generated)
  lintDeclared .component n nameStx
  lintLines .component n nameStx stx
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with comps := l.comps.push path }.declared path

/-! ## Constants and global expectations -/

@[command_elab Lang.constCmd] def elabConst : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
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
    lintRelTypes modName stx[4]
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := (← getState).placeholders.contains type.constName
    unless Core.constantAccepted abstract false do
      throwErrorAt stx[4] (Core.unknownConstantMsg abstract).text
    let t ← toTerm { modName, vars := #[], insts := #[], place := .prop, emptyOk := Core.Position.declared.checked false false, natOk := type.isConstOf ``Nat } stx[6]
    if type.isConstOf ``Nat then checkNat stx[6] t s!"note: `{n}` has type `Nat`"
    let value ← elabProp t type
    let applies ← applications { modName, vars := #[], insts := #[], place := .prop } stx[6]
    unless Core.constantAccepted abstract !applies.isEmpty do
      throwErrorAt applies[0]! (Core.unknownConstantMsg abstract).text
    lintBools stx[6]
    addDecl (.defnDecl { name := decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
    record (.item { item := { kind := .constItem, path, isPub, owner := modName }, ref := nameStx })
    let int? ← if type.isConstOf ``Int || type.isConstOf ``Nat then intConstValue? { modName, vars := #[], insts := #[], place := .prop } stx[6]
      else pure none
    record (.constInfo { path, decl, type, value, int? })
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
  modifyLocal fun l => { l with outsideCore := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binderStxs.flatMap (·[1].getArgs)
  for x in binderIds do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt binderIds[k]! (Core.dupBinderMsg declared[k]!).text
  for b in binderStxs do
    let r ← resolvePath modName (pathSegs b[3])
    let .item { kind := .compItem, path, .. } := r | throwErrorAt b[3] (Core.notACompMsg r).text
    let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
    unless c.decidable do
      modifyLocal fun l => { l with outsideCore := true }
      recordLint .undecidable b[3] (Core.undecidableInstMsg path)
    noteCounts c b[3]
    for x in b[1].getArgs do
      let w := (declaredIdent x).1.getId
      let x ← declare x modName
      liftMsg x (Core.checkItemName "instance" w)
      lintName .instance w x
      binders := binders.push { name := w, ref := x, comp := c, offset := vars.size }
      -- Like an instance's, but its inputs are shown in counterexamples.
      vars := vars ++ c.vars.map fun v =>
        let role := Core.Role.ofInst v.role v.isPub
        { name := w ++ v.name, role, isPub := role != .instHidden, type := v.type, ref := x : Var }
  withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
    let cx : ExprCtx := { modName, vars, insts := binders.map (·.name), place := .prop, inGlobal := true }
    discard (takeIndexes fvs)
    let e ← elabProp (← toTerm cx body)
    let indexes := (← takeIndexes fvs).map fun (r, g) => (n, Core.IndexPlace.prop, r, g)
    lintBools body
    lintConstant cx "expect" body
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
             decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied, indexes }

/-- The text of the global expectation `stx` that `duplicate_constraint`
compares: after its name, without the parentheses around its body. -/
def globalText (stx : Syntax) : String :=
  let body := unparen stx[4]
  match stx[1].getTailPos?, body.getPos?, stx.getSubstring? false false with
  | some a, some b, some sub => String.Pos.Raw.extract sub.str a b ++ exactText body
  | _, _, _ => exactText body

@[command_elab Lang.globalCmd] def elabGlobal : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let nameStx := stx[1]
  let n ← segName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  startDeclared
  -- `duplicate_constraint` (`lint::duplicate_constraint`), against the
  -- earlier ones of its module.
  let text := globalText stx
  let l ← getLocal
  if let some (_, earlier, _) := l.globalTexts.find? fun (m, _, t) => m == modName && Core.writtenSame t text then
    let msg := Core.duplicateConstraintMsg .expect .expect earlier.toString
    recordLint .duplicateConstraint nameStx (if l.inMarkdown then msg.note Core.fixHelp else msg)
  modifyLocal fun l => { l with globalTexts := l.globalTexts.push (modName, n, text) }
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let binders := if stx[3].isNone then #[] else stx[3][1].getArgs
  let info ← liftTermElabM <| elabGlobalInfo modName n nameStx binders stx[4] decl
  lintDeclared .global n nameStx
  let all ← evidenceTested nameStx (fren.evidence.get (← getOptions))
  let info := { info with tested := Core.Tested.ofSettings all #[] #[(n, none)] #[] #[] }
  record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
  record (.globalInfo path info)
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  modifyLocal fun l => { l with globals := l.globals.push path }.declared path

/-! ## Refinements -/

/-- Elaborates `refine r: c refines a { bindings }` into the comp that
checks it (`Reqs/Lang/Refinement`): `c`'s inputs, `a`'s assumptions, an
instance of `c` named as it is, `a`'s instances, and `a`'s requirements
and definitions as expectations, with `a`'s variables read as their
bindings or as `c`'s of the same names, and `c`'s outputs from the
instance. With `by`, the tactics prove the obligation, generated as `r`,
and the solver is asked nothing. -/
@[command_elab Lang.refineCmd] def elabRefine : CommandElab := recordingErrors fun stx => do
  -- Its proof, after `by`, is Lean.
  let spec := stx.getArgs[:7].toArray
  spec.forM checkLexemes
  spec.forM checkParsed
  lintInvisible stx
  let modName := (← getLocal).currentModule
  let nameStx := stx[1]
  let n ← segName nameStx
  liftMsg nameStx (Core.checkItemName "refinement" n)
  checkFresh modName n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  let compOf (p : Syntax) : CommandElabM CompInfo := do
    let r ← resolvePath modName (pathSegs p)
    let .item { kind := .compItem, path := cp, .. } := r | throwErrorAt p (Core.notACompMsg r).text
    let some c := (← getState).comps.get? cp | throwError "internal error: unknown comp `{cp}`"
    return c
  let c ← compOf stx[3]
  let a ← compOf stx[5]
  let bs := if stx[6].isNone then #[] else stx[6][1].getSepArgs
  let bound := bs.map (·[0].getId)
  -- The bindings (`refinement::binding`).
  match Core.checkRefineBindings a.path ((a.vars.filter (·.name.isAtomic)).map (·.name)) bound with
  | .ok () => pure ()
  | .error (i, msg) => throwErrorAt bs[i]![0] msg.text
  -- The interface (`refinement::interface`), for the variables not bound.
  for v in a.vars.filter fun v => v.name.isAtomic && !bound.contains v.name do
    let cv? := c.vars.find? (·.name == v.name)
    let input := v.role == Core.Role.input
    -- Widening in the direction values flow: an input's from `a`, an
    -- output's from `c` (`lang::widening`).
    let widensTo (s t : Expr) := s == t || (s.isConstOf ``Nat && t.isConstOf ``Int)
    let widens (cv : Var) := if input then widensTo v.type cv.type else widensTo cv.type v.type
    let ok := Core.interfaceAccepted input cv?.isSome (cv?.any (·.role == Core.Role.input)) (cv?.any (·.isPub))
      (cv?.any (widensTo v.type ·.type)) (cv?.any (widensTo ·.type v.type))
    unless ok do
      let why := match cv? with
        | none => s!"it has no variable `{v.name}`"
        | some cv => if !widens cv then s!"its `{v.name}` has another type"
          else if input then s!"its `{v.name}` is not an input"
          else if cv.role == Core.Role.input then s!"its `{v.name}` is an input, not an output"
          else s!"its output `{v.name}` is not public"
      throwErrorAt stx[5] (Core.interfaceMsg c.path a.path v.name why).text
  let w := Name.mkSimple c.path.getString!
  if a.insts.any (·.name == w) then throwErrorAt stx[5] (Core.dupMemberMsg w).text
  let tested := Core.Tested.ofSettings (← evidenceTested nameStx (fren.evidence.get (← getOptions)))
    -- The bindings too, for the definedness of their indexes.
    (a.assumes.map (·.name) ++ bound) ((a.reqs.map (·.name) ++ a.defs.map (·.1)).map (·, none))
    -- `a`'s instances too, for the definedness of their bindings.
    (#[(w, none)] ++ a.insts.map (·.name, none)) #[]
  let proof? := if stx[7].isNone then none else some stx[7][1]
  let info ← liftTermElabM do
    -- The bindings, over `c`'s own variables, seen from outside, as the
    -- instance's: a defined output is an output (`refinement::mention`).
    let own := (c.vars.filter (·.name.isAtomic)).map fun v =>
      { v with role := if v.role == .input then .input else Core.Role.ofInst v.role v.isPub, defn? := none }
    -- The mix of relational operators and counting, as in a component
    -- (`Reqs/Lang/Decidability#relations`): `c`'s, `a`'s and the bindings'.
    modifyLocal fun l => { l with outsideCore := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
    noteCounts c stx[3]
    noteCounts a stx[5]
    let bindingsA ← withLocalDeclsD (own.map fun v => (v.name, fun _ => pure v.type)) fun cfvs => do
      discard (takeIndexes cfvs)
      bs.mapM fun b => do
        let x := b[0]
        let some v := a.vars.find? (·.name == x.getId) | throwError "internal error: no variable for `{x.getId}`"
        let cx : ExprCtx := { modName, vars := own, insts := #[], place := .prop
                              refining? := some { concrete := c.path, abstract := a.path, input := v.role == .input } }
        let t ← if b[1].isNone then toTerm cx (← pathExpr x x.getId)
          else toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := v.type.isConstOf ``Nat } b[1][1]
        if v.type.isConstOf ``Nat then
          checkNat (if b[1].isNone then x else b[1][1]) t s!"note: `{x.getId}` of `{Core.showPath a.path}` has type `Nat`"
        unless b[1].isNone do lintBools b[1][1]
        let e ← mkLambdaFVars cfvs (← elabProp t v.type)
        return (v, e, ← takeIndexes cfvs)
    let (relational, counts) ← checkCounts
    let l ← getLocal
    -- An input that `a` reads has `a`'s type, which widens to `c`'s
    -- (`refinement::interface`).
    let inputs := (c.vars.filter fun v => v.name.isAtomic && v.role == .input).map fun v =>
      match a.vars.find? fun u => u.name == v.name && u.role == .input && !bound.contains u.name with
      | some u => { v with type := u.type }
      | none => v
    let vars := inputs ++ c.vars.map (fun v =>
        let role := Core.Role.ofInst v.role v.isPub
        { v with name := w ++ v.name, role, isPub := role != .instHidden, isDet := false, defn? := none, ref := nameStx })
      ++ a.vars.filter (!·.name.isAtomic)
    withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let fvOf (x : Name) : Expr := fvs[(vars.findIdx? (·.name == x)).getD 0]!
      -- `c`'s variables as a binding reads them, its outputs from the instance.
      -- An input of `a`'s type `Nat`, read where `c`'s `Int` is, is widened.
      let ownC := own.map fun v =>
        let x := fvOf (if v.role == .input then v.name else w ++ v.name)
        if v.role == .input && v.type.isConstOf ``Int && (vars.find? (·.name == v.name)).any (·.type.isConstOf ``Nat) then
          mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) x else x
      -- `a`'s variables: their bindings, or else `c`'s of the same names.
      let argsA := a.vars.map fun v => match bindingsA.find? (·.1.name == v.name) with
        | some (_, e, _) => e.beta ownC
        | none =>
          let n := if v.name.isAtomic && v.role == .output then w ++ v.name else v.name
          -- `c`'s `Nat`, read as `a`'s `Int`, is widened (`lang::widening`).
          if v.type.isConstOf ``Int && (vars.find? (·.name == n)).any (·.type.isConstOf ``Nat) then
            mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) (fvOf n)
          else fvOf n
      let sliceC := c.vars.map fun v => fvOf (w ++ v.name)
      let lam (e : Expr) : TermElabM Expr := mkLambdaFVars fvs e
      let reported (p : PropInfo) := { p with ref := nameStx, trigger? := none, triggerRef? := none }
      let assumes ← a.assumes.mapM fun p => return { reported p with body := ← lam (p.body.beta argsA) }
      let reqs ← a.reqs.mapM fun p => return { reported p with kind := .expect, body := ← lam (p.body.beta argsA) }
      let defs ← a.defs.mapM fun (d, e) => do
        let i := (a.vars.findIdx? (·.name == d)).getD 0
        return { kind := .expect, name := d, ref := nameStx, trigger? := none, triggerRef? := none, decl := decl ++ d
                 body := ← lam (← mkEq argsA[i]! (e.beta argsA)) : PropInfo }
      -- `a`'s `Nat`, given to `c`'s `Int`, is widened.
      let bindings ← inputs.mapM fun v => do
        let x := fvOf v.name
        let x := if v.type.isConstOf ``Nat && (vars.find? (·.name == w ++ v.name)).any (·.type.isConstOf ``Int) then
          mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) x else x
        mkEq (fvOf (w ++ v.name)) x
      let instC : InstInfo := { name := w, comp := c.path, ref := nameStx, decl
                                bindings := ← lam (mkAndN bindings.toList)
                                behaviour := ← lam (c.meaning sliceC)
                                assumes := ← c.assumes.mapM fun p => return (p.name, ← lam (p.body.beta sliceC)) }
      -- `a`'s instances are hypotheses: their assumptions are `a`'s own
      -- obligations, checked in `a` (`Reqs/Lang/Refinement#the-obligation`).
      let instsA ← a.insts.mapM fun i => return { i with
        bindings := ← lam (i.bindings.beta argsA), behaviour := ← lam (i.behaviour.beta argsA), assumes := #[] }
      -- Reported at the refinement, as its other checks are.
      let indexes ← a.indexes.mapM fun (x, place, _, goal) => do
        let place := match place with | .binding k => .binding (k + 1) | p => p
        return (x, place, nameStx, ← lam (goal.beta argsA))
      -- A binding's, where it is read (`Reqs/Lang/Refinement#bindings`):
      -- an input's under the assumptions, an output's as a requirement.
      let indexes := indexes ++ (← bindingsA.flatMapM fun (v, _, idx) => idx.mapM fun (r, goal) => do
        return (v.name, if v.role == .input then .binding 0 else .prop, r, ← lam (goal.beta ownC)))
      -- The obligation: `A_a → A_c ∧ (I_c ∧ R_c ∧ D_c ∧ I_a → R_a ∧ D_a)`.
      let hypsA := mkAndN (assumes.map (·.body.beta fvs)).toList
      let goal := mkAnd (mkAndN (instC.assumes.map (·.2.beta fvs)).toList)
        (← mkArrow (mkAndN ((#[instC] ++ instsA).map fun i => mkAnd (i.bindings.beta fvs) (i.behaviour.beta fvs)).toList)
          (mkAndN ((reqs ++ defs).map (·.body.beta fvs)).toList))
      let value ← mkForallFVars fvs (← mkArrow hypsA goal)
      let uses ← usesOf #[value]
      addUsesDef uses decl value
      return { path, vars, props := assumes ++ reqs ++ defs, insts := #[instC] ++ instsA, ref := nameStx, decl, uses
               decidable := c.decidable && a.decidable && !l.outsideCore
               undecidableDenied := c.undecidableDenied || a.undecidableDenied || l.undecidableDenied
               relational, counts, indexes, tested : CompInfo }
  record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  match proof? with
  | none =>
    record (.refinementInfo info)
    modifyLocal fun l => { l with refinements := l.refinements.push path }.declared path
  -- A proof: no check of the refinement is asked of the solver
  -- (`Reqs/Lang/Refinement#evidence`).
  | some tac => liftTermElabM do
    let type ← withUses info.uses fun xs => mkForallFVars xs (mkAppN (mkConst decl) xs)
    let tacs : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨tac⟩
    let pf ← Term.elabTermEnsuringType (← `(by $tacs)) type
    Term.synthesizeSyntheticMVarsNoPostponing
    addDecl (.thmDecl { name := decl ++ `proof, levelParams := [], type, value := ← instantiateMVars pf })

end Fren
