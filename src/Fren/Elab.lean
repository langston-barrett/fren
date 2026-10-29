-- keep-sorted start
import Fren.FinSet
import Fren.Finite
import Fren.Lint
import Fren.Model
import Fren.SeqElems
import Fren.SimpSet
import Fren.Syntax
import FrenCore.Checking
import FrenCore.Closures
import FrenCore.FnBlocks
import FrenCore.Generics
import FrenCore.Global
import FrenCore.Guards
import FrenCore.Lexical
import FrenCore.Mentions
import FrenCore.Patterns
import FrenCore.Procedures
import FrenCore.Quantifier
import FrenCore.Regex
import FrenCore.Syntax
import FrenCore.Ty
import FrenCore.TypeFacts
import FrenCore.Typing
-- keep-sorted end

/-!
# Elaborators

These are the only code that changes the Fren model. Each records Fren's own
representation of a declaration, then generates ordinary Lean declarations
from it (an `inductive` per enum; a `def` per constant; a `def` per
`assume`/`ensure`/`expect`, plus `assumes` and `ensures`, per procedure; a `def` per
global expectation) so that specs can be used from Lean.
-/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of this
-- file's hundreds of indexes. This rule, tried first, proves it at once, and fails
-- at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Whether `e` is a `match`, or a table over a scrutinee, which means
one. Access their columns and arms through the helpers below. -/
def isMatchLike (e : Syntax) : Bool := e.isOfKind ``Lang.matchExpr || e.isOfKind ``Lang.tableMatchExpr ||
  e.isOfKind ``Lang.matchManyExpr || e.isOfKind ``Lang.tableMatchManyExpr

def isManyMatch (e : Syntax) : Bool := e.isOfKind ``Lang.matchManyExpr || e.isOfKind ``Lang.tableMatchManyExpr

def matchScrutinees (e : Syntax) : Array Syntax :=
  if isManyMatch e then #[e[1]] ++ e[3].getSepArgs else if e.isOfKind ``Lang.lambdaMatchExpr then #[] else #[e[1]]

def matchSourceArms (e : Syntax) : Array Syntax :=
  (if isManyMatch e then e[5] else if e.isOfKind ``Lang.lambdaMatchExpr then e[2] else e[3]).getSepArgs

def matchPatterns (e arm : Syntax) : Array Syntax :=
  if isManyMatch e || e.isOfKind ``Lang.lambdaMatchExpr || arm.isOfKind ``Lang.fren_many_arm then arm[0].getSepArgs else #[arm[0]]

def matchArm (e arm : Syntax) : Syntax :=
  if isManyMatch e || e.isOfKind ``Lang.lambdaMatchExpr || arm.isOfKind ``Lang.fren_many_arm then (mkNode ``Lang.fren_arm ((arm.setArg 0 arm[0].getSepArgs[0]!).getArgs)).raw else arm


/-- The identifiers of a `Lang.fren_path`. -/
def pathSegs (p : Syntax) : Array Syntax :=
  p[0].getSepArgs.map fun segment =>
    if segment.isIdent && segment.getId.hasMacroScopes then
      mkIdentFrom segment segment.getId.eraseMacroScopes
    else segment

/-- The name of the field that `.x` reads, at `s` in a `fieldExpr`: an
identifier, or digits, as the field `0` of a newtype is. -/
partial def fieldName (s : Syntax) : Name :=
  if s.isIdent then s.getId
  else if s.isOfKind fieldIdxKind then Name.mkSimple s[0].getAtomVal
  else if s.getNumArgs == 1 then fieldName s[0]
  else .anonymous

/-- The name that the item declaration `id` declares, without the `!` that
marks it as shadowing one of the prelude's names (`Core.declaredName`). -/
def itemSegName (id : Syntax) : CommandElabM Name := return (Core.declaredName (← segName id)).1

/-- Checks the name of a module, enum, variant or comp; an item's, but a
variant's, without its `!` (`itemSegName`). -/
def checkItemName (what : String) (id : Syntax) : CommandElabM Name := do
  let n ← if what == "variant" then segName id else itemSegName id
  liftMsg id (Core.checkItemName what n)
  return n

/-- Fails if `n` is already declared or imported by name in module `modName`,
or if its declaration `ref`, written `n!` if it shadows, does not mark
that it hides one of the prelude's names exactly when it does
(`Core.Table.checkFreshItem`). -/
def checkFresh (modName n : Name) (ref : Syntax) : CommandElabM Unit := do
  liftMsg ref ((← getState).table.checkFreshItem modName n (Core.declaredName ref.getId).2)

open Lang in
/-- Reports the first identifier or integer literal of `stx` that Lean read
but that is not one of Fren's (`lang::identifier`,
`lang::integer_literal`), or prefix `!`, as the `fren` command's lexer
does. -/
partial def checkLexemes (stx : Syntax) : CommandElabM Unit := do
  if stx.isOfKind ``Lang.refinesMember then
    stx.getArgs[:6].toArray.forM checkLexemes
    return
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

/-- The tokens of `stx`, in order: its atoms and identifiers. -/
partial def tokensOf (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args => args.flatMap tokensOf
  | .missing => #[]
  | _ => #[stx]

open Lang in
/-- Reports the first problem of `stx` that the `fren` command's parser
reports, in source order, before any other check of its item, where Lean's
grammar accepts it:
- a name that is not a single segment. A name may be dotted only where it
  is an expression's whole path, which reads a call's variable or a
  value's field or method, or where it follows `.`, or names an option;
- a member's `set_option` of an option other than `fren.evidence`;
- a parameter's modifier, or its definition, `x := e`, before its
  expression is read;
- an operator of another language, `==`, `&&`, `||` or `|`, after its
  left operand;
- `table` as a name: it is a reserved word, which Lean reads as a name
  where an expression starts, as it reads `when`. -/
partial def checkParsed (stx : Syntax) : CommandElabM Unit := do
  if stx.isOfKind ``Lang.refinesMember then
    stx.getArgs[:6].toArray.forM checkParsed
    return
  let reserved (p : Syntax) : CommandElabM Unit := do
    let id := (pathSegs p)[0]!
    if id.getId.getRoot == Name.mkSimple "table" then throwErrorAt id Core.tableNameMsg
  match stx with
  | `(fren_expr| $a == $_) | `(fren_expr| $a && $_) | `(fren_expr| $a || $_) | `(fren_expr| $a | $_) =>
    checkParsed a
    throwErrorAt stx[1] (Core.foreignOpMsg stx[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| $p:fren_path) =>
    reserved p
    unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
  | `(fren_expr| $p:fren_path($args,*)) =>
    reserved p
    unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
    args.getElems.forM checkParsed
  | _ =>
    if stx.isIdent then discard (segName stx)
    else if stx.isOfKind ``Lang.fren_path then discard (segNames (pathSegs stx))
    else if stx.isOfKind ``Lang.fren_result_evidence then
      unless stx[1].getId == `fren.evidence do
        throwErrorAt stx[1] (Core.memberOptionMsg stx[1].getId.toString).text
    else if stx.isOfKind ``Lang.evidenceMember then
      unless stx[1].getId == `fren.evidence do
        throwErrorAt stx[1] (Core.memberOptionMsg stx[1].getId.toString).text
      checkParsed stx[4]
    else if stx.isOfKind ``Lang.fren_proc_param then
      -- A parameter's modifier or definition, as the `fren` command's
      -- parser reports it.
      unless stx[0].isNone do throwErrorAt stx[0] (Core.paramModifierMsg ((stx[0].reprint.getD "").trimAscii.toString)).text
      checkParsed stx[1]
      checkParsed stx[2]
      unless stx[3].isNone do throwErrorAt stx[3][0] Core.inputDefinitionMsg.text
    else if stx.isOfKind ``Lang.fieldExpr || stx.isOfKind ``Lang.methodExpr then
      stx.getArgs.forM fun a => unless a.isIdent do checkParsed a
    else stx.getArgs.forM checkParsed

/-- Records `unnecessary_trailing_comma` on the commas of the command `stx`
that end a list on the line of its `}` or `]`
(`lint::unnecessary_trailing_comma`). -/
def lintTrailingCommas (stx : Syntax) : CommandElabM Unit := do
  let toks := tokensOf stx
  -- Each token's text, and whether a line ends between it and the one before.
  let texts := toks.mapIdx fun i t =>
    let lineBreak := (toks[i - 1]?.bind (·.getTrailing?)).any (·.toString.contains '\n')
    ((if t.isAtom then t.getAtomVal.trimAscii.toString else ""), i > 0 && lineBreak)
  let fixable := (← getLocal).inMarkdown
  for i in Core.trailingCommas texts do
    let msg := Core.unnecessaryTrailingCommaMsg texts[i + 1]!.1
    recordLint .unnecessaryTrailingComma toks[i]! (if fixable then msg.note Core.fixHelp else msg)

@[command_elab Lang.modCmd] def elabMod : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  let segs := pathSegs stx[2]
  -- A path that did not parse, as in `mod 2`, which Lean has reported.
  if segs.isEmpty || segs.any (·.getId.isAnonymous) then return
  let names ← segNames segs
  let (path, new) ← liftResolve segs ((← getState).table.declareModule names (!stx[0].isNone))
  for i in new do
    let ref := (segs[i.path.components.length - 1]?).getD stx
    lintName .module (Name.mkSimple i.path.getString!) ref
    if let some msg := Core.moduleInceptionMsg? i.path then recordLint .moduleInception ref msg
    if let some msg := Core.moduleNameMsg? .module i.path.getPrefix (Name.mkSimple i.path.getString!) then
      recordLint .moduleNameRepetitions ref msg
    record (.item { item := i, ref })
  modifyLocal ({ · with currentModule := path })

/-- Imports the path `segs`, written at `ref`, into the current module, or,
with `scope`, into the procedure of that path. -/
def declareUse (segs : Array Syntax) (glob : Bool) (ref : Syntax) (scope : Option Name := none) : CommandElabM Unit := do
  let modName := (← getLocal).currentModule
  let u ← liftResolve segs ((← getState).table.declareUse modName (← segNames segs) glob (scope.getD modName))
  record (.useDef u)
  recordUse u ref

@[command_elab Lang.useCmd] def elabUse : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  declareUse (pathSegs stx[1]) (!stx[2].isNone) stx[1]

@[command_elab Lang.useGroupCmd] def elabUseGroup : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  for p in stx[3].getSepArgs do
    declareUse (pathSegs stx[1] ++ pathSegs p) false p

/-- The path of a type written as one, or `none` for `Set<T>`, `Rel<A, B>`
and an instance of a generic type. -/
def typePath? (ty : Syntax) : Option Syntax :=
  if ty.isOfKind ``Lang.fren_path then some ty
  else if ty.isOfKind ``Lang.setType || ty.isOfKind ``Lang.relType || ty.isOfKind ``Lang.seqType
    || ty.isOfKind ``Lang.instanceType then none
  else some ty[0]

/-- The type `ty` as its segments, as the `fren` command's parser has it
(`Core.ownIn`). -/
partial def typeSegs (ty : Syntax) : Array String :=
  if ty.isOfKind ``Lang.setType then #[Core.setSeg] ++ typeSegs ty[2]
  else if ty.isOfKind ``Lang.seqType then #[Core.seqSeg] ++ typeSegs ty[2]
  else if ty.isOfKind ``Lang.relType then #[Core.relSeg] ++ typeSegs ty[2] ++ #[Core.relSep] ++ typeSegs ty[4]
  -- A function type (`Reqs/Lang/HigherOrder#function-types`).
  else if ty.isOfKind ``Lang.fnType then
    let ps := (ty[2].getSepArgs.map typeSegs).toList.intersperse #[Core.fnSep]
    #[Core.fnSeg] ++ ps.foldl (· ++ ·) #[] ++ #[Core.fnArrow] ++ typeSegs ty[5]
  else if ty.isOfKind ``Lang.instanceType then
    let args := (ty[2].getSepArgs.map typeSegs).toList.intersperse #[Core.argsSep]
    (pathSegs ty[0]).map (·.getId.toString) ++ #[Core.argsOpen] ++ args.foldl (· ++ ·) #[] ++ #[Core.argsClose]
  else match typePath? ty with
    | some p => (pathSegs p).map (·.getId.toString)
    | none => #[]

/-- The Lean types within the `Fren.FinSet`s and pairs of `t`. -/
partial def elemTypes (t : Expr) : Array Expr :=
  if t.isAppOfArity ``Fren.FinSet 1 || t.isAppOfArity ``Fren.Seq 1 then elemTypes t.appArg!
  else if t.isAppOfArity ``Prod 2 then elemTypes t.appFn!.appArg! ++ elemTypes t.appArg!
  else #[t]

/-- The abstract type that the Lean type `t` is, or that is an element type
within it (`Core.Ty.abstractWithin?`), and whether it is `t` itself. -/
def abstractWithin? [Monad m] [MonadEnv m] (t : Expr) : m (Option (Name × Bool)) := do
  let st ← getState
  -- A generic function's type parameter may be anywhere a type is
  -- (`Core.Ty.abstractWithin?`).
  let some e := (elemTypes t).find? fun e => e.isConst && st.placeholders.contains e.constName
    && (Core.typeParamName? e.constName).isNone | return none
  let p := st.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == e.constName then some a.path else none
  return some (p.getD .anonymous, e == t)

/-- The Lean type of the type named by the path `segs`, with the type
arguments `args`, as many as its type parameters (`lang::type_arguments`),
written at `ref`; `params` are the type parameters in scope. -/
def instanceType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name)
    (segs : Array Syntax) (args : Array Expr) (params : Array Name) (ref : Syntax) : m Expr := do
  let one := segs.size == 1
  let builtin := one && [`Bool, `Int, `Nat, `String, `Set, `Seq, `Rel].contains segs[0]!.getId
  let fnParam := one && ((← getLocal).fnTypeParams.any (·.2.contains segs[0]!.getId))
  if builtin || fnParam || (one && params.contains segs[0]!.getId) then
    unless Core.writtenArgumentsAccepted (if builtin then .builtin else .parameter) 0 args.size do
      throwErrorAt ref (Core.typeArgsMsg segs[0]!.getId.toString #[] args.size).text
  let arity (named : Core.TypeNamed) (path : Name) (ps : Array Name) : m Unit := do
    unless Core.writtenArgumentsAccepted named ps.size args.size do
      throwErrorAt ref (Core.typeArgsMsg (Core.showPath path) ps args.size).text
  match ← resolveWritten modName segs with
  | .item { kind := .enumItem, path, .. } =>
    let some e := (← getState).enums.get? path | throwError "internal error: unknown enum `{path}`"
    arity .data path e.params
    return mkAppN e.const (e.leanArgs args)
  | .item { kind := .recordItem, path, .. } =>
    if let some n := (← getState).newtypes.get? path then
      arity .other path #[]
      return Lean.mkConst n.decl
    let some r := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
    arity .data path r.params
    return mkAppN (Lean.mkConst r.decl) args
  | .item { kind := .typeItem, path, .. } =>
    arity .other path #[]
    if let some (t, _) := (← getState).aliases.get? path then return t
    return Lean.mkConst (placeholderName path)
  | r => throwErrorAt ref (Core.notATypeMsg r).text

/-- Whether a function type is written within the type `ty`, or is `ty`. -/
partial def hasFnType (ty : Syntax) : Bool := ty.isOfKind ``Lang.fnType || ty.getArgs.any hasFnType

/-- A function type written `ty` at `site`, where it may not be
(`lang::function_type_place`); a function type within another is reported
where that one is elaborated. -/
def checkFnTypeSite [Monad m] [MonadError m] (site : Core.TypeSite) (ty : Syntax) : m Unit := do
  if ty.isOfKind ``Lang.fnType then throwErrorAt ty (Core.fnTypePlaceMsg site []).text

/-- The Lean type of the Fren type `ty`. Within the declaration of a generic
type, its type parameters `params` are types, the `k`th the loose bound
variable `.bvar k` (`Reqs/Lang/Generics`). -/
partial def elabType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name) (ty : Syntax)
    (params : Array Name := #[]) : m Expr := do
  -- A function type is only a defined function's parameter's, which
  -- `fnParamType` elaborates (`lang::function_type_place`).
  if let some w := Core.fnTypeWithin (typeSegs ty).toList then throwErrorAt ty (Core.fnTypePlaceMsg .constant w).text
  -- `Set<T>`: `"Set" "<" T ">"`; `Rel<A, B>`: `"Rel" "<" A "," B ">"`.
  -- An element type, which is never a `Nat` (`lang::nat_place`), nor a type
  -- parameter (`lang::type_parameter_place`).
  let elem (e : Syntax) : m Expr := do
    let t ← elabType modName e params
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
    if let .bvar k := t then throwErrorAt e (Core.typeParamPlaceMsg params[k]! .element "").text
    if let some n := t.constName?.bind (Core.typeParamName? ·) then
      throwErrorAt e (Core.typeParamPlaceMsg (Name.mkSimple n) .element "").text
    return t
  -- An instance of a generic type, `G<A, B>`, whose arguments are payloads'
  -- types (`Reqs/Lang/Generics#type-parameters`).
  if ty.isOfKind ``Lang.instanceType then
    let segs := pathSegs ty[0]
    let given := ty[2].getSepArgs
    -- `Set`, `Seq` and `Rel` with too many or too few types, which the
    -- `fren` command's parser reports, at what follows the types it reads.
    if segs.size == 1 && [`Set, `Seq, `Rel].contains segs[0]!.getId then
      let n := if segs[0]!.getId == `Rel then 2 else 1
      let at_ := if given.size > n then ty[2].getArgs[2 * n - 1]! else ty[3]
      throwErrorAt at_ s!"expected `{if given.size > n then ">" else ","}`"
    let mut args := #[]
    for a in given do
      let t ← elabType modName a params
      unless !t.isConstOf ``Nat || Core.natPlaceAccepted .argument do throwErrorAt a (Core.natPlaceMsg .argument).text
      if let some (p, whole) ← abstractWithin? t then throwErrorAt a (Core.abstractFieldMsg p true !whole).text
      args := args.push t
    return ← instanceType modName segs args params ty
  let some p := typePath? ty |
    if ty.isOfKind ``Lang.relType then
      return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero])
        (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← elem ty[2]) (← elem ty[4]))
    else if ty.isOfKind ``Lang.seqType then return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← elem ty[2])
    else return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (← elem ty[2])
  let segs := pathSegs p
  if segs.size == 1 then
    if let some k := params.idxOf? segs[0]!.getId then return .bvar k
    -- A generic function's type parameter, an abstract type within it
    -- (`Reqs/Lang/GenericFunctions#type-parameters`).
    if let some (fn, ps) := (← getLocal).fnTypeParams then
      if let some k := ps.idxOf? segs[0]!.getId then
        return Lean.mkConst (placeholderName (Core.typeParamPath fn k ps[k]!))
  if segs.size == 1 && segs[0]!.getId == `Bool then return Lean.mkConst ``Bool
  if segs.size == 1 && segs[0]!.getId == `Int then return Lean.mkConst ``Int
  if segs.size == 1 && segs[0]!.getId == `Nat then return Lean.mkConst ``Nat
  if segs.size == 1 && segs[0]!.getId == `String then return Lean.mkConst ``String
  instanceType modName segs #[] params p

/-- The `Rel<A, B>`s within the type `ty`. -/
partial def relTypes (ty : Syntax) : Array Syntax :=
  (if ty.isOfKind ``Lang.relType then #[ty] else #[]) ++ ty.getArgs.flatMap relTypes

/-- Records `zero_sized_map_values` on each `Rel<A, B>` within the type
`ty` whose `B` is an enumeration of one variant without a payload
(`lint::zero_sized_map_values`). -/
def lintRelTypes [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name)
    (ty : Syntax) (params : Array Name := #[]) : m Unit := do
  for r in relTypes ty do
    let b ← elabType modName r[4] params
    let some e := (← getState).enumOf? b | continue
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

/-- What a field's or payload's type is declared in: a payload of an
enumeration, a field of a record, or a newtype's. -/
inductive FieldPlace where
  | payload
  | field
  | newtype
  deriving BEq

/-- Lean syntax for the Lean type of a Fren type: a constant, or one applied
to type arguments; within the declaration of a generic type, `.bvar k` is
its type parameter `params[k]`. -/
partial def typeSyntax (t : Expr) (params : Array Name := #[]) : Term :=
  let go (t : Expr) := typeSyntax t params
  if t.isAppOfArity ``Fren.FinSet 1 then Unhygienic.run `(Fren.FinSet $(go t.appArg!))
  else if t.isAppOfArity ``Fren.Seq 1 then Unhygienic.run `(Fren.Seq $(go t.appArg!))
  else if t.isAppOfArity ``Prod 2 then Unhygienic.run `($(go t.appFn!.appArg!) × $(go t.appArg!))
  else if let .bvar k := t then mkIdent (params[k]?.getD `_)
  else if t.isConst then mkCIdent t.constName!
  else if t.getAppFn.isConst then
    Unhygienic.run `(($(mkCIdent t.getAppFn.constName!) $(t.getAppArgs.map go)*))
  -- Not known yet, as the element type of `[]`: Lean infers it.
  else Unhygienic.run `(_)

/-! ## Comps -/

/-- The placeholder of the abstract type or function at `path`. -/
def placeholderOf (path : Name) : TermElabM AbstractInfo := do
  let some a := (← getState).abstracts.get? path | throwError "internal error: unknown abstract item `{path}`"
  return a

/-- A binder of a `match` pattern, a quantifier's bound name, or a name of a
`let` or `where` (`isDef`), in scope. -/
structure MatchBinder where
  name : Name
  /-- Its value: the selector applied to the scrutinee, the local of the
  `have` that defines the name, or for a bound name, a local that each
  instance replaces with a value. -/
  term : Term
  type : Expr
  /-- Its scrutinee or definition, and the number of binders in scope
  there: mentioning it counts as mentioning what that mentions. A bound
  name has none, and mentions nothing. -/
  scrutinee : Option Syntax
  outer : Nat
  isDef : Bool := false
  /-- For a name, its written type, which is expected of its definition. -/
  annot? : Option Core.Ty := none
  /-- For a name, the indexes of its definition, each with the term that it
  is in range, guarded only within the definition: a mention puts them
  under its own guards (`Reqs/Lang/Let#meaning`). -/
  obligations : Array (Syntax × Term) := #[]
  /-- Likewise, the questions about the rows of its definition's tables. -/
  tableObligations : Array (Syntax × Core.TableGoal × Term) := #[]
  /-- A bound name of a type that is not listed, of an unbounded quantifier,
  which Lean's `∀` or `∃` binds: within the body, it mentions itself, as a
  variable does. -/
  unbounded : Bool := false
  /-- A closure's parameter, which its `fun` binds: what an `Expr` within
  its body mentions of it is closed over it, as of a definition
  (`quantTerm`). -/
  closure : Bool := false
  /-- For a binder in a defined function's body, the position of the
  parameter that it is bound from a payload of, directly or nested
  (`lang::structural_recursion`). -/
  payloadOf? : Option Nat := none

/-- A clause of the contract of the function at `path`, whose parameters
are `params`: whether it is a postcondition (`lang::contract_application`). -/
structure ContractCx where
  path : Name
  post : Bool
  params : Array Name
  deriving Inhabited

/-- What expression translation needs to know about the comp. -/
structure ExprCtx where
  modName : Name
  vars : Array Var
  /-- The procedure's calls, in order. -/
  insts : Array Name
  place : Core.Place
  /-- For a binding, the index of its call. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array MatchBinder := #[]
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a defined function's body, if it may recurse
  (`lang::structural_recursion`): its parameters' names, its type, and the
  local that stands for it. -/
  selfRec? : Option (Array Name × Core.FnTy × Term) := none
  /-- In a higher-order function's body or contract, its function
  parameters: each one's name, type and term
  (`Reqs/Lang/HigherOrder#function-parameters`). -/
  fnParams : Array (Name × Core.FnTy × Term) := #[]
  /-- In a closure's body, which applies no uninterpreted function. -/
  inClosure : Bool := false
  /-- In a clause of a function's contract, the function. -/
  contract? : Option ContractCx := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- Something here gives `{}` its type (`Reqs/Lang/Expressions#sets`). -/
  emptyOk : Bool := false
  /-- The Fren type expected here, as the `fren` command's `expected?`: a
  declared type, or a sibling's. Only parentheses, a conditional's branches
  and a `match`'s arms pass it on; `{}` and `[]` check themselves against
  it (`Reqs/Lang/Types#checking-and-synthesis`). -/
  expected? : Option Core.Ty := none
  /-- A `Nat` is expected here, so an integer literal is one
  (`lang::literal_type`). -/
  natOk : Bool := false
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array Term := #[]
  /-- Whether to record the indexes and tables of this expression for their
  checks, and report its lints: not when it is elaborated a second time, as
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
  /-- In a definition of a `let` or `where`, the names of it and of the
  later definitions of its clause that hide nothing, each with whether it
  is its own: a mention of one is used before its definition
  (`lang::definition_order`). -/
  pending : Array (Name × Bool) := #[]
  /-- In a definition of a `let` or `where` that nothing mentions, which
  counts for nothing: what it may mention, linear arithmetic and the
  decidable core are not checked in it (`Reqs/Lang/Let#meaning`). -/
  unmentioned : Bool := false
  /-- What the chain of `and` that this expression is an operand of, or is,
  is a part of, for its pattern tests (`lang::test_scope`). Only `and`,
  `is` and parentheses read it, and only their operands see it. -/
  testContext : Core.TestContext := .standalone
  /-- For an operand of a chain of `and`, its position in the chain and the
  chain's number of operands. -/
  testAt? : Option (Nat × Nat) := none
  /-- The members' expressions of the guards of the quantifiers over
  elements around this expression, by where they are
  (`LocalState.elemMembers`). -/
  elemGuards : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- Within the body of a quantifier over elements: whether it is a
  `forall`; and the quantifiers that are directly its body, or the body of
  one of those (`Core.ElementNesting`). -/
  elemKind? : Option Bool := none
  elemDirect : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- The bound names of the quantifiers over elements, of the same kind,
  that this expression is directly the body of, which its quantifier may
  mention (`Core.ElementVerdict.mentionsBound`). -/
  elemChain : Array Name := #[]
  /-- Translating a defined function's body a second time, for its Lean
  definition, where a `match` is Lean's own where it can be
  (`Reqs/Generated#matches`). -/
  leanMatch : Bool := false
  /-- Translating a structural recursion's body for its Lean definition,
  where a `match` whose arms are propositions is a Lean `match` of their
  `decide`s, so that Lean's structural recursion sees through it
  (`lang::recursive_match`). -/
  leanBoolArms : Bool := false

/-- What the binder `b` is, for a declaration that hides it (`Core.bindingLocals`). -/
def MatchBinder.what (b : MatchBinder) : Name × Core.BindingKind :=
  (b.name, if b.scrutinee.isNone then .boundName else if b.isDef then .definition else .patternBinder)

def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option MatchBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : MatchBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name) ++ cx.fnParams.map (·.1)

/-- The function parameter named `n`, with its type and term, if no binder
or variable hides it (`Reqs/Lang/HigherOrder#function-parameters`). -/
def ExprCtx.fnParam? (cx : ExprCtx) (n : Name) : Option (Core.FnTy × Term) :=
  if (cx.binder? n).isSome || cx.vars.any (·.name == n) then none
  else (cx.fnParams.find? (·.1 == n)).map fun (_, t, x) => (t, x)

/-- The names that the pattern tests translated since `LocalState.bound`
had `mark` names bind. -/
def boundSince (mark : Nat) : TermElabM (Array MatchBinder) :=
  return ((← getLocal).bound.extract mark).map fun (name, term, type, sc, outer) =>
    { name, term := ⟨term⟩, type, scrutinee := some sc, outer }

/-- Runs `x`, and returns with its result the names that the pattern tests
that it translates bind (`LocalState.bound`), which it removes: those of
the condition of a `when` or `if` (`lang::test_scope`). -/
def withBound (x : TermElabM α) : TermElabM (α × Array MatchBinder) := do
  let mark := (← getLocal).bound.size
  let r ← x
  let new ← boundSince mark
  modifyLocal fun l => { l with bound := l.bound.extract 0 mark }
  return (r, new)

/-- Whether the path `p` names a variant. -/
def isVariant (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← segNames (pathSegs p)
  return (← getState).table.resolvePath cx.modName names cx.shadowing matches .ok (.variant ..)

/-- Whether the path `p`, applied, builds a variant or a newtype rather
than applying a function. -/
def isConstruction (cx : ExprCtx) (p : Syntax) : TermElabM Bool := do
  let names ← segNames (pathSegs p)
  let s ← getState
  match s.table.resolvePath cx.modName names cx.shadowing with
  | .ok (.variant ..) => return true
  | .ok (.item { kind := .recordItem, path, .. }) => return s.newtypes.contains path
  | _ => return false

/-- The defined function that the path `p`, applied, applies, if any. -/
def definedFn? (cx : ExprCtx) (p : Syntax) : TermElabM (Option DefinedInfo) := do
  let names ← segNames (pathSegs p)
  let s ← getState
  let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
  return s.defined.get? path

/-- The paths of the functions that `e` applies (`unused_assumption`). -/
partial def appliedPaths (e : Syntax) : Array Syntax :=
  if e.isOfKind ``Lang.appExpr then e[2].getSepArgs.foldl (· ++ appliedPaths ·) #[e[0]]
  else e.getArgs.foldl (· ++ appliedPaths ·) #[]

/-- The uninterpreted functions that `e` applies, as links of
`unused_assumption` (`Core.fnLink`). -/
def appliedFns (cx : ExprCtx) (e : Syntax) : TermElabM (Array Name) := do
  let s ← getState
  (appliedPaths e).filterMapM fun p => do
    let some names ← try some <$> segNames (pathSegs p) catch _ => pure none | return none
    let .ok (.item { kind := .fnItem, path, .. }) := s.table.resolvePath cx.modName names cx.shadowing | return none
    return if s.defined.contains path then none else some (Core.fnLink path)

/-- The Lean type `t` as the Fren type it stands for (`coreTy?`), given the
model `s`. -/
partial def coreTyOf (s : State) (t : Expr) (params : Array Name := #[]) : Option Core.Ty :=
  let go (t : Expr) := coreTyOf s t params
  if t.isProp || t.isConstOf ``Bool then some .bool
  else if t.isConstOf ``Int then some .int
  else if t.isConstOf ``Nat then some .nat
  else if t.isConstOf ``String then some .string
  else if let .bvar k := t then some (.param k (params[k]?.getD .anonymous))
  else if t.isAppOfArity ``Fren.Seq 1 then (go t.appArg!).map .seq
  else if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then do
      return .rel (← go e.appFn!.appArg!) (← go e.appArg!)
    else (go e).map .set
  else if let some e := s.enumOf? t then do
    return .enum e.path (← (e.frenArgs t.getAppArgs).toList.mapM go)
  else if let some r := s.recordOf? t then do
    return .record r.path (← t.getAppArgs.toList.mapM go)
  else match t.constName? with
    | none => none
    | some d =>
      if let some n := s.newtypeOfDecl? d then (go n.under).map (.newtype n.path)
      else (s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none).map
        (.abstract ·.path)

/-- What counting the values of the instances of the enumeration or record
`p` needs of its declaration (`Core.Ty.valueCount`), given the model `s`. -/
def dataSig (s : State) (p : Name) : Option Core.DataSig :=
  let tys (params : Array Name) (ts : Array Expr) := ts.map fun t => (coreTyOf s t params).getD (.abstract .anonymous)
  match s.enums.get? p, s.records.get? p with
  | some e, _ => some { isRecord := false, unbounded := e.unbounded, ctors := e.payloads.map (tys e.params) }
  | none, some r => some { isRecord := true, unbounded := r.unbounded, ctors := #[tys r.params (r.fields.map (·.2))] }
  | none, none => none

/-- The facts of the declared type `t` (`lang::type_facts`), from the
declarations as both front ends give them to `Core.typeFacts`. -/
def factsOf (s : State) (t : Core.PTy) : Core.TypeFacts := Core.typeFacts s.shapeOf t.node

/-- The facts of the Lean type `ty` (`factsOf`), which accept the least if
it stands for no Fren type. -/
def exprFacts (s : State) (ty : Expr) : Core.TypeFacts :=
  match coreTyOf s ty with
  | some t => factsOf s (.plain t)
  | none => .unknown

/-- The Fren name of the type whose Lean type is `t`. -/
partial def typeName (t : Expr) : TermElabM String := do
  -- A comparison or connective is a `Prop` in Lean, and a `Bool` in Fren.
  if t.isConstOf ``Bool || t.isProp then return "Bool"
  if t.isConstOf ``Int then return "Int"
  if t.isConstOf ``Nat then return "Nat"
  if t.isConstOf ``String then return "String"
  if t.isAppOfArity ``Fren.Seq 1 then return s!"Seq<{← typeName t.appArg!}>"
  if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then return s!"Rel<{← typeName e.appFn!.appArg!}, {← typeName e.appArg!}>"
    return s!"Set<{← typeName e}>"
  let s ← getState
  -- An instance of a generic type, with its arguments (`Reqs/Lang/Generics#printing`).
  if let some e := s.enumOf? t then return ((coreTyOf s t).map (·.show)).getD (Core.showPath e.path)
  if let some r := s.recordOf? t then return ((coreTyOf s t).map (·.show)).getD (Core.showPath r.path)
  let some d := t.constName? | return toString t
  if let some n := s.newtypeOfDecl? d then return Core.showPath n.path
  if let some a := s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none then
    return Core.Ty.show (.abstract a.path)
  return toString d

/-- The Lean type `t` as the Fren type it stands for, as the `fren` command
has it (`Core.Ty`), if it is one: a condition's `Prop` is a `Bool`, and
`.bvar k`, within the declaration of a generic type, its type parameter
`params[k]`. -/
def coreTy? (t : Expr) (params : Array Name := #[]) : TermElabM (Option Core.Ty) := do
  return coreTyOf (← getState) (← instantiateMVars t) params

/-- The operator `op`, prefix if `pre`, at the current syntax, of operands
of the Fren types `tx?` and `ty?`, if they have them: if one is a newtype,
it must have `op`, and both must be of it, as the `fren` command checks
(`Core.checkNewtypeOperator`). -/
def checkNewtypeOp (op : String) (tx? ty? : Option Core.Ty) (pre := false) : TermElabM Unit := do
  let (some tx, some ty) := (tx?, ty?) | return
  liftMsg (← getRef) (Core.checkNewtypeOperator op pre tx ty (← getState).orderedDecl)

/-- The newtypes that a value of the newtype `n` is, from the outermost
in: `n`, then its underlying type, if that is a newtype, and so on. -/
partial def newtypeChain (st : State) (n : NewtypeInfo) : Array NewtypeInfo :=
  #[n] ++ ((st.newtypeOf? n.under).map (newtypeChain st)).getD #[]

/-- `x`, a value of the newtypes `chain`, from the outermost in, read
through each of their fields: the value that the solver sees. -/
def unwrapTerm (chain : Array NewtypeInfo) (x : Term) : TermElabM Term :=
  chain.foldlM (fun t n => `($(mkCIdent n.field) $t)) x

/-- The Lean type of the Fren expression `t`, elaborated with the procedure's
variables in scope. -/
def typeOf (t : Term) : TermElabM Expr := do
  let e ← withoutErrToSorry <| Term.withSynthesize <| elabTerm (← `(open Classical in $t)) none
  whnfR (← instantiateMVars (← inferType e))

/-- The Fren type of the term `t` (`coreTy?`), if it has one. A term whose
type cannot be found alone, as `{}`'s, has none: its error, if any, is
left to Lean's elaboration of the whole. -/
def frenTypeOf? (t : Term) : TermElabM (Option Core.Ty) := do
  let s ← saveState
  try coreTy? (← typeOf t) catch _ => s.restore; pure none

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

/-- Reports `ref`, translated to `t` and written where its type is declared
to be `expected`, unless it may stand there (`lang::widening`), with the
`fren` command's message and the note `why` gives from the type's name.
A Lean type that is not a Fren type is left to Lean. -/
def checkDeclared (ref : Syntax) (t : Term) (expected : Expr) (why : String → String) : TermElabM Unit := do
  if let some et ← coreTy? expected then checkTermType ref t et (some (why et.show))

/-- `ts`, each widened to an `Int` if one is an `Int` and another a `Nat`:
the branches of a conditional or the bodies of a `match`'s arms
(`lang::operator_type`). -/
def widenMixed (ts : Array Term) : TermElabM (Array Term) := do
  let tys ← ts.mapM typeOf
  if tys.any (·.isConstOf ``Int) && tys.any (·.isConstOf ``Nat) then ts.mapM widenTerm else pure ts

/-- The types of the parameters of a function of type `type`, which none
depends on. -/
def paramTypes : Expr → Array Expr
  | .forallE _ d b _ => #[d] ++ paramTypes b
  | _ => #[]

/-- Strips parentheses from `e`. -/
partial def unparen (e : Syntax) : Syntax :=
  if e.isOfKind choiceKind && e.getArgs.any (·.isOfKind ``Lang.booleanBlockExpr) then
    unparen ((e.getArgs.find? (·.isOfKind ``Lang.booleanBlockExpr)).getD e[0])
  else if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then unparen e[1] else e

/-- The single name that the expression `a` is, without parentheses, if it
is one. -/
def soleName? (a : Syntax) : Option Name :=
  let a := unparen a
  let a := if a.getNumArgs == 1 then a[0] else a
  if a.isOfKind ``Lang.fren_path && (pathSegs a).size == 1 then some (pathSegs a)[0]!.getId else none

/-- In a defined function's body that may recurse, where the expression `a`
comes from (`lang::structural_recursion`): the position of the parameter
that it is, or that it is bound from a payload of, with whether it is a
payload. -/
def ExprCtx.recOrigin? (cx : ExprCtx) (a : Syntax) : Option (Nat × Bool) := do
  let (ps, _, _) ← cx.selfRec?
  let n ← soleName? a
  match cx.binder? n with
  | some b => return (← b.payloadOf?, true)
  | none =>
    guard (cx.vars.any (·.name == n))
    return (← ps.idxOf? n, false)

/-- Where the argument `a` at position `i` of a recursive application comes
from, relative to the parameter there (`lang::structural_recursion`). -/
def ExprCtx.recArg (cx : ExprCtx) (a : Syntax) (i : Nat) : Core.RecArg :=
  match cx.recOrigin? a with
  | some (j, true) => if j == i then .payload else .name
  | some (j, false) => if j == i then .itself else .name
  | none => if (soleName? a).isSome then .name else .expr

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

/-- Of `when c, d`, `c and d` and `if c then d else f`: `c`, whose pattern
tests' names `d` sees, `d`, and the other parts (`lang::test_scope`). -/
def testScoped? (e : Syntax) : Option (Syntax × Syntax × Array Syntax) :=
  if e.getNumArgs == 4 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "when" then some (e[1], e[3], #[])
  else if isBinOp e "and" then some (e[0], e[2], #[])
  else if isIte e then some (e[1], e[3], #[e[5]])
  else none

/-- The pattern tests of the chain of `and` `c`, each with its scrutinee and
its pattern. -/
def chainTests (c : Syntax) : Array (Syntax × Syntax) :=
  (chainOperands "and" c).filterMap fun o => if o.isOfKind ``Lang.isExpr then some (o[0], o[2]) else none

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

/-- The constructor `c` of an enumeration or record, applied to the type
arguments `targs`, explicitly if there are any, and to `args`: so that Lean
infers no argument that Fren does not (`Reqs/Generated#generic-types`). -/
def ctorApp (c : Name) (targs : Array Expr) (args : Array Term) (ref : Syntax := .missing) : TermElabM Term := do
  let f := if ref.isMissing then mkCIdent c else mkCIdentFrom ref c
  if targs.isEmpty then return ← `($f $args*)
  `(@$f $(targs.map typeSyntax)* $args*)

/-- Every value of a finite type, as terms, if there are at most `cap` of
them: a relation's `domain` and `range` are its image under them, which
the solver decides without a projection (`Reqs/Cli`). -/
partial def valuesOf? (ty : Expr) (cap : Nat := 64) : TermElabM (Option (Array Term)) := do
  if ty.isConstOf ``Bool then return some #[← `(true), ← `(false)]
  let s ← getState
  -- An instance's, with its arguments for the type parameters
  -- (`lang::instantiation`), given to each constructor explicitly.
  let targs := ty.getAppArgs
  let ctors : Array (Name × Array Expr) ←
    if let some e := s.enumOf? ty then
      if (exprFacts s ty).unbounded then return none
      let ps := e.payloadsAt targs
      pure (e.variants.mapIdx fun i _ => (e.ctor i, ps[i]?.getD #[]))
    else if let some r := s.recordOf? ty then
      if (exprFacts s ty).unbounded then return none
      pure #[(r.ctor, (r.fieldsAt targs).map (·.2))]
    -- A newtype's values are its underlying type's, as the `fren` command
    -- has them.
    else if let some n := ty.constName?.bind s.newtypeOfDecl? then
      pure #[(n.ctor, #[n.under])]
    else return none
  let mut out := #[]
  for (c, ts) in ctors do
    let mut combos : Array (Array Term) := #[#[]]
    for t in ts do
      let some vs ← valuesOf? t cap | return none
      combos := combos.flatMap fun pre => vs.map pre.push
      if combos.size > cap then return none
    for args in combos do out := out.push (← ctorApp c targs args)
    if out.size > cap then return none
  return some out

/-- The position of `s`'s variant among the variants of the ordered
enumeration `info`, an `Int`: its constructor's index, as a conditional on
each variant but the last, as the `fren` command writes it
(`FrenCli.DataDecl.ordinal`), so that comparing two values compares their
positions without quantifiers. -/
def ordinalTerm (info : EnumInfo) (s : Term) : TermElabM Term := do
  let last := info.variants.size - 1
  (List.range last).foldrM (init := ← `(($(Syntax.mkNumLit (toString last)) : Int))) fun k acc =>
    `(if $s = $(mkCIdent (info.ctor k)) then ($(Syntax.mkNumLit (toString k)) : Int) else $acc)

/-- `x < y`, or `x ≤ y` if not `strict`, of values compared by `o`, as a
Lean proposition, as the `fren` command's `orderSmt` writes it: a record's
lexicographically, by its fields in the order declared, and a newtype's as
its field's. -/
partial def orderTerm (o : Core.OrderPlan) (strict : Bool) (x y : Term) : TermElabM Term := do
  let st ← getState
  match o with
  | .number => if strict then `($x < $y) else `($x ≤ $y)
  | .string => if strict then `(Fren.Str.lt $x $y) else `(Fren.Str.le $x $y)
  | .enum p _ =>
    let some info := st.enums.get? p | throwError "internal error: unknown enum `{p}`"
    let (i, j) := (← ordinalTerm info x, ← ordinalTerm info y)
    if strict then `($i < $j) else `($i ≤ $j)
  | .newtype p u =>
    let some n := st.newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    orderTerm u strict (← `($(mkCIdent n.field) $x)) (← `($(mkCIdent n.field) $y))
  | .record p fs =>
    let some r := st.records.get? p | throwError "internal error: unknown record `{p}`"
    -- From the last field, compared as the whole is, back to the first,
    -- which decides unless the two are equal.
    let sel (f : Name) (v : Term) : TermElabM Term := `($(mkCIdent (r.decl ++ f)) $v)
    let some (fl, ol) := fs.getLast? | if strict then `(False) else `(True)
    let mut acc ← orderTerm ol strict (← sel fl x) (← sel fl y)
    for (f, of) in fs.dropLast.reverse do
      let (a, b) := (← sel f x, ← sel f y)
      acc ← `($(← orderTerm of true a b) ∨ ($a = $b ∧ $acc))
    return acc

/-- The ordering `op` of `x` and `y`, compared by `o`: of a newtype, its
field's; of numbers and enumerations, with `op` itself; otherwise as
`orderTerm` writes it, with `>` and `≥` as `<` and `≤` of `y` and `x`. -/
partial def orderingTerm (o : Core.OrderPlan) (op : String) (x y : Term) : TermElabM Term := do
  match o with
  | .newtype p u =>
    let some n := (← getState).newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    orderingTerm u op (← `($(mkCIdent n.field) $x)) (← `($(mkCIdent n.field) $y))
  | .number => match op with
    | "<" => `($x < $y) | "<=" => `($x ≤ $y) | ">" => `($x > $y) | _ => `($x ≥ $y)
  | .enum p _ =>
    let some info := (← getState).enums.get? p | throwError "internal error: unknown enum `{p}`"
    let (i, j) := (← ordinalTerm info x, ← ordinalTerm info y)
    match op with
    | "<" => `($i < $j) | "<=" => `($i ≤ $j) | ">" => `($i > $j) | _ => `($i ≥ $j)
  | _ => match op with
    | "<" => orderTerm o true x y
    | "<=" => orderTerm o false x y
    | ">" => orderTerm o true y x
    | _ => orderTerm o false y x

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
  -- `min` and `max` of an ordered record's, newtype's or `String`'s value,
  -- by their order, and a record's or newtype's other methods, which it has
  -- none of (`lang::method_type`, `lang::ordered_type`).
  let st ← getState
  if let some ct := (← coreTy? ty).filter (fun ct => ct matches .record .. | .newtype .. || (ct == .string && (m == "min" || m == "max"))) then
    let name := ct.show
    let ordered := ct.ordered st.orderedDecl
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (ordered := ordered))
      | throwErrorAt ref (if ordered then Core.unknownMethodMsg m name false (ordered := true)
          else if m == "min" || m == "max" then Core.unorderedMethodMsg (ct.orderedDecl?.getD .record) m name
          else Core.noMethodsMsg m name).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ← isDefEq ta ty do throwErrorAt stx s!"type mismatch: expected `{← typeName ty}`, found `{← typeName ta}`"
    let y : Term := (args.map (·.1))[0]?.getD t
    let some plan := st.orderPlan? ct | throwError "internal error: `{name}` is not ordered"
    let cmp ← orderingTerm plan (if method == .min then "<=" else ">=") t y
    return (← `(if $cmp then $t else $y), ty)
  if let some info := st.enumOf? ty then
    let name := Core.showPath info.path
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (ordered := info.ordered))
      | throwErrorAt ref (if info.ordered then Core.unknownMethodMsg m name false (ordered := true)
          else if m == "min" || m == "max" then Core.unorderedMethodMsg .enumeration m name
          else Core.noMethodsMsg m name).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ← isDefEq ta ty do throwErrorAt stx s!"type mismatch: expected `{← typeName ty}`, found `{← typeName ta}`"
    -- Conditionals on the variants' positions, as for an `Int`.
    let y : Term := (args.map (·.1))[0]?.getD t
    let (i, j) := (← ordinalTerm info t, ← ordinalTerm info y)
    let term ← if method == .min then `(if $i ≤ $j then $t else $y) else `(if $i ≥ $j then $t else $y)
    return (term, ty)
  unless ty.isConstOf ``String do throwErrorAt ref (Core.noMethodsMsg m (← typeName ty)).text
  let some method := (Core.Method.ofName? m).filter (·.accepts true false)
    | throwErrorAt ref (Core.unknownMethodMsg m "String" (ordered := true)).text
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
  -- The field `0` of a newtype (`Reqs/Lang/Expressions#newtypes`).
  if let some n := (← getState).newtypeOf? ty then
    unless f == Name.mkSimple "0" do throwErrorAt ref (Core.noFieldMsg f (Core.showPath n.path) #[Name.mkSimple "0"]).text
    return (← `($(mkCIdentFrom ref n.field) $t), n.under)
  -- A field named by digits is no method's name.
  if Core.positionalField f && ((← getState).recordOf? ty).isNone then
    throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (ty.isConstOf ``Int || ty.isConstOf ``Nat) && f == `abs then
    modifyLocal fun l => { l with absEnds := l.absEnds.push ref.getTailPos? }
  if ty.isConstOf ``String || ty.isConstOf ``Int || ty.isConstOf ``Nat || (relTypes? ty).isSome || ty.isAppOfArity ``Fren.Seq 1 then
    return ← callMethod ref t ty f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if ((← getState).enumOf? ty).isSome && (f == `min || f == `max) then
    return ← callMethod ref t ty f.toString #[]
  if ty.isAppOfArity ``Fren.FinSet 1 then
    unless f == `card do throwErrorAt ref (Core.unknownSetMethodMsg f.toString (← typeName ty)).text
    return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
  let some r := (← getState).recordOf? ty
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let some (_, ft) := (r.fieldsAt ty.getAppArgs).find? (·.1 == f)
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) (r.fields.map (·.1))).text
  return (← `($(mkCIdentFrom ref (r.decl ++ f)) $t), ft)

/-! ### Patterns (`Reqs/Lang/Patterns`) -/

/-- The alternatives of a pattern of `match` or `is`, a `fren_top_pattern`,
as written, and whether it is an or-pattern: of more than one, or with a
leading `|`. -/
def topAlts (top : Syntax) : Array Syntax × Bool :=
  let alts := top[1].getSepArgs
  (alts, alts.size > 1 || !top[0].isNone)

/-- The payload's patterns of a variant pattern, each a `fren_or_pattern`. -/
def patternArgs (p : Syntax) : Array Syntax :=
  if p.isOfKind ``Lang.variantPattern && !p[1].isNone then p[1][1].getSepArgs else #[]

mutual
/-- The alternatives of the or-patterns within the pattern `p`, in preorder
(`Core.Pat.alternatives`). -/
partial def innerAlternatives (p : Syntax) : Array Syntax :=
  (patternArgs p).flatMap fun a => orAlternatives a[0].getSepArgs (a[0].getSepArgs.size > 1)

/-- The alternatives `alts` of an or-pattern (`isOr`), each followed by
those within it, or those within its only pattern. -/
partial def orAlternatives (alts : Array Syntax) (isOr : Bool) : Array Syntax :=
  if isOr then alts.flatMap fun a => #[a] ++ innerAlternatives a else alts.flatMap innerAlternatives
end

/-- The alternatives of the or-patterns of the pattern `top` of `match` or
`is`, in preorder. -/
def topAlternatives (top : Syntax) : Array Syntax := let (alts, isOr) := topAlts top; orAlternatives alts isOr

/-- The identifiers of one segment, not applied, of the pattern `p`, in
preorder: its binders, once those that name variants, `true` and `false`
are told apart. -/
partial def patternNames (p : Syntax) : Array Syntax :=
  if p.isOfKind ``Lang.variantPattern then
    if p[1].isNone then
      match pathSegs p[0] with
      | #[x] => #[x]
      | _ => #[]
    else (patternArgs p).flatMap fun a => a[0].getSepArgs.flatMap patternNames
  else #[]

/-- The identifiers of one segment, not applied, of the pattern `top` of
`match` or `is`. -/
def topNames (top : Syntax) : Array Syntax := (topAlts top).1.flatMap patternNames

/-- The names that the quantifier `e` binds, without the `!` of shadowing. -/
def quantNames (e : Syntax) : Array Name :=
  e[1].getArgs.flatMap fun b => b[1].getArgs.map fun x => (declaredIdent x).1.getId

/-- The names of the parameters of the closure `e`, without the `!` of
shadowing. -/
def closureNames (e : Syntax) : Array Name :=
  e[1].getSepArgs.map fun p => (declaredIdent p[0]).1.getId

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def pathMentions (e : Syntax) (all : Bool := true) : Array Name :=
  let pathMentions (e : Syntax) := pathMentions e all
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
  else if isMatchLike e || e.isOfKind ``Lang.lambdaMatchExpr then
    (matchSourceArms e).foldl (init := (matchScrutinees e).flatMap pathMentions) fun acc arm =>
      -- In its arm, a binder's name means the binder, not what it shadows.
      let bound := ((matchPatterns e arm).flatMap topNames).map fun b => (declaredIdent b).1.getId
      let guard := if arm[1].isNone then #[] else pathMentions arm[1][1]
      acc ++ (guard ++ pathMentions arm[3]).filter (!bound.contains ·.getRoot)
  -- A pattern's paths name variants.
  else if e.isOfKind ``Lang.isExpr then pathMentions e[0]
  else if e.isOfKind ``Lang.letExpr then
    let defs := e[1].getSepArgs
    (Core.clauseMentions (defs.map fun d => (declaredIdent d[0]).1.getId) (defs.map fun d => pathMentions d[3]) (pathMentions e[3]) all).1
  -- In its body, a bound name means the bound name, not what it shadows,
  -- and its binders' types are not variables.
  else if e.isOfKind ``Lang.quantExpr then
    let bound := quantNames e
    (pathMentions e[3]).filter (!bound.contains ·.getRoot)
  else if e.isOfKind ``Lang.closureExpr then
    let bound := closureNames e
    (pathMentions e[3]).filter (!bound.contains ·.getRoot)
  -- In what sees them, the names that the pattern tests of a condition, or
  -- of the left operand of `and`, bind mean them (`lang::test_scope`).
  else if let some (c, d, others) := testScoped? e then
    let bound := (chainTests c).flatMap fun (_, p) => (topNames p).map fun b => (declaredIdent b).1.getId
    pathMentions c ++ (pathMentions d).filter (!bound.contains ·.getRoot) ++ others.foldl (· ++ pathMentions ·) #[]
  else e.getArgs.foldl (· ++ pathMentions ·) #[]

/-- Which of the definitions `defs` of a `let` or `where` clause its body
`body` mentions, directly or through the later ones that it mentions: the
others count for nothing (`Reqs/Lang/Let#meaning`). -/
def usedDefinitions (defs : Array Syntax) (body : Syntax) : Array Bool :=
  (Core.clauseMentions (defs.map fun d => (declaredIdent d[0]).1.getId) (defs.map fun d => pathMentions d[3] false)
    (pathMentions body false) false).2

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

/-- A reference to procedure variable `n`, if it is one, checking that it may be
mentioned here (`inst::mention`). -/
def varRef? (cx : ExprCtx) (id : Syntax) (n : Name) : TermElabM (Option Term) := do
  let some v := cx.vars.find? (·.name == n) | return none
  -- A defined output mentions what its definition does.
  for u in if cx.unmentioned then #[] else defDeps cx.vars v do
    let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
    let ok := Core.checkMention cx.place u.role earlier u.name
    match ok with
    | .ok () => pure ()
    | .error msg => throwErrorAt id (if u.name == n then msg else Core.throughDefinition n msg).text
  return some (mkIdentFrom id n)

open Lang in
/-- The expression that is the name `n`, a path of one segment. -/
def pathExpr (ref : Syntax) (n : Name) : TermElabM Syntax := do
  let tmpl ← `(fren_expr| x)
  return tmpl.raw.setArg 0 (mkNode ``Lang.fren_path #[mkNullNode #[mkIdentFrom ref n]])

/-- Give an implicit match its fresh, unspellable argument references. -/
def explicitLambdaMatch (e : Syntax) (names : Array Syntax) : TermElabM Syntax := do
  let values ← names.mapM fun n => pathExpr n n.getId
  let arms := e[2].getSepArgs
  for arm in arms do
    unless arm[0].getSepArgs.size == names.size do
      throwErrorAt arm (Core.arityMsg `match names.size arm[0].getSepArgs.size "pattern").text
  if names.size == 1 then
    return mkNode ``Lang.matchExpr #[e[0], values[0]!, mkAtom "{",
      Syntax.mkSep (arms.map fun a => (mkNode ``Lang.fren_arm ((a.setArg 0 a[0].getSepArgs[0]!).getArgs)).raw) (mkAtom ","), mkAtom "}"]
  return mkNode ``Lang.matchManyExpr #[e[0], values[0]!, mkAtom ",",
    Syntax.mkSep (values.extract 1 values.size) (mkAtom ","), mkAtom "{", e[2], mkAtom "}"]

open Lang in
/-- Expand unnamed function parameters before normal function elaboration. -/
def anonymousMatchFunction (stx : Syntax) : TermElabM Syntax := do
  if !stx[8].isNone && (unparen stx[8][1]).isOfKind ``Lang.lambdaMatchExpr &&
      stx[5].getSepArgs.all (fun p => p[1].isNone && !(typePath? p[0]).any (fun q => (pathSegs q).size == 1 && (pathSegs q)[0]!.getId.toString.endsWith "?")) then do
    let ps := stx[5].getSepArgs
    let names := ps.mapIdx fun j p => mkIdentFrom p (Name.mkSimple s!"#match{j}")
    let fnTemplate ← `(command| fn placeholder(x: Int): Int := 0)
    let template := fnTemplate.raw[5].getSepArgs[0]!
    let params := ps.zip names |>.map fun (p, n) =>
      let path := mkNode ``Lang.fren_path #[mkNullNode #[n]]
      let named := template.setArg 0 ((template[0]).setArg 0 path)
      named.setArg 1 (mkNullNode #[mkAtom ":", p[0]])
    let body ← explicitLambdaMatch (unparen stx[8][1]) names
    pure ((stx.setArg 5 (Syntax.mkSep params (mkAtom ","))).setArg 8 (stx[8].setArg 1 body))
  else pure stx

/-- For `x.m(a)`, an application of a dotted name, the receiver `x` and the
method `m`. Paths are written with `::`, so an applied dotted name is a
method call, as the `fren` command parses it: of a value, or of a variable
read from a call, as in `w.x.len()`. The only root that is not a
receiver is a call without variables (unless a binder shadows it).

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

/-- For `c(a, b)`, an application of a cardinality operator
(`Reqs/Lang/Expressions#cardinality`), the operator. A variable named like
it shadows it, which applying the variable reports. -/
def cardinalityApp? (e : Syntax) : Option Core.Cardinality := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  Core.builtinFunction? segs[0]!.getId

/-- What the identifier `x` of one segment, not applied, is in a pattern
(`lang::pattern_name`). -/
def patternName (cx : ExprCtx) (x : Syntax) : TermElabM Core.PatternName := do
  let (n, bang) := Core.declaredName x.getId
  return Core.patternName (n == `true || n == `false) bang ((← getState).table.namesVariant? cx.modName n)

/-- The binders of the pattern `top` of `match` or `is`, in preorder. -/
def topBinders (cx : ExprCtx) (top : Syntax) : TermElabM (Array Syntax) :=
  (topNames top).filterM fun x => return (← patternName cx x) == .binder

/-- Whether a pattern test of the chain of `and` `c` binds names. -/
def chainBinds (cx : ExprCtx) (c : Syntax) : TermElabM Bool :=
  (chainTests c).anyM fun (_, p) => return !(← topBinders cx p).isEmpty

/-- The names that the pattern tests of the chain of `and` `c` bind, which
what follows the chain sees (`lang::test_scope`). -/
def chainBinders (cx : ExprCtx) (c : Syntax) : TermElabM (List String) := do
  let bs ← (chainTests c).mapM fun (_, p) => topBinders cx p
  return bs.toList.flatMap fun xs => xs.toList.map fun x => (Core.declaredName x.getId).1.toString

/-- The shape of `e`, for what it mentions (`lang::mentions`), where `bs`
are the binders of `e` around the subexpression, each with the shape of its
scrutinee. -/
partial def shapeOf (cx : ExprCtx) (e : Syntax) (bs : Array (Name × Core.MentionShape) := #[]) : TermElabM Core.MentionShape := do
  let parts (k : Core.MentionKind) (es : Array Syntax) : TermElabM Core.MentionShape :=
    return .node k (← es.toList.mapM (shapeOf cx · bs))
  if let some (recv, _) := methodApp? cx e then
    return ← parts .method (#[(← pathExpr e recv)[0]] ++ e[2].getSepArgs)
  -- A cardinality operator has a fixed meaning, as an operator does.
  if (cardinalityApp? e).isSome then return ← parts .compound e[2].getSepArgs
  if e.isOfKind ``Lang.appExpr then
    let k : Core.MentionKind ← if ← isConstruction cx e[0] then pure .construction
      else if (← definedFn? cx e[0]).isSome then pure .defined
      else pure (.uninterpreted ("::".intercalate ((pathSegs e[0]).toList.map (·.getId.toString (escape := false)))))
    parts k e[2].getSepArgs
  else if e.isOfKind ``Lang.recordExpr then
    -- A field without `:= e` is `x := x`.
    parts .construction (← e[2].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1])
  else if e.isOfKind ``Lang.updateExpr then
    -- The updated value, and the new values.
    parts .compound (#[e[1]] ++ (← e[3].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1]))
  else if isMatchLike e || e.isOfKind ``Lang.lambdaMatchExpr then
    let shapes ← (matchScrutinees e).mapM (shapeOf cx · bs)
    let arms ← (matchSourceArms e).toList.flatMapM fun arm => do
      let mut new := #[]
      for p in matchPatterns e arm, j in [0:(matchPatterns e arm).size] do
        new := new ++ (← topBinders cx p).map fun b => ((declaredIdent b).1.getId,
          Core.MentionShape.node .binder (shapes[j]?.toList))
      ((if arm[1].isNone then [] else [arm[1][1]]) ++ [arm[3]]).mapM (shapeOf cx · (bs ++ new))
    return .node .compound (shapes.toList ++ arms)
  else if e.isOfKind ``Lang.isExpr then parts .compound #[e[0]]
  else if e.isOfKind ``Lang.letExpr then
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← e[1].getSepArgs.foldlM (init := bs) fun bs d => do
      return bs.push ((declaredIdent d[0]).1.getId, .node .definition [← shapeOf cx d[3] bs])
    return .node .compound [← shapeOf cx e[3] bs]
  else if e.isOfKind ``Lang.quantExpr then
    let new := quantNames e |>.map fun n => (n, Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOf cx e[3] (bs ++ new)]
  -- A closure's parameter varies, as a variable does
  -- (`Reqs/Lang/HigherOrder#arguments`).
  else if e.isOfKind ``Lang.closureExpr then
    let new := closureNames e |>.map fun n => (n, Core.MentionShape.leaf (.variable (n.toString (escape := false))))
    return .node .compound [← shapeOf cx e[3] (bs ++ new)]
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size != 1 then return .leaf .constant
    let n := segs[0]!.getId
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf (if b.unbounded then .variable (n.toString (escape := false)) else .bound)
      return .node .binder [← shapeOf (cx.at b) sc]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return .node .definition [← shapeOf { cx with binders := #[] } d]
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable (n.toString (escape := false)) else .constant)
  else if e.isAtom || e.isIdent then return .leaf .literal
  -- The names that the pattern tests of a condition, or of the left
  -- operand of `and`, bind, in what sees them (`lang::test_scope`).
  else if let some (c, d, others) := testScoped? e then
    let new ← (chainTests c).flatMapM fun (sc, p) => do
      let s ← shapeOf cx sc bs
      return (← topBinders cx p).map fun b => ((declaredIdent b).1.getId, Core.MentionShape.node .binder [s])
    return .node .compound ([← shapeOf cx c bs, ← shapeOf cx d (bs ++ new)] ++ (← others.toList.mapM (shapeOf cx · bs)))
  else parts .compound e.getArgs

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← shapeOf cx e).mentions

/-- The names of the variables and uninterpreted functions that `e`
mentions (`lang::mentions`). -/
def mentionedNames (cx : ExprCtx) (e : Syntax) : TermElabM (List Core.Mention) := return (← shapeOf cx e).mentioned

/-- The applications of uninterpreted functions in `e`. -/
partial def applications (cx : ExprCtx) (e : Syntax) : TermElabM (Array Syntax) := do
  let inner ← e.getArgs.foldlM (init := #[]) fun acc a => return acc ++ (← applications cx a)
  if e.isOfKind ``Lang.appExpr && (methodApp? cx e).isNone && (cardinalityApp? e).isNone then
    if !(← isConstruction cx e[0]) && (← definedFn? cx e[0]).isNone then return #[e] ++ inner
  return inner

/-- Whether the Lean type of a Fren type has infinitely many values
(`Reqs/Lang/Decidability#outputs`): it is not finite (`lang::type_facts`),
so an abstract type counts. -/
def infiniteType (ty : Expr) : TermElabM Bool := return !(exprFacts (← getState) ty).finite

/-- Whether `e` mentions an output of an infinite type, directly, through a
definition or through a binder. -/
partial def mentionsInfiniteOutput (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  for n in pathMentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsInfiniteOutput (cx.at b) sc then return true
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

/-- Where `e` is written, without its parentheses: how the memberships of
quantifiers over elements are found again (`ExprCtx.elemGuards`). -/
def elemKey (e : Syntax) : Option String.Pos.Raw × Option String.Pos.Raw :=
  let e := unparen e
  (e.getPos?, e.getTailPos?)

/-- Whether the names `ns`, as mentioned, are an output that is not
defined, or mention one, through a definition or through a binder: one
that the realizability check quantifies over, as the `fren` command's
`mentionsOutput`. -/
partial def mentionsOutputOf (cx : ExprCtx) (ns : Array Name) : TermElabM Bool := do
  for n in ns do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsOutputOf (cx.at b) (pathMentions sc) then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && u.defn?.isNone then return true
  return false

/-- `mentionsOutputOf` of the names that `e` mentions. -/
def mentionsOutput (cx : ExprCtx) (e : Syntax) : TermElabM Bool := mentionsOutputOf cx (pathMentions e)

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (ref : Syntax) (c : Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Syntax) (ground : Bool := false) (finiteRange : Bool := true) (literalOperand : Bool := false) :
    TermElabM Unit := do
  if cx.unmentioned then return
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
  if cx.unmentioned then return
  let some (a, b) := relTypes? ty | return
  let tys ← match Core.Method.ofName? m with
    | some .inverse => pure #[a, b]
    | some .closure | some .image | some .range => pure #[a]
    | some .domain => pure #[b]
    | _ => return
  let finite ← tys.allM fun t => return !(← infiniteType t)
  modifyLocal fun l => { l with relationalUsed := true }
  checkCore cx ref .relational true true operands (← operands.allM (isConstant cx ·)) finite

/-- Records a `card`, of the receiver `recv` of Lean type `ty`: in a procedure
that applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (recv : Syntax) : TermElabM Unit := do
  if cx.unmentioned then return
  if m == "card" && ty.isAppOfArity ``Fren.FinSet 1 && !(← isConstant cx recv) then
    modifyLocal fun l => { l with countRefs := l.countRefs.push ref }

/-- Reports `undecidable` at each count of the current procedure, if it also
applies a relational operator; gives whether it does and whether it counts. -/
def checkCounts [Monad m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m] : m (Bool × Bool) := do
  let l ← getLocal
  if l.relationalUsed then
    for r in l.countRefs do
      modifyLocal fun l => { l with outsideCore := true }
      recordLint .undecidable r (Core.undecidableMsg .relationalCard false)
  return (l.relationalUsed, !l.countRefs.isEmpty)

/-- Records what a call of `c`, written at `ref`, brings to the current
procedure's mix of relational operators and counting. -/
def noteCounts [Monad m] [MonadEnv m] (c : CompInfo) (ref : Syntax) : m Unit :=
  modifyLocal fun l => { l with relationalUsed := l.relationalUsed || c.relational, guardedUsed := l.guardedUsed || c.guarded
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
  let f := fieldName e[2]
  -- For `redundant_newtype_roundtrip`.
  if let (some n, true) := ((← getState).newtypeOf? ty, cx.noteIndexes && f == Name.mkSimple "0") then
    modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .unwraps n.path.toString) }
  let r ← readField e[2] t ty f
  if let (true, some m) := (ty.isAppOfArity ``Fren.Seq 1, Core.Method.ofName? f.toString) then
    checkCore cx e m.seqConstruct true true #[e[0]] (← isConstant cx e[0])
  checkRelational cx e ty f.toString #[e[0]]
  checkRelationalCard cx e ty f.toString e[0]
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

/-- Whether the row `r` of a table is `_`, which is a token node. -/
def isWildRow (r : Syntax) : Bool := r[1].getNumArgs == 1 && r[1][0].isAtom && r[1][0].getAtomVal == "_"

/-- The nodes in `e`'s arguments, through lists such as a call's arguments. -/
partial def subNodes (e : Syntax) : Array Syntax :=
  e.getArgs.flatMap fun a =>
    if a.isAtom || a.isIdent || a.isMissing then #[] else if a.isOfKind nullKind then subNodes a else #[a]

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
  if let some (xs, ops) := chainOf? e then .mk (.chain (ops.map (·.getAtomVal.trimAscii.toString))) range e (xs.map go) else
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
  -- An application's operands are its arguments, and a field read's its
  -- receiver, as the `fren` command sees them.
  else if e.isOfKind ``Lang.appExpr then .mk .atom range e (e[2].getSepArgs.map go)
  else if e.isOfKind ``Lang.fieldExpr then .mk .atom range e #[go e[0]]
  else if e.isOfKind ``Lang.quantExpr || e.isOfKind ``Lang.closureExpr then .mk .quant range e #[go e[3]]
  -- A table, with its rows' conditions and values, as the `fren` command
  -- sees it.
  else if e.isOfKind ``Lang.tableExpr then
    .mk .atom range e (e[2].getSepArgs.flatMap fun r => (if isWildRow r then #[] else #[go r[1]]).push (go r[3]))
  else
  match e.getNumArgs, atom 0, atom 1 with
  | 3, "(", _ => go e[1]
  | 4, "when", _ => .mk (.when false) range e #[go e[1], go e[3]]
  | 4, "unless", _ => .mk (.when true) range e #[go e[1], go e[3]]
  | 4, "let", _ => .mk .«let» range e #[go e[3]]
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
`ensure` or `expect` as `kind` says (`lint::assertions_on_constants`). -/
def lintConstant (cx : ExprCtx) (kind : String) (e : Syntax) : TermElabM Unit := do
  if Core.assertionOnConstant (← mentionedNames cx e) then
    let literal? := match boolNode "" 0 (unparen e) with | .mk (.lit b) .. => some b | _ => none
    recordLint .assertionsOnConstants e (Core.assertionOnConstantMsg kind literal?)

/-- The integer literals in `e`, its patterns' among them. -/
partial def numLits (e : Syntax) : Array Syntax :=
  if e.isOfKind numLitKind then #[e] else e.getArgs.flatMap numLits

/-- The end of the last token in `e`, wherever it is among its parts. -/
partial def lastTailPos (e : Syntax) : String.Pos.Raw :=
  e.getArgs.foldl (fun acc a => max acc (lastTailPos a)) (e.getTailPos?.getD 0)

/-- Whether a name declared in `cx`, or among `extra`, would hide
something in scope (`lang::shadowing`). -/
def hidesIn (cx : ExprCtx) (extra : Core.Locals := #[]) : TermElabM (String → Bool) := do
  let table := (← getState).table
  let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome ++ extra
  return fun n => (table.hidden? cx.modName locals (Name.mkSimple n)).isSome

/-- The names that `e` declares, without their `!`: those of its `let`s and
`where` clauses, its bound names and its patterns' binders
(`Core.ForallCx`). -/
partial def declaredNames (e : Syntax) : Array String :=
  let own :=
    if e.isOfKind ``Lang.letExpr then e[1].getSepArgs.map fun d => Core.nameText (declaredIdent d[0]).1.getId
    else if e.isOfKind ``Lang.quantExpr then (quantNames e).map Core.nameText
    else if e.isOfKind ``Lang.closureExpr then (closureNames e).map Core.nameText
    else if isMatchLike e || e.isOfKind ``Lang.lambdaMatchExpr then
      (matchSourceArms e).flatMap fun arm => ((matchPatterns e arm).flatMap topNames).map fun b => Core.nameText (declaredIdent b).1.getId
    else if e.isOfKind ``Lang.isExpr then (topNames e[2]).map fun b => Core.nameText (declaredIdent b).1.getId
    else #[]
  own ++ e.getArgs.flatMap declaredNames

/-- Records the expressions in `e` that the lints that rewrite them
(`Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated, where `hides` says
whether a name declared there would hide something in scope. -/
def lintBools (e : Syntax) (hides : String → Bool) : TermElabM Unit := do
  let some sub := e.getSubstring? false false | return
  -- To the end of everything in `e`: the `let` that a `where` clause
  -- becomes ends where its expression does, before its definitions
  -- (`withWhere`).
  let stop := max sub.stopPos (lastTailPos e)
  let src := (String.Pos.Raw.extract sub.str sub.startPos stop).toList.toArray
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let node := boolNode sub.str sub.startPos e
  -- Not a rewrite of an expression with a pattern test that binds names,
  -- which could move what mentions them out of their scope
  -- (`lang::test_scope`).
  let tests := (← getLocal).bindingTests
  modifyLocal fun l => { l with bindingTests := #[] }
  let pos (p : Option String.Pos.Raw) : Nat := (p.map (·.byteIdx)).getD 0
  let keeps (first last : Syntax) := !tests.any fun (a, b) =>
    pos first.getPos? ≤ pos a && pos b ≤ pos last.getTailPos?
  for (l, ref, msg) in Core.rewriteReports src node fixable do
    if keeps ref ref then recordLint l ref msg
  let (boolEqs, ordereds, variants, absEnds, mentioning, facts) :=
    ((← getLocal).boolEqs, (← getLocal).ordereds, (← getLocal).variants, (← getLocal).absEnds, (← getLocal).mentioning,
      (← getLocal).facts)
  modifyLocal fun l => { l with boolEqs := #[], ordereds := #[], variants := #[], absEnds := #[], mentioning := #[], facts := #[] }
  -- Looked up by where they are, in maps, rather than by reading the
  -- arrays, which would take time quadratic in the expression's size: the
  -- first entry for each, as `find?` gives it, and whether one is there,
  -- as `contains` says. A position is its byte offset.
  let key (p : Option String.Pos.Raw × Option String.Pos.Raw) := (p.1.map (·.byteIdx), p.2.map (·.byteIdx))
  let firstAt {α : Type} (xs : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × α)) :
      Std.HashMap (Option Nat × Option Nat) α :=
    xs.foldl (init := {}) fun m (p, a) => if m.contains (key p) then m else m.insert (key p) a
  let (variants, facts, ordereds, mentioning) := (firstAt variants, firstAt facts, firstAt ordereds, firstAt mentioning)
  let boolEqs := Std.HashSet.ofArray (boolEqs.map key)
  let absEnds := Std.HashSet.ofArray (absEnds.map (·.map (·.byteIdx)))
  let spanOf (s : Syntax) := key (s.getPos?, s.getTailPos?)
  let variant? (s : Syntax) := variants[spanOf s]?
  let fact? (s : Syntax) := facts[spanOf s]?
  let ordered? (s : Syntax) := ordereds[spanOf s]?
  let mentioned (s : Syntax) := mentioning[spanOf s]?.getD []
  let help (msg : Core.Msg) := if fixable && !msg.fixes.isEmpty then #[Core.fixHelp] else #[]
  let st ← getState
  let fcx : Core.ForallCx :=
    { variants? := fun p => (st.enums.get? p.toName).bind fun info =>
        if (List.range info.variants.size).all (info.payloads[·]?.all (·.isEmpty)) then some info.variants.size else none
      declared := declaredNames e, hides, unguarded := !Core.hasGuarded (e.reprint.getD "") }
  for r in Core.opReports src (boolEqs.contains <| spanOf ·) ordered? variant? (absEnds.contains <| ·.getTailPos?.map (·.byteIdx))
      mentioned fact? fcx node do
    -- A node's position is its first token's, and its tail its last's.
    let ref := match r.last? with | some l => mkNullNode #[r.ref, l] | none => r.ref
    if keeps r.ref (r.last?.getD r.ref) then recordLint r.lint ref { r.msg with notes := r.msg.notes ++ help r.msg }
  for r in Core.arithReports src node do
    if keeps r.ref r.ref then recordLint r.lint r.ref { r.msg with notes := r.msg.notes ++ help r.msg }
  -- `zero_prefixed_literal`, in expressions and patterns alike.
  let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos (p.getD sub.startPos)).length
  for n in numLits e do
    let r : Core.Range := { start := off n.getPos?, stop := off n.getTailPos? }
    unless r.stop ≤ src.size do throwErrorAt n "internal error: a literal outside the text of its expression"
    if let some (_, msg) := Core.zeroPrefixedReport? src r then
      recordLint .zeroPrefixedLiteral n (if fixable then msg.note Core.fixHelp else msg)
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

/-- `inconsistent_struct_constructor` on the literal `e` of the record
`path`, which declares `declared`, whose fields are `given`
(`lint::inconsistent_struct_constructor`). -/
def lintFieldOrder (e : Syntax) (path : Name) (declared : Array Name) (given : Array Syntax) : TermElabM Unit := do
  let some sub := e.getSubstring? false false | return
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  let off (p : String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos p).length
  let range (s : Syntax) : Core.Range :=
    { start := off (s.getPos?.getD sub.startPos), stop := off (s.getTailPos?.getD sub.startPos) }
  let some fixed? := Core.reorderedFields? src ⟨0, src.size⟩ (given.map range) (given.map (·[0].getId)) declared | return
  let msg := Core.inconsistentStructConstructorMsg (Name.mkSimple path.getString!) declared fixed?
  recordLint .inconsistentStructConstructor e (if (← getLocal).inMarkdown && fixed?.isSome then msg.note Core.fixHelp else msg)

/-- The Lean type of the Fren type `t`, the inverse of `coreTy?`, for the
type arguments of a construction. -/
partial def leanTypeOf (t : Core.Ty) : TermElabM Expr := do
  let s ← getState
  let set (e : Expr) := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) e
  match t with
  | .bool => return Lean.mkConst ``Bool
  | .int => return Lean.mkConst ``Int
  | .nat => return Lean.mkConst ``Nat
  | .string => return Lean.mkConst ``String
  | .set e => return set (← leanTypeOf e)
  | .rel a b => return set (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← leanTypeOf a) (← leanTypeOf b))
  | .seq e => return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← leanTypeOf e)
  | .enum p as =>
    let some e := s.enums.get? p | throwError "internal error: unknown enum `{p}`"
    return mkAppN e.const (e.leanArgs (← as.toArray.mapM leanTypeOf))
  | .record p as =>
    let some r := s.records.get? p | throwError "internal error: unknown record `{p}`"
    return mkAppN (Lean.mkConst r.decl) (← as.toArray.mapM leanTypeOf)
  | .abstract p => return Lean.mkConst (placeholderName p)
  | .newtype p _ =>
    let some n := s.newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    return Lean.mkConst n.decl
  | .param _ n => throwError "internal error: the type parameter `{n}` outside its declaration"

/-- A construction of a generic type (`Reqs/Lang/Generics#type-arguments`).
-/
structure Construction where
  /-- The generic type's path. -/
  path : Name
  params : Array Name
  /-- Its values' declared types, which mention the type parameters. -/
  declared : Array Core.Ty
  /-- Its values in their order: a record's fields in the order of its
  declaration, `none` for one that is not given. -/
  values : Array (Option Syntax)

open Lang in
/-- The construction of a generic enumeration or record that `e` is, if it
is one, as the `fren` command's `construction?` finds it. -/
def construction? (cx : ExprCtx) (e : Syntax) : TermElabM (Option Construction) := do
  let st ← getState
  let tys (params : Array Name) (ts : Array Expr) := ts.map fun t => (coreTyOf st t params).getD (.abstract .anonymous)
  let variant (p : Syntax) (vals : Array Syntax) : Option Construction := do
    let .ok (.variant en idx) := st.table.resolvePath cx.modName ((pathSegs p).map (·.getId)) cx.shadowing | none
    let info ← st.enums.get? en.path
    guard !info.params.isEmpty
    let ts ← info.payloads[idx]?
    return { path := en.path, params := info.params, declared := tys info.params ts, values := vals.map some }
  if e.isOfKind ``Lang.appExpr then return variant e[0] e[2].getSepArgs
  if e.getNumArgs == 1 && e[0].isOfKind ``Lang.fren_path then return variant e[0] #[]
  if e.isOfKind ``Lang.recordExpr then
    let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath cx.modName ((pathSegs e[0]).map (·.getId)) cx.shadowing
      | return none
    let some info := st.records.get? path | return none
    if info.params.isEmpty then return none
    let given := e[2].getSepArgs
    let vals ← info.fields.mapM fun (f, _) => do
      let some b := given.find? (·[0].getId == f) | return none
      if b[1].isNone then return some (← pathExpr b[0] b[0].getId) else return some b[1][1]
    return some { path, params := info.params, declared := tys info.params (info.fields.map (·.2)), values := vals }
  return none

open Lang in
/-- `e`'s shape, for whether it synthesizes a type (`Core.TypeShape`). -/
partial def typeShape (cx : ExprCtx) (e : Syntax) : TermElabM Core.TypeShape := do
  let go := typeShape cx
  if let some c ← construction? cx e then
    let shapes ← c.values.mapM fun v? => match v? with
      | some v => go v
      | none => pure .other
    return Core.constructionShape c.params c.declared shapes
  -- An application of a generic function (`Reqs/Lang/GenericFunctions#applications`).
  if e.isOfKind ``Lang.appExpr then
    let st ← getState
    if let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath cx.modName ((pathSegs e[0]).map (·.getId)) cx.shadowing then
      if let some d := (st.defined.get? path).filter (!·.typeParams.isEmpty) then
        return Core.callShape d.typeParams.size d.declared d.result (← e[2].getSepArgs.mapM go)
      -- One without a body, as the `fren` command has it.
      if let some a := (st.abstracts.get? path).filter (!·.typeParams.isEmpty) then
        return Core.callShape a.typeParams.size a.declared a.result (← e[2].getSepArgs.mapM go)
  if e.isOfKind ``Lang.setExpr || e.isOfKind ``Lang.seqExpr then
    let elems := e[1].getSepArgs
    if elems.isEmpty then return .emptyLiteral else return .anyPart (← elems.toList.mapM go)
  else if e.isOfKind ``Lang.pairExpr then return .pair (← go e[1]) (← go e[3])
  else if e.isOfKind ``Lang.unionExpr || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr then
    return .anyPart [← go e[0], ← go e[2]]
  else if isMatchLike e then return .anyPart (← (matchSourceArms e).toList.mapM (go ·[3]))
  else if e.isOfKind ``Lang.letExpr then return .anyPart [← go e[3]]
  else if e.isOfKind ``Lang.tableExpr then return .anyPart (← e[2].getSepArgs.toList.mapM (go ·[3]))
  else match e with
    | `(fren_expr| $a ++ $b) => return .anyPart [← go a, ← go b]
    | `(fren_expr| ($a)) => return .anyPart [← go a]
    | `(fren_expr| if $_ then $a else $b) => return .anyPart [← go a, ← go b]
    | _ => return .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← typeShape cx e).synthesizes

/-- Whether one of `es` synthesizes a type. -/
def anySynthesizes (cx : ExprCtx) (es : Array Syntax) : TermElabM Bool := es.anyM (synthesizes cx)

/-- Translates the values `vals` of the construction `c` of a generic type,
written `what` at `ref`, with `go`, which translates a value checked against
a type, if one is given, and returns their terms and the construction's
type arguments, which are inferred (`Core.inferConstruction`), as the
`fren` command's `elabConstruction` does, in the same order. `expected?` is
the type expected of the construction, and `note k t` explains that value
`k` has the type `t`. -/
def constructionTerms (go : Option Core.Ty → Syntax → TermElabM Term) (cx : ExprCtx) (expected? : Option Core.Ty)
    (ref : Syntax) (c : Construction) (vals : Array Syntax) (what : String) (note : Nat → Core.Ty → String) :
    TermElabM (Array Term × Array Core.Ty) := do
  let exp := match expected? with
    | some (.enum p as) | some (.record p as) => if p == c.path then some as.toArray else none
    | _ => none
  let synth ← vals.mapM (synthesizes cx)
  let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
    Core.inferConstruction c.params c.declared synth exp
      (throwErrorAt ref (Core.cannotInferMsg what (Core.showPath c.path)).text : TermElabM Unit)
      (fun k x? => do
        let t ← (go x? vals[k]! : TermElabM Term)
        modify (·.set! k t)
        frenTypeOf? t)
      (fun k x f => (liftMsg vals[k]! (Core.checkType x f (some (note k x))) : TermElabM Unit))
  let (args, ts) ← run.run (vals.map fun _ => default)
  return (ts, args)

open Lang in
/-- `unnecessary_struct_initialization` on the record literal `e`, of the
type `ty`, with the fields `given`, where `go` translates expressions
(`lint::unnecessary_struct_initialization`). -/
def lintStructInit (go : Syntax → TermElabM Term) (ty : Core.Ty) (e : Syntax) (given : Array Syntax) :
    TermElabM Unit := do
  -- Each field's value as `r.f`, its own field `f` of `r`, with `r`'s text.
  let mut reads := #[]
  for b in given do
    if b[1].isNone then return
    let v := unparen b[1][1]
    let v := if v.getNumArgs == 1 then v[0] else v
    let f := b[0].getId
    if v.isOfKind ``Lang.fieldExpr && v[2].getId == f then
      reads := reads.push (v[0], srcText v[0])
    else if v.isOfKind ``Lang.fren_path && (pathSegs v).size == 1 then
      let id := (pathSegs v)[0]!
      unless !id.getId.isAtomic && id.getId.getString! == f.toString do return
      let t := srcText id
      let t := String.ofList (t.toList.take (t.length - f.toString.length - 1))
      reads := reads.push (← `(fren_expr| $(mkIdentFrom id id.getId.getPrefix):ident), t)
    else return
  let some (r, t) := reads[0]? | return
  let same := reads.all (Core.writtenSame ·.2 t)
  -- A value has a type; a call is not one.
  let saved ← saveState
  let ty? ← try some <$> typeOf (← go r) catch _ => pure none
  let core? ← ty?.bindM coreTy?
  saved.restore
  if Core.unnecessaryStructInit given.size true same ty?.isSome (core? == some ty) then
    let msg := Core.unnecessaryStructInitMsg t
    recordLint .unnecessaryStructInitialization e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)

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
  else if isMatchLike p then
    if same p[1] then some Core.receiverSlot else none
  else if p.isOfKind ``Lang.isExpr then at_ .patternTest #[0]
  else if p.isOfKind ``Lang.quantExpr then at_ .quant #[3]
  -- A chained comparison's operands, not the comparisons within it.
  else if let some (xs, ops) := chainOf? p then (xs.findIdx? same).bind ((Core.BKind.chain (ops.map (·.getAtomVal.trimAscii.toString))).slots[·]?.join)
  else match p.getNumArgs, atom 0, atom 1 with
    | 3, "(", _ => none
    | 4, "when", _ => at_ (.when false) #[1, 3]
    | 4, "unless", _ => at_ (.when true) #[1, 3]
    | 2, "not", _ => at_ .not #[1]
    | 2, "-", _ => at_ .neg #[1]
    | 3, _, op => if op.isEmpty then none else at_ (.bin op) #[0, 2]
    | _, _, _ => none

mutual
/-- The pattern `p`, resolved as `q`, as written (`Core.PatNode`). -/
partial def patNode (p : Syntax) (q : Core.Pat) : Core.PatNode Syntax :=
  match q with
  | .ctor _ qs => .mk q (exactText p) p (((patternArgs p).zip qs).map fun (a, q) => orNode a[0].getSepArgs q)
  | _ => .mk q (exactText p) p #[]

/-- The or-pattern of the alternatives `alts`, resolved as `q`, where its
alternatives are, or its only pattern. -/
partial def orNode (alts : Array Syntax) (q : Core.Pat) : Core.PatNode Syntax :=
  match q with
  | .or qs =>
    let at_ := mkNullNode #[alts[0]!, alts.back!]
    .mk q (exactText at_) at_ ((alts.zip qs).map fun (a, q) => patNode a q)
  | _ => patNode alts[0]! q
end

/-- The lints of each or-pattern within the pattern `n`, of a `match` arm
or of `is` (`Reqs/Lint/Complexity/Patterns`): `wildcard_in_or_patterns`,
`manual_range_patterns` and `unnested_or_patterns`. -/
def lintOrPatterns (n : Core.PatNode Syntax) : TermElabM Unit := do
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable then m.note Core.fixHelp else m
  for o in n.orPatterns do
    let alts := o.kids
    if Core.wildcardInOr (alts.any (·.pat matches .wild false)) then
      recordLint .wildcardInOrPatterns o.at_ (help Core.wildcardInOrMsg)
    else if let some fixed := Core.manualRangeFix? (alts.map fun a => (a.pat, a.text)) then
      recordLint .manualRangePatterns o.at_ (help (Core.manualRangeMsg fixed))
    else
      for (i, j, fixed) in Core.unnestedRuns alts do
        recordLint .unnestedOrPatterns (mkNullNode #[alts[i]!.at_, alts[j]!.at_]) (help (Core.unnestedOrMsg fixed))

/-- The name that the binder `x` declares, without its `!`. -/
def binderName (x : Syntax) : String := Core.nameText (Core.declaredName x.getId).1

/-- `collapsible_match` on the arm `i` of the `match` whose arms are `arms`
and patterns `pats` (`lint::collapsible_match`): the arm's pattern is one
variant whose payload's patterns are `_` or binders, and its body a
`match` on one of those binders. -/
def lintCollapsible (cx : ExprCtx) (arms : Array Syntax) (pats : Array Core.Pat) (i : Nat) : TermElabM Unit := do
  let arm := arms[i]!
  let (alts, isOr) := topAlts arm[0]
  let #[p] := alts | return
  if isOr || !p.isOfKind ``Lang.variantPattern || p[1].isNone then return
  let .ctor _ qs := pats[i]! | return
  let body := unparen arm[3]
  unless body.isOfKind ``Lang.matchExpr do return
  let s := unparen body[1]
  let s := if s.getNumArgs == 1 then s[0] else s
  unless s.isOfKind ``Lang.fren_path && (pathSegs s).size == 1 do return
  let x := Core.nameText (pathSegs s)[0]!.getId
  let args := (patternArgs p).map (·[0].getSepArgs)
  let binderOf : Array Syntax × Core.Pat → Option String
    | (#[b], .wild true) => some (binderName (pathSegs b[0])[0]!)
    | _ => none
  let binders := (args.zip qs).filterMap binderOf
  let some k := (args.zip qs).findIdx? (binderOf · == some x) | return
  let flat := qs.all (· matches .wild _)
  let innerArms := body[3].getSepArgs
  -- An arm with a guard may not be taken where its pattern matches.
  if (arms.any (!·[1].isNone)) || innerArms.any (!·[1].isNone) then return
  let some d := innerArms.back? | return
  let innerWildcard := match topAlts d[0] with
    | (#[w], false) => w.isOfKind ``Lang.wildPattern
    | _ => false
  -- The first later arm that matches a value of the variant: one with `_`
  -- or a binder among its alternatives, since an arm that names the variant
  -- after this one is unreachable.
  let wild? := ((List.range arms.size).filter (· > i)).find? fun j => pats[j]!.top.any (· matches .wild _)
  let sameWildcard := wild?.any fun j => pats[j]! matches .wild false &&
    Core.writtenSame (exactText arms[j]![3]) (exactText d[3])
  -- The inner `_` arm's body is taken where the outer one's is after the
  -- fix, outside the arm's pattern, so it must mention none of its binders.
  let mentioned := Core.mentionsName (exactText body[3]) x || binders.any (Core.mentionsName (exactText d[3]) ·)
  let innerBinders ← innerArms.flatMapM fun a => return (← topBinders cx a[0]).map binderName
  let clash := innerBinders.any binders.contains
  unless Core.collapsibleMatch true flat innerWildcard sameWildcard mentioned clash innerArms.size do return
  let commented := Core.hasComment (exactText arm)
  let innerTexts := innerArms.pop.map fun a => (" | ".intercalate ((topAlts a[0]).1.map exactText).toList, exactText a[3])
  let fixed := Core.collapsedArms (exactText p[0]) ((patternArgs p).map exactText) k innerTexts
  let msg := Core.collapsibleMatchMsg x (if commented then none else some fixed)
  recordLint .collapsibleMatch body (if !commented && (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Core.Pat.flat`), where no arm overlaps another without containing
it. -/
def lintMatch (cx : ExprCtx) (e : Syntax) (ty : Expr) (pats : Array Core.Pat)
    (slot : Option Core.Slot) : TermElabM Unit := do
  let arms := e[3].getSepArgs
  -- A table over a scrutinee is called a table (`Core.Msg.ofTable`).
  let tm (m : Core.Msg) : Core.Msg := if e.isOfKind ``Lang.tableMatchExpr then m.ofTable else m
  -- An arm with a guard may not be taken where its pattern matches, so
  -- the lints that move, merge or remove arms, or replace the `match`,
  -- look only at a `match` without guards, and the arms with guards name
  -- no variant for the lints of `_` (`Reqs/Lint/Pedantic/Matches#arms`).
  let guarded := arms.map (!·[1].isNone)
  let anyGuard := guarded.any id
  let mut infos : Array Core.ArmInfo := #[]
  for arm in arms, pat in pats do
    let (alts, _) := topAlts arm[0]
    let alts := if alts.size == 1 && arm[0][0].isNone && alts[0]!.isOfKind ``Lang.wildPattern then #[] else alts
    let texts := alts.map exactText
    infos := infos.push { alts := texts, binds := !(← topBinders cx arm[0]).isEmpty, noPayload := pat.noPayload
                          equatable := Core.equatable pat texts, disjoint := alts.isEmpty || Core.disjointPat pat texts
                          body := { text := exactText arm[3], prec := exprPrec arm[3] } }
  let flat := pats.all (·.flat)
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable then m.note Core.fixHelp else m
  -- `trivial_match` (`lint::trivial_match`).
  if let #[i] := infos then
    if Core.trivialMatch infos.size i.binds && !anyGuard then recordLint .trivialMatch e (tm (Core.trivialMatchMsg (i.body.inSlot slot (followedStx e))))
  -- `needless_match` (`lint::needless_match`): only a `match` whose arms
  -- are `_` and variants whose payloads' patterns are `_` or binders.
  let scr := exactText (unparen e[1])
  let enum? := (← getState).enumOf? ty
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  for arm in arms, pat in pats do
    let body := unparen arm[3]
    let (alts, isOr) := topAlts arm[0]
    match pat, enum?, alts with
    | .wild false, _, _ =>
      wildcard := true
      scrutineeBack := Core.writtenSame (exactText body) scr
    | .ctor idx qs, some info, #[alt] =>
      unless !isOr && qs.all (· matches .wild _) do givenBack := false; continue
      let bs := (patternArgs alt).map (·[0].getSepArgs[0]!)
      let binders := bs.map fun b => if b.isOfKind ``Lang.wildPattern then "_" else (pathSegs b[0])[0]!.getId.toString
      -- The arm's binders shadow items in its body.
      let shadowing := cx.shadowing ++ (binders.filter (· != "_")).map Name.mkSimple
      let (p, args) := if body.isOfKind ``Lang.appExpr then (body[0], body[2].getSepArgs)
        else (if body.getNumArgs == 1 then body[0] else body, #[])
      -- A dotted name, as `K.len` or `w.x`, is a value, not a variant.
      let same ← if p.isOfKind ``Lang.fren_path && (pathSegs p).all (·.getId.isAtomic) then do
          let names := (pathSegs p).map (·.getId)
          pure (match (← getState).table.resolvePath cx.modName names shadowing with
            | .ok (.variant en i) => en.path == info.path && i == idx
            | _ => false)
        else pure false
      unless Core.givesBack same binders (args.map (exactText ∘ unparen)) do givenBack := false
    | _, _, _ => givenBack := false
  let trivial := Core.trivialMatch infos.size (infos[0]?.any (·.binds))
  let needless := Core.needlessMatch (givenBack && !anyGuard) wildcard scrutineeBack trivial
  if needless then
    let scrutinee : Core.BText := { text := scr, prec := exprPrec (unparen e[1]) }
    recordLint .needlessMatch e (help (tm (Core.needlessMatchMsg (scrutinee.inSlot slot (followedStx e)))))
  if flat && !anyGuard then
    for g in Core.sameArmGroups infos do
      let (i, msg) := Core.sameArmsMsg infos g slot (followedStx e)
      recordLint .matchSameArms arms[i]! (help (tm msg))
  let scrutinee : Core.BText := { text := exactText e[1], prec := exprPrec e[1] }
  let membership? := if anyGuard then none else Core.membershipParts? infos scrutinee slot
  if let some (pre, post, test) := membership? then
    recordLint .matchLikeMembership e (help (tm (Core.membershipMsg (pre ++ scrutinee.text ++ post) test)))
  -- `single_match_else` (`lint::single_match_else`).
  let bool := ty.isConstOf ``Bool || ty.isProp
  if let some fixed := (if anyGuard then none else
      Core.singleMatchElseFix? infos scrutinee slot (membership?.isSome || needless || trivial) (followedStx e) bool) then
    let msg := tm (Core.singleMatchElseMsg fixed (Core.hasComment (exactText e)))
    recordLint .singleMatchElse e (if msg.fixes.isEmpty then msg else help msg)
  -- `match_bool` (`lint::match_bool`).
  if bool && !anyGuard then
    if let some fixed := Core.matchBoolFix? pats infos scrutinee.text slot (membership?.isSome || trivial) (followedStx e) then
      let msg := tm (Core.matchBoolMsg fixed (Core.hasComment (exactText e)))
      recordLint .matchBool e (if msg.fixes.isEmpty then msg else help msg)
  let isTable := e.isOfKind ``Lang.tableMatchExpr
  -- `match_overlapping_arm` (`lint::match_overlapping_arm`). An arm with a
  -- guard is left out, as in Clippy; the arms of a table over a scrutinee
  -- are checked to be disjoint instead.
  let intervals := (pats.zip guarded).map fun (p, g) => p.top.map fun
    | .int lo hi => if g || isTable then none else some (lo, hi)
    | _ => none
  for ((j, b), (i, a)) in Core.overlappingArms intervals do
    recordLint .matchOverlappingArm (topAlts arms[j]![0]).1[b]! (Core.overlappingArmMsg (exactText (topAlts arms[i]![0]).1[a]!))
  unless isTable do
    for i in [0:arms.size] do lintCollapsible cx arms pats i
  for arm in arms, q in pats do lintOrPatterns (orNode (topAlts arm[0]).1 q)
  -- In a table over a scrutinee, `_` also takes what the guards of the
  -- other arms leave, which no pattern can name without overlapping them.
  unless flat && !(isTable && anyGuard) do return
  let some info := (← getState).enumOf? ty | return
  let some w := (Array.range infos.size).find? fun i => infos[i]!.wildcard && !guarded[i]! | return
  let names (p : Core.Pat) : Array Nat := match p with
    | .ctor k _ => #[k]
    | .or alts => alts.filterMap fun | .ctor k _ => some k | _ => none
    | _ => #[]
  let unguarded := (pats.zip guarded).filterMap fun (p, g) => if g then none else some p
  let covered := ((List.range info.variants.size).filter fun k => !unguarded.any (names · |>.contains k)).toArray
  let siblings ← (arms.flatMap fun arm => (topAlts arm[0]).1.filter (·.isOfKind ``Lang.variantPattern)).mapM fun p =>
    (pathSegs p[0]).mapM segName
  let table := (← getState).table
  -- The pattern that names each variant that `_` matches, if one resolves.
  let named := covered.map fun k => (table.variantPath? cx.modName cx.shadowing info.path info.variants[k]! siblings).map
    (Core.variantPattern · info.payloads[k]!.size)
  -- `wildcard_enum_match_arm` (`lint::wildcard_enum_match_arm`).
  let (_, fixable) := Core.wildcardEnumMatchArm true (named.filter (·.isNone)).size
  let pattern? := if fixable then some (" | ".intercalate (named.filterMap id).toList) else none
  let msg := tm (Core.wildcardEnumMsg (covered.map (info.path ++ info.variants[·]!)) pattern?)
  recordLint .wildcardEnumMatchArm arms[w]![0] (if fixable then help msg else msg)
  unless Core.wildcardSingle covered.size do return
  let msg := tm (Core.wildcardMsg (info.path ++ info.variants[covered[0]!]!) named[0]!)
  recordLint .wildcardSingleVariant arms[w]![0] (if named[0]!.isSome then help msg else msg)

/-- A binder of a pattern, with the type of its value, and its value, read
from the scrutinee with selectors. -/
structure PatBinder where
  source? : Option Syntax := none
  ident : Syntax
  type : Expr
  term : Term
  /-- Bound from a payload of the scrutinee, directly or nested, rather
  than to the whole scrutinee. -/
  payload : Bool := false
  deriving Inhabited

/-- The type of a value of the Lean type `t`, as patterns see it. -/
partial def patTyOf (st : State) (t : Expr) : Core.PatTy :=
  if t.isConstOf ``Bool || t.isProp then .bool
  else if t.isConstOf ``Int then .int
  else if t.isConstOf ``Nat then .nat
  else if t.isConstOf ``String then .string
  -- A type parameter, in a payload's type (`Core.Sigs`).
  else if let .bvar k := t then .param k
  else match st.enumOf? t with
    | some e => .enum e.path ((e.frenArgs t.getAppArgs).toList.map (patTyOf st))
    | none => .other

/-- The heads of the patterns within `p`, in preorder, as Lean's `match`
sees them (`PatHead`): an or-pattern at the top (`top`) is its
alternatives'. -/
partial def patHeads (p : Core.Pat) (top := true) : Array PatHead :=
  match p with
  | .wild false => #[.wildcard]
  | .wild true => #[.binder]
  | .bool _ | .int _ _ | .str _ => #[.literal]
  | .ctor _ args => #[.variant] ++ args.flatMap (patHeads · false)
  | .or alts => if top then alts.flatMap (patHeads · true) else #[.orPattern]

/-- The variants of each enumeration, with their payloads' types, as
patterns see them. -/
def patSigs : TermElabM Core.Sigs := do
  let st ← getState
  return fun p => ((st.enums.get? p).map fun e => (e.variants.zip e.payloads).map fun (v, ts) => (v, ts.map (patTyOf st))).getD #[]

/-- The name of the type `t`, where a `Bool` may be a `Prop`. -/
def patTypeName (t : Expr) : TermElabM String := if t.isProp then pure "Bool" else typeName t

/-- The integer `v`, as a term. -/
def intTerm (v : Int) : TermElabM Term := do
  let n := Syntax.mkNumLit (toString v.natAbs)
  if v < 0 then `((-$n : Int)) else `(($n : Int))

/-- The conjunction of `ts`, `none` for none. -/
def conjTerm (ts : Array Term) : TermElabM (Option Term) := do
  let some last := ts.back? | return none
  some <$> ts.pop.foldrM (init := last) fun t acc => `($t ∧ $acc)

/-- The value of the bound `b` of a range pattern. -/
def boundValue (cx : ExprCtx) (b : Syntax) : TermElabM Int := do
  if b.isOfKind ``Lang.numBound then
    let n := b[1].isNatLit?.getD 0
    return if b[0].isNone then n else -(n : Int)
  let p := b[0]
  let segs := pathSegs p
  if segs.size == 1 then
    let n := segs[0]!.getId
    if cx.vars.any (·.name == n.getRoot) then throwErrorAt b (Core.rangeBoundMsg "a variable").text
    if (cx.binder? n.getRoot).isSome then throwErrorAt b (Core.rangeBoundMsg "a binder").text
  match ← resolvePath cx.modName segs cx.shadowing with
  | .item { kind := .constItem, path, .. } =>
    let some c := (← getState).consts.find? path | throwErrorAt b s!"internal error: unknown constant `{path}`"
    unless c.type.isConstOf ``Int || c.type.isConstOf ``Nat do throwErrorAt b (Core.rangeBoundMsg s!"a constant of `{← typeName c.type}`").text
    let some v := c.int? | throwErrorAt b (Core.rangeConstantMsg path).text
    return v
  | r => throwErrorAt b (Core.rangeBoundMsg r.describe).text

mutual
/-- Resolves the pattern `p` of a value of type `ty`, which is `x`
(`Reqs/Lang/Patterns`), within an or-pattern if `inOr`: the pattern, its
binders in preorder, and its test, `none` if it matches every value. In a
pattern test (`test`), a binder is reported once the pattern is resolved,
rather than within an or-pattern. As the `fren` command's
`resolvePattern`, in the same order. -/
partial def resolvePattern (cx : ExprCtx) (ty : Expr) (x : Term) (inOr test : Bool) (p : Syntax) :
    TermElabM (Core.Pat × Array PatBinder × Option Term) := withRef p do
  -- Lean's parser has reported a pattern that it could not read.
  if p.hasMissing then throwAbortTerm
  let wrong (what : String) : TermElabM Unit := do throwErrorAt p (Core.patternTypeMsg (← patTypeName ty) what).text
  let pty := patTyOf (← getState) ty
  if p.isOfKind ``Lang.wildPattern then return (.wild, #[], none)
  if p.isOfKind ``Lang.strPattern then
    unless pty == .string do wrong "a pattern of `String`"
    let some v := p[0].isStrLit? | throwErrorAt p "internal error: a string pattern"
    liftMsg p (Core.checkStringChars v)
    return (.str v, #[], some (← `($x = Fren.Str.lit $(quote v))))
  -- A `Nat` is compared as an `Int`, as integer literals are.
  let xi ← if pty == .nat then `(($x : Int)) else pure x
  if p.isOfKind ``Lang.numPattern then
    unless pty == .int || pty == .nat do wrong "a pattern of `Int`"
    let n := p[1].isNatLit?.getD 0
    let v : Int := if p[0].isNone then n else -(n : Int)
    return (.int v v, #[], some (← `($xi = $(← intTerm v))))
  if p.isOfKind ``Lang.rangePattern || p.isOfKind ``Lang.fromPattern || p.isOfKind ``Lang.uptoPattern then
    unless pty == .int || pty == .nat do wrong "a pattern of `Int`"
    let (lo?, hi?, inclusive) :=
      if p.isOfKind ``Lang.rangePattern then (some p[0], some p[2], true)
      else if p.isOfKind ``Lang.fromPattern then (some p[0], p[2].getOptional?, false)
      else (none, some p[1], true)
    let lo ← lo?.mapM (boundValue cx)
    let hi ← hi?.mapM (boundValue cx)
    if Core.rangeEmpty lo hi inclusive then throwErrorAt p (Core.emptyRangeMsg (exactText p)).text
    let (l, h) := Core.rangeInterval lo hi inclusive
    let parts := (← l.toArray.mapM fun v => do `($(← intTerm v) ≤ $xi)) ++ (← h.toArray.mapM fun v => do `($xi ≤ $(← intTerm v)))
    return (.int l h, #[], ← conjTerm parts)
  -- A variant, a binder, `true` or `false`.
  let segs := pathSegs p[0]
  if segs.size == 1 && p[1].isNone then
    match ← patternName cx segs[0]! with
    | .boolLiteral =>
      unless pty == .bool do wrong "a pattern of `Bool`"
      let b := (Core.declaredName segs[0]!.getId).1 == `true
      return (.bool b, #[], some (← if b then `(($x : Prop)) else `(¬($x : Prop))))
    | .binder =>
      if inOr && !test then throwErrorAt p (Core.orBinderMsg (declaredIdent segs[0]!).1.getId).text
      return (.wild true, #[{ ident := segs[0]!, type := ty, term := x }], none)
    | .variant => pure ()
  let r ← resolveWritten cx.modName segs cx.shadowing cx.noteIndexes
  let some info := (← getState).enumOf? ty
    | throwErrorAt p (Core.patternTypeMsg (← patTypeName ty) (match r with
        | .variant en _ => s!"a pattern of `{Core.showPath en.path}`"
        | r => r.describe)).text
  let .variant en idx := r | throwErrorAt p (Core.notAVariantOfMsg info.path r.describe).text
  if en.path != info.path then
    throwErrorAt p (Core.notAVariantOfMsg info.path s!"a variant of `{Core.showPath en.path}`").text
  let v := info.path ++ en.variants[idx]!
  -- The payload's types, with the scrutinee's arguments (`lang::instantiation`).
  let tys := (info.payloadsAt ty.getAppArgs)[idx]!
  if let some msg := Core.variantMentionMsg? v tys.size (!p[1].isNone) then throwErrorAt p msg.text
  let args := patternArgs p
  unless args.size == tys.size do throwErrorAt p (Core.arityMsg v tys.size args.size "pattern").text
  let ctor := info.ctor idx
  let sels ← (Array.range tys.size).mapM fun k => `($(mkCIdent (info.sel idx k)) $x)
  let mut pats := #[]
  let mut bs := #[]
  let mut tests := #[← `($x = $(← ctorApp ctor ty.getAppArgs sels))]
  for a in args, t in tys, sel in sels do
    let (q, qbs, qt) ← resolveOr cx t sel inOr test a[0].getSepArgs false
    pats := pats.push q
    bs := bs ++ qbs.map ({ · with payload := true })
    tests := tests ++ qt.toArray
  return (.ctor idx pats, bs, ← conjTerm tests)

/-- Resolves the alternatives `alts` of an or-pattern (`isOr`, or of more
than one), or its only pattern. -/
partial def resolveOr (cx : ExprCtx) (ty : Expr) (x : Term) (inOr test : Bool) (alts : Array Syntax) (isOr : Bool) :
    TermElabM (Core.Pat × Array PatBinder × Option Term) := do
  if alts.size == 1 && !isOr then return ← resolvePattern cx ty x inOr test alts[0]!
  let mut pats := #[]
  let mut bs := #[]
  let mut tests := #[]
  let mut every := false
  for a in alts do
    let (q, qbs, qt) ← resolvePattern cx ty x true test a
    pats := pats.push q
    bs := bs ++ qbs
    match qt with
    | some t => tests := tests.push t
    | none => every := true
  if every then return (.or pats, bs, none)
  let some last := tests.back? | return (.or pats, bs, none)
  return (.or pats, bs, some (← tests.pop.foldrM (init := last) fun t acc => `($t ∨ $acc)))
end

/-- Resolves the pattern `top` of `match` or `is`. -/
def resolveTop (cx : ExprCtx) (ty : Expr) (x : Term) (test : Bool) (top : Syntax) :
    TermElabM (Core.Pat × Array PatBinder × Option Term) :=
  let (alts, isOr) := topAlts top
  resolveOr cx ty x false test alts isOr

/-- Elaborates a proposition. Errors are not recovered from with `sorry`: an
item that does not elaborate makes its procedure fail, rather than being checked
as `sorry`. -/
def elabProp (t : Term) (type : Expr := mkSort .zero) : TermElabM Expr := do
  -- Equality on an abstract type has no `Decidable` instance but the
  -- classical one, which `if` may need.
  let t ← `(open Classical in $t)
  let e ← withoutErrToSorry <| withSynthesize <| do
    if type.isProp || type.isConstOf ``Bool then
      let value ← elabTerm t none
      let found ← instantiateMVars (← inferType value)
      if type.isProp && found.isConstOf ``Bool then
        return ← mkEq value (mkConst ``Bool.true)
      if type.isConstOf ``Bool && (← isProp value) then
        let decision ← match ← trySynthInstance (mkApp (mkConst ``Decidable) value) with
          | .some decision => pure decision
          | _ => pure (mkApp (mkConst ``Classical.propDecidable) value)
        return mkApp2 (mkConst ``Decidable.decide) value decision
    elabTermEnsuringType t type
  let e ← instantiateMVars e
  if e.hasMVar || e.hasSorry then throwErrorAt t "could not elaborate this expression"
  return e

/-! ## Pattern types, and the items that declare types -/

/-- Records `undecidable` at `ref`, outside the decidable core, with `msg`. -/
def recordOutsideCore (ref : Syntax) (msg : Core.Msg) : TermElabM Unit := do
  modifyLocal fun l => { l with outsideCore := true }
  recordLint .undecidable ref msg

/-- The declared type `ty`, written in the module `modName`: its Lean type,
and the type with the patterns of the pattern types within it
(`Reqs/Lang/Types#pattern-types`), as the `fren` command's `elabPTy`. -/
partial def elabPType (modName : Name) (ty : Syntax) (params : Array Name := #[]) : TermElabM (Expr × Core.PTy) := do
  -- What Lean recovered from a parse error that it has reported.
  if ty.hasMissing then throwAbortTerm
  -- A function type is only a defined function's parameter's
  -- (`lang::function_type_place`).
  if let some w := Core.fnTypeWithin (typeSegs ty).toList then throwErrorAt ty (Core.fnTypePlaceMsg .constant w).text
  let text := Core.typeText (exactText ty)
  -- An element type, which is never a `Nat` (`lang::nat_place`), nor a type
  -- parameter (`lang::type_parameter_place`), and whose constraint, if any,
  -- quantifies over the elements, outside the decidable core
  -- (`lang::pattern_place`).
  let elem (e : Syntax) : TermElabM (Expr × Core.PTy) := do
    let (t, pt) ← elabPType modName e params
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
    if let .bvar k := t then throwErrorAt e (Core.typeParamPlaceMsg params[k]! .element "").text
    if let some n := t.constName?.bind (Core.typeParamName? ·) then
      throwErrorAt e (Core.typeParamPlaceMsg (Name.mkSimple n) .element "").text
    if (pt.cons (← getState).shapeOf).isSome then recordOutsideCore e Core.undecidableElementsMsg
    return (t, pt)
  if ty.isOfKind ``Lang.relType then
    let (a, pa) ← elem ty[2]
    let (b, pb) ← elem ty[4]
    return (mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) a b),
      { ty := .rel pa.ty pb.ty, elems := #[pa, pb], text })
  if ty.isOfKind ``Lang.seqType then
    let (a, pa) ← elem ty[2]
    return (mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) a, { ty := .seq pa.ty, elems := #[pa], text })
  if ty.isOfKind ``Lang.setType then
    let (a, pa) ← elem ty[2]
    return (mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) a, { ty := .set pa.ty, elems := #[pa], text })
  -- An instance of a generic type, `G<A, B>`, whose arguments are declared
  -- types, with their patterns, as the `fren` command's `elabBasePTy` checks
  -- them (`Reqs/Lang/Generics#type-parameters`).
  if ty.isOfKind ``Lang.instanceType then
    let segs := pathSegs ty[0]
    let given := ty[2].getSepArgs
    -- `Set`, `Seq` and `Rel` with too many or too few types, which the
    -- `fren` command's parser reports, at what follows the types it reads.
    if segs.size == 1 && [`Set, `Seq, `Rel].contains segs[0]!.getId then
      let n := if segs[0]!.getId == `Rel then 2 else 1
      let at_ := if given.size > n then ty[2].getArgs[2 * n - 1]! else ty[3]
      throwErrorAt at_ s!"expected `{if given.size > n then ">" else ","}`"
    let mut args := #[]
    let mut pts := #[]
    for a in given do
      let (t, pt) ← elabPType modName a params
      -- An argument is never `Nat` (`lang::nat_place`), and is a payload's
      -- type.
      unless !t.isConstOf ``Nat || Core.natPlaceAccepted .argument do throwErrorAt a (Core.natPlaceMsg .argument).text
      if let some (p, whole) ← abstractWithin? t then throwErrorAt a (Core.abstractFieldMsg p true !whole).text
      args := args.push t
      pts := pts.push pt
    let t ← instanceType modName segs args params ty
    let some ct ← coreTy? t params | throwErrorAt ty s!"internal error: a type without a Fren type"
    -- A recursive enumeration's type arguments bring no constraints
    -- (`Reqs/Lang/Generics#pattern-types-as-type-arguments`).
    if let .enum p _ := ct then
      if ((← getState).shapeOf p).any (·.recursive) then
        for a in given, pt in pts do
          if (pt.cons (← getState).shapeOf).isSome then
            throwErrorAt a (Core.recursiveArgumentMsg pt.text (Core.showPath p)).text
    -- Nor do they within an instance, once its arguments stand for its
    -- parameters.
    if let some p := ct.dataPath? then
      if let some (a, q) := Core.recursiveArgumentWithin? (← getState).shapeOf p pts then
        throwErrorAt ty (Core.recursiveArgumentMsg a.text (Core.showPath q)).text
    return (t, { ty := ct, elems := pts, text })
  -- A path: an alias names a type, as declared.
  let t ← elabType modName ty params
  let segs := pathSegs (typePath? ty).get!
  if let .ok (.item { kind := .typeItem, path, .. }) := (← getState).table.resolvePath modName (← segNames segs) #[] then
    if let some (t, pt) := (← getState).aliases.get? path then return (t, { pt with text })
  let some ct ← coreTy? t params | throwErrorAt ty s!"internal error: a type without a Fren type"
  return (t, { Core.PTy.plain ct with text })

/-- That the term `x`, of the type `ty`, matches the pattern `p`, as a
pattern test is, and as the `fren` command's `patSmt` says. -/
partial def patTerm (ty : Core.Ty) (p : Core.Pat) (x : Term) : TermElabM Term := do
  match p with
  | .wild _ => `(True)
  | .bool b => if b then `(($x : Prop)) else `(¬($x : Prop))
  | .int lo hi =>
    let xi ← if ty == .nat then `(($x : Int)) else pure x
    if lo.isSome && lo == hi then return ← `($xi = $(← intTerm lo.get!))
    let parts := (← lo.toArray.mapM fun v => do `($(← intTerm v) ≤ $xi)) ++ (← hi.toArray.mapM fun v => do `($xi ≤ $(← intTerm v)))
    return (← conjTerm parts).getD (← `(True))
  | .str v => `($x = Fren.Str.lit $(quote v))
  | .ctor idx args =>
    let .enum ep targs := ty | `(True)
    let some info := (← getState).enums.get? ep | `(True)
    let ctor := info.ctor idx
    -- With an instance's arguments for its type parameters.
    let tys := (info.shape.inst (targs.toArray.map .plain)).parts[idx]?.getD #[]
    let sels ← (Array.range (info.payloads[idx]!.size)).mapM fun k => `($(mkCIdent (info.sel idx k)) $x)
    let mut tests := #[← `($x = $(mkCIdent ctor) $sels*)]
    for a in args, k in [0:args.size] do
      unless a matches .wild _ do
        tests := tests.push (← patTerm (tys[k]?.map (·.ty) |>.getD .int) a sels[k]!)
    return (← conjTerm tests).get!
  | .or alts =>
    if alts.any (· matches .wild _) then return ← `(True)
    let ts ← alts.mapM (patTerm ty · x)
    let some last := ts.back? | `(True)
    ts.pop.foldrM (init := last) fun t acc => `($t ∨ $acc)

/-- The constraint `c` of the term `x` (`Core.Cons`), as the `fren`
command's `consSmt` says, where `depth` numbers the bound variables of the
quantifiers around it. -/
partial def consTerm (c : Core.Cons) (x : Term) (depth : Nat := 0) : TermElabM Term := do
  let st ← getState
  match c with
  | .predicate i =>
    let some f := st.defined.get? i.predicate | throwError "internal error: unknown subset predicate"
    -- A Nat result is represented by Int in uninterpreted-function facts.
    -- Its nonnegativity is a separate base fact; evaluate the invariant
    -- on the corresponding Nat value while retaining that base fact.
    let x ← if (f.ptys.1[0]?).any (·.ty == .nat) then do
      let value ← elabTerm x none
      let type ← whnf (← inferType value)
      if type.isConstOf ``Int then `(Int.toNat $x) else pure x
      else pure x
    `($(mkCIdent f.decl) $(f.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $x)
  | .pat ty p => patTerm ty p x
  | .atLeast0 => `(0 ≤ $x)
  | .fields path _ cs =>
    let some r := st.records.get? path | `(True)
    let ts ← cs.mapM fun (k, c) => do consTerm c (← `($(mkCIdent (r.decl ++ r.fields[k]!.1)) $x)) depth
    return (← conjTerm ts).getD (← `(True))
  | .newtype path c =>
    let some n := st.newtypes.get? path | `(True)
    consTerm c (← `($(mkCIdent n.field) $x)) depth
  | .payloads path _ cs =>
    let some info := st.enums.get? path | `(True)
    let ts ← cs.mapM fun (v, k, c) => do
      let ctor := info.ctor v
      let sels ← (Array.range (info.payloads[v]!.size)).mapM fun j => `($(mkCIdent (info.sel v j)) $x)
      `($x = $(mkCIdent ctor) $sels* → $(← consTerm c sels[k]! depth))
    return (← conjTerm ts).getD (← `(True))
  | .elems seq _ c =>
    let b := mkIdent (Name.mkSimple s!"fren_e{depth}")
    if seq then
      `(∀ $b:ident : Int, 0 ≤ $b ∧ $b < Fren.Seq.len $x → $(← consTerm c (← `(Fren.Seq.nth $x $b)) (depth + 1)))
    else `(∀ $b:ident, $b ∈ $x → $(← consTerm c b (depth + 1)))
  | .pairs _ _ ca cb =>
    let (u, v) := (mkIdent (Name.mkSimple s!"fren_a{depth}"), mkIdent (Name.mkSimple s!"fren_b{depth}"))
    let parts := (← ca.toArray.mapM (consTerm · u (depth + 1))) ++ (← cb.toArray.mapM (consTerm · v (depth + 1)))
    `(∀ $u:ident $v:ident, ($u, $v) ∈ $x → $((← conjTerm parts).getD (← `(True))))
  | .all cs =>
    let ts ← cs.mapM (consTerm · x depth)
    return (← conjTerm ts).getD (← `(True))

/-- The constraint `c` of a value of the Lean type `ty`, as a predicate:
`fun x => c x`. -/
def predOf (ty : Expr) (c : Core.Cons) : TermElabM Expr :=
  withLocalDeclD `fren_x ty fun x => do
    let p ← elabProp (← consTerm c (mkIdent `fren_x))
    mkLambdaFVars #[x] p

/-- The constraint `c` of a value of the Lean type `ty`, which mentions the
type parameters `params` of a generic type as loose bound variables, as a
predicate over the arguments of a selector of the type, `{T : Type}`,
`[Inhabited T]` and the value: `fun T inst x => c x`. -/
def genericPredOf (params : Array Name) (ty : Expr) (c : Core.Cons) : TermElabM Expr := do
  if params.isEmpty then return ← predOf ty c
  let rec go (k : Nat) (ts : Array Expr) : TermElabM Expr := do
    if h : k < params.size then
      withLocalDecl params[k] .implicit (mkSort Level.one) fun t => go (k + 1) (ts.push t)
    else
      let insts := ts.mapIdx fun i t => (Name.mkSimple s!"inst{i}", mkApp (mkConst ``Inhabited [Level.one]) t)
      withLocalDeclsDND insts fun is =>
        withLocalDeclD `fren_x (ty.instantiate ts) fun x => do
          let p ← elabProp (← consTerm c (mkIdent `fren_x))
          mkLambdaFVars (ts ++ is ++ #[x]) p
  termination_by params.size - k
  go 0 #[]

/-- The constraint that a value of the declared type `pt`, of the Lean
type `ty`, brings, as a predicate (`Core.PTy.cons`). -/
def factPred? (ty : Expr) (pt : Core.PTy) (nat : Bool := false) : TermElabM (Option Expr) := do
  let some c := pt.cons (← getState).shapeOf nat | return none
  some <$> predOf ty c

/-- What the checks need of the elaborator (`ElabHooks`): for the instances
of generic functions without a body, the Lean types of their signatures,
and the constraints of their result types (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`). -/
def elabHooks : ElabHooks where
  leanType t := (leanTypeOf t).run'
  fact pt nat := (do
    if (pt.cons (← getState).shapeOf).isNone then return none
    let nat := nat && pt.ty == Core.Ty.nat
    let ty ← if nat then pure (Lean.mkConst ``Int) else leanTypeOf pt.ty
    factPred? ty pt nat).run'
  coreTy e := return coreTyOf (← getState) e

/-- The declared type of the variable, parameter or function `name`,
written `ty?`, which is `Bool` if it is not written: its Lean type, and the
type with its patterns, as `varType` checks it. -/
def varPType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM (Expr × Core.PTy) := do
  let n := name.getId
  let t ← ty?.mapM (elabPType modName)
  if let some ty := ty? then lintRelTypes modName ty
  unless n.toString.startsWith "#match" do liftMsg name (Core.checkVarName n (t.map (·.1.isConstOf ``Bool)))
  if let (some ty, some (t, pt)) := (ty?, t) then
    if pt.invariants.isEmpty && !n.toString.startsWith "#match" then lintBoolType n ty t
  return t.getD (Lean.mkConst ``Bool, .plain .bool)

/-- The declared type of the `k`th field or payload value of the variant
`v` of a record, newtype or enumeration whose parts are `shape`'s, with the
type arguments `args` for its type parameters, if it is generic, as the
`fren` command's `partPTy` has it (`Core.PTy.subst`). -/
def partPType (shape : Core.DataShape) (v k : Nat) (args : Array Core.Ty := #[]) : Core.PTy :=
  let t := (shape.parts[v]?.bind (·[k]?)).getD default
  if args.isEmpty then t else t.subst (args.map .plain)

/-- Records the obligation of the value `x`, given at `ref` where the type
`t` is declared, if it has one, for the pattern-type check
(`Reqs/Check#pattern-types`): its guard implies that the value matches,
marked with its type (`Fren.typeObligation`). -/
def noteObligation (cx : ExprCtx) (place : Core.ValuePlace) (ref : Syntax) (t : Core.PTy) (x : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some o := Core.siteObligation place (t.obligation (← getState).shapeOf) | return
  let parts := o.namedParts
  let parts := if parts.isEmpty then #[(.anonymous, o)] else parts
  for (name, part) in parts do
    let label := if name.isAnonymous then t.text else "@invariant:" ++ Core.showPath name
    let goal ← `(Fren.typeObligation $(quote label) $(← consTerm part x))
    let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) goal
    modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- The Lean type of a field or payload, `ty`, of the type `ownName`, with
the type parameters `params`, being declared in the module `modName` as the
Lean type `own`, and its type as declared, checking that it is accepted
(`lang::field_type`, `lang::type_parameter_place`), in the order of the
`fren` command's checks. -/
def fieldType (modName : Name) (ty : Syntax) (own : Name) (place : FieldPlace) (ownName : Name)
    (params : Array Name := #[]) : CommandElabM (Expr × Core.PTy) := do
  let path := modName ++ ownName
  checkFnTypeSite (if place == .payload then .payload else .field) ty
  let segs := typeSegs ty
  let (whole, inSet) := Core.ownIn segs ownName.toString
  let (isOwn, declared, nested) := Core.ownArgs segs ownName.toString (params.map toString)
  match place with
  | .payload =>
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
    -- A recursive payload is the enumeration with its own parameters.
    let place := Core.recursivePlace declared nested
    if (isOwn || nested) && !Core.typeParamPlaceAccepted place then
      throwErrorAt ty (Core.typeParamPlaceMsg .anonymous place (Core.ownWritten path params) !params.isEmpty).text
    if isOwn then
      return (mkAppN (Lean.mkConst own) ((Array.range params.size).map (.bvar ·)),
        .plain (.enum path (params.toList.zipIdx.map fun (p, k) => .param k p)))
  | .field =>
    if isOwn || nested then throwErrorAt ty (Core.recursiveRecordMsg ownName).text
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
  | .newtype =>
    if whole then throwErrorAt ty (Core.recursiveRecordMsg ownName).text
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
  let payload := place == .payload
  let (t, pt) ← liftTermElabM (elabPType modName ty params)
  lintRelTypes modName ty params
  if let some (p, whole) ← abstractWithin? t then
    unless Core.fieldTypeAccepted true false false payload do
      throwErrorAt ty (Core.abstractFieldMsg p payload !whole).text
  return (t, pt)

/-- The type parameters `params` of the enumeration or record being
declared in the module `modName`, checked as the `fren` command checks
them: distinct (`lang::distinct_names`), without `!`, and without the name
of a built-in type or of an item in scope (`Reqs/Lang/Generics`). -/
def elabTypeParams (modName : Name) (params : Array Syntax) : CommandElabM (Array Name) := do
  for p in params do discard (segName p)
  let ns := params.map (·.getId)
  if let some k := (Core.repeatsAt ns)[0]? then throwErrorAt params[k]! (Core.dupTypeParamMsg ns[k]!).text
  for p in params, n in ns do
    liftMsg p (Core.checkNoBang n)
    if [`Bool, `Int, `Nat, `String, `Set, `Seq, `Rel].contains n then
      throwErrorAt p (Core.typeParamNameMsg n s!"the built-in type `{n}`").text
    if let .ok r := (← getState).table.resolvePath modName #[n] #[] then
      throwErrorAt p (Core.typeParamNameMsg n r.describe).text
  return ns

/-- The binders of the type parameters `params` of a generic type's
declaration, `(T : Type)`, or implicit, `{T : Type}`, followed by an
`Inhabited` instance of each, `[Inhabited T]`. -/
def paramBinders (params : Array Name) (implicit : Bool) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  if !implicit then
    return ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent p) : Type))
  let types ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| {$(mkIdent p) : Type})
  let insts ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| [Inhabited $(mkIdent p)])
  return types ++ insts

/-- The Lean type `decl`, applied to the type parameters `params`. -/
def selfType (decl : Name) (params : Array Name) : CommandElabM Term :=
  if params.isEmpty then pure (mkCIdent decl) else `(($(mkCIdent decl) $(params.map fun p => (mkIdent p : Term))*))

@[command_elab Lang.enumCmd] def elabEnum : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "enum" nameStx
  checkFresh modName n nameStx
  lintName .enumeration n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  let params ← elabTypeParams modName (if stx[4].isNone then #[] else stx[4][0][1].getSepArgs)
  let variantStxs := stx[6].getSepArgs
  -- Distinct names (`lang::distinct_names`), of names that are single
  -- segments, as the `fren` command parses them.
  for v in variantStxs do discard (segName v[0])
  if let some k := (Core.repeatsAt (variantStxs.map (·[0].getId)))[0]? then
    throwErrorAt variantStxs[k]![0] (Core.dupVariantMsg variantStxs[k]![0].getId).text
  let mut variants := #[]
  let mut payloads : Array (Array Expr) := #[]
  let mut ptys : Array (Array (Core.PTy × Syntax)) := #[]
  let mut nRecursive := 0
  let mut unbounded := false
  for v in variantStxs do
    let vn ← checkItemName "variant" v[0]
    lintName .variant vn v[0]
    variants := variants.push vn
    let tys := if v[1].isNone then #[] else v[1][1].getSepArgs
    let tps ← tys.mapM fun t => fieldType modName t decl .payload n params
    let ts := tps.map (·.1)
    let st ← getState
    -- Recursive if a payload's type is the enumeration or built from it
    -- (`lang::well_founded`).
    let own := (Core.PTy.plain (.enum path (params.toList.zipIdx.map fun (p, k) => .param k p))).node
    let nodes := tps.toList.map fun (t, pt) => if t.getAppFn.isConstOf decl then own else pt.node
    if Core.recursiveVariant st.shapeOf own nodes then nRecursive := nRecursive + 1
    unbounded := unbounded || tps.any fun (t, pt) => t.getAppFn.isConstOf decl || (factsOf st pt).unbounded
    payloads := payloads.push ts
    ptys := ptys.push (tps.zip tys |>.map fun ((_, pt), t) => (pt, t))
  unless Core.wellFounded variants.size nRecursive do throwErrorAt nameStx (Core.illFoundedMsg n).text
  -- A recursive enumeration's payloads are never `Nat`s (`lang::nat_place`),
  -- and a constraint of one is outside the decidable core
  -- (`lang::pattern_place`).
  let isRecursive := nRecursive > 0
  let shape : Core.DataShape := { recursive := isRecursive, parts := ptys.map (·.map (·.1)) }
  if isRecursive then
    let st ← getState
    for pts in ptys do
      for (pt, t) in pts do
        if pt.ty == .nat then throwErrorAt t (Core.natPlaceMsg .recursivePayload).text
        if (pt.cons (fun q => if q == path then some shape else st.shapeOf q) true).isSome then
          liftTermElabM (recordOutsideCore t Core.undecidableRecursivePayloadMsg)
  -- `enum_variant_names` (`lint::enum_variant_names`, `lint::variant_has_enum_name`).
  if let some msg := Core.enumVariantNamesMsg? n variants then recordLint .enumVariantNames nameStx msg
  for v in variantStxs, vn in variants do
    if let some msg := Core.variantNameMsg? n vn then recordLint .enumVariantNames v[0] msg
  -- Only an enumeration without payloads may be ordered
  -- (`lang::ordered_declaration`); the first payload is reported.
  let withPayload := variantStxs.filter (!·[1].isNone)
  unless Core.orderedDeclAccepted isOrdered withPayload.size none do
    throwErrorAt withPayload[0]![0] (Core.orderedPayloadMsg n withPayload[0]![0].getId).text
  -- One of the prelude's types is the Lean type that it is, for which
  -- nothing is generated (`Reqs/Lang/Prelude#lean`).
  if let some l := Core.leanTypeOf? path then
    record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
    record (.enumInfo { path, decl := l.lean, variants, payloads, unbounded, ordered := isOrdered, shape, params, lean? := some l })
    return
  let own : Term ← if params.isEmpty then pure (mkIdent decl) else `(($(mkIdent decl) $(params.map fun p => (mkIdent p : Term))*))
  let ctors ← (variants.zip payloads).mapM fun (v, ts) => do
    let bs ← ts.mapIdxM fun k t => do
      let ty := if t.getAppFn.isConstOf decl then own else typeSyntax t params
      `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent (Name.mkSimple s!"x{k}")) : $ty))
    `(Lean.Parser.Command.ctor| | $(mkIdent v):ident $bs:bracketedBinder*)
  -- A generic type has a parameter of type `Type` for each of its type
  -- parameters (`Reqs/Generated#generic-types`). Declared by its name
  -- relative to the current namespace, `decl`, so that Lean names the
  -- instances it derives in `decl`'s namespace, apart from other items' and
  -- Lean's own.
  let binders ← paramBinders params false
  elabCommand (← `(inductive $(mkIdentFrom nameStx (leanName .anonymous path)):ident $binders:bracketedBinder* where $ctors:ctor*
    deriving DecidableEq, Repr, Inhabited))
  if payloads.all (·.isEmpty) && params.isEmpty then
    let vals := variants.map fun v => mkCIdent (decl ++ v)
    -- Named after the full path: an anonymous instance is named after `n`
    -- alone, which enumerations in different modules can share.
    elabCommand (← `(instance $(mkIdent (`_root_ ++ decl ++ `instFinite)):ident : Fren.Finite $(mkCIdent decl) :=
      ⟨[$vals,*], by intro x; cases x <;> decide⟩))
  -- A selector for each value of each payload, which a `match` reads; of a
  -- generic type, with its parameters implicit, and an `Inhabited` instance
  -- of each, for `default`.
  let self ← selfType decl params
  let implicits ← paramBinders params true
  for v in variants, ts in payloads do
    let ctor := decl ++ v
    let xs := (Array.range ts.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
    for t in ts, k in [0:ts.size] do
      let sel := mkIdent (`_root_ ++ selectorName ctor k)
      let x := xs[k]!
      let ty := if t.getAppFn.isConstOf decl then self else typeSyntax t params
      let cmd ← if variants.size == 1 then
          `(def $sel:ident $implicits:bracketedBinder* (v : $self) : $ty := match v with | $(mkCIdent ctor) $xs* => $x)
        else
          `(def $sel:ident $implicits:bracketedBinder* (v : $self) : $ty := match v with | $(mkCIdent ctor) $xs* => $x | _ => default)
      elabCommand cmd
      -- So that `simp [fren_spec]` reads a payload of a variant that is
      -- built (`Reqs/Generated#proofs`).
      let names ← get
      elabCommand (← `(attribute [fren_spec] $sel:ident))
      modify fun t => { t with nextMacroScope := names.nextMacroScope, ngen := names.ngen }
  -- Each read of a recursive enumeration's payload brings the payload's
  -- constraint (`Core.readCons`), as an application does.
  let readFacts ← if !isRecursive then pure #[] else liftTermElabM do
    let st ← getState
    let shapes (q : Name) := if q == path then some shape else st.shapeOf q
    let mut out := #[]
    for v in variants, ts in payloads, vi in [0:variants.size] do
      for t in ts, k in [0:ts.size] do
        if let some c := Core.readCons shapes path vi k then
          out := out.push (selectorName (decl ++ v) k, ← genericPredOf params t c)
    return out
  record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
  record (.enumInfo { path, decl, variants, payloads, unbounded, ordered := isOrdered, shape, readFacts, params })
  unless isPub do recordItem .enumeration path nameStx

@[command_elab Lang.structCmd] def elabStruct : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  let params ← elabTypeParams modName (if stx[4].isNone then #[] else stx[4][0][1].getSepArgs)
  -- A generic record is not ordered, for now (`Core.orderedGenericAccepted`).
  unless Core.orderedGenericAccepted isOrdered params.size do throwErrorAt nameStx (Core.orderedGenericMsg n).text
  let mut fields : Array (Name × Expr) := #[]
  let mut ptys : Array Core.PTy := #[]
  let fieldStxs := stx[6].getSepArgs
  for f in fieldStxs do discard (segName f[0])
  if let some k := (Core.repeatsAt (fieldStxs.map (·[0].getId)))[0]? then
    throwErrorAt fieldStxs[k]![0] (Core.dupFieldMsg fieldStxs[k]![0].getId).text
  for f in fieldStxs do
    let fn := f[0].getId
    liftMsg f[0] (Core.checkNoBang fn)
    lintName .field fn f[0]
    let (t, pt) ← if f[1].isNone then pure (Lean.mkConst ``Bool, .plain .bool) else fieldType modName f[1][1] decl .field n params
    ptys := ptys.push pt
    -- As for a variable (`lang::bool_naming`).
    liftMsg f[0] (Core.checkVarName fn (if f[1].isNone then none else some (t.isConstOf ``Bool)))
    unless f[1].isNone || !pt.invariants.isEmpty do liftTermElabM (lintBoolType fn f[1][1] t)
    fields := fields.push (fn, t)
  -- `struct_field_names` (`lint::struct_field_names`, `lint::field_has_record_name`).
  if let some msg := Core.structFieldNamesMsg? n (fields.map (·.1)) then recordLint .structFieldNames nameStx msg
  for f in fieldStxs, (fn, _) in fields do
    if let some msg := Core.fieldNameMsg? n fn then recordLint .structFieldNames f[0] msg
  -- `struct_excessive_bools` (`lint::struct_excessive_bools`).
  let nBools := (fields.filter (·.2.isConstOf ``Bool)).size
  if Core.structExcessiveBools nBools then recordLint .structExcessiveBools nameStx (Core.structExcessiveBoolsMsg n nBools)
  let st ← getState
  -- An ordered record's fields are ordered (`lang::ordered_declaration`);
  -- the first that is not is reported.
  let first? := Core.PTy.firstUnordered? st.orderedDecl ptys.toList
  unless Core.orderedDeclAccepted isOrdered 0 first? do
    if let some k := first? then
      let f := fieldStxs[k]!
      throwErrorAt (if f[1].isNone then f[0] else f[1][1]) (Core.unorderedFieldMsg .record n fields[k]!.1 ptys[k]!.ty).text
  let unbounded := ptys.any fun pt => (factsOf st pt).unbounded
  let bs ← fields.mapM fun (f, t) => `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent f):ident : $(typeSyntax t params)))
  let binders ← paramBinders params false
  elabCommand (← `(structure $(mkIdentFrom nameStx (leanName .anonymous path)):ident $binders:bracketedBinder* where
    $(mkIdent (if params.isEmpty then `«{}» else Name.mkSimple "mk!")):ident :: $bs:structExplicitBinder*
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.recordInfo { path, decl, fields, unbounded, shape := { isRecord := true, parts := #[ptys] }, params, ordered := isOrdered })
  unless isPub do recordItem .record path nameStx

@[command_elab Lang.newtypeCmd] def elabNewtype : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
  openGenerated
  checkLexemes stx
  checkParsed stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  -- Exactly one field, whose type is accepted as a record's field's
  -- (`lang::newtype`).
  let tys := stx[5].getSepArgs
  let some ty := tys[0]? | throwErrorAt nameStx (Core.newtypeFieldsMsg path 0).text
  unless Core.newtypeAccepted tys.size true do throwErrorAt nameStx (Core.newtypeFieldsMsg path tys.size).text
  let (under, pt) ← fieldType modName ty decl .newtype n
  -- An ordered newtype's underlying type is ordered
  -- (`lang::ordered_declaration`).
  unless Core.orderedDeclAccepted isOrdered 0 (Core.PTy.firstUnordered? (← getState).orderedDecl [pt]) do
    throwErrorAt ty (Core.unorderedFieldMsg .newtype n (Name.mkSimple "0") pt.ty).text
  let unbounded := Core.newtypeUnbounded (factsOf (← getState) pt).unbounded
  -- One field, `«0»`, so that `x.0` in Fren is `x.«0»` in Lean.
  elabCommand (← `(structure $(mkIdentFrom nameStx (leanName .anonymous path)):ident where
    $(mkIdent `mk):ident :: $(mkIdent (Name.mkSimple "0")):ident : $(typeSyntax under)
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.newtypeInfo { path, decl, under, unbounded, shape := { isRecord := true, isNewtype := true, parts := #[#[pt]] }, ordered := isOrdered })
  unless isPub do recordItem .record path nameStx


open Lang in
/-- Whether `e` is written as a sequence: a sequence literal, or a `++`, a
conditional or a `match` with one among its shared parts, so that the right
of `in` is checked against a sequence, as in the `fren` command. -/
partial def seqShaped (e : Syntax) : Bool :=
  if e.isOfKind ``Lang.seqExpr then true
  else if isMatchLike e then (matchSourceArms e).any (seqShaped ·[3])
  else match e with
    | `(fren_expr| $a ++ $b) | `(fren_expr| if $_ then $a else $b) => seqShaped a || seqShaped b
    | _ => false

/-- Two parts of one type, `a` in `cxa` and `b` in `cxb`, as the `fren`
command's `pair`: one that does not synthesize its type is translated after
the other, if that one does, and expects the other's type, widened unless a
`Nat` is expected here (`lang::checked`). -/
def pairTerms (toTerm : ExprCtx → Syntax → TermElabM Term) (cxa cxb : ExprCtx) (a b : Syntax) :
    TermElabM (Term × Term) := do
  let sibling (cx' : ExprCtx) (t : Term) : TermElabM (Option Core.Ty) := do
    if cx'.expected? == some .nat then return some .nat
    return ((← frenTypeOf? t).map (·.widen)).orElse fun _ => cx'.expected?
  if !(← synthesizes cxa a) && (← synthesizes cxb b) then
    let y ← toTerm cxb b
    return (← toTerm { cxa with expected? := ← sibling cxa y } a, y)
  let x ← toTerm cxa a
  return (x, ← toTerm { cxb with expected? := ← sibling cxb x } b)

open Lang in
/-- Translates a record literal, where `go` translates its values, given
the type each is expected to have. -/
def recordTerm (go : Option Core.Ty → Syntax → TermElabM Term) (cx : ExprCtx) (expected? : Option Core.Ty) (e : Syntax) :
    TermElabM Term := withRef e do
  let r ← resolveWritten cx.modName (pathSegs e[0]) cx.shadowing cx.noteIndexes
  let .item { kind := .recordItem, path, .. } := r | throwErrorAt e[0] (Core.wrongKindMsg "a record" r).text
  if (← getState).newtypes.contains path then throwErrorAt e[0] (Core.constructionMsg path true).text
  let some info := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
  let given := e[2].getSepArgs
  match Core.checkFieldInits path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (some i, msg) => throwErrorAt given[i]![0] msg.text
  | .error (none, msg) => throwError msg.text
  if cx.noteIndexes then lintFieldOrder e path (info.fields.map (·.1)) given
  -- A generic record's type arguments are inferred, as the `fren` command
  -- infers them (`Reqs/Lang/Generics#type-arguments`).
  if let some c ← construction? cx e then
    let vals ← info.fields.mapM fun (f, _) => do
      let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
      if cx.noteIndexes then lintRedundant b true
      if b[1].isNone then return (← `(fren_expr| $(⟨b[0]⟩):ident)).raw else pure b[1][1]
    let note (k : Nat) (t : Core.Ty) := s!"note: `{info.fields[k]!.1}` of `{Core.showPath path}` has type `{t.show}`"
    let (args, targs) ← constructionTerms go cx expected? e c vals (Core.showPath path) note
    -- Each field's obligation, of its type with the record's arguments.
    for v in vals, t in args, k in [0:vals.size] do
      noteObligation cx .field v (partPType info.shape 0 k targs) t
    if cx.noteIndexes then lintStructInit (go none) (.record path targs.toList) e given
    return ← ctorApp info.ctor (← targs.mapM leanTypeOf) args e[0]
  let args ← info.fields.zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
    if cx.noteIndexes then lintRedundant b true
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath path}` has type `{tn}`"
    noteObligation cx .field v (partPType info.shape 0 k) t
    return t
  if cx.noteIndexes then lintStructInit (go none) (.record path []) e given
  `($(mkCIdentFrom e[0] (recordCtor info.decl)) $args*)

open Lang in
/-- Translates a record update into the record literal whose other fields
are read from the updated value (`Reqs/Lang/Expressions#record-updates`),
where `toTerm` translates its parts. -/
def updateTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e <| withFreshMacroScope do
  let rv ← toTerm { cx with emptyOk := Core.Position.synthesized.checked false false } e[1]
  let ty ← typeOf rv
  let some info := (← getState).recordOf? ty
    | throwErrorAt e[1] (Core.updateBaseMsg (← typeName ty)).text
  let given := e[3].getSepArgs
  match Core.checkFieldUpdates info.path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (i, msg) => throwErrorAt given[i]![0] msg.text
  -- A `Nat` is expected of a `Nat` field (`lang::literal_type`).
  let go (x? : Option Core.Ty) := toTerm { cx with emptyOk := Core.Position.declared.checked false false, expected? := x?,
                                                   natOk := x? == some .nat }
  -- `r` bound once, so that nested updates grow linearly.
  let bind := info.fields.size > given.size && !rv.raw.isIdent
  let r ← if bind then `(r) else pure rv
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let targs := ty.getAppArgs
  let cargs := match ← coreTy? ty with
    | some (.record _ as) => as.toArray
    | _ => #[]
  let args ← (info.fieldsAt targs).zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | `($(mkCIdentFrom e[1] (info.decl ++ f)) $r)
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath info.path}` has type `{tn}`"
    noteObligation cx .field v (partPType info.shape 0 k cargs) t
    return t
  let lit ← ctorApp info.ctor targs args e
  if bind then `(let r := $rv; $lit) else pure lit

/-- The type of a `match`'s arms so far, `armsTy?`, after the arm whose body
`ref` is translated to `body` and checked against `shared?`
(`lang::arm_type`). A body that does not synthesize its type has the one
it is checked against, as in the `fren` command. -/
def armType (cx : ExprCtx) (armsTy? : Option Core.Ty) (ref : Syntax) (body : Term) (shared? : Option Core.Ty) :
    TermElabM (Option Core.Ty) := do
  let synth ← synthesizes cx ref
  let t? := (← frenTypeOf? body).orElse fun _ => if synth then none else shared?
  let some t := t? | return armsTy?
  return some (← liftMsg ref (Core.checkArm armsTy? t))

/-- Records the questions about the arms of the `match` `e`, whose patterns
are `pats`, each taken where `taken` says, of which those with a guard
are `guarded`, for its completeness and reachability checks
(`check::completeness`, `check::reachability`): completeness, unless its
arms without guards are exhaustive, is reported at `match`, and the
reachability of an arm at its pattern. Of a table over a scrutinee
(`table?`, the pairs of its arms that the disjointness check asks about,
whose guards' indexes are in range where `defined` says), also the
disjointness of those pairs, at the later arm's pattern, and completeness
at `table`. -/
def noteMatch (cx : ExprCtx) (e : Syntax) (pats : Array Syntax) (taken : Array (Option Term)) (guarded : Array Bool)
    (unguardedExhaustive : Bool) (table? : Option (Array (Nat × Nat))) (defined : Array (Option Term)) :
    TermElabM Unit := do
  unless cx.noteIndexes do return
  let orF (cs : Array Term) : Term := cs.pop.foldr (fun c acc => Unhygienic.run `($c ∨ $acc)) cs.back!
  let andF (a b : Term) : Term := Unhygienic.run `($a ∧ $b)
  let notF (c : Term) : Term := Unhygienic.run `(¬$c)
  let trueF : Term := Unhygienic.run `(True)
  let complete := Core.completenessAsked unguardedExhaustive
  let goals := match table? with
    | some pairs => Core.tableMatchGoals orF andF notF trueF taken guarded defined pairs complete
    | none => Core.splitGoals .match orF andF notF trueF taken guarded complete
  for (g, f) in goals do
    let ref := match g with
      | .reachability _ j | .disjointness _ _ j => pats[j]!
      | _ => e[0]
    let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

/-- The alternatives of the or-pattern `p` at the top of an arm's pattern,
each its own Lean pattern, or `p` alone (`patHeads`). -/
partial def topPats (p : Core.Pat) : Array Core.Pat :=
  match p with
  | .or alts => alts.flatMap topPats
  | p => #[p]

/-- The pattern `q` of a value of type `ty`, built from `_`, binders and
variants (`matchForm`), as a pattern of Lean's `match`: each binder is
named by the next of `names`, in preorder. -/
partial def leanPattern (names : Array Name) (ty : Expr) (q : Core.Pat) : StateT Nat TermElabM Term := do
  match q with
  | .wild false => `(_)
  | .wild true =>
    let k ← get
    set (k + 1)
    let some n := names[k]? | throwError "internal error: a binder without a name"
    pure ⟨mkIdent n⟩
  | .ctor idx args =>
    let some info := (← getState).enumOf? ty
      | throwError "internal error: a variant's pattern of a value that is not of an enumeration"
    let tys := (info.payloadsAt ty.getAppArgs)[idx]!
    let ps ← (args.zip tys).mapM fun (a, t) => leanPattern names t a
    if ps.isEmpty then pure ⟨mkCIdent (info.ctor idx)⟩ else `($(mkCIdent (info.ctor idx)) $ps*)
  | _ => throwError "internal error: a pattern that is not Lean's"

/-- The arms of a Lean `match`, each an alternative of a pattern of `ty`
(`topPats`) with its right-hand side, but those that Lean would find
redundant after the earlier ones, with `_` and `default` last where those
are not exhaustive (`Reqs/Generated#matches`). -/
def leanMatchAlts (pty : Core.PatTy) (arms : Array (Array (Core.Pat × Term) × Term)) (default : Term) :
    TermElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  let sigs ← patSigs
  let mut rows : Array (List Core.Pat) := #[]
  let mut out := #[]
  for (alts, rhs) in arms do
    for (q, p) in alts do
      unless Core.useful sigs [pty] rows [q] do continue
      rows := rows.push [q]
      out := out.push (← `(Lean.Parser.Term.matchAltExpr| | $p:term => $rhs))
  if Core.useful sigs [pty] rows [.wild false] then
    out := out.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $default))
  return out

open Lang in
/-- The `match` `e` on `s`, of type `ty`, whose arms' patterns are `pats`, as
a Lean `match`, where `toTerm` translates its parts again, with each
binder the local that its pattern binds (`Reqs/Generated#matches`): an
arm with a guard is taken where its pattern matches and its guard holds,
and otherwise the arms after it are tried, as `rest k ()`, which tries the
arms from `k` on. `none` where its arms are propositions, which stay `if`s
(`matchForm`). Each arm's context, binders and expected type are
`armInfo`, as the `if`s' translation has them. -/
def leanMatchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (s : Term) (ty : Expr)
    (pty : Core.PatTy) (pats : Array Core.Pat) (armInfo : Array (ExprCtx × Array MatchBinder × Option Core.Ty))
    (vector? : Option (Array Expr × Array Term × Core.Sigs) := none) : TermElabM (Option Term) := do
  let arms := e[3].getSepArgs
  let mut bodies : Array Term := #[]
  let mut guards : Array (Option Term) := #[]
  let mut tys : Array (Option Expr) := #[]
  for arm in arms, (acx, new, exp) in armInfo do
    let decls := new.map fun b => (b.name, fun (_ : Array Expr) => pure b.type)
    let (g?, body, ty?) ← withLocalDeclsD decls fun _ => do
      let lcx : ExprCtx := { acx with binders := cx.binders ++ new.map fun (b : MatchBinder) => { b with term := ⟨mkIdent b.name⟩ } }
      let g? ← if arm[1].isNone then pure none
        else some <$> toTerm { lcx with natOk := false, emptyOk := false, expected? := none } arm[1][1]
      let body ← toTerm { lcx with expected? := exp } arm[3]
      let ty? ← try some <$> typeOf body catch _ => pure none
      return (g?, body, ty?)
    bodies := bodies.push body
    guards := guards.push g?
    tys := tys.push ty?
  let mut armKind : ArmKind := if tys.any (·.any (·.isProp)) then .propositions else .values
  if armKind == .propositions && cx.leanBoolArms then
    bodies ← (bodies.zip tys).mapM fun (b, t?) => if t?.any (·.isProp) then `(decide $b) else pure b
    tys := tys.map fun t? => if t?.any (·.isProp) then some (Lean.mkConst ``Bool) else t?
    armKind := .values
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  let heads := if vector?.isSome then pats.flatMap fun p => match p with
    | .ctor _ ps => ps.flatMap patHeads
    | _ => patHeads p
    else pats.flatMap patHeads
  unless matchForm scrutineeKind armKind heads == .leanMatch do return none
  -- An `Int` where another arm is a `Nat` (`widenMixed`).
  let mixed := tys.any (·.any (·.isConstOf ``Int)) && tys.any (·.any (·.isConstOf ``Nat))
  let widen (b : Term) (t? : Option Expr) : TermElabM Term :=
    if mixed && t?.any (·.isConstOf ``Nat) then `(($b : Int)) else pure b
  bodies ← (bodies.zip tys).mapM fun (b, t?) => widen b t?
  let default ← `(Fren.Seq.nth (∅ : Fren.Seq _) 0)
  let n := arms.size
  let rests ← (Array.range (n + 1)).mapM fun k => return mkIdent (← mkFreshUserName (Name.mkSimple s!"rest{k}"))
  let fallTo (k : Nat) : TermElabM Term := if k == n then pure default else `($(rests[k]!) ())
  let names := armInfo.map fun (_, new, _) => new.map (·.name)
  let altsOf (k : Nat) : TermElabM (Array (Core.Pat × Term)) :=
    (topPats pats[k]!).mapM fun q => return (q, ← (leanPattern names[k]! ty q).run' 0)
  -- The `match` of the arms from `start` on.
  let build (start : Nat) : TermElabM Term := do
    if let some (types, terms, signatures) := vector? then
      let mut rows : Array (List Core.Pat) := #[]
      let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for k in [start:n] do
        let rhs ← match guards[k]! with
          | some g => do let rest ← fallTo (k + 1); `(if $g then $(bodies[k]!) else $rest)
          | none => pure bodies[k]!
        for q in (pats[k]!.expand).1.map (·.1) do
          unless Core.useful signatures [pty] rows [q] do continue
          rows := rows.push [q]
          let columns ← match q with
            | .ctor _ ps => ((ps.zip types).mapM fun (p, t) => leanPattern names[k]! t p).run' 0
            | _ => types.mapM fun _ => `(_)
          alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $columns:term,* => $rhs))
      if Core.useful signatures [pty] rows [.wild false] then
        let wilds ← types.mapM fun _ => `(_)
        alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $wilds:term,* => $default))
      let discrs ← terms.mapM fun t => `(Lean.Parser.Term.matchDiscr| $t:term)
      return ← `(match $discrs:matchDiscr,* with $alts:matchAlt*)
    let mut out := #[]
    for k in [start:n] do
      let rhs ← match guards[k]! with
        | some g => do
          let r ← fallTo (k + 1)
          `(if $g then $(bodies[k]!) else $r)
        | none => pure bodies[k]!
      out := out.push (← altsOf k, rhs)
    let alts ← leanMatchAlts pty out default
    `(match $s:term with $alts:matchAlt*)
  -- Of the arms' type, so that a `match` of `Bool`s where a proposition is
  -- expected is coerced as a whole, rather than each arm, which would leave
  -- a `match` of propositions, with no `Decidable` instance.
  let t? := if mixed then some (Lean.mkConst ``Int) else tys.findSome? id
  let tStx? ← t?.mapM exprToSyntax
  let typed (m : Term) : TermElabM Term := match tStx? with
    | some t => `(($m : $t))
    | none => pure m
  let mut out ← typed (← build 0)
  let needed := (Array.range n).filterMap fun k => if guards[k]!.isSome && k + 1 < n then some (k + 1) else none
  unless needed.isEmpty do
    let some tStx := tStx? | throwError "internal error: no type for the arms of a `match`"
    for k in needed do
      out ← `(let $(rests[k]!) : Unit → $tStx := fun _ => $(← build k); $out)
  return some out

open Lang in
/-- Translates a `match` into a chain of `if`s that test its scrutinee
against each arm's pattern, where `toTerm` translates its parts: a variant
by comparing with the variant built from the value's own payload, a
literal by equality and a range by comparisons; binders read the payload
with the selectors. -/
def matchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (slot : Option Core.Slot) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  -- The scrutinee synthesizes its type, and each body is checked against the
  -- whole's, or another's (`lang::checked`).
  let original := e
  let many := isManyMatch e
  let scrutinees := matchScrutinees e
  let sourceArms := matchSourceArms e
  for arm in sourceArms do
    unless (matchPatterns e arm).size == scrutinees.size do
      throwErrorAt arm (Core.arityMsg `match scrutinees.size (matchPatterns e arm).size "pattern").text
  let terms ← scrutinees.mapM (toTerm { cx with emptyOk := Core.Position.synthesized.checked false false, natOk := false })
  let types ← terms.mapM typeOf
  let ptypes := types.map (patTyOf (← getState))
  for scr in scrutinees, pty in ptypes, ty in types do
    if pty == .other then throwErrorAt scr (Core.scrutineeMsg (← typeName ty)).text
  let scrutinee := scrutinees[0]!
  let origin? := scrutinees.findSome? cx.recOrigin?
  let arms := sourceArms.map (matchArm e)
  let mut resolved := #[]
  let mut rows := #[]
  for arm in sourceArms do
    let parts ← ((matchPatterns e arm).zipIdx).mapM fun (p, j) => do
      let (q, bs, test) ← resolveTop cx types[j]! terms[j]! false p
      return (q, bs.map fun b => { b with source? := some scrutinees[j]! }, test)
    rows := rows.push (parts.map (·.1))
    resolved := resolved.push (parts[0]!.1, parts.flatMap (·.2.1),
      Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) (parts.filterMap (·.2.2)))
  let baseSigs ← patSigs
  let (sigs, pty, pats) := if many then Core.matchVector baseSigs ptypes rows
    else (baseSigs, ptypes[0]!, rows.map (·[0]!))
  let s := terms[0]!
  let ty := types[0]!
  let e : Syntax := if many then (mkNode (if e.isOfKind ``Lang.tableMatchManyExpr then ``Lang.tableMatchExpr else ``Lang.matchExpr)
    #[e[0], scrutinee, mkAtom "{", Syntax.mkSep arms (mkAtom ","), mkAtom "}"]).raw else e
  let usesBefore := (← getLocal).recUses.size
  let guarded := arms.map (!·[1].isNone)
  let isTable := e.isOfKind ``Lang.tableMatchExpr
  -- In a table over a scrutinee, only the last arm may be `_` without a
  -- guard, the otherwise (`Reqs/Lang/Expressions#tables-over-a-scrutinee`).
  if isTable then
    if let some k := Core.rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g) then
      throwErrorAt arms[k]![0] Core.armAfterWildMsg.text
  let checked := if isTable then Core.checkTableArms sigs pty pats guarded
    else (Core.checkMatch sigs pty pats guarded).map (·, #[])
  let (unguardedExhaustive, pairs) ← match checked with
    | .ok u => pure u
    | .error (some (i, some j), msg) => throwErrorAt ((matchPatterns original sourceArms[i]!).flatMap topAlternatives)[j]! (if many then Core.vectorMsg msg else msg).text
    | .error (some (i, none), msg) => throwErrorAt arms[i]![0] (if many then Core.vectorMsg msg else msg).text
    | .error (none, msg) => throwError (if many then Core.vectorMsg msg else msg).text
  let p := if scrutinee.getNumArgs == 1 then scrutinee[0] else scrutinee
  let implicitArg := p.isOfKind ``Lang.fren_path && (pathSegs p).any (fun n => n.getId.toString.startsWith "#match")
  if cx.noteIndexes && !many && !implicitArg then lintMatch cx e ty pats slot
  -- In a defined function's Lean definition, a Lean `match`, where its
  -- patterns are Lean's (`Reqs/Generated#matches`).
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  let heads := if many then rows.flatMap (fun ps => ps.flatMap patHeads) else pats.flatMap patHeads
  let lean := cx.leanMatch && matchForm scrutineeKind .values heads == .leanMatch
  -- Each arm's context, binders and the type expected of its body.
  let mut armInfo : Array (ExprCtx × Array MatchBinder × Option Core.Ty) := #[]
  let mut bodies : Array Term := #[]
  -- Where each arm is taken, if no earlier one is: its test and its guard;
  -- `none` for an arm taken wherever it is tried.
  let mut taken : Array (Option Term) := #[]
  -- Of a table over a scrutinee, that the indexes in each arm's guard are
  -- in range where it evaluates them, if it has any.
  let mut defined : Array (Option Term) := #[]
  -- The type of the arms so far, once one has one.
  let mut armsTy? : Option Core.Ty := none
  -- The arms that wait for another's type: their index, context and body.
  let mut waiting : Array (Nat × ExprCtx × Syntax) := #[]
  -- An arm's guard is guarded by its pattern's matching where no earlier
  -- arm is taken (`Core.GuardedOperand.armGuard`), and its body by its
  -- being the first arm taken (`Core.GuardedOperand.armBody`). They are
  -- built directly: their negations are never needed, so `guard` would
  -- only return them.
  for arm in arms, (_, bs, t?) in resolved do
    let before := cx.guards ++ (← taken.filterMapM fun t? => t?.mapM fun t => `(¬$t))
    let armGuards := before ++ t?.toArray
    -- Distinct names (`lang::distinct_names`), by the names they declare,
    -- without the `!` of shadowing.
    let declared := bs.map fun b => (declaredIdent b.ident).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt bs[k]!.ident (Core.dupPatternBinderMsg declared[k]!).text
    let mut new : Array MatchBinder := #[]
    for b in bs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let y ← declare b.ident cx.modName locals
      let bn := y.getId
      liftMsg y (Core.checkVarName bn (some (b.type.isConstOf ``Bool || b.type.isProp)))
      lintName .binder bn y
      -- A payload of a parameter, or of a binder bound from one, is bound
      -- from a payload of that parameter; so is the whole of such a binder.
      let source := b.source?.getD scrutinee
      let payloadOf? := cx.recOrigin? source |>.bind fun (j, p) => if b.payload || p then some j else none
      new := new.push { name := bn, term := b.term, «type» := b.type, scrutinee := some source, outer := cx.binders.size, payloadOf? }
    let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
    -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
    let (g?, d?) ← if arm[1].isNone then pure (none, none) else if !isTable then do
      let g := arm[1][1]
      let c ← toTerm { gcx with natOk := false, emptyOk := false, expected? := none } g
      checkTermType g c .bool (some Core.armGuardNote)
      pure (some c, none)
    else do
      -- In a table over a scrutinee, translated under its pattern's test
      -- alone, so that its indexes say where it defines them, for its
      -- disjointness; then they, and the questions about its tables, are
      -- put under the earlier arms' not being taken, as a row's condition
      -- is.
      let g := arm[1][1]
      let (k, kt) := ((← getLocal).indexes.size, (← getLocal).tables.size)
      let c ← toTerm { gcx with natOk := false, emptyOk := false, expected? := none, guards := t?.toArray } g
      checkTermType g c .bool (some Core.armGuardNote)
      let l ← getLocal
      let inGuard := l.indexes.extract k
      let under (f : Term) : TermElabM Term := before.foldrM (fun g acc => `($g → $acc)) f
      let idx ← inGuard.mapM fun (r, f) => return (r, ← under f)
      let tbl ← (l.tables.extract kt).mapM fun (r, q, f) => return (r, q, ← under f)
      modifyLocal fun l => { l with indexes := l.indexes.extract 0 k ++ idx, tables := l.tables.extract 0 kt ++ tbl }
      pure (some c, Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) (inGuard.map (·.2)))
    defined := defined.push d?
    let own := t?.toArray ++ g?.toArray
    taken := taken.push (Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) own)
    let others := (arms.eraseIdx! bodies.size).map (·[3])
    let emptyOk := Core.Position.shared.checked cx.emptyOk (← anySynthesizes cx others)
    let acx := { gcx with guards := armGuards ++ g?.toArray, emptyOk }
    -- Each body is checked against the whole's type, or the arms' so far,
    -- as the `fren` command does: one that does not synthesize its own,
    -- before any has given one, waits for a later arm that does.
    let shared? := expected?.orElse fun _ => armsTy?.map (·.widen)
    armInfo := armInfo.push (acx, new, shared?)
    if shared?.isNone && !(← synthesizes cx arm[3]) && (← arms.anyM (synthesizes cx ·[3])) then
      waiting := waiting.push (bodies.size, acx, arm[3])
      bodies := bodies.push (← `(sorry))
      continue
    let body ← toTerm { acx with expected? := shared? } arm[3]
    armsTy? ← armType cx armsTy? arm[3] body shared?
    bodies := bodies.push body
  for (k, acx, b) in waiting do
    armInfo := armInfo.modify k fun (c, n, _) => (c, n, armsTy?.map (·.widen))
    let body ← toTerm { acx with expected? := armsTy?.map (·.widen) } b
    if armsTy?.isSome then armsTy? ← armType cx armsTy? b body (armsTy?.map (·.widen))
    bodies := bodies.set! k body
  noteMatch cx e (arms.map (·[0])) taken guarded unguardedExhaustive (if isTable then some pairs else none) defined
  -- A recursive application under a `match` on an enumeration's parameter
  -- or payload that is not a Lean `match` (`lang::recursive_match`).
  if origin?.isSome && pty matches .enum .. then
    let nonLean? := if many then (rows.zipIdx.find? fun (ps, j) => ps.any (!·.leanPattern) || guarded[j]!).map (·.2)
      else Core.firstNonLeanPattern? pats guarded
    if let some k := nonLean? then
      if (← getLocal).recUses.size > usesBefore then
        modifyLocal fun l => { l with recMatches := l.recMatches.push arms[k]![0] }
  let widened ← widenMixed bodies
  if lean then
    if let some m ← leanMatchTerm toTerm cx e s ty pty pats armInfo (if many then some (types, terms, sigs) else none) then return m
  -- The first arm that is taken. Where the arms without guards are
  -- exhaustive, the last arm has none, and takes whatever is left;
  -- otherwise, where none is taken, the `match` is the index out of range
  -- of the empty sequence, as a table where no row holds is.
  let complete := !Core.completenessAsked unguardedExhaustive
  let mut out ← if complete then pure widened.back! else `(Fren.Seq.nth (∅ : Fren.Seq _) 0)
  for i in (List.range (if complete then bodies.size - 1 else bodies.size)).reverse do
    out ← match taken[i]! with
      | some t => `(if $t then $(widened[i]!) else $out)
      | none => pure widened[i]!
  return out

open Lang in
/-- Translates `e is P`, which is `match e { P => true, _ => false }`, into
the test of `P` (`Reqs/Lang/Expressions#pattern-tests`). -/
def isTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let scrutinee := e[0]
  let s ← toTerm cx scrutinee
  let ty ← typeOf s
  let pty := patTyOf (← getState) ty
  if pty == .other then throwErrorAt scrutinee (Core.isScrutineeMsg (← typeName ty)).text
  -- Whether the names that it binds are in scope anywhere (`lang::test_scope`):
  -- then its or-patterns bind none, as a `match` arm's do.
  let (k, n) := cx.testAt?.getD (0, 1)
  let binds := Core.testBinds cx.testContext k n
  let (q, bs, test) ← resolveTop cx ty s (!binds) e[2]
  match Core.checkPatternTest (← patSigs) pty q (bs.map (·.ident.getId)) binds cx.testContext with
  | .ok () => pure ()
  | .error (.binder k, msg) => throwErrorAt bs[k]!.ident msg.text
  | .error (.alternative j, msg) => throwErrorAt (topAlternatives e[2])[j]! msg.text
  | .error (.whole, msg) => throwErrorAt e[2] msg.text
  if cx.noteIndexes && !bs.isEmpty then
    modifyLocal fun l => { l with bindingTests := l.bindingTests.push (e.getPos?, e.getTailPos?) }
  if binds && !bs.isEmpty then
    -- Declared as a `match` arm's binders are, for the later operands of the
    -- chain and the body that sees them.
    let declared := bs.map fun b => (declaredIdent b.ident).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt bs[k]!.ident (Core.dupPatternBinderMsg declared[k]!).text
    let mut new := #[]
    for b in bs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let y ← declare b.ident cx.modName locals
      let bn := y.getId
      liftMsg y (Core.checkVarName bn (some (b.type.isConstOf ``Bool || b.type.isProp)))
      if cx.noteIndexes then lintName .binder bn y
      -- With its type, so that where a `Prop` is expected, as in the body
      -- of `when`, the selector's type parameters are those of the
      -- scrutinee's type, not inferred from there.
      let term ← `(($(b.term) : $(← exprToSyntax b.type)))
      new := new.push (bn, term.raw, b.type, scrutinee, cx.binders.size)
    modifyLocal fun l => { l with bound := l.bound ++ new }
  if cx.noteIndexes then
    -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`):
    -- not of a test that binds names, which it is needed for.
    let irrefutable := bs.isEmpty && Core.irrefutableIs (Core.matchesEvery (← patSigs) pty q)
    if irrefutable then recordLint .irrefutableIs e (Core.irrefutableIsMsg (← patTypeName ty) (q matches .wild _))
    lintOrPatterns (orNode (topAlts e[2]).1 q)
    let texts := (topAlts e[2]).1.map exactText
    if Core.isEquality texts.size (Core.equatable q texts) irrefutable then
      let msg := Core.isEqualityMsg { text := exactText scrutinee, prec := exprPrec scrutinee } texts[0]!
      recordLint .isEquality e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  -- In a defined function's Lean definition, a test that binds nothing is a
  -- Lean `match` where its pattern is Lean's (`Reqs/Generated#matches`).
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  if cx.leanMatch && bs.isEmpty && matchForm scrutineeKind .values (patHeads q) == .leanMatch then
    let alts ← (topPats q).mapM fun a => return (a, ← (leanPattern #[] ty a).run' 0)
    let ms ← leanMatchAlts pty #[(alts, ← `(true))] (← `(false))
    return ← `(((match $s:term with $ms:matchAlt*) : Bool) = true)
  match test with
  | some t => return t
  | none => `(true)

/-- Whether `e` is a `when`, an `unless` or a quantifier, whose body
extends as far right as possible. -/
def isConditional (e : Syntax) : Bool :=
  e.isOfKind ``Lang.quantExpr ||
    (e.getNumArgs == 4 && e[0].isAtom && ["when", "unless"].contains e[0].getAtomVal.trimAscii.toString)

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
  -- `x is P`, of the variants that `P` names, each with only `_` in its
  -- payload, so that it tests the variant alone.
  if e.isOfKind ``Lang.isExpr then
    let st ← getState
    let mut out : Array (Nat × String) := #[]
    let mut en? : Option Name := none
    for p in (topAlts e[2]).1 do
      unless p.isOfKind ``Lang.variantPattern do return none
      unless (patternArgs p).all fun a => a[0].getSepArgs.size == 1 && a[0].getSepArgs[0]!.isOfKind ``Lang.wildPattern do
        return none
      let .ok (.variant en i) := st.table.resolvePath cx.modName ((pathSegs p[0]).map (·.getId)) cx.shadowing
        | return none
      unless en?.all (· == en.path) do return none
      en? := some en.path
      out := out.push (i, exactText p)
    let some en := en? | return none
    return some { scrutinee := srcText (unparen e[0]), enum := en, variants := out }
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

/-- The text of `e` as a row's condition or value in a table. -/
def rowPartOf (e : Syntax) : String :=
  let e := unparen e
  Core.rowPart (srcText e) (isConditional e || e.isOfKind ``Lang.letExpr)

/-- `if_chain_match` and `manual_table` on the chain of `if` that starts at
`e` (`lint::if_chain_match`, `lint::manual_table`). -/
def lintIfChain (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  let (cs, as, z) := ifChain e
  -- A table's row does not see what its condition's pattern tests bind
  -- (`lang::test_scope`).
  if ← cs.anyM (chainBinds cx) then return
  let ts? := Core.sameScrutinee (← cs.mapM (variantTest? cx))
  let ts := ts?.getD #[]
  let enums := (← getState).enums
  let n := ((ts[0]?.bind fun t => enums.get? t.enum).map (·.variants.size)).getD 0
  let (fires, wildcard) := Core.ifChainMatch cs.size ts?.isSome (Core.repeatedVariants ts) (Core.untestedVariants n ts)
  -- `manual_table` (`lint::manual_table`).
  if Core.manualTable cs.size ts?.isSome then
    recordLint .manualTable e (Core.manualTableMsg (cs.map rowPartOf) (as.map rowPartOf) (rowPartOf z))
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
whether it reads `card`. A field read of a dotted name, as in `(r).s.len`,
reads each of its components in turn, so its receiver is the read of all
but the last, `(r).s`. -/
def lengthOf? (a : Syntax) : TermElabM (Option (Syntax × Bool)) := do
  let a := (splitDotted? a).getD a
  if a.isOfKind ``Lang.fieldExpr then
    let .str pre m := a[2].getId | return none
    unless m == "len" || m == "card" do return none
    let recv := if pre.isAnonymous then a[0] else a.setArg 2 (mkIdentFrom a[2] pre)
    return some (recv, m == "card")
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

/-- `e` without parentheses, as an operand: its text and precedence. -/
def bareText (e : Syntax) : Core.BText := { text := srcText (unparen e), prec := exprPrec (unparen e) }

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
  recordLint (if card then .cardZero else .lengthZero) e (Core.lengthZeroMsg card (bareText recv) emptyText empty d)

/-- `eq_op` on `e`, if it is an infix operator (`lint::eq_op`), or `when` or
`unless` (`lint::eq_op_conditional`). The body of `when`, and the right
operand of `and`, see the names that the other's pattern tests bind, which
the other does not (`lang::test_scope`). -/
def lintEqOp (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  -- Generated Boolean lowering has no written operands to compare.
  if (exactText e).isEmpty then return
  if isConditional e then
    unless e[0].getHeadInfo matches .original .. do return
    let negated := e[0].getAtomVal.trimAscii.toString == "unless"
    let c := exactText (unparen e[1])
    let seen ← if negated then pure [] else chainBinders cx e[1]
    if let some v := Core.eqOpConditional negated (Core.writtenSameIn c (exactText (unparen e[3])) [] seen) then
      recordLint .eqOp e (Core.eqOpConditionalMsg negated v c)
    return
  unless e.getNumArgs == 3 && e[1].isAtom do return
  -- The lowering may retain written member spans on synthetic parents.
  -- Only a written operator has operands that the user wrote together.
  unless e[1].getHeadInfo matches .original .. do return
  let some op := Core.InfixOp.ofOp? e[1].getAtomVal.trimAscii.toString | return
  let a := exactText (unparen e[0])
  if a.isEmpty || (exactText (unparen e[2])).isEmpty then return
  let seen ← if op matches .and then chainBinders cx e[0] else pure []
  if let some v := Core.eqOp op (Core.writtenSameIn a (exactText (unparen e[2])) [] seen) then
    recordLint .eqOp e (Core.eqOpMsg op v a)

/-- `same_branches` on `e`, `if c then a else b`, where `binds` is whether
`c`'s pattern tests bind names (`lint::same_branches`). -/
def lintSameBranches (binds : Bool) (e a b : Syntax) : TermElabM Unit := do
  let (a, b) := (unparen a, unparen b)
  if (exactText a).isEmpty || (exactText b).isEmpty then return
  unless Core.sameBranches binds (Core.writtenSame (exactText a) (exactText b)) do return
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
  if e.isOfKind ``Lang.fieldExpr then return some (e[0], (fieldName e[2]).toString)
  let p := if e.getNumArgs == 1 then e[0] else e
  unless p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 do return none
  let .str pre m := (pathSegs p)[0]!.getId | return none
  if pre.isAnonymous then return none
  return some (← pathExpr e pre, m)

open Lang in
/-- `manual_record_update` on the record literal `e` of the record `path`
(`lint::manual_record_update`). -/
def lintManualUpdate (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (path : Name) :
    TermElabM Unit := do
  unless cx.noteIndexes do return
  let given := e[2].getSepArgs
  let some info := (← getState).records.get? path | return
  -- The fields that read their own field from a value of this record, by the
  -- value's text.
  let mut copies : Array (String × Syntax × Array Nat) := #[]
  for h : i in [0:given.size] do
    let b := given[i]
    if b[1].isNone then continue
    let some (recv, n) ← lastName? b[1][1] | continue
    unless n == b[0].getId.toString do continue
    -- Only its type: what elaborating it reports is reported where it is.
    let saved ← getLocal
    let t? ← try some <$> typeOf (← toTerm { cx with noteIndexes := false } recv) catch _ => pure none
    modifyLocal fun _ => saved
    let some t := t? | continue
    unless (t.constName?.bind (← getState).recordOfDecl?).any (·.path == path) do continue
    let w := Core.writtenForm (exactText recv)
    match copies.findIdx? (·.1 == w) with
    | some k => copies := copies.modify k fun (w, r, ks) => (w, r, ks.push i)
    | none => copies := copies.push (w, recv, #[i])
  -- The value with the most copies, the first of those with as many.
  let best? := copies.foldl (init := none) fun acc c =>
    if acc.all (·.2.2.size < c.2.2.size) then some c else acc
  let some (_, recv, ks) := best? | return
  unless Core.manualRecordUpdate info.fields.size ks.size do return
  let kept := ((Array.range given.size).filter (!ks.contains ·)).map (exactText given[·]!)
  recordLint .manualRecordUpdate e (Core.manualRecordUpdateMsg (exactText recv) ks.size kept)

open Lang in
/-- `needless_update` and `redundant_bindings` on the record update `e`
(`lint::needless_update`, `lint::redundant_bindings`, `lint::field_copy`). -/
def lintUpdate (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let saved ← getLocal
  let t? ← try some <$> typeOf (← toTerm { cx with noteIndexes := false } e[1]) catch _ => pure none
  modifyLocal fun _ => saved
  let some info := t?.bind (·.constName?) |>.bind (← getState).recordOfDecl? | return
  let given := e[3].getSepArgs
  if Core.needlessUpdate info.fields.size given.size then
    recordLint .needlessUpdate e (Core.needlessUpdateMsg (Core.showPath info.path) (exactText e[1]))
  let baseText := Core.writtenForm (exactText e[1])
  let value (b : Syntax) : String := if b[1].isNone then "" else Core.writtenForm (exactText b[1][1])
  let others := given.any fun b => !Core.fieldCopy b[0].getId.toString (value b) baseText true
  for b in given do
    lintRedundant b true
    unless b[1].isNone do
      if Core.fieldCopy b[0].getId.toString (value b) baseText others then
        recordLint .redundantBindings b (Core.fieldCopyMsg b[0].getId.toString (exactText e[1]))

/-- The names that `e` reads one after another, innermost first, each with
its receiver. -/
partial def namesRead (e : Syntax) : TermElabM (Array (Syntax × String)) := do
  match ← lastName? e with
  | some (r, n) => return (← namesRead (unparen r)).push (r, n)
  | none => return #[]

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
  -- `literal_dot_in_pattern` (`lint::literal_dot_in_pattern`).
  if let some (fixed, found) := Core.literalDotsPattern? lit then
    let msg := Core.literalDotMsg found (Core.patternLiteral (srcText p) fixed)
    recordLint .literalDotInPattern p (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  let some (fix, s) := Core.trivialPattern? lit | return
  let fixed := (Core.trivialPatternText (bareText recv) (srcText recv) fix s).inSlot (parent?.bind (operandSlot · e))
  recordLint .trivialPattern e (Core.trivialPatternMsg fix fixed)

/-- What the first of the operands `xs` of an ordering is expected to be,
as the `fren` command's `orderingExpected?`: if it does not synthesize its
type, the type, widened, of the first that does, translated without
effect; otherwise nothing, as each later operand is expected to be of the
first's type (`lang::checked`). -/
def orderingExpected? (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (xs : Array Syntax) :
    TermElabM (Option Core.Ty) := do
  if ← synthesizes cx xs[0]! then return none
  let some m ← xs.findM? (synthesizes cx) | return none
  let s ← saveState
  let t? ← frenTypeOf? (← toTerm { cx with noteIndexes := false } m)
  s.restore
  return t?.map (·.widen)

open Lang in
/-- An operand of `=` or `!=`, as `lang::function_comparison` sees it: a
closure, the name of a function or of a function parameter, or a value. -/
def comparand (cx : ExprCtx) (e : Syntax) : TermElabM Core.Comparand := do
  let e := unparen e
  if e.isOfKind ``Lang.closureExpr || e.isOfKind ``Lang.lambdaMatchExpr then return .closure
  let p := if e.getNumArgs == 1 && e[0].isOfKind ``Lang.fren_path then e[0] else e
  unless p.isOfKind ``Lang.fren_path do return .value
  let segs := pathSegs p
  if segs.size == 1 then
    let n := segs[0]!.getId
    if (cx.fnParam? n).isSome then return .functionName
    if (cx.binder? n.getRoot).isSome || cx.vars.any (·.name.isPrefixOf n) then return .value
  match (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing with
  | .ok (.item { kind := .fnItem, .. }) => return .functionName
  | _ => return .value

open Lang in
/-- `a = b`, `a != b` and the orderings; on strings, checks the decidable
core, and writes the orderings with `Fren.Str.lt` and `Fren.Str.le`, and
`a > b` as `b < a`, since lean-smt writes `>` on strings as `str.>`,
which is not SMT-LIB. -/
def compareTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let (a, b) := (e[0], e[2])
  let op := e[1].getAtomVal.trimAscii.toString
  let string (t : Term) : TermElabM Bool := return (← typeOf t).isConstOf ``String
  -- Functions are not compared (`lang::function_comparison`).
  if op == "=" || op == "!=" then
    unless Core.comparisonAccepted [← comparand cx a, ← comparand cx b] do throwError (Core.functionComparisonMsg op).text
  lintLength toTerm cx e
  let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
  if op == "=" || op == "!=" then
    -- `++` is in the core against a constant.
    let (x, y) ← pairTerms toTerm { cx with concatOk := cb, emptyOk := Core.Position.compared.checked false (← synthesizes cx b) }
      { cx with concatOk := ca, emptyOk := Core.Position.compared.checked false (← synthesizes cx a) } a b
    -- Both sides have one type, after widening, as the `fren` command checks
    -- (`lang::operator_type`).
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then
      liftMsg e (Core.checkComparable op tx ty)
      -- For `manual_pattern_test`, at the end of the expression.
      if cx.noteIndexes && (tx == .nat || ty == .nat) then
        modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .natOperands) }
    -- After the sides and their types, as in the binary: not where either
    -- is an error.
    lintEmptyEquation cx e
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
  -- An ordering compares values of an ordered type, which the left operand
  -- gives: `Int`s, `Nat`s, `String`s, or the values of an ordered
  -- enumeration, record or newtype, as the `fren` command checks
  -- (`lang::operator_type`, `lang::ordered_type`, `lang::newtype_operator`).
  -- The right is expected to have the left's type, and the left the
  -- right's, if only the right synthesizes one (`lang::checked`).
  let x ← toTerm { cx with expected? := ← orderingExpected? toTerm cx #[a, b] } a
  let tx? ← frenTypeOf? x
  let st ← getState
  let info? := st.enumOf? (← typeOf x)
  let operandTy : Core.Ty ← match tx? with
    | some tx => liftMsg a (Core.orderingType op tx st.orderedDecl)
    | none => pure .int
  let y ← toTerm { cx with expected? := some operandTy } b
  checkNewtypeOp op tx? (← frenTypeOf? y)
  checkTermType b y operandTy (Core.opNote op operandTy)
  -- For the lints of integers, at the end of the expression: what it compares.
  if cx.noteIndexes && !(tx? matches some (.newtype ..)) then
    let compared : Core.Ordered := if operandTy matches .enum .. && info?.any (·.ordered) then .enumeration
      else if operandTy == .int || operandTy == .nat then .number else .other
    modifyLocal fun l => { l with ordereds := l.ordereds.push ((e.getPos?, e.getTailPos?), compared) }
  -- An ordered record's values compare by their fields, and a newtype's as
  -- their fields do (`Reqs/Lang/Items#ordered-declarations`).
  if operandTy matches .record .. | .newtype .. then
    let some plan := st.orderPlan? operandTy | throwError "internal error: `{operandTy.show}` is not ordered"
    if plan.strings then checkCore cx e .stringCompare true (ca || cb) #[a, b] (ca && cb)
    return ← orderingTerm plan op x y
  -- An ordered enumeration's values compare by their positions.
  if let (.enum .., some info) := (operandTy, info?) then
    let (i, j) := (← ordinalTerm info x, ← ordinalTerm info y)
    return ← match op with
      | "<" => `($i < $j) | "<=" => `($i ≤ $j) | ">" => `($i > $j) | _ => `($i ≥ $j)
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
  let mut x ← toTerm { cx with expected? := ← orderingExpected? toTerm cx xs } xs[0]!
  -- A value of an ordered type, a `Nat` widened, and every operand the
  -- first's type, which each is expected to have (`lang::checked`), as the
  -- `fren` command checks (`lang::operator_type`, `lang::ordered_type`,
  -- `lang::newtype_operator`).
  let tx0? ← frenTypeOf? x
  let st ← getState
  let info? := st.enumOf? (← typeOf x)
  let t0? ← match tx0? with
    | some t => some <$> liftMsg xs[0]! (Core.orderingType names[0]! t st.orderedDecl)
    | none => pure none
  let string := t0? == some .string
  -- An ordered enumeration's values compare by their positions, and an
  -- ordered record's or newtype's by their fields.
  let plan? := match t0? with
    | some t@(.record ..) | some t@(.newtype ..) => st.orderPlan? t
    | _ => none
  let ordinal := if t0? matches some (.enum ..) then info? else none
  let pos (t : Term) : TermElabM Term := match ordinal with | some info => ordinalTerm info t | none => pure t
  let mut links := #[]
  for op in names, a in xs, b in xs.extract 1, opStx in ops do
    let y ← toTerm { cx with guards := cx.guards ++ links, expected? := t0? } b
    -- A node's position is its first token's, and its tail its last's, so
    -- this one spans the comparison, from `a` to `b`, for its messages.
    let link := mkNullNode #[a, opStx, b]
    withRef link (checkNewtypeOp op t0? (← frenTypeOf? y))
    if let some t0 := t0? then checkTermType b y t0 (Core.opNote op t0)
    if string || plan?.any (·.strings) then
      let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
      checkCore cx link .stringCompare true (ca || cb) #[a, b] (ca && cb)
    if let some plan := plan? then
      links := links.push (← withRef link (orderingTerm plan op x y))
      x := y
      continue
    -- On strings, as `compareTerm` writes them.
    let (i, j) := (← pos x, ← pos y)
    links := links.push (← withRef link <| match op, string with
      | "<", false => `($i < $j) | "<=", false => `($i ≤ $j)
      | ">", false => `($i > $j) | ">=", false => `($i ≥ $j)
      | "<", true => `(Fren.Str.lt $x $y) | "<=", true => `(Fren.Str.le $x $y)
      | ">", true => `(Fren.Str.lt $y $x) | _, _ => `(Fren.Str.le $y $x))
    x := y
  links.extract 1 |>.foldlM (fun acc l => `($acc ∧ $l)) links[0]!

/-- Whether `e` is `[]`, which takes its type from where it is written. -/
def isEmptySeq (e : Syntax) : Bool := e.isOfKind ``Lang.seqExpr && e[1].getSepArgs.isEmpty

/-- `a ++ b`, where `concatOk` says whether the core allows it here. -/
def concatTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (concatOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  let (a, b) := (e[0], e[2])
  -- Each operand is checked against the whole's type, or the other's
  -- (`lang::checked`), as in the `fren` command: `[] ++ q` takes its type
  -- from `q`, translated first without recording anything.
  let expected? ← if expected?.isNone && !(← synthesizes cx a) && (← synthesizes cx b) then
      let s ← saveState
      let t? ← frenTypeOf? (← toTerm { cx with noteIndexes := false } b)
      s.restore
      pure t?
    else pure expected?
  let x ← toTerm { cx with concatOk := true, emptyOk := Core.Position.shared.checked cx.emptyOk (← synthesizes cx b), expected? } a
  unless (← getState).newtypes.isEmpty || !(← synthesizes cx a) do
    let tx? ← frenTypeOf? x
    checkNewtypeOp "++" tx? tx?
  -- Sequences: outside the core, unless constant.
  if (← typeOf x).isAppOfArity ``Fren.Seq 1 then
    let y ← toTerm { cx with emptyOk := Core.Position.shared.checked cx.emptyOk (← synthesizes cx a), expected? := ← frenTypeOf? x } b
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
  -- An enumeration's or record's `min` and `max` take the receiver's type,
  -- so a variant of a generic type takes its type arguments, as in the
  -- `fren` command.
  let ordered? ← if m == "min" || m == "max" then
      pure ((← frenTypeOf? r).filter (· matches .enum .. | .record ..)) else pure none
  let as ← args.mapM fun a => do
    let acx := { cx with emptyOk := position.checked false false, natOk := natArg }
    let acx := match ordered? with | some t => { acx with expected? := some t } | none => acx
    return (← if pattern then patternTerm a else toTerm acx a, a)
  if seq then
    let c := (Core.Method.ofName? m).map (·.seqConstruct) |>.getD .seqWord
    checkCore cx e c true true (#[recvStx] ++ args) ((← args.allM (isConstant cx ·)) && (← isConstant cx recvStx))
      (literalOperand := args.any fun a => (unparen a).isOfKind ``Lang.seqExpr)
  if rty.isConstOf ``String then
    let constantArgs ← args.allM (isConstant cx ·)
    let recvConstant ← isConstant cx recvStx
    let c := (Core.Method.ofName? m).map (·.construct) |>.getD .stringAtom
    -- `min` and `max` compare their strings, as `<=` does.
    let comparable := !(m == "min" || m == "max") || constantArgs || recvConstant
    checkCore cx e c constantArgs comparable (#[recvStx] ++ args) (constantArgs && recvConstant)
  let t := (← callMethod ref r rty m as).1
  -- `min` and `max` of an ordered record or newtype with a `String` within
  -- compare strings (`Reqs/Lang/Decidability#orderings`).
  if m == "min" || m == "max" then
    let ct? := (← frenTypeOf? r).filter (· matches .record .. | .newtype ..)
    if let some ct := ct? then
      if (((← getState).orderPlan? ct).map (·.strings)).getD false then
        let (ca, cb) := (← isConstant cx recvStx, ← args.allM (isConstant cx ·))
        checkCore cx e .stringCompare true (ca || cb) (#[recvStx] ++ args) (ca && cb)
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

open Lang in
/-- Checks that the members `xs` of a set literal (or, if `seq`, the
elements of a sequence literal), written `elems`, have the first's type, if
a newtype is one of them, with the `fren` command's message: Lean's reports
other mismatches. -/
def checkNewtypeMembers (cx : ExprCtx) (seq : Bool) (elems : Array Syntax) (xs : Array Term) : TermElabM Unit := do
  let s ← getState
  if s.newtypes.isEmpty then return
  let typed ← (elems.zip xs).filterMapM fun (e, x) => do
    if !(← synthesizes cx e) || e.isOfKind ``Lang.pairExpr then return none
    return some (e, ← typeOf x)
  let some (_, t0) := typed[0]? | return
  unless typed.any fun (_, t) => (s.newtypeOf? t).isSome do return
  for (e, t) in typed do
    unless ← isDefEq t t0 do
      let name ← typeName t0
      let lit := if seq then s!"Seq<{name}>" else s!"Set<{name}>"
      throwErrorAt e (Core.membersMsg seq (← typeName t0) (← typeName t) lit).text

/-- `t`, a `Bool` if it is a condition, a `Prop`: a member of a set is a
value, and a `Bool` in Fren, as `true` is. -/
def boolTerm (t : Term) : TermElabM Term := do
  if (← typeOf t).isProp then `(if $t then true else false) else pure t

/-- Freeze a Boolean value's type before embedding it in a proposition.
In particular, polymorphic sequence indexing must keep its element Bool. -/
def propositionTerm (t : Term) : TermElabM Term := do
  if (← typeOf t).isConstOf ``Bool then `(($t : Bool) = true) else pure t

/-- `{a, b}`, or `{}` where `emptyOk` says that something gives it a type. -/
def setLitTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  let elems := e[1].getSepArgs
  if elems.isEmpty then
    unless emptyOk do throwErrorAt e Core.emptySetTypeMsg.text
    if expected?.isSome then discard (liftMsg e (Core.checkEmptyLiteral false expected?))
    return ← `((∅ : Fren.FinSet _))
  checkCore cx e .setAlgebra true true elems
  if cx.noteIndexes then lintDuplicates e elems
  let synth ← elems.mapM (synthesizes cx)
  -- A member, given the type of the literal expected of it, as the `fren`
  -- command's `member`: a pair's members expect a relation's types. A member
  -- is never a `Nat` (`lang::nat_place`).
  let member (k : Nat) (lit? : Option Core.Ty) (noteIndexes := cx.noteIndexes) : TermElabM Term := do
    let x := elems[k]!
    let mcx := { cx with noteIndexes, emptyOk := Core.Position.shared.checked emptyOk ((synth.eraseIdx! k).any id) }
    if x.isOfKind ``Lang.pairExpr then
      let (ea?, eb?) := match lit? with | some (.rel a b) => (some a, some b) | _ => (none, none)
      let (a, b) := (← widenTerm (← toTerm { mcx with expected? := ea? } x[1]), ← widenTerm (← toTerm { mcx with expected? := eb? } x[3]))
      return ← `((($a, $b) : $(typeSyntax (← typeOf a)) × $(typeSyntax (← typeOf b))))
    boolTerm (← widenTerm (← toTerm { mcx with expected? := lit?.bind fun | .set t => some t | _ => none } x))
  -- The type of the literal a member makes: a pair makes a relation.
  let litTy (k : Nat) (x : Term) : TermElabM (Option Core.Ty) := do
    if elems[k]!.isOfKind ``Lang.pairExpr then
      let t ← instantiateMVars (← typeOf x)
      unless t.isAppOfArity ``Prod 2 do return none
      let (some a, some b) := (← coreTy? t.appFn!.appArg!, ← coreTy? t.appArg!) | return none
      return some (.rel a.widen b.widen)
    return (← frenTypeOf? x).map (.set ·.widen)
  -- Each member is checked against the literal's type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  let lit? ← if expected?.isNone && !synth[0]! then
      match synth.findIdx? id with
      | some k => do
        let s ← saveState
        let t? ← litTy k (← member k none (noteIndexes := false))
        s.restore
        pure t?
      | none => pure none
    else pure expected?
  let x0 ← member 0 lit?
  let t0? := (← litTy 0 x0).orElse fun _ => if synth[0]! then none else lit?
  let mut xs := #[x0]
  for k in [1:elems.size] do
    let x ← member k t0?
    if let (some t, some t0) := (← litTy k x, t0?) then
      unless t == t0 do
        let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
        throwErrorAt elems[k]! (Core.membersMsg false mt0 mt t0.show).text
    xs := xs.push x
  checkNewtypeMembers cx false elems xs
  `(($(← finSetLit xs) : Fren.FinSet _))

/-- `x in s`, `s subset t`, `s union t`, `s inter t` and `s minus t`. -/
def setOpTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  let (a, b) := (e[0], e[2])
  checkCore cx e .setAlgebra true true #[a, b]
  if e.isOfKind ``Lang.memberExpr then
    if (unparen b).isOfKind ``Lang.setExpr && cx.noteIndexes then
      if let #[m] := (unparen b)[1].getSepArgs then
        unless m.isOfKind ``Lang.pairExpr do recordLint .singletonMembership e (Core.singletonMembershipMsg (srcText a) (srcText m))
    -- The left synthesizes a type, which the right is checked against (`lang::checked`).
    let x ← widenTerm (← pairOrTerm toTerm { cx with emptyOk := Core.Position.synthesized.checked false false } a)
    -- The right expects a set or sequence of the left's type, as it is
    -- written, or a relation of a pair's, as in the `fren` command.
    let tx ← instantiateMVars (← typeOf x)
    let elem? ← if a.isOfKind ``Lang.pairExpr && tx.isAppOfArity ``Prod 2 then do
        let (some p, some q) := (← coreTy? tx.appFn!.appArg!, ← coreTy? tx.appArg!) | pure none
        pure (some (Core.Ty.rel p.widen q.widen))
      else pure ((← coreTy? tx).map fun t => if seqShaped b then .seq t.widen else .set t.widen)
    let s ← toTerm { cx with emptyOk := Core.Position.compared.checked false (← synthesizes cx a), expected? := elem? } b
    let (tx, ts) := (← typeOf x, ← typeOf s)
    -- `ts` is taken apart only once it is known to be a `Seq`: a `(← ...)`
    -- after `&&` would run, and panic, for any other type.
    let isSeq ← if ts.isAppOfArity ``Fren.Seq 1 then isDefEq ts.appArg! tx else pure false
    -- The membership of a quantifier over elements' guard: its report
    -- waits for the quantifier's verdict (`quantTerm`).
    if cx.elemGuards.contains (elemKey b) then
      let infinite ← #[a, b].anyM (mentionsInfiniteOutput cx)
      let ground ← isConstant cx e
      let report := if !isSeq || cx.unmentioned || Core.inCore .seqWord true true infinite ground
          (literalOperand := (unparen b).isOfKind ``Lang.seqExpr) then none
        else some (e, Core.undecidableMsg .seqWord infinite)
      modifyLocal fun l => { l with elemMembers := l.elemMembers.push (elemKey b, isSeq, report) }
      if isSeq then return ← `($x ∈ $s)
    if isSeq then
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
  let cxa := { cx with emptyOk := position.checked cx.emptyOk (← synthesizes cx b) }
  let cxb := { cx with emptyOk := position.checked cx.emptyOk (← synthesizes cx a) }
  let (x, y) ← if e.isOfKind ``Lang.joinExpr then pure (← toTerm cxa a, ← toTerm cxb b)
    else
      -- The whole's expected type is not the operands' for `subset`.
      let expected? := if e.isOfKind ``Lang.subsetExpr then none else expected?
      pairTerms toTerm { cxa with expected? } { cxb with expected? } a b
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
    (op : Join := .implies) (test : Core.TestContext × Option (Nat × Nat) := (.standalone, none)) : TermElabM Term := do
  let e ← getRef
  let j := match op with | .or => "or" | .and => "and" | .implies => ""
  -- `membership_chain`, at the top of a chain of `or` or of `and` (`lint::membership_chain`).
  if !j.isEmpty && cx.chain != j && cx.noteIndexes then
    let ds := chainOperands j e
    let cmp := if op matches .and then "!=" else "="
    let eqs := ds.filterMap fun d => let d := unparen d; if isBinOp d cmp then some (d[0], d[2]) else none
    let lefts := eqs.map (srcText ·.1)
    let laterIndexes := (eqs.extract 1).any fun (_, v) => !(indexedIn v).isEmpty
    let patterns ← eqs.allM fun (_, v) => return Core.patternValue (srcText (unparen v)) (← variantOf? cx v).isSome
    if Core.membershipChainFires ds.size (eqs.size == ds.size && lefts.all (· == lefts[0]!)) laterIndexes patterns then
      recordLint .membershipChain e (Core.membershipChainMsg lefts[0]! (eqs.map (srcText ·.2)) (op matches .and))
  -- `index_after_use` (`lint::index_after_use`).
  if op matches .and && cx.noteIndexes && !(← chainBinds cx c) then
    if (indexedIn c).any (fun q => boundsSeq d q && !boundsSeq c q) then recordLint .indexAfterUse e (Core.indexAfterUseMsg (srcText c) (srcText d))
  let cx := { cx with chain := j }
  -- Each operand's type is checked as the `fren` command checks it
  -- (`lang::operator_type`).
  let kw := if operand matches .unlessBody then "unless" else "when"
  -- For `manual_at_most_one`: whether the operands give a definedness
  -- obligation.
  let mark := (← getLocal).indexes.size + (← getLocal).tables.size
  -- Of `and`, the position of each operand in its chain, and the names
  -- that the left one's pattern tests bind, which the right one sees; at
  -- the top of the chain, those of the whole, which only the body of the
  -- `when` or `if` whose condition it is sees. Of `when`, the names that
  -- its condition's pattern tests bind, which its body sees
  -- (`lang::test_scope`).
  let (context, at?) := test
  let (k, n) := at?.getD (0, (chainOperands "and" e).size)
  let left := (chainOperands "and" c).size
  let (ccx, dcx) : ExprCtx × ExprCtx := match op with
    | .and => ({ cx with testContext := context, testAt? := some (k, n) }, { cx with testContext := context, testAt? := some (k + left, n) })
    | .or => ({ cx with testContext := .orOperand }, { cx with testContext := .orOperand })
    | .implies => ({ cx with testContext := if operand matches .unlessBody then .unlessCondition else .whenCondition }, cx)
  let boundMark := (← getLocal).bound.size
  let x ← toTerm ccx c
  checkTermType c x .bool (if j.isEmpty then some s!"note: the condition of `{kw}` is a `Bool`" else Core.opNote j .bool)
  let x ← propositionTerm x
  let g ← operand.guard (pure x) `(¬$x)
  let new ← boundSince boundMark
  let seen := match op with
    | .and => new
    | .or => #[]
    | .implies => if Core.binderVisible ccx.testContext 0 1 .body then new else #[]
  if op matches .implies then modifyLocal fun l => { l with bound := l.bound.extract 0 boundMark }
  let y ← toTerm { dcx with guards := cx.guards.push g, binders := cx.binders ++ seen } d
  if op matches .and && at?.isNone && !Core.binderVisible context 0 n .body then
    modifyLocal fun l => { l with bound := l.bound.extract 0 boundMark }
  if op matches .and && cx.noteIndexes && (← getLocal).indexes.size + (← getLocal).tables.size > mark then
    modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .obligations) }
  if j.isEmpty then checkTermType e y .bool (some s!"note: the body of `{kw}` is a `Bool`")
  else checkTermType d y .bool (Core.opNote j .bool)
  let y ← propositionTerm y
  match op with
  | .implies => `($g → $y)
  | .and => `($x ∧ $y)
  | .or => `($x ∨ $y)

/-- `goal` where `guards` hold. -/
def guardedGoal (guards : Array Term) (goal : Term) : TermElabM Term :=
  guards.foldrM (fun g acc => `($g → $acc)) goal

/-- Records the index `q[i]` at `ref`, as the terms `q` and `i`, for the
definedness check (`check::definedness`): its guard implies its bounds. -/
def noteIndex (cx : ExprCtx) (ref : Syntax) (q i : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let bounds ← `(0 ≤ $i ∧ $i < Fren.Seq.len $q)
  let goal ← guardedGoal cx.guards bounds
  modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- Records the questions about the rows of the table `e`, whose rows other
than `_` have the conditions `conds`, written at `refs`, whose indexes are
in range where `defined` says, for its
completeness and disjointness checks (`check::completeness`,
`check::disjointness`): completeness is reported at `table`, and the
disjointness of two rows at the later one's condition. -/
def noteTable (cx : ExprCtx) (e : Syntax) (refs : Array Syntax) (conds : Array Term) (defined : Array (Option Term))
    (wild : Bool) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let orF (cs : Array Term) : Term := cs.pop.foldr (fun c acc => Unhygienic.run `($c ∨ $acc)) cs.back!
  let andF (a b : Term) : Term := Unhygienic.run `($a ∧ $b)
  let notF (c : Term) : Term := Unhygienic.run `(¬$c)
  for (g, f) in Core.tableGoals orF andF notF (Unhygienic.run `(True)) conds defined wild do
    let ref := match g with
      | .disjointness _ _ j | .reachability _ j => refs[j]!
      | _ => e[0]
    let goal ← guardedGoal cx.guards f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

/-- The arguments for the placeholders `uses` of a definition of the generic
function at `path`, or of its contract, with the type parameters `tps`, at
its instance with the type arguments `targs`: a type parameter's type
argument, its `Inhabited` instance's, and any other placeholder itself
(`Reqs/Generated#generic-functions`). -/
def usesTerms (uses : Array Name) (path : Name) (tps : Array Name) (targs : Array Core.Ty) : TermElabM (Array Term) :=
  uses.mapM fun u => do
    for p in tps, k in [0:tps.size] do
      let ph := placeholderName (Core.typeParamPath path k p)
      if u == ph then return typeSyntax (← leanTypeOf targs[k]!)
      if u == inhabitedName ph then return ← `((inferInstance : Inhabited $(typeSyntax (← leanTypeOf targs[k]!))))
    return ⟨(mkCIdent u).raw⟩

/-- Records an application of the generic function at `path` at the type
arguments `targs`, in the current item (`Core.GenericUse`). -/
def recordGenericUse (path : Name) (targs : Array Core.Ty) : TermElabM Unit := do
  let l ← getLocal
  record (.genericUse (← getMainModule)
    { file := 0, item := l.currentItem, caller? := l.fnTypeParams.map (·.1), callee := path, targs })

/-- Records the questions about the application at `ref` of the function at
`path` to the arguments `args`, if the function has preconditions, for
the precondition check (`check::precondition`): its guard implies each
precondition at the arguments, in order; of a generic function, at the
instance with the type arguments that `inst?` gives its type parameters. -/
def notePreconditions (cx : ExprCtx) (ref : Syntax) (path : Name) (args : Array Term)
    (inst? : Option (Array Name × Array Core.Ty) := none) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some k := (← getState).contracts.get? path | return
  let pres ← k.pres.mapM fun pre => do
    let some (tps, targs) := inst? | return (pre.name, ← `($(mkCIdent pre.decl) $(pre.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*))
    return (pre.name, ← `(@$(mkCIdent pre.decl) $(← usesTerms pre.uses path tps targs)* $args*))
  let guarded (g : Term) : Term := cx.guards.foldr (fun c acc => Unhygienic.run `($c → $acc)) g
  for (q, goal) in Core.preconditionQuestions guarded path pres do
    modifyLocal fun l => { l with tables := l.tables.push (ref, q, goal) }

open Lang in
/-- Translates a table into a chain of `if`s over its rows' conditions,
where `toTerm` translates its parts. Where no row holds, a table without a
`_` row is an index out of range of the empty sequence, `Fren.Seq.nth ∅
0`, as the solver sees it: one unspecified value of each type
(`Reqs/Lang/Expressions#tables`). -/
def tableTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (slot : Option Core.Slot) :
    TermElabM Term := withRef e do
  let rows := e[2].getSepArgs
  -- Only the last row may be `_` (`Reqs/Lang/Expressions#tables`).
  if let some k := Core.rowAfterWild? (rows.map isWildRow) then throwErrorAt rows[k]![1] Core.rowAfterWildMsg.text
  let wild := isWildRow rows.back!
  let mut conds : Array Term := #[]
  let mut refs : Array Syntax := #[]
  let mut defined : Array (Option Term) := #[]
  -- The negations of the earlier rows' conditions, which guard a row
  -- (`Core.earlierFail`).
  let mut negs : Array Term := #[]
  let mut values : Array Term := #[]
  for r in rows, k in [0:rows.size] do
    let before := cx.guards ++ negs
    let mut own := #[]
    if isWildRow r then
      -- The `_` row, which is last, for its reachability.
      refs := refs.push r[1]
    else
      -- Translated under its own guards alone, so that its indexes say where
      -- it defines them; then they, and the questions about its tables, are
      -- put under the guards around it.
      let (k, kt) := ((← getLocal).indexes.size, (← getLocal).tables.size)
      let c ← toTerm { cx with guards := #[], natOk := false, emptyOk := false, expected? := none } r[1]
      checkTermType r[1] c .bool (some Core.rowConditionNote)
      let l ← getLocal
      let inCond := l.indexes.extract k
      let idx ← inCond.mapM fun (r, g) => return (r, ← guardedGoal before g)
      let tbl ← (l.tables.extract kt).mapM fun (r, q, g) => return (r, q, ← guardedGoal before g)
      modifyLocal fun l => { l with indexes := l.indexes.extract 0 k ++ idx, tables := l.tables.extract 0 kt ++ tbl }
      conds := conds.push c
      defined := defined.push (Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) (inCond.map (·.2)))
      refs := refs.push r[1]
      negs := negs.push (← `(¬$c))
      own := #[c]
    -- Each value is checked against the whole's type, or another's (`lang::checked`).
    let others := (rows.eraseIdx! k).map (·[3])
    let emptyOk := Core.Position.shared.checked cx.emptyOk (← anySynthesizes cx others)
    values := values.push (← toTerm { cx with guards := before ++ own, emptyOk } r[3])
  -- Each value has the type of those before it (`Core.checkRowType`).
  let mut t0? : Option Core.Ty := none
  for r in rows, v in values do
    let some t ← frenTypeOf? v | continue
    if let some t0 := t0? then liftMsg r[3] (Core.checkRowType t0 t)
    t0? := some ((t0?.map (·.join t)).getD t)
  noteTable cx e refs conds defined wild
  -- `same_branches` on a table (`lint::same_rows`).
  if cx.noteIndexes then
    let first := exactText rows[0]![3]
    let (fires, _) := Core.sameRows rows.size (rows.all fun r => Core.writtenSame (exactText r[3]) first) wild
    if fires then
      let v : Core.BText := { text := first, prec := exprPrec rows[0]![3] }
      let msg := Core.sameRowsMsg first (v.inSlot slot (followedStx e)) wild
      recordLint .sameBranches e (if wild && (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  let widened ← widenMixed values
  -- The first row whose condition holds.
  let mut out ← if wild then pure widened.back! else
    `(if $(conds.back!) then $(widened.back!) else Fren.Seq.nth (∅ : Fren.Seq _) 0)
  for i in (List.range (widened.size - 1)).reverse do
    out ← `(if $(conds[i]!) then $(widened[i]!) else $out)
  return out

/-- `t` within the `have`s of `binds`, each a local, its type and its
definition, the first outermost. -/
def haves (binds : Array (Ident × Term × Term)) (t : Term) : TermElabM Term :=
  binds.foldrM (fun (x, ty, d) acc => `(have $x : $ty := $d; $acc)) t

/-- The range of `stx` in the characters of `str`, the text it is written
in, as the `fren` command counts it. -/
def charRange (str : String) (stx : Syntax) : Core.Range := charRangeAt str (stx.getPos?, stx.getTailPos?)
where
  /-- The range from `p` to `q`, in characters. -/
  charRangeAt (str : String) : Option String.Pos.Raw × Option String.Pos.Raw → Core.Range
    | (p, q) =>
      let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract str 0 (p.getD 0)).length
      { start := off p, stop := off q }

/-- The text that `stx` is written in, as characters. -/
def sourceOf (stx : Syntax) : String :=
  match stx.getSubstring? false false with
  | some sub => sub.str
  | none => ""

/-- Records the lints of the `let` or `where` clause `e`, of the
definitions `defs`: its names that neither the body nor a later definition
mentions (`unused_variables`), `let_and_return` and `redundant_locals`
(`lint::let_and_return`, `lint::redundant_locals`), as the `fren` command
reports them. -/
def lintClause (e : Syntax) (defs : Array Syntax) (isWhere : Bool) : TermElabM Unit := do
  let body := e[3]
  let names := defs.map fun d => (declaredIdent d[0]).1.getId
  let used := (Core.clauseMentions names (defs.map (pathMentions ·[3])) (pathMentions body) true).2
  for d in defs, n in names, u in used do
    unless u do recordLint .unusedVariables (declaredIdent d[0]).1 (Core.unusedDefinitionMsg n)
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable && !m.fixes.isEmpty then m.note Core.fixHelp else m
  -- A path, as an expression, is a node around the path.
  let ownName (x : Syntax) (n : Name) : Bool :=
    let x := unparen x
    let x := if x.getNumArgs == 1 then x[0] else x
    x.isOfKind ``Lang.fren_path && (match pathSegs x with | #[y] => y.getId == n | _ => false)
  let bodyIsLast := defs.size > 0 && ownName body names.back!
  let redundant := (defs.zip names).map fun (d, n) =>
    Core.redundantLocal (declaredIdent d[0]).2 (!d[1].isNone) (ownName d[3] n)
  unless (defs.size > 0 && Core.letAndReturn bodyIsLast (!defs.back![1].isNone)) || redundant.contains true do return
  -- The clause's text, from `let`, or from its body to its last definition.
  let str := sourceOf body
  let cs := str.toList.toArray
  let clause : Core.Range := if isWhere then { start := (charRange str body).start, stop := (charRange str defs.back!).stop }
    else charRange str e
  let commented := Core.hasComment (Core.textOf cs clause)
  let ranges := defs.map fun d => ({ start := (charRange str d).start, stop := (charRange str d[3]).stop } : Core.Range)
  if defs.size > 0 && Core.letAndReturn bodyIsLast (!defs.back![1].isNone) then
    let earlier? := if defs.size < 2 then none
      else some (Core.textOf cs { start := ranges[0]!.start, stop := ranges[defs.size - 2]!.stop })
    let fixed := Core.letAndReturnFixed isWhere earlier? (Core.textOf cs (charRange str defs.back![3]))
    recordLint .letAndReturn (unparen body) (help (Core.letAndReturnMsg names.back! isWhere clause fixed commented))
  for d in defs, n in names, r in redundant do
    if r then recordLint .redundantLocals d[0] (Core.redundantLocalMsg n)

open Lang in
/-- Elaborates the definitions `defs` of a `let` (`inLet`) or `where`
clause, from the `k`th, each in the scope of the earlier ones, and runs
`body` in the context of the clause's body, with each name's local, type
and definition (`Reqs/Lang/Let`). Each name is a local while `body` runs,
so that the types of terms that mention it are known. -/
partial def withDefinitions (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (defs : Array Syntax)
    (inLet : Bool) (used : Array Bool) (body : ExprCtx → Array (Ident × Term × Term) → TermElabM α) (k : Nat := 0)
    (binds : Array (Ident × Term × Term) := #[]) : TermElabM α := do
  let some d := defs[k]? | body cx binds
  let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome
  let x ← declare d[0] cx.modName locals
  let n := x.getId
  -- This name and the later ones that hide nothing are not in scope yet.
  let pending := (defs.extract k defs.size).toList.zipIdx.filterMap fun (z, j) =>
    let (y, bang) := declaredIdent z[0]
    if bang then none else some (y.getId, j == 0)
  let pannot? ← if d[1].isNone then pure none else some <$> elabPType cx.modName d[1][1]
  let annot? := pannot?.map (·.1)
  -- Its indexes are guarded where the name is mentioned, and so is its
  -- written type's obligation (`Reqs/Lang/Let#definitions`).
  let before := (← getLocal).indexes
  let beforeTables := (← getLocal).tables
  modifyLocal fun l => { l with indexes := #[], tables := #[] }
  let position := if annot?.isSome then Core.Position.declared else .synthesized
  -- Its written type is expected of it, as the `fren` command has it.
  let dcx := { cx with guards := #[], pending := pending.toArray, emptyOk := position.checked false false
                       natOk := annot?.any (·.isConstOf ``Nat), unmentioned := cx.unmentioned || !used[k]!
                       expected? := pannot?.map (·.2.ty) }
  let t ← toTerm dcx d[3]
  if let some (_, pt) := pannot? then noteObligation dcx .letDefinition d[3] pt t
  let obligations := (← getLocal).indexes
  let tableObligations := (← getLocal).tables
  modifyLocal fun l => { l with indexes := before, tables := beforeTables }
  let last := inLet && k + 1 == defs.size
  -- A condition is a `Prop`, and its name a `Bool`, as a variable is.
  let ty ← typeOf t
  let ty := if ty.isProp then Lean.mkConst ``Bool else ty
  -- A `Nat` widens to an `Int`, as anywhere an `Int` is expected.
  let widens := annot?.any (·.isConstOf ``Int) && ty.isConstOf ``Nat
  let ty ← match annot? with
    | some a =>
      unless widens || (← isDefEq a ty) do
        throwErrorAt d[3] (Core.definitionTypeMsg n (← typeName a) (← typeName ty) last).text
      pure a
    | none => pure ty
  let t ← if widens then widenTerm t else pure t
  liftMsg x ((Core.checkVarName n (some (ty.isConstOf ``Bool))).mapError (Core.membershipNote last))
  if cx.noteIndexes then lintName .binder n x
  -- Named apart from every local around it, so that putting a definition's
  -- indexes under the `have`s of its uses captures nothing.
  let lname := Name.mkSimple s!"{Core.nameText n}@{cx.binders.size}"
  let tyStx := typeSyntax (← instantiateMVars ty)
  let b : MatchBinder := { name := n, term := mkIdent lname, «type» := ty, scrutinee := d[3], outer := cx.binders.size,
                           isDef := true, obligations, tableObligations, annot? := pannot?.map (·.2.ty) }
  let value ← `(($t : $tyStx))
  withLocalDeclD lname ty fun _ =>
    withDefinitions toTerm { cx with binders := cx.binders.push b } defs inLet used body (k + 1)
      (binds.push (mkIdent lname, tyStx, value))

open Lang in
/-- `let ds in b`, or `b where ds`, which a `where` clause becomes
(`withWhere`): `b` within a `have` for each definition. -/
def letTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk concatOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  let defs := e[1].getSepArgs
  let inLet := defs.all (·.isOfKind ``Lang.fren_let_def)
  withDefinitions toTerm cx defs inLet (usedDefinitions defs e[3]) fun bcx binds => do
    let mark := (← getLocal).indexes.size
    let tableMark := (← getLocal).tables.size
    -- A body that is a membership right after the `in` may have been meant
    -- as part of the last definition, which `in` ended.
    let b ← tryCatch (toTerm { bcx with emptyOk, concatOk } e[3]) fun ex => do
      let .error ref msg := ex | throw ex
      unless inLet && e[3].isOfKind ``Lang.memberExpr do throw ex
      let text ← msg.toString
      throw (.error ref m!"{text}{if (text.splitOn "\n\n").length > 1 then "\n" else "\n\n"}{Core.membershipNoteText}")
    -- Not of what a function's block lowers to, whose `where` is written
    -- nowhere (`Reqs/Lang/Items#function-blocks`).
    let lowered := e[2].getPos?.isNone
    if cx.noteIndexes && !lowered then lintClause e defs !inLet
    -- The indexes of the body, and of the names it mentions, are within the
    -- `have`s.
    let xs := (← getLocal).indexes
    let wrapped ← (xs.extract mark xs.size).mapM fun (r, g) => return (r, ← haves binds g)
    let ts := (← getLocal).tables
    let wrappedTables ← (ts.extract tableMark ts.size).mapM fun (r, q, g) => return (r, q, ← haves binds g)
    modifyLocal fun l => { l with indexes := xs.extract 0 mark ++ wrapped, tables := ts.extract 0 tableMark ++ wrappedTables }
    haves binds b

/-- `[a, b]`, or `[]` where `emptyOk` says that something gives it a type. -/
def seqLitTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  let elems := e[1].getSepArgs
  if elems.isEmpty then
    unless emptyOk do throwErrorAt e Core.emptySeqTypeMsg.text
    if expected?.isSome then discard (liftMsg e (Core.checkEmptyLiteral true expected?))
    return ← `((∅ : Fren.Seq _))
  let synth ← elems.mapM (synthesizes cx)
  let ecx (k : Nat) := { cx with emptyOk := Core.Position.shared.checked emptyOk ((synth.eraseIdx! k).any id) }
  -- Each element is checked against the literal's element type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  -- An element is never a `Nat` (`lang::nat_place`).
  let elem? ← match expected?.bind fun | .seq t => some t | _ => none with
    | some t => pure (some t)
    | none => if synth[0]! then pure none else
        match synth.findIdx? id with
        | some k => do
          let s ← saveState
          let t? ← frenTypeOf? (← toTerm { ecx k with noteIndexes := false } elems[k]!)
          s.restore
          pure t?
        | none => pure none
  let x0 ← toTerm { ecx 0 with expected? := elem? } elems[0]!
  let t0? := ((← frenTypeOf? x0).orElse fun _ => if synth[0]! then none else elem?).map (·.widen)
  let mut xs := #[← boolTerm (← widenTerm x0)]
  for k in [1:elems.size] do
    let x ← toTerm { ecx k with expected? := t0? } elems[k]!
    if let (some t, some t0) := ((← frenTypeOf? x).map (·.widen), t0?) then
      unless t == t0 do throwErrorAt elems[k]! (Core.membersMsg true t0.show t.show (Core.Ty.seq t0).show).text
    xs := xs.push (← boolTerm (← widenTerm x))
  -- After its elements, as in the `fren` command.
  checkCore cx e .seqArray true true elems
  checkNewtypeMembers cx true elems xs
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
  if e.isOfKind ``Lang.fieldExpr then return ← method e[0] (fieldName e[2]).toString #[]
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
  unless (← getState).newtypes.isEmpty do
    let tx? ← frenTypeOf? x
    checkNewtypeOp op tx? tx?
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
    (p : TSyntax ``fren_path) (expected? : Option Core.Ty := none) : TermElabM Term := do
  let segs := pathSegs p
  if h : segs.size = 1 then
    lintChain toTerm cx parent? e
    let id := segs[0]
    let n := id.getId
    -- A binder or variable, then any fields read from it.
    let base? ← if let some b := cx.binder? n.getRoot then do
        if let some sc := b.scrutinee then
          if b.isDef then
            -- A name stands for its definition: its indexes are guarded
            -- here, and what it mentions may be mentioned here, which
            -- translating it again checks, without its lints.
            if cx.noteIndexes then
              let goals ← b.obligations.mapM fun (r, g) => return (r, ← guardedGoal cx.guards g)
              let tables ← b.tableObligations.mapM fun (r, q, g) => return (r, q, ← guardedGoal cx.guards g)
              modifyLocal fun l => { l with indexes := l.indexes ++ goals, tables := l.tables ++ tables }
            let saved ← saveState
            discard (toTerm { cx.at b with noteIndexes := false, pending := #[], emptyOk := true, expected? := b.annot? } sc)
            saved.restore
          else discard (toTerm (cx.at b) sc)
        else if cx.noteIndexes && n.isAtomic then
          modifyLocal fun l => { l with boundMentions := l.boundMentions.push ((id.getPos?, id.getTailPos?), b.outer) }
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
    if let some (_, own) := cx.pending.find? (·.1 == n.getRoot) then
      throwErrorAt id (Core.definedLaterMsg n.getRoot own).text
    unless n.isAtomic do throwErrorAt segs[0] (Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name))).text
    if let some c := Core.builtinFunction? n then throwError (Core.unappliedMsg (.mkSimple c.name)).text
    -- A function parameter, which is applied (`lang::function_argument`).
    if (cx.fnParam? n).isSome then throwError (Core.unappliedMsg n).text
  match ← resolveWritten cx.modName segs cx.shadowing cx.noteIndexes with
  | .variant en idx =>
    let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
    let n := (info.payloads[idx]?.map (·.size)).getD 0
    if let some msg := Core.variantMentionMsg? (en.path ++ en.variants[idx]!) n false then throwError msg.text
    if cx.noteIndexes then
      let v := ((e.getPos?, e.getTailPos?), (en.path ++ en.variants[idx]!).toString)
      modifyLocal fun l => { l with variants := l.variants.push v }
      if info.ordered then
        let f := ((e.getPos?, e.getTailPos?), Core.NodeFact.ordinal en.path.toString idx info.variants.size)
        modifyLocal fun l => { l with facts := l.facts.push f }
    -- Of a generic enumeration, with its type arguments, which are inferred
    -- from what is expected (`Reqs/Lang/Generics#type-arguments`).
    if let some c ← construction? cx e then
      let (_, targs) ← constructionTerms (fun _ v => toTerm cx v) cx expected? e c #[]
        (Core.showPath (en.path ++ en.variants[idx]!)) fun _ _ => ""
      return ← ctorApp (info.ctor idx) (info.leanArgs (← targs.mapM leanTypeOf)) #[] e
    return mkCIdentFrom e (info.ctor idx)
  | .item { kind := .constItem, path, .. } =>
    let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
    -- Its value's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if c.guarded then modifyLocal fun l => { l with guardedUsed := true }
    -- Its value, not its generated definition (see `Fren.Model`).
    `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
  | .item { kind := .fnItem, path, .. } => throwError (Core.unappliedMsg path).text
  | r => throwError (Core.notAValueMsg r).text

/-- `c(args)`, a cardinality operator applied, where `toTerm` translates
the arguments: the number of them that are `true`, compared with 1, as a
linear sum (`lang::cardinality`). -/
def cardinalityTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (c : Core.Cardinality)
    (args : Array Syntax) : TermElabM Term := do
  let mut ites : Array Term := #[]
  for a in args, k in [0:args.size] do
    -- A `Bool` gives `{}` no type, so `{}` is reported as one whose type
    -- cannot be known, as the `fren` command reports it.
    -- `{}` and `[]` are never `Bool`s, in parentheses or not.
    let lit := unparen a
    if (lit.isOfKind ``Lang.setExpr || lit.isOfKind ``Lang.seqExpr) && lit[1].getSepArgs.isEmpty then
      throwErrorAt lit (Core.cardinalityArgMsg c (k + 1) (if lit.isOfKind ``Lang.setExpr then "{}" else "[]")).text
    let t ← toTerm { cx with emptyOk := false, natOk := false } a
    let ty ← typeOf t
    unless ty.isConstOf ``Bool || ty.isProp do throwErrorAt a (Core.cardinalityArgMsg c (k + 1) (← typeName ty)).text
    ites := ites.push (← `(if $t then (1 : Int) else 0))
  let mut sum := ites[0]!
  for i in ites.extract 1 ites.size do sum ← `($sum + $i)
  match c with
  | .exactlyOne => `($sum = 1)
  | .atMostOne => `($sum ≤ 1)

/-- A closure, as a Lean `fun`, with its body's obligations, each at its
reference, with its table's question if it is one, as a predicate of the
closure's parameters (`closureTerm`). -/
structure ClosureTerm where
  term : Term
  obligations : Array (Syntax × Option Core.TableGoal × Term) := #[]
  deriving Inhabited

open Lang in
/-- The closure whose parameters are `params`, of their types, and whose
body is `body`, of the type `r?` if it is known, where `toTerm` translates
its body: a Lean `fun`, its parameters' types and its body's
(`Reqs/Lang/HigherOrder#meaning`). Its parameters are declared as a
quantifier's bound names are, but not where `synthetic`, as those of a
function's name are, and its body's indexes, tables and applications with
preconditions are checked for every value of them. -/
def closureTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (params : Array (Syntax × Core.Ty))
    (body : Syntax) (r? : Option Core.Ty) (synthetic : Bool) : TermElabM (ClosureTerm × Array Core.Ty × Core.Ty) := do
  let mut named : Array (Name × Name × Core.Ty × Expr) := #[]
  for (x, t) in params, i in [0:params.size] do
    let bn ← if synthetic then pure x.getId else do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what) ++ named.map fun (bn, _) => (bn, Core.BindingKind.boundName)) cx.selfFn.isSome
      let y ← declare x cx.modName locals
      liftMsg y (Core.checkVarName y.getId (some (t == .bool)))
      lintName .binder y.getId y
      pure y.getId
    -- Named apart from every local around it, as the solver never sees it.
    let local_ := Name.mkSimple s!"{bn.toString (escape := false)}#{cx.binders.size + i}"
    named := named.push (bn, local_, t, ← leanTypeOf t)
  withLocalDeclsD (named.map fun (_, l, _, ty) => (l, fun _ => pure ty)) fun _ => do
    let new := named.mapIdx fun i (bn, l, _, ty) =>
      ({ name := bn, term := ⟨mkIdent l⟩, «type» := ty, scrutinee := none, outer := cx.binders.size + i, unbounded := true
         closure := true } : MatchBinder)
    let outer := (← getLocal).indexes
    let outerTables := (← getLocal).tables
    modifyLocal fun l => { l with indexes := #[], tables := #[] }
    let t ← toTerm { cx with binders := cx.binders ++ new, expected? := r?, natOk := false, inClosure := true
                             emptyOk := r?.isSome } body
    let rt := (← frenTypeOf? t).getD .bool
    -- Its obligations, each a predicate of its parameters, which the
    -- application puts at each application of the function parameter
    -- (`lang::closure_obligation`).
    let over (g : Term) : TermElabM Term := named.foldrM (init := g) fun (_, l, _, ty) acc => do
      `(fun ($(mkIdent l) : $(← exprToSyntax ty)) => $acc)
    let raw : Array (Syntax × Option Core.TableGoal × Term) := (← getLocal).indexes.map (fun (ref, g) => (ref, none, g))
      ++ (← getLocal).tables.map fun (ref, q, g) => (ref, some q, g)
    let obls ← raw.mapM fun (ref, q?, g) => return (ref, q?, ← over g)
    modifyLocal fun l => { l with indexes := outer, tables := outerTables }
    let rty ← exprToSyntax (← leanTypeOf (r?.getD rt))
    let lam ← named.foldrM (init := ← `(($t : $rty))) fun (_, l, _, ty) acc => do
      `(fun ($(mkIdent l) : $(← exprToSyntax ty)) => $acc)
    return ({ term := lam, obligations := obls }, named.map (·.2.2.1), rt)

/-- Records the use `u`, written at `ref`, of the defined function `f`, whose
parameters are `ps`, in its own body; an error if with it the uses are not a
structural recursion (`lang::structural_recursion`). -/
def noteRecUse (ref : Syntax) (f : Name) (ps : Array Name) (u : Core.RecUse) : TermElabM Unit := do
  -- Once for each use written: an expression elaborated again, such as a
  -- `match`'s arms for Lean's `match` or a `match`'s scrutinee where a
  -- closure refers to an arm's binder, is not another use.
  let range? := ref.getRange?
  if range?.isSome && (← getLocal).recUses.any (·.1.getRange? == range?) then return
  modifyLocal fun l => { l with recUses := l.recUses.push (ref, u) }
  let uses := (← getLocal).recUses
  if let .notStructural _ i := Core.recursion ps.size (uses.toList.map (·.2)) then
    -- A function always has a parameter; without one, the message names the function.
    throwErrorAt ref (Core.nonStructuralMsg f (ps[i]?.getD f) u.form (u.args[i]?.getD .expr)).text

open Lang in
/-- A closure, or the name of a function, `e`, given for the function
parameter of type `ft`, as its function's signature declares it, of the
higher-order function `f`, whose parameters' types are `ps` where they are
known and whose result's is `r?` if it is known: its term, its
parameters' types and its body's (`Reqs/Lang/HigherOrder#arguments`). The
name of a function `g` is the closure `|x1, ..., xn| g(x1, ..., xn)`. -/
def fnArgTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (f : String) (ft : Core.FnTy)
    (ps : Array (Option Core.Ty)) (r? : Option Core.Ty) (e : Syntax) : TermElabM (ClosureTerm × Array Core.Ty × Core.Ty) := do
  let e := unparen e
  if e.isOfKind ``Lang.lambdaMatchExpr then
    let some types := ps.mapM id | throwErrorAt e (Core.closureParamUnknownMsg f).text
    let names := types.mapIdx fun j _ => mkIdentFrom e (Name.mkSimple s!"#match{j}")
    let body ← explicitLambdaMatch e names
    return ← closureTerm toTerm cx ((names.map (·.raw)).zip types) body r? true
  if e.isOfKind ``Lang.closureExpr then
    let params := e[1].getSepArgs
    if let some msg := Core.argumentMsg? ft (.closure params.size) then throwErrorAt e msg.text
    -- Distinct names (`lang::distinct_names`).
    let declared := params.map fun p => (declaredIdent p[0]).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then throwErrorAt params[k]![0] (Core.dupBoundMsg declared[k]!).text
    let named ← (params.zip ps).mapM fun (p, p?) => do
      -- Its written type is the function type's (`lang::function_argument`).
      let t ← match (if p[1].isNone then none else some p[1][1]), p? with
        | some ty, some q => do
          let a := ((← coreTy? (← elabPType cx.modName ty).1)).getD .bool
          unless a == q do
            throwErrorAt ty (Core.typeMismatchMsg q a (some s!"note: this parameter of the closure for `{f}` has type `{q.show}`")).text
          pure q
        | some ty, none => pure (((← coreTy? (← elabPType cx.modName ty).1)).getD .bool)
        | none, some q => pure q
        | none, none => throwErrorAt p[0] (Core.closureParamUnknownMsg f).text
      return (p[0], t)
    return ← closureTerm toTerm cx named e[3] r? false
  let p := if e.getNumArgs == 1 && e[0].isOfKind ``Lang.fren_path then e[0] else e
  unless p.isOfKind ``Lang.fren_path do throwErrorAt e ((Core.argumentMsg? ft .other).getD default).text
  -- A function parameter, or a defined function, but not an uninterpreted
  -- one (`lang::function_argument`).
  let segs := pathSegs p
  -- The function itself, in its own body, not applied.
  if let some (ps, _, _) := cx.selfRec? then
    if segs.size == 1 && cx.selfFn == some segs[0]!.getId then
      noteRecUse p (cx.modName ++ segs[0]!.getId) ps { form := .passed }
  let isParam := segs.size == 1 && (cx.fnParam? segs[0]!.getId).isSome
  unless isParam do
    match (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing with
    | .ok (.item { kind := .fnItem, path, .. }) =>
      let shape : Core.ArgShape := if (← getState).defined.contains path then .definedName else .uninterpretedName
      if let some msg := Core.argumentMsg? ft shape path then throwErrorAt e msg.text
    | _ => throwErrorAt e ((Core.argumentMsg? ft .other).getD default).text
  let some tys := ps.mapM id | throwErrorAt e (Core.closureParamUnknownMsg f).text
  let xs := (List.range tys.size).toArray.map fun k => mkIdentFrom p (Name.mkSimple s!"#{k}")
  let args ← xs.mapM fun x => pathExpr p x.getId
  let tmpl ← `(fren_expr| f(x))
  let call := (tmpl.raw.setArg 0 p).setArg 2 (Syntax.mkSep args (mkAtom ","))
  closureTerm toTerm cx ((xs.map (·.raw)).zip tys) call r? true

open Lang in
/-- An application `e` of the higher-order function `d` at `path`, whose
name is written `p`, to `elems` (`Reqs/Lang/HigherOrder#applications`):
its definition applied to its value arguments and then its closures, in
order, which unfolding reduces as the `fren` command unfolds them. -/
def hoAppTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e p : Syntax) (path : Name) (d : DefinedInfo)
    (elems : Array Syntax) (expected? : Option Core.Ty) : TermElabM Term := do
  unless elems.size == d.nParams do throwError (Core.arityMsg path d.nParams elems.size).text
  let f := Core.showPath path
  let synth ← elems.mapM (synthesizes cx)
  let run : StateT (Array Term × Array (Option ClosureTerm)) TermElabM (Array Core.Ty) :=
    Core.inferHigherOrder d.typeParams d.hoParams d.result synth expected?
      (throwErrorAt e (Core.cannotInferCallMsg f).text : TermElabM Unit)
      (fun k x? => do
        let t ← (toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := x? == some Core.Ty.nat
                                  expected? := x? } elems[k]! : TermElabM Term)
        modify fun (ts, cs) => (ts.set! k t, cs)
        frenTypeOf? t)
      (fun k x t => (liftMsg elems[k]!
        (Core.checkType x t (some s!"note: argument {k + 1} of `{f}` has type `{x.show}`")) : TermElabM Unit))
      (fun k ps r? => do
        let .function ft := d.hoParams[k]! | return none
        let (c, pts, rt) ← (fnArgTerm toTerm cx f ft ps r? elems[k]! : TermElabM _)
        modify fun (ts, cs) => (ts.set! k c.term, cs.set! k (some c))
        return some (pts, rt))
      (fun k ft (_, rt) => (liftMsg elems[k]!
        (Core.checkType ft.result rt (some s!"note: the closure for argument {k + 1} of `{f}` returns `{ft.result.show}`")) : TermElabM Unit))
  let (targs, ts, closures) ← do
    let (targs, (ts, cs)) ← run.run (elems.map fun _ => default, elems.map fun _ => none)
    pure (targs, ts, cs)
  for a in elems, t in ts, k in [0:ts.size] do
    if d.hoParams[k]! matches .value _ then noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
  -- Its value arguments, then its closures (`Reqs/Generated#higher-order-functions`).
  let inOrder := (ts.zip d.hoParams).filterMap (fun (t, q) => if q matches .value _ then some t else none)
    ++ (ts.zip d.hoParams).filterMap fun (t, q) => if q matches .function _ then some t else none
  let generic := !d.typeParams.isEmpty
  notePreconditions cx p path inOrder (if generic then some (d.typeParams, targs) else none)
  -- Each closure's obligations, at each application of its function
  -- parameter in the unfolded body (`lang::closure_obligation`).
  if cx.noteIndexes then
    for c? in closures.filter Option.isSome, (decl, uses) in d.oblDecls do
      let some c := c? | continue
      for (ref, q?, pred) in c.obligations do
        let g ← if generic then `(@$(mkCIdent decl) $(← usesTerms uses path d.typeParams targs)* $inOrder* $pred)
          else `($(mkCIdent decl) $(uses.map fun u => ⟨(mkCIdent u).raw⟩)* $inOrder* $pred)
        modifyLocal fun l => { l with vias := l.vias.push (ref.getPos?, path) }
        match q? with
        | some q => modifyLocal fun l => { l with tables := l.tables.push (ref, q, g) }
        | none => modifyLocal fun l => { l with indexes := l.indexes.push (ref, g) }
  if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
  if generic then return ← `(@$(mkCIdentFrom p d.decl) $(← usesTerms d.uses path d.typeParams targs)* $inOrder*)
  `($(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $inOrder*)

open Lang in
/-- `p(args)`: a method, a variant with a payload, or a function applied.
`toTerm` translates its parts, and `parent?` is the expression around it. -/
def appTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax)
    (p : TSyntax ``fren_path) (args : Syntax.TSepArray `fren_expr ",") (expected? : Option Core.Ty := none) :
    TermElabM Term := do
  if let some (recv, m) := methodApp? cx e then
    let recv ← pathExpr p recv
    if m.toString == "matches?" then lintPattern cx parent? e recv args.getElems
    return ← methodTerm toTerm cx e p recv m.toString args.getElems cx.natOk
  let segs := pathSegs p
  if segs.size == 1 && (cx.vars.any (·.name == segs[0]!.getId) || (cx.binder? segs[0]!.getId).isSome) then
    throwErrorAt p (Core.varNotAFunctionMsg segs[0]!.getId).text
  if segs.size == 1 && cx.selfFn == some segs[0]!.getId then
    let f := cx.modName ++ segs[0]!.getId
    let some (ps, ft, fx) := cx.selfRec? | throwErrorAt p (Core.recursiveMsg f).text
    -- An application of itself, which must be structural recursion
    -- (`lang::structural_recursion`), typed as a function parameter's.
    unless args.getElems.size == ft.params.size do throwError (Core.arityMsg f ft.params.size args.getElems.size).text
    noteRecUse p f ps { form := if cx.inClosure then .inClosure else .applied
                        args := args.getElems.toList.zipIdx.map fun (a, i) => cx.recArg a i }
    let ts ← (args.getElems.zip ft.params).zipIdx.mapM fun ((a, t), k) => do
      let x ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := false, expected? := some t } a
      if let some found ← frenTypeOf? x then
        liftMsg a (Core.checkType t found (some s!"note: argument {k + 1} of `{Core.showPath f}` has type `{t.show}`"))
      return x
    let ps := cx.vars.map (·.ptype)
    for a in args.getElems, t in ts, i in [0:ts.size] do
      noteObligation cx .argument a (ps[i]?.getD default) t
    if cx.noteIndexes then
      let vals ← ts.mapM fun t => Term.elabTerm t none
      let gs ← cx.guards.mapM elabProp
      modifyLocal fun l => { l with recApps := l.recApps.push (p, vals, gs) }
    return ← `($fx $ts*)
  -- A function parameter (`Reqs/Lang/HigherOrder#function-parameters`).
  if segs.size == 1 then
    if let some (ft, fx) := cx.fnParam? segs[0]!.getId then
      let f := segs[0]!.getId
      unless args.getElems.size == ft.params.size do throwError (Core.arityMsg f ft.params.size args.getElems.size).text
      let ts ← (args.getElems.zip ft.params).zipIdx.mapM fun ((a, t), k) => do
        let x ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := false, expected? := some t } a
        if let some found ← frenTypeOf? x then
          liftMsg a (Core.checkType t found (some s!"note: argument {k + 1} of `{f}` has type `{t.show}`"))
        return x
      return ← `($fx $ts*)
  if let some c := cardinalityApp? e then return ← cardinalityTerm toTerm cx c args.getElems
  -- In its own contract, the function is applied to its parameters, in a
  -- postcondition (`lang::contract_application`); it is not yet in scope.
  let own? := cx.contract?.filter fun k => segs.size == 1 && segs[0]!.getId == Name.mkSimple k.path.getString!
  if let some k := own? then
    -- Each argument as written: a name of one segment, not hidden by a
    -- binder, or another expression.
    let written := args.getElems.map fun a =>
      let a := unparen a
      let a := if a.getNumArgs == 1 then a[0] else a
      if a.isOfKind ``Lang.fren_path && (pathSegs a).size == 1 && (cx.binder? (pathSegs a)[0]!.getId).isNone then
        some (pathSegs a)[0]!.getId
      else none
    let toParams := Core.appliesToParams written k.params
    unless Core.contractApplicationAccepted (if k.post then .postcondition else .precondition) true toParams do
      throwErrorAt p (Core.contractSelfMsg k.path !k.post).text
  -- A variable shadows a function, as it does any other item.
  let r ← match own? with
    | some k => pure (.item { kind := .fnItem, path := k.path, isPub := true, owner := cx.modName })
    | none => resolveWritten cx.modName (pathSegs p) cx.shadowing cx.noteIndexes
  if let .item { kind := .recordItem, path, .. } := r then
    -- A newtype, built from its value (`Reqs/Lang/Expressions#newtypes`).
    let some n := (← getState).newtypes.get? path | throwErrorAt p (Core.constructionMsg path false).text
    unless args.getElems.size == 1 do throwError (Core.arityMsg path 1 args.getElems.size "value").text
    let a := args.getElems[0]!
    let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := n.under.isConstOf ``Nat } a
    -- Its value is checked as the `fren` command checks it (`Core.checkType`).
    if let (true, some u) := (← synthesizes cx a, ← coreTy? n.under) then
      if let some found ← frenTypeOf? t then
        liftMsg a (Core.checkType u found (some s!"note: the value of `{Core.showPath path}` has type `{u.show}`"))
    if cx.noteIndexes then
      let synth ← synthesizes cx a
      modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .wraps path.toString synth) }
    noteObligation cx .construction a (partPType n.shape 0 0) t
    return ← `($(mkCIdentFrom p n.ctor) $t)
  if let .variant en idx := r then
    -- A variant with a payload, built from its values.
    let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
    let v := en.path ++ en.variants[idx]!
    let n := (info.payloads[idx]?.map (·.size)).getD 0
    if let some msg := Core.variantMentionMsg? v n true then throwError msg.text
    unless args.getElems.size == n do throwError (Core.arityMsg v n args.getElems.size "value").text
    let note (k : Nat) (ty : String) := s!"note: value {k + 1} of the payload of `{Core.showPath v}` has type `{ty}`"
    -- Of a generic enumeration, with its type arguments, which are inferred
    -- (`Reqs/Lang/Generics#type-arguments`).
    if let some c ← construction? cx e then
      let go (x? : Option Core.Ty) := toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := false, expected? := x? }
      let (ts, targs) ← constructionTerms go cx expected? e c args.getElems (Core.showPath v) fun k t => note k t.show
      -- Each value's obligation, of its type with the enumeration's arguments.
      for a in args.getElems, t in ts, k in [0:ts.size] do
        noteObligation cx .payload a (partPType info.shape idx k targs) t
      return ← ctorApp (info.ctor idx) (info.leanArgs (← targs.mapM leanTypeOf)) ts p
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := info.payloads[idx]![k]!.isConstOf ``Nat,
                                expected? := ← coreTy? info.payloads[idx]![k]! } a
      checkDeclared a t info.payloads[idx]![k]! (note k)
      noteObligation cx .payload a (partPType info.shape idx k) t
      return t
    return ← `($(mkCIdentFrom p (info.ctor idx)) $args*)
  let .item { kind := .fnItem, path, .. } := r | throwErrorAt p (Core.notAFunctionMsg r).text
  if let some d := ((← getState).defined.get? path).filter (!·.hoParams.isEmpty) then
    return ← hoAppTerm toTerm cx e p path d args.getElems expected?
  if let some d := (← getState).defined.get? path then
    let argStxs := args.getElems
    -- Its definition, applied to the placeholders it uses; its arguments
    -- may mention anything (`lang::argument`).
    unless args.getElems.size == d.nParams do throwError (Core.arityMsg path d.nParams args.getElems.size).text
    if !d.typeParams.isEmpty then
      -- A generic function, at the instance whose type arguments are
      -- inferred, as the `fren` command infers them
      -- (`Reqs/Lang/GenericFunctions#applications`).
      let elems := args.getElems
      let synth ← elems.mapM (synthesizes cx)
      let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
        Core.inferCall d.typeParams d.declared d.result synth expected?
          (throwErrorAt e (Core.cannotInferCallMsg (Core.showPath path)).text : TermElabM Unit)
          (fun k x? => do
            let natOk := x? == some Core.Ty.nat
            let t ← (toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk, expected? := x? }
              elems[k]! : TermElabM Term)
            modify (·.set! k t)
            frenTypeOf? t)
          (fun k x f => (liftMsg elems[k]!
            (Core.checkType x f (some s!"note: argument {k + 1} of `{Core.showPath path}` has type `{x.show}`")) : TermElabM Unit))
      let (targs, ts) ← run.run (elems.map fun _ => default)
      for a in elems, t in ts, k in [0:ts.size] do
        noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
      notePreconditions cx p path ts (some (d.typeParams, targs))
      recordGenericUse path targs
      if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
      return ← `(@$(mkCIdentFrom p d.decl) $(← usesTerms d.uses path d.typeParams targs)* $ts*)
    let tys := paramTypes (← instantiateForall (← getConstInfo d.decl).type (d.uses.map mkConst))
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := tys[k]!.isConstOf ``Nat, expected? := ← coreTy? tys[k]! } a
      checkDeclared a t tys[k]! fun ty => s!"note: argument {k + 1} of `{Core.showPath path}` has type `{ty}`"
      noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
      return t
    notePreconditions cx p path args
    -- Its body's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if d.guarded then modifyLocal fun l => { l with guardedUsed := true }
    return ← `($(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*)
  if cx.inClosure then throwErrorAt p (Core.closureUninterpretedMsg path).text
  if cx.selfFn.isSome then throwErrorAt p (Core.appliesUninterpretedMsg path).text
  let a ← placeholderOf path
  if !a.typeParams.isEmpty then
    -- A generic function without a body, at the instance whose type
    -- arguments are inferred, as for a defined one: its placeholder applied
    -- to them and their `Inhabited` instances
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`). Outputs
    -- may not occur in its arguments (`inst::mention`).
    let acx := if cx.place == .prop then { cx with place := .argument } else cx
    let elems := args.getElems
    unless elems.size == a.declared.size do throwError (Core.arityMsg path a.declared.size elems.size).text
    let synth ← elems.mapM (synthesizes acx)
    let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
      Core.inferCall a.typeParams a.declared a.result synth expected?
        (throwErrorAt e (Core.cannotInferCallMsg (Core.showPath path)).text : TermElabM Unit)
        (fun k x? => do
          let natOk := x? == some Core.Ty.nat
          let t ← (toTerm { acx with emptyOk := Core.Position.declared.checked false false, natOk, expected? := x? }
            elems[k]! : TermElabM Term)
          modify (·.set! k t)
          frenTypeOf? t)
        (fun k x f => (liftMsg elems[k]!
          (Core.checkType x f (some s!"note: argument {k + 1} of `{Core.showPath path}` has type `{x.show}`")) : TermElabM Unit))
    let (targs, ts) ← run.run (elems.map fun _ => default)
    for x in elems, t in ts, k in [0:ts.size] do
      noteObligation acx .argument x (a.ptys.1[k]?.getD default) t
    notePreconditions cx p path ts (some (a.typeParams, targs))
    recordGenericUse path targs
    let tyArgs ← targs.flatMapM fun t => do
      let ty := typeSyntax (← leanTypeOf t)
      return #[ty, ← `((inferInstance : Inhabited $ty))]
    return ← `(@$(mkCIdentFrom p a.placeholder) $tyArgs* $ts*)
  let a' := a
  let nParams := (← getConstInfo a.placeholder).type.getForallArity
  unless args.getElems.size == nParams do throwError (Core.arityMsg path nParams args.getElems.size).text
  -- Outputs may not occur in arguments (`inst::mention`); assumptions and
  -- bindings exclude them already.
  let acx := if cx.place == .prop then { cx with place := .argument } else cx
  let tys := paramTypes (← getConstInfo a.placeholder).type
  let args ← args.getElems.zipIdx.mapM fun (a, k) => do
    let t ← toTerm { acx with emptyOk := Core.Position.declared.checked false false, natOk := tys[k]!.isConstOf ``Nat, expected? := ← coreTy? tys[k]! } a
    checkDeclared a t tys[k]! fun ty => s!"note: argument {k + 1} of `{Core.showPath path}` has type `{ty}`"
    noteObligation acx .argument a (a'.ptys.1[k]?.getD default) t
    return t
  notePreconditions cx p path args
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
  return ← propositionTerm x

/-- The nonempty `xs` joined by `op`, as a balanced tree, so that a
quantifier's expansion is as deep as the logarithm of its instances, which
the solver's preprocessing recurses through. -/
partial def balanced (op : Expr → Expr → Expr) (xs : Array Expr) : Expr :=
  if xs.size ≤ 1 then xs[0]!
  else op (balanced op (xs.extract 0 (xs.size / 2))) (balanced op (xs.extract (xs.size / 2)))

/-- Whether the quantifier `e` is a `forall`, rather than an `exists`. -/
def isForall (e : Syntax) : Bool :=
  let kw := if e[0].isAtom then e[0] else e[0][0]
  kw.getAtomVal.trimAscii.toString == "forall"

/-- The number of values of `ty`, if a quantifier ranges over it
(`lang::quantified_type`), counted without listing them. An unbounded
enumeration or record is recursive or has a part that a quantifier does
not range over, so it is not looked into, and the recursion ends. -/
def valueCount? (ty : Expr) : TermElabM (Option Nat) := do
  -- As the `fren` command counts them, by an instance's arguments too
  -- (`lang::instance_values`).
  let s ← getState
  let some t := coreTyOf s (← instantiateMVars ty) | return none
  return t.valueCount (dataSig s)

/-- The Lean type of a quantifier's binder's type `ty`, which must not be a
procedure. -/
def binderType (modName : Name) (ty : Syntax) : TermElabM (Expr × Core.PTy) := do
  if let some p := (typePath? ty).filter fun _ => !hasFnType ty then
    if let .ok (.item { kind := .compItem, path, .. }) := (← getState).table.resolvePath modName (← segNames (pathSegs p)) #[] then
      throwErrorAt ty (Core.quantifiedComponentMsg (Core.showPath path)).text
  elabPType modName ty

/-- The value `v` of the Lean type `ty`, as a term (`Core.PVal`). -/
partial def valueTerm (ty : Expr) (v : Core.PVal) : TermElabM Term := do
  let s ← getState
  match v with
  | .bool b => if b then `(true) else `(false)
  | .int i => if ty.isConstOf ``Nat then `(($(Syntax.mkNumLit (toString i.toNat)) : Nat)) else intTerm i
  | .ctor idx args =>
    let some d := ty.getAppFn.constName? | `(sorry)
    -- With an instance's arguments for its type parameters.
    let targs := ty.getAppArgs
    let (c, ts) :=
      if let some e := s.enumOfDecl? d then (e.ctor idx, (e.payloadsAt targs)[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then (r.ctor, (r.fieldsAt targs).map (·.2))
      else if let some n := s.newtypeOfDecl? d then (n.ctor, #[n.under])
      else (.anonymous, #[])
    let as ← (args.zip ts).mapM fun (w, t) => valueTerm t w
    `($(mkCIdent c) $as*)

/-- The values of the declared type `pt`, of the Lean type `ty`, as terms,
and how many there are, if a quantifier ranges over it, as the `fren`
command's `binderValues`. -/
def binderValues (ty : Expr) (pt : Core.PTy) : TermElabM (Option (Nat × Array Term)) := do
  let st ← getState
  -- Only a listed type's values are listed (`lang::quantified_type`).
  unless (factsOf st pt).listed do return none
  if (pt.cons st.shapeOf).isNone then
    let some n ← valueCount? ty | return none
    return some (n, (← valuesOf? ty Core.maxInstances).getD #[])
  let some n := pt.count? st.shapeOf | return none
  if n > Core.maxInstances then return some (n, #[])
  let vs := (pt.values st.shapeOf Core.maxInstances).getD #[]
  return some (n, ← vs.mapM (valueTerm ty))

/-- Whether `e` names `n` anywhere within it: as a path of one segment
whose root is `n`, or a field of a record literal or update written
without `:=`; not as an applied function, a record's type, or within a
type or pattern. A name is compared as written, whatever shadows it, as
the `fren` command's `Expr.names` does. -/
partial def namesBound (n : Name) (e : Syntax) : Bool :=
  if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    segs.size == 1 && segs[0]!.getId.getRoot == n
  else if e.isOfKind ``Lang.fren_binding then
    (e[1].isNone && e[0].getId == n) || namesBound n e[1]
  else if e.isOfKind ``Lang.appExpr || e.isOfKind ``Lang.recordExpr then e.getArgs.extract 1 |>.any (namesBound n)
  else if e.isOfKind ``Lang.fren_binder || e.isOfKind ``Lang.fren_top_pattern || e.isOfKind ``Lang.fren_or_pattern then false
  else if e.isOfKind ``Lang.fren_let_def then namesBound n e[3]
  else e.getArgs.any (namesBound n)

/-- What `Core.splitConjuncts` sees of a node of a guard, without the
parentheses around it, as the `fren` command's `guardNode`. -/
def guardNode (e : Syntax) : Core.GuardNode Syntax :=
  let e := unparen e
  let op (o : Syntax) := o.getAtomVal.trimAscii.toString
  if e.getNumArgs == 3 && e[1].isAtom && op e[1] == "and" then .conj e[0] e[2]
  else if let some (xs, ops) := chainOf? e then .compare xs (ops.map op)
  else if isComparison e then .compare #[e[0], e[2]] #[op e[1]]
  else .other

/-- The condition and body of `e`, if it is a `when`. -/
def whenOf? (e : Syntax) : Option (Syntax × Syntax) :=
  let e := unparen e
  if e.getNumArgs == 4 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "when" then some (e[1], e[3]) else none

/-- The conjuncts of the guard of a quantifier, a `forall` if `all`, whose
body is `body` (`Core.guardConjunctsBy`). -/
def guardConjuncts (all : Bool) (body : Syntax) : Array (Core.GuardConjunct Syntax) :=
  Core.guardConjunctsBy guardNode whenOf? all body

/-- The domain of the bound name at position `k` of `names`, the bound
names of a quantifier, a `forall` if `all`, with the body `body`, where
`nat` says that it is a `Nat` (`Core.boundDomain`), as the `fren` command's
`domainOf`. -/
def domainOf (all : Bool) (names : Array Name) (body : Syntax) (k : Nat) (nat : Bool) : Core.GuardDomain :=
  let alone (e : Syntax) : Option Nat :=
    -- A path, as an expression, is a node around it.
    let e := unparen e
    let e := if e.getNumArgs == 1 then e[0] else e
    if e.isOfKind ``Lang.fren_path then
      let segs := pathSegs e
      if segs.size == 1 then names.idxOf? segs[0]!.getId else none
    else none
  let mentions (e : Syntax) : List Nat := (List.range names.size).filter fun j => namesBound names[j]! e
  (Core.boundDomain alone mentions (guardConjuncts all body) k nat).1

/-- Records the lints of the quantifier `e`, a `forall` if `all`, whose
binders `binders` declare `ids`, with their types `bound`, of `sizes`
values each, and whose body is `body`: its bound names that the body does
not mention (`unused_variables`), and `trivial_quantifier`
(`lint::trivial_quantifier`), whose fix writes the value of each bound
name in place of its mentions recorded since `mark`, of the binders from
`outer`. A global expectation's binders over values, whose `e` is its
body, have no `forall` of their own, and no fix. -/
def lintQuant (e : Syntax) (all : Bool) (binders ids : Array Syntax) (bound : Array (Name × Expr)) (sizes : Array Nat)
    (body : Syntax) (outer mark : Nat) : TermElabM Unit := do
  let mentioned := (pathMentions body).map (·.getRoot)
  for x in ids, (bn, _) in bound do
    unless mentioned.contains bn do recordLint .unusedVariables (declaredIdent x).1 (Core.unusedBoundMsg bn all)
  unless Core.trivialQuantifier (sizes.filter (· == 1)).size do return
  let some i := sizes.idxOf? 1 | return
  -- The binder of each bound name.
  let bs := binders.flatMap fun b => b[1].getArgs.map fun _ => b
  let st ← getState
  -- The value of a type of one value, if it is a variant without a payload.
  let values := bound.mapIdx fun k (_, ty) => do
    let info ← ty.constName?.bind st.enumOfDecl?
    let #[v] := info.variants | none
    guard (info.payloads[0]?.all (·.isEmpty))
    pure s!"{exactText bs[k]![3]}::{v}"
  let str := sourceOf body
  let cs := str.toList.toArray
  let quant := charRange str e
  let own := e.getPos? != body.getPos?
  let recorded := (← getLocal).boundMentions.extract mark
  let fixed? : Option String := do
    -- A name the body declares again would hide nothing once the quantifier is gone.
    let redeclared := bound.any fun (bn, _) => (declaredNames body).contains (Core.nameText bn)
    guard (Core.trivialQuantifierFixed (sizes.filter (· == 1)).size sizes.size (values.all Option.isSome) (!own)
      redeclared)
    guard (!Core.hasComment (Core.textOf cs quant))
    let vs ← values.mapM id
    let ms := recorded.filterMap fun (r, k) =>
      if outer ≤ k && k < outer + vs.size then some (charRange.charRangeAt str r, vs[k - outer]!) else none
    pure (Core.substituted cs (charRange str body) ms)
  let msg := Core.trivialQuantifierMsg all bound[i]!.1 (exactText bs[i]![3]) values[i]! quant fixed?
  recordLint .trivialQuantifier bs[i]! (if (← getLocal).inMarkdown && fixed?.isSome then msg.note Core.fixHelp else msg)

/-- Whether the declaration `decl` of a defined function has a quantifier
over a type that is not listed, Lean's `∀` over a value or `∃`, directly or
through another defined function that it applies, to a depth of `fuel`,
beyond which it is taken to have one, as the `fren` command's
`fnQuantifies` (`Core.ElementUse.quantifiedArgument`). -/
partial def defQuantifies (env : Environment) (s : State) (fuel : Nat) (decl : Name) : Bool :=
  if fuel == 0 then true else
  match (env.find? decl).bind (·.value?) with
  | none => false
  | some v =>
    let dependent : Expr → Bool
      | .forallE _ _ b _ => b.hasLooseBVars
      | _ => false
    let quantified := (v.find? fun x => x.isAppOf ``Exists || dependent x).isSome
    let decls := s.defined.foldl (init := #[]) fun acc _ d => if d.decl != decl then acc.push d.decl else acc
    quantified || decls.any fun d => (v.find? (·.isConstOf d)).isSome && defQuantifies env s (fuel - 1) d

/-- How the expression `e`, within the body of a quantifier, uses the bound
name `x`, where `inner` are the names that the body declares, which may
stand for `x` (`Core.ElementUse`), as the `fren` command's `elementUses`. -/
partial def elementUses (cx : ExprCtx) (x : Name) (inner : Array Name) (e : Syntax) :
    TermElabM (Array Core.ElementUse) := do
  let names (e : Syntax) : Bool := (pathMentions e).any fun n => n.getRoot == x || inner.contains n.getRoot
  let st ← getState
  let positions (m : String) : Nat := match m with | "update" | "at" => 1 | "slice" => 2 | _ => 0
  let own : Array Core.ElementUse ← do
    if e.isOfKind ``Lang.indexExpr then
      pure (if names e[2] && !(← isConstant cx e[0]) then #[.index] else #[])
    else if e.isOfKind ``Lang.methodExpr then
      let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
      let m := if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString
      pure (if (e[4].getSepArgs.extract 0 (positions m)).any names && !(← isConstant cx e[0]) then #[.index] else #[])
    else if e.isOfKind ``Lang.appExpr then
      let args := e[2].getSepArgs
      if !args.any names then pure #[]
      else if let some (_, m) := methodApp? cx e then
        pure (if (args.extract 0 (positions m.toString)).any names then #[.index] else #[])
      else
        let some names' ← (try some <$> segNames (pathSegs e[0]) catch _ => pure none) | pure #[]
        match st.table.resolvePath cx.modName names' cx.shadowing with
        | .ok (.item { kind := .fnItem, path, .. }) =>
          if let some d := st.defined.get? path then
            let ps := if d.typeParams.isEmpty then d.ptys.1.map (·.ty) else d.declared
            if ps.any (Core.hasSeqWithin st.shapeOf 8) then pure #[.seqArgument]
            else pure (if defQuantifies (← getEnv) st 8 d.decl then #[.quantifiedArgument] else #[])
          else
            let facts := (st.abstracts.get? path).any fun a =>
              a.ptys.2.ty == .nat || a.fact?.isSome || st.contracts.contains path
            pure (if facts then #[.factArgument] else #[])
        | _ => pure #[]
    else if e.isOfKind ``Lang.quantExpr then
      let receivers := (guardConjuncts (isForall e) e[3]).filterMap fun
        | some (_, .mem, r) => some r
        | _ => none
      pure (if receivers.any names then #[.receiver] else #[])
    else pure #[]
  return own ++ (← e.getArgs.flatMapM (elementUses cx x inner))

/-- The quantifier that is directly the body `e` of a quantifier over
elements, a `forall` if `all`, if any, by where it is (`elemKey`), as the
`fren` command's `elementSpine`. -/
partial def elementSpine (all : Bool) (e : Syntax) : Option (Option String.Pos.Raw × Option String.Pos.Raw) :=
  let e := unparen e
  if let some (_, d) := whenOf? e then (if all then elementSpine all d else none)
  else if let .conj _ b := guardNode e then (if all then none else elementSpine all b)
  else if e.isOfKind ``Lang.quantExpr && isForall e == all then some (elemKey e)
  else none

open Lang in
/-- `forall (x: T), e`, or `exists` unless `all`, with the binders
`binders` and the body `body`: expanded over the bound names of listed
types (`Reqs/Lang/Quantifiers#meaning`), and Lean's `∀` or `∃` over the
others, around the expansion (`Reqs/Lang/Quantifiers#unbounded-quantifiers`).
The body is elaborated once, over a local for each bound name, and
instantiated at every combination of the values of those of listed types,
the last name varying fastest, and the instances conjoined or disjoined;
so are the definedness goals of its indexes, which hold in every instance,
under `∀` whatever the quantifier. A local of a type that is not listed is
named `x'k`, with `k` its position among the binders in scope, as the
solver knows it, and `undecidable` is reported at its binder
(`lang::in_core`). The names must be distinct, follow the Boolean names
rule and be written with `!` exactly when they shadow (`lang::shadowing`),
and the combinations be at most `Core.maxInstances`
(`lang::quantifier_size`), as the `fren` command checks them. -/
def quantTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (all : Bool)
    (binders : Array Syntax) (body : Syntax) : TermElabM Term := withRef e do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := binders.flatMap (·[1].getArgs)
  for x in ids do discard (segName x)
  let declared := ids.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt ids[k]! (Core.dupBoundMsg declared[k]!).text
  -- Each bound name, its Lean type and declared type, and its values if
  -- its type is listed.
  let mut bound : Array (Name × Expr × Core.PTy × Option (Array Term)) := #[]
  let mut sizes := #[]
  let mut unlisted := #[]
  for b in binders do
    let (ty, pt) ← binderType cx.modName b[3]
    let values? ← binderValues ty pt
    -- Reported once the quantifier's verdict is known.
    if values?.isNone then unlisted := unlisted.push b
    for x in b[1].getArgs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what) ++ bound.map (·.1, Core.BindingKind.boundName)) cx.selfFn.isSome
      let x ← declare x cx.modName locals
      let bn := x.getId
      liftMsg x (Core.checkVarName bn (some (ty.isConstOf ``Bool)))
      lintName .binder bn x
      bound := bound.push (bn, ty, pt, values?.map (·.2))
      if let some (n, _) := values? then sizes := sizes.push n
  let n := cx.instances * Core.instanceCount sizes
  unless Core.quantifierSizeAccepted n do
    throwErrorAt (mkNullNode binders) (Core.quantifierSizeMsg n (cx.instances > 1)).text
  let names := bound.map (·.1)
  -- A quantifier over a sequence's elements (`lang::element_quantifier`):
  -- each bound name of a type that is not listed has the members of `x in
  -- e` as its domain, by the first conjunct of the guard that names it, as
  -- the `fren` command finds them.
  let conjuncts := guardConjuncts all body
  let parts := Core.guardPartsBy guardNode whenOf? all body
  let members : Array (Option Syntax) := bound.zipIdx.filterMap fun ((bn, ty, _, vs?), k) =>
    if vs?.isSome then none else some <|
      match domainOf all names body k (ty.isConstOf ``Nat) with
      | .members j =>
        if (parts.extract 0 j).any (·.any (namesBound bn)) then none
        else match conjuncts[j]? with
          | some (some (_, .mem, m)) => some m
          | _ => none
      | _ => none
  let candidate := !members.isEmpty && members.all Option.isSome
  let nesting : Core.ElementNesting := match cx.elemKind? with
    | none => .top
    | some k => if k == all && cx.elemDirect.contains (elemKey e) then .direct else .other
  let bodyCx := if candidate then
      { cx with elemGuards := cx.elemGuards ++ members.filterMap (·.map elemKey), elemKind? := some all
                elemDirect := cx.elemDirect ++ (elementSpine all body).toArray
                elemChain := (if nesting == .direct then cx.elemChain else #[])
                  ++ (bound.filter (·.2.2.2.isNone)).map (·.1) }
    else cx
  let values ← bound.filterMapM fun (_, ty, _, vs?) => vs?.mapM (·.mapM (elabProp · ty))
  let combos := values.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]]
  let localName (k : Nat) (bn : Name) (listed : Bool) : Name :=
    if listed then bn else .mkSimple s!"{bn.getString!}'{cx.binders.size + k}"
  withLocalDeclsD (bound.mapIdx fun k (bn, ty, _, vs?) => (localName k bn vs?.isSome, fun _ => pure ty)) fun fvs => do
    let new ← (bound.zip fvs).mapIdxM fun i ((bn, ty, _, vs?), fv) => do
      return { name := bn, term := ← exprToSyntax fv, «type» := ty, scrutinee := none, outer := cx.binders.size + i
               unbounded := vs?.isNone : MatchBinder }
    let listedFvs := (bound.zip fvs).filterMap fun ((_, _, _, vs?), fv) => vs?.map fun _ => fv
    let free := (bound.zip fvs).filterMap fun ((_, ty, pt, vs?), fv) => if vs?.isNone then some (fv, ty, pt) else none
    let outer := (← getLocal).indexes
    let outerTables := (← getLocal).tables
    modifyLocal fun l => { l with indexes := #[], tables := #[] }
    let mark := (← getLocal).boundMentions.size
    let t ← toTerm { bodyCx with binders := cx.binders ++ new, natOk := false, instances := cx.instances * combos.size } body
    -- Its verdict, from its bound names of types that are not listed, in
    -- order, as the `fren` command decides it.
    let verdict ← if !candidate then pure Core.ElementVerdict.notMembers else do
      let recorded := (← getLocal).elemMembers
      let inner := (declaredNames body).map Name.mkSimple
      let unbounded := bound.filter (·.2.2.2.isNone)
      let mut infos := #[]
      for (bn, _, _, _) in unbounded, m? in members, k in [0:unbounded.size] do
        let some m := m? | continue
        let seq := (recorded.find? (·.1 == elemKey m)).any (·.2.1)
        let earlier := (unbounded.extract 0 k).map (·.1) ++ (cx.binders.filter (·.unbounded)).map (·.name)
        infos := infos.push
          { members := if seq then .seq else .set
            receiverBound := (pathMentions m).any (earlier.contains ·.getRoot)
            uses := (← elementUses cx bn inner body).toList : Core.ElementBinder }
      -- What the quantifier mentions, once its own bound names are not.
      let chain := if nesting == .direct then cx.elemChain else #[]
      let bodyNames := (pathMentions body).filter fun n => !names.contains n.getRoot
      let boundNames := bodyNames.any fun n =>
        let r := n.getRoot
        !chain.contains r && (cx.binder? r).any (·.unbounded)
      let output ← mentionsOutputOf cx bodyNames
      pure (Core.elementVerdict nesting output boundNames infos.toList)
    let inCore := verdict == .inCore
    -- The reports that its guard's memberships deferred, and its binders'.
    let keys := members.filterMap (·.map elemKey)
    let deferred := (← getLocal).elemMembers.filter (keys.contains ·.1)
    modifyLocal fun l => { l with elemMembers := l.elemMembers.filter (!keys.contains ·.1) }
    unless inCore || cx.unmentioned do
      for (_, _, r?) in deferred do
        if let some (ref, msg) := r? then
          modifyLocal fun l => { l with outsideCore := true }
          recordLint .undecidable ref msg
      for b in unlisted do
        modifyLocal fun l => { l with outsideCore := true }
        recordLint .undecidable b ((Core.elementUndecidableMsg verdict).getD (Core.undecidableMsg .quantifier false))
    -- A bound name of a type that is not listed, with a domain, makes the
    -- queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`), unless the
    -- quantifier is expanded.
    if !inCore && bound.zipIdx.any (fun ((_, ty, _, vs?), k) => vs?.isNone && domainOf all names body k (ty.isConstOf ``Nat) != .unbounded) then
      modifyLocal fun l => { l with guardedUsed := true }
    -- Each bound name's number of values, 0 for a type that is not listed.
    if cx.noteIndexes then
      lintQuant e all binders ids (bound.map fun (bn, ty, _, _) => (bn, ty))
        (bound.map fun (_, _, _, vs?) => (vs?.map (·.size)).getD 0) body cx.binders.size mark
    checkTermType body t .bool (some s!"note: the body of `{if all then "forall" else "exists"}` is a `Bool`")
    let b ← elabProp t
    let inner ← (← getLocal).indexes.mapM fun (ref, g) => return (ref, ← elabProp g)
    let innerTables ← (← getLocal).tables.mapM fun (ref, q, g) => return (ref, q, ← elabProp g)
    let inst (x : Expr) (vals : Array Expr) : Expr := x.replaceFVars listedFvs vals
    -- Lean's `∀`, or `∃` unless `forall?`, over the bound names of types
    -- that are not listed, with what their types bring as a hypothesis or a
    -- conjunct, and without `have`s, which lean-smt does not translate.
    let bindFree (forall? : Bool) (x : Expr) : TermElabM Expr := do
      if free.isEmpty then return x
      -- A quantifier over elements in the core is marked, for each query
      -- to expand (`Fren.Elems`).
      let marked (q : Expr) : Expr := if inCore then Elems.mark free.size q else q
      let cons ← free.filterMapM fun (fv, ty, pt) => return (← factPred? ty pt).map (·.beta #[fv])
      let x ← zetaReduce x
      if forall? then
        return marked (← mkForallFVars (free.map (·.1)) (cons.foldr mkArrow' x))
      else
        return marked (← free.foldrM (init := cons.foldr mkAnd x) fun (fv, _, _) acc => do
          mkAppM ``Exists #[← mkLambdaFVars #[fv] acc])
    -- The names of enclosing `let`s and `where`s are locals here, which the
    -- `have`s that define them bind again: what mentions them is closed
    -- over them, and applied to their names.
    let lctx ← getLCtx
    let defs := cx.binders.filterMap fun d =>
      if d.isDef || d.closure then (lctx.findFromUserName? d.term.raw.getId).map (d.term, ·.toExpr) else none
    let close (x : Expr) : TermElabM Term := do
      let used := defs.filter fun (_, fv) => x.containsFVar fv.fvarId!
      if used.isEmpty then return ← exprToSyntax x
      let f ← exprToSyntax (← mkLambdaFVars (used.map (·.2)) x)
      `($f $(used.map (·.1))*)
    let goals ← inner.mapM fun (ref, g) => return (ref, ← close (← bindFree true (balanced mkAnd (combos.map (inst g)))))
    let tableGoals ← innerTables.mapM fun (ref, q, g) =>
      return (ref, q, ← close (← bindFree true (balanced mkAnd (combos.map (inst g)))))
    modifyLocal fun l => { l with indexes := outer ++ goals, tables := outerTables ++ tableGoals }
    close (← bindFree all (balanced (if all then mkAnd else mkOr) (combos.map (inst b))))
where
  /-- `p → q`, a non-dependent arrow. -/
  mkArrow' (p q : Expr) : Expr := .forallE `h p q .default

/-- `if c then a else b`, where `toTerm` translates its parts, which are
checked against a type if `emptyOk`, and are `Nat`s if `natOk` is. -/
def iteTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk natOk : Bool) (e c' a b : Syntax) :
    TermElabM Term := do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  if cx.noteIndexes && !cx.inElse then lintIfChain cx e
  -- Not where the condition's pattern tests bind names, which the `then`
  -- branch sees and the `else` branch does not, so that the same text may
  -- mean different values (`lang::test_scope`), as `sameBranches` decides.
  if cx.noteIndexes then lintSameBranches (← chainBinds cx c') e a b
  if cx.noteIndexes then
    let ms ← mentionedNames cx c'
    unless ms.isEmpty do
      modifyLocal fun l => { l with mentioning := l.mentioning.push (((unparen c').getPos?, (unparen c').getTailPos?), ms) }
  -- The names that the condition's pattern tests bind, which the `then`
  -- branch sees (`lang::test_scope`).
  let (c, new) ← withBound (toTerm { cx with inElse := false, testContext := .ifCondition } c')
  checkTermType c' c .bool (some "note: the condition of `if` is a `Bool`")
  let c ← propositionTerm c
  let gx ← Core.GuardedOperand.thenBranch.guard (pure c) `(¬$c)
  let gy ← Core.GuardedOperand.elseBranch.guard (pure c) `(¬$c)
  let seen (site : Core.TestSite) := if Core.binderVisible .ifCondition 0 1 site then new else #[]
  let cxa := { cx with emptyOk := Core.Position.shared.checked emptyOk (← synthesizes cx b), natOk, guards := cx.guards.push gx, inElse := false, expected?
                       binders := cx.binders ++ seen .body }
  let cxb := { cx with emptyOk := Core.Position.shared.checked emptyOk (← synthesizes cx a), natOk, guards := cx.guards.push gy, inElse := true, expected?
                       binders := cx.binders ++ seen .elseBranch }
  let (x, y) ← pairTerms toTerm cxa cxb a b
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
  if op == "*" then
    let (ma, mb) := (← mentionedNames cx a, ← mentionedNames cx b)
    unless cx.unmentioned || Core.productAccepted ma mb do
      throwError (Core.nonlinearMsg ma mb).text
    -- For `branches_sharing_code`, without parentheses, as `boolNode` has them.
    if cx.noteIndexes then
      let at_ (s : Syntax) := ((unparen s).getPos?, (unparen s).getTailPos?)
      modifyLocal fun l => { l with mentioning := l.mentioning ++ ([(ma, a), (mb, b)].filter (!·.1.isEmpty) |>.map fun (m, s) => (at_ s, m)) }
  let natOk := natOk && op != "-"
  let x ← toTerm { cx with natOk } a
  -- Of a newtype, its underlying type's `+` or `-`, on its field, which is
  -- the newtype's; of a number, a newtype on the right is the newtype's
  -- error, as the `fren` command checks (`lang::newtype_operator`).
  let tx? ← frenTypeOf? x
  if let some (.newtype p _) := tx? then
    let y ← toTerm cx b
    checkNewtypeOp op tx? (← frenTypeOf? y)
    -- `N(a.0 + b.0)`, through every newtype, each with its construction's
    -- obligation, from the innermost out.
    let st ← getState
    let chain := newtypeChain st (st.newtypes.get! p)
    let (fx, fy) := (← unwrapTerm chain x, ← unwrapTerm chain y)
    let sum ← if op == "+" then `($fx + $fy) else `($fx - $fy)
    return ← chain.foldrM (init := sum) fun n v => do
      noteObligation cx .construction (← getRef) ((n.shape.parts[0]?.bind (·[0]?)).getD default) v
      `($(mkCIdent n.ctor) $v)
  checkNumberTerm a x op
  let y ← toTerm { cx with natOk } b
  if let some (.newtype ..) ← frenTypeOf? y then checkNewtypeOp op tx? (← frenTypeOf? y)
  checkNumberTerm b y op
  if op == "-" then `((($x : Int) - ($y : Int))) else if op == "+" then `($x + $y) else `($x * $y)

open Lang in
/-- The expressions that `toTerm` gives no syntax pattern of its own:
quantifiers, fields, methods, `mod`, collections, indexes, records, `match`
and `is`, where
`toTerm` translates their parts, `emptyOk` and `natOk` are what is
expected of the whole, and `parent?` is the expression around it. -/
def otherTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (emptyOk natOk : Bool)
    (e : Syntax) : TermElabM Term := do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  if e.isOfKind ``Lang.quantExpr then return ← quantTerm toTerm cx e (isForall e) e[1].getArgs e[3]
  if let some e' := splitDotted? e then return ← toTerm { cx with expected? } e'
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
  else if e.isOfKind ``Lang.setExpr then setLitTerm toTerm { cx with expected? } emptyOk e
  else if e.isOfKind ``Lang.memberExpr || e.isOfKind ``Lang.subsetExpr || e.isOfKind ``Lang.unionExpr
      || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr || e.isOfKind ``Lang.joinExpr then setOpTerm toTerm { cx with emptyOk, expected? } e
  else if e.isOfKind ``Lang.pairExpr then throwError Core.pairPlaceMsg.text
  -- Only an argument for a function parameter (`lang::function_argument`).
  else if e.isOfKind ``Lang.closureExpr || e.isOfKind ``Lang.lambdaMatchExpr then throwError Core.closurePlaceMsg.text
  else if e.isOfKind ``Lang.seqExpr then seqLitTerm toTerm { cx with expected? } emptyOk e
  else if e.isOfKind ``Lang.indexExpr then indexTerm toTerm cx e
  else if e.isOfKind ``Lang.recordExpr then do
    let t ← recordTerm (fun x? => toTerm { cx with emptyOk := Core.Position.declared.checked false false, expected? := x?, natOk := x? == some .nat }) cx expected? e
    if let .item { kind := .recordItem, path, .. } ← resolvePath cx.modName (pathSegs e[0]) cx.shadowing then
      lintManualUpdate toTerm cx e path
    return t
  else if isMatchLike e then matchTerm toTerm { cx with emptyOk, natOk, expected? } e (parent?.bind (operandSlot · e))
  else if e.isOfKind ``Lang.tableExpr then tableTerm toTerm { cx with emptyOk, natOk, expected? } e (parent?.bind (operandSlot · e))
  else if e.isOfKind ``Lang.isExpr then isTerm toTerm cx e
  else if e.isOfKind ``Lang.updateExpr then do
    let t ← updateTerm toTerm cx e
    lintUpdate toTerm cx e
    return t
  else if e.isOfKind ``Lang.noArgsCardinalityExpr then
    -- The operator's name, a non-reserved token, perhaps under the node of
    -- its alternatives.
    let leaf := if e[0].isAtom || e[0].isIdent then e[0] else e[0][0]
    let n := if leaf.isIdent then leaf.getId.toString else leaf.getAtomVal.trimAscii.toString
    let some c := Core.Cardinality.ofName? n | throwError "internal error: no cardinality operator `{n}`"
    -- A variable that shadows it is reported first, as for any application.
    if cx.vars.any (·.name == Name.mkSimple n) || (cx.binder? (Name.mkSimple n)).isSome then
      throwErrorAt e[0] (Core.varNotAFunctionMsg (Name.mkSimple n)).text
    throwError (Core.cardinalityNoArgsMsg c).text
  else throwError "unsupported Fren expression"

/-- Only source guards distribute Boolean clauses; quantified bodies remain one clause. -/
def isBooleanGuard (e : Syntax) : Bool := isConditional e && !e.isOfKind ``Lang.quantExpr

/-- Split the delimiter of a root infix labelled conjunction. A label's
body keeps ordinary Boolean precedence until the next `and label:`. -/
partial def splitNamedTail (e : Syntax) : Syntax × Option Syntax :=
  if isBinOp e "and" && e[2].isOfKind ``Lang.labelledExpr then (e[0], some e[2])
  else if isBinOp e "and" || isBinOp e "or" || isBinOp e "iff" then
    let (body, next) := splitNamedTail e[2]
    (e.setArg 2 body, next)
  else if isConditional e then
    let (body, next) := splitNamedTail e[3]
    (e.setArg 3 body, next)
  else (e, none)

/-- A prefix block or the root infix labelled-conjunction spelling. -/
partial def booleanBlockView (source : Syntax) : Option (String × Array (Option Syntax × Syntax)) := Id.run do
  let e := unparen source
  if e.isOfKind ``Lang.booleanBlockExpr then
    let keyword := if e[0].isAtom then e[0] else e[0][0]
    return some (keyword.getAtomVal.trimAscii.toString, e[2].getSepArgs.map fun member =>
      (if member[0].isNone then none else some member[0][0], member[1]))
  if e.isOfKind ``Lang.labelledExpr then
    let (head, tail) := splitNamedTail e[2]
    let rest := tail.bind booleanBlockView |>.map (·.2) |>.getD #[]
    return some ("and", #[(some e[0], head)] ++ rest)
  return none

open Lang in
/-- Lower Boolean blocks through existing guarded operators. In particular
n-ary equivalence has two branches, never left-associated binary parity. -/
def lowerBooleanBlock (op : String) (members : Array (Option Syntax × Syntax)) : TermElabM Syntax := do
  let truth ← `(fren_expr| true)
  let falsity ← `(fren_expr| false)
  let fold (op : String) (xs : Array Syntax) : TermElabM Syntax := do
    let mut value : Syntax := if op == "and" then truth else falsity
    for e in xs.reverse do
      value ← if op == "and" then do `(fren_expr| $(⟨e⟩):fren_expr and $(⟨value⟩):fren_expr)
               else do `(fren_expr| $(⟨e⟩):fren_expr or $(⟨value⟩):fren_expr)
    return value
  let values := members.map (·.2)
  if op == "one" then
    let mut noneSeen := falsity
    let mut oneSeen := truth
    for e in values.reverse do
      let nextNone ← `(fren_expr| if $(⟨e⟩):fren_expr then $(⟨oneSeen⟩):fren_expr else $(⟨noneSeen⟩):fren_expr)
      oneSeen ← `(fren_expr| if $(⟨e⟩):fren_expr then false else $(⟨oneSeen⟩):fren_expr)
      noneSeen := nextNone
    return noneSeen
  if op != "iff" then return ← fold op values
  if values.size <= 1 then return truth
  let first : TSyntax `fren_expr := ⟨values[0]!⟩
  let rest := values.extract 1
  let yes ← fold "and" rest
  let negatives ← rest.mapM fun e => do `(fren_expr| not $(⟨e⟩):fren_expr)
  let no ← fold "and" (negatives.map (·.raw))
  return ← `(fren_expr| if $first then $(⟨yes⟩):fren_expr else $(⟨no⟩):fren_expr)

open Lang in
/-- Translates a Fren expression to a Lean term, resolving names with Fren's
rules. Variables become references to locals of the same name; variants
become references to the generated constructors. -/
partial def toTerm (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  if e.isOfKind choiceKind && e.getArgs.any (·.isOfKind ``Lang.booleanBlockExpr) then
    return ← toTerm cx (unparen e)
  if let some (op, members) := booleanBlockView e then
    if op == "iff" && members.size <= 1 then
      for (_, member) in members do
        discard (boolOperand toTerm { cx with noteIndexes := false, expected? := some .bool } "iff" member)
    let labels := members.filterMap (·.1)
    if let some k := (Core.repeatsAt (labels.map (·.getId)))[0]? then
      throwErrorAt labels[k]! "a Boolean block repeats label `{labels[k]!.getId}`"
    let before := (← getLocal).indexes.size
    let beforeTables := (← getLocal).tables.size
    let term ← toTerm cx (← lowerBooleanBlock op members)
    if op == "one" || op == "iff" then
      -- Only these decision-tree lowerings duplicate a written operation.
      -- Do not merge ordinary let/table uses elsewhere in a procedure.
      let marked (ref : Syntax) := if ref.isOfKind `Fren.booleanSiteRef then ref else mkNode `Fren.booleanSiteRef #[ref]
      modifyLocal fun l => { l with
        indexes := l.indexes.extract 0 before ++ (l.indexes.extract before).map (fun (ref, goal) => (marked ref, goal))
        tables := l.tables.extract 0 beforeTables ++ (l.tables.extract beforeTables).map (fun (ref, question, goal) => (marked ref, question, goal)) }
    return term
  let concatOk := cx.concatOk
  let emptyOk := cx.emptyOk
  let natOk := cx.natOk
  let expected? := cx.expected?
  -- An operand of `or` or `and` continues its chain only if it is one too.
  let parent? := cx.parent?
  -- Only `and`, `is` and parentheses read where their chain is (`lang::test_scope`).
  let test := (cx.testContext, cx.testAt?)
  let cx := { cx with concatOk := false, emptyOk := false, natOk := false, expected? := none
                      chain := if isBinOp (unparen e) cx.chain then cx.chain else ""
                      parent? := some e, inElse := cx.inElse && isIte (unparen e)
                      testContext := .standalone, testAt? := none }
  let go := toTerm cx
  -- A chained comparison's comparisons are not operators of their own here.
  if cx.noteIndexes && (chainOf? e).isNone then lintEqOp cx e
  if let some (xs, ops) := chainOf? e then return ← chainTerm toTerm cx e xs ops
  match e with
  | `(fren_expr| when $c, $d) => guardedTerm toTerm cx c d .whenBody
  | `(fren_expr| unless $c, $d) => guardedTerm toTerm cx c d .unlessBody
  | `(fren_expr| $a iff $b) => `($(← boolOperand toTerm cx "iff" a) ↔ $(← boolOperand toTerm cx "iff" b))
  | `(fren_expr| $a or $b) => guardedTerm toTerm cx a b .orRight (op := .or)
  | `(fren_expr| $a and $b) => guardedTerm toTerm cx a b .andRight (op := .and) (test := test)
  | `(fren_expr| not $a) => `(¬$(← boolOperand toTerm { cx with testContext := .notOperand } "not" a))
  | `(fren_expr| if $c' then $a else $b) => iteTerm toTerm { cx with expected? } emptyOk natOk e c' a b
  | `(fren_expr| $_ = $_) | `(fren_expr| $_ != $_) | `(fren_expr| $_ < $_) | `(fren_expr| $_ <= $_)
  | `(fren_expr| $_ > $_) | `(fren_expr| $_ >= $_) => compareTerm toTerm cx e
  | `(fren_expr| $_ ++ $_) => concatTerm toTerm { cx with emptyOk, expected? } concatOk e
  | `(fren_expr| $s:str) =>
    liftMsg s (Core.checkStringChars s.getString)
    `(Fren.Str.lit $s)
  | `(fren_expr| $a + $b) => arithTerm toTerm cx natOk "+" a b
  | `(fren_expr| $a - $b) => arithTerm toTerm cx natOk "-" a b
  | `(fren_expr| $a * $b) => arithTerm toTerm cx natOk "*" a b
  | `(fren_expr| $_ div $_) => divTerm toTerm cx e "div" natOk
  | `(fren_expr| -$a) =>
    let x ← go a
    unless (← getState).newtypes.isEmpty do
      let tx? ← frenTypeOf? x
      checkNewtypeOp "-" tx? tx? (pre := true)
    checkNumberTerm a x "-"
    `((-($x : Int)))
  | `(fren_expr| $_ == $_) | `(fren_expr| $_ && $_) | `(fren_expr| $_ || $_) | `(fren_expr| $_ | $_) =>
    throwErrorAt e[1] (Core.foreignOpMsg e[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| !$_) => throwErrorAt e[0] (Core.foreignOpMsg "!").text
  | `(fren_expr| $_ <- $_) => throwErrorAt e[1] Core.leftArrowMsg.text
  -- Checked against the whole's type, if it is (`lang::checked`).
  | `(fren_expr| ($a)) =>
    let inner ← toTerm { cx with concatOk, natOk, expected?, emptyOk := Core.Position.shared.checked emptyOk false,
                                 testContext := test.1, testAt? := test.2 } a
    `(($inner))
  | `(fren_expr| $n:num) => if natOk then `(($n : Nat)) else `(($n : Int))
  | `(fren_expr| true) => `(true)
  | `(fren_expr| false) => `(false)
  | `(fren_expr| $p:fren_path) => pathTerm toTerm cx parent? e p expected?
  | `(fren_expr| $p:fren_path($args,*)) => appTerm toTerm { cx with natOk } parent? e p args expected?
  | _ =>
    if e.isOfKind ``Lang.letExpr then letTerm toTerm { cx with natOk } emptyOk concatOk e
    -- Only `is` reads where its chain is, and its operand does not see it.
    else otherTerm toTerm { cx with expected?, testContext := test.1, testAt? := test.2 } parent? emptyOk natOk e

open Lang in
/-- The conditions of a top-level `when`/`unless` chain, as a term, and a
syntax node spanning them. -/
partial def triggerOf (cx : ExprCtx) (e : Syntax) : TermElabM (Option (Term × Syntax)) := do
  -- Through a `let` or `where`, whose names stand for their definitions.
  if e.isOfKind ``Lang.letExpr then
    let defs := e[1].getSepArgs
    let saved ← saveState
    let r ← withDefinitions toTerm { cx with noteIndexes := false } defs (defs.all (·.isOfKind ``Lang.fren_let_def))
        (usedDefinitions defs e[3]) fun bcx binds => do
        let some (t, ref) ← triggerOf bcx e[3] | return none
        return some (← haves binds t, ref)
    saved.restore
    return r
  let (cond, neg, body) ← match e with
    | `(fren_expr| when $c, $d) => pure (c, false, d)
    | `(fren_expr| unless $c, $d) => pure (c, true, d)
    | `(fren_expr| ($a)) => return ← triggerOf cx a
    | _ => return none
  -- With the names that its pattern tests bind, which the body may see
  -- (`lang::test_scope`).
  let context : Core.TestContext := if neg then .unlessCondition else .whenCondition
  let (c, new) ← withBound (toTerm { cx with noteIndexes := false, testContext := context } cond)
  let c ← if neg then `(¬$c) else pure c
  let seen := if Core.binderVisible context 0 1 .body then new else #[]
  match ← triggerOf { cx with binders := cx.binders ++ seen } body with
  | none => return some (c, mkNullNode #[e[0], cond])
  | some (t, ref) => return some (← `($c ∧ $t), mkNullNode #[e[0], ref])

open Lang in
/-- The expression `e` with its optional `fren_where` `w?`, as the `let` it
means (`Reqs/Lang/Let`), whose definitions are `fren_def`s rather than
`fren_let_def`s. Its `let` has the position of `e`'s first token, so that
it spans `e` in the source. -/
def withWhere (e w? : Syntax) : Syntax :=
  if w?.getNumArgs == 0 then e else
  let w := w?[0]
  mkNode ``Lang.letExpr #[Syntax.atom e.getHeadInfo "let", w[1], w[0], e]

/-- An assumption, requirement, expectation or cover goal: its kind, its name, and its
expression, with its `where` clause. -/
def constraint? (m : Syntax) : Option (PropKind × Syntax × Syntax) :=
  -- A member that failed to parse may lack its last parts.
  if m.getNumArgs < 4 || m.getNumArgs > 5 || !m[0].isAtom then none else
  let kind? := match m[0].getAtomVal.trimAscii.toString with
    | "assume" => some PropKind.assume
    | "ensure" => some .ensure
    | "expect" => some .expect
    | "cover" => some .cover
    | _ => none
  kind?.map (·, m[1], withWhere m[3] m[4])

/-- A defined output's definition, with its `where` clause. -/
def definition? (m : Syntax) : Option Syntax :=
  if m[5].isNone then none else some (withWhere m[5][1] m[5][2])

/-- The indexes and tables recorded since the last call, which it forgets,
each with its goal elaborated, rewritten by `subst`, and closed over `fvs`. -/
def takeIndexes (fvs : Array Expr) (subst : Expr → Expr := id) :
    TermElabM (Array (Syntax × Option Core.TableGoal × Expr)) := do
  let xs := (← getLocal).indexes
  let ts := (← getLocal).tables
  modifyLocal fun l => { l with indexes := #[], tables := #[] }
  let sites ← (xs.mapM fun (ref, g) => return (ref, none, subst (← elabProp g)))
    >>= fun indices => return indices ++ (← ts.mapM fun (ref, q, g) => return (ref, some q, subst (← elabProp g)))
  let mut unique : Array (Syntax × Option Core.TableGoal × Expr) := #[]
  for (ref, question, goal) in sites do
    -- A decision tree may translate one source operation along several
    -- paths. Their obligations are guard implications: their conjunction
    -- asks about that source operation under the union of its reach guards.
    let same := if !ref.isOfKind `Fren.booleanSiteRef then none else
      unique.findIdx? fun (previous, previousQuestion, previousGoal) =>
        previous.isOfKind `Fren.booleanSiteRef && ref[0].getPos?.isSome
          && ref[0].getPos? == previous[0].getPos? && ref[0].getTailPos? == previous[0].getTailPos?
          && question == previousQuestion && obligationTy? goal == obligationTy? previousGoal
    if let some i := same then
      let (previous, previousQuestion, previousGoal) := unique[i]!
      unique := unique.set! i (previous, previousQuestion, mkAnd previousGoal goal)
    else unique := unique.push (ref, question, goal)
  unique.mapM fun (ref, question, goal) =>
    return (if ref.isOfKind `Fren.booleanSiteRef then ref[0] else ref, question, ← mkLambdaFVars fvs goal)

/-- Runs `k`, then puts back the name generators, the macro scopes and the
metavariables and Lean's caches as they were before it, so that what is elaborated after it
is named as it would be without it: the solver's queries, and so the
checks' messages, depend on those names (`Reqs/Generated#matches`). What
`k` returns must not mention its metavariables or locals. -/
def keepingNames (k : TermElabM α) : TermElabM α := do
  let s ← getThe Core.State
  -- Its caches too, which may have seen the locals whose names are reused,
  -- and the elaborator's pending metavariables.
  let m ← getThe Meta.State
  let t ← getThe Term.State
  try k finally
    set m
    set t
    modifyThe Core.State fun t => { t with nextMacroScope := s.nextMacroScope, ngen := s.ngen }

/-- What compiled code that applies the constant `c` needs of it
(`Mention`): a proof, which is erased, needs nothing. -/
def mentionOf (c : Name) : MetaM Mention := do
  if c == ``Classical.propDecidable then return .classicalDecision
  if isNoncomputable (← getEnv) c then return .noncomputableDecl
  match (← getEnv).find? c with
  | some (.axiomInfo a) => return if ← isProp a.type then .computable else .dataAxiom
  | _ => return .computable

/-- Compiles the generated definition `name`, of type `type` and value
`value`, or marks it `noncomputable`, as `definitionForm` says from what
its value mentions (`Reqs/Generated#computable-definitions`). Compiled
synchronously, so that a definition that Lean's compiler rejects, which
the rule says it does not, is an error here. -/
def compileGenerated (name : Name) (type value : Expr) : TermElabM Unit := keepingNames do
  let kind : ValueKind ← forallTelescope type fun _ r => return if r.isProp then .proposition else .data
  -- A proposition's mentions do not matter.
  let mentions ← if kind == .proposition then pure #[] else
    (value.foldConsts #[] fun c acc => acc.push c).mapM (liftM <| mentionOf ·)
  match definitionForm kind mentions with
  | .notCompiled => pure ()
  | .markedNoncomputable => modifyEnv (addNoncomputable · name)
  | .compiled => withOptions (Elab.async.set · false) (compileDecls #[name])

/-- Adds the definition `name` of the closed `value`, generalized over the
placeholders `uses` (`Reqs/Generated#procedures`), compiled unless
`compile` is false (`compileGenerated`). -/
def addUsesDef (uses : Array Name) (name : Name) (value : Expr) (compile := true) : TermElabM Unit := do
  let type ← inferType value
  let (type, value) ← withUses uses fun xs => do
    return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs value))
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  -- Reducible, like `abbrev`, so that instances such as `Decidable` see
  -- through them.
  setReducibleAttribute name
  if compile then compileGenerated name type value

/-- The name under which a defined function's Lean definition is
elaborated, `decl`'s, so that its matchers are named under it, before
`addLeanDef` adds them under `decl`: not a Fren name, which has no `#`. -/
def leanDeclName (decl : Name) : Name := decl.str "#lean"

/-- Adds the definition `name` of the closed `value`, a defined function's
Lean definition, generalized over the placeholders `uses`, as `addUsesDef`
does: with each of the matchers of its Lean `match`es, which Lean added
under `leanDeclName name` over the placeholders, added again under `name`,
generalized over them too, and registered as a matcher, so that `split`,
`simp` and `#print` see a `match` (`Reqs/Generated#matches`). -/
def addLeanDef (uses : Array Name) (name : Name) (value : Expr) : TermElabM Unit := do
  let tmp := leanDeclName name
  let ms := value.foldConsts #[] fun c acc => if c.getPrefix == tmp && !acc.contains c then acc.push c else acc
  let mut value := value
  for m in ms do
    let some info ← Meta.getMatcherInfo? m | throwError "internal error: `{m}` is not a matcher"
    let .defnInfo ci ← getConstInfo m | throwError "internal error: `{m}` is not a definition"
    let m' := name ++ Name.mkSimple m.getString!
    let (type, val) ← withUses uses fun xs => do
      return (← mkForallFVars xs (replaceUses uses xs ci.type), ← mkLambdaFVars xs (replaceUses uses xs ci.value))
    addDecl (.defnDecl { name := m', levelParams := ci.levelParams, type, value := val, hints := ci.hints, safety := .safe })
    Meta.Match.addMatcherInfo m' { info with numParams := info.numParams + uses.size }
    setInlineAttribute m'
    let args := uses.map (Lean.mkConst ·)
    value := value.replace fun e => match e with
      | .const c ls => if c == m then some (mkAppN (.const m' ls) args) else none
      | _ => none
  addUsesDef uses name value

/-- Adds the recursive definition `name` of type `type` and value `value`,
which mentions `name`, as Lean's `def` adds one, by its structural
recursion, compiled where `definitionForm` says that it is
(`Reqs/Generated#computable-definitions`). -/
def addRecursiveDef (ref : Syntax) (name : Name) (type value : Expr) : TermElabM Unit := do
  let kind : ValueKind ← forallTelescope type fun _ r => return if r.isProp then .proposition else .data
  let mentions ← if kind == .proposition then pure #[] else
    ((value.foldConsts #[] fun c acc => if c == name then acc else acc.push c).mapM (liftM <| mentionOf ·))
  let computeKind := if definitionForm kind mentions == .compiled then .regular else .noncomputable
  addPreDefinitions ({}, {}) #[{ ref, kind := .def, levelParams := [], modifiers := { computeKind }, declName := name
                                 binders := .missing, type, value, termination := .none }]

/-- Adds a structural recursion's two definitions
(`lang::structural_recursion`), from `recLean`, its Lean definition's value
over itself first, with the placeholders `uses` as themselves and its
`match`es Lean's, whose matchers are under `leanDeclName decl`: the
solver's, `solverName decl`, as it is (`DefinedInfo.recursive`); and
`decl`, generalized over the placeholders, with the matchers added again
under `decl`, as `addLeanDef` adds them. Lean's structural recursion
accepts each. -/
def addRecursiveDefs (ref : Syntax) (uses : Array Name) (decl : Name) (recLean : Expr) : TermElabM Unit := do
  let type := recLean.bindingDomain!
  let solver := solverName decl
  -- The solver's, with the defined functions that it applies unfolded, as
  -- a query's are (`Fren.unfoldDefined`), but the structural recursions.
  let st ← getState
  let ds := st.defined.foldl (init := ({} : NameSet)) fun acc _ d => acc.insert d.decl
  let sv ← Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined st (recLean.beta #[Lean.mkConst solver]) ds.contains))
  addRecursiveDef ref solver type sv
  let tmp := leanDeclName decl
  let ms := recLean.foldConsts #[] fun c acc => if c.getPrefix == tmp && !acc.contains c then acc.push c else acc
  let args := uses.map (Lean.mkConst ·)
  let mut value := recLean.beta #[mkAppN (Lean.mkConst decl) args]
  for m in ms do
    let some info ← Meta.getMatcherInfo? m | throwError "internal error: `{m}` is not a matcher"
    let .defnInfo ci ← getConstInfo m | throwError "internal error: `{m}` is not a definition"
    let m' := decl ++ Name.mkSimple m.getString!
    let (mty, mval) ← withUses uses fun xs => do
      return (← mkForallFVars xs (replaceUses uses xs ci.type), ← mkLambdaFVars xs (replaceUses uses xs ci.value))
    addDecl (.defnDecl { name := m', levelParams := ci.levelParams, type := mty, value := mval, hints := ci.hints, safety := .safe })
    Meta.Match.addMatcherInfo m' { info with numParams := info.numParams + uses.size }
    setInlineAttribute m'
    -- Lean's equation lemmas of the recursion are realized from it.
    enableRealizationsForConst m'
    value := value.replace fun e => match e with
      | .const c ls => if c == m then some (mkAppN (.const m' ls) args) else none
      | _ => none
  let body := value
  let (gType, gValue) ← withUses uses fun xs => do
    return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs body))
  addRecursiveDef ref decl gType gValue

/-! ## Abstract types and functions -/

/-- Records the questions about the tables and applications of the body
and contract of the function at `path`, whose parameters are `vars`, or of
the value of the constant at `path`, `tables`, with its preconditions and
postconditions, `props`, as a procedure for their checks (`Entry.bodyInfo`), if
it has any questions or postconditions to check (`Core.bodyKinds`). -/
def recordBody (path : Name) (ref : Syntax) (decl : Name) (vars : Array Var)
    (tables : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)) (props : Array PropInfo := #[])
    (fn? : Option Name := none) : TermElabM Unit := do
  if tables.isEmpty && !props.any (·.kind == .ensure) then return
  let uses ← usesOf (tables.map (·.2.2.2.2) ++ props.map (·.body))
  let info : CompInfo := { path := path.getPrefix, vars, props, ref, decl, uses, fn?
                           decidable := !(← getLocal).outsideCore, guarded := (← getLocal).guardedUsed
                           indexes := tables }
  record (.bodyInfo path info)
  modifyLocal fun l => { l with bodies := l.bodies.push path }.declared path

/-- Declares the placeholder for the abstract type or function at `path`
(`AbstractInfo`). -/
def declarePlaceholder (path : Name) (type : Expr) (isType : Bool) (ptys : Array Core.PTy × Core.PTy := (#[], default))
    (fact? : Option Expr := none) (typeParams : Array Name := #[]) (declared : Array Core.Ty := #[])
    (result : Core.Ty := .bool) (resultP : Core.PTy := default) : TermElabM Unit := do
  let placeholder := placeholderName path
  addDecl (.axiomDecl { name := placeholder, levelParams := [], type, isUnsafe := false })
  let s ← getState
  let deps := type.foldConsts #[] fun c acc => if s.placeholders.contains c && !acc.contains c then acc.push c else acc
  record (.abstractInfo { path, placeholder, isType, deps, ptys, fact?, typeParams, declared, result, resultP
                          module := ← getMainModule })
  -- An abstract type has a value, so its placeholder has an `Inhabited`
  -- instance, itself a placeholder, which an index of a sequence of it
  -- needs; an implementation gives the interpretation's own.
  if isType then
    let inst := inhabitedName placeholder
    let instType := mkApp (Lean.mkConst ``Inhabited [Level.one]) (Lean.mkConst placeholder)
    addDecl (.axiomDecl { name := inst, levelParams := [], type := instType, isUnsafe := false })
    addInstance inst .global 1000
    record (.abstractInfo { path := inhabitedName path, placeholder := inst, isType := false, deps := #[placeholder] })

/-- `t`, over the placeholders of the type parameters `tps` of the generic
function at `path` and of their `Inhabited` instances, as a type that takes
a `Type` and an instance of it for each, first (`typeParamPlaceholders`):
the type of the placeholder of a generic function without a body
(`Reqs/Generated#generic-functions`). -/
def withTypeParams (path : Name) (tps : Array Name) (t : Expr) : TermElabM Expr :=
  go 0 #[]
where
  go (k : Nat) (xs : Array Expr) : TermElabM Expr := do
    if h : k < tps.size then
      withLocalDeclD (Name.mkSimple tps[k].toString) (mkSort Level.one) fun x =>
        withLocalDecl (Name.mkSimple "#inhabited") .instImplicit (mkApp (Lean.mkConst ``Inhabited [Level.one]) x) fun i =>
          go (k + 1) (xs ++ #[x, i])
    else mkForallFVars xs (atInstance path tps xs t)

@[command_elab Lang.typeCmd] def elabAbstractType : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  -- A type alias names a type (`Reqs/Lang/Items#type-aliases`).
  unless stx[3].isNone do
    let n ← checkItemName "type alias" nameStx
    checkFresh modName n nameStx
    lintName .typeAlias n nameStx
    let (t, pt) ← liftTermElabM (elabPType modName stx[3][1])
    lintRelTypes modName stx[3][1]
    record (.item { item := { kind := .typeItem, path := modName ++ n, isPub, owner := modName }, ref := nameStx })
    record (.aliasInfo (modName ++ n) t pt)
    unless isPub do recordItem .typeAlias (modName ++ n) nameStx
    return
  let n ← checkItemName "abstract type" nameStx
  checkFresh modName n nameStx
  lintName .abstractType n nameStx
  let path := modName ++ n
  liftTermElabM <| declarePlaceholder path (mkSort (.succ .zero)) true
  record (.item { item := { kind := .typeItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .abstractType path nameStx

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
parameters' and result's types are neither `Nat`s, pattern types nor
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

open Lang in
/-- Source Boolean alternatives over the same closed variables as a clause.
Leading guards are distributed into each member, retaining exact owner
meaning; diagnostic-only translation records no duplicate obligations. -/
partial def clauseBranchGroups (cx : ExprCtx) (owner : Name) (expression : Syntax)
    (fvs : Array Expr) (subst : Expr → Expr := id) : TermElabM (Array (Core.BranchGroup Expr)) := do
  let rec strip (e : Syntax) (wrappers : Array Syntax) : TermElabM (Array (Core.BranchGroup Expr)) := do
    let e := unparen e
    if isBooleanGuard e || e.isOfKind ``Lang.letExpr then
      return ← strip e[3] (wrappers.push e)
    let group? := (booleanBlockView e).orElse fun _ =>
      if isBinOp e "iff" then some ("iff", #[(none, e[0]), (none, e[2])]) else none
    let some (op, members) := group? | return #[]
    if op != "or" && op != "iff" && op != "one" then return #[]
    if op == "iff" && members.size <= 1 then return #[]
    let saved ← getLocal
    try
      let source := (← getFileMap).source
      let members ← members.mapIdxM fun i (label, body) => do
        let segment := label.map (fun label => label.getId.toString (escape := false)) |>.getD (toString (i + 1))
        let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString (escape := false) ++ "." ++ segment)
        let guarded := wrappers.foldr (fun wrapper body => wrapper.setArg 3 body) body
        let value ← elabProp (← toTerm { cx with noteIndexes := false } guarded)
        let formula ← mkLambdaFVars fvs (subst value)
        let text := exactText body
        return { name, formula
                 range? := some (charRange source (label.getD body)), text : Core.BranchMember Expr }
      -- Recover activation from the already elaborated wrapper, avoiding a
      -- second elaboration of generated contract lets with hygienic binders.
      let guard? ← if !wrappers.any isBooleanGuard then pure none else do
        let wrapped ← if let some first := members[0]? then pure (first.formula.beta fvs) else do
          let original := wrappers.foldr (fun wrapper body => wrapper.setArg 3 body) e
          pure (subst (← elabProp (← toTerm { cx with noteIndexes := false } original)))
        let first ← zetaReduce wrapped
        let rec conditions (remaining : Nat) (body : Expr) : MetaM (List Expr) := do
          if remaining == 0 then return []
          if let .forallE _ condition tail _ := body.consumeMData then
            if !tail.hasLooseBVars && (← isProp condition) then
              return condition :: (← conditions (remaining - 1) tail)
          return []
        let active ← conditions (wrappers.filter isBooleanGuard).size first
        pure (some (← mkLambdaFVars fvs (mkAndN active)))
      return #[{ owner, guard?, kind := if op == "or" then .disjunction else if op == "one" then .exactlyOne else .equivalence, members }]
    finally modifyLocal fun _ => saved
  strip expression #[]

open Lang in
/-- Observe raw members only under their source evaluation guards. This
metadata is evaluated in the actual primary model, not by a fresh query. -/
partial def clauseMemberGroups (cx : ExprCtx) (owner : Name) (expression : Syntax)
    (fvs : Array Expr) (subst : Expr → Expr := id) : TermElabM (Array (Core.MemberGroup Expr)) := do
  let rec strip (e : Syntax) (wrappers : Array Syntax) (wanted : Bool) : TermElabM (Array (Core.MemberGroup Expr)) := do
    let e := unparen e
    if isBooleanGuard e || e.isOfKind ``Lang.letExpr then return ← strip e[3] (wrappers.push e) wanted
    if e.getNumArgs == 2 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "not" then
      return ← strip e[1] wrappers (!wanted)
    let group? := booleanBlockView e
    let some (op, members) := group? | return #[]
    let saved ← getLocal
    try
      let source := (← getFileMap).source
      let mut out := #[]
      for (label, body) in members, i in [0:members.size] do
        let mut conditions : Array Syntax := #[]
        for previous in [0:i] do
          if op == "iff" && previous == 0 then continue
          let previousBody := members[previous]!.2
          let condition ← if op == "or" then `(fren_expr| not $(⟨previousBody⟩):fren_expr)
            else if op == "iff" then `(fren_expr| $(⟨members[0]!.2⟩):fren_expr iff $(⟨previousBody⟩):fren_expr)
            else pure (⟨previousBody⟩ : TSyntax `fren_expr)
          conditions := conditions.push condition
        let mut guard ← lowerBooleanBlock "and" (conditions.map (none, ·))
        if op == "one" then
          let prior := members.extract 0 i
          let atMostOne ← lowerBooleanBlock "one" prior
          let noneTrue ← lowerBooleanBlock "and" (← prior.mapM fun (_, e) => do
            let neg ← `(fren_expr| not $(⟨e⟩):fren_expr)
            pure (none, neg.raw))
          guard ← `(fren_expr| $(⟨noneTrue⟩):fren_expr or $(⟨atMostOne⟩):fren_expr)
        let skipped := op == "iff" && members.size <= 1
        if skipped then guard ← `(fren_expr| false)
        let mut value : Syntax ← if skipped then do `(fren_expr| true) else pure body
        for wrapper in wrappers.reverse do
          value := wrapper.setArg 3 value
          if wrapper.isOfKind ``Lang.letExpr then guard := wrapper.setArg 3 guard
          else
            let condition := wrapper[1]
            guard ← if wrapper[0].getAtomVal.trimAscii.toString == "unless" then
                `(fren_expr| not $(⟨condition⟩):fren_expr and $(⟨guard⟩):fren_expr)
              else `(fren_expr| $(⟨condition⟩):fren_expr and $(⟨guard⟩):fren_expr)
        let raw ← elabProp (← toTerm { cx with noteIndexes := false } value)
        let reachable ← elabProp (← toTerm { cx with noteIndexes := false } guard)
        let raw ← mkLambdaFVars fvs (subst raw)
        let reachable ← mkLambdaFVars fvs (subst reachable)
        let segment := label.map (·.getId.toString) |>.getD (toString (i + 1))
        out := out.push { name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString ++ "." ++ segment), formula := raw
                          valueFormula? := some raw, evaluationGuard? := some reachable
                          range? := some (charRange source (label.getD body)), text := exactText body : Core.BranchMember Expr }
      return #[{ owner, op, wanted, members := out }]
    finally modifyLocal fun _ => saved
  strip expression #[] true

/-- Root source conjunctions of predicates, with leading wrappers kept
on each leaf. Ordinary conjunctions inside a leaf are not reinterpreted. -/
partial def predicateConjunction (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then predicateConjunction e[3]
  else (booleanBlockView e).any (·.1 == "and")

partial def predicateLeafSources (owner : Name) (source : Syntax) : TermElabM (Array (Name × Syntax × Syntax)) := do
  let e := unparen source
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then
    return (← predicateLeafSources owner e[3]).map fun (name, ref, body) => (name, ref, e.setArg 3 body)
  if let some ("and", members) := booleanBlockView e then
    let labels := members.filterMap (·.1)
    if let some k := (Core.repeatsAt (labels.map (·.getId)))[0]? then
      throwErrorAt labels[k]! "a Boolean block repeats label `{labels[k]!.getId}`"
    for label in labels do
      discard (segName label)
      liftMsg label (Core.checkNoBang label.getId)
    let mut out := #[]
    for (label, body) in members, i in [0:members.size] do
      let segment := label.map (·.getId.toString (escape := false)) |>.getD (toString (i + 1))
      let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString (escape := false) ++ "." ++ segment)
      let leaves ← predicateLeafSources name body
      out := out ++ leaves.map fun (n, ref, value) => (n, if n == name then label.getD ref else ref, value)
    return out
  return #[(owner, source, source)]

partial def predicateNamedRoot (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  let e := unparen e
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then return ← predicateNamedRoot cx e[3]
  if !e.isOfKind ``Lang.appExpr then return false
  let segs := pathSegs e[0]
  if let .ok (.item { kind := .fnItem, path, .. }) := (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing then
    return ((← getState).defined.find? path).any (fun info => !info.namedMembers.isEmpty || !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty)
  return false

/-- Metadata is elaborated again in the definition's own lexical scope and
closed over typed parameters. Callers instantiate lambdas, never substitute
raw source identifiers into their own scope. -/
def predicateMetadata (scope : Name) (vars : Array Var)
    (functions : Array (Name × Core.FnTy × Expr × Name)) (body : Syntax) :
    TermElabM (Array PredicateMemberInfo × Array (Core.BranchGroup Expr) × Array (Core.MemberGroup Expr)) := do
  let saved ← getLocal
  try
    withLocalDeclsD (functions.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
    withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let all := fvs ++ fnFvs
      let cx : ExprCtx := {
        modName := scope, vars, insts := #[], place := .prop
        fnParams := functions.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)) }
      let mut members := #[]
      if predicateConjunction body || (← predicateNamedRoot cx body) then
        for (name, ref, expression) in ← predicateLeafSources .anonymous body do
          discard (takeIndexes all)
          let statement ← elabProp (← toTerm cx expression)
          let sites ← takeIndexes all
          let branchGroups ← clauseBranchGroups cx name expression all
          let memberGroups ← clauseMemberGroups cx name expression all
          members := members.push { name, ref, body := ← mkLambdaFVars all statement, sites, branchGroups, memberGroups }
      let branchGroups ← clauseBranchGroups cx .anonymous body all
      let memberGroups ← clauseMemberGroups cx .anonymous body all
      return (members, branchGroups, memberGroups)
  finally modifyLocal fun _ => saved

/-- Source application occurrence identities, before typed expansion. -/
partial def predicateSourceApps (cx : ExprCtx) (source : Syntax) : TermElabM (Array (Name × Nat)) := do
  let mut out := #[]
  if source.isOfKind ``Lang.appExpr then
    let segs := pathSegs source[0]
    if !(segs.size == 1 && (cx.fnParam? segs[0]!.getId).isSome) then
      if let .ok (.item { kind := .fnItem, path, .. }) := (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing then
        out := out.push (path, (source.getPos?.getD 0).byteIdx)
  for child in source.getArgs do
    out := out ++ (← predicateSourceApps cx child)
  return out

/-- The defined predicate at a typed root, after Bool-to-Prop coercion. -/
def predicateApplication? (state : State) (e : Expr) : Option (DefinedInfo × Array Expr) := do
  let e := e.consumeMData
  let call := if e.isAppOfArity ``Eq 3 && e.getAppArgs[0]!.isConstOf ``Bool && e.getAppArgs[2]!.isConstOf ``Bool.true then
      e.getAppArgs[1]! else e
  let declaration ← call.getAppFn.constName?
  let (_, info) ← state.defined.toList.find? (fun (_, d) => d.decl == declaration && d.result == .bool)
  if call.getAppNumArgs != info.uses.size + info.nParams then none else
    some (info, call.getAppArgs)

partial def predicateCallPolarity? (state : State) (body : Expr) (wanted : Bool := true) :
    Option (DefinedInfo × Array Expr × Bool) :=
  let body := body.consumeMData
  if body.isAppOfArity ``Not 1 then predicateCallPolarity? state body.appArg! (!wanted)
  else (predicateApplication? state body).map fun (info, arguments) => (info, arguments, wanted)

def predicateInstance (info : DefinedInfo) (arguments : Array Expr) (body : Expr) : Expr :=
  (replaceUses info.uses (arguments.extract 0 info.uses.size) body).beta (arguments.extract info.uses.size)

/-- Typed unfolding of named predicate conjunctions. Free constants keep
the defining module's meaning, and each call occurrence has its own path. -/
partial def expandPredicateConstraint (cx : ExprCtx) (prop : PropInfo) (source : Syntax) (fvs : Array Expr) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
  let state ← getState
  let applications ← predicateSourceApps cx source
  let wrap (guards : Array Expr) (body : Expr) : Expr :=
    guards.foldr (fun condition body => .forallE `condition condition body .default) body
  let rec contains (body : Expr) : MetaM Bool := do
    let body := body.consumeMData
    if let some (info, _, _) := predicateCallPolarity? state body then return !info.namedMembers.isEmpty || !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty
    if body.isAppOfArity ``And 2 then return (← contains body.getAppArgs[0]!) || (← contains body.getAppArgs[1]!)
    if let .forallE _ condition tail _ := body then
      if !tail.hasLooseBVars && (← isProp condition) then return ← contains tail
    return false
  let rec expand (body : Expr) (written : Syntax) (owner : Name) (guards : Array Expr) :
      StateT (Std.TreeMap Name Nat Name.quickCmp) TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
    let body := body.consumeMData
    if let .forallE _ condition tail _ := body then
      if !tail.hasLooseBVars && (← isProp condition) then
        return ← expand tail (if isBooleanGuard (unparen written) then (unparen written)[3] else written) owner (guards.push condition)
    if prop.kind != .cover && body.isAppOfArity ``And 2 && (← contains body) then
      let leftSource := if isBinOp (unparen written) "and" then (unparen written)[0] else written
      let rightSource := if isBinOp (unparen written) "and" then (unparen written)[2] else written
      let left ← expand body.getAppArgs[0]! leftSource (Name.mkSimple (owner.toString (escape := false) ++ ".1")) guards
      let right ← expand body.getAppArgs[1]! rightSource (Name.mkSimple (owner.toString (escape := false) ++ ".2")) guards
      return (left.1 ++ right.1, left.2.1 ++ right.2.1, left.2.2 ++ right.2.2)
    if let some (info, arguments, wanted) := predicateCallPolarity? state body then
      if prop.kind != .cover && wanted && !info.namedMembers.isEmpty then
        let seen : Std.TreeMap Name Nat Name.quickCmp ← get
        let next := seen.getD info.path 0 + 1
        set (seen.insert info.path next : Std.TreeMap Name Nat Name.quickCmp)
        let same := applications.filter (·.1 == info.path)
        let index := ((same.findIdx? (fun (_, pos) => pos == (written.getPos?.getD 0).byteIdx)).map (· + 1)).getD next
        let occurrence := Core.showPath info.path ++ s!"@{index}"
        let prefixName := owner.toString (escape := false) ++ "." ++ occurrence
        let callOccurrences ← get
        set ({} : Std.TreeMap Name Nat Name.quickCmp)
        let mut props := #[]
        let mut declarations := #[]
        let mut sites := #[]
        for member in info.namedMembers do
          let name := Name.mkSimple (prefixName ++ (if member.name.isAnonymous then "" else "." ++ member.name.toString (escape := false)))
          let instantiated := wrap guards (predicateInstance info arguments member.body)
          let decl := prop.decl ++ name
          let trigger ← liftM <| do
            let rec top (e : Expr) (conditions : Array Expr) : MetaM (Array Expr) := do
              if let .forallE _ condition tail _ := e.consumeMData then
                if !tail.hasLooseBVars && (← isProp condition) then return ← top tail (conditions.push condition)
              return conditions
            let conditions ← top instantiated #[]
            if conditions.isEmpty then pure none else some <$> mkLambdaFVars fvs (mkAndN conditions.toList)
          let changeName (n : Name) := Name.mkSimple (prefixName ++ "." ++ n.toString (escape := false))
          let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
            let apply (e : Expr) := predicateInstance info arguments e
            let formula := apply m.formula
            let raw := m.valueFormula?.map apply
            let reach := m.evaluationGuard?.map apply
            let reach := if guards.isEmpty then reach else some (mkAndN (guards.toList ++ reach.toList))
            return { m with name := changeName m.name, formula := ← mkLambdaFVars fvs formula
                            valueFormula? := ← raw.mapM (fun e => liftM (mkLambdaFVars fvs e))
                            evaluationGuard? := ← reach.mapM (fun e => liftM (mkLambdaFVars fvs e)) }
          let branches ← member.branchGroups.mapM fun group => do
            return { group with
              owner := name, members := ← group.members.mapM (fun m => liftM (mapMember m))
              guard? := ← (if guards.isEmpty && group.guard?.isNone then pure none else do
                let conditions := guards.toList ++ (group.guard?.map (predicateInstance info arguments)).toList
                pure (some (← liftM (mkLambdaFVars fvs (mkAndN conditions))))) }
          let observations ← member.memberGroups.mapM fun group => do
            return { group with owner := name, members := ← group.members.mapM (fun m => liftM (mapMember m)) }
          let child := { prop with name, ref := member.ref, body := ← mkLambdaFVars fvs instantiated, decl
                                   trigger? := trigger, triggerRef? := (if trigger.isSome then some member.ref else none)
                                   branchGroups := branches, memberGroups := observations
                                   evidenceOwner? := some prop.name, source? := info.source?, sourceRef := true }
          if ← contains (predicateInstance info arguments member.body) then
            let nested ← expand (predicateInstance info arguments member.body) member.ref name guards
            props := props ++ nested.1
            declarations := declarations ++ nested.2.1
            sites := sites ++ nested.2.2
          else
            props := props.push child
            declarations := declarations.push (decl, instantiated)
          for (ref, question, goal) in member.sites do
            let goal := wrap guards (predicateInstance info arguments goal)
            let marked := mkApp (mkConst ``Fren.leafObligation) goal
            sites := sites.push (name, if prop.kind == .assume then .assume else .prop, ref, question, ← mkLambdaFVars fvs marked)
        set callOccurrences
        return (props, declarations, sites)
      else if !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty then
        let prefixName := owner.toString (escape := false) ++ "." ++ Core.showPath info.path ++ "@1."
        let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
          let apply (e : Expr) := predicateInstance info arguments e
          let reach := m.evaluationGuard?.map apply
          let reach := if guards.isEmpty then reach else some (mkAndN (guards.toList ++ reach.toList))
          return { m with
            name := Name.mkSimple (prefixName ++ m.name.toString (escape := false))
            formula := ← mkLambdaFVars fvs (apply m.formula)
            valueFormula? := ← m.valueFormula?.mapM (fun e => liftM (mkLambdaFVars fvs (apply e)))
            evaluationGuard? := ← reach.mapM (fun e => liftM (mkLambdaFVars fvs e)) }
        let branches ← (if wanted then info.namedBranchGroups else #[]).mapM fun group => do
          let conditions := guards.toList ++ (group.guard?.map (predicateInstance info arguments)).toList
          let guard? ← if conditions.isEmpty then pure none else some <$> mkLambdaFVars fvs (mkAndN conditions)
          return { group with owner, guard?, members := ← group.members.mapM (fun m => liftM (mapMember m)) }
        let observations ← info.namedMemberGroups.mapM fun group => do
          return { group with
            owner, wanted := (if wanted then group.wanted else !group.wanted)
            members := ← group.members.mapM (fun m => liftM (mapMember m)) }
        let body := wrap guards body
        let decl := prop.decl ++ owner
        return (#[{ prop with
          name := owner, ref := written, body := ← mkLambdaFVars fvs body, decl
          branchGroups := branches, memberGroups := observations, source? := info.source?
          evidenceOwner? := some prop.name }], (if decl == prop.decl then #[] else #[(decl, body)]), #[])
    let body := wrap guards body
    let decl := prop.decl ++ owner
    return (#[{ prop with name := owner, ref := written, body := ← mkLambdaFVars fvs body, decl,
                           evidenceOwner? := some prop.name }], (if decl == prop.decl then #[] else #[(decl, body)]), #[])
  let body ← zetaReduce (prop.body.beta fvs)
  if let some (info, arguments, wanted) := predicateCallPolarity? state body then
    if (prop.kind == .cover || info.namedMembers.isEmpty || !wanted) && (!info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty) then
      let prefixName := prop.name.toString (escape := false) ++ "." ++ Core.showPath info.path ++ "@1."
      let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
        let apply (e : Expr) := mkLambdaFVars fvs (predicateInstance info arguments e)
        return { m with
          name := Name.mkSimple (prefixName ++ m.name.toString (escape := false))
          formula := ← apply m.formula
          valueFormula? := ← m.valueFormula?.mapM (fun e => liftM (apply e))
          evaluationGuard? := ← m.evaluationGuard?.mapM (fun e => liftM (apply e)) }
      let branches ← (if wanted then info.namedBranchGroups else #[]).mapM fun g => do
        return { g with
          owner := prop.name, members := ← g.members.mapM mapMember
          guard? := ← g.guard?.mapM (fun e => liftM (mkLambdaFVars fvs (predicateInstance info arguments e))) }
      let observations ← info.namedMemberGroups.mapM fun g => do
        return { g with
          owner := prop.name, wanted := (if wanted then g.wanted else !g.wanted)
          members := ← g.members.mapM mapMember }
      return (#[{ prop with branchGroups := branches, memberGroups := observations, source? := info.source? }], #[], #[])
  if !(← contains body) then return (#[prop], #[], #[])
  return (← (expand body source prop.name #[]).run {}).1

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
    let tables := (← takeIndexes fvs (fun (x : Expr) => x.replaceFVars fnFvs phs)).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
    let checked? ← if fnVars.isEmpty then pure none else some <$> mkLambdaFVars fvs (body.replaceFVars fnFvs phs)
    -- A postcondition of the value, for realizability: the function
    -- applied to its parameters is the value.
    let ofValue? ← match post, value? with
      | true, some (ph, v) => withLocalDeclD v.name v.type fun x => do
        -- At its own type parameters, whatever term gives their
        -- `Inhabited` instances.
        let nTypes := 2 * ((← placeholderOf path).typeParams.size)
        let isApp (t : Expr) : Bool :=
          t.isAppOfArity ph (nTypes + fvs.size) && t.getAppArgs.extract nTypes == fvs
        some <$> mkLambdaFVars (fvs.push x) (body.replace fun t => if isApp t then some x else none)
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
  let sites' ← sites.mapM fun (n, place, r, q, g) => return (n, place, r, q, ← withValue g)
  return (vars.push v, props', sites')

/-- Elaborates the function `stx`, a `fnCmd`, as written or as a function
written with a block lowers to (`elabFnBlock`): `orig` is the command as
written, whose lexemes, layout and lines are checked. -/
def elabFunctionCore (stx orig : Syntax) (uses : Array Syntax := #[]) : CommandElabM Unit := do
  checkLexemes orig
  checkParsed orig
  lintItem orig
  lintTrailingCommas orig
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  liftMsg nameStx (Core.checkFnName n)
  checkFresh modName n nameStx
  lintName .function n nameStx
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  -- The `use`s of its block, and the scope that its paths resolve in, as
  -- a procedure's (`Reqs/Lang/Items#function-blocks`).
  for m in uses do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if uses.isEmpty then modName else path
  let stx ← liftTermElabM <| anonymousMatchFunction stx
  let params := stx[5].getSepArgs
  let body? := if stx[8].isNone then none else some (withWhere stx[8][1] stx[8][2])
  let clauses := stx[9].getArgs
  -- Its type parameters, which are abstract types within it, whether it
  -- is defined or not (`lang::generic_function`).
  let tpStxs := if stx[3].isNone then #[] else stx[3][0][1].getSepArgs
  let tps ← elabTypeParams scope tpStxs
  if !tps.isEmpty then
    liftTermElabM do
      for p in tps, k in [0:tps.size] do declarePlaceholder (Core.typeParamPath path k p) (mkSort Level.one) true
    modifyLocal fun l => { l with fnTypeParams := some (path, tps) }
  let contract := !clauses.isEmpty
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Syntax) := !p[1].isNone ||
    (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (declaredIdent (pathSegs q)[0]!).1.getId.toString.endsWith "?"
  let nNamed := (params.filter named).size
  unless Core.functionParamsAccepted body?.isSome contract params.size nNamed do
    let bad := params.find? (named · != (body?.isSome || contract)) |>.getD nameStx
    throwErrorAt bad (Core.functionParamsMsg path body?.isSome contract).text
  let decl ← generatedName path
  -- A generic function's signature, with its type parameters as
  -- `Core.Ty.param`, each inferred at applications from it
  -- (`lang::generic_signature`).
  let signature (params : Array Expr) (result : Expr) : TermElabM (Array Core.Ty × Core.Ty) := do
    let asParams (t : Expr) : TermElabM Core.Ty := return ((← coreTy? t).getD .bool).asParams path tps
    let declared ← params.mapM asParams
    let resultTy ← asParams result
    if let some k := Core.firstUnmentioned? declared resultTy tps.size then
      throwErrorAt tpStxs[k]! (Core.unmentionedTypeParamMsg n tps[k]!).text
    return (declared, resultTy)
  -- Without a body, a placeholder, which takes a `Type` and its `Inhabited`
  -- instance for each type parameter first, if it is generic: each
  -- instance is an unknown function of its own
  -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
  let placeholder (params : Array Expr) (ptys : Array Core.PTy) (result : Expr) (rp : Core.PTy) : TermElabM Unit := do
    let (declared, resultTy) ← signature params result
    let type ← withTypeParams path tps (← mkArrowN params result)
    declarePlaceholder path type false (ptys, rp) (← resultFact? result rp) tps declared resultTy (rp.asParams path tps)
  let some body := body? | do
    liftTermElabM do
      if contract then
        let vars := (← paramVarsHo scope path params false).1
        lintFnBools n nameStx (vars.map (·.type))
        let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
        placeholder (vars.map (·.type)) (vars.map (·.ptype)) result rp
        modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
        let (vars, props, sites) ← elabContract scope path n decl false vars clauses
        recordBody path nameStx decl vars sites props path
      else
        let pps ← params.mapM fun p => do lintRelTypes scope p[0]; elabPType scope p[0]
        let params := pps.map (·.1)
        lintFnBools n nameStx params
        -- As for a variable, with the result type (`lang::bool_naming`).
        let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
        placeholder params (pps.map (·.2)) result rp
    if contract then
      lintDeclared .function n nameStx
      lintLines .function n nameStx orig
    record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
    unless isPub do recordItem .function path nameStx
    modifyLocal fun l => { l with fnTypeParams := none }
  liftTermElabM do
    -- The parameters, declared like a procedure's parameters, and the function
    -- parameters (`Reqs/Lang/HigherOrder#function-parameters`).
    let (vars, fnPs) ← paramVarsHo scope path params true
    lintFnBools n nameStx (vars.map (·.type))
    let (result, rp) ← varPType scope nameStx (if stx[7].isNone then none else some stx[7][1])
    -- Each type parameter is inferred at applications from the signature
    -- (`lang::generic_signature`), where a function parameter's type
    -- stands for its parameters' and its result's.
    let asParams (t : Expr) : TermElabM Core.Ty := return ((← coreTy? t).getD .bool).asParams path tps
    let declared ← vars.mapM (asParams ·.type)
    let resultTy ← asParams result
    let fnDeclared := fnPs.flatMap fun (_, _, _, ft, _) => (ft.asParams path tps).params.push (ft.asParams path tps).result
    if let some k := Core.firstUnmentioned? (declared ++ fnDeclared) resultTy tps.size then
      throwErrorAt tpStxs[k]! (Core.unmentionedTypeParamMsg n tps[k]!).text
    -- Each function parameter is an uninterpreted function, of its
    -- placeholder, for the function's own checks.
    for (_, x, _, _, lty) in fnPs do declarePlaceholder (path ++ x) lty false
    let fnVars := fnPs.map fun (_, x, _, ft, lty) => (x, ft, lty, placeholderName (path ++ x))
    let phs : Array Expr := fnVars.map fun p => Lean.mkConst p.2.2.2
    modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
    -- A first-order function that is not generic may apply itself, in a
    -- structural recursion (`lang::structural_recursion`): within the
    -- body, a local of its type stands for it, which its definitions
    -- replace with themselves.
    let selfName := n.appendAfter "#self"
    let recursive := tps.isEmpty && fnPs.isEmpty
    let selfTy := vars.foldr (fun v acc => .forallE v.name v.type acc .default) result
    let withSelf {α : Type} (k : Option Expr → TermElabM α) : TermElabM α :=
      if recursive then withLocalDeclD selfName selfTy fun s => k (some s) else k none
    let (lam, tables, obls, leanLam?, recLeanLam?, recIdx?, selfApps) ← withLocalDeclsD (fnVars.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
        withSelf fun self? => withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let all := fvs ++ fnFvs
      let selfRec? := if recursive then some (vars.map (·.name), ({ params := declared, result := resultTy } : Core.FnTy),
        (⟨(mkIdent selfName).raw⟩ : Term)) else none
      let cx : ExprCtx := { modName := scope, vars, insts := #[], place := .prop
                            selfFn := if (← getLocal).inSubset then none else some n, natOk := result.isConstOf ``Nat
                            expected? := if result.isConstOf ``Nat then some .nat else none
                            fnParams := fnVars.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)), selfRec? }
      discard (takeIndexes fvs)
      modifyLocal fun l => { l with recUses := #[], recApps := #[], recMatches := #[] }
      let t ← toTerm cx body
      let uses := (← getLocal).recUses
      let recursion := Core.recursion vars.size (uses.toList.map (·.2))
      let structural := recursion matches .structural _
      if structural then
        if let some m := (← getLocal).recMatches[0]? then throwErrorAt m (Core.recursiveMatchMsg path).text
      noteObligation cx .body body rp t
      -- Its tables, the applications of functions with preconditions, and
      -- its pattern types' obligations, for their checks; its indexes are
      -- not checked.
      -- A structural recursion's applications of itself are of its solver
      -- form there (`DefinedInfo.recursive`).
      let selfFor (x : Expr) : Expr := match self? with
        | some s => x.replaceFVar s (Lean.mkConst (solverName decl))
        | none => x
      let tables := (← takeIndexes fvs (fun (x : Expr) => selfFor (x.replaceFVars fnFvs phs))).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
      checkDeclared body t result fun ty => s!"note: `{n}` returns `{ty}`"
      -- A `Bool` body is decided, classically if need be: equality on an
      -- abstract type has no other `Decidable` instance.
      let elabValue (t : Term) : TermElabM Expr := do
        if result.isConstOf ``Bool then
          let p ← elabProp t
          let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
            | .some i => pure i
            | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
          pure (mkApp2 (mkConst ``Decidable.decide) p inst)
        else elabProp t result
      let value ← elabValue t
      -- The Lean definition's value, where the body has a `match` or a
      -- pattern test: the body translated again, with each `match` Lean's
      -- where it can be (`Reqs/Generated#matches`). What that translation
      -- records and reports is dropped, as the first's stands; where it
      -- fails, the definition is the solver's.
      let leanValue? ← if !structural && (body.find? fun x => isMatchLike x || x.isOfKind ``Lang.isExpr).isNone then pure none else
        keepingNames <| withDeclName (leanDeclName decl) do
          let saved ← saveState
          try
            let t' ← toTerm { cx with leanMatch := true, leanBoolArms := structural } body
            -- But the metavariables, which the terms of the types that `t'`
            -- is written with stand for (`exprToSyntax`).
            let mctx ← getMCtx
            saved.restore
            setMCtx mctx
            -- A structural recursion's `Bool` body is a `Bool`, a Lean
            -- `match` of its arms' `decide`s, rather than decided again.
            let v ← if structural && result.isConstOf ``Bool then elabProp t' result else elabValue t'
            some <$> (instantiateMVars v)
          catch _ =>
            saved.restore
            pure none
      -- For each function parameter, its closures' obligations: over the
      -- parameters and a predicate of the closure's parameters
      -- (`lang::closure_obligation`).
      let unfolded ← if fnFvs.isEmpty then pure value else unfoldForSites value
      let obls ← fnFvs.mapM fun f => do
        let pty ← forallTelescope (← inferType f) fun xs _ => mkForallFVars xs (mkSort .zero)
        withLocalDeclD `p pty fun pr => do
          let gs ← siteGoals f pr [] unfolded
          let body := if gs.isEmpty then Lean.mkConst ``True else gs.pop.foldr mkAnd gs.back!
          mkLambdaFVars (all.push pr) body
      -- A structural recursion's Lean definition is a Lean `match`, which
      -- `lang::recursive_match` makes sure there is: over itself first.
      let recLean? ← if !structural then pure none else
        match leanValue?, self? with
        | some v, some s => pure (some (← mkLambdaFVars #[s] (← mkLambdaFVars all v)))
        | _, _ => throwErrorAt nameStx s!"internal error: no Lean definition of the structural recursion `{n}`"
      return (selfFor (← mkLambdaFVars all value), tables, obls, ← leanValue?.mapM (mkLambdaFVars all ·), recLean?,
        (match recursion with | .structural i => some i | _ => none),
        ← (← getLocal).recApps.mapM fun (r, args, gs) => do
          return (r, ← args.mapM fun x => do mkLambdaFVars fvs (selfFor (← instantiateMVars x)),
            ← gs.mapM fun x => do mkLambdaFVars fvs (selfFor (← instantiateMVars x))))
    lintBools body (← hidesIn { modName := scope, vars, insts := #[], place := .prop, selfFn := some n })
    -- A parameter that only the contract mentions is used too.
    let mentioned := (pathMentions body ++ clauses.flatMap fun c => pathMentions (withWhere c[3] c[4])).map (·.getRoot)
    let mentioned := if fnPs.isEmpty then mentioned
      else mentioned ++ appliedNames body ++ clauses.flatMap fun c => appliedNames (withWhere c[3] c[4])
    -- In order, a function parameter among the others.
    let paramRefs := Id.run do
      let mut out := vars.map fun v => (v.name, v.ref)
      for (j, x, ref, _, _) in fnPs do out := out.insertIdxIfInBounds j (x, ref)
      return out
    for (x, ref) in Core.unmentioned paramRefs mentioned do
      recordLint .unusedVariables ref (Core.unusedParamMsg x)
    let uses ← usesOf #[lam]
    -- Where its Lean definition is a Lean `match`, the solver's is beside it
    -- (`DefinedInfo.solver?`).
    -- A structural recursion's body as the solver reads it, with the
    -- defined functions it applies unfolded, as a query's are.
    let recBody? ← if recLeanLam?.isNone then pure none else do
      let st ← getState
      let ds := st.defined.foldl (init := ({} : NameSet)) fun acc _ d => acc.insert d.decl
      some <$> Meta.zetaReduce (← Lean.Core.betaReduce (← deltaDefined st lam ds.contains))
    let solver? ← match recLeanLam?, leanLam? with
      | some recLean, _ => addRecursiveDefs nameStx uses decl recLean; pure (some (solverName decl))
      | none, none => addUsesDef uses decl lam; pure none
      | none, some leanLam =>
        let saved ← saveState
        try
          -- As many names as `addUsesDef uses decl lam` would take.
          keepingNames (addLeanDef uses decl leanLam)
          addUsesDef uses (solverName decl) lam (compile := false)
          modifyEnv (addNoncomputable · (solverName decl))
          pure (some (solverName decl))
        catch _ =>
          saved.restore
          addUsesDef uses decl lam
          pure none
    let oblDecls ← (obls.zip fnVars).mapM fun (o, x, _) => do
      let name := decl ++ `obligation ++ x
      let ouses ← usesOf #[o]
      addUsesDef ouses name o
      return (name, ouses)
    let ptys := Id.run do
      let mut out := vars.map (·.ptype)
      for (j, _, _, ft, _) in fnPs do out := out.insertIdxIfInBounds j (.plain ft.result)
      return out
    let hoParams := Id.run do
      let mut out := declared.map Core.HoParam.value
      for (j, _, _, ft, _) in fnPs do out := out.insertIdxIfInBounds j (.function (ft.asParams path tps))
      return if fnPs.isEmpty then #[] else out
    let (namedMembers, namedBranchGroups, namedMemberGroups) ← if resultTy == .bool && (← getLocal).recUses.isEmpty then
        predicateMetadata scope vars fnVars body else pure (#[], #[], #[])
    let source? := some (← getFileName, ← getFileMap)
    record (.definedInfo { path, decl, uses, nParams := vars.size + fnPs.size, ptys := (ptys, rp)
                           guarded := (← getLocal).guardedUsed, typeParams := tps
                           declared := if hoParams.isEmpty then declared else hoParams.map (·.ty), result := resultTy, hoParams
                           oblDecls, solver?, namedMembers, namedBranchGroups, namedMemberGroups, source?, recursive := recLeanLam?.isSome, recBody?, decreasing? := recIdx?
                           fact? := ← if recIdx?.isSome then (← resultFact? result rp).mapM instantiateMVars else pure none })
    let (_, props, sites) ← if contract then elabContract scope path n decl true vars clauses fnVars (paramRefs.map (·.1)) else pure (vars, #[], #[])
    let selfSites ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let k := (← getState).contracts.get? path
      let mut out := #[]
      for (ref, args, gs) in selfApps do
        let args := args.map (·.beta fvs)
        let gs := gs.map (·.beta fvs)
        for p in (k.map (·.pres)).getD #[] do
          let g := gs.foldr (fun g b => mkForall `h .default g b) (p.at args)
          out := out.push (n, Core.IndexPlace.body, ref, some (Core.TableGoal.precondition path p.name), ← mkLambdaFVars fvs g)
      return out
    recordBody path nameStx decl vars (tables.map (fun (r, q, g) => (n, .body, r, q, g)) ++ sites ++ selfSites) props path
  lintDeclared .function n nameStx
  lintLines .function n nameStx orig
  record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .function path nameStx (defined := true)
  modifyLocal fun l => { l with fnTypeParams := none }
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))


/-- A function without a block: uninterpreted, or with a body. -/
@[command_elab Lang.fnCmd] def elabFunction : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  elabFunctionCore stx stx

/-- The names that the identifiers within `e` mention, as the `fren`
command reads them from its tokens: each one's first segment, without the
`!` of shadowing. -/
partial def identRoots (e : Syntax) : Array String :=
  if e.isIdent then
    let s := Core.nameText e.getId.getRoot
    #[if s.endsWith "!" then (s.dropEnd 1).toString else s]
  else e.getArgs.foldl (init := #[]) fun acc a =>
    (identRoots a).foldl (init := acc) fun acc n => if acc.contains n then acc else acc.push n

/-- `stx`, everything within it at the position of `ref`. -/
partial def withInfoOf (ref : Syntax) : Syntax → Syntax
  | .node _ k args => .node (SourceInfo.fromRef ref) k (args.map (withInfoOf ref))
  | .atom _ v => .atom (SourceInfo.fromRef ref) v
  | .ident _ raw v pre => .ident (SourceInfo.fromRef ref) raw v pre
  | s => s

/-- `text`, parsed as a `cat`, at the position of `ref`. -/
def parseAt (cat : Name) (text : String) (ref : Syntax) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) cat text with
  | .ok s => return withInfoOf ref s
  | .error e => throwErrorAt ref e

/-- The indices of the definitions of `defs`, `fren_def`s with their
names, that an expression `e` with its own `where` clause `w?` needs
(`Core.neededDefs`). -/
def neededOf (defs : Array (String × Syntax)) (e w? : Syntax) : Array Nat :=
  Core.neededDefs defs (fun d => identRoots d[3]) (identRoots e ++ identRoots w?)

/-- An expression `e` with its own `where` clause `w?`, as an expression
and a `where` clause: the definitions of `defs` that it needs, around it
with its own clause within. -/
def withNeeded (defs : Array (String × Syntax)) (e w? : Syntax) : Syntax × Syntax :=
  let needed := neededOf defs e w?
  if needed.isEmpty then (e, w?) else
  let args := needed.foldl (init := #[]) fun acc i => (if acc.isEmpty then acc else acc.push (mkAtom ",")).push defs[i]!.2
  (withWhere e w?, mkNullNode #[(mkNode ``Lang.fren_where #[mkAtom "where", mkNullNode args] : Syntax)])

/-- A function written with its result and a block
(`Reqs/Lang/Items#function-blocks`), as the `fren` command reads it: the
function whose body is its `out` member's expression and whose contract is
its `assume`s and `ensure`s, each with the result, `r := f(x)`, and the
`let`s that it needs as a `where` clause (`F0442`–`F0445`, `F0165`). -/
@[command_elab Lang.fnBlockCmd] def elabFnBlock : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  let results := stx[9].getSepArgs
  let r := results[0]!
  unless r[0].isNone do throwErrorAt r[0][0][0] (Core.fnMemberMsg? .evidence false "set_option").get!.text
  unless r[1].isNone do throwErrorAt r[1] (Core.fnMemberMsg? .define true "det").get!.text
  if let some r2 := results[1]? then throwErrorAt (r2.getHead?.getD r2) Core.fnResultsMsg.text
  let rx := (declaredIdent r[2]).1
  let rn := Core.nameText rx.getId
  let mut lets : Array (String × Syntax) := #[]
  let mut out? : Option Syntax := none
  let mut clauses := #[]
  let mut uses := #[]
  for m in stx[12].getArgs do
    let mut inner := m
    while inner.isOfKind ``Lang.evidenceMember do inner := inner[4]
    if inner.isOfKind ``Lang.refinesMember then
      throwErrorAt inner "`refines` is accepted only in global expectation blocks"
    -- Each member that a function's block does not take (`F0442`,
    -- `F0443`), at its first token, or a `use`'s or an evidence
    -- setting's whole, as the `fren` command reports it.
    let kind? : Option (Core.FnMember × Bool × String × Syntax) :=
      if m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember then some (.use, false, "use", m)
      else if m.isOfKind ``Lang.evidenceMember then some (.evidence, false, "set_option", mkNullNode #[m[0], m[3]])
      else if m.isOfKind ``Lang.callMember then some (.call, false, "call", m[0])
      else if m.isOfKind ``Lang.existsMember then some (.exists, !m[0].isNone, "exists", if m[0].isNone then m[1] else m[0])
      else if m.isOfKind ``Lang.letMember then some (.let, !m[0].isNone, "let", if m[0].isNone then m[1] else m[0])
      else match constraint? m with
        | some (.expect, _, _) => some (.claim, false, "expect", m[0])
        | some (.cover, _, _) => some (.claim, false, "cover", m[0])
        | _ => none
    if let some (k, det, kw, ref) := kind? then
      if let some msg := Core.fnMemberMsg? k det kw then throwErrorAt ref msg.text
    if m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember then uses := uses.push m
    else if m.isOfKind ``Lang.letMember then
      let x := (declaredIdent m[2]).1
      lets := lets.push (Core.nameText x.getId, (mkNode ``Lang.fren_def #[m[2], m[3], m[4], withWhere m[5] m[6]] : Syntax))
    else if m.isOfKind ``Lang.defineMember then
      let x := Core.nameText m[1].getId
      unless x == rn do throwErrorAt (mkNullNode #[m[0], m[1]]) (Core.fnOutMsg x rn).text
      if out?.isSome then throwErrorAt m[1] (Core.resultDefinedTwiceMsg x).text
      out? := some (mkNullNode #[m[2], m[3], m[4]])
    else if (constraint? m).isSome then clauses := clauses.push m
  -- Expand implicit parameters before forming the result's self-call in
  -- postconditions; that call must use the same fresh parameters.
  let (parameters, expandedOut) ← match out? with
    | some body => liftTermElabM do
      let fn := mkNode ``Lang.fnCmd #[stx[0], stx[1], stx[2], stx[3], stx[4], stx[5], stx[6], mkNullNode, body, mkNullNode]
      let expanded ← anonymousMatchFunction fn
      pure (expanded[5], some expanded[8])
    | none => pure (stx[5], out?)
  out? := expandedOut
  -- The result, the function applied to its parameters, at the result's
  -- name.
  let fname := Core.nameText (declaredIdent stx[2]).1.getId
  let pnames := parameters.getSepArgs.map fun p =>
    match typePath? p[0] with
    | some q => (declaredIdent (pathSegs q)[0]!).1.getId
    | none => Name.anonymous
  let args ← liftTermElabM <| pnames.mapM (pathExpr rx)
  let template ← parseAt `fren_expr s!"{fname}(false)" rx
  let value := template.setArg 2 (Syntax.mkSep args (mkAtom ","))
  -- With the result's type, if written, which a generic function's
  -- application may need.
  let rDef : Syntax := mkNode ``Lang.fren_def #[withInfoOf rx (mkIdent rx.getId), r[3], mkAtom ":=", value]
  let defs := #[(rn, rDef)] ++ lets
  -- The result is the function's value: neither its body nor its
  -- preconditions mention it (`F0165`).
  let check (e w? : Syntax) : CommandElabM Unit := do
    let needed := Core.neededDefs lets (fun d => identRoots d[3]) (identRoots e ++ identRoots w?)
    let all := identRoots e ++ identRoots w? ++ needed.flatMap fun i => identRoots lets[i]!.2[3]
    if all.contains rn then throwErrorAt (mkNullNode #[e, w?]) (Core.fnResultMentionMsg rn).text
  let mut clauses' := #[]
  -- And the `let`s that some expression needs, the others unused.
  let mut used : Array Nat := #[]
  for c in clauses do
    let isEnsure := c[0].getAtomVal.trimAscii.toString == "ensure"
    unless isEnsure do check c[3] c[4]
    used := used ++ (neededOf defs c[3] c[4]).filterMap fun i => if i == 0 then none else some (i - 1)
    let kw := mkAtomFrom c[0] (if isEnsure then "ensure " else "assume ")
    let (e, w) := withNeeded defs c[3] c[4]
    clauses' := clauses'.push (mkNode ``Lang.fren_clause #[kw, c[1], c[2], e, w])
  let body ← match out? with
    | some d => do
      check d[1] d[2]
      used := used ++ neededOf lets d[1] d[2]
      let (e, w) := withNeeded lets d[1] d[2]
      pure (mkNullNode #[d[0], e, w])
    | none => pure mkNullNode
  -- Its `let`s that nothing needs, as a procedure's (`unused_variables`).
  for (n, d) in lets, i in [0:lets.size] do
    unless used.contains i do
      recordLint .unusedVariables (declaredIdent d[0]).1 (Core.unusedVariableMsg (Name.mkSimple n) false true)
  -- A result `r?` without a type is a `Bool`, as is the function's
  -- value if its name ends in `?` too.
  let result ← if !r[3].isNone then pure r[3]
    else if rn.endsWith "?" && !fname.endsWith "?" then pure (mkNullNode #[mkAtom ":", ← parseAt `fren_type "Bool" rx])
    else pure mkNullNode
  let fn := mkNode ``Lang.fnCmd #[stx[0], stx[1], stx[2], stx[3], stx[4], parameters, stx[6], result, body, mkNullNode clauses']
  elabFunctionCore fn stx uses

/-- A call whose procedure has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Name
  ref : Syntax
  comp : CompInfo
  /-- `fren_binding`s. -/
  bindings : Array Syntax
  /-- Where its variables start among the calling procedure's. -/
  offset : Nat
  /-- A call's arguments, each bound to the parameter in its position,
  rather than bindings written by name. -/
  positional : Bool := false

/-- Resolves the call `call x := p(args)`: the called procedure, the
call's variables, and its bindings, each argument bound to the parameter
in its position (`F0408`, `F0409`). -/
def resolveInst (modName : Name) (x p : Syntax) (bs : Array Syntax) (offset : Nat) :
    TermElabM (PendingInst × Array Var) := do
  liftMsg x (Core.checkItemName "call" x.getId)
  let r ← resolvePath modName (pathSegs p)
  let .item { kind := .compItem, path, .. } := r | throwErrorAt p (Core.notACompMsg r).text
  let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
  unless c.decidable do
    modifyLocal fun l => { l with outsideCore := true }
    recordLint .undecidable p (Core.undecidableInstMsg path)
  noteCounts c p
  let params := c.vars.filter (fun v => v.role == .input && v.name.isAtomic) |>.map (·.name)
  let callee := Core.showPath path
  let some bound := Core.callBindings (params.map Core.nameText) bs
    | let ref := if bs.size > params.size then mkNullNode (bs.extract params.size bs.size) else p
      throwErrorAt ref (Core.callArityMsg callee (params.map Core.nameText) bs.size).text
  -- Each argument, bound to its parameter, at the argument.
  let bs := (params.zip bound).map fun (n, (_, a)) =>
    mkNode ``Lang.fren_binding #[mkIdentFrom a n, mkNullNode #[mkAtom ":=", a]]
  let w := x.getId
  -- An input's constraint is the call's obligation, which the call
  -- check asks, rather than a fact (`Reqs/Check#call-assumptions`).
  let vars := c.vars.map fun v =>
    let role := Core.Role.ofInst v.role v.isPub
    { name := w ++ v.name, role, isPub := role == .instOutput, type := v.type, ref := x, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact? : Var }
  return ({ name := w, ref := x, comp := c, bindings := bs, offset, positional := true }, vars)

/-- The obligations of the inputs of `c`, whose variables are `slice`, an
call's among `fvs`, whose types have one: each named after its input,
with its type, as written, and closed over `fvs`
(`Reqs/Check#call-assumptions`). -/
def typedObligations (c : CompInfo) (slice fvs : Array Expr) : TermElabM (Array (Name × String × Expr)) := do
  let mut out := #[]
  for (v, x) in c.vars.zip slice do
    unless v.role == .input do continue
    let some o := v.ptype.obligation (← getState).shapeOf | continue
    let parts := o.namedParts
    let parts := if parts.isEmpty then #[(.anonymous, o)] else parts
    for (name, part) in parts, k in [0:parts.size] do
      let label := if name.isAnonymous then v.ptype.text else "@invariant:" ++ Core.showPath name
      let p ← predOf v.type part
      out := out.push (Name.num v.name k, label, ← mkLambdaFVars fvs (p.beta #[x]))
  return out

open Lang in
/-- The equations made by the bindings of a call, over the procedure's
variables `fvs`. -/
def elabBindings (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) : TermElabM Expr := do
  let mut eqs := #[]
  for b in pi.bindings do
    let x := b[0]
    let some idx := cx.vars.findIdx? (·.name == pi.name ++ x.getId)
      | throwError "internal error: no variable for `{x.getId}`"
    let natOk := cx.vars[idx]!.type.isConstOf ``Nat
    let t ← if b[1].isNone then toTerm cx (← `(fren_expr| $(⟨x⟩):ident)) else toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk, expected? := ← coreTy? cx.vars[idx]!.type } b[1][1]
    checkDeclared (if b[1].isNone then x else b[1][1]) t cx.vars[idx]!.type fun ty =>
      s!"note: `{x.getId}` of `{Core.showPath pi.comp.path}` has type `{ty}`"
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if cx.vars[idx]!.type.isConstOf ``Int && (← frenTypeOf? t) == some .int then
      modifyLocal fun l => { l with natKept := l.natKept.push (pi.comp.path, Core.nameText x.getId) }
    unless b[1].isNone do lintBools b[1][1] (← hidesIn cx)
    unless pi.positional do lintRedundant b false
    let fv := fvs[idx]!
    eqs := eqs.push (← mkEq fv (← elabProp t (← inferType fv)))
  return mkAndN eqs.toList

/-- Elaborates a call, and the body over `fvs` of the definition `decl`
generated for it. -/
def elabInst (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) (decl : Name) : TermElabM (InstInfo × Expr) := do
  let bindings ← elabBindings cx fvs pi
  let slice := fvs.extract pi.offset (pi.offset + pi.comp.vars.size)
  let behaviour := pi.comp.meaning slice
  let typed ← typedObligations pi.comp slice fvs
  -- A call's own meaning is not a hypothesis of its precondition check.
  -- Inline its local definitions into those obligations instead.
  let mut defined := slice
  for (name, value) in pi.comp.defs do
    if let some k := pi.comp.vars.findIdx? (·.name == name) then
      defined := defined.set! k (value.beta defined)
  return (·, mkAnd bindings (pi.comp.meaningDecl slice)) {
    name := pi.name, comp := pi.comp.path, ref := pi.ref, decl
    bindings := ← mkLambdaFVars fvs bindings
    behaviour := ← mkLambdaFVars fvs behaviour
    assumes := typed.map (fun (n, _, f) => (n, f))
      ++ (← pi.comp.assumes.mapM fun a => return (a.name, ← mkLambdaFVars fvs (a.body.beta defined)))
    typed := typed.map fun (n, t, _) => (n, t) }

/-- Whether the evidence `value`, written at `ref`, is testing
(`Reqs/Check#checking-by-testing`). -/
def evidenceTested (ref : Syntax) (value : String) : CommandElabM Core.Evidence := do
  let some b := Core.evidenceOf? value | throwErrorAt ref (Core.invalidEvidenceMsg value).text
  return b

/-- Whether the item-level or file-level `fren.evidence` in effect sets
checks to testing. An invalid value, reported once where it is set
(`elabEvidenceOption`), sets nothing. -/
def evidenceInEffect : CommandElabM Core.Evidence :=
  return (Core.evidenceOf? (fren.evidence.get (← getOptions))).getD {}

/-- The size bound of enumeration in effect (`fren.enumeration.size`). -/
def enumSizeInEffect : CommandElabM Nat := do
  let n := fren.enumeration.size.get (← getOptions)
  return if n > Core.Enumeration.maxSize then Core.Enumeration.defaultSize else n

/-- `set_option`, as Lean elaborates it, but for `fren.evidence`, an invalid
value is reported once, at the value, rather than at each item it would
set, and does not stop them, as in the `fren` command. -/
@[command_elab Lean.Parser.Command.set_option] def elabEvidenceOption : CommandElab := recordingErrors fun stx => do
  let opt := stx[1].getId.eraseMacroScopes
  unless opt == `fren.evidence || opt == `fren.enumeration.size do throwUnsupportedSyntax
  if let some v := stx[3].isStrLit? then
    if (Core.evidenceTested? v).isNone then logErrorAt stx[3] (Core.invalidEvidenceMsg v).text
  if let some n := stx[3].isNatLit? then
    if n > Core.Enumeration.maxSize then logErrorAt stx[3] (Core.Enumeration.sizeTooLargeMsg n).text
  elabSetOption stx

open Lang in
/-- A member without its `set_option fren.evidence ... in`, and the
setting, if it has one: the innermost, if there are several. -/
partial def unwrapEvidence (m : Syntax) : CommandElabM (Syntax × Option (Core.Evidence × Syntax)) := do
  unless m.isOfKind ``Lang.evidenceMember do return (m, none)
  -- Its option is `fren.evidence` (`checkParsed`).
  let b ← evidenceTested m[2] (m[2].isStrLit?.getD "")
  let (inner, set?) ← unwrapEvidence m[4]
  return (inner, set?.getD (b, m))

open Lang in
/-- The members of a procedure without their evidence settings, and the checks
that those and the procedure's setting `all` set to testing. -/
def testedOf (all : Core.Evidence) (raw : Array Syntax) : CommandElabM (Array Syntax × Core.Tested × Core.Tested) := do
  let reserved := raw.filterMap fun m0 => Id.run do
    let mut m := m0
    while m.isOfKind ``Lang.evidenceMember do m := m[4]
    return (constraint? m).map fun (_, x, _) => x.getId
  let mut refinesIndex := 0
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
    if let some (kind, x, _) := constraint? m then
      match kind with
      | .expect | .cover => expects := expects.push (x.getId, b?)
      | .assume => misplaced "an assumption"; constraints := constraints.push x.getId
      | .ensure => misplaced "a guarantee"; constraints := constraints.push x.getId
    -- By the names they declare, without the `!` of shadowing.
    else if m.isOfKind ``Lang.refinesMember then
      refinesIndex := refinesIndex + 1
      while reserved.contains (Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      expects := expects.push (Name.mkSimple s!"refines_{refinesIndex}", b?)
    else if m.isOfKind ``Lang.callMember then insts := insts.push ((declaredIdent m[1]).1.getId, b?)
    else if m.isOfKind ``Lang.outMember then
      -- `[pub] [det] out x [: T] [:= e]`
      let y := (declaredIdent m[3]).1.getId
      if !m[1].isNone then dets := dets.push (y, b?)
      else misplaced "a variable that is not `det`"
      if !m[5].isNone then constraints := constraints.push y
    else misplaced (if m.isOfKind ``Lang.inMember then "a parameter" else "a `use`")
  let by_ (f : Core.Evidence → Bool) :=
    let pick (xs : Array (Name × Option Core.Evidence)) := xs.map fun (n, e?) => (n, e?.map f)
    Core.Tested.ofSettings (f all) constraints (pick expects) (pick insts) (pick dets)
  return (members, by_ (·.tested), by_ (·.enumerated))

open Lang in
/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own, as the `fren` command sees them
(`lint::manual_nat`). -/
partial def constraintConjuncts (e : Syntax) : Array Syntax :=
  let rec go (e : Syntax) : Array Syntax := if isBinOp e "and" then go e[0] ++ go e[2] else #[e]
  go (unparen e)

open Lang in
/-- Records `manual_nat` in the procedure `compPath` of `members`
(`lint::manual_nat`): for each variable it fires on, at its first bound,
reported at the end of the file (`reportLints`). -/
def lintManualNat (compPath : Name) (members : Array Syntax) : TermElabM Unit := do
  let vars := members.filterMap fun m =>
    if m.isOfKind ``Lang.inMember then some ((declaredIdent m[1]).1, (if m[2].isNone then none else some m[2][1]), true, false)
    else if m.isOfKind ``Lang.outMember then
      some ((declaredIdent m[3]).1, (if m[4].isNone then none else some m[4][1]), false, !m[5].isNone)
    else none
  let props := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some (true, x.raw, constraintConjuncts e)
    | `(fren_member| ensure $x:ident : $e) => some (false, x.raw, constraintConjuncts e)
    | `(fren_member| expect $x:ident : $e) => some (false, x.raw, #[])
    | `(fren_member| cover $x:ident : $e) => some (false, x.raw, #[])
    | _ => none
  let wf (e : Syntax) : String := Core.writtenForm (exactText (unparen e))
  let conjunct (assumption : Bool) (e : Syntax) : Core.NatConjunct :=
    let e := unparen e
    if e.getNumArgs == 3 && e[1].isAtom && Core.binaryOps.contains e[1].getAtomVal.trimAscii.toString then
      { assumption, op := .ofOp e[1].getAtomVal.trimAscii.toString, left := wf e[0], right := wf e[2] }
    else { assumption, op := .otherOp, left := "", right := "" }
  let isInt (ty? : Option Syntax) : Bool := ty?.any (exactText · == "Int")
  let bounds := Core.manualNatBounds
    (vars.map fun (x, ty?, isIn, defined) =>
      { name := Core.nameText x.getId, role := if isIn then .input else if defined then .definedOutput else .output
        int := isInt ty? })
    (props.map fun (assumption, _, cs) => cs.map (conjunct assumption))
  for (i, p, k) in bounds do
    let (x, _, isIn, _) := vars[i]!
    let (_, name, cs) := props[p]!
    let msg := Core.manualNatMsg (Core.nameText x.getId) isIn (Core.nameText name.getId) (exactText (unparen cs[k]!))
    let report := { lint := .manualNat, level := ← lintLevel .manualNat, ref := unparen cs[k]!
                    msg }
    modifyLocal fun l => { l with natReports := l.natReports.push (compPath, Core.nameText x.getId, report) }

open Lang in
/-- The name that a member declares, if any: a variable, a call or a
constraint, which share one namespace (`lang::distinct_names`). -/
def memberName? (m : Syntax) : Option Syntax :=
  if m.isOfKind ``Lang.inMember then some m[1]
  else if m.isOfKind ``Lang.outMember then some m[3]
  else if m.isOfKind ``Lang.defineMember then some m[1]
  else if m.isOfKind ``Lang.existsMember || m.isOfKind ``Lang.letMember then some m[2]
  else if m.isOfKind ``Lang.callMember then some m[1]
  else if let some (_, x, _) := constraint? m then some x
  else none

open Lang in
/-- The kind of a member without its evidence setting, for
`arbitrary_source_item_ordering`, by its syntax kind; `none` for what is
not one, which a procedure's members never are. -/
def memberKind? (m : Syntax) : Option Core.MemberKind :=
  [(``Lang.useMember, .use), (``Lang.useGroupMember, .use), (``Lang.existsMember, .exists), (``Lang.letMember, .let),
    (``Lang.defineMember, .define), (``Lang.assumeMember, .assumption), (``Lang.callMember, .call),
    (``Lang.ensureMember, .guarantee),
    (``Lang.expectMember, .expectation), (``Lang.coverMember, .cover)].lookup m.getKind

open Lang in
/-- The names that a defined output's definition, or a call's
bindings, mention: a binding `x` without `:= e` mentions `x`. -/
def memberMentions (m : Syntax) : Array Name :=
  if m.isOfKind ``Lang.defineMember then (pathMentions m[3]).map (·.getRoot)
  else if m.isOfKind ``Lang.letMember then (pathMentions m[5]).map (·.getRoot)
  else if m.isOfKind ``Lang.callMember then m[5].getSepArgs.foldl (init := #[]) fun acc a => acc ++ (pathMentions a).map (·.getRoot)
  else #[]

/-- Records `arbitrary_source_item_ordering` on the procedure `stx`, whose
members, with their evidence settings, are `raw`, and `members` without
them (`lint::arbitrary_source_item_ordering`). -/
def lintMemberOrder (stx open_ : Syntax) (raw members : Array Syntax) : CommandElabM Unit := do
  let some kinds := members.mapM memberKind? | return
  let some i := Core.firstOutOfOrder? kinds | return
  let msg := Core.memberOrderMsg kinds[i]! kinds[i - 1]!
  let some sub := stx.getSubstring? false false | return
  let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos (p.getD sub.startPos)).length
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  let names := members.map fun m => (memberName? m).map fun x => (declaredIdent x).1.getId
  let mentions := members.map fun m => (memberMentions m).filterMap fun n => names.findIdx? (· == some n)
  let ranges := raw.map fun m => ({ start := off m.getPos?, stop := off m.getTailPos? } : Core.Range)
  let fix? := Core.memberOrderFix? src (off open_.getTailPos?) ranges kinds mentions
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown && fix?.isSome
  recordLint .arbitrarySourceItemOrdering raw[i]! (if fixable then msg.note Core.fixHelp else msg)

/-! ### `elabComp`, in parts

Each part is a definition of its own, so that the compiler, whose time grows
faster than the length of a `do` block, compiles several short ones, and
in parallel. -/

section
open Lang

/-- A procedure's variables, the names declared so far, and whether every one
was declared without an error, reporting each error, and one cycle of
definitions, as the `fren` command does. -/
def elabCompVars (scope : Name) (members : Array Syntax) : TermElabM (Array Var × NameSet × Bool) := do
  let mut ok := true
  let mut names : NameSet := {}
  let mut vars : Array Var := #[]
  for m in members do
    let (role, isPub, isDet, x, ty?, defn?) ← match m.getKind with
      -- An input has no definition (`checkParsed`).
      | ``Lang.inMember =>
        pure (Core.Role.input, true, false, m[1], if m[2].isNone then none else some m[2][1], none)
      | ``Lang.outMember =>
        pure (.output, !m[0].isNone, !m[1].isNone, m[3], if m[4].isNone then none else some m[4][1], definition? m)
      | _ => continue
    -- An error in shadowing leaves the variable's meaning clear.
    let x ← try declare x scope
      catch ex => logException ex; ok := false; pure (declaredIdent x).1
    names := names.insert x.getId
    lintName .variable x.getId x
    try
      if let some ty := ty? then checkFnTypeSite .variable ty
      let (ty, ptype) ← varPType scope x ty?
      let st ← getState
      unless (← getLocal).inSubset || Core.variableTypeAccepted (role == .output) (factsOf st ptype).unbounded defn?.isSome do
        throwErrorAt x (Core.unboundedOutputMsg x.getId ptype.text).text
      let fact? ← factPred? ty ptype
      vars := vars.push { name := x.getId, role, isPub, isDet, «type» := ty, ref := x, defn?, ptype, fact? }
    catch ex => logException ex; ok := false
  -- One cycle is reported, as by the `fren` command.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    logErrorAt v.ref (Core.cyclicDefinitionMsg cycle).text; ok := false
  return (vars, names, ok)

/-- A procedure's calls, whose variables follow the procedure's own `vars`: the
calls still to elaborate, all the variables, the names declared so
far, and whether every call was resolved. -/
def elabCompInsts (scope : Name) (members : Array Syntax) (vars : Array Var) (names : NameSet) :
    TermElabM (Array PendingInst × Array Var × NameSet × Bool) := do
  let mut ok := true
  let mut vars := vars
  let mut names := names
  let mut pending : Array PendingInst := #[]
  for m in members do
    unless m.isOfKind ``Lang.callMember do continue
    let (x, p, bs) := (m[1], m[3], m[5].getSepArgs)
    -- A call named by a literal is not resolved, which would report
    -- its name again; the `fren` command stops at the first report too.
    if let .error msg := Core.checkNotLiteral (declaredIdent x).1.getId then
      logErrorAt x msg.text; ok := false; continue
    let x ← try declare x scope
      catch ex => logException ex; ok := false; pure (declaredIdent x).1
    names := names.insert x.getId
    lintName .instance x.getId x
    try
      let (pi, ivars) ← resolveInst scope x p bs vars.size
      pending := pending.push pi
      vars := vars ++ ivars
      -- Its bindings give each input of its procedure a value, and the
      -- call's assumption check reads them (`unused_assumption`).
      let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Core.Role.input).map (pi.comp.path, ·.name)
      modifyLocal fun l => { l with globalReads := l.globalReads ++ reads }
    catch ex => logException ex; ok := false
  return (pending, vars, names, ok)

/-- A procedure's calls, over its variables `fvs`, and then its definitions,
each after those it mentions, with the earlier ones substituted, so that
each value mentions no defined output: the calls, the generated
definitions so far, the definitions' values, the variables they define,
and the indexes, and whether all were elaborated. -/
def elabCompDefinitions (scope : Name) (vars : Array Var) (pending : Array PendingInst) (declBase : Name)
    (fvs : Array Expr) :
    TermElabM (Array InstInfo × Array (Name × Expr) × Array (Name × Expr) × Array Expr × CompIndexes × Bool) := do
  let instNames := pending.map (·.name)
  let mut good := true
  let mut insts : Array InstInfo := #[]
  let mut indexes : CompIndexes := #[]
  -- The generated definitions, over `fvs`, added once the placeholders
  -- that they use are known.
  let mut defs : Array (Name × Expr) := #[]
  for pi in pending, k in [0:pending.size] do
    try
      let cx := { modName := scope, vars, insts := instNames, place := .binding, current := k }
      let (i, body) ← elabInst cx fvs pi (declBase ++ `call ++ pi.name)
      insts := insts.push i
      defs := defs.push (i.decl, body)
      indexes := indexes ++ (← takeIndexes fvs).map fun (r, q, g) => (pi.name, .binding k, r, q, g)
    catch ex => logException ex; good := false
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
        let dcx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop, emptyOk := Core.Position.declared.checked false false, concatOk := true
                               natOk := v.type.isConstOf ``Nat, expected? := ← coreTy? v.type }
        let t ← toTerm dcx e
        checkDeclared e t v.type fun ty => s!"note: `{v.name}` has type `{ty}`, so its definition must too"
        noteObligation dcx .definition e v.ptype t
        elabProp t v.type
      indexes := indexes ++ (← takeIndexes fvs).map fun (r, q, g) => (v.name, .prop, r, q, g)
      lintBools e (← hidesIn { modName := scope, vars, insts := instNames, place := .prop })
      let value := value.replaceFVars defnFvs (values.map (·.2))
      defs := defs.push (declBase ++ `def ++ v.name, ← mkEq fvs[idx]! value)
      values := values.push (v.name, value)
      defnFvs := defnFvs.push fvs[idx]!
    catch ex => logException ex; good := false
  return (insts, defs, values, defnFvs, indexes, good)

/-- A procedure's assumptions, requirements and expectations, over its variables
`fvs`, where the defined outputs `defnFvs` have the values `values`: the
constraints, the generated definitions with theirs added, the indexes with
theirs added, the names declared, and whether all were elaborated. -/
def elabCompConstraints (scope : Name) (members : Array Syntax) (vars : Array Var) (instNames : Array Name)
    (declBase : Name) (fvs defnFvs : Array Expr) (values : Array (Name × Expr)) (names : NameSet)
    (defs : Array (Name × Expr)) (indexes : CompIndexes) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes × NameSet × Bool) := do
  let mut good := true
  let mut names := names
  let mut defs := defs
  let mut indexes := indexes
  let mut props : Array PropInfo := #[]
  for m in members do
    let some (kind, x, e) := constraint? m | continue
    if let .error msg := Core.checkNoBang x.getId then
      logErrorAt x msg.text; good := false; continue
    names := names.insert x.getId
    if let .original .. := x.getHeadInfo then lintName .constraint x.getId x
    try
      if x.getId.toString.endsWith "?" then
        throwErrorAt x (Core.propNameMsg x.getId).text
      let cx := { modName := scope, vars, insts := instNames, place := if kind == .assume then .assume else .prop }
      discard (takeIndexes fvs)
      let t ← toTerm cx e
      checkDeclared e t (mkConst ``Bool) fun _ => "note: a constraint is a `Bool`"
      let body ← elabProp t
      -- An assumption sees defined outputs only as their definitions.
      let subst (b : Expr) := if kind == .assume then b.replaceFVars defnFvs (values.map (·.2)) else b
      let body := subst body
      let place : Core.IndexPlace := if kind == .assume then .assume else .prop
      let leaf := match x.getHeadInfo with | .original .. => false | _ => true
      indexes := indexes ++ (← takeIndexes fvs subst).map fun (r, q, g) =>
        (x.getId, place, r, q, if leaf then mkApp (mkConst ``Fren.leafObligation) g else g)
      lintBools e (← hidesIn cx)
      lintConstant cx kind.keyword e
      let trig ← triggerOf cx e
      let trigger? ← trig.mapM fun (t, _) => do mkLambdaFVars fvs (← elabProp t)
      let branchGroups ← clauseBranchGroups cx x.getId e fvs subst
      let memberGroups ← clauseMemberGroups cx x.getId e fvs subst
      let decl := declBase ++ Name.mkSimple kind.keyword ++ x.getId
      defs := defs.push (decl, body)
      props := props.push {
        kind, name := x.getId, ref := x, body := ← mkLambdaFVars fvs body,
        trigger?, triggerRef? := trig.map (·.2), decl, branchGroups, memberGroups }
    catch ex => logException ex; good := false
  let mut expanded := #[]
  for prop in props do
    let source := (members.findSome? fun member => do
      let (_, name, expression) ← constraint? member
      if name.getId == prop.name then some expression else none).getD prop.ref
    let cx : ExprCtx := { modName := scope, vars, insts := instNames, place := if prop.kind == .assume then .assume else .prop }
    let (leaves, generated, sites) ← expandPredicateConstraint cx prop source fvs
    if leaves.any (fun leaf => leaf.name != prop.name) then
      indexes ← indexes.mapM fun (name, place, ref, question, goal) => do
        if name == prop.name then
          return (name, place, ref, question, ← mkLambdaFVars fvs (mkApp (mkConst ``Fren.leafObligation) (goal.beta fvs)))
        else return (name, place, ref, question, goal)
    expanded := expanded ++ leaves
    defs := defs ++ generated
    indexes := indexes ++ sites
  return (expanded, defs, indexes, names, good)

/-- Instantiate a specification positionally and generate ordinary expectation
propositions. Specification assumptions are deliberately absent. -/
def elabRefinesMembers (scope : Name) (members : Array Syntax) (vars : Array Var)
    (insts : Array InstInfo) (declBase : Name) (fvs defnFvs : Array Expr)
    (values : Array (Name × Expr)) (props : Array PropInfo) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
  let mut out := #[]
  let mut defs := #[]
  let mut indexes := #[]
  let mut earlier : Array Name := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then earlier := earlier.push m[1].getId
    unless m.isOfKind ``Lang.refinesMember do continue
    let call := m[1].getId
    let some inst := insts.find? (·.name == call)
      | throwErrorAt m[1] "`{call}` is not a call in this global expectation block"
    let r ← resolvePath scope (pathSegs m[2])
    let .item { kind := .compItem, path, .. } := r
      | throwErrorAt m[2] (Core.notACompMsg r).text
    let some spec := (← getState).comps.get? path
      | throwErrorAt m[2] "unknown specification procedure"
    let some concrete := (← getState).comps.get? inst.comp
      | throwErrorAt m[1] "unknown called procedure"
    noteCounts spec m[2]
    unless spec.decidable do modifyLocal fun l => { l with outsideCore := true }
    let inputs := spec.vars.filter fun v => v.name.isAtomic && v.role == .input
    let results := spec.vars.filter fun v => v.name.isAtomic && v.role == .output && v.isPub
    let actual := concrete.vars.filter fun v => v.name.isAtomic && v.role == .output && v.isPub
    let args := m[4].getSepArgs
    unless args.size == inputs.size do
      throwErrorAt m[2] (Core.callArityMsg (Core.showPath path) (inputs.map (Core.nameText ·.name)) args.size).text
    unless results.size == actual.size do
      throwErrorAt m[2] "refinement result count mismatch: specification has {results.size}, call has {actual.size}"
    for v in spec.vars do
      if v.name.isAtomic && v.role != .input && !v.isPub && v.defn?.isNone then
        throwErrorAt m[2] "specification `exists` variable `{v.name}` is not supported by `refines`"
    discard (takeIndexes fvs)
    let cx : ExprCtx := { modName := scope, vars, insts := insts.map (·.name), place := .prop }
    let inputValues ← (inputs.zip args).mapM fun (v, arg) => do
      let t ← toTerm { cx with natOk := v.type.isConstOf ``Nat, expected? := ← coreTy? v.type } arg
      checkDeclared arg t v.type fun ty => s!"note: specification parameter `{v.name}` has type `{ty}`"
      elabProp t v.type
    let resultValues ← (results.zip actual).mapM fun (v, cv) => do
      let some i := vars.findIdx? (·.name == call ++ cv.name)
        | throwErrorAt m "missing call result"
      let value := fvs[i]!
      if ← isDefEq cv.type v.type then return value
      if cv.type.isConstOf ``Nat && v.type.isConstOf ``Int then
        return mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) value
      throwErrorAt m[2] "refinement result type mismatch at `{v.name}`: call result `{cv.name}` cannot flow to the specification result"
    let (body, specificationIndexes) ← withLocalDeclsD (spec.vars.map fun v => (v.name, fun _ => pure v.type)) fun sfvs => do
      let mut slice := sfvs
      for v in inputs, value in inputValues do
        slice := slice.set! (spec.vars.findIdx? (·.name == v.name)).get! value
      for v in results, value in resultValues do
        slice := slice.set! (spec.vars.findIdx? (·.name == v.name)).get! value
      -- Stored definitions already substitute dependencies on other lets.
      -- Public results retain the concrete result, even when defined in the spec.
      for (name, value) in spec.defs do
        let some i := spec.vars.findIdx? (·.name == name) | continue
        unless spec.vars[i]!.isPub do slice := slice.set! i (value.beta slice)
      let guarantees := spec.ensures.map (·.body.beta slice)
      let definitions ← spec.defs.filterMapM fun (name, value) => do
        let some i := spec.vars.findIdx? (·.name == name) | return none
        unless spec.vars[i]!.isPub do return none
        return some (← mkEq slice[i]! (value.beta slice))
      let typedResults ← ((inputs.zip inputValues) ++ (results.zip resultValues)).filterMapM fun (v, value) => do
        let some obligation := v.ptype.obligation (← getState).shapeOf | return none
        let pred ← predOf v.type obligation
        return some (pred.beta #[value])
      let goal := mkAndN (guarantees ++ definitions ++ typedResults).toList
      let internalFacts := (spec.vars.zip slice).filterMap fun (v, value) =>
        if v.name.isAtomic then none else v.fact?.map (·.beta #[value])
      let callFacts := internalFacts ++ spec.insts.map fun i => mkAnd (i.bindings.beta slice) (i.behaviour.beta slice)
      let internal := (spec.vars.zip sfvs).filterMap fun (v, fv) => if v.name.isAtomic then none else some fv
      let close (goal : Expr) : TermElabM Expr := do
        let goal ← if callFacts.isEmpty then pure goal else mkArrow (mkAndN callFacts.toList) goal
        mkForallFVars internal goal
      let checked := spec.ensures.map (·.name) ++ spec.defs.map (·.1)
      let specificationIndexes ← spec.indexes.filterMapM fun (n, _, _, question, value) => do
        unless question.isNone && checked.contains n do return none
        return some (← mkLambdaFVars fvs (← close (value.beta slice)))
      return (← close goal, specificationIndexes)
    let mut serial := defs.size + 1
    while (props ++ out).any (·.name == Name.mkSimple s!"refines_{serial}") do serial := serial + 1
    let name := Name.mkSimple s!"refines_{serial}"
    let decl := declBase ++ `expect ++ name
    indexes := indexes ++ ((← takeIndexes fvs).map fun (r, q, g) => (name, Core.IndexPlace.prop, r, q, g))
      ++ specificationIndexes.map (fun g => (name, Core.IndexPlace.prop, m, none, g))
    if !m[6].isNone then
      let assumptions := (props.filter (·.kind == .assume)).map (·.body.beta fvs)
      let calls := (insts.filter fun i => earlier.contains i.name).map fun i => mkAnd (i.bindings.beta fvs) (i.behaviour.beta fvs)
      let definitions ← (values.zip defnFvs).mapM fun ((_, value), fv) => mkEq fv value
      let goal ← mkForallFVars fvs (← mkArrow (mkAndN (assumptions ++ calls ++ definitions).toList) body)
      let tacs : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨m[6][1]⟩
      let pf ← withoutErrToSorry <| Term.elabTermEnsuringType (← `(by $tacs)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      if pf.hasSorry then throwErrorAt m[6] "a refinement proof must not contain `sorry`"
      if pf.hasMVar then throwErrorAt m[6] "refinement proof has unresolved goals"
      -- Kernel-check the proof while all block variables are abstracted.
      let uses ← usesOf #[goal, pf]
      let (proofType, proofValue) ← withUses uses fun xs => do
        return (← mkForallFVars xs (replaceUses uses xs goal), ← mkLambdaFVars xs (replaceUses uses xs pf))
      addDecl (.thmDecl { name := decl ++ `proof, levelParams := [], «type» := proofType, value := proofValue })
    defs := defs.push (decl, body)
    if m[6].isNone then
      out := out.push { kind := .expect, name, ref := m, decl, trigger? := none, triggerRef? := none, body := ← mkLambdaFVars fvs body }
  return (out, defs, indexes)

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a procedure's
constraints. -/
def lintDuplicateConstraints (members : Array Syntax) : TermElabM Unit := do
  let constraints := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some (Core.ConstraintKind.assume, x.raw, e.raw)
    | `(fren_member| ensure $x:ident : $e) => some (.ensure, x.raw, e.raw)
    | `(fren_member| expect $x:ident : $e) => some (.expect, x.raw, e.raw)
    | `(fren_member| cover $x:ident : $e) => some (.cover, x.raw, e.raw)
    | _ => none
  -- Cover goals are compared with each other, and constraints with each other.
  for group in #[constraints.filter (·.1 != .cover), constraints.filter (·.1 == .cover)] do
    for (i, j) in Core.repeatedConstraints (group.map fun (_, _, e) => srcText (unparen e)) do
      let (k, x, _) := group[i]!
      let (k', x', _) := group[j]!
      let msg := Core.duplicateConstraintMsg k' k x'.getId.toString
      let fixable := (Core.duplicateConstraint k' k true).2 && (← getLocal).inMarkdown
      recordLint .duplicateConstraint x (if fixable then msg.note Core.fixHelp else msg)

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
procedure's outputs. -/
def lintOutputs (lcx : ExprCtx) (members : Array Syntax) (vars : Array Var) : TermElabM Unit := do
  let reqs := members.filterMap fun m => match constraint? m with
    | some (.ensure, x, e) => some (x.getId, e)
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
    let mentioned ← match v.defn? with | some d => mentionedNames lcx d | none => pure []
    let (constant, definable) := Core.outputLints v.defn?.isSome mentioned about.size equation
    if constant then recordLint .constantOutput v.ref (Core.constantOutputMsg v.name)
    if definable then recordLint .definableOutput v.ref (Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a procedure's cover goals: each
assumption and guarantee as its kind, its name and its written form. -/
def lintTrivialCover (lcx : ExprCtx) (members : Array Syntax) : TermElabM Unit := do
  let facts := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some ("assumption", x.getId, Core.writtenForm (exactText (unparen e)))
    | `(fren_member| ensure $x:ident : $e) => some ("guarantee", x.getId, Core.writtenForm (exactText (unparen e)))
    | _ => none
  for m in members do
    let `(fren_member| cover $x:ident : $e) := m | continue
    let w := Core.writtenForm (exactText (unparen e))
    -- Only whether it has one: what elaborating it reports is reported where it is.
    let saved ← getLocal
    let trigger ← try Option.isSome <$> triggerOf lcx e catch _ => pure false
    modifyLocal fun _ => saved
    let same? := (facts.find? (·.2.2 == w)).map fun (k, n, _) => (k, n)
    if let some why := Core.trivialCover trigger same? then
      recordLint .trivialCover x (Core.trivialCoverMsg x.getId why)

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a procedure's
requirements. -/
def lintCaseSplitGuarantees (lcx : ExprCtx) (members : Array Syntax) (vars : Array Var) : TermElabM Unit := do
  -- Each requirement `when T, y = e`, as its name, where it is
  -- reported, `y`, the operator, `T` and the text of `e`.
  let mut cases : Array (Name × Syntax × String × String × Core.VariantTest × String) := #[]
  for m in members do
    let `(fren_member| ensure $x:ident : $e) := m | continue
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
    if Core.caseSplitGuarantees cs.size (Core.repeatedVariants ts) then
      recordLint .caseSplitGuarantees cases[group[1]!]!.2.1 (Core.caseSplitGuaranteesMsg y op cs (Core.untestedVariants n ts))

/-- Adds a procedure's generated definitions `defs` over its variables `fvs`,
with `p.defs`, `p.assumes` and `p.ensures`, and `p.out.d` for each definition
that mentions only inputs. -/
def addCompDefs (vars : Array Var) (declBase : Name) (fvs : Array Expr) (uses : Array Name)
    (props : Array PropInfo) (values : Array (Name × Expr)) (defs : Array (Name × Expr)) : TermElabM Unit := do
  let appD (decl : Name) := mkAppN (Lean.mkConst decl) (uses.map (Lean.mkConst ·) ++ fvs)
  let app (p : PropInfo) := appD p.decl
  let mut defs := defs
  unless values.isEmpty do
    defs := defs.push (declBase ++ `defs, mkAndN (values.map fun (d, _) => appD (declBase ++ `def ++ d)).toList)
  -- The constraints of the inputs' and outputs' types first
  -- (`Reqs/Generated#procedures`).
  let typeFacts (role : Core.Role) : List Expr := ((vars.zip fvs).filter fun (v, _) =>
      v.name.isAtomic && v.role == role && v.defn?.isNone).toList.filterMap fun (v, x) =>
    v.fact?.map (·.beta #[x])
  defs := defs ++ #[(declBase ++ `assumes, mkAndN (typeFacts .input ++ (props.filter (·.kind == .assume) |>.map app).toList)),
    (declBase ++ `ensures, mkAndN (typeFacts .output ++ (props.filter (·.kind == .ensure) |>.map app).toList))]
  for (decl, body) in defs do
    addUsesDef uses decl (← mkLambdaFVars fvs body)
  -- `p.out.d`, a function of the inputs, when the definition mentions
  -- only inputs.
  let inputs := (vars.zip fvs).filter (·.1.role == .input) |>.map (·.2)
  for (d, value) in values do
    let others := fvs.filter (!inputs.contains ·)
    unless others.any (value.containsFVar ·.fvarId!) do
      addUsesDef uses (declBase ++ `out ++ d) (← mkLambdaFVars inputs value)

/-- A procedure's calls, definitions and constraints, elaborated over its
variables, with its lints of them, and, if all were elaborated, its
generated definitions added: the constraints, the calls, the
placeholders used, the definitions' values over the variables, the
indexes, and whether all were elaborated. -/
def elabCompBody (scope : Name) (members : Array Syntax) (vars : Array Var) (pending : Array PendingInst)
    (declBase : Name) (varsOk : Bool) (varNames : NameSet) :
    TermElabM (Array PropInfo × Array InstInfo × Array Name × Array (Name × Expr) × CompIndexes × Bool) := do
  let instNames := pending.map (·.name)
  let decls := vars.map fun v => (v.name, fun _ => pure v.type)
  withLocalDeclsD decls fun fvs => do
    discard (takeIndexes fvs)
    let (insts, defs, values, defnFvs, indexes, defsOk) ← elabCompDefinitions scope vars pending declBase fvs
    let (props, defs, indexes, _, propsOk) ←
      elabCompConstraints scope members vars instNames declBase fvs defnFvs values varNames defs indexes
    let (refines, refineDefs, refineIndexes) ←
      elabRefinesMembers scope members vars insts declBase fvs defnFvs values props
    let props := props ++ refines
    let defs := defs ++ refineDefs
    let indexes := indexes ++ refineIndexes
    let good := varsOk && defsOk && propsOk
    lintDuplicateConstraints members
    let lcx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop }
    lintOutputs lcx members vars
    lintTrivialCover lcx members
    lintCaseSplitGuarantees lcx members vars
    let uses ← usesOf ((← fvs.mapM fun x => inferType x) ++ defs.map (·.2))
    if good then addCompDefs vars declBase fvs uses props values defs
    let closed ← values.mapM fun (d, v) => return (d, ← mkLambdaFVars fvs v)
    return (props, insts, uses, closed, indexes, good)

/-- `unused_variables` and `unused_assumption` (`lint::unused_assumption`)
of a procedure whose items were all elaborated: the latter is recorded, to be
reported unless the file reads one of the inputs (`reportLints`), or one
that another assumption ties to a used variable, transitively. -/
def lintCompUnused (scope path : Name) (members : Array Syntax) (vars : Array Var) (instNames : Array Name)
    (global : Bool := false) : TermElabM Unit := do
  let mut mentioned := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do mentioned := mentioned ++ pathMentions a
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do mentioned := mentioned ++ pathMentions a
    if let some (_, _, e) := constraint? m then mentioned := mentioned ++ pathMentions e
  for v in vars do
    if let some d := v.defn? then mentioned := mentioned ++ pathMentions d
  -- A public definition says what the output is, so it is used.
  let own := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Core.unmentioned (own.map fun v => (v.name, v)) mentioned do
    recordLint .unusedVariables v.ref (Core.unusedVariableMsg x global (v.role == .output))
  let mut others := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do others := others ++ pathMentions a
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do others := others ++ pathMentions a
    if let some (kind, _, e) := constraint? m then
      unless kind == .assume do others := others ++ pathMentions e
  for v in vars do
    if let some d := v.defn? then others := others ++ pathMentions d
  let inputs := vars.filter (·.role == .input) |>.map (·.name)
  let level ← lintLevel .unusedAssumption
  let assumed := members.filterMap fun m => match constraint? m with
    | some (.assume, x, e) => some (x, e)
    | _ => none
  let mss := assumed.map fun (_, e) => (pathMentions e).foldl (init := #[]) fun acc n =>
    if vars.any (·.name == n) && !acc.contains n then acc.push n else acc
  -- The uninterpreted functions that they apply link too.
  let acx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop }
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do others := others ++ (← appliedFns acx a)
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do others := others ++ (← appliedFns acx a)
    if let some (kind, _, e) := constraint? m then
      unless kind == .assume do others := others ++ (← appliedFns acx e)
  for v in vars do
    if let some d := v.defn? then others := others ++ (← appliedFns acx d)
  let links ← assumed.mapIdxM fun i (_, e) => return mss[i]! ++ (← appliedFns acx e)
  let used := Core.usedAssumptions links others
  for (x, _) in assumed, ms in mss, ls in links, u in used do
    if Core.unusedAssumption ms.size (ms.all inputs.contains) u false then
      let r : Core.AssumptionRecord := { component := path, name := x.getId, inputs := ms, links := ls, level }
      modifyLocal fun l => { l with assumptions := l.assumptions.push (r, x) }

/-- `unrelated_binders` (`lint::unrelated_binders`) of the global
expectation `n` with the members `members`: whether its calls fall into
groups that nothing relates. An atom of a constraint relates the calls it
mentions and those whose arguments mention a parameter it mentions; a call
relates itself to the calls its arguments mention; and a parameter
relates the calls whose arguments mention it. -/
def lintUnrelatedCalls (nameStx : Syntax) (n : String) (members : Array Syntax) : TermElabM Unit := do
  let calls := members.filterMap fun m =>
    if m.isOfKind ``Lang.callMember then
      some ((declaredIdent m[1]).1.getId, m[5].getSepArgs.flatMap fun a => (pathMentions a).map (·.getRoot))
    else none
  let params := members.filterMap fun m =>
    if m.isOfKind ``Lang.inMember then some (declaredIdent m[1]).1.getId else none
  let names := calls.map (·.1)
  let reading (p : Name) := (calls.filter (·.2.contains p)).map (·.1)
  let expand (roots : Array Name) := roots.filter names.contains ++ (roots.filter params.contains).flatMap reading
  let atoms := members.flatMap (fun m => match constraint? m with
      | some (_, _, e) => (boolNode "" 0 (unparen e)).atoms.map fun a => expand ((pathMentions a.ref).map (·.getRoot))
      | none => if m.isOfKind ``Lang.refinesMember then
          #[expand (#[m[1].getId] ++ m[4].getSepArgs.flatMap fun a => (pathMentions a).map (·.getRoot))]
        else #[])
    -- A relation of one call alone puts it in no group.
    ++ (calls.map (fun ((w, roots) : Name × Array Name) => #[w] ++ roots.filter names.contains) ++ params.map reading).filter (fun (a : Array Name) => a.size ≥ 2)
  let groups := Core.binderGroups names atoms
  if Core.unrelatedBinders groups.size then
    recordLint .unrelatedBinders nameStx (Core.unrelatedBindersMsg n groups)

/-- A procedure's members, elaborated, with the procedure recorded if all were: whether
they were, and the generated declarations. -/
def elabCompMembers (scope path modName declBase : Name) (isPub : Bool) (nameStx : Syntax)
    (members : Array Syntax) (tested : Core.Tested) (enumerated : Core.Tested := {}) (enumSize : Nat := 3)
    (global : Bool := false) :
    TermElabM (Bool × Array Name) := do
  unless global do
    for m in members do
      if m.isOfKind ``Lang.refinesMember then
        throwErrorAt m "`refines` is accepted only in global expectation blocks"
  let (vars, names, ok) ← elabCompVars scope members
  unless ok do return (false, #[])
  let (pending, vars, names, ok) ← elabCompInsts scope members vars names
  let instNames := pending.map (·.name)
  -- A call that is not resolved is reported once, not again at each
  -- use of it, as by the `fren` command (`Reqs/View#static-errors`).
  unless ok do return (false, #[])
  if global then lintUnrelatedCalls nameStx path.getString! members
  -- Bindings; assumptions, requirements and expectations
  let (props, insts, uses, values, indexes, ok) ← elabCompBody scope members vars pending declBase ok names
  lintManualNat path members
  if ok then lintCompUnused scope path members vars instNames global
  let mut generated := insts.map (·.decl) ++ props.map (·.decl) ++ #[declBase ++ `assumes, declBase ++ `ensures]
    ++ values.map (declBase ++ `def ++ ·.1) ++ (if values.isEmpty then #[] else #[declBase ++ `defs])
  let env ← getEnv
  generated := generated ++ (values.map (declBase ++ `out ++ ·.1)).filter env.contains
  if ok then
    let (relational, counts) ← checkCounts
    let expandEvidence (evidence : Core.Tested) : Core.Tested :=
      { evidence with props := evidence.props ++ props.filterMap fun prop =>
          if prop.evidenceOwner?.any evidence.props.contains && !evidence.props.contains prop.name then some prop.name else none }
    let tested := expandEvidence tested
    let enumerated := expandEvidence enumerated
    let info : CompInfo := { path, vars, props, insts, ref := nameStx, decl := declBase, uses, defs := values
                             decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied
                             relational, counts, indexes, tested, enumerated, enumSize, guarded := (← getLocal).guardedUsed
                             global }
    -- A global expectation is an item that nothing calls
    -- (`Reqs/Lang/Global`).
    if global then
      record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
      record (.globalInfo path info)
    else
      record (.item { item := { kind := .compItem, path, isPub, owner := modName }, ref := nameStx })
      record (.compInfo info)
  return (ok, generated)

/-- The results of the procedure `stx`: `fren_result`s. -/
def procResults (stx : Syntax) : Array Syntax := if stx[6].isNone then #[] else stx[6][2].getSepArgs

/-- Reports an `out` member of the procedure `stx` whose name is not one of
its results (`F0444`), as the `fren` command's parser does. -/
def checkProcMembers (stx : Syntax) : CommandElabM Unit := do
  let results := (procResults stx).map fun r => (declaredIdent r[2]).1.getId
  for m0 in stx[8].getArgs do
    let (m, _) ← unwrapEvidence m0
    if m.isOfKind ``Lang.defineMember && !results.contains m[1].getId then
      throwErrorAt (mkNullNode #[m[0], m[1]]) (Core.procOutMsg (Core.nameText m[1].getId)).text

open Lang in
/-- One source clause's independent conjunction leaves, preserving lexical
and leading guard wrappers. Disjunction/negation/equivalence remain one
clause; generated paths are logical names, not user binder declarations. -/
partial def clauseLeaves (owner : Name) (source : Syntax) : CommandElabM (Array (Syntax × Syntax)) := do
  let e := unparen source
  if isBooleanGuard e then
    return (← clauseLeaves owner e[3]).map fun (name, body) => (name, e.setArg 3 body)
  if e.isOfKind ``Lang.letExpr then
    return (← clauseLeaves owner e[3]).map fun (name, body) => (name, e.setArg 3 body)
  if let some ("and", members) := booleanBlockView e then
    let labels := members.filterMap (·.1)
    if let some k := (Core.repeatsAt (labels.map (·.getId)))[0]? then
      throwErrorAt labels[k]! "a Boolean block repeats label `{labels[k]!.getId}`"
    let mut leaves := #[]
    for (label, body) in members, i in [0:members.size] do
      if let some label := label then
        discard (segName label)
        liftMsg label (Core.checkNoBang label.getId)
      let segment := label.map (·.getId.toString) |>.getD (toString (i + 1))
      let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString ++ "." ++ segment)
      let child ← clauseLeaves name body
      leaves := leaves ++ child.map fun (ref, value) =>
        (if ref.getId == name then (mkIdentFrom (label.getD body) name).raw else ref, value)
    return leaves
  let owner := if owner.isAnonymous then Name.mkSimple "1" else owner
  return #[(mkIdentFrom source owner, source)]

partial def booleanBlockRoot (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then booleanBlockRoot e[3]
  else (unparen e).isOfKind ``Lang.booleanBlockExpr

partial def conjunctionClause (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then conjunctionClause e[3]
  else (booleanBlockView e).any (·.1 == "and")

/-- Normalize the optional outer label and conjunction-clause sugar
before evidence settings and duplicate-member checks are collected. -/
def splitBooleanMember (member : Syntax) : CommandElabM (Option (Array Syntax)) := do
  let bare := member.isOfKind ``Lang.bareAssumeMember || member.isOfKind ``Lang.bareEnsureMember || member.isOfKind ``Lang.bareExpectMember
  let parsed := constraint? member
  if !bare && parsed.isNone then return none
  let (kind, owner, expression) := if bare then
      let kind := if member.isOfKind ``Lang.bareAssumeMember then PropKind.assume
                  else if member.isOfKind ``Lang.bareEnsureMember then .ensure else .expect
      (kind, Name.anonymous, withWhere member[1] member[2])
    else let (kind, name, expression) := parsed.get!; (kind, name.getId, expression)
  if bare && !booleanBlockRoot expression then throwErrorAt expression "expected a named clause or a Boolean block"
  if kind == .cover || (!bare && !conjunctionClause expression) then return some #[member]
  let leaves ← clauseLeaves owner expression
  return some (leaves.map fun (name, body) =>
    let syntaxKind := match kind with | .assume => ``Lang.assumeMember | .ensure => ``Lang.ensureMember
                                      | .expect => ``Lang.expectMember | .cover => ``Lang.coverMember
    mkNode syntaxKind #[member[0], name, mkAtom ":", body, mkNullNode])

/-- The members of the procedure `stx` as a component's, as the `fren`
command reads them: its parameters as inputs, its results as public
outputs, each defined by the `out` member of its block that defines it, at
most one (`F0421`), and its block's `exists` and `let` members as private
outputs. Each keeps its evidence setting. -/
def procMembers (stx : Syntax) : CommandElabM (Array Syntax) := do
  let results := procResults stx
  let resultNames := results.map fun r => (declaredIdent r[2]).1.getId
  let mut defs : Array (Name × Syntax) := #[]
  let mut body := #[]
  for m0 in stx[8].getArgs do
    let (m, set?) ← unwrapEvidence m0
    let rewrap (inner : Syntax) : Syntax := match set? with
      | some (_, ev) => ev.setArg 4 inner
      | none => inner
    if let some split ← splitBooleanMember m then
      body := body ++ split.map rewrap
    else if m.isOfKind ``Lang.defineMember && resultNames.contains m[1].getId then
      if defs.any (·.1 == m[1].getId) then throwErrorAt m[1] (Core.resultDefinedTwiceMsg (Core.nameText m[1].getId)).text
      defs := defs.push (m[1].getId, mkNullNode #[m[2], m[3], m[4]])
    else if m.isOfKind ``Lang.existsMember then
      body := body.push (rewrap (mkNode ``Lang.outMember #[mkNullNode, m[0], mkAtom "out", m[2], m[3], mkNullNode]))
    else if m.isOfKind ``Lang.letMember then
      body := body.push (rewrap (mkNode ``Lang.outMember
        #[mkNullNode, m[0], mkAtom "out", m[2], m[3], mkNullNode #[m[4], m[5], m[6]]]))
    else body := body.push m0
  let params := stx[4].getSepArgs.map fun p => mkNode ``Lang.inMember #[mkAtom "in", p[1], p[2], mkNullNode]
  let outs := results.map fun r =>
    let defn := ((defs.find? (·.1 == (declaredIdent r[2]).1.getId)).map (·.2)).getD mkNullNode
    let out : Syntax := mkNode ``Lang.outMember #[mkNullNode #[mkAtom "pub"], r[1], mkAtom "out", r[2], r[3], defn]
    if r[0].isNone then out else
      let e := r[0][0]
      (mkNode ``Lang.evidenceMember #[e[0], e[1], e[2], e[3], out] : Syntax)
  return params ++ outs ++ body

@[command_elab Lang.procCmd] def elabProc : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  checkProcMembers stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "procedure" nameStx
  checkFresh modName n nameStx
  lintName .component n nameStx
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  let declBase ← generatedName path
  let all ← procMembers stx
  -- The evidence settings, apart from the members they set.
  let (members, tested, enumerated) ← testedOf (← evidenceInEffect) all
  let enumSize ← enumSizeInEffect
  -- Its `use`s, and the scope that its paths resolve in.
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`): variables, calls and
  -- constraints share one namespace.
  let named := members.filterMap memberName?
  for x in named do
    if let .original .. := x.getHeadInfo then discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k]! (Core.dupMemberMsg declared[k]!).text
  let raw := stx[8].getArgs
  let body ← raw.mapM fun m => return (← unwrapEvidence m).1
  lintMemberOrder stx stx[7] raw body
  let (ok, generated) ← liftTermElabM <| elabCompMembers scope path modName declBase isPub nameStx members tested enumerated enumSize
  lintDeclared .component n nameStx
  lintLines .component n nameStx stx
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with comps := l.comps.push path }.declared path

/-- The first member of the global expectation `stx`, aligned as a
procedure's, that its block does not accept (`lang::block_member`), with
where it is reported. -/
def blockMemberError? (stx : Syntax) : CommandElabM (Option (Syntax × Core.BlockMember × Bool)) := do
  for r in procResults stx do
    unless Core.blockMemberAccepted .result !r[1].isNone do return some (r[2], .result, !r[1].isNone)
  for m0 in stx[8].getArgs do
    let (m, _) ← unwrapEvidence m0
    let (kind, det) : Core.BlockMember × Bool :=
      if m.isOfKind ``Lang.existsMember then (.exists, !m[0].isNone)
      else if m.isOfKind ``Lang.letMember then (.let, !m[0].isNone)
      else if m.isOfKind ``Lang.defineMember then (.define, false)
      else if m.isOfKind ``Lang.assumeMember then (.assume, false)
      else if m.isOfKind ``Lang.ensureMember then (.ensure, false)
      else if m.isOfKind ``Lang.expectMember then (.expect, false)
      else if m.isOfKind ``Lang.coverMember then (.cover, false)
      else if m.isOfKind ``Lang.callMember then (.call, false)
      else if m.isOfKind ``Lang.refinesMember then (.refines, false)
      else (.use, false)
    unless Core.blockMemberAccepted kind det do return some (m, kind, det)
  return none

/-- `expect n(x: T) { members }`, a global expectation with a block
(`Reqs/Lang/Global`): elaborated as a procedure is, but for the members it
does not accept (`F0417`), and recorded as a global expectation, which
nothing calls. -/
@[command_elab Lang.globalBlockCmd] def elabGlobalBlock : CommandElab := recordingErrors fun stx0 => do
  checkLexemes stx0
  checkParsed stx0
  -- Aligned as a procedure's, after a `pub` that it does not have.
  let stx : Syntax := mkNode ``Lang.procCmd (#[mkNullNode] ++ stx0.getArgs)
  checkProcMembers stx
  lintItem stx0
  lintTrailingCommas stx0
  let modName := (← getLocal).currentModule
  let nameStx := stx[2]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  if let some (ref, m, det) ← blockMemberError? stx then
    throwErrorAt ref (Core.blockMemberMsg m det).text
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  let declBase ← generatedName path
  let all ← procMembers stx
  let (members, tested, enumerated) ← testedOf (← evidenceInEffect) all
  let enumSize ← enumSizeInEffect
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  let named := members.filterMap memberName?
  for x in named do
    if let .original .. := x.getHeadInfo then discard (segName x)
  let declared := named.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k]! (Core.dupMemberMsg declared[k]! (global := true)).text
  let raw := stx[8].getArgs
  let body ← raw.mapM fun m => return (← unwrapEvidence m).1
  lintMemberOrder stx stx[7] raw body
  let (ok, generated) ← liftTermElabM <|
    elabCompMembers scope path modName declBase false nameStx members tested enumerated enumSize (global := true)
  lintDeclared .global n nameStx
  lintLines .global n nameStx stx0
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with globals := l.globals.push path }.declared path

open Lang in
/-- Declared subset aliases reuse ordinary predicate functions and the
shared procedure check protocol, with separate declaration-only checks. -/
@[command_elab Lang.subsetTypeCmd] def elabSubsetType : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  let module := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "type alias" nameStx
  checkFresh module n nameStx
  let path := module ++ n
  let binder := stx[4]
  discard (segName binder)
  let base : TSyntax `fren_type := ⟨stx[6]⟩
  let (ty, baseType) ← liftTermElabM (elabPType module base)
  let some (op, members) := booleanBlockView stx[8]
    | throwErrorAt stx[8] "expected a labelled invariant"
  unless op == "and" && !members.isEmpty do throwErrorAt stx[8] "expected a nonempty labelled invariant list"
  let clauses ← members.mapM fun (label, expression) => do
    let some label := label | throwErrorAt expression "every subset invariant must have a label"
    discard (segName label)
    return (label, expression)
  let labels := clauses.map (·.1.getId)
  if let some k := (Core.repeatsAt labels)[0]? then
    throwErrorAt clauses[k]!.1 ({ code? := some "F0372", headline := s!"duplicate invariant `{Core.showPath (path ++ labels[k]!)}`", label? := some "already declared in this subset type" } : Core.Msg).text
  let position := (charRange (← getFileMap).source nameStx).start
  let mut invariants := baseType.invariants
  let mut pattern := baseType.pat?
  let mut previous : Array Syntax := #[]
  let makeProc (name : Syntax) (parameters results : Syntax) (members : Array Syntax) : Syntax :=
    mkNode ``Lang.procCmd #[mkNullNode #[mkAtom "pub"], mkAtom "proc", name, mkAtom "(", parameters,
      mkAtom ")", results, mkAtom "{", mkNullNode members, mkAtom "}"]
  let ghost (command : Syntax) : CommandElabM Unit := do
    let saved ← getLocal
    try
      modifyLocal fun l => { l with inSubset := true }
      elabProc command
    finally
      modifyLocal fun l => { l with inSubset := saved.inSubset, lintReports := saved.lintReports, natReports := saved.natReports }
  for (label, expression) in clauses do
    let predicateName := Name.mkSimple (Core.subsetPredicateName n.toString label.getId.toString position)
    let predicate := mkIdentFrom label predicateName
    let body : TSyntax `fren_expr := ⟨expression⟩
    let parameter : TSyntax `ident := ⟨binder⟩
    let command ← `(pub fn $predicate:ident($parameter:ident : $base) := $body)
    let before ← getLocal
    modifyLocal fun l => { l with inSubset := true }
    try
      elabFunctionCore command command
    catch ex =>
      let message ← ex.toMessageData.toString
      if (message.splitOn "cannot find").length > 1 then
        throwErrorAt expression ({ code? := some "F0373", headline := "an invariant may mention only its binder, constants and functions", label? := some s!"outside the scope of `{binder.getId}`" } : Core.Msg).text
      throw ex
    finally
      modifyLocal fun l => { l with inSubset := before.inSubset }
    -- Definedness is checked with earlier conjuncts, never unconditionally
    -- as an ordinary function body or using its own membership as a fact.
    let insideInvariant (ref : Syntax) := match ref.getPos?, ref.getTailPos?, expression.getPos?, expression.getTailPos? with
      | some start, some stop, some first, some last => first <= start && stop <= last
      | _, _, _, _ => false
    modifyLocal fun l => { l with
      bodies := before.bodies
      lintReports := before.lintReports ++ (l.lintReports.extract before.lintReports.size).filter (insideInvariant ·.ref)
      natReports := before.natReports ++ (l.natReports.extract before.natReports.size).filter (insideInvariant ·.2.2.ref) }
    invariants := invariants.push { name := path ++ label.getId, predicate := module ++ predicateName }
    let value := unparen expression
    if pattern.isNone && clauses.size == 1 && value.isOfKind ``Lang.isExpr && soleName? value[0] == some binder.getId then
      let (matched, bound, _) ← liftTermElabM <| resolveTop { modName := module, vars := #[], insts := #[], place := .prop } ty (mkIdent `x) true value[2]
      if bound.isEmpty then pattern := some matched
    let validator := mkIdentFrom label (Name.mkSimple (Core.subsetCheckName n.toString s!"defined_{label.getId.toString.toLower}" position))
    let param ← `(fren_proc_param| $parameter:ident : $base)
    let assumptions ← previous.mapIdxM fun i e => do
      let earlier := mkIdentFrom label (Name.mkSimple s!"earlier_{i}")
      `(fren_member| assume $earlier:ident : $(⟨e⟩):fren_expr)
    let value := mkIdentFrom label `subset_predicate?
    let definition ← `(fren_member| let $value:ident := $body)
    ghost (makeProc validator (Syntax.mkSep #[param] (mkAtom ",")) mkNullNode (assumptions.map (·.raw) |>.push definition))
    if let some info := (← getState).comps.get? (module ++ validator.getId) then
      record (.compInfo { info with subsetInvariant? := some (path ++ label.getId) })
    previous := previous.push expression
  record (.item { item := { kind := .typeItem, path, isPub, owner := module }, ref := nameStx })
  record (.aliasInfo path ty { baseType with invariants, pat? := pattern, text := n.toString })
  let inhabit := mkIdentFrom nameStx (Name.mkSimple (Core.subsetCheckName n.toString "inhabited" position))
  let binderIdent : TSyntax `ident := ⟨binder⟩
  let result ← `(fren_result| $binderIdent:ident : $base)
  let resultSyntax := mkNullNode #[mkAtom ":", mkAtom "(", Syntax.mkSep #[result] (mkAtom ","), mkAtom ")"]
  let guarantees ← clauses.mapM fun (label, _) => do
    let predicate := mkIdentFrom label (Name.mkSimple (Core.subsetPredicateName n.toString label.getId.toString position))
    let app ← `(fren_expr| $predicate:ident($binderIdent:ident))
    let labelIdent : TSyntax `ident := ⟨label⟩
    `(fren_member| ensure $labelIdent:ident : $app)
  ghost (makeProc inhabit mkNullNode resultSyntax (guarantees.map (·.raw)))
  if let some info := (← getState).comps.get? (module ++ inhabit.getId) then
    record (.compInfo { info with subset? := some path })

end

/-! ## Constants and global expectations -/

@[command_elab Lang.constCmd] def elabConst : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let valueStx := withWhere stx[6] stx[7]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkConstName n)
  checkFresh modName n nameStx
  lintName .constant n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  liftTermElabM do
    let (type, pt) ← elabPType modName stx[4]
    lintRelTypes modName stx[4]
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := (← getState).placeholders.contains type.constName
    unless Core.constantAccepted abstract false do
      throwErrorAt stx[4] (Core.unknownConstantMsg abstract).text
    modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
    discard (takeIndexes #[])
    let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop, emptyOk := Core.Position.declared.checked false false, natOk := type.isConstOf ``Nat, expected? := ← coreTy? type }
    let t ← toTerm cx valueStx
    noteObligation cx .constant valueStx pt t
    let tables := (← takeIndexes #[]).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
    checkDeclared valueStx t type fun ty => s!"note: `{n}` has type `{ty}`"
    -- A `Bool` value is decided, classically if need be, as a defined
    -- function's body is: an unbounded quantifier, or equality on an
    -- abstract type, has no other `Decidable` instance.
    let value ← if type.isConstOf ``Bool then do
        let p ← elabProp t
        let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
          | .some i => pure i
          | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
        pure (mkApp2 (mkConst ``Decidable.decide) p inst)
      else elabProp t type
    let applies ← applications { modName, vars := #[], insts := #[], place := .prop } valueStx
    unless Core.constantAccepted abstract !applies.isEmpty do
      throwErrorAt applies[0]! (Core.unknownConstantMsg abstract).text
    lintBools valueStx (← hidesIn { modName, vars := #[], insts := #[], place := .prop })
    addDecl (.defnDecl { name := decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
    compileGenerated decl type value
    record (.item { item := { kind := .constItem, path, isPub, owner := modName }, ref := nameStx })
    let int? ← if type.isConstOf ``Int || type.isConstOf ``Nat then intConstValue? { modName, vars := #[], insts := #[], place := .prop } valueStx
      else pure none
    record (.constInfo { path, decl, type, value, int?, guarded := (← getLocal).guardedUsed })
    recordBody path nameStx decl #[] (tables.map fun (r, q, g) => (n, .body, r, q, g))
    unless isPub do recordItem .constant path nameStx
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))

/-- Elaborates a global expectation in its short form, `expect n: e`, into
a `CompInfo` whose path is its module (`Model.Entry.globalInfo`),
generating `decl` for it. Binders over values, `forall (m: M), e`, are a
quantifier around `e`. -/
def elabGlobalInfo (modName n : Name) (nameStx : Syntax) (binderStxs : Array Syntax) (body : Syntax)
    (decl : Name) : TermElabM CompInfo := do
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binderStxs.flatMap (·[1].getArgs)
  for x in binderIds do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt binderIds[k]! (Core.dupBinderMsg declared[k]!).text
  let valueBinders := binderStxs
  let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop }
  discard (takeIndexes #[])
  let t ← if valueBinders.isEmpty then toTerm cx body else quantTerm toTerm cx body true valueBinders body
  checkDeclared body t (mkConst ``Bool) fun _ => "note: an expectation is a `Bool`"
  let e ← elabProp t
  let indexes := (← takeIndexes #[]).map fun (r, q, g) => (n, Core.IndexPlace.prop, r, q, g)
  -- The body is in the scope of the binders over values too.
  lintBools body (← hidesIn cx (valueBinders.flatMap (·[1].getArgs) |>.map fun x =>
    ((declaredIdent x).1.getId, Core.BindingKind.boundName)))
  lintConstant cx "expect" body
  -- A quantifier leaves it without a trigger.
  let trig ← if valueBinders.isEmpty then triggerOf cx body else pure none
  let trigger? ← trig.mapM fun (t, _) => elabProp t
  let value ← mkArrow (mkAndN []) e
  let uses ← usesOf #[value]
  addUsesDef uses decl value
  let prop : PropInfo := {
    kind := .expect, name := n, ref := nameStx, body := e
    trigger?, triggerRef? := trig.map (·.2), decl }
  discard checkCounts
  return { path := modName, vars := #[], props := #[prop], ref := nameStx, decl, uses
           decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied, indexes
           guarded := (← getLocal).guardedUsed }

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
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let nameStx := stx[1]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  startDeclared
  modifyLocal fun l => { l with currentItem := modName ++ n }
  -- `duplicate_constraint` (`lint::duplicate_constraint`), against the
  -- earlier ones of its module.
  let text := globalText stx
  let l ← getLocal
  if let some (_, earlier, _) := l.globalTexts.find? fun (m, _, t) => m == modName && Core.writtenSame t text then
    let msg := Core.duplicateConstraintMsg .expect .expect earlier.toString
    recordLint .duplicateConstraint nameStx (if l.inMarkdown then msg.note Core.fixHelp else msg)
  modifyLocal fun l => { l with globalTexts := l.globalTexts.push (modName, n, text) }
  let path := modName ++ n
  let decl ← generatedName path
  let binders := if stx[3].isNone then #[] else stx[3][1].getArgs
  let info ← liftTermElabM <| elabGlobalInfo modName n nameStx binders (withWhere stx[4] stx[5]) decl
  lintDeclared .global n nameStx
  let all ← evidenceInEffect
  let info := { info with tested := Core.Tested.ofSettings all.tested #[] #[(n, none)] #[] #[]
                          enumerated := Core.Tested.ofSettings all.enumerated #[] #[(n, none)] #[] #[]
                          enumSize := ← enumSizeInEffect }
  record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
  record (.globalInfo path info)
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  modifyLocal fun l => { l with globals := l.globals.push path }.declared path


end Fren
