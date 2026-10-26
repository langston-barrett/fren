-- keep-sorted start
import Fren.FinSet
import Fren.Finite
import Fren.Lint
import Fren.Model
import Fren.SimpSet
import Fren.Syntax
import FrenCore.Checking
import FrenCore.Guards
import FrenCore.Lexical
import FrenCore.Mentions
import FrenCore.Patterns
import FrenCore.Quantifier
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
`assume`/`ensure`/`expect`, plus `assumes` and `ensures`, per comp; a `def` per
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

/-- The name of the field that `.x` reads, at `s` in a `fieldExpr`: an
identifier, or digits, as the field `0` of a newtype is. -/
partial def fieldName (s : Syntax) : Name :=
  if s.isIdent then s.getId
  else if s.isOfKind fieldIdxKind then Name.mkSimple s[0].getAtomVal
  else if s.getNumArgs == 1 then fieldName s[0]
  else .anonymous

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
  left operand;
- `table` as a name: it is a reserved word, which Lean reads as a name
  where an expression starts, as it reads `when`. -/
partial def checkParsed (stx : Syntax) : CommandElabM Unit := do
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

/-- The tokens of `stx`, in order: its atoms and identifiers. -/
partial def tokensOf (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args => args.flatMap tokensOf
  | .missing => #[]
  | _ => #[stx]

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
with `scope`, into the component of that path. -/
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

/-- The path of a type written as one, or `none` for `Set(T)` and `Rel(A, B)`. -/
def typePath? (ty : Syntax) : Option Syntax :=
  if ty.isOfKind ``Lang.fren_path then some ty
  else if ty.isOfKind ``Lang.setType || ty.isOfKind ``Lang.relType || ty.isOfKind ``Lang.seqType
    || ty.isOfKind ``Lang.patType then none
  else some ty[0]

/-- The Lean type of the Fren type `ty`. -/
partial def elabType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name) (ty : Syntax) : m Expr := do
  -- A pattern type's Lean type is its base type's.
  if ty.isOfKind ``Lang.patType then return ← elabType modName ty[0]
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
  match ← resolveWritten modName segs with
  | .item { kind := .enumItem, path, .. } => return Lean.mkConst (← enumDecl path)
  | .item { kind := .recordItem, path, .. } =>
    if let some n := (← getState).newtypes.get? path then return Lean.mkConst n.decl
    let some r := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
    return Lean.mkConst r.decl
  | .item { kind := .typeItem, path, .. } =>
    if let some (t, _) := (← getState).aliases.get? path then return t
    return Lean.mkConst (placeholderName path)
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
  -- Not of a pattern type, whose pattern the annotation holds.
  if ty.isOfKind ``Lang.patType then return
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
  if ty.isOfKind ``Lang.patType then typeElems ty[0] else
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

/-- Lean syntax for the Lean type of a Fren type: a constant. -/
partial def typeSyntax (t : Expr) : Term :=
  if t.isAppOfArity ``Fren.FinSet 1 then Unhygienic.run `(Fren.FinSet $(typeSyntax t.appArg!))
  else if t.isAppOfArity ``Fren.Seq 1 then Unhygienic.run `(Fren.Seq $(typeSyntax t.appArg!))
  else if t.isAppOfArity ``Prod 2 then Unhygienic.run `($(typeSyntax t.appFn!.appArg!) × $(typeSyntax t.appArg!))
  else if t.isConst then mkCIdent t.constName!
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
  /-- For a name, the indexes of its definition, each with the term that it
  is in range, guarded only within the definition: a mention puts them
  under its own guards (`Reqs/Lang/Let#meaning`). -/
  obligations : Array (Syntax × Term) := #[]
  /-- Likewise, the questions about the rows of its definition's tables. -/
  tableObligations : Array (Syntax × Core.TableGoal × Term) := #[]

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
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a clause of a function's contract, the function. -/
  contract? : Option ContractCx := none
  /-- In a global expectation, whose instances are its binders. -/
  inGlobal : Bool := false
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

/-- What the binder `b` is, for a declaration that hides it (`Core.bindingLocals`). -/
def MatchBinder.what (b : MatchBinder) : Name × String :=
  (b.name, if b.scrutinee.isNone then "the bound name" else if b.isDef then "the definition" else "the binder")

def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option MatchBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : MatchBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name)

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
  if let some n := s.newtypeOfDecl? d then return Core.showPath n.path
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
  if let some n := s.newtypeOfDecl? d then return (← coreTy? n.under).map (.newtype n.path)
  if let some a := s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none then
    return some (.abstract a.path)
  return none

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

/-- The Lean type of the Fren expression `t`, elaborated with the comp's
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
    -- A newtype's values are its underlying type's, as the `fren` command
    -- has them.
    else if let some n := s.newtypeOfDecl? d then
      pure #[(n.ctor, #[n.under])]
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

/-- The position of `s`'s variant among the variants of the ordered
enumeration `info`, an `Int`: its constructor's index, as a conditional on
each variant but the last, as the `fren` command writes it
(`FrenCli.DataDecl.ordinal`), so that comparing two values compares their
positions without quantifiers. -/
def ordinalTerm (info : EnumInfo) (s : Term) : TermElabM Term := do
  let last := info.variants.size - 1
  (List.range last).foldrM (init := ← `(($(Syntax.mkNumLit (toString last)) : Int))) fun k acc =>
    `(if $s = $(mkCIdent (info.decl ++ info.variants[k]!)) then ($(Syntax.mkNumLit (toString k)) : Int) else $acc)

/-- `x < y`, or `x ≤ y` if not `strict`, of values compared by `o`, as a
Lean proposition, as the `fren` command's `orderSmt` writes it: a record's
lexicographically, by its fields in the order declared, and a newtype's as
its field's. -/
partial def orderTerm (o : Core.OrderPlan) (strict : Bool) (x y : Term) : TermElabM Term := do
  let st ← getState
  match o with
  | .number => if strict then `($x < $y) else `($x ≤ $y)
  | .string => if strict then `(Fren.Str.lt $x $y) else `(Fren.Str.le $x $y)
  | .enum p =>
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
  | .enum p =>
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
  if let some ct := (← coreTy? ty).filter (fun ct => ct matches .record _ | .newtype .. || (ct == .string && (m == "min" || m == "max"))) then
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
  if let some info := ty.constName?.bind st.enumOfDecl? then
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
  if Core.positionalField f && (ty.constName?.bind (← getState).recordOfDecl?).isNone then
    throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (ty.isConstOf ``Int || ty.isConstOf ``Nat) && f == `abs then
    modifyLocal fun l => { l with absEnds := l.absEnds.push ref.getTailPos? }
  if ty.isConstOf ``String || ty.isConstOf ``Int || ty.isConstOf ``Nat || (relTypes? ty).isSome || ty.isAppOfArity ``Fren.Seq 1 then
    return ← callMethod ref t ty f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if (ty.constName?.bind (← getState).enumOfDecl?).isSome && (f == `min || f == `max) then
    return ← callMethod ref t ty f.toString #[]
  if ty.isAppOfArity ``Fren.FinSet 1 then
    unless f == `card do throwErrorAt ref (Core.unknownSetMethodMsg f.toString (← typeName ty)).text
    return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
  let some r := ty.constName?.bind (← getState).recordOfDecl?
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  let some (_, ft) := r.fields.find? (·.1 == f)
    | throwErrorAt ref (Core.noFieldMsg f (Core.showPath r.path) (r.fields.map (·.1))).text
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
  else if e.isOfKind ``Lang.matchExpr then
    e[3].getSepArgs.foldl (init := pathMentions e[1]) fun acc arm =>
      -- In its arm, a binder's name means the binder, not what it shadows.
      let bound := (topNames arm[0]).map fun b => (declaredIdent b).1.getId
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

/-- A reference to comp variable `n`, if it is one, checking that it may be
mentioned here (`inst::mention`). -/
def varRef? (cx : ExprCtx) (id : Syntax) (n : Name) : TermElabM (Option Term) := do
  let some v := cx.vars.find? (·.name == n) | return none
  -- A defined output mentions what its definition does.
  for u in if cx.unmentioned then #[] else defDeps cx.vars v do
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

/-- For `c(a, b)`, an application of a cardinality operator
(`Reqs/Lang/Expressions#cardinality`), the operator. A variable named like
it shadows it, which applying the variable reports. -/
def cardinalityApp? (e : Syntax) : Option Core.Cardinality := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  Core.builtinFunction? segs[0]!.getId

/-- What the identifier `x`, the only segment of the path `p`, not applied,
is in a pattern (`lang::pattern_name`). -/
def patternName (cx : ExprCtx) (p x : Syntax) : TermElabM Core.PatternName := do
  let (n, bang) := Core.declaredName x.getId
  return Core.patternName (n == `true || n == `false) bang (← isVariant cx p)

/-- The binders of the pattern `top` of `match` or `is`, in preorder. -/
def topBinders (cx : ExprCtx) (top : Syntax) : TermElabM (Array Syntax) :=
  (topNames top).filterM fun x => return (← patternName cx (mkNode ``Lang.fren_path #[mkNullNode #[x]]) x) == .binder

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
    let arms ← e[3].getSepArgs.toList.flatMapM fun arm => do
      let new := (← topBinders cx arm[0]).map fun b => ((declaredIdent b).1.getId, Core.MentionShape.node .binder [s])
      ((if arm[1].isNone then [] else [arm[1][1]]) ++ [arm[3]]).mapM (shapeOf cx · (bs ++ new))
    return .node .compound (s :: arms)
  else if e.isOfKind ``Lang.isExpr then parts .compound #[e[0]]
  else if e.isOfKind ``Lang.letExpr then
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← e[1].getSepArgs.foldlM (init := bs) fun bs d => do
      return bs.push ((declaredIdent d[0]).1.getId, .node .binder [← shapeOf cx d[3] bs])
    return .node .compound [← shapeOf cx e[3] bs]
  else if e.isOfKind ``Lang.quantExpr then
    let new := quantNames e |>.map fun n => (n, Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOf cx e[3] (bs ++ new)]
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size != 1 then return .leaf .constant
    let n := segs[0]!.getId
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf .bound
      return .node .binder [← shapeOf (cx.at b) sc]
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
  if e.isOfKind ``Lang.appExpr && (methodApp? cx e).isNone && (cardinalityApp? e).isNone then
    if !(← isConstruction cx e[0]) && (← definedFn? cx e[0]).isNone then return #[e] ++ inner
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
  -- A newtype has its underlying type's values, as the `fren` command has
  -- it: a newtype of a set of a finite type is finite, though unbounded.
  if let some n := s.newtypeOfDecl? d then return ← infiniteType n.under
  return true

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

/-- Records a `card`, of the receiver `recv` of Lean type `ty`: in a comp
that applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (recv : Syntax) : TermElabM Unit := do
  if cx.unmentioned then return
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
  else if e.isOfKind ``Lang.quantExpr then .mk .quant range e #[go e[3]]
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
  if Core.assertionOnConstant (← mentionsAny cx e) then
    let literal? := match boolNode "" 0 (unparen e) with | .mk (.lit b) .. => some b | _ => none
    recordLint .assertionsOnConstants e (Core.assertionOnConstantMsg kind literal?)

/-- The integer literals in `e`, its patterns' among them. -/
partial def numLits (e : Syntax) : Array Syntax :=
  if e.isOfKind numLitKind then #[e] else e.getArgs.flatMap numLits

/-- The end of the last token in `e`, wherever it is among its parts. -/
partial def lastTailPos (e : Syntax) : String.Pos.Raw :=
  e.getArgs.foldl (fun acc a => max acc (lastTailPos a)) (e.getTailPos?.getD 0)

/-- Records the expressions in `e` that the lints that rewrite them
(`Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated. -/
def lintBools (e : Syntax) : TermElabM Unit := do
  let some sub := e.getSubstring? false false | return
  -- To the end of everything in `e`: the `let` that a `where` clause
  -- becomes ends where its expression does, before its definitions
  -- (`withWhere`).
  let stop := max sub.stopPos (lastTailPos e)
  let src := (String.Pos.Raw.extract sub.str sub.startPos stop).toList.toArray
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let node := boolNode sub.str sub.startPos e
  for (l, ref, msg) in Core.rewriteReports src node fixable do
    recordLint l ref msg
  let (boolEqs, ordereds, variants, absEnds, mentioning, facts) :=
    ((← getLocal).boolEqs, (← getLocal).ordereds, (← getLocal).variants, (← getLocal).absEnds, (← getLocal).mentioning,
      (← getLocal).facts)
  modifyLocal fun l => { l with boolEqs := #[], ordereds := #[], variants := #[], absEnds := #[], mentioning := #[], facts := #[] }
  let variant? (s : Syntax) := (variants.find? (·.1 == (s.getPos?, s.getTailPos?))).map (·.2)
  let fact? (s : Syntax) := (facts.find? (·.1 == (s.getPos?, s.getTailPos?))).map (·.2)
  let ordered? (s : Syntax) := (ordereds.find? (·.1 == (s.getPos?, s.getTailPos?))).map (·.2)
  let help (msg : Core.Msg) := if fixable && !msg.fixes.isEmpty then #[Core.fixHelp] else #[]
  let at_ (rs : Array (Option String.Pos.Raw × Option String.Pos.Raw)) (s : Syntax) := rs.contains (s.getPos?, s.getTailPos?)
  for r in Core.opReports src (at_ boolEqs) ordered? variant? (absEnds.contains ·.getTailPos?) (at_ mentioning) fact? node do
    -- A node's position is its first token's, and its tail its last's.
    let ref := match r.last? with | some l => mkNullNode #[r.ref, l] | none => r.ref
    recordLint r.lint ref { r.msg with notes := r.msg.notes ++ help r.msg }
  for r in Core.arithReports src node do
    recordLint r.lint r.ref { r.msg with notes := r.msg.notes ++ help r.msg }
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

open Lang in
/-- `unnecessary_struct_initialization` on the record literal `e`, of the
record whose structure is `decl`, with the fields `given`, where `go`
translates expressions (`lint::unnecessary_struct_initialization`). -/
def lintStructInit (go : Syntax → TermElabM Term) (decl : Name) (e : Syntax) (given : Array Syntax) :
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
  -- A value has a type; an instance is not one.
  let saved ← saveState
  let ty? ← try some <$> typeOf (← go r) catch _ => pure none
  saved.restore
  if Core.unnecessaryStructInit given.size true same ty?.isSome (ty?.bind (·.constName?) == some decl) then
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
  else if p.isOfKind ``Lang.matchExpr then
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

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Core.Pat.flat`), where no arm overlaps another without containing
it. -/
def lintMatch (cx : ExprCtx) (e : Syntax) (ty : Expr) (pats : Array Core.Pat)
    (slot : Option Core.Slot) : TermElabM Unit := do
  let arms := e[3].getSepArgs
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
    if Core.trivialMatch infos.size i.binds && !anyGuard then recordLint .trivialMatch e (Core.trivialMatchMsg (i.body.inSlot slot (followedStx e)))
  -- `needless_match` (`lint::needless_match`): only a `match` whose arms
  -- are `_` and variants whose payloads' patterns are `_` or binders.
  let scr := exactText (unparen e[1])
  let enum? := ty.constName?.bind (← getState).enumOfDecl?
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
    recordLint .needlessMatch e (help (Core.needlessMatchMsg (scrutinee.inSlot slot (followedStx e))))
  if flat && !anyGuard then
    for g in Core.sameArmGroups infos do
      let (i, msg) := Core.sameArmsMsg infos g slot (followedStx e)
      recordLint .matchSameArms arms[i]! (help msg)
  let scrutinee : Core.BText := { text := exactText e[1], prec := exprPrec e[1] }
  let membership? := if anyGuard then none else Core.membershipParts? infos scrutinee slot
  if let some (pre, post, test) := membership? then
    recordLint .matchLikeMembership e (help (Core.membershipMsg (pre ++ scrutinee.text ++ post) test))
  -- `single_match_else` (`lint::single_match_else`).
  if let some fixed := (if anyGuard then none else
      Core.singleMatchElseFix? infos scrutinee slot (membership?.isSome || needless || trivial) (followedStx e)) then
    let msg := Core.singleMatchElseMsg fixed (Core.hasComment (exactText e))
    recordLint .singleMatchElse e (if msg.fixes.isEmpty then msg else help msg)
  unless flat do return
  let some info := ty.constName?.bind (← getState).enumOfDecl? | return
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
  let msg := Core.wildcardEnumMsg (covered.map (info.path ++ info.variants[·]!)) pattern?
  recordLint .wildcardEnumMatchArm arms[w]![0] (if fixable then help msg else msg)
  unless Core.wildcardSingle covered.size do return
  let msg := Core.wildcardMsg (info.path ++ info.variants[covered[0]!]!) named[0]!
  recordLint .wildcardSingleVariant arms[w]![0] (if named[0]!.isSome then help msg else msg)

/-- A binder of a pattern, with the type of its value, and its value, read
from the scrutinee with selectors. -/
structure PatBinder where
  ident : Syntax
  type : Expr
  term : Term
  deriving Inhabited

/-- The type of a value of the Lean type `t`, as patterns see it. -/
def patTyOf (st : State) (t : Expr) : Core.PatTy :=
  if t.isConstOf ``Bool || t.isProp then .bool
  else if t.isConstOf ``Int then .int
  else if t.isConstOf ``Nat then .nat
  else if t.isConstOf ``String then .string
  else match t.constName?.bind st.enumOfDecl? with
    | some e => .enum e.path
    | none => .other

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

open Lang in
/-- `e`'s shape, for whether it synthesizes a type (`Core.TypeShape`). -/
partial def typeShape (e : Syntax) : Core.TypeShape :=
  if e.isOfKind ``Lang.setExpr || e.isOfKind ``Lang.seqExpr then
    let elems := e[1].getSepArgs
    if elems.isEmpty then .emptyLiteral else .anyPart (elems.toList.map typeShape)
  else if e.isOfKind ``Lang.pairExpr then .pair (typeShape e[1]) (typeShape e[3])
  else if e.isOfKind ``Lang.unionExpr || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr then
    .anyPart [typeShape e[0], typeShape e[2]]
  else if e.isOfKind ``Lang.matchExpr then .anyPart (e[3].getSepArgs.toList.map (typeShape ·[3]))
  else if e.isOfKind ``Lang.letExpr then .anyPart [typeShape e[3]]
  else if e.isOfKind ``Lang.tableExpr then .anyPart (e[2].getSepArgs.toList.map (typeShape ·[3]))
  else match e with
    | `(fren_expr| $a ++ $b) => .anyPart [typeShape a, typeShape b]
    | `(fren_expr| ($a)) => .anyPart [typeShape a]
    | `(fren_expr| if $_ then $a else $b) => .anyPart [typeShape a, typeShape b]
    | _ => .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (e : Syntax) : Bool := (typeShape e).synthesizes

/-- Whether one of `es` synthesizes a type. -/
def anySynthesizes (es : Array Syntax) : Bool := es.any synthesizes


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
    match ← patternName cx p[0] segs[0]! with
    | .boolLiteral =>
      unless pty == .bool do wrong "a pattern of `Bool`"
      let b := (Core.declaredName segs[0]!.getId).1 == `true
      return (.bool b, #[], some (← if b then `(($x : Prop)) else `(¬($x : Prop))))
    | .binder =>
      if inOr && !test then throwErrorAt p (Core.orBinderMsg (declaredIdent segs[0]!).1.getId).text
      return (.wild true, #[{ ident := segs[0]!, type := ty, term := x }], none)
    | .variant => pure ()
  let r ← resolveWritten cx.modName segs cx.shadowing cx.noteIndexes
  let some info := ty.constName?.bind (← getState).enumOfDecl?
    | throwErrorAt p (Core.patternTypeMsg (← patTypeName ty) (match r with
        | .variant en _ => s!"a pattern of `{Core.showPath en.path}`"
        | r => r.describe)).text
  let .variant en idx := r | throwErrorAt p (Core.notAVariantOfMsg info.path r.describe).text
  if en.path != info.path then
    throwErrorAt p (Core.notAVariantOfMsg info.path s!"a variant of `{Core.showPath en.path}`").text
  let v := info.path ++ en.variants[idx]!
  let tys := info.payloads[idx]!
  if let some msg := Core.variantMentionMsg? v tys.size (!p[1].isNone) then throwErrorAt p msg.text
  let args := patternArgs p
  unless args.size == tys.size do throwErrorAt p (Core.arityMsg v tys.size args.size "pattern").text
  let ctor := info.decl ++ info.variants[idx]!
  let sels ← (Array.range tys.size).mapM fun k => `($(mkCIdent (selectorName ctor k)) $x)
  let mut pats := #[]
  let mut bs := #[]
  let mut tests := #[← `($x = $(mkCIdent ctor) $sels*)]
  for a in args, t in tys, sel in sels do
    let (q, qbs, qt) ← resolveOr cx t sel inOr test a[0].getSepArgs false
    pats := pats.push q
    bs := bs ++ qbs
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

/-! ## Pattern types, and the items that declare types -/

/-- Records `undecidable` at `ref`, outside the decidable core, with `msg`. -/
def recordOutsideCore (ref : Syntax) (msg : Core.Msg) : TermElabM Unit := do
  modifyLocal fun l => { l with outsideCore := true }
  recordLint .undecidable ref msg

/-- The declared type `ty`, written in the module `modName`: its Lean type,
and the type with the patterns of the pattern types within it
(`Reqs/Lang/Types#pattern-types`), as the `fren` command's `elabPTy`. -/
partial def elabPType (modName : Name) (ty : Syntax) : TermElabM (Expr × Core.PTy) := do
  -- What Lean recovered from a parse error that it has reported.
  if ty.hasMissing then throwAbortTerm
  let text := Core.typeText (exactText ty)
  if ty.isOfKind ``Lang.patType then
    let (t, base) ← elabPType modName ty[0]
    -- Pattern types are not nested, also through an alias.
    if base.pat?.isSome then throwErrorAt ty[0] (Core.nestedAliasMsg (exactText ty[0])).text
    let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop }
    let (q, bs, _) ← resolveTop cx t (mkIdent `x) true ty[2]
    if let some b := bs[0]? then throwErrorAt b.ident (Core.patternTypeBinderMsg (declaredIdent b.ident).1.getId).text
    return (t, { base with pat? := some q, text })
  -- An element type, which is never a `Nat` (`lang::nat_place`), and whose
  -- constraint, if any, quantifies over the elements, outside the decidable
  -- core (`lang::pattern_place`).
  let elem (e : Syntax) : TermElabM (Expr × Core.PTy) := do
    let (t, pt) ← elabPType modName e
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
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
  -- A path: an alias names a type, as declared.
  let t ← elabType modName ty
  let segs := pathSegs (typePath? ty).get!
  if let .ok (.item { kind := .typeItem, path, .. }) := (← getState).table.resolvePath modName (← segNames segs) #[] then
    if let some (t, pt) := (← getState).aliases.get? path then return (t, { pt with text })
  let some ct ← coreTy? t | throwErrorAt ty s!"internal error: a type without a Fren type"
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
    let .enum ep := ty | `(True)
    let some info := (← getState).enums.get? ep | `(True)
    let ctor := info.decl ++ info.variants[idx]!
    let tys := info.shape.parts[idx]?.getD #[]
    let sels ← (Array.range (info.payloads[idx]!.size)).mapM fun k => `($(mkCIdent (selectorName ctor k)) $x)
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
  | .pat ty p => patTerm ty p x
  | .atLeast0 => `(0 ≤ $x)
  | .fields path cs =>
    let some r := st.records.get? path | `(True)
    let ts ← cs.mapM fun (k, c) => do consTerm c (← `($(mkCIdent (r.decl ++ r.fields[k]!.1)) $x)) depth
    return (← conjTerm ts).getD (← `(True))
  | .newtype path c =>
    let some n := st.newtypes.get? path | `(True)
    consTerm c (← `($(mkCIdent n.field) $x)) depth
  | .payloads path cs =>
    let some info := st.enums.get? path | `(True)
    let ts ← cs.mapM fun (v, k, c) => do
      let ctor := info.decl ++ info.variants[v]!
      let sels ← (Array.range (info.payloads[v]!.size)).mapM fun j => `($(mkCIdent (selectorName ctor j)) $x)
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

/-- The constraint that a value of the declared type `pt`, of the Lean
type `ty`, brings, as a predicate (`Core.PTy.cons`). -/
def factPred? (ty : Expr) (pt : Core.PTy) (nat : Bool := false) : TermElabM (Option Expr) := do
  let some c := pt.cons (← getState).shapeOf nat | return none
  some <$> predOf ty c

/-- The declared type of the variable, parameter or function `name`,
written `ty?`, which is `Bool` if it is not written: its Lean type, and the
type with its patterns, as `varType` checks it. -/
def varPType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM (Expr × Core.PTy) := do
  let n := name.getId
  let t ← ty?.mapM (elabPType modName)
  if let some ty := ty? then lintRelTypes modName ty
  liftMsg name (Core.checkVarName n (t.map (·.1.isConstOf ``Bool)))
  if let (some ty, some (t, _)) := (ty?, t) then lintBoolType n ty t
  return t.getD (Lean.mkConst ``Bool, .plain .bool)

/-- Records the obligation of the value `x`, given at `ref` where the type
`t` is declared, if it has one, for the pattern-type check
(`Reqs/Check#pattern-types`): its guard implies that the value matches,
marked with its type (`Fren.typeObligation`). -/
def noteObligation (cx : ExprCtx) (place : Core.ValuePlace) (ref : Syntax) (t : Core.PTy) (x : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some o := Core.siteObligation place t.obligation | return
  let goal ← `(Fren.typeObligation $(quote t.text) $(← consTerm o x))
  let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) goal
  modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- The Lean type of a field or payload, `ty`, checking that it is accepted
(`lang::field_type`): `own` is the type being declared. -/
def fieldType (modName : Name) (ty : Syntax) (own : Option Name) (payload : Bool) (ownName : Name) :
    CommandElabM (Expr × Core.PTy) := do
  let (cores, inSet) := typeElems ty
  let own1 (core : Syntax) := let segs := pathSegs core; segs.size == 1 && segs[0]!.getId == ownName
  let isOwn := cores.any own1
  if isOwn && inSet then throwErrorAt ty (Core.recursiveSetMsg (modName ++ ownName)).text
  if let some decl := own then
    if isOwn then
      unless Core.fieldTypeAccepted false true false payload do
        throwErrorAt ty (Core.recursiveRecordMsg ownName).text
      return (Lean.mkConst decl, .plain (.enum (modName ++ ownName)))
  let (t, pt) ← liftTermElabM (elabPType modName ty)
  lintRelTypes modName ty
  let st ← getState
  let e := ((elemTypes t).find? fun e => e.isConst && st.placeholders.contains e.constName).getD t
  let abstract := e.isConst && st.placeholders.contains e.constName
  unless Core.fieldTypeAccepted abstract false false payload do
    let p := ((← getState).abstracts.foldl (init := none) fun acc _ a =>
      acc <|> if a.placeholder == e.constName then some a.path else none).getD .anonymous
    throwErrorAt ty (Core.abstractFieldMsg p payload inSet).text
  return (t, pt)

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
  let decl := (← getCurrNamespace) ++ path
  let variantStxs := stx[5].getSepArgs
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
    let tps ← tys.mapM fun t => fieldType modName t (some decl) true n
    let ts := tps.map (·.1)
    if ts.any (·.isConstOf decl) then nRecursive := nRecursive + 1
    let st ← getState
    unbounded := unbounded || ts.any fun t => t.isConstOf decl || st.unbounded t
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
  -- Each read of a recursive enumeration's payload brings the payload's
  -- constraint (`Core.readCons`), as an application does.
  let readFacts ← if !isRecursive then pure #[] else liftTermElabM do
    let st ← getState
    let shapes (q : Name) := if q == path then some shape else st.shapeOf q
    let mut out := #[]
    for v in variants, ts in payloads, vi in [0:variants.size] do
      for t in ts, k in [0:ts.size] do
        if let some c := Core.readCons shapes path vi k then
          out := out.push (selectorName (decl ++ v) k, ← predOf t c)
    return out
  record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
  record (.enumInfo { path, decl, variants, payloads, unbounded, ordered := isOrdered, shape, readFacts })
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
  let decl := (← getCurrNamespace) ++ path
  let mut fields : Array (Name × Expr) := #[]
  let mut ptys : Array Core.PTy := #[]
  let fieldStxs := stx[5].getSepArgs
  for f in fieldStxs do discard (segName f[0])
  if let some k := (Core.repeatsAt (fieldStxs.map (·[0].getId)))[0]? then
    throwErrorAt fieldStxs[k]![0] (Core.dupFieldMsg fieldStxs[k]![0].getId).text
  for f in fieldStxs do
    let fn := f[0].getId
    liftMsg f[0] (Core.checkNoBang fn)
    lintName .field fn f[0]
    let (t, pt) ← if f[1].isNone then pure (Lean.mkConst ``Bool, .plain .bool) else fieldType modName f[1][1] (some decl) false n
    ptys := ptys.push pt
    -- As for a variable (`lang::bool_naming`).
    liftMsg f[0] (Core.checkVarName fn (if f[1].isNone then none else some (t.isConstOf ``Bool)))
    unless f[1].isNone do liftTermElabM (lintBoolType fn f[1][1] t)
    fields := fields.push (fn, t)
  -- `struct_field_names` (`lint::struct_field_names`, `lint::field_has_record_name`).
  if let some msg := Core.structFieldNamesMsg? n (fields.map (·.1)) then recordLint .structFieldNames nameStx msg
  for f in stx[5].getSepArgs, (fn, _) in fields do
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
  let unbounded := fields.any fun (_, t) => st.unbounded t
  let bs ← fields.mapM fun (f, t) => `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent f):ident : $(typeSyntax t)))
  elabCommand (← `(structure $(mkIdentFrom nameStx path):ident where
    $(mkIdent `«{}»):ident :: $bs:structExplicitBinder*
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.recordInfo { path, decl, fields, unbounded, shape := { isRecord := true, parts := #[ptys] }, ordered := isOrdered })
  unless isPub do recordItem .record path nameStx

@[command_elab Lang.newtypeCmd] def elabNewtype : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
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
  let decl := (← getCurrNamespace) ++ path
  -- Exactly one field, whose type is accepted as a record's field's
  -- (`lang::newtype`).
  let tys := stx[5].getSepArgs
  let some ty := tys[0]? | throwErrorAt nameStx (Core.newtypeFieldsMsg path 0).text
  unless Core.newtypeAccepted tys.size true do throwErrorAt nameStx (Core.newtypeFieldsMsg path tys.size).text
  let (under, pt) ← fieldType modName ty (some decl) false n
  -- An ordered newtype's underlying type is ordered
  -- (`lang::ordered_declaration`).
  unless Core.orderedDeclAccepted isOrdered 0 (Core.PTy.firstUnordered? (← getState).orderedDecl [pt]) do
    throwErrorAt ty (Core.unorderedFieldMsg .newtype n (Name.mkSimple "0") pt.ty).text
  let unbounded := Core.newtypeUnbounded ((← getState).unbounded under)
  -- One field, `«0»`, so that `x.0` in Fren is `x.«0»` in Lean.
  elabCommand (← `(structure $(mkIdentFrom nameStx path):ident where
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
  else if e.isOfKind ``Lang.matchExpr then e[3].getSepArgs.any (seqShaped ·[3])
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
  if !synthesizes a && synthesizes b then
    let y ← toTerm cxb b
    return (← toTerm { cxa with expected? := ← sibling cxa y } a, y)
  let x ← toTerm cxa a
  return (x, ← toTerm { cxb with expected? := ← sibling cxb x } b)

open Lang in
/-- Translates a record literal, where `go` translates its values, given
the type each is expected to have. -/
def recordTerm (go : Option Core.Ty → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
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
  let args ← info.fields.zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
    if cx.noteIndexes then lintRedundant b true
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath path}` has type `{tn}`"
    noteObligation cx .field v ((info.shape.parts[0]?.bind (·[k]?)).getD default) t
    return t
  if cx.noteIndexes then lintStructInit (go none) info.decl e given
  `($(mkCIdentFrom e[0] (recordCtor info.decl)) $args*)

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
  -- A `Nat` is expected of a `Nat` field (`lang::literal_type`).
  let go (x? : Option Core.Ty) := toTerm { cx with emptyOk := Core.Position.declared.checked false false, expected? := x?,
                                                   natOk := x? == some .nat }
  -- `r` bound once, so that nested updates grow linearly.
  let bind := info.fields.size > given.size && !rv.raw.isIdent
  let r ← if bind then `(r) else pure rv
  let args ← info.fields.zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | `($(mkCIdentFrom e[1] (info.decl ++ f)) $r)
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath info.path}` has type `{tn}`"
    noteObligation cx .field v ((info.shape.parts[0]?.bind (·[k]?)).getD default) t
    return t
  let lit ← `($(mkCIdentFrom e (recordCtor info.decl)) $args*)
  if bind then `(let r := $rv; $lit) else pure lit

/-- The type of a `match`'s arms so far, `armsTy?`, after the arm whose body
`ref` is translated to `body` and checked against `shared?`
(`lang::arm_type`). A body that does not synthesize its type has the one
it is checked against, as in the `fren` command. -/
def armType (armsTy? : Option Core.Ty) (ref : Syntax) (body : Term) (shared? : Option Core.Ty) :
    TermElabM (Option Core.Ty) := do
  let t? := (← frenTypeOf? body).orElse fun _ => if synthesizes ref then none else shared?
  let some t := t? | return armsTy?
  return some (← liftMsg ref (Core.checkArm armsTy? t))

/-- Records the questions about the arms of the `match` `e`, whose patterns
are `pats`, each taken where `taken` says, of which those with a guard
are `guarded`, for its completeness and reachability checks
(`check::completeness`, `check::reachability`): completeness, unless its
arms without guards are exhaustive, is reported at `match`, and the
reachability of an arm at its pattern. -/
def noteMatch (cx : ExprCtx) (e : Syntax) (pats : Array Syntax) (taken : Array (Option Term)) (guarded : Array Bool)
    (unguardedExhaustive : Bool) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let orF (cs : Array Term) : Term := cs.pop.foldr (fun c acc => Unhygienic.run `($c ∨ $acc)) cs.back!
  let andF (a b : Term) : Term := Unhygienic.run `($a ∧ $b)
  let notF (c : Term) : Term := Unhygienic.run `(¬$c)
  let trueF : Term := Unhygienic.run `(True)
  for (g, f) in Core.splitGoals .match orF andF notF trueF taken guarded (Core.completenessAsked unguardedExhaustive) do
    let ref := match g with
      | .reachability _ j => pats[j]!
      | _ => e[0]
    let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

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
  let scrutinee := e[1]
  let s ← toTerm { cx with emptyOk := Core.Position.synthesized.checked false false, natOk := false } scrutinee
  let ty ← typeOf s
  let pty := patTyOf (← getState) ty
  if pty == .other then throwErrorAt scrutinee (Core.scrutineeMsg (← typeName ty)).text
  let arms := e[3].getSepArgs
  -- Each arm's pattern, its binders and its test.
  let mut resolved := #[]
  for arm in arms do resolved := resolved.push (← resolveTop cx ty s false arm[0])
  let pats := resolved.map (·.1)
  let guarded := arms.map (!·[1].isNone)
  let unguardedExhaustive ← match Core.checkMatch (← patSigs) pty pats guarded with
    | .ok u => pure u
    | .error (some (i, some j), msg) => throwErrorAt (topAlternatives arms[i]![0])[j]! msg.text
    | .error (some (i, none), msg) => throwErrorAt arms[i]![0] msg.text
    | .error (none, msg) => throwError msg.text
  if cx.noteIndexes then lintMatch cx e ty pats slot
  let mut bodies : Array Term := #[]
  -- Where each arm is taken, if no earlier one is: its test and its guard;
  -- `none` for an arm taken wherever it is tried.
  let mut taken : Array (Option Term) := #[]
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
    let armGuards := cx.guards ++ (← taken.filterMapM fun t? => t?.mapM fun t => `(¬$t)) ++ t?.toArray
    -- Distinct names (`lang::distinct_names`), by the names they declare,
    -- without the `!` of shadowing.
    let declared := bs.map fun b => (declaredIdent b.ident).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt bs[k]!.ident (Core.dupPatternBinderMsg declared[k]!).text
    let mut new : Array MatchBinder := #[]
    for b in bs do
      let locals := Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome cx.inGlobal
      let y ← declare b.ident cx.modName locals
      let bn := y.getId
      liftMsg y (Core.checkVarName bn (some (b.type.isConstOf ``Bool || b.type.isProp)))
      lintName .binder bn y
      new := new.push { name := bn, term := b.term, «type» := b.type, scrutinee := some scrutinee, outer := cx.binders.size }
    let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
    -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
    let g? ← if arm[1].isNone then pure none else do
      let g := arm[1][1]
      let c ← toTerm { gcx with natOk := false, emptyOk := false, expected? := none } g
      checkTermType g c .bool (some Core.armGuardNote)
      pure (some c)
    let own := t?.toArray ++ g?.toArray
    taken := taken.push (Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) own)
    let others := (arms.eraseIdx! bodies.size).map (·[3])
    let emptyOk := Core.Position.shared.checked cx.emptyOk (anySynthesizes others)
    let acx := { gcx with guards := armGuards ++ g?.toArray, emptyOk }
    -- Each body is checked against the whole's type, or the arms' so far,
    -- as the `fren` command does: one that does not synthesize its own,
    -- before any has given one, waits for a later arm that does.
    let shared? := expected?.orElse fun _ => armsTy?.map (·.widen)
    if shared?.isNone && !synthesizes arm[3] && arms.any (synthesizes ·[3]) then
      waiting := waiting.push (bodies.size, acx, arm[3])
      bodies := bodies.push (← `(sorry))
      continue
    let body ← toTerm { acx with expected? := shared? } arm[3]
    armsTy? ← armType armsTy? arm[3] body shared?
    bodies := bodies.push body
  for (k, acx, b) in waiting do
    let body ← toTerm { acx with expected? := armsTy?.map (·.widen) } b
    if armsTy?.isSome then armsTy? ← armType armsTy? b body (armsTy?.map (·.widen))
    bodies := bodies.set! k body
  noteMatch cx e (arms.map (·[0])) taken guarded unguardedExhaustive
  let widened ← widenMixed bodies
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
  let (q, bs, test) ← resolveTop cx ty s true e[2]
  match Core.checkPatternTest (← patSigs) pty q (bs.map (·.ident.getId)) with
  | .ok () => pure ()
  | .error (.binder k, msg) => throwErrorAt bs[k]!.ident msg.text
  | .error (.alternative j, msg) => throwErrorAt (topAlternatives e[2])[j]! msg.text
  | .error (.whole, msg) => throwErrorAt e[2] msg.text
  if cx.noteIndexes then
    -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`).
    let irrefutable := Core.irrefutableIs (Core.matchesEvery (← patSigs) pty q)
    if irrefutable then recordLint .irrefutableIs e (Core.irrefutableIsMsg (← patTypeName ty) (q matches .wild _))
    let texts := (topAlts e[2]).1.map exactText
    if Core.isEquality (Core.equatable q texts) irrefutable then
      let msg := Core.isEqualityMsg { text := exactText scrutinee, prec := exprPrec scrutinee } texts
      recordLint .isEquality e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  match test with
  | some t => return t
  | none => `(true)

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
    -- `++` is in the core against a constant.
    let (x, y) ← pairTerms toTerm { cx with concatOk := cb, emptyOk := Core.Position.compared.checked false (synthesizes b) }
      { cx with concatOk := ca, emptyOk := Core.Position.compared.checked false (synthesizes a) } a b
    -- Both sides have one type, after widening, as the `fren` command checks
    -- (`lang::operator_type`).
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then liftMsg e (Core.checkComparable op tx ty)
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
  let x ← toTerm cx a
  let tx? ← frenTypeOf? x
  let st ← getState
  let info? := (← typeOf x).constName?.bind st.enumOfDecl?
  let operandTy : Core.Ty ← match tx? with
    | some tx => liftMsg a (Core.orderingType op tx st.orderedDecl)
    | none => pure .int
  let y ← toTerm cx b
  checkNewtypeOp op tx? (← frenTypeOf? y)
  checkTermType b y operandTy (Core.opNote op operandTy)
  -- For the lints of integers, at the end of the expression: what it compares.
  if cx.noteIndexes && !(tx? matches some (.newtype ..)) then
    let compared : Core.Ordered := if operandTy matches .enum _ && info?.any (·.ordered) then .enumeration
      else if operandTy == .int || operandTy == .nat then .number else .other
    modifyLocal fun l => { l with ordereds := l.ordereds.push ((e.getPos?, e.getTailPos?), compared) }
  -- An ordered record's values compare by their fields, and a newtype's as
  -- their fields do (`Reqs/Lang/Items#ordered-declarations`).
  if operandTy matches .record _ | .newtype .. then
    let some plan := st.orderPlan? operandTy | throwError "internal error: `{operandTy.show}` is not ordered"
    if plan.strings then checkCore cx e .stringCompare true (ca || cb) #[a, b] (ca && cb)
    return ← orderingTerm plan op x y
  -- An ordered enumeration's values compare by their positions.
  if let (.enum _, some info) := (operandTy, info?) then
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
  let mut x ← toTerm cx xs[0]!
  -- A value of an ordered type, a `Nat` widened, and every operand the
  -- first's type, as the `fren` command checks (`lang::operator_type`,
  -- `lang::ordered_type`, `lang::newtype_operator`).
  let tx0? ← frenTypeOf? x
  let st ← getState
  let info? := (← typeOf x).constName?.bind st.enumOfDecl?
  let t0? ← match tx0? with
    | some t => some <$> liftMsg xs[0]! (Core.orderingType names[0]! t st.orderedDecl)
    | none => pure none
  let string := t0? == some .string
  -- An ordered enumeration's values compare by their positions, and an
  -- ordered record's or newtype's by their fields.
  let plan? := match t0? with
    | some t@(.record _) | some t@(.newtype ..) => st.orderPlan? t
    | _ => none
  let ordinal := if t0? matches some (.enum _) then info? else none
  let pos (t : Term) : TermElabM Term := match ordinal with | some info => ordinalTerm info t | none => pure t
  let mut links := #[]
  for op in names, a in xs, b in xs.extract 1, opStx in ops do
    let y ← toTerm { cx with guards := cx.guards ++ links } b
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
  let expected? ← if expected?.isNone && !synthesizes a && synthesizes b then
      let s ← saveState
      let t? ← frenTypeOf? (← toTerm { cx with noteIndexes := false } b)
      s.restore
      pure t?
    else pure expected?
  let x ← toTerm { cx with concatOk := true, emptyOk := Core.Position.shared.checked cx.emptyOk (synthesizes b), expected? } a
  unless (← getState).newtypes.isEmpty || !synthesizes a do
    let tx? ← frenTypeOf? x
    checkNewtypeOp "++" tx? tx?
  -- Sequences: outside the core, unless constant.
  if (← typeOf x).isAppOfArity ``Fren.Seq 1 then
    let y ← toTerm { cx with emptyOk := Core.Position.shared.checked cx.emptyOk (synthesizes a), expected? := ← frenTypeOf? x } b
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
    let recvConstant ← isConstant cx recvStx
    let c := (Core.Method.ofName? m).map (·.construct) |>.getD .stringAtom
    -- `min` and `max` compare their strings, as `<=` does.
    let comparable := !(m == "min" || m == "max") || constantArgs || recvConstant
    checkCore cx e c constantArgs comparable (#[recvStx] ++ args) (constantArgs && recvConstant)
  let t := (← callMethod ref r rty m as).1
  -- `min` and `max` of an ordered record or newtype with a `String` within
  -- compare strings (`Reqs/Lang/Decidability#orderings`).
  if m == "min" || m == "max" then
    let ct? := (← frenTypeOf? r).filter (· matches .record _ | .newtype ..)
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
def checkNewtypeMembers (seq : Bool) (elems : Array Syntax) (xs : Array Term) : TermElabM Unit := do
  let s ← getState
  if s.newtypes.isEmpty then return
  let typed ← (elems.zip xs).filterMapM fun (e, x) => do
    if !synthesizes e || e.isOfKind ``Lang.pairExpr then return none
    return some (e, ← typeOf x)
  let some (_, t0) := typed[0]? | return
  unless typed.any fun (_, t) => (s.newtypeOf? t).isSome do return
  for (e, t) in typed do
    unless ← isDefEq t t0 do
      let name ← typeName t0
      let lit := if seq then s!"Seq({name})" else s!"Set({name})"
      throwErrorAt e (Core.membersMsg seq (← typeName t0) (← typeName t) lit).text

/-- `t`, a `Bool` if it is a condition, a `Prop`: a member of a set is a
value, and a `Bool` in Fren, as `true` is. -/
def boolTerm (t : Term) : TermElabM Term := do
  if (← typeOf t).isProp then `(if $t then true else false) else pure t

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
  -- A member, given the type of the literal expected of it, as the `fren`
  -- command's `member`: a pair's members expect a relation's types. A member
  -- is never a `Nat` (`lang::nat_place`).
  let member (k : Nat) (lit? : Option Core.Ty) (noteIndexes := cx.noteIndexes) : TermElabM Term := do
    let x := elems[k]!
    let mcx := { cx with noteIndexes, emptyOk := Core.Position.shared.checked emptyOk (anySynthesizes (elems.eraseIdx! k)) }
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
  let lit? ← if expected?.isNone && !synthesizes elems[0]! then
      match elems.findIdx? synthesizes with
      | some k => do
        let s ← saveState
        let t? ← litTy k (← member k none (noteIndexes := false))
        s.restore
        pure t?
      | none => pure none
    else pure expected?
  let x0 ← member 0 lit?
  let t0? := (← litTy 0 x0).orElse fun _ => if synthesizes elems[0]! then none else lit?
  let mut xs := #[x0]
  for k in [1:elems.size] do
    let x ← member k t0?
    if let (some t, some t0) := (← litTy k x, t0?) then
      unless t == t0 do
        let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
        throwErrorAt elems[k]! (Core.membersMsg false mt0 mt t0.show).text
    xs := xs.push x
  checkNewtypeMembers false elems xs
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
    let s ← toTerm { cx with emptyOk := Core.Position.compared.checked false (synthesizes a), expected? := elem? } b
    let (tx, ts) := (← typeOf x, ← typeOf s)
    -- `ts` is taken apart only once it is known to be a `Seq`: a `(← ...)`
    -- after `&&` would run, and panic, for any other type.
    let isSeq ← if ts.isAppOfArity ``Fren.Seq 1 then isDefEq ts.appArg! tx else pure false
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
  let cxa := { cx with emptyOk := position.checked cx.emptyOk (synthesizes b) }
  let cxb := { cx with emptyOk := position.checked cx.emptyOk (synthesizes a) }
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
  -- For `manual_at_most_one`: whether the operands give a definedness
  -- obligation.
  let mark := (← getLocal).indexes.size + (← getLocal).tables.size
  let x ← toTerm cx c
  checkTermType c x .bool (if j.isEmpty then some s!"note: the condition of `{kw}` is a `Bool`" else Core.opNote j .bool)
  let g ← operand.guard (pure x) `(¬$x)
  let y ← toTerm { cx with guards := cx.guards.push g } d
  if op matches .and && cx.noteIndexes && (← getLocal).indexes.size + (← getLocal).tables.size > mark then
    modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .obligations) }
  if j.isEmpty then checkTermType e y .bool (some s!"note: the body of `{kw}` is a `Bool`")
  else checkTermType d y .bool (Core.opNote j .bool)
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
      | .disjointness _ j | .reachability _ j => refs[j]!
      | _ => e[0]
    let goal ← guardedGoal cx.guards f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

/-- Records the questions about the application at `ref` of the function at
`path` to the arguments `args`, if the function has preconditions, for
the precondition check (`check::precondition`): its guard implies each
precondition at the arguments, in order. -/
def notePreconditions (cx : ExprCtx) (ref : Syntax) (path : Name) (args : Array Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some k := (← getState).contracts.get? path | return
  let pres ← k.pres.mapM fun pre => return (pre.name, ← `($(mkCIdent pre.decl) $(pre.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*))
  let guarded (g : Term) : Term := cx.guards.foldr (fun c acc => Unhygienic.run `($c → $acc)) g
  for (q, goal) in Core.preconditionQuestions guarded path pres do
    modifyLocal fun l => { l with tables := l.tables.push (ref, q, goal) }

open Lang in
/-- Translates a table into a chain of `if`s over its rows' conditions,
where `toTerm` translates its parts. Where no row holds, a table without a
`_` row is an index out of range of the empty sequence, `Fren.Seq.nth ∅
0`, as the solver sees it: one unspecified value of each type
(`Reqs/Lang/Expressions#tables`). -/
def tableTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
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
    let emptyOk := Core.Position.shared.checked cx.emptyOk (anySynthesizes others)
    values := values.push (← toTerm { cx with guards := before ++ own, emptyOk } r[3])
  -- Each value has the type of those before it (`Core.checkRowType`).
  let mut t0? : Option Core.Ty := none
  for r in rows, v in values do
    let some t ← frenTypeOf? v | continue
    if let some t0 := t0? then liftMsg r[3] (Core.checkRowType t0 t)
    t0? := some ((t0?.map (·.join t)).getD t)
  noteTable cx e refs conds defined wild
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
  let locals := Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome cx.inGlobal
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
  let dcx := { cx with guards := #[], pending := pending.toArray, emptyOk := position.checked false false
                       natOk := annot?.any (·.isConstOf ``Nat), unmentioned := cx.unmentioned || !used[k]! }
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
  -- Named apart from every local around it, so that putting a definition's
  -- indexes under the `have`s of its uses captures nothing.
  let lname := Name.mkSimple s!"{Core.nameText n}@{cx.binders.size}"
  let tyStx := typeSyntax (← instantiateMVars ty)
  let b : MatchBinder := { name := n, term := mkIdent lname, «type» := ty, scrutinee := d[3], outer := cx.binders.size,
                           isDef := true, obligations, tableObligations }
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
  let ecx (k : Nat) := { cx with emptyOk := Core.Position.shared.checked emptyOk (anySynthesizes (elems.eraseIdx! k)) }
  -- Each element is checked against the literal's element type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  -- An element is never a `Nat` (`lang::nat_place`).
  let elem? ← match expected?.bind fun | .seq t => some t | _ => none with
    | some t => pure (some t)
    | none => if synthesizes elems[0]! then pure none else
        match elems.findIdx? synthesizes with
        | some k => do
          let s ← saveState
          let t? ← frenTypeOf? (← toTerm { ecx k with noteIndexes := false } elems[k]!)
          s.restore
          pure t?
        | none => pure none
  let x0 ← toTerm { ecx 0 with expected? := elem? } elems[0]!
  let t0? := ((← frenTypeOf? x0).orElse fun _ => if synthesizes elems[0]! then none else elem?).map (·.widen)
  let mut xs := #[← boolTerm (← widenTerm x0)]
  for k in [1:elems.size] do
    let x ← toTerm { ecx k with expected? := t0? } elems[k]!
    if let (some t, some t0) := ((← frenTypeOf? x).map (·.widen), t0?) then
      unless t == t0 do throwErrorAt elems[k]! (Core.membersMsg true t0.show t.show (Core.Ty.seq t0).show).text
    xs := xs.push (← boolTerm (← widenTerm x))
  -- After its elements, as in the `fren` command.
  checkCore cx e .seqArray true true elems
  checkNewtypeMembers true elems xs
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
    (p : TSyntax ``fren_path) : TermElabM Term := do
  let segs := pathSegs p
  if h : segs.size = 1 then
    lintChain toTerm cx parent? e
    let id := segs[0]
    let n := id.getId
    -- A binder or variable, then any fields read from it.
    let base? ← if let some b := cx.binder? n.getRoot then do
        -- A bound name has no scrutinee: it mentions nothing.
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
            discard (toTerm { cx.at b with noteIndexes := false, pending := #[], emptyOk := true } sc)
            saved.restore
          else discard (toTerm (cx.at b) sc)
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
    return mkCIdentFrom e (info.decl ++ en.variants[idx]!)
  | .item { kind := .constItem, path, .. } =>
    let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
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
    if let (true, some u) := (synthesizes a, ← coreTy? n.under) then
      if let some found ← frenTypeOf? t then
        liftMsg a (Core.checkType u found (some s!"note: the value of `{Core.showPath path}` has type `{u.show}`"))
    if cx.noteIndexes then
      modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .wraps path.toString (synthesizes a)) }
    noteObligation cx .construction a ((n.shape.parts[0]?.bind (·[0]?)).getD default) t
    return ← `($(mkCIdentFrom p n.ctor) $t)
  if let .variant en idx := r then
    -- A variant with a payload, built from its values.
    let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
    let v := en.path ++ en.variants[idx]!
    let n := (info.payloads[idx]?.map (·.size)).getD 0
    if let some msg := Core.variantMentionMsg? v n true then throwError msg.text
    unless args.getElems.size == n do throwError (Core.arityMsg v n args.getElems.size "value").text
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := info.payloads[idx]![k]!.isConstOf ``Nat,
                                expected? := ← coreTy? info.payloads[idx]![k]! } a
      checkDeclared a t info.payloads[idx]![k]! fun ty => s!"note: value {k + 1} of the payload of `{Core.showPath v}` has type `{ty}`"
      noteObligation cx .payload a ((info.shape.parts[idx]?.bind (·[k]?)).getD default) t
      return t
    return ← `($(mkCIdentFrom p (info.decl ++ en.variants[idx]!)) $args*)
  let .item { kind := .fnItem, path, .. } := r | throwErrorAt p (Core.notAFunctionMsg r).text
  if let some d := (← getState).defined.get? path then
    -- Its definition, applied to the placeholders it uses; its arguments
    -- may mention anything (`lang::argument`).
    unless args.getElems.size == d.nParams do throwError (Core.arityMsg path d.nParams args.getElems.size).text
    let tys := paramTypes (← instantiateForall (← getConstInfo d.decl).type (d.uses.map mkConst))
    let args ← args.getElems.zipIdx.mapM fun (a, k) => do
      let t ← toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := tys[k]!.isConstOf ``Nat, expected? := ← coreTy? tys[k]! } a
      checkDeclared a t tys[k]! fun ty => s!"note: argument {k + 1} of `{Core.showPath path}` has type `{ty}`"
      noteObligation cx .argument a (d.ptys.1[k]?.getD default) t
      return t
    notePreconditions cx p path args
    return ← `($(mkCIdentFrom p d.decl) $(d.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*)
  if cx.selfFn.isSome then throwErrorAt p (Core.appliesUninterpretedMsg path).text
  let a ← placeholderOf path
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
  return x

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
partial def valueCount? (ty : Expr) : TermElabM (Option Nat) := do
  if ty.isConstOf ``Bool then return some 2
  let s ← getState
  let some d := ty.constName? | return none
  let (kind, unbounded, ctors) : Core.QuantifiedKind × Bool × Array (Array Expr) :=
    if let some e := s.enumOfDecl? d then (.enum, e.unbounded, e.variants.mapIdx fun i _ => e.payloads[i]?.getD #[])
    else if let some r := s.recordOfDecl? d then (.record, r.unbounded, #[r.fields.map (·.2)])
    else (.other, false, #[])
  if unbounded then return none
  let counts ← ctors.mapM (·.mapM valueCount?)
  unless Core.quantifiedTypeAccepted kind false (counts.all (·.all Option.isSome)) do return none
  return some (counts.foldl (fun n cs => n + cs.foldl (fun m c => m * c.getD 0) 1) 0)

/-- The Lean type of a quantifier's binder's type `ty`, which must not be a
component. -/
def binderType (modName : Name) (ty : Syntax) : TermElabM (Expr × Core.PTy) := do
  if let some p := typePath? ty then
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
    let some d := ty.constName? | `(sorry)
    let (c, ts) :=
      if let some e := s.enumOfDecl? d then (e.decl ++ e.variants[idx]!, e.payloads[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then (recordCtor r.decl, r.fields.map (·.2))
      else if let some n := s.newtypeOfDecl? d then (n.ctor, #[n.under])
      else (.anonymous, #[])
    let as ← (args.zip ts).mapM fun (w, t) => valueTerm t w
    `($(mkCIdent c) $as*)

/-- The values of the declared type `pt`, of the Lean type `ty`, as terms,
and how many there are, if a quantifier ranges over it, as the `fren`
command's `binderValues`. -/
def binderValues (ty : Expr) (pt : Core.PTy) : TermElabM (Option (Nat × Array Term)) := do
  let st ← getState
  if (pt.cons st.shapeOf).isNone then
    let some n ← valueCount? ty | return none
    return some (n, (← valuesOf? ty Core.maxInstances).getD #[])
  let some n := pt.count? st.shapeOf | return none
  if n > Core.maxInstances then return some (n, #[])
  let vs := (pt.values st.shapeOf Core.maxInstances).getD #[]
  return some (n, ← vs.mapM (valueTerm ty))

open Lang in
/-- `forall (x: T), e`, or `exists` unless `all`, with the binders
`binders` and the body `body`, expanded (`Reqs/Lang/Quantifiers#meaning`):
the body is elaborated once, over a local for each bound name, and
instantiated at every combination of their values, the last name varying
fastest, and the instances conjoined or disjoined; so are the definedness
goals of its indexes, which hold in every instance. Each type must be one
that a quantifier ranges over (`lang::quantified_type`), the names
distinct, following the Boolean names rule and written with `!` exactly
when they shadow (`lang::shadowing`), and the combinations at most
`Core.maxInstances` (`lang::quantifier_size`), as the `fren` command checks
them. -/
def quantTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (all : Bool)
    (binders : Array Syntax) (body : Syntax) : TermElabM Term := withRef e do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := binders.flatMap (·[1].getArgs)
  for x in ids do discard (segName x)
  let declared := ids.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt ids[k]! (Core.dupBoundMsg declared[k]!).text
  let mut bound : Array (Name × Expr) := #[]
  let mut sizes := #[]
  let mut listed := #[]
  for b in binders do
    let (ty, pt) ← binderType cx.modName b[3]
    let some (n, vs) ← binderValues ty pt
      | let collection := ty.isAppOfArity ``Fren.FinSet 1 || ty.isAppOfArity ``Fren.Seq 1
        let shown ← if pt.pat?.isSome then pure pt.text else typeName ty
        throwErrorAt b[3] (Core.quantifiedTypeMsg shown collection).text
    for x in b[1].getArgs do
      let locals := Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
        (cx.binders.map (·.what) ++ bound.map (·.1, "the bound name")) cx.selfFn.isSome cx.inGlobal
      let x ← declare x cx.modName locals
      let bn := x.getId
      liftMsg x (Core.checkVarName bn (some (ty.isConstOf ``Bool)))
      lintName .binder bn x
      bound := bound.push (bn, ty)
      sizes := sizes.push n
      listed := listed.push vs
  let n := cx.instances * Core.instanceCount sizes
  unless Core.quantifierSizeAccepted n do
    throwErrorAt (mkNullNode binders) (Core.quantifierSizeMsg n (cx.instances > 1)).text
  let values ← (bound.zip listed).mapM fun ((_, ty), vs) => vs.mapM (elabProp · ty)
  let combos := values.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]]
  withLocalDeclsD (bound.map fun (bn, ty) => (bn, fun _ => pure ty)) fun fvs => do
    let new ← (bound.zip fvs).mapIdxM fun i ((bn, ty), fv) => do
      return { name := bn, term := ← exprToSyntax fv, «type» := ty, scrutinee := none, outer := cx.binders.size + i : MatchBinder }
    let outer := (← getLocal).indexes
    let outerTables := (← getLocal).tables
    modifyLocal fun l => { l with indexes := #[], tables := #[] }
    let t ← toTerm { cx with binders := cx.binders ++ new, natOk := false, instances := cx.instances * combos.size } body
    checkTermType body t .bool (some s!"note: the body of `{if all then "forall" else "exists"}` is a `Bool`")
    let b ← elabProp t
    let inner ← (← getLocal).indexes.mapM fun (ref, g) => return (ref, ← elabProp g)
    let innerTables ← (← getLocal).tables.mapM fun (ref, q, g) => return (ref, q, ← elabProp g)
    let inst (x : Expr) (vals : Array Expr) : Expr := x.replaceFVars fvs vals
    -- The names of enclosing `let`s and `where`s are locals here, which the
    -- `have`s that define them bind again: what mentions them is closed
    -- over them, and applied to their names.
    let lctx ← getLCtx
    let defs := cx.binders.filterMap fun d =>
      if d.isDef then (lctx.findFromUserName? d.term.raw.getId).map (d.term, ·.toExpr) else none
    let close (x : Expr) : TermElabM Term := do
      let used := defs.filter fun (_, fv) => x.containsFVar fv.fvarId!
      if used.isEmpty then return ← exprToSyntax x
      let f ← exprToSyntax (← mkLambdaFVars (used.map (·.2)) x)
      `($f $(used.map (·.1))*)
    let goals ← inner.mapM fun (ref, g) => return (ref, ← close (balanced mkAnd (combos.map (inst g))))
    let tableGoals ← innerTables.mapM fun (ref, q, g) => return (ref, q, ← close (balanced mkAnd (combos.map (inst g))))
    modifyLocal fun l => { l with indexes := outer ++ goals, tables := outerTables ++ tableGoals }
    close (balanced (if all then mkAnd else mkOr) (combos.map (inst b)))

/-- `if c then a else b`, where `toTerm` translates its parts, which are
checked against a type if `emptyOk`, and are `Nat`s if `natOk` is. -/
def iteTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk natOk : Bool) (e c' a b : Syntax) :
    TermElabM Term := do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  if cx.noteIndexes && !cx.inElse then lintIfChain cx e
  if cx.noteIndexes then lintSameBranches e a b
  if cx.noteIndexes && (← mentionsAny cx c') then
    modifyLocal fun l => { l with mentioning := l.mentioning.push ((unparen c').getPos?, (unparen c').getTailPos?) }
  let c ← toTerm { cx with inElse := false } c'
  checkTermType c' c .bool (some "note: the condition of `if` is a `Bool`")
  let gx ← Core.GuardedOperand.thenBranch.guard (pure c) `(¬$c)
  let gy ← Core.GuardedOperand.elseBranch.guard (pure c) `(¬$c)
  let cxa := { cx with emptyOk := Core.Position.shared.checked emptyOk (synthesizes b), natOk, guards := cx.guards.push gx, inElse := false, expected? }
  let cxb := { cx with emptyOk := Core.Position.shared.checked emptyOk (synthesizes a), natOk, guards := cx.guards.push gy, inElse := true, expected? }
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
    let (ma, mb) := (← mentionsAny cx a, ← mentionsAny cx b)
    unless cx.unmentioned || Core.productAccepted ma mb do
      throwError Core.nonlinearMsg.text
    -- For `branches_sharing_code`, without parentheses, as `boolNode` has them.
    if cx.noteIndexes then
      let at_ (s : Syntax) := ((unparen s).getPos?, (unparen s).getTailPos?)
      modifyLocal fun l => { l with mentioning := l.mentioning ++ ([(ma, a), (mb, b)].filter (·.1) |>.map (at_ ·.2)) }
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
  else if e.isOfKind ``Lang.seqExpr then seqLitTerm toTerm { cx with expected? } emptyOk e
  else if e.isOfKind ``Lang.indexExpr then indexTerm toTerm cx e
  else if e.isOfKind ``Lang.recordExpr then do
    let t ← recordTerm (fun x? => toTerm { cx with emptyOk := Core.Position.declared.checked false false, expected? := x?, natOk := x? == some .nat }) cx e
    if let .item { kind := .recordItem, path, .. } ← resolvePath cx.modName (pathSegs e[0]) cx.shadowing then
      lintManualUpdate toTerm cx e path
    return t
  else if e.isOfKind ``Lang.matchExpr then matchTerm toTerm { cx with emptyOk, natOk, expected? } e (parent?.bind (operandSlot · e))
  else if e.isOfKind ``Lang.tableExpr then tableTerm toTerm { cx with emptyOk, natOk, expected? } e
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

open Lang in
/-- Translates a Fren expression to a Lean term, resolving names with Fren's
rules. Variables become references to locals of the same name; variants
become references to the generated constructors. -/
partial def toTerm (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let concatOk := cx.concatOk
  let emptyOk := cx.emptyOk
  let natOk := cx.natOk
  let expected? := cx.expected?
  -- An operand of `or` or `and` continues its chain only if it is one too.
  let parent? := cx.parent?
  let cx := { cx with concatOk := false, emptyOk := false, natOk := false, expected? := none
                      chain := if isBinOp (unparen e) cx.chain then cx.chain else ""
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
  | `(fren_expr| ($a)) => `(($(← toTerm { cx with concatOk, natOk, expected?, emptyOk := Core.Position.shared.checked emptyOk false } a)))
  | `(fren_expr| $n:num) => if natOk then `(($n : Nat)) else `(($n : Int))
  | `(fren_expr| true) => `(true)
  | `(fren_expr| false) => `(false)
  | `(fren_expr| $p:fren_path) => pathTerm toTerm cx parent? e p
  | `(fren_expr| $p:fren_path($args,*)) => appTerm toTerm { cx with natOk } parent? e p args
  | _ =>
    if e.isOfKind ``Lang.letExpr then letTerm toTerm { cx with natOk } emptyOk concatOk e
    else otherTerm toTerm { cx with expected? } parent? emptyOk natOk e

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
  let c ← toTerm { cx with noteIndexes := false } cond
  let c ← if neg then `(¬$c) else pure c
  match ← triggerOf cx body with
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
  return (← xs.mapM fun (ref, g) => return (ref, none, ← mkLambdaFVars fvs (subst (← elabProp g))))
    ++ (← ts.mapM fun (ref, q, g) => return (ref, some q, ← mkLambdaFVars fvs (subst (← elabProp g))))

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

/-- Records the questions about the tables and applications of the body
and contract of the function at `path`, whose parameters are `vars`, or of
the value of the constant at `path`, `tables`, with its preconditions and
postconditions, `props`, as a comp for their checks (`Entry.bodyInfo`), if
it has any questions or postconditions to check (`Core.bodyKinds`). -/
def recordBody (path : Name) (ref : Syntax) (decl : Name) (vars : Array Var)
    (tables : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)) (props : Array PropInfo := #[])
    (fn? : Option Name := none) : TermElabM Unit := do
  if tables.isEmpty && !props.any (·.kind == .ensure) then return
  let uses ← usesOf (tables.map (·.2.2.2.2) ++ props.map (·.body))
  let info : CompInfo := { path := path.getPrefix, vars, props, ref, decl, uses, fn?
                           decidable := !(← getLocal).outsideCore
                           indexes := tables }
  record (.bodyInfo path info)
  modifyLocal fun l => { l with bodies := l.bodies.push path }.declared path

/-- Declares the placeholder for the abstract type or function at `path`
(`AbstractInfo`). -/
def declarePlaceholder (path : Name) (type : Expr) (isType : Bool) (ptys : Array Core.PTy × Core.PTy := (#[], default))
    (fact? : Option Expr := none) : TermElabM Unit := do
  let placeholder := placeholderName path
  addDecl (.axiomDecl { name := placeholder, levelParams := [], type, isUnsafe := false })
  let s ← getState
  let deps := type.foldConsts #[] fun c acc => if s.placeholders.contains c && !acc.contains c then acc.push c else acc
  record (.abstractInfo { path, placeholder, isType, deps, ptys, fact? })
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
a comp's inputs. -/
def paramVars (modName path : Name) (params : Array Syntax) : TermElabM (Array Var) := do
  let paramIds ← params.mapM fun p => do
    let some q := typePath? p[0] | throwErrorAt p[0] (Core.functionParamsMsg path true).text
    pure (pathSegs q)[0]!
  for x in paramIds do discard (segName x)
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

/-- What each application of a function whose result has the declared type
`rp`, of the Lean type `result`, brings: what its result's type does, a
`Nat`'s among it, over an `Int`, as the solver sees a function into `Nat`
(`Fren.natResult`). None if the type brings nothing beyond a `Nat`'s. -/
def resultFact? (result : Expr) (rp : Core.PTy) : TermElabM (Option Expr) := do
  if (rp.cons (← getState).shapeOf).isNone then return none
  factPred? (if result.isConstOf ``Nat then mkConst ``Int else result) rp (rp.ty == .nat)

/-- Elaborates the clauses of the contract of the function `n` at `path`,
whose parameters are `vars` and whose definitions are named under `decl`,
and records the contract (`Reqs/Lang/Items#contracts`). Gives each clause
as a constraint of the function's body's comp, named after the function
and the clause, a postcondition only if the function is defined; and the
questions about the tables and applications in them: a precondition's
under the other preconditions, a postcondition's under all of them. -/
def elabContract (modName path n decl : Name) (defined : Bool) (vars : Array Var) (clauses : Array Syntax) :
    TermElabM (Array Var × Array PropInfo × Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)) := do
  -- The clauses' names share one namespace with the parameters
  -- (`lang::distinct_names`).
  let names := vars.map (·.name) ++ clauses.map fun c => (declaredIdent c[1]).1.getId
  if let some k := (Core.repeatsAt names)[0]? then
    if k ≥ vars.size then throwErrorAt clauses[k - vars.size]![1] (Core.dupClauseMsg names[k]!).text
  -- An uninterpreted function's value, an output of its contract's comp,
  -- for its realizability (`Reqs/Check#contracts-of-uninterpreted-functions`):
  -- named after the function, unless a parameter is.
  let value? ← if defined then pure none else do
    let a ← placeholderOf path
    let name := Core.contractValueName n (vars.map (·.name))
    let ty ← forallTelescope (← getConstInfo a.placeholder).type fun _ r => pure r
    -- With its result's type, which it is realized in.
    let fact? ← factPred? ty a.ptys.2
    pure (some (a.placeholder, ({ name, role := .output, isPub := true, «type» := ty, ref := mkIdent name
                                  ptype := a.ptys.2, fact? } : Var)))
  let mut pres : Array ClauseInfo := #[]
  let mut posts : Array ClauseInfo := #[]
  let mut props : Array PropInfo := #[]
  let mut sites := #[]
  for c in clauses do
    let kw := if c[0].isAtom then c[0] else c[0][0]
    let post := kw.getAtomVal.trimAscii.toString == "ensure"
    let x := c[1]
    liftMsg x (Core.checkNoBang x.getId)
    let cn ← segName x
    lintName .constraint cn x
    if cn.toString.endsWith "?" then throwErrorAt x (Core.propNameMsg cn).text
    let e := withWhere c[3] c[4]
    let (lam, ofValue?, tables) ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let cx : ExprCtx := { modName, vars, insts := #[], place := .prop
                            contract? := some { path, post, params := vars.map (·.name) } }
      discard (takeIndexes fvs)
      let t ← toTerm cx e
      checkDeclared e t (mkConst ``Bool) fun _ => "note: a clause of a contract is a `Bool`"
      let body ← elabProp t
      let tables := (← takeIndexes fvs).filter (·.2.1.isSome)
      -- A postcondition of the value, for realizability: the function
      -- applied to its parameters is the value.
      let ofValue? ← match post, value? with
        | true, some (ph, v) => withLocalDeclD v.name v.type fun x => do
          let app := mkAppN (mkConst ph) fvs
          some <$> mkLambdaFVars (fvs.push x) (body.replace fun t => if t == app then some x else none)
        | _, _ => pure none
      return (← mkLambdaFVars fvs body, ofValue?, tables)
    lintBools e
    let uses ← usesOf #[lam]
    let k : ClauseInfo := { name := cn, decl := decl ++ cn, uses }
    addUsesDef uses k.decl lam
    if post then posts := posts.push k else pres := pres.push k
    sites := sites ++ tables.map fun (r, q, g) => (n ++ cn, if post then Core.IndexPlace.body else .assume, r, q, g)
    props := props.push { kind := if post then .ensure else .assume, name := n ++ cn, ref := x, body := ofValue?.getD lam
                          trigger? := none, triggerRef? := none, decl := k.decl }
  record (.contractInfo { path, pres, posts, defined })
  -- A defined function's contract has nothing to realize, nor an
  -- uninterpreted function's without postconditions.
  let some (_, v) := value?.filter fun _ => !posts.isEmpty
    | return (vars, props.filter (defined || ·.kind == .assume), sites)
  -- Every other formula over the parameters is over the value too, which
  -- it does not mention.
  let withValue (e : Expr) : TermElabM Expr :=
    lambdaBoundedTelescope e vars.size fun xs b => withLocalDeclD v.name v.type fun x => mkLambdaFVars (xs.push x) b
  let props' ← props.mapM fun p => if p.kind == .ensure then pure p else return { p with body := ← withValue p.body }
  let sites' ← sites.mapM fun (n, place, r, q, g) => return (n, place, r, q, ← withValue g)
  return (vars.push v, props', sites')

@[command_elab Lang.fnCmd] def elabFunction : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← segName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  liftMsg nameStx (Core.checkFnName n)
  checkFresh modName n nameStx
  lintName .function n nameStx
  startDeclared
  let path := modName ++ n
  let params := stx[4].getSepArgs
  let body? := if stx[7].isNone then none else some (withWhere stx[7][1] stx[7][2])
  let clauses := stx[8].getArgs
  let contract := !clauses.isEmpty
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Syntax) := !p[1].isNone ||
    (typePath? p[0]).any fun q => (pathSegs q).size == 1 && (declaredIdent (pathSegs q)[0]!).1.getId.toString.endsWith "?"
  let nNamed := (params.filter named).size
  unless Core.functionParamsAccepted body?.isSome contract params.size nNamed do
    let bad := params.find? (named · != (body?.isSome || contract)) |>.getD nameStx
    throwErrorAt bad (Core.functionParamsMsg path body?.isSome contract).text
  let decl := (← getCurrNamespace) ++ path
  let some body := body? | do
    liftTermElabM do
      if contract then
        let vars ← paramVars modName path params
        lintFnBools n nameStx (vars.map (·.type))
        let (result, rp) ← varPType modName nameStx (if stx[6].isNone then none else some stx[6][1])
        declarePlaceholder path (← mkArrowN (vars.map (·.type)) result) false (vars.map (·.ptype), rp) (← resultFact? result rp)
        modifyLocal fun l => { l with outsideCore := false }
        let (vars, props, sites) ← elabContract modName path n decl false vars clauses
        recordBody path nameStx decl vars sites props path
      else
        let pps ← params.mapM fun p => do lintRelTypes modName p[0]; elabPType modName p[0]
        let params := pps.map (·.1)
        lintFnBools n nameStx params
        -- As for a variable, with the result type (`lang::bool_naming`).
        let (result, rp) ← varPType modName nameStx (if stx[6].isNone then none else some stx[6][1])
        declarePlaceholder path (← mkArrowN params result) false (pps.map (·.2), rp) (← resultFact? result rp)
    if contract then
      lintDeclared .function n nameStx
      lintLines .function n nameStx stx
    record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
    unless isPub do recordItem .function path nameStx
  liftTermElabM do
    -- The parameters, declared like a comp's inputs.
    let vars ← paramVars modName path params
    lintFnBools n nameStx (vars.map (·.type))
    let (result, rp) ← varPType modName nameStx (if stx[6].isNone then none else some stx[6][1])
    modifyLocal fun l => { l with outsideCore := false }
    let (lam, tables) ← withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let cx : ExprCtx := { modName, vars, insts := #[], place := .prop, selfFn := some n, natOk := result.isConstOf ``Nat
                            expected? := if result.isConstOf ``Nat then some .nat else none }
      discard (takeIndexes fvs)
      let t ← toTerm cx body
      noteObligation cx .body body rp t
      -- Its tables, the applications of functions with preconditions, and
      -- its pattern types' obligations, for their checks; its indexes are
      -- not checked.
      let tables := (← takeIndexes fvs).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
      checkDeclared body t result fun ty => s!"note: `{n}` returns `{ty}`"
      -- A `Bool` body is decided, classically if need be: equality on an
      -- abstract type has no other `Decidable` instance.
      let value ← if result.isConstOf ``Bool then do
          let p ← elabProp t
          let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
            | .some i => pure i
            | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
          pure (mkApp2 (mkConst ``Decidable.decide) p inst)
        else elabProp t result
      return (← mkLambdaFVars fvs value, tables)
    lintBools body
    -- A parameter that only the contract mentions is used too.
    let mentioned := (pathMentions body ++ clauses.flatMap fun c => pathMentions (withWhere c[3] c[4])).map (·.getRoot)
    for (x, v) in Core.unmentioned (vars.map fun v => (v.name, v)) mentioned do
      recordLint .unusedVariables v.ref (Core.unusedParamMsg x)
    let uses ← usesOf #[lam]
    addUsesDef uses decl lam
    record (.definedInfo { path, decl, uses, nParams := vars.size, ptys := (vars.map (·.ptype), rp) })
    let (_, props, sites) ← if contract then elabContract modName path n decl true vars clauses else pure (vars, #[], #[])
    recordBody path nameStx decl vars (tables.map (fun (r, q, g) => (n, .body, r, q, g)) ++ sites) props path
  lintDeclared .function n nameStx
  lintLines .function n nameStx stx
  record (.item { item := { kind := .fnItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .function path nameStx (defined := true)
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
  -- An input's constraint is the instance's obligation, which the instance
  -- check asks, rather than a fact (`Reqs/Check#instance-assumptions`).
  let vars := c.vars.map fun v =>
    let role := Core.Role.ofInst v.role v.isPub
    { name := w ++ v.name, role, isPub := role == .instOutput, type := v.type, ref := x, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact? : Var }
  return ({ name := w, ref := x, comp := c, bindings := bs, offset }, vars)

/-- The obligations of the inputs of `c`, whose variables are `slice`, an
instance's among `fvs`, whose types have one: each named after its input,
with its type, as written, and closed over `fvs`
(`Reqs/Check#instance-assumptions`). -/
def typedObligations (c : CompInfo) (slice fvs : Array Expr) : TermElabM (Array (Name × String × Expr)) :=
  (c.vars.zip slice).filterMapM fun (v, x) => do
    unless v.role == .input do return none
    let some o := v.ptype.obligation | return none
    let p ← predOf v.type o
    return some (Name.num v.name 0, v.ptype.text, ← mkLambdaFVars fvs (p.beta #[x]))

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
    let t ← if b[1].isNone then toTerm cx (← `(fren_expr| $(⟨x⟩):ident)) else toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk, expected? := ← coreTy? cx.vars[idx]!.type } b[1][1]
    checkDeclared (if b[1].isNone then x else b[1][1]) t cx.vars[idx]!.type fun ty =>
      s!"note: `{x.getId}` of `{Core.showPath pi.comp.path}` has type `{ty}`"
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if cx.vars[idx]!.type.isConstOf ``Int && (← frenTypeOf? t) == some .int then
      modifyLocal fun l => { l with natKept := l.natKept.push (pi.comp.path, Core.nameText x.getId) }
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
  let typed ← typedObligations pi.comp slice fvs
  return (·, mkAnd bindings (pi.comp.meaningDecl slice)) {
    name := pi.name, comp := pi.comp.path, ref := pi.ref, decl
    bindings := ← mkLambdaFVars fvs bindings
    behaviour := ← mkLambdaFVars fvs behaviour
    assumes := typed.map (fun (n, _, f) => (n, f))
      ++ (← pi.comp.assumes.mapM fun a => return (a.name, ← mkLambdaFVars fvs (a.body.beta slice)))
    typed := typed.map fun (n, t, _) => (n, t) }

/-- Whether the evidence `value`, written at `ref`, is testing
(`Reqs/Check#checking-by-testing`). -/
def evidenceTested (ref : Syntax) (value : String) : CommandElabM Bool := do
  let some b := Core.evidenceTested? value | throwErrorAt ref (Core.invalidEvidenceMsg value).text
  return b

/-- Whether the item-level or file-level `fren.evidence` in effect sets
checks to testing. An invalid value, reported once where it is set
(`elabEvidenceOption`), sets nothing. -/
def evidenceInEffect : CommandElabM Bool :=
  return (Core.evidenceTested? (fren.evidence.get (← getOptions))).getD false

/-- `set_option`, as Lean elaborates it, but for `fren.evidence`, an invalid
value is reported once, at the value, rather than at each item it would
set, and does not stop them, as in the `fren` command. -/
@[command_elab Lean.Parser.Command.set_option] def elabEvidenceOption : CommandElab := recordingErrors fun stx => do
  unless stx[1].getId.eraseMacroScopes == `fren.evidence do throwUnsupportedSyntax
  if let some v := stx[3].isStrLit? then
    if (Core.evidenceTested? v).isNone then logErrorAt stx[3] (Core.invalidEvidenceMsg v).text
  elabSetOption stx

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
    if let some (kind, x, _) := constraint? m then
      match kind with
      | .expect | .cover => expects := expects.push (x.getId, b?)
      | .assume => misplaced "an assumption"; constraints := constraints.push x.getId
      | .ensure => misplaced "a guarantee"; constraints := constraints.push x.getId
    else match m with
    -- By the names they declare, without the `!` of shadowing.
    | `(fren_member| inst $x:ident : $_:fren_path { $_,* }) => insts := insts.push ((declaredIdent x).1.getId, b?)
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
/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own, as the `fren` command sees them
(`lint::manual_nat`). -/
partial def constraintConjuncts (e : Syntax) : Array Syntax :=
  let rec go (e : Syntax) : Array Syntax := if isBinOp e "and" then go e[0] ++ go e[2] else #[e]
  go (unparen e)

open Lang in
/-- Records `manual_nat` in the component `compPath` of `members`
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
/-- The name that a member declares, if any: a variable, an instance or a
constraint, which share one namespace (`lang::distinct_names`). -/
def memberName? (m : Syntax) : Option Syntax :=
  if m.isOfKind ``Lang.inMember then some m[1]
  else if m.isOfKind ``Lang.outMember then some m[3]
  else if let some (_, x, _) := constraint? m then some x
  else match m with
    | `(fren_member| inst $x:ident : $_:fren_path { $_,* }) => some x
    | _ => none

open Lang in
/-- The kind of a member without its evidence setting, for
`arbitrary_source_item_ordering`, by its syntax kind; `none` for what is
not one, which a component's members never are. -/
def memberKind? (m : Syntax) : Option Core.MemberKind :=
  [(``Lang.useMember, .use), (``Lang.useGroupMember, .use), (``Lang.inMember, .input), (``Lang.outMember, .output),
    (``Lang.assumeMember, .assumption), (``Lang.instMember, .inst), (``Lang.ensureMember, .guarantee),
    (``Lang.expectMember, .expectation), (``Lang.coverMember, .cover)].lookup m.getKind

open Lang in
/-- The names that a defined output's definition, or an instance's
bindings, mention: a binding `x` without `:= e` mentions `x`. -/
def memberMentions (m : Syntax) : Array Name :=
  if m.isOfKind ``Lang.outMember then
    if m[5].isNone then #[] else (pathMentions m[5][1]).map (·.getRoot)
  else if m.isOfKind ``Lang.instMember then
    -- `inst w: c { b, ... }`
    m[5].getSepArgs.foldl (init := #[]) fun acc b =>
      acc ++ if b[1].isNone then #[(declaredIdent b[0]).1.getId] else (pathMentions b[1][1]).map (·.getRoot)
  else #[]

/-- Records `arbitrary_source_item_ordering` on the component `stx`, whose
members, with their evidence settings, are `raw`, and `members` without
them (`lint::arbitrary_source_item_ordering`). -/
def lintMemberOrder (stx : Syntax) (raw members : Array Syntax) : CommandElabM Unit := do
  let some kinds := members.mapM memberKind? | return
  let some i := Core.firstOutOfOrder? kinds | return
  let msg := Core.memberOrderMsg kinds[i]! kinds[i - 1]!
  let some sub := stx.getSubstring? false false | return
  let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos (p.getD sub.startPos)).length
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  let names := members.map fun m => (memberName? m).map fun x => (declaredIdent x).1.getId
  let mentions := members.map fun m => (memberMentions m).filterMap fun n => names.findIdx? (· == some n)
  let ranges := raw.map fun m => ({ start := off m.getPos?, stop := off m.getTailPos? } : Core.Range)
  let fix? := Core.memberOrderFix? src (off stx[3].getTailPos?) ranges kinds mentions
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown && fix?.isSome
  recordLint .arbitrarySourceItemOrdering raw[i]! (if fixable then msg.note Core.fixHelp else msg)

/-! ### `elabComp`, in parts

Each part is a definition of its own, so that the compiler, whose time grows
faster than the length of a `do` block, compiles several short ones, and
in parallel. -/

section
open Lang

/-- The indexes of a comp's items, and the questions about its tables:
each item's name, where it is, the index's syntax, the question, and the
goal over the comp's variables. -/
abbrev CompIndexes := Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)

/-- A comp's variables, the names declared so far, and whether every one
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
      let (ty, ptype) ← varPType scope x ty?
      let st ← getState
      unless Core.variableTypeAccepted (role == .output) (st.unbounded ty) defn?.isSome do
        throwErrorAt x (Core.unboundedOutputMsg x.getId ptype.text).text
      let fact? ← factPred? ty ptype
      vars := vars.push { name := x.getId, role, isPub, isDet, «type» := ty, ref := x, defn?, ptype, fact? }
    catch ex => logException ex; ok := false
  -- One cycle is reported, as by the `fren` command.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    logErrorAt v.ref (Core.cyclicDefinitionMsg cycle).text; ok := false
  return (vars, names, ok)

/-- A comp's instances, whose variables follow the comp's own `vars`: the
instances still to elaborate, all the variables, the names declared so
far, and whether every instance was resolved. -/
def elabCompInsts (scope : Name) (members : Array Syntax) (vars : Array Var) (names : NameSet) :
    TermElabM (Array PendingInst × Array Var × NameSet × Bool) := do
  let mut ok := true
  let mut vars := vars
  let mut names := names
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
      -- Its bindings give each input of its component a value, and the
      -- instance's assumption check reads them (`unused_assumption`).
      let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Core.Role.input).map (pi.comp.path, ·.name)
      modifyLocal fun l => { l with globalReads := l.globalReads ++ reads }
    catch ex => logException ex; ok := false
  return (pending, vars, names, ok)

/-- A comp's instances, over its variables `fvs`, and then its definitions,
each after those it mentions, with the earlier ones substituted, so that
each value mentions no defined output: the instances, the generated
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
      let (i, body) ← elabInst cx fvs pi (declBase ++ `inst ++ pi.name)
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
      lintBools e
      let value := value.replaceFVars defnFvs (values.map (·.2))
      defs := defs.push (declBase ++ `def ++ v.name, ← mkEq fvs[idx]! value)
      values := values.push (v.name, value)
      defnFvs := defnFvs.push fvs[idx]!
    catch ex => logException ex; good := false
  return (insts, defs, values, defnFvs, indexes, good)

/-- A comp's assumptions, requirements and expectations, over its variables
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
    lintName .constraint x.getId x
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
      indexes := indexes ++ (← takeIndexes fvs subst).map fun (r, q, g) => (x.getId, place, r, q, g)
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
  return (props, defs, indexes, names, good)

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a comp's
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
    for (i, j) in Core.repeatedConstraints (group.map fun (_, _, e) => exactText (unparen e)) do
      let (k, x, _) := group[i]!
      let (k', x', _) := group[j]!
      let msg := Core.duplicateConstraintMsg k' k x'.getId.toString
      let fixable := (Core.duplicateConstraint k' k true).2 && (← getLocal).inMarkdown
      recordLint .duplicateConstraint x (if fixable then msg.note Core.fixHelp else msg)

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
comp's outputs. -/
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
    let mentions ← match v.defn? with | some d => mentionsAny lcx d | none => pure true
    let (constant, definable) := Core.outputLints v.defn?.isSome mentions about.size equation
    if constant then recordLint .constantOutput v.ref (Core.constantOutputMsg v.name)
    if definable then recordLint .definableOutput v.ref (Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a comp's cover goals: each
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

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a comp's
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

/-- Adds a comp's generated definitions `defs` over its variables `fvs`,
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
  -- (`Reqs/Generated#components`).
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

/-- A comp's instances, definitions and constraints, elaborated over its
variables, with its lints of them, and, if all were elaborated, its
generated definitions added: the constraints, the instances, the
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
of a comp whose items were all elaborated: the latter is recorded, to be
reported unless the file reads one of the inputs (`reportLints`), or one
that another assumption ties to a used variable, transitively. -/
def lintCompUnused (scope path : Name) (members : Array Syntax) (vars : Array Var) (instNames : Array Name) :
    TermElabM Unit := do
  let mut mentioned := #[]
  for m in members do
    match m with
    | `(fren_member| inst $_:ident : $_:fren_path { $bs,* }) =>
      for b in bs.getElems do
        let b := b.raw
        mentioned := mentioned ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
    | _ => if let some (_, _, e) := constraint? m then mentioned := mentioned ++ pathMentions e
  for v in vars do
    if let some d := v.defn? then mentioned := mentioned ++ pathMentions d
  -- A public definition says what the output is, so it is used.
  let own := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Core.unmentioned (own.map fun v => (v.name, v)) mentioned do
    recordLint .unusedVariables v.ref (Core.unusedVariableMsg x false (v.role == .output))
  let mut others := #[]
  for m in members do
    match m with
    | `(fren_member| inst $_:ident : $_:fren_path { $bs,* }) =>
      for b in bs.getElems do
        let b := b.raw
        others := others ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
    | _ => if let some (kind, _, e) := constraint? m then
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
    match m with
    | `(fren_member| inst $_:ident : $_:fren_path { $bs,* }) =>
      for b in bs.getElems do
        if !b.raw[1].isNone then others := others ++ (← appliedFns acx b.raw[1][1])
    | _ => if let some (kind, _, e) := constraint? m then
        unless kind == .assume do others := others ++ (← appliedFns acx e)
  for v in vars do
    if let some d := v.defn? then others := others ++ (← appliedFns acx d)
  let links ← assumed.mapIdxM fun i (_, e) => return mss[i]! ++ (← appliedFns acx e)
  let used := Core.usedAssumptions links others
  for (x, _) in assumed, ms in mss, ls in links, u in used do
    if Core.unusedAssumption ms.size (ms.all inputs.contains) u false then
      let r : Core.AssumptionRecord := { component := path, name := x.getId, inputs := ms, links := ls, level }
      modifyLocal fun l => { l with assumptions := l.assumptions.push (r, x) }

/-- A comp's members, elaborated, with the comp recorded if all were: whether
they were, and the generated declarations. -/
def elabCompMembers (scope path modName declBase : Name) (isPub : Bool) (nameStx : Syntax)
    (members : Array Syntax) (tested : Core.Tested) : TermElabM (Bool × Array Name) := do
  let (vars, names, ok) ← elabCompVars scope members
  unless ok do return (false, #[])
  let (pending, vars, names, ok) ← elabCompInsts scope members vars names
  let instNames := pending.map (·.name)
  -- An instance that is not resolved is reported once, not again at each
  -- use of it, as by the `fren` command (`Reqs/View#static-errors`).
  unless ok do return (false, #[])
  -- Bindings; assumptions, requirements and expectations
  let (props, insts, uses, values, indexes, ok) ← elabCompBody scope members vars pending declBase ok names
  lintManualNat path members
  if ok then lintCompUnused scope path members vars instNames
  let mut generated := insts.map (·.decl) ++ props.map (·.decl) ++ #[declBase ++ `assumes, declBase ++ `ensures]
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

@[command_elab Lang.compCmd] def elabComp : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
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
  let (members, tested) ← testedOf (← evidenceInEffect) stx[4].getArgs
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
  lintMemberOrder stx stx[4].getArgs members
  let (ok, generated) ← liftTermElabM <| elabCompMembers scope path modName declBase isPub nameStx members tested
  lintDeclared .component n nameStx
  lintLines .component n nameStx stx
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with comps := l.comps.push path }.declared path

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
  let n ← segName nameStx
  liftMsg nameStx (Core.checkConstName n)
  checkFresh modName n nameStx
  lintName .constant n nameStx
  let path := modName ++ n
  let decl := (← getCurrNamespace) ++ path
  liftTermElabM do
    let (type, pt) ← elabPType modName stx[4]
    lintRelTypes modName stx[4]
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := (← getState).placeholders.contains type.constName
    unless Core.constantAccepted abstract false do
      throwErrorAt stx[4] (Core.unknownConstantMsg abstract).text
    modifyLocal fun l => { l with outsideCore := false }
    discard (takeIndexes #[])
    let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop, emptyOk := Core.Position.declared.checked false false, natOk := type.isConstOf ``Nat, expected? := ← coreTy? type }
    let t ← toTerm cx valueStx
    noteObligation cx .constant valueStx pt t
    let tables := (← takeIndexes #[]).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
    checkDeclared valueStx t type fun ty => s!"note: `{n}` has type `{ty}`"
    let value ← elabProp t type
    let applies ← applications { modName, vars := #[], insts := #[], place := .prop } valueStx
    unless Core.constantAccepted abstract !applies.isEmpty do
      throwErrorAt applies[0]! (Core.unknownConstantMsg abstract).text
    lintBools valueStx
    addDecl (.defnDecl { name := decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
    record (.item { item := { kind := .constItem, path, isPub, owner := modName }, ref := nameStx })
    let int? ← if type.isConstOf ``Int || type.isConstOf ``Nat then intConstValue? { modName, vars := #[], insts := #[], place := .prop } valueStx
      else pure none
    record (.constInfo { path, decl, type, value, int? })
    recordBody path nameStx decl #[] (tables.map fun (r, q, g) => (n, .body, r, q, g))
    unless isPub do recordItem .constant path nameStx
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))

/-- The component that a global expectation's binder of type `ty` ranges
over the behaviours of, or `none` if it ranges over the values of a type
(`lang::quantifier_binder`), which a quantifier checks. A path that names
neither is an error. -/
def globalBinderComp? (modName : Name) (ty : Syntax) : TermElabM (Option Name) := do
  let some p := typePath? ty | return none
  let segs := pathSegs p
  if segs.size == 1 && [`Bool, `Int, `Nat, `String].contains segs[0]!.getId then return none
  match ← resolvePath modName segs with
  | .item { kind := .compItem, path, .. } => return some path
  | .item { kind := .enumItem, .. } | .item { kind := .recordItem, .. } | .item { kind := .typeItem, .. } => return none
  | r => throwErrorAt ty (Core.wrongKindMsg "a component or a type" r).text

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
  -- The binders over values, a quantifier around the body (`lang::quantifier_binder`).
  let mut valueBinders := #[]
  for b in binderStxs do
    let some path ← globalBinderComp? modName b[3] | valueBinders := valueBinders.push b; continue
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
        { name := w ++ v.name, role, isPub := role != .instHidden, type := v.type, ref := x, ptype := v.ptype
          fact? := v.fact? : Var }
  withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
    let cx : ExprCtx := { modName, vars, insts := binders.map (·.name), place := .prop, inGlobal := true }
    discard (takeIndexes fvs)
    let t ← if valueBinders.isEmpty then toTerm cx body else quantTerm toTerm cx body true valueBinders body
    checkDeclared body t (mkConst ``Bool) fun _ => "note: an expectation is a `Bool`"
    let e ← elabProp t
    let indexes := (← takeIndexes fvs).map fun (r, q, g) => (n, Core.IndexPlace.prop, r, q, g)
    lintBools body
    lintConstant cx "expect" body
    for (w, ref) in Core.unmentioned (binders.map fun b => (b.name, b.ref)) ((pathMentions body).map (·.getRoot)) do
      recordLint .unusedVariables ref (Core.unusedVariableMsg w true false)
    -- What it reads through instances (`unused_assumption`).
    let reads := (pathMentions body).filterMap fun m => match m.components with
      | [w, x] => (binders.find? (·.name == w)).map fun b => (b.comp.path, x)
      | _ => none
    -- And the uninterpreted functions it applies, which its binders'
    -- assumptions may constrain.
    let fns ← appliedFns cx body
    let reads := reads ++ binders.flatMap fun b => fns.map (b.comp.path, ·)
    modifyLocal fun l => { l with globalReads := l.globalReads ++ reads }
    -- `unrelated_binders` (`lint::unrelated_binders`).
    let atoms := (boolNode "" 0 (unparen body)).atoms.map fun a => (pathMentions a.ref).map (·.getRoot)
    let groups := Core.binderGroups (binders.map (·.name)) atoms
    if Core.unrelatedBinders groups.size then
      recordLint .unrelatedBinders nameStx (Core.unrelatedBindersMsg n.toString groups)
    -- A quantifier leaves it without a trigger.
    let trig ← if valueBinders.isEmpty then triggerOf cx body else pure none
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
  lintItem stx
  lintTrailingCommas stx
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
  let info ← liftTermElabM <| elabGlobalInfo modName n nameStx binders (withWhere stx[4] stx[5]) decl
  lintDeclared .global n nameStx
  let all ← evidenceInEffect
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
  lintItem stx
  lintTrailingCommas (mkNullNode spec)
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
    -- What it reads by name keeps an `Int` one (`lint::manual_nat`).
    if let some cv := cv? then
      let given (t : Expr) : Core.Given := if t.isConstOf ``Int then .givenInt else .givenNat
      if let (concrete, .givenInt) := Core.refinementGiven input (given v.type) (given cv.type) then
        let kept := (if concrete then c.path else a.path, Core.nameText v.name)
        modifyLocal fun l => { l with natKept := l.natKept.push kept }
  let w := Name.mkSimple c.path.getString!
  if a.insts.any (·.name == w) then throwErrorAt stx[5] (Core.dupMemberMsg w).text
  -- `a`'s assumptions are hypotheses here, so it reads each input of `a`,
  -- through its binding or by name (`unused_assumption`).
  let reads := (a.vars.filter fun v => v.name.isAtomic && v.role == Core.Role.input).map (a.path, ·.name)
  modifyLocal fun l => { l with globalReads := l.globalReads ++ reads }
  let tested := Core.Tested.ofSettings (← evidenceInEffect)
    -- The bindings too, for the definedness of their indexes.
    (a.assumes.map (·.name) ++ bound) ((a.ensures.map (·.name) ++ a.defs.map (·.1)).map (·, none))
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
          else toTerm { cx with emptyOk := Core.Position.declared.checked false false, natOk := v.type.isConstOf ``Nat, expected? := ← coreTy? v.type } b[1][1]
        checkDeclared (if b[1].isNone then x else b[1][1]) t v.type fun ty =>
          s!"note: `{x.getId}` of `{Core.showPath a.path}` has type `{ty}`"
        -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
        if v.type.isConstOf ``Int && (← frenTypeOf? t) == some .int then
          modifyLocal fun l => { l with natKept := l.natKept.push (a.path, Core.nameText x.getId) }
        unless b[1].isNone do lintBools b[1][1]
        let e ← mkLambdaFVars cfvs (← elabProp t v.type)
        return (v, e, ← takeIndexes cfvs)
    let (relational, counts) ← checkCounts
    let l ← getLocal
    -- An input that `a` reads has `a`'s type, which widens to `c`'s
    -- (`refinement::interface`).
    -- It brings what `a`'s type of it brings, and an input that `a` does
    -- not read brings nothing (`Reqs/Lang/Refinement#the-interface`).
    let inputs := (c.vars.filter fun v => v.name.isAtomic && v.role == .input).map fun v =>
      match a.vars.find? fun u => u.name == v.name && u.role == .input && !bound.contains u.name with
      | some u => { v with type := u.type, ptype := u.ptype, fact? := u.fact? }
      | none => { v with fact? := none }
    -- `c`'s inputs' constraints are its instance's obligations.
    let vars := inputs ++ c.vars.map (fun v =>
        let role := Core.Role.ofInst v.role v.isPub
        { v with name := w ++ v.name, role, isPub := role != .instHidden, isDet := false, defn? := none, ref := nameStx
                 fact? := if v.role == .input then none else v.fact? })
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
      let reqs ← a.ensures.mapM fun p => return { reported p with kind := .expect, body := ← lam (p.body.beta argsA) }
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
      let typed ← typedObligations c sliceC fvs
      let instC : InstInfo := { name := w, comp := c.path, ref := nameStx, decl
                                bindings := ← lam (mkAndN bindings.toList)
                                behaviour := ← lam (c.meaning sliceC)
                                assumes := typed.map (fun (n, _, f) => (n, f))
                                  ++ (← c.assumes.mapM fun p => return (p.name, ← lam (p.body.beta sliceC)))
                                typed := typed.map fun (n, t, _) => (n, t) }
      -- `a`'s instances are hypotheses: their assumptions are `a`'s own
      -- obligations, checked in `a` (`Reqs/Lang/Refinement#the-obligation`).
      let instsA ← a.insts.mapM fun i => return { i with
        bindings := ← lam (i.bindings.beta argsA), behaviour := ← lam (i.behaviour.beta argsA), assumes := #[] }
      -- Reported at the refinement, as its other checks are.
      let indexes ← a.indexes.mapM fun (x, place, _, q, goal) => do
        let place := match place with | .binding k => .binding (k + 1) | p => p
        return (x, place, nameStx, q, ← lam (goal.beta argsA))
      -- A binding's, where it is read (`Reqs/Lang/Refinement#bindings`):
      -- an input's under the assumptions, an output's as a requirement.
      let indexes := indexes ++ (← bindingsA.flatMapM fun (v, _, idx) => idx.mapM fun (r, q, goal) => do
        return (v.name, if v.role == .input then .binding 0 else .prop, r, q, ← lam (goal.beta ownC)))
      -- What the types of `a`'s outputs bring, checked as its guarantees
      -- are (`Reqs/Lang/Refinement#the-interface`): an obligation of each.
      let indexes := indexes ++ (← (a.vars.zip argsA).filterMapM fun (v, x) => do
        unless v.name.isAtomic && v.role == .output && v.defn?.isNone do return none
        let some o := v.ptype.obligation | return none
        let p ← predOf v.type o
        let goal := mkApp2 (mkConst ``Fren.typeObligation) (mkStrLit v.ptype.text) (p.beta #[x])
        return some (v.name, Core.IndexPlace.prop, nameStx, none, ← lam goal))
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
