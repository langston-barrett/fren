-- keep-sorted start
import Fren.FinSet
import Fren.Finite
import Fren.Lint
import Fren.Model
import Fren.SeqElems
import Fren.SimpSet
import Fren.Syntax
import FrenCore.Check.Contracts
import FrenCore.Checking
import FrenCore.Closures
import FrenCore.FnBlocks
import FrenCore.Generics
import FrenCore.Global
import FrenCore.Guards
import FrenCore.Induction
import FrenCore.Lexical
import FrenCore.Mentions
import FrenCore.Patterns
import FrenCore.Procedures
import FrenCore.Quantifier
import FrenCore.Regex
import FrenCore.Symbols
import FrenCore.Syntax
import FrenCore.Traits
import FrenCore.Ty
import FrenCore.TypeFacts
import FrenCore.Typing
-- keep-sorted end

/-! # Hosted elaboration: syntax -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
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
  | .ident info raw x _ =>
    -- A generated name that no source wrote, such as the pattern
    -- shorthand's binder (`Core.shorthandBinder`), has no position; a
    -- written `«#value»` does, and is checked.
    if info.getPos?.isNone && Core.generatedName (Core.nameText x) then return
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
partial def checkParsed (stx : Syntax) (global := false) : CommandElabM Unit := do
  let global := global || stx.isOfKind ``Lang.globalBlockCmd
  if stx.isOfKind ``Lang.refinesMember then
    stx.getArgs[:6].toArray.forM (checkParsed · global)
    return
  let reserved (p : Syntax) : CommandElabM Unit := do
    let id := (pathSegs p)[0]!
    if id.getId.getRoot == Name.mkSimple "table" then throwErrorAt id Core.tableNameMsg
  match stx with
  | `(fren_expr| $a == $_) | `(fren_expr| $a && $_) | `(fren_expr| $a || $_) | `(fren_expr| $a | $_) =>
    checkParsed a global
    throwErrorAt stx[1] (Core.foreignOpMsg stx[1].getAtomVal.trimAscii.toString).text
  | `(fren_expr| $p:fren_path) =>
    reserved p
    unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
  | `(fren_expr| $p:fren_path($args,*)) =>
    reserved p
    unless (pathSegs p).size == 1 do discard (segNames (pathSegs p))
    args.getElems.forM (checkParsed · global)
  | _ =>
    if stx.isIdent then discard (segName stx)
    else if stx.isOfKind ``Lang.fren_path then discard (segNames (pathSegs stx))
    else if stx.isOfKind ``Lang.fren_result_evidence then
      unless stx[1].getId == `fren.evidence do
        throwErrorAt stx[1] (Core.memberOptionMsg stx[1].getId.toString).text
    else if stx.isOfKind ``Lang.evidenceMember then
      unless stx[1].getId == `fren.evidence do
        throwErrorAt stx[1] (Core.memberOptionMsg stx[1].getId.toString).text
      checkParsed stx[4] global
    else if stx.isOfKind ``Lang.fren_proc_param then
      -- A parameter's modifier or definition, as the `fren` command's
      -- parser reports it.
      unless stx[0].isNone do throwErrorAt stx[0] (Core.paramModifierMsg ((stx[0].reprint.getD "").trimAscii.toString)).text
      checkParsed stx[1] global
      checkParsed stx[2] global
      unless stx[3].isNone do throwErrorAt stx[3][0] (Core.inputDefinitionMsg global).text
    else if stx.isOfKind ``Lang.fren_row && !stx[0].isNone then
      -- A row that starts with `|` (`F0166`).
      throwErrorAt stx[0] Core.rowBarMsg.text
    else if stx.isOfKind ``Lang.fieldExpr || stx.isOfKind ``Lang.methodExpr then
      stx.getArgs.forM fun a => unless a.isIdent do checkParsed a global
    else stx.getArgs.forM (checkParsed · global)

/-- Records `unnecessary_trailing_comma` on the commas of the command `stx`
that end a list on the line of its `}` or `]`
(`lint::unnecessary_trailing_comma`). -/
def lintTrailingCommas (stx : Syntax) : CommandElabM Unit := do
  -- A trait's member's, which the trait reports.
  if (← getLocal).inTrait then return
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


end Fren
