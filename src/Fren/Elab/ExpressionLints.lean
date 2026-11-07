-- keep-sorted start
import Fren.Elab.Mentions
-- keep-sorted end

/-! # Hosted elaboration: expression lints -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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

/-- Records `assertions_on_constants` on the clause `e` of the contract of
the function `f`, a postcondition if `post`, if it mentions nothing, and
otherwise `contract_mentions_nothing` if it mentions nothing of `f`'s own
(`lint::contract_mentions_nothing`). -/
def lintContractClause (cx : ExprCtx) (post : Bool) (clause f : Name) (params : Array Name) (e : Syntax) : TermElabM Unit := do
  let mentioned ← mentionedNames cx e
  if Core.assertionOnConstant mentioned then
    let literal? := match boolNode "" 0 (unparen e) with | .mk (.lit b) .. => some b | _ => none
    recordLint .assertionsOnConstants e (Core.assertionOnConstantMsg (if post then "postcondition" else "precondition") literal?)
  else if Core.contractMentionsNothing mentioned
      (f.toString (escape := false)) (params.toList.map (·.toString (escape := false))) then
    recordLint .contractMentionsNothing e (Core.contractMentionsNothingMsg post (clause.toString (escape := false)) (f.toString (escape := false)) mentioned)

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


end Fren
