-- keep-sorted start
import Fren.Elab.Construction
-- keep-sorted end

/-! # Hosted elaboration: comparison lints -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
    unless ((← getState).recordOf? t).any (·.path == path) do continue
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
  -- The record of an instance too, as `Box<Int>`, by its head (`State.recordOf?`).
  let some info := t?.bind (← getState).recordOf? | return
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


end Fren
