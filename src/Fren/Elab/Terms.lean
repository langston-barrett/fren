-- keep-sorted start
import Fren.Elab.Applications
import Fren.Elab.Arithmetic
import Fren.Elab.Matches
import Fren.Elab.Quantifiers
import Fren.Elab.Sequences
import Fren.Elab.Tables
-- keep-sorted end

/-! # Hosted elaboration: terms -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
  let cxa := { cx with emptyOk := Core.ExprSite.branch.checked emptyOk (← synthesizes cx b), natOk, guards := cx.guards.push gx, inElse := false, expected?
                       binders := cx.binders ++ seen .body }
  let cxb := { cx with emptyOk := Core.ExprSite.branch.checked emptyOk (← synthesizes cx a), natOk, guards := cx.guards.push gy, inElse := true, expected?
                       binders := cx.binders ++ seen .elseBranch }
  let (x, y) ← pairTerms toTerm .branch cxa cxb a b
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
    let t ← recordTerm (fun x? => toTerm { cx with emptyOk := Core.ExprSite.recordField.checked false false, expected? := Core.ExprSite.recordField.expected x? none, natOk := x? == some .nat }) cx expected? e
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
    let inner ← toTerm { cx with concatOk, natOk, expected?, emptyOk := Core.ExprSite.parenthesized.checked emptyOk false,
                                 testContext := test.1, testAt? := test.2 } a
    `(($inner))
  | `(fren_expr| $n:num) => if natOk then `(($n : Nat)) else `(($n : Int))
  | `(fren_expr| true) => `(true)
  | `(fren_expr| false) => `(false)
  | `(fren_expr| $p:fren_path) => pathTerm toTerm cx parent? e p expected?
  | `(fren_expr| $p:fren_path($args,*)) => appTerm toTerm { cx with natOk } parent? e p args expected?
  | _ =>
    if e.isOfKind ``Lang.letExpr then letTerm toTerm { cx with natOk } emptyOk concatOk expected? e
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


end Fren
