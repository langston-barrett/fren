-- keep-sorted start
import Fren.Elab.ComparisonLints
import Fren.Elab.Records
-- keep-sorted end

/-! # Hosted elaboration: comparisons -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
    let (x, y) ← pairTerms toTerm .comparedOperand { cx with concatOk := cb, emptyOk := Core.ExprSite.comparedOperand.checked false (← synthesizes cx b) }
      { cx with concatOk := ca, emptyOk := Core.ExprSite.comparedOperand.checked false (← synthesizes cx a) } a b
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
  let x ← toTerm { cx with expected? := Core.ExprSite.comparedOperand.expected none (← orderingExpected? toTerm cx #[a, b]) } a
  let tx? ← frenTypeOf? x
  let st ← getState
  let info? := st.enumOf? (← typeOf x)
  let operandTy : Core.Ty ← match tx? with
    | some tx => liftMsg a (Core.orderingType op tx st.orderedDecl)
    | none => pure .int
  let y ← toTerm { cx with expected? := Core.ExprSite.comparedOperand.expected none (some operandTy) } b
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
  let mut x ← toTerm { cx with expected? := Core.ExprSite.comparedOperand.expected none (← orderingExpected? toTerm cx xs) } xs[0]!
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
    let y ← toTerm { cx with guards := cx.guards ++ links, expected? := Core.ExprSite.comparedOperand.expected none t0? } b
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
  let sibling? ← if expected?.isNone && !(← synthesizes cx a) && (← synthesizes cx b) then
      let s ← saveState
      let t? ← frenTypeOf? (← toTerm { cx with noteIndexes := false } b)
      s.restore
      pure t?
    else pure none
  let x ← toTerm { cx with concatOk := true, emptyOk := Core.ExprSite.concatOperand.checked cx.emptyOk (← synthesizes cx b),
                           expected? := Core.ExprSite.concatOperand.expected expected? sibling? } a
  unless (← getState).newtypes.isEmpty || !(← synthesizes cx a) do
    let tx? ← frenTypeOf? x
    checkNewtypeOp "++" tx? tx?
  -- Sequences: outside the core, unless constant.
  if (← typeOf x).isAppOfArity ``Fren.Seq 1 then
    let y ← toTerm { cx with emptyOk := Core.ExprSite.concatOperand.checked cx.emptyOk (← synthesizes cx a), expected? := Core.ExprSite.concatOperand.expected none (← frenTypeOf? x) } b
    if let (some tx, some ty) := (← frenTypeOf? x, ← frenTypeOf? y) then liftMsg b (Core.checkConcatOperands tx ty)
    checkCore cx e .seqWord true true #[a, b] (← isConstant cx e)
    return ← `(($x ++ $y : $(typeSyntax (← typeOf x))))
  -- Where the core allows it, only its operands' outputs matter.
  if concatOk then checkCore cx e .stringAtom true true #[a, b]
  else checkCore cx e .stringSearch true true #[a, b] (← isConstant cx e)
  -- Each operand is a `String`, as the `fren` command checks (`lang::operator_type`).
  checkTermType a x .string (Core.opNote "++" .string)
  let y ← toTerm { cx with concatOk := true, emptyOk := Core.ExprSite.stringOperand.checked false false } b
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
  -- A `Nat` is expected of `min`'s and `max`'s argument where one is of the
  -- whole (`lang::nat_result`).
  let natArg := natOk && rty.isConstOf ``Nat && (m == "min" || m == "max")
  -- An enumeration's or record's `min` and `max` take the receiver's type,
  -- so a variant of a generic type takes its type arguments, as in the
  -- `fren` command.
  let ordered? ← if m == "min" || m == "max" then
      pure ((← frenTypeOf? r).filter (· matches .enum .. | .record ..)) else pure none
  let site : Core.ExprSite := if seq then .seqMethodArgument else if ordered?.isSome then .orderedMethodArgument else .methodArgument
  let as ← args.mapM fun a => do
    let acx := { cx with emptyOk := site.checked false false, natOk := natArg }
    let acx := match ordered? with | some t => { acx with expected? := site.expected (some t) none } | none => acx
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
    let cx := { cx with emptyOk := Core.ExprSite.pairMember.checked cx.emptyOk false }
    let (x, y) := (← widenTerm (← toTerm cx e[1]), ← widenTerm (← toTerm cx e[3]))
    -- Typed, so that a pair of numerals is a pair of `Int`s.
    return ← `((($x, $y) : $(typeSyntax (← typeOf x)) × $(typeSyntax (← typeOf y))))
  toTerm cx e


end Fren
