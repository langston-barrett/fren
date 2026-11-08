-- keep-sorted start
import FrenCli.Elab.ExprSupport
import FrenCli.MatchDisjoint
-- keep-sorted end

/-!
# Expression elaboration for `.fren` files

Type-checks expressions and translates them to SMT-LIB terms with mutually
recursive elaborators. Also holds helpers for definitions, contract lints
and quantifier triggers.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

mutual
/-- Two parts of the same type at `site`, each checked against the other's,
when it does not synthesize its own (`lang::checked`). -/
partial def exprPair (site : Fren.Core.ExprSite) (cxa cxb : ExprCtx) (a b : Expr) : M ((String × Ty) × (String × Ty)) := do
  let sibling (cx' : ExprCtx) (t : Ty) := site.expected cx'.expected? (some t.widen)
  let (cxa, cxb) := ({ cxa with expected? := site.expected cxa.expected? none }, { cxb with expected? := site.expected cxb.expected? none })
  if !(← synthesizes cxa a) && (← synthesizes cxb b) then
    let rb ← elabExpr cxb b
    return (← elabExpr { cxa with expected? := sibling cxa rb.2 } a, rb)
  let ra ← elabExpr cxa a
  return (ra, ← elabExpr { cxb with expected? := sibling cxb ra.2 } b)

/-- `e`, elaborated in `cx`, which must be of the type `t`; `why` notes why. -/
partial def exprExpect (cx : ExprCtx) (e : Expr) (t : Ty) (why : Option String := none) : M String := do
  let (s, t') ← elabExpr cx e
  liftMsg e.span (Fren.Core.checkType t t' why)
  return s

/-- `length_zero`, `card_zero` and `absurd_extreme_comparisons` on `a op b`
(`lint::length_zero`, `lint::absurd_extreme_comparisons`). -/
partial def exprLintLength (cx : ExprCtx) (e : Expr) (op : String) (a b : Expr) : M Unit := do
  unless cx.noteIndexes do return
  let some c := Fren.Core.Comparison.ofOp? op | return
  let lit? : Expr → Option Int
    | .num _ d => some d
    | .neg _ (.num _ d) => some (-(d : Int))
    | _ => none
  -- The length, the literal, and whether the length is on the left.
  let (n, d, left) ← match lit? b, lit? a with
    | some d, _ => pure (a, d, true)
    | none, some d => pure (b, d, false)
    | none, none => return
  let some (recv, card) := lengthOf? n | return
  -- `const_is_empty` (`lint::const_is_empty`), rather than `length_zero`
  -- and `card_zero` on a literal, or `absurd_extreme_comparisons` where
  -- it fires.
  let literal := recv.literalCount?.isSome
  if let some (set, count) := recv.literalCount? then
    let (fires, value) := Fren.Core.constIsEmpty c d left set count
    -- `[]` and `{}` have no type here, which is an error.
    let untyped := count == 0 && !(recv matches .str ..)
    if fires && card == set && !untyped then
      lint .constIsEmpty e.span (Fren.Core.constIsEmptyMsg value)
      return
  let fires := !literal && (Fren.Core.lengthZero c d left).1
  let empty := (Fren.Core.lengthZero c d left).2
  let (absurd, value) := Fren.Core.absurdComparison c d left
  unless fires || absurd do return
  -- Only its type: what elaborating it reports is reported where it is.
  let saved ← get
  let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, concatOk := true } recv)
    fun _ => pure none
  set saved
  let some t := t? | return
  let isSet := t matches .set _ | .rel ..
  unless card == isSet do return
  if absurd then
    if card || t matches .string | .seq _ then lint .absurdExtremeComparisons e.span (Fren.Core.absurdComparisonMsg card value)
    return
  let emptyText := match t with | .string => "\"\"" | .seq _ => "[]" | _ => "{}"
  lintFix (if card then .cardZero else .lengthZero) e.span
    (Fren.Core.lengthZeroMsg card { text := ← srcAt (recv.writtenSpan (← get).src), prec := recv.boolNode.kind.prec }
      emptyText empty d)

/-- `redundant_method_chain`, at the end of a chain (`lint::method_chain`):
not on the receiver of a field or method read without arguments. -/
partial def exprLintChain (cx : ExprCtx) (e : Expr) (parent? : Option Expr) (src : Array Char) (slot : Option Fren.Core.Slot) : M Unit := do
  let inChain := parent?.any fun
    | .field _ r _ | .method _ r _ #[] => r.span == e.span
    | _ => false
  unless cx.noteIndexes && !inChain do return
  let steps := namesRead e
  let ms := steps.map (Fren.Core.Method.ofName? ·.2)
  let shortens (i : Nat) := match ms[i]?, ms[i + 1]? with
    | some (some a), some (some b) => Fren.Core.methodChain a b != .keep
    | _, _ => false
  unless (List.range steps.size).any shortens do return
  -- The first receiver that is a relation or a sequence, which has no
  -- fields: the names after it are its methods.
  for (recv, _) in steps, i in [0:steps.size] do
    let saved ← get
    let rcx := { cx with noteIndexes := false, concatOk := true }
    let t? : Option Ty ← tryCatch (some <$> (·.2) <$> elabExpr rcx recv) fun _ => pure none
    set saved
    unless t? matches some (.rel ..) | some (.seq _) do continue
    let some chain := (ms.extract i).mapM id | return
    let short := Fren.Core.shortestChain chain.toList
    if short.length < chain.size then
      let written := Fren.Core.textOf src (Fren.Core.withParens src (toRange (recv.writtenSpan src)))
      let fixed : Fren.Core.BText :=
        if short.isEmpty then { text := Fren.Core.textOf src (toRange recv.span), prec := recv.boolNode.kind.prec }
        else { text := written ++ String.join (short.map (s!".{·.name}")), prec := Fren.Core.BKind.atom.prec }
      lintFix .redundantMethodChain (e.writtenSpan src) (Fren.Core.methodChainMsg (fixed.inSlot slot (← followedSpan e.span)))
    return

partial def elabExpr (cx : ExprCtx) (e : Expr) : M (String × Ty) := do
  let result ← elabExprCore cx e
  noteResolved "expr" e.span fun _ => result.2.showQualified
  if e matches .app .. then
    let st ← get
    if st.resolved?.isSome then
      if let some args := st.callTargs[(st.file, e.span.start)]? then
        noteResolved "arguments" e.span fun _ => s!"<{", ".intercalate (args.toList.map (·.showQualified))}>"
  return result

/-- `elabExpr` before recording its surface type. -/
partial def elabExprCore (cx : ExprCtx) (e : Expr) : M (String × Ty) := do
  let original := cx
  let concatOk := cx.concatOk
  let expected? := cx.expected?
  let chain := cx.chain
  let parent? := cx.parent?
  let inElse := cx.inElse
  -- Only `and` and `is` read where their chain is (`lang::test_scope`).
  let test := (cx.testContext, cx.testAt?)
  let cx := { cx with concatOk := false, expected? := none, chain := "", parent? := some e, inElse := false
                      testContext := .standalone, testAt? := none }
  let opNote := Fren.Core.opNote
  match e with
  | .block sp op members => do
    let mut seen : Array String := #[]
    for (label, _) in members do
      if let some label := label then
        if seen.contains label.name then
          err label.span { code? := some "F0372", headline := s!"duplicate Boolean member label `{label.name}`", label? := some "already used in this block" }
        seen := seen.push label.name
    if op == "iff" && members.size <= 1 then
      for (_, member) in members do
        let (_, ty) ← elabExpr { original with noteIndexes := false, expected? := some .bool } member
        liftMsg member.span (Fren.Core.checkType .bool ty (some "note: a Boolean block member is a `Bool`"))
    let before ← get
    let result ← elabExpr original (Expr.lowerBlock sp op members)
    -- A source operation may occur in several branches of the generated
    -- decision tree. Conjoin its guarded obligations into one source site.
    let after ← get
    let mut indexes := #[]
    for (source, goal, kind) in after.indexes.extract before.indexes.size after.indexes.size do
      if let some k := indexes.findIdx? fun (old, previous, oldKind) => old == source && oldKind == kind && siteOperation previous == siteOperation goal then
        let (old, previous, oldKind) := indexes[k]!
        indexes := indexes.set! k (old, conj #[previous, goal], oldKind)
      else indexes := indexes.push (source, goal, kind)
    let mut tables := #[]
    for (source, kind, goal) in after.tables.extract before.tables.size after.tables.size do
      if let some k := tables.findIdx? fun (old, oldKind, previous) => old == source && oldKind == kind && siteOperation previous == siteOperation goal then
        let (old, oldKind, previous) := tables[k]!
        tables := tables.set! k (old, oldKind, conj #[previous, goal])
      else tables := tables.push (source, kind, goal)
    modify fun s => { s with
      indexes := before.indexes ++ indexes
      tables := before.tables ++ tables
      lintReports := before.lintReports ++ (s.lintReports.extract before.lintReports.size s.lintReports.size).filter (fun r => r.ref != sp)
      lintFixes := before.lintFixes ++ (s.lintFixes.extract before.lintFixes.size s.lintFixes.size).filter (fun r => r.span != sp) }
    return result
  | .when span neg c d => elabWhenExpr cx e span neg c d
  | .quant span all bs body => elabQuantExpr cx span all bs body
  | .not _ a => return (s!"(not {← exprExpect { cx with testContext := .notOperand } a .bool (opNote "not" .bool)})", .bool)
  | .ite span c a b => elabIteExpr cx e expected? inElse span c a b
  | .neg span a => elabNegExpr cx span a
  | .num _ v => return (toString v, Fren.Core.literalTy (expected? == some .nat))
  | .set span elems => elabSetExpr cx expected? span elems
  | .pair span .. => err span Fren.Core.pairPlaceMsg
  | .seq span elems => elabSeqExpr cx expected? span elems
  | .index span q i => elabIndexExpr cx span q i
  | .str span v => elabStrExpr span v
  | .method span recv m args => elabMethodExpr cx e expected? parent? span recv m args
  | .bool _ b => return (toString b, .bool)
  | .chain _ es ops => elabChainExpr cx es ops
  | .bin span op a b => elabBinExpr cx e concatOk expected? chain test span op a b
  | .path _ segs => elabPathExpr cx e expected? parent? segs
  | .app span segs args => elabAppExpr cx expected? span segs args
  | .field span a f => elabFieldExpr cx e parent? span a f
  | .record span tySegs fields => elabRecordExpr cx expected? span tySegs fields
  | .update span base fields => elabUpdateExpr cx span base fields
  | .match span scrutinee arms isTable => elabMatchExpr cx e expected? parent? span scrutinee arms isTable
  | .matches span scrutinees arms isTable =>
    if scrutinees.isEmpty then err span Fren.Core.closurePlaceMsg
    elabMatchExpr cx e expected? parent? span scrutinees[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) isTable
      (some (scrutinees, arms.map (·.1)))
  | .table span rows => elabTableExpr cx e expected? parent? span rows
  | .is span scrutinee p => elabIsExpr cx test span scrutinee p
  | .«let» span defs body isWhere => elabLetExpr cx span concatOk expected? defs body isWhere
  -- Only an argument for a function parameter (`lang::function_argument`).
  | .closure span .. => err span Fren.Core.closurePlaceMsg

/-- `elabExpr` on a `when` or `unless`. -/
partial def elabWhenExpr (cx : ExprCtx) (e : Expr) (span : Span) (neg : Bool) (c : Expr) (d : Expr) : M (String × Ty) := do
  -- `eq_op` (`lint::eq_op_conditional`).
  if cx.noteIndexes then
    let tc ← srcAt c.span
    -- The body of `when` sees the names that the condition's pattern tests
    -- bind (`lang::test_scope`).
    let seen ← if neg then pure [] else chainBinders cx c
    if let some v := Fren.Core.eqOpConditional neg (Fren.Core.writtenSameIn tc (← srcAt d.span) [] seen) then
      lint .eqOp span (Fren.Core.eqOpConditionalMsg neg v tc)
  let kw := if neg then "unless" else "when"
  -- The names that the condition's pattern tests bind, which the body of
  -- `when` sees (`lang::test_scope`).
  let context : Fren.Core.TestContext := if neg then .unlessCondition else .whenCondition
  let (c, new) ← withBound do
    exprExpect { cx with testContext := context } c .bool (some s!"note: the condition of `{kw}` is a `Bool`")
  let g := (if neg then Fren.Core.GuardedOperand.unlessBody else .whenBody).guard c s!"(not {c})"
  let seen := if Fren.Core.binderVisible context 0 1 .body then new else #[]
  let (d, td) ← elabExpr { cx with guards := cx.guards.push g, binders := cx.binders ++ seen } d
  unless td == .bool do mismatch e .bool td (some s!"note: the body of `{kw}` is a `Bool`")
  return (if neg then s!"(=> (not {c}) {d})" else s!"(=> {c} {d})", .bool)

/-- `elabExpr` on a quantifier. -/
partial def elabQuantExpr (cx : ExprCtx) (span : Span) (all : Bool) (bs : Array Binder) (body : Expr) : M (String × Ty) := do
  -- Expanded over the bound names of listed types: the body, elaborated
  -- once, at each combination of their values
  -- (`Reqs/Lang/Quantifiers#meaning`), and so are the definedness goals
  -- of its indexes, and the questions about its tables, which hold in
  -- every instance. The other bound names are the solver's quantifier's,
  -- around the expansion, and around those goals as a `forall`, whatever
  -- the quantifier (`Reqs/Lang/Quantifiers#unbounded-quantifiers`).
  let (new, combos, free, unlisted) ← quantBinders cx bs (defer := true)
  let names := new.map (·.name.getString!)
  -- A quantifier over a sequence's elements (`lang::element_quantifier`):
  -- each bound name of a type that is not listed has the members of `x in
  -- e` as its domain, by the first conjunct of the guard that names it.
  let parts := Fren.Core.guardPartsBy guardNode whenOf? all body
  let members : Array (Option Expr) := new.zipIdx.filterMap fun (c, k) =>
    if !c.unbounded then none else some <|
      match domainOf all names body k (c.ty == Ty.nat) with
      | (.members j, bounds) =>
        if (parts.extract 0 j).any (·.any (·.names names[k]!)) then none else bounds[j]?.bind (·.map (·.1))
      | _ => none
  let candidate := !members.isEmpty && members.all Option.isSome
  let nesting : Fren.Core.ElementNesting := match cx.elemKind? with
    | none => .top
    | some k => if k == all && cx.elemDirect.contains span then .direct else .other
  let bodyCx := if candidate then
      { cx with elemGuards := cx.elemGuards ++ members.filterMap (·.map (·.span)), elemKind? := some all
                elemDirect := cx.elemDirect ++ (elementSpine all body).toArray
                elemChain := (if nesting == .direct then cx.elemChain else #[]) ++ (new.filter (·.unbounded)).map (·.name) }
    else cx
  let outer ← takeIndexes
  let outerTables ← takeTables
  let natBefore := (← get).natApps.size
  let mark := (← get).boundMentions.size
  let (b, tb) ← elabExpr { bodyCx with binders := cx.binders ++ new, instances := cx.instances * combos.size } body
  if cx.noteIndexes then lintQuant span all bs new body mark
  let kw := if all then "forall" else "exists"
  unless tb == .bool do mismatch body .bool tb (some s!"note: the body of `{kw}` is a `Bool`")
  -- Its verdict, from its bound names of types that are not listed, in order.
  let verdict ← if !candidate then pure Fren.Core.ElementVerdict.notMembers else do
    let recorded := (← get).elemMembers
    let inner := body.declaredNames.map Name.mkSimple
    let unbounded := new.filter (·.unbounded)
    let mut infos := #[]
    for c in unbounded, e? in members, k in [0:unbounded.size] do
      let some e := e? | continue
      let seq := (recorded.find? (·.1 == e.span)).any (·.2.1)
      let earlier := (unbounded.extract 0 k).map (·.name) ++ (cx.binders.filter (·.unbounded)).map (·.name)
      infos := infos.push
        { members := if seq then .seq else .set
          receiverBound := (mentions e).any (earlier.contains ·.getRoot)
          uses := (← elementUses cx c.name inner body).toList : Fren.Core.ElementBinder }
    -- What the quantifier mentions, once its own bound names are not.
    let whole := Expr.quant span all bs body
    let chain := if nesting == .direct then cx.elemChain else #[]
    let bound := (mentions whole).any fun n =>
      let r := n.getRoot
      !chain.contains r && (cx.binder? r).any (·.unbounded)
    pure (Fren.Core.elementVerdict nesting (← mentionsOutput cx whole) bound infos.toList)
  let inCore := verdict == .inCore
  -- The reports that its guard's memberships deferred, and its binders'.
  let spans := members.filterMap (·.map (·.span))
  let deferred := (← get).elemMembers.filter (spans.contains ·.1)
  modify fun s => { s with elemMembers := s.elemMembers.filter (!spans.contains ·.1) }
  unless inCore do
    modify fun s => { s with quantified := true }
    for (_, _, r?) in deferred do
      if let some (sp, msg) := r? then
        modify fun s => { s with outsideCore := true }
        lint .undecidable sp msg
    unless cx.unmentioned do
      for sp in unlisted do
        modify fun s => { s with outsideCore := true }
        lint .undecidable sp ((Fren.Core.elementUndecidableMsg verdict).getD (Fren.Core.undecidableMsg .quantifier false))
  -- A bound name of a type that is not listed, with a domain, makes the
  -- queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`), unless the
  -- quantifier is expanded.
  if !inCore && new.zipIdx.any (fun (c, k) => c.unbounded && (domainOf all names body k (c.ty == Ty.nat)).1 != .unbounded) then
    modify fun s => { s with guardedUsed := true }
  let syms := new.filterMap fun c => if c.unbounded then none else some c.smt
  let inst (smt : String) (vals : Array String) : String :=
    substQuoted (fun p => match syms.idxOf? (quote p) with | some i => vals[i]! | none => quote p) smt
  let inner ← takeIndexes
  let innerTables ← takeTables
  modify fun s => { s with indexes := outer ++ inner.map (fun (sp, g, t) => (sp, bindFree free true (conj (combos.map (inst g))) inCore, t)),
                           tables := outerTables ++ innerTables.map fun (sp, q, g) => (sp, q, bindFree free true (conj (combos.map (inst g))) inCore) }
  -- The `Nat` applications in the body, at each instance, as the solver
  -- sees them (`natFacts`); one whose arguments mention a bound name of a
  -- type that is not listed brings its facts for every value of the bound
  -- names, as each holds whatever the arguments: the solver's quantifier
  -- over them, around it, whose facts are within it (`appFactsOf`).
  let freeIn (app : String) : Array FreeBound := free.filter fun u => (app.splitOn u.sym).length > 1
  let close (app : String) : String :=
    let us := freeIn app
    if us.isEmpty then app
    else s!"(forall ({" ".intercalate (us.toList.map fun u => s!"({u.sym} {u.sort})")}) {app})"
  modify fun s => { s with natApps := s.natApps.extract 0 natBefore
    ++ ((s.natApps.extract natBefore).map close |>.flatMap fun app => combos.map (inst app)).toList.eraseDups.toArray }
  let instances := combos.map (inst b)
  let expanded := if all then conj instances else if instances.size == 1 then instances[0]! else s!"(or {" ".intercalate instances.toList})"
  return (bindFree free all expanded inCore, .bool)

/-- `elabExpr` on an `if`. -/
partial def elabIteExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (inElse : Bool) (span : Span) (c : Expr) (a : Expr) (b : Expr) : M (String × Ty) := do
  let pair := exprPair .branch
  if cx.noteIndexes && !inElse then lintIfChain cx e
  -- `same_branches` (`lint::same_branches`): not where the condition's
  -- pattern tests bind names, which the `then` branch sees and the `else`
  -- branch does not, so that the same text may mean different values
  -- (`lang::test_scope`).
  if cx.noteIndexes then
    let ta ← srcAt a.span
    if Fren.Core.sameBranches (← chainBinds cx c) (Fren.Core.writtenSame ta (← srcAt b.span)) then
      let .mk kind .. := a.boolNode
      lintFix .sameBranches span (Fren.Core.sameBranchesMsg ta kind.prec (← srcAt { start := 0, stop := span.start })
        (← srcAt { start := span.stop, stop := (← get).src.size }))
  if cx.noteIndexes then
    let ms ← mentionedNames cx c
    unless ms.isEmpty do modify fun s => { s with mentioning := s.mentioning.push (c.span, ms) }
  -- The names that the condition's pattern tests bind, which the `then`
  -- branch sees (`lang::test_scope`).
  let (c, new) ← withBound do
    exprExpect { cx with testContext := .ifCondition } c .bool (some "note: the condition of `if` is a `Bool`")
  let gx := Fren.Core.GuardedOperand.thenBranch.guard c s!"(not {c})"
  let gy := Fren.Core.GuardedOperand.elseBranch.guard c s!"(not {c})"
  let seen (site : Fren.Core.TestSite) := if Fren.Core.binderVisible .ifCondition 0 1 site then new else #[]
  let ((x, tx), (y, ty)) ← pair { cx with expected?, guards := cx.guards.push gx, binders := cx.binders ++ seen .body }
    { cx with expected?, guards := cx.guards.push gy, inElse := true, binders := cx.binders ++ seen .elseBranch } a b
  liftMsg span (Fren.Core.checkBranches tx ty)
  return (s!"(ite {c} {x} {y})", tx.join ty)

/-- `elabExpr` on a negation `-a`. -/
partial def elabNegExpr (cx : ExprCtx) (span : Span) (a : Expr) : M (String × Ty) := do
  let number := exprNumber
  let newtypeOp := @exprNewtypeOp
  let (x, t) ← elabExpr cx a
  newtypeOp "-" span t t (pre := true)
  number a t "-"
  return (s!"(- {x})", .int)

/-- `elabExpr` on a set literal. -/
partial def elabSetExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (elems : Array Expr) : M (String × Ty) := do
  -- A literal's type may be written nowhere, as in `x in {1}`.
  modify fun s => { s with usesSets := true }
  if elems.isEmpty then
    let t ← liftMsg span (Fren.Core.checkEmptyLiteral false expected?)
    return (s!"(as set.empty {t.sort})", t)
  -- Before its members, whose errors would hide them, as in Lean.
  checkCore cx span .setAlgebra true true elems
  -- `duplicate_elements` (`lint::duplicate_elements`).
  if cx.noteIndexes then
    let repeats := Fren.Core.repeatedElements (← elems.mapM (srcAt ·.span))
    if Fren.Core.duplicateElements repeats.size then
      let range (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }
      lintFix .duplicateElements span
        (Fren.Core.duplicateElementsMsg (← get).src (range span) (elems.map (range ·.span)) repeats)
  -- A member, as the fields of its tuple, and the type of the literal
  -- it makes: a pair makes a relation.
  let member (e : Expr) (expected? : Option Ty) : M (String × Ty) := do
    if let some (a, b) := e.pair? (← get).src then
      let (ea?, eb?) := match expected? with | some (.rel x y) => (some x, some y) | _ => (none, none)
      let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected ea? none } a
      let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected eb? none } b
      return (s!"{x} {y}", .rel tx.widen ty.widen)
    let (x, t) ← elabExpr { cx with expected? := expected?.bind fun | .set t => some t | _ => none } e
    return (x, .set t.widen)
  -- Each member is checked against the literal's type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  let sibling? ← if expected?.isNone && !(← synthesizes cx elems[0]!) then
      match ← elems.findM? (synthesizes cx) with
      | some m => do
        let saved ← get
        let t ← (·.2) <$> member m none
        set saved
        pure (some t)
      | none => pure none
    else pure none
  let (x0, t0) ← member elems[0]! (Fren.Core.ExprSite.element.expected expected? sibling?)
  let mut xs := #[x0]
  for e in elems.extract 1 do
    let (x, t) ← member e (Fren.Core.ExprSite.element.expected none (some t0))
    unless t == t0 do
      let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
      err e.span (Fren.Core.membersMsg false mt0 mt t0.show)
    xs := xs.push x
  let ts := xs.map (s!"(tuple {·})")
  let smt := if ts.size == 1 then s!"(set.singleton {ts[0]!})"
    else s!"(set.insert {" ".intercalate (ts.pop.toList)} (set.singleton {ts.back!}))"
  return (smt, t0)

/-- `elabExpr` on a sequence literal. -/
partial def elabSeqExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (elems : Array Expr) : M (String × Ty) := do
  modify fun s => { s with usesSeqs := true }
  if elems.isEmpty then
    let t ← liftMsg span (Fren.Core.checkEmptyLiteral true expected?)
    return (s!"(as seq.empty {t.sort})", t)
  -- Each element is checked against the literal's element type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  let whole? := expected?.bind fun | .seq t => some t | _ => none
  let sibling? ← match whole? with
    | some _ => pure none
    | none => if ← synthesizes cx elems[0]! then pure none else
        match ← elems.findM? (synthesizes cx) with
        | some m => do
          let saved ← get
          let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } m
          set saved
          pure (some t)
        | none => pure none
  let (x0, t0) ← elabExpr { cx with expected? := Fren.Core.ExprSite.element.expected whole? sibling? } elems[0]!
  -- An element is never a `Nat` (`lang::nat_place`).
  let t0 := t0.widen
  let mut xs := #[x0]
  for e in elems.extract 1 do
    let (x, t) ← elabExpr { cx with expected? := Fren.Core.ExprSite.element.expected none (some t0) } e
    let t := t.widen
    unless t == t0 do
      err e.span (Fren.Core.membersMsg true t0.show t.show (Ty.seq t0).show)
    xs := xs.push x
  checkCore cx span .seqArray true true elems
  let us := xs.map (s!"(seq.unit {·})")
  return (if us.size == 1 then us[0]! else s!"(seq.++ {" ".intercalate us.toList})", .seq t0)

/-- `elabExpr` on an index `q[i]`. -/
partial def elabIndexExpr (cx : ExprCtx) (span : Span) (q : Expr) (i : Expr) : M (String × Ty) := do
  let expect := @exprExpect cx
  let (x, tq) ← elabExpr cx q
  let .seq elem := tq | err q.span (Fren.Core.notIndexableMsg tq.show)
  let ix ← expect i .int (some "note: an index is an `Int`")
  checkCore cx span .seqArray true true #[q, i]
  -- `negative_position` (`lint::negative_position`).
  if let (true, some k) := (cx.noteIndexes, Fren.Core.negativeLiteral? (← srcAt i.span)) then
    let src := (← get).src
    lint .negativePosition span (Fren.Core.negativeIndexMsg (Fren.Core.textOf src (Fren.Core.withParens src (toRange (q.writtenSpan src)))) k)
  noteIndex cx span x ix
  return (s!"(seq.nth {x} {ix})", elem)

/-- `elabExpr` on a string literal. -/
partial def elabStrExpr (span : Span) (v : String) : M (String × Ty) := do
  liftMsg span (Fren.Core.checkStringChars v)
  modify fun s => { s with usesStrings := true }
  return (Fren.Core.smtStringLit v, .string)

/-- `elabExpr` on a method call. -/
partial def elabMethodExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span) (recv : Expr) (m : Ident) (args : Array Expr) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  if args.isEmpty then lintChain
  -- `trivial_pattern` (`lint::trivial_pattern`).
  if let (true, #[.str _ p], true) := (m.name == "matches?", args, cx.noteIndexes) then
    -- `manual_pattern_char_comparison` and `almost_complete_range`
    -- (`lint::manual_pattern_char_comparison`, `lint::almost_complete_range`).
    if (Fren.Core.parseRe p) matches .ok _ then
      let lit ← srcAt args[0]!.span
      if let some fixed := Fren.Core.charClassPattern? p then
        lintFix .manualPatternCharComparison args[0]!.span
          (Fren.Core.manualPatternCharComparisonMsg (Fren.Core.patternLiteral lit fixed))
      if let some (fixed, found) := Fren.Core.completeRangesPattern? p then
        lintFix .almostCompleteRange args[0]!.span (Fren.Core.almostCompleteRangeMsg found (Fren.Core.patternLiteral lit fixed))
      -- `literal_dot_in_pattern` (`lint::literal_dot_in_pattern`).
      if let some (fixed, found) := Fren.Core.literalDotsPattern? p then
        lintFix .literalDotInPattern args[0]!.span (Fren.Core.literalDotMsg found (Fren.Core.patternLiteral lit fixed))
    if let some (fix, lit) := Fren.Core.trivialPattern? p then
      let bare : Fren.Core.BText := { text := ← srcAt recv.span, prec := recv.boolNode.kind.prec }
      let fixed := Fren.Core.trivialPatternText bare (recv.text src).text fix lit
      lintFix .trivialPattern (e.writtenSpan src) (Fren.Core.trivialPatternMsg fix (fixed.inSlot slot))
  let (r, t) ← elabExpr { cx with concatOk := true, expected? := Fren.Core.ExprSite.receiver.expected none none } recv
  let mut as := #[]
  for a in args do
    -- A pattern, as SMT-LIB's regular expression.
    if m.name == "matches?" && t == .string then
      let .str sp pat := a | err a.span Fren.Core.patternNotLiteralMsg
      match Fren.Core.parseRe pat with
      | .ok re => as := as.push (re.toSmt, .string, sp)
      | .error e =>
        -- The column in the source: after `r`, `#`s and `"`.
        let st ← get
        let pre := ((st.src.extract sp.start sp.stop).toList.takeWhile (· != '"')).length + 1
        let col := sp.start + pre + e.column
        err { start := col, stop := min (col + 1) (sp.stop - 1) } e.msg
      continue
    -- A sequence method's argument has the receiver's type or its element's.
    let expected? := match t, Fren.Core.Method.ofName? m.name with
      | .seq elem, some method => Fren.Core.ExprSite.seqMethodArgument.expected (match method.params[as.size]? with
        | some .string => some t | some .elem => some elem | some .int => some .int | _ => none) none
      -- A `Nat` is expected of `min`'s and `max`'s argument where one is of
      -- the whole (`lang::nat_result`), which is no type it is checked
      -- against: an `Int` is one too.
      | .nat, some .min | .nat, some .max => expected?.filter (· == .nat)
      -- An enumeration's or record's `min` and `max` take the receiver's
      -- type, so a variant of a generic type takes its type arguments.
      | .enum .., some .min | .enum .., some .max | .record .., some .min | .record .., some .max =>
        Fren.Core.ExprSite.orderedMethodArgument.expected (some t) none
      | _, _ => Fren.Core.ExprSite.methodArgument.expected none none
    let (x, ta) ← elabExpr { cx with expected? } a
    as := as.push (x, ta, a.span)
  -- Typed before it is linted, as in Lean, so that a call with a type
  -- error reports no lint of its own (`Reqs/View#static-errors`).
  let res ← callMethod m.span r t m.name as
  if let (.string, some method) := (t, Fren.Core.Method.ofName? m.name) then
    let constantArgs ← args.allM (isConstant cx)
    let recvConstant ← isConstant cx recv
    -- `min` and `max` compare their strings, as `<=` does.
    let comparable := !(method matches .min | .max) || constantArgs || recvConstant
    checkCore cx span method.construct constantArgs comparable (#[recv] ++ args) (constantArgs && recvConstant)
  -- `min` and `max` of an ordered record or newtype with a `String`
  -- within compare strings (`Reqs/Lang/Decidability#orderings`).
  if (t matches .record .. | .newtype ..) && (m.name == "min" || m.name == "max") then
    if let some plan ← orderPlan? t then
      if plan.strings then
        let (ca, cb) := (← isConstant cx recv, ← args.allM (isConstant cx))
        checkCore cx span .stringCompare true (ca || cb) (#[recv] ++ args) (ca && cb)
  if let (.seq _, some method) := (t, Fren.Core.Method.ofName? m.name) then
    checkCore cx span method.seqConstruct true true (#[recv] ++ args)
      ((← args.allM (isConstant cx)) && (← isConstant cx recv)) (literalOperand := args.any (· matches .seq ..))
  if let some tys := relRange? t m.name then checkRelational cx span tys (#[recv] ++ args)
  checkRelationalCard cx span t m.name recv
  -- `empty_argument` (`lint::empty_argument`).
  if let (some meth, true) := (Fren.Core.Method.ofName? m.name, cx.noteIndexes) then
    -- The receiver as written, with its parentheses, as in the help
    -- `(a ++ b).at((a ++ b).len - 1)`.
    let src := (← get).src
    let recvText := Fren.Core.textOf src (Fren.Core.withParens src (toRange (recv.writtenSpan src)))
    if let some msg := Fren.Core.emptyArgumentMsg? meth (t matches .seq _) recvText (← args.mapM (srcAt ·.span)) then
      lint .emptyArgument span msg
    -- `negative_position` (`lint::negative_position`).
    if let some msg := Fren.Core.negativeArgumentMsg? meth (t matches .seq _) recvText (← args.mapM (srcAt ·.span)) then
      lint .negativePosition span msg
  return res

/-- What the first of the operands `es` of an ordering is expected to be:
if it does not synthesize its type, the type, widened, of the first that
does, elaborated without effect; otherwise nothing, as each later operand
is expected to be of the first's type (`lang::checked`). So a variant of a
generic enumeration takes its type arguments from the other side, as in
`Level::Low < x`. -/
partial def orderingExpected? (cx : ExprCtx) (es : Array Expr) : M (Option Ty) := do
  if ← synthesizes cx es[0]! then return none
  let some m ← es.findM? (synthesizes cx) | return none
  let saved ← get
  let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } m
  set saved
  return some t.widen

/-- `elabExpr` on a chain of comparisons. -/
partial def elabChainExpr (cx : ExprCtx) (es : Array Expr) (ops : Array (String × Span)) : M (String × Ty) := do
  let newtypeOp := @exprNewtypeOp
  -- `a < b <= c` is `a < b and b <= c`, with `b` elaborated once
  -- (`Reqs/Lang/Expressions#chained-comparisons`). As in that expansion,
  -- the comparisons before an operand guard it. The parser has checked
  -- its operators.
  let (x0, t0) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (← orderingExpected? cx es) } es[0]!
  -- The first operand gives the operands' type, a `Nat` widened, if it
  -- is ordered (`lang::operator_type`, `lang::ordered_type`), which each
  -- later operand is expected to have (`lang::checked`).
  let u ← liftMsg es[0]!.span (Fren.Core.orderingType ops[0]!.1 t0 (← orderedDecl))
  let plan := (← orderPlan? u).getD .number
  let mut (x, ca) := (x0, ← isConstant cx es[0]!)
  let mut links := #[]
  for (op, _) in ops, a in es, b in es.extract 1 do
    let (y, tb) ← elabExpr { cx with guards := cx.guards ++ links, expected? := Fren.Core.ExprSite.comparedOperand.expected none (some u) } b
    newtypeOp op (a.span.to b.span) u tb
    liftMsg b.span (Fren.Core.checkType u tb (Fren.Core.opNote op u))
    let cb ← isConstant cx b
    if plan.strings then
      checkCore cx (a.span.to b.span) .stringCompare true (ca || cb) #[a, b] (ca && cb)
    -- SMT-LIB has only `str.<` and `str.<=`.
    links := links.push <| ← if u != .string then orderingSmt plan op x y else pure <| match op with
      | "<" => s!"(str.< {x} {y})"
      | "<=" => s!"(str.<= {x} {y})"
      | ">" => s!"(str.< {y} {x})"
      | _ => s!"(str.<= {y} {x})"
    (x, ca) := (y, cb)
  return (s!"(and {" ".intercalate links.toList})", .bool)

/-- `elabExpr` on a binary operator. -/
partial def elabBinExpr (cx : ExprCtx) (e : Expr) (concatOk : Bool) (expected? : Option Ty) (chain : String)
    (test : Fren.Core.TestContext × Option (Nat × Nat)) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- `eq_op` (`lint::eq_op`).
  if let (some o, true) := (Fren.Core.InfixOp.ofOp? op, cx.noteIndexes) then
    -- Only for an operator that `eqOp` can report, whatever the operands.
    if (Fren.Core.eqOp o true).isSome then
      let ta ← srcAt a.span
      -- The right operand of `and` sees the names that the left's pattern
      -- tests bind (`lang::test_scope`).
      let seen ← if op == "and" then chainBinders cx a else pure []
      if let some v := Fren.Core.eqOp o (Fren.Core.writtenSameIn ta (← srcAt b.span) [] seen) then
        lint .eqOp span (Fren.Core.eqOpMsg o v ta)
  match op with
  | "iff" | "or" | "and" => elabBoolOpExpr cx e chain test span op a b
  | "=" | "!=" => elabEqualityExpr cx e span op a b
  | "<" | "<=" | ">" | ">=" => elabComparisonExpr cx e span op a b
  | "in" => elabInExpr cx e span a b
  | "union" | "inter" | "minus" | "subset" => elabSetOpExpr cx expected? span op a b
  | "join" => elabJoinExpr cx span a b
  | "++" => elabConcatExpr cx e concatOk expected? span op a b
  | "div" | "mod" => elabDivModExpr cx expected? span op a b
  | _ => elabArithExpr cx expected? span op a b

/-- `elabExpr` on a Boolean operator. -/
partial def elabBoolOpExpr (cx : ExprCtx) (e : Expr) (chain : String) (test : Fren.Core.TestContext × Option (Nat × Nat))
    (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let opNote := Fren.Core.opNote
  let smt := if op == "iff" then "=" else op
  -- `membership_chain`, at the top of a chain of `or` or of `and` (`lint::membership_chain`).
  if op != "iff" && chain != op && cx.noteIndexes then
    let ds := chainOperands op e
    let cmp := if op == "and" then "!=" else "="
    let eqs := ds.filterMap fun | .bin _ c l r => if c == cmp then some (l, r) else none | _ => none
    let lefts ← eqs.mapM fun (l, _) => srcAt l.span
    let same := eqs.size == ds.size && lefts.all (· == lefts[0]!)
    let laterIndexes ← (eqs.extract 1).anyM fun (_, v) => return !(← indexedIn v).isEmpty
    let patterns ← eqs.allM fun (_, v) => return Fren.Core.patternValue (← srcAt v.span) (← variantOf? cx v).isSome
    if Fren.Core.membershipChainFires ds.size same laterIndexes patterns then
      lintFix .membershipChain span
        (Fren.Core.membershipChainMsg lefts[0]! (← eqs.mapM fun (_, r) => srcAt r.span) (op == "and"))
  -- `index_after_use` (`lint::index_after_use`).
  if op == "and" && cx.noteIndexes && !(← chainBinds cx a) then
    let qs ← indexedIn a
    if ← qs.anyM fun q => return (← boundsSeq b q) && !(← boundsSeq a q) then
      lintFix .indexAfterUse span (Fren.Core.indexAfterUseMsg (← srcAt a.span) (← srcAt b.span))
  -- For `manual_at_most_one`: whether the operands give a definedness
  -- obligation.
  let mark := (← get).indexes.size + (← get).tables.size
  -- Of `and`, the position of each operand in its chain, and the names
  -- that the left one's pattern tests bind, which the right one sees; at
  -- the top of the chain, those of the whole, which only the body of the
  -- `when` or `if` whose condition it is sees (`lang::test_scope`).
  let (context, at?) := test
  let (k, n) := at?.getD (0, (chainOperands "and" e).size)
  let left := (chainOperands "and" a).size
  let (acx, bcx) : ExprCtx × ExprCtx := match op with
    | "and" => ({ cx with testContext := context, testAt? := some (k, n) }, { cx with testContext := context, testAt? := some (k + left, n) })
    | "or" => ({ cx with testContext := .orOperand }, { cx with testContext := .orOperand })
    | _ => (cx, cx)
  let boundMark := (← get).bound.size
  let (x, tx) ← elabExpr { acx with chain := op } a
  unless tx == .bool do mismatch a .bool tx (opNote op .bool)
  -- `b` is evaluated when `a` does not decide the result.
  let guards := match op with
    | "and" => cx.guards.push (Fren.Core.GuardedOperand.andRight.guard x s!"(not {x})")
    | "or" => cx.guards.push (Fren.Core.GuardedOperand.orRight.guard x s!"(not {x})")
    | _ => cx.guards
  let bound := (← get).bound
  let new := if op == "and" then bound.extract boundMark else #[]
  let (y, ty) ← elabExpr { bcx with guards, chain := op, binders := cx.binders ++ new } b
  unless ty == .bool do mismatch b .bool ty (opNote op .bool)
  if op == "and" && at?.isNone && !Fren.Core.binderVisible context 0 n .body then
    modify fun s => { s with bound := s.bound.extract 0 boundMark }
  if op == "and" && cx.noteIndexes && (← get).indexes.size + (← get).tables.size > mark then
    modify fun s => { s with facts := s.facts.push (span, .obligations) }
  return (s!"({smt} {x} {y})", .bool)

/-- `elabExpr` on `=` or `!=`. -/
partial def elabEqualityExpr (cx : ExprCtx) (e : Expr) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- Functions are not compared (`lang::function_comparison`).
  unless Fren.Core.comparisonAccepted [← comparand cx a, ← comparand cx b] do
    err span (Fren.Core.functionComparisonMsg op)
  let pair := exprPair .comparedOperand
  let lintLength := exprLintLength cx e
  lintLength op a b
  -- `++` is in the core against a constant.
  let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
  let ((x, tx), (y, ty)) ← pair { cx with concatOk := cb } { cx with concatOk := ca } a b
  liftMsg span (Fren.Core.checkComparable op tx ty)
  -- For `manual_pattern_test`, at the end of the expression.
  if cx.noteIndexes && (tx == .nat || ty == .nat) then modify fun s => { s with facts := s.facts.push (span, .natOperands) }
  -- `const_is_empty` on a literal and an empty one (`lint::const_empty_equation`),
  -- after the sides and their types, as in Lean.
  if let (some (_, m), some (_, n), true) := (a.literalCount?, b.literalCount?, cx.noteIndexes) then
    let (fires, value) := Fren.Core.constEmptyEquation (op == "=") (max m n)
    if fires && min m n == 0 then lint .constIsEmpty span (Fren.Core.constIsEmptyMsg value)
  -- For `bool_equality`, at the end of the expression.
  if tx == .bool && cx.noteIndexes then modify fun s => { s with boolEqs := s.boolEqs.push span }
  -- A side that is a `++` is reported as one; one whose definition
  -- has a `++` stands for it, and is reported here.
  let named (e : Expr) : M Bool := do
    return (definitionOf? cx e).isSome && (← hasConcat cx e)
  let concat (e : Expr) := e matches .bin _ "++" _ _
  if tx == .string && ((← named a) || (← named b)) then
    checkCore cx span .stringSearch true true #[] (ca || cb)
  else if tx == .string && !concat a && !concat b then
    checkCore cx span .stringCompare true (ca || cb || (isVariable a && isVariable b)) #[] (ca && cb)
  return (if op == "=" then s!"(= {x} {y})" else s!"(distinct {x} {y})", .bool)

/-- `elabExpr` on an ordering comparison. -/
partial def elabComparisonExpr (cx : ExprCtx) (e : Expr) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let newtypeOp := @exprNewtypeOp
  let lintLength := exprLintLength cx e
  lintLength op a b
  -- The left operand gives the operands' type, if it is ordered
  -- (`lang::operator_type`, `lang::ordered_type`); a newtype on either
  -- side is the newtype's error (`lang::newtype_operator`). The right is
  -- expected to have the left's type, and the left the right's, if only the
  -- right synthesizes one (`lang::checked`).
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (← orderingExpected? cx #[a, b]) } a
  let t ← liftMsg a.span (Fren.Core.orderingType op tx (← orderedDecl))
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (some t) } b
  newtypeOp op span tx ty
  liftMsg b.span (Fren.Core.checkType t ty (Fren.Core.opNote op t))
  -- For the lints of integers, at the end of the expression: what it compares.
  if cx.noteIndexes && !(tx matches .newtype ..) then
    let ordered : Fren.Core.Ordered := if t matches .enum .. then .enumeration
      else if t == .int || t == .nat then .number else .other
    modify fun s => { s with ordereds := s.ordereds.push (span, ordered) }
  let plan := (← orderPlan? t).getD .number
  if plan.strings then
    let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
    checkCore cx span .stringCompare true (ca || cb) #[a, b] (ca && cb)
  -- An ordered enumeration's values compare by their positions, and an
  -- ordered record's by its fields (`Reqs/Lang/Items#ordered-declarations`).
  return (← orderingSmt plan op x y, .bool)

/-- `elabExpr` on `in`. -/
partial def elabInExpr (cx : ExprCtx) (e : Expr) (span : Span) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- Before its operands, whose errors would hide it, as in Lean.
  checkCore cx span .setAlgebra true true #[a, b]
  if let (.set _ #[m], true) := (b, cx.noteIndexes) then
    unless m matches .pair .. do lintFix .singletonMembership span (Fren.Core.singletonMembershipMsg (← srcAt a.span) (← srcAt m.span))
  if let some (pa, pb) := a.pair? (← get).src then
    let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected none none } pa
    let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected none none } pb
    let (tx, ty) := (tx.widen, ty.widen)
    let (r, tr) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipRight.expected none (some (.rel tx ty)) } b
    unless tr == .rel tx ty do
      err span (Fren.Core.membershipTypeMsg (Ty.rel tx ty).show tr.show true)
    return (s!"(set.member (tuple {x} {y}) {r})", .bool)
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipLeft.expected none none } a
  -- A member is never a `Nat`: one is widened (`lang::nat_place`).
  let tx := tx.widen
  -- The right is checked against a set or sequence of the left's type, as
  -- it is written (`lang::checked`).
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipRight.expected none (some (if seqShaped b then .seq tx else .set tx)) } b
  -- The membership of a quantifier over elements' guard: its report waits
  -- for the quantifier's verdict (`elabQuantExpr`).
  if cx.elemGuards.contains b.span then
    let infinite ← #[a, b].anyM (mentionsInfiniteOutput cx)
    let ground ← isConstant cx e
    let report := if ty != .seq tx || cx.unmentioned
        || Fren.Core.inCore .seqWord true true infinite ground (literalOperand := b matches .seq ..)
      then none else some (span, Fren.Core.undecidableMsg .seqWord infinite)
    modify fun s => { s with elemMembers := s.elemMembers.push (b.span, ty == .seq tx, report) }
    if ty == .seq tx then return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
  if ty == .seq tx then
    checkCore cx span .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := b matches .seq ..)
    return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
  unless ty == .set tx do
    err span { code? := some "F0325", headline := s!"`in` needs a `Set<{tx.show}>` on its right, found `{ty.show}`"
               label? := some s!"`{tx.show}` and `{ty.show}`"
               notes := #["note: `x in s` is membership: `s` is a set of values of `x`'s type"] }
  return (s!"(set.member (tuple {x}) {y})", .bool)

/-- `elabExpr` on a set operator. -/
partial def elabSetOpExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let site : Fren.Core.ExprSite := if op == "subset" then .subsetOperand else .setOperand
  let pair := exprPair site
  -- Before its operands, whose errors would hide it, as in Lean.
  checkCore cx span .setAlgebra true true #[a, b]
  -- The operands of `subset` give each other their type, and those of the
  -- others are also checked against the whole's (`lang::checked`).
  let expected? := if op == "subset" then none else expected?
  let ((x, tx), (y, ty)) ← pair { cx with expected? } { cx with expected? } a b
  match Fren.Core.checkSetOperands op tx ty with
  | .ok () => pure ()
  | .error (k, msg) => err (if k == 0 then a else b).span msg
  let smt := match op with
    | "union" => "set.union" | "inter" => "set.inter" | "minus" => "set.minus" | _ => "set.subset"
  return (s!"({smt} {x} {y})", if op == "subset" then .bool else tx)

/-- `elabExpr` on `join`. -/
partial def elabJoinExpr (cx : ExprCtx) (span : Span) (a : Expr) (b : Expr) : M (String × Ty) := do
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.joinOperand.expected none none } a
  let .rel ta tb := tx | err a.span (Fren.Core.joinTypeMsg tx.show none)
  -- Both operands synthesize their types (`lang::checked`).
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.joinOperand.expected none none } b
  let .rel tb' tc := ty | err b.span (Fren.Core.joinTypeMsg ty.show none)
  unless tb == tb' do err span (Fren.Core.joinTypeMsg tx.show (some ty.show))
  checkRelational cx span #[tb] #[a, b]
  return (s!"(rel.join {x} {y})", .rel ta tc)

/-- `elabExpr` on `++`. -/
partial def elabConcatExpr (cx : ExprCtx) (e : Expr) (concatOk : Bool) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let opNote := Fren.Core.opNote
  let newtypeOp := @exprNewtypeOp
  -- Each operand is checked against the whole's type, or the other's
  -- (`lang::checked`): `[] ++ q` takes its type from `q`.
  let sibling? ← if expected?.isNone && !(← synthesizes cx a) && (← synthesizes cx b) then do
      let saved ← get
      let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } b
      set saved
      pure (some t)
    else pure none
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.concatOperand.expected expected? sibling?, concatOk := true } a
  newtypeOp op span tx tx
  if let .seq _ := tx then
    let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.concatOperand.expected none (some tx) } b
    liftMsg b.span (Fren.Core.checkConcatOperands tx ty)
    checkCore cx span .seqWord true true #[a, b] (← isConstant cx e)
    return (s!"(seq.++ {x} {y})", tx)
  -- Where the core allows it, only its operands' outputs matter.
  if concatOk then checkCore cx span .stringAtom true true #[a, b]
  else checkCore cx span .stringSearch true true #[a, b] (← isConstant cx e)
  unless tx == .string do mismatch a .string tx (opNote op .string)
  let (y, ty) ← elabExpr { cx with concatOk := true, expected? := Fren.Core.ExprSite.stringOperand.expected none none } b
  unless ty == .string do mismatch b .string ty (opNote op .string)
  return (s!"(str.++ {x} {y})", .string)

/-- `elabExpr` on `div` or `mod`. -/
partial def elabDivModExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let expect := @exprExpect cx
  let number := exprNumber
  let opNote := Fren.Core.opNote
  let newtypeOp := @exprNewtypeOp
  -- By the divisor's value (`lang::divisor`). A `Nat` is expected of
  -- the dividend where one is of the whole (`lang::nat_result`).
  let (x, tx) ← elabExpr { cx with expected? := if expected? == some .nat then some .nat else none } a
  newtypeOp op span tx tx
  number a tx op
  discard (expect b .int (opNote op .int))
  let (form, value, c) ← divisorForm cx b
  liftMsg b.span (Fren.Core.checkDivisor op form value c)
  -- By a numeral, which the linear logics require: Euclidean,
  -- `x div -k` is `-(x div k)` and `x mod -k` is `x mod k`.
  let k := value.natAbs
  let nat := Fren.Core.natResult (if op == "mod" then .mod else .div) (tx == .nat) false (value > 0)
  return (if op == "mod" then s!"(mod {x} {k})" else if value < 0 then s!"(- (div {x} {k}))" else s!"(div {x} {k})",
    if nat then .nat else .int)

/-- `elabExpr` on `+`, `-` or `*`. -/
partial def elabArithExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let number := exprNumber
  let newtypeOp := @exprNewtypeOp
  if op == "*" then
    let (ma, mb) := (← mentionedNames cx a, ← mentionedNames cx b)
    unless cx.unmentioned || Fren.Core.productAccepted ma mb do err span (Fren.Core.nonlinearMsg ma mb)
    -- For `branches_sharing_code`.
    if cx.noteIndexes then
      modify fun s => { s with mentioning := s.mentioning ++ ([(ma, a.span), (mb, b.span)].filter (!·.1.isEmpty) |>.map fun (m, sp) => (sp, m)) }
  -- `+` and `*` of `Nat`s are `Nat`s; `-` is always an `Int`, so that
  -- nothing truncates (`lang::operator_type`).
  let nat := op != "-" && expected? == some .nat
  if nat && op == "+" then modify fun s => { s with natSums := s.natSums.push (s.file, span) }
  let (x, tx) ← elabExpr { cx with expected? := if nat then some .nat else none } a
  -- Of a newtype, the `+` or `-` of the type it is erased to, as
  -- `N(a.0 + b.0)` is; of a number, a newtype on the right is the
  -- newtype's error (`lang::newtype_operator`).
  if let .newtype .. := tx then
    let (y, ty) ← elabExpr cx b
    newtypeOp op span tx ty
    -- `+` of a newtype of `Nat`, whose `-` would be an error.
    if op == "+" && tx.erased == .nat then modify fun s => { s with natSums := s.natSums.push (s.file, span) }
    -- The obligations of `N(a.0 + b.0)`, of each newtype from the
    -- innermost out, which is the erased sum at each.
    let sum := s!"({op} {x} {y})"
    for p in tx.newtypePaths.reverse do
      noteObligation cx .construction span (← partPTy p 0 0) sum
    return (sum, tx)
  number a tx op
  let (y, ty) ← elabExpr { cx with expected? := if nat then some .nat else none } b
  newtypeOp op span tx ty
  number b ty op
  return (s!"({op} {x} {y})", if op != "-" && tx == .nat && ty == .nat then .nat else .int)

/-- `elabExpr` on a path. -/
partial def elabPathExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (segs : Array Ident) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  if segs.size == 1 then
    lintChain
    let n := identName segs[0]!.name
    let span := segs[0]!.span
    -- A binder or variable, then any fields read from it.
    let base? ← if let some b := cx.binder? n.getRoot then do
        noteResolved "local" span fun _ => n.toString
        if let some sc := b.scrutinee then
          if b.isDef then
            -- A name stands for its definition: its indexes are guarded
            -- here, and what it mentions may be mentioned here, which
            -- elaborating it again checks, without its lints.
            if cx.noteIndexes then
              modify fun s => { s with indexes := s.indexes ++ b.obligations.map (fun (sp, g, t) => (sp, guarded cx.guards g, t)),
                                       tables := s.tables ++ b.tableObligations.map fun (sp, q, g) => (sp, q, guarded cx.guards g) }
            let saved ← get
            discard (elabExpr { cx.at b with noteIndexes := false, pending := #[], expected? := some b.ty } sc)
            set saved
          else discard (elabExpr (cx.at b) sc)
        else if cx.noteIndexes && n.isAtomic then
          modify fun s => { s with boundMentions := s.boundMentions.push (span, b.smt) }
        pure (some ((b.smt, b.ty), n.components.drop 1))
      else
        let ks := (List.range n.components.length).reverse.map (· + 1)
        match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
        | some (v, k) =>
          noteResolved "local" span fun _ => n.toString
          for u in if cx.unmentioned then #[] else defDeps cx.vars v do
            let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
            let ok := Fren.Core.checkMention cx.place u.role earlier u.name
            match ok with
            | .ok () => pure ()
            | .error msg => err span (if u.name == v.name then msg else Fren.Core.throughDefinition v.name msg)
          pure (some ((quote v.name.toString, v.ty), n.components.drop k))
        | none =>
          -- A constant, then the fields read from its value, or the
          -- methods without arguments applied to it.
          let root := n.getRoot
          if n.isAtomic || cx.insts.contains root then pure none else
          let st ← get
          match st.table.resolvePath st.scope #[root] cx.shadowing with
          | .ok (.item { kind := .constItem, .. }) =>
            -- Resolved again, to record its use and any import it uses;
            -- the first lookup leaves a root that is not a constant to the
            -- errors below.
            -- The lexer admits only ASCII identifiers, so characters are
            -- offsets.
            let text := (segs[0]!.name.splitOn ".").head!
            let rootSeg : Ident := { name := text, span := { span with stop := span.start + text.length } }
            let .item { kind := .constItem, path, .. } ← resolve #[rootSeg] cx.shadowing | pure none
            let some c := (← get).consts.find? path | internal span s!"unknown constant `{path}`"
            unless cx.unmentioned do noteItemCore path
            pure (some (c, n.components.drop 1))
          | _ => pure none
    if let some (base, fields) := base? then
      -- The span of each component of the dotted name.
      let parts := segs[0]!.name.splitOn "."
      let starts := parts.foldl (init := #[span.start]) fun acc p => acc.push (acc.back! + p.length + 1)
      let first := parts.length - fields.length
      return ← (fields.zipIdx).foldlM (init := base) fun (smt, t) (f, j) => do
        let fspan : Span := { start := starts[first + j]!, stop := starts[first + j + 1]! - 1 }
        -- Typed before it is linted, as a call is.
        let res ← readField fspan smt t f
        if t == .string then
          let recvName := ".".intercalate (parts.take (first + j))
          let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
          checkCore cx (span.to fspan) .stringAtom true true #[.path recvSpan #[{ name := recvName, span := recvSpan }]]
        if let some tys := relRange? t f.toString then
          let recvName := ".".intercalate (parts.take (first + j))
          let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
          checkRelational cx (span.to fspan) tys #[.path recvSpan #[{ name := recvName, span := recvSpan }]]
        let recvName := ".".intercalate (parts.take (first + j))
        let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
        checkRelationalCard cx (span.to fspan) t f.toString (.path recvSpan #[{ name := recvName, span := recvSpan }])
        if let (.seq _, some m) := (t, Fren.Core.Method.ofName? f.toString) then
          let r : Expr := .path recvSpan #[{ name := recvName, span := recvSpan }]
          checkCore cx (span.to fspan) m.seqConstruct true true #[r] (← isConstant cx r)
        return res
    if let some (_, own) := cx.pending.find? (·.1 == n.getRoot) then
      err span (Fren.Core.definedLaterMsg n.getRoot own)
    if !n.isAtomic then
      err span (Fren.Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name)))
  if segs.size == 1 then
    if let some c := Fren.Core.builtinFunction? (identName segs[0]!.name) then
      err e.span (Fren.Core.unappliedMsg (.mkSimple c.name))
    -- A function parameter, which is applied (`lang::function_argument`).
    if (cx.fnParam? (identName segs[0]!.name)).isSome then
      err e.span (Fren.Core.unappliedMsg (identName segs[0]!.name))
  match ← resolveWritten segs cx.shadowing cx.noteIndexes with
  | .variant en idx =>
    let d := (← get).dataOf? en.path
    let n := (d.bind (·.ctors[idx]?)).map (·.2.size) |>.getD 0
    if let some msg := Fren.Core.variantMentionMsg? (en.path ++ en.variants[idx]!) n false then err e.span msg
    if cx.noteIndexes then
      modify fun s => { s with variants := s.variants.push (e.span, (en.path ++ en.variants[idx]!).toString) }
      if let some d := d then
        if d.ordered then
          modify fun s => { s with facts := s.facts.push (e.span, .ordinal en.path.toString idx d.ctors.size) }
    if let some d := d.filter (!·.params.isEmpty) then
      let (_, args) ← elabConstruction elabExpr .payload { cx with expected? } d #[] #[] e.span (showPath (en.path ++ en.variants[idx]!)) fun _ _ => ""
      return (d.build args.toList en.variants[idx]! [], .enum en.path args.toList)
    return (ctorSym en.path en.variants[idx]!, .enum en.path [])
  | .item { kind := .constItem, path, .. } =>
    let some c := (← get).consts.find? path | internal e.span s!"unknown constant `{path}`"
    unless cx.unmentioned do noteItemCore path
    -- Its value's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    return c
  | .item { kind := .fnItem, path, .. } => err e.span (Fren.Core.unappliedMsg path)
  | r => err e.span (Fren.Core.notAValueMsg r)

/-- `elabExpr` on an application. -/
partial def elabAppExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (segs : Array Ident) (args : Array Expr) : M (String × Ty) := do
  let fnSpan := segs[0]!.span.to segs.back!.span
  if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
    err fnSpan (Fren.Core.varNotAFunctionMsg (identName segs[0]!.name))
  if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
    let f := (← get).module ++ Name.mkSimple segs[0]!.name
    noteResolved "name" fnSpan fun _ => resolvedPath f
    let some (ps, ft, sym) := cx.selfRec? | err fnSpan (Fren.Core.recursiveMsg f)
    -- An application of itself, which must be structural recursion
    -- (`lang::structural_recursion`), typed as a function parameter's.
    unless args.size == ft.params.size do err span (Fren.Core.arityMsg f ft.params.size args.size)
    noteRecUse fnSpan f ps { form := if cx.inClosure then .inClosure else .applied
                             args := args.toList.zipIdx.map fun (a, i) => cx.recArg a i }
    let mut smts := #[]
    for a in args, t in ft.params, k in [0:args.size] do
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
      liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath f}` has type `{t.show}`"))
      let pt := (((← get).funPTys.find? f).map (·.1[k]?.getD default)).getD default
      noteObligation cx .argument a.span pt x
      smts := smts.push x
    if cx.noteIndexes then
      modify fun s => { s with recApps := s.recApps.push (fnSpan, smts, cx.guards) }
    -- Of a generic one, at its own type parameters, the instance that it
    -- applies within itself (`LState.callTargs`,
    -- `Reqs/Lang/Recursion#generic-recursion`).
    if let some (g, tps) := (← get).fnTypeParams.filter (·.1 == f) then
      let own := tps.mapIdx fun k p => Ty.abstract (Fren.Core.typeParamPath g k p)
      modify fun s => { s with callTargs := if s.module == Fren.Core.preludeModule then s.callTargs
                                 else s.callTargs.insert (s.file, span.start) own }
    return (s!"({sym} {" ".intercalate smts.toList})", ft.result)
  -- A function parameter (`Reqs/Lang/HigherOrder#function-parameters`).
  if segs.size == 1 then
    if let some (ft, sym) := cx.fnParam? (identName segs[0]!.name) then
      noteResolved "local" fnSpan fun _ => segs[0]!.name
      let f := identName segs[0]!.name
      unless args.size == ft.params.size do err span (Fren.Core.arityMsg f ft.params.size args.size)
      let mut smts := #[]
      for a in args, t in ft.params, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
        liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{f}` has type `{t.show}`"))
        smts := smts.push x
      return (s!"({sym} {" ".intercalate smts.toList})", ft.result)
  if segs.size == 1 then
    if let some c := Fren.Core.builtinFunction? (identName segs[0]!.name) then
      -- The number of its arguments that are `true`, compared with 1: a
      -- linear sum (`lang::cardinality`).
      if args.isEmpty then err span (Fren.Core.cardinalityNoArgsMsg c)
      let mut ites := #[]
      for a in args, k in [0:args.size] do
        -- `{}` and `[]` are never `Bool`s.
        if a matches .set _ #[] | .seq _ #[] then
          err a.span (Fren.Core.cardinalityArgMsg c (k + 1) (if a matches .set .. then "{}" else "[]"))
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.countArgument.expected none none } a
        unless ta == .bool do err a.span (Fren.Core.cardinalityArgMsg c (k + 1) ta.show)
        ites := ites.push s!"(ite {x} 1 0)"
      let count := if ites.size == 1 then ites[0]! else s!"(+ {" ".intercalate ites.toList})"
      return (s!"({c.smtOp} {count} 1)", .bool)
  -- In its own contract, the function is applied to its parameters, in a
  -- postcondition (`lang::contract_application`); it is not yet in scope.
  let own? := cx.contract?.filter fun (f, _, _) => segs.size == 1 && Name.mkSimple segs[0]!.name == Name.mkSimple f.getString!
  if let some (f, post, params) := own? then
    -- Each argument as written: a name of one segment, not hidden by a
    -- binder, or another expression.
    let written := args.map fun
      | .path _ #[s] => if (cx.binder? (identName s.name)).isNone then some (identName s.name) else none
      | _ => none
    let toParams := Fren.Core.appliesToParams written params
    unless Fren.Core.contractApplicationAccepted (if post then .postcondition else .precondition) true toParams do
      err fnSpan (Fren.Core.contractSelfMsg f !post)
  -- A variable shadows a function, as it does any other item.
  let module := (← get).module
  let resolved ← match own? with
    | some (f, _, _) => pure (.item { kind := .fnItem, path := f, isPub := true, owner := module })
    | none => resolveWritten segs cx.shadowing cx.noteIndexes
  noteResolved "name" fnSpan fun _ => resolvedPath resolved.path
  let path ← match resolved with
    | .item { kind := .fnItem, path, .. } =>
      unless cx.unmentioned do noteItemCore path
      if let some h := (← get).hofs.find? path then
        return ← elabHigherOrderApp cx expected? span fnSpan path h args
      pure path
    | .variant en idx =>
      -- A variant with a payload, built from its values.
      let v := en.variants[idx]!
      let some d := (← get).dataOf? en.path | internal fnSpan s!"unknown enum `{en.path}`"
      let tys := d.ctors[idx]!.2.map (·.2)
      if let some msg := Fren.Core.variantMentionMsg? (en.path ++ v) tys.size true then err span msg
      unless args.size == tys.size do err span (Fren.Core.arityMsg (en.path ++ v) tys.size args.size "value")
      let note (k : Nat) (t : Ty) := s!"note: value {k + 1} of the payload of `{showPath (en.path ++ v)}` has type `{t.show}`"
      if !d.params.isEmpty then
        let (smts, targs) ← elabConstruction elabExpr .payload { cx with expected? } d tys args span (showPath (en.path ++ v)) note
        -- Each value's obligation, of its type with the enumeration's arguments.
        for a in args, x in smts, k in [0:args.size] do
          noteObligation cx .payload a.span (← partPTy en.path idx k targs) x
        return (d.build targs.toList v smts.toList, .enum en.path targs.toList)
      let mut smts := #[]
      for a in args, t in tys, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.payload.expected (some t) none } a
        liftMsg a.span (Fren.Core.checkType t ta (some (note k t)))
        noteObligation cx .payload a.span (← partPTy en.path idx k) x
        smts := smts.push x
      return (s!"({ctorSym en.path v} {" ".intercalate smts.toList})", .enum en.path [])
    | .item { kind := .recordItem, path, .. } =>
      -- A newtype, built from its value, which is erased
      -- (`Reqs/Lang/Expressions#newtypes`).
      let some u := (← get).newtypes.find? path | err fnSpan (Fren.Core.constructionMsg path false)
      unless args.size == 1 do err span (Fren.Core.arityMsg path 1 args.size "value")
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.newtypeValue.expected (some u) none } args[0]!
      unless ta.widens u do mismatch args[0]! u ta (some s!"note: the value of `{showPath path}` has type `{u.show}`")
      if cx.noteIndexes then
        let synth ← synthesizes cx args[0]!
        modify fun s => { s with facts := s.facts.push (span, .wraps path.toString synth) }
      noteObligation cx .construction args[0]!.span (← partPTy path 0 0) x
      return (x, .newtype path u)
    | r => err fnSpan (Fren.Core.notAFunctionMsg r)
  -- A variable, written as its name, that is the argument at the
  -- decreasing parameter of a structural recursion
  -- (`lang::induction_candidate`).
  let writtenArgs := args.map fun
    | .path _ #[s] => some (identName s.name)
    | _ => none
  if let some x := Fren.Core.inductionArgument? ((← get).recursiveDecreasing.get? path)
      writtenArgs (cx.vars.map (·.name)) (fun x => (cx.binder? x).isSome) then
    modify fun st => { st with inductionArgs := st.inductionArgs.push x }
  if let some g := (← get).genericFns.find? path then
    -- A generic function, at the instance whose type arguments are inferred
    -- (`Reqs/Lang/GenericFunctions#applications`); its arguments may
    -- mention anything (`lang::argument`).
    -- One without a body is uninterpreted, at each instance
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`): a
    -- defined function's body applies none (`lang::function_body`), and
    -- outputs may not occur in its arguments (`inst::mention`).
    if !g.defined then
      if cx.selfFn.isSome then err fnSpan (Fren.Core.appliesUninterpretedMsg path)
      modify fun s => { s with applied := s.applied.push span }
    let acx := if !g.defined && cx.place == .prop then { cx with place := .argument } else cx
    unless args.size == g.declared.size do err span (Fren.Core.arityMsg path g.declared.size args.size)
    let synth ← args.mapM (synthesizes cx)
    let go : StateT (Array String) M (Array Ty) :=
      Fren.Core.inferCall g.params g.declared g.result synth expected?
        (err span (Fren.Core.cannotInferCallMsg (showPath path)) : M Unit)
        (fun k x? => do
          let (smt, t) ← (elabExpr { acx with expected? := Fren.Core.ExprSite.functionArgument.expected x? none } args[k]! : M _)
          modify fun a => a.set! k smt
          return some t)
        (fun k x f => (liftMsg args[k]!.span
          (Fren.Core.checkType x f (some s!"note: argument {k + 1} of `{showPath path}` has type `{x.show}`")) : M Unit))
    let (targs, smts) ← go.run (args.map fun _ => "")
    -- A function of sets of a type that may be finite, at its instance
    -- (`Reqs/Lang/Decidability#sets`).
    if !g.defined then
      let st ← get
      let finiteSet (t : Ty) : Bool := t matches .set _ | .rel .. && !st.infinite t
      let (ps, r) := Fren.Core.instanceSig g.declared g.result targs
      if (ps.push r).any finiteSet then
        checkCore cx span .setFunction true true #[] (infiniteElems := false)
    let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
    for a in args, x in smts, k in [0:args.size] do
      noteObligation acx .argument a.span (ptys[k]?.getD default) x
    let sym ← instantiate path targs
    modify fun s => { s with genericCalls := s.genericCalls.push (path, targs)
                             callTargs := if s.module == Fren.Core.preludeModule then s.callTargs
                               else s.callTargs.insert (s.file, span.start) targs
                             genericUses := s.genericUses.push
                               { file := s.file, item := s.item, caller? := s.fnTypeParams.map (·.1), callee := path, targs } }
    notePreconditions cx fnSpan path smts targs
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    let app := s!"({sym} {" ".intercalate smts.toList})"
    -- At least 0, if a `Nat`, its type's constraint, if it brings one, and
    -- meeting its postconditions where its arguments meet its
    -- preconditions, at its instance (`lang::uninterpreted_instance`).
    if !g.defined then
      let posts := (((← get).contracts.find? path).map (·.posts)).getD #[]
      if Fren.Core.instanceNat g.result || !posts.isEmpty || (← get).funFacts.contains sym then
        modify fun s => { s with natApps := s.natApps.push app }
    return (app, Fren.Core.callType g.result targs)
  if let some (_, params, result, _) := (← get).defs.find? (·.1 == path) then
    -- Its arguments may mention anything (`lang::argument`).
    unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
    let mut smts := #[]
    let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
    for a in args, (_, t) in params, k in [0:args.size] do
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
      liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`"))
      noteObligation cx .argument a.span (ptys[k]?.getD default) x
      smts := smts.push x
    notePreconditions cx fnSpan path smts
    -- Its body's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    return (s!"({itemSym path} {" ".intercalate smts.toList})", result)
  if cx.inClosure then err fnSpan (Fren.Core.closureUninterpretedMsg path)
  if cx.selfFn.isSome then err fnSpan (Fren.Core.appliesUninterpretedMsg path)
  modify fun s => { s with applied := s.applied.push span }
  let some (_, params, result) := (← get).funs.find? (·.1 == path) | internal fnSpan s!"unknown function `{path}`"
  -- A function of sets of a type that may be finite (`Reqs/Lang/Decidability#sets`).
  let st ← get
  let finiteSet (t : Ty) : Bool := t matches .set _ | .rel .. && !st.infinite t
  if (params.push result).any finiteSet then
    checkCore cx span .setFunction true true #[] (infiniteElems := false)
  unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
  -- Outputs may not occur in arguments (`inst::mention`); assumptions and
  -- bindings exclude them already.
  let acx := if cx.place == .prop then { cx with place := .argument } else cx
  let mut smts := #[]
  let ptys := (← get).funPTys.find? path
  for a in args, t in params, k in [0:args.size] do
    let (x, ta) ← elabExpr { acx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
    liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`"))
    noteObligation acx .argument a.span ((ptys.bind (·.1[k]?)).getD default) x
    smts := smts.push x
  notePreconditions cx fnSpan path smts
  let app := s!"({itemSym path} {" ".intercalate smts.toList})"
  -- At least 0, if a `Nat`, its type's constraint, if it brings one, and
  -- meeting its postconditions where its arguments meet its
  -- preconditions (`Reqs/Lang/Items#uninterpreted-functions`).
  let posts := (((← get).contracts.find? path).map (·.posts)).getD #[]
  if result == .nat || !posts.isEmpty || (← get).funFacts.contains (itemSym path) then
    modify fun s => { s with natApps := s.natApps.push app }
  return (app, result)

/-- A closure, or the name of a function, given for the function parameter
of type `ft`, as its function's signature declares it, of the higher-order
function `f`, whose parameters' types are `ps` where they are known and
whose result's is `r?` if it is known: the closure as the solver sees it,
its parameters' types and its body's (`Reqs/Lang/HigherOrder#arguments`).
The name of a function `g` is the closure `|x1, ..., xn| g(x1, ..., xn)`. -/
partial def elabFnArg (cx : ExprCtx) (f : String) (ft : Fren.Core.FnTy) (ps : Array (Option Ty)) (r? : Option Ty)
    (e : Expr) : M (ClosureArg × Array Ty × Ty) := do
  match e with
  | .matches span #[] arms false =>
    let some types := ps.mapM id | err span (Fren.Core.closureParamUnknownMsg f)
    let names := types.mapIdx fun j _ => ({ name := s!"#match{j}", span } : Ident)
    let values := names.map fun n => Expr.path span #[n]
    let body := if types.size == 1 then Expr.match span values[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) false
      else Expr.matches span values arms false
    for (patterns, _, _) in arms do
      unless patterns.size == types.size do err patterns[0]!.span (Fren.Core.arityMsg `match types.size patterns.size "pattern")
    elabClosure cx (names.zip types) body r? true
  | .closure span params body =>
    if let some msg := Fren.Core.argumentMsg? ft (.closure params.size) then err span msg
    -- `_` declares no name: one that no spec can write or mention.
    let params := params.mapIdx fun k (x, ty?) => if x.name == "_" then ({ x with name := s!"#_{k}" }, ty?) else (x, ty?)
    -- Distinct names (`lang::distinct_names`).
    let declared := params.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then err params[k]!.1.span (Fren.Core.dupBoundMsg declared[k]!)
    let named ← params.zip ps |>.mapM fun ((x, ty?), p?) => do
      -- Its written type is the function type's (`lang::function_argument`).
      let t ← match ty?, p? with
        | some segs, some p => do
          let a := (← elabPTy segs).ty
          unless a == p do err (typeSpan segs) (Fren.Core.typeMismatchMsg p a (some s!"note: this parameter of the closure for `{f}` has type `{p.show}`"))
          pure p
        | some segs, none => pure (← elabPTy segs).ty
        | none, some p => pure p
        | none, none => err x.span (Fren.Core.closureParamUnknownMsg f)
      return (x, t)
    lintClosure cx ps r? span params body
    elabClosure cx named body r? false
  | .path span segs =>
    -- The function itself, in its own body, not applied.
    if let some (ps, _, _) := cx.selfRec? then
      if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
        noteRecUse span ((← get).module ++ Name.mkSimple segs[0]!.name) ps { form := .passed }
    -- A function parameter, or a defined function, but not an
    -- uninterpreted one (`lang::function_argument`).
    let isParam := segs.size == 1 && (cx.fnParam? (identName segs[0]!.name)).isSome
    unless isParam do
      let st ← get
      match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
      | .ok (.item { kind := .fnItem, path, .. }) =>
        let shape := if st.defs.any (·.1 == path) || st.hofs.contains path then .definedName else .uninterpretedName
        if let some msg := Fren.Core.argumentMsg? ft shape path then err span msg
      | _ => err span ((Fren.Core.argumentMsg? ft .other).getD default)
    let some tys := ps.mapM id | err span (Fren.Core.closureParamUnknownMsg f)
    let xs := (List.range tys.size).toArray.map fun k => ({ name := s!"#{k}", span } : Ident)
    let call := Expr.app span segs (xs.map fun x => .path span #[x])
    elabClosure cx (xs.zip tys) call r? true
  | _ => err e.span ((Fren.Core.argumentMsg? ft .other).getD default)

/-- The closure whose parameters are `params`, of their types, and whose
body is `body`, of the type `r?` if it is known: its parameters are
declared as a quantifier's bound names are, but not where `synthetic`, as
those of a function's name are. Its body's indexes, tables and
applications with preconditions are its obligations, over its
parameters' symbols, which the application of the higher-order function
puts at each application of the function parameter (`lang::closure_obligation`). -/
partial def elabClosure (cx : ExprCtx) (params : Array (Ident × Ty)) (body : Expr) (r? : Option Ty) (synthetic : Bool) :
    M (ClosureArg × Array Ty × Ty) := do
  let n := (← get).nextClosure
  modify fun s => { s with nextClosure := s.nextClosure + 1 }
  let mut new : Array CBinder := #[]
  let mut free : Array FreeBound := #[]
  for (x, t) in params do
    -- `_`, which declares no name (`elabFnArg`), as a synthetic one.
    let bn ← if synthetic || x.name.startsWith "#_" then pure (Name.mkSimple x.name) else do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        ((cx.binders ++ new).map (·.what)) cx.selfFn.isSome
      let y ← declare x locals
      let bn := Name.mkSimple y.name
      liftMsg y.span (Fren.Core.checkVarName bn (some (t == .bool)))
      lintName .binder bn y.span
      pure bn
    let sym := quote (Fren.Core.closureSymbol bn.toString n)
    let st ← get
    free := free.push { sym, sort := t.sort, cons? := ((Fren.Core.PTy.plain t).cons st.shapeOf true).map (consSmt st.dataOf? · sym) }
    new := new.push { name := bn, smt := sym, ty := t, scrutinee := none, outer := cx.binders.size + new.size, unbounded := true }
  let outer ← takeIndexes
  let outerTables ← takeTables
  let site : Fren.Core.ExprSite := if r?.isSome then .typedClosureBody else .untypedClosureBody
  let (b, tb) ← elabExpr { cx with binders := cx.binders ++ new, expected? := site.expected r? none, inClosure := true } body
  let inner ← takeIndexes
  let innerTables ← takeTables
  modify fun s => { s with indexes := outer, tables := outerTables }
  let _ := free
  return ({ closure := { params := new.toList.map (·.smt), body := Fren.Core.STerm.parse b }, indexes := inner
            tables := innerTables }, new.map (·.ty), tb)

/-- `elabExpr` on an application of the higher-order function `h` at
`path` (`Reqs/Lang/HigherOrder#applications`): its body, unfolded at its
arguments, each closure unfolded within it (`Fren.Core.inlineCall`), and
its preconditions so too. -/
partial def elabHigherOrderApp (cx : ExprCtx) (expected? : Option Ty) (span fnSpan : Span) (path : Name)
    (h : HigherOrderFn) (args : Array Expr) : M (String × Ty) := do
  unless args.size == h.params.size do err span (Fren.Core.arityMsg path h.params.size args.size)
  let synth ← args.mapM (synthesizes cx)
  let f := showPath path
  let go : StateT (Array String × Array (Option ClosureArg)) M (Array Ty) :=
    Fren.Core.inferHigherOrder h.typeParams (h.params.map (·.2.2)) h.result synth expected?
      (err span (Fren.Core.cannotInferCallMsg f) : M Unit)
      (fun k x? => do
        let (smt, t) ← (elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected x? none } args[k]! : M _)
        modify fun (a, c) => (a.set! k smt, c)
        return some t)
      (fun k x t => (liftMsg args[k]!.span
        (Fren.Core.checkType x t (some s!"note: argument {k + 1} of `{f}` has type `{x.show}`")) : M Unit))
      (fun k ps r? => do
        let .function ft := h.params[k]!.2.2 | return none
        let (c, pts, rt) ← (elabFnArg cx f ft ps r? args[k]! : M _)
        noteFnArg path k args[k]!
        modify fun (a, cs) => (a, cs.set! k (some c))
        return some (pts, rt))
      (fun k ft (_, rt) => (liftMsg args[k]!.span
        (Fren.Core.checkType ft.result rt (some s!"note: the closure for argument {k + 1} of `{f}` returns `{ft.result.show}`")) : M Unit))
  let (targs, smts, closures) ← do
    let (targs, (smts, closures)) ← go.run (args.map fun _ => "", args.map fun _ => none)
    pure (targs, smts, closures)
  -- Its type arguments, for the evaluator's lowering (`State.callTargs`).
  unless h.typeParams.isEmpty || (← get).module == Fren.Core.preludeModule do
    modify fun s => { s with callTargs := s.callTargs.insert (s.file, span.start) targs }
  let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
  for a in args, x in smts, k in [0:args.size] do
    if h.params[k]!.2.2 matches .value _ then noteObligation cx .argument a.span (ptys[k]?.getD default) x
  let values := (h.params.zip smts).toList.filterMap fun ((_, sym, p), x) => if p matches .value _ then some (sym, x) else none
  let fns := (h.params.zip closures).toList.filterMap fun ((_, sym, _), c?) => c?.map (sym, ·.closure)
  let globals ← globalSyms
  let isLocal (s : String) : Bool := (s.startsWith "|" || s.startsWith "let@") && !globals.contains s
  -- Its preconditions, at the arguments, with the closures unfolded.
  if cx.noteIndexes then
    let mut pres := #[]
    for (pn, text) in h.pres do
      let (pre, next) := Fren.Core.inlineCall (← hofText path h targs text) values fns isLocal (← get).nextCapture
      modify fun s => { s with nextCapture := next }
      pres := pres.push (pn, pre)
    for (q, goal) in Fren.Core.preconditionQuestions (guarded cx.guards) path pres do
      modify fun s => { s with tables := s.tables.push (fnSpan, q, goal) }
  let body ← hofText path h targs h.body
  -- Each closure's obligations, at each application of its function
  -- parameter in the body, with the other closures unfolded there
  -- (`lang::closure_obligation`).
  if cx.noteIndexes then
    for (fsym, c?) in (h.params.map (·.2.1)).zip closures do
      let some c := c? | continue
      let others := fns.filter (·.1 != fsym)
      let at_ (g : String) : M (Option String) := do
        let (b, next) := Fren.Core.inlineCall body [] others isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        -- Its free names, as the closure's, are captured outside the body.
        let (g', lets, next) := Fren.Core.captureFree (Fren.Core.STerm.parse g) c.closure.params isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        -- Where the body never applies it, the closure is never evaluated.
        let o := (Fren.Core.closureObligation (Fren.Core.STerm.parse b) fsym c.closure.params g').getD (.atom "true")
        -- With the closure unfolded where the arguments and the guards
        -- apply it too, and the other parameters at their arguments.
        let (t, next) := Fren.Core.inlineCall o.print values [(fsym, c.closure)] isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        if lets.isEmpty then return some t
        return some s!"(let ({" ".intercalate (lets.map fun (x, v) => s!"({x} {v})")}) {t})"
      for (sp, g, t) in c.indexes do
        if let some o ← at_ g then modify fun s => { s with indexes := s.indexes.push (sp, o, t), vias := s.vias.push (sp, path) }
      for (sp, q, g) in c.tables do
        if let some o ← at_ g then modify fun s => { s with tables := s.tables.push (sp, q, o), vias := s.vias.push (sp, path) }
  let (smt, next) := Fren.Core.inlineCall body values fns isLocal (← get).nextCapture
  modify fun s => { s with nextCapture := next }
  if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
  return (smt, h.result.subst targs)

/-- `elabExpr` on a field read. -/
partial def elabFieldExpr (cx : ExprCtx) (e : Expr) (parent? : Option Expr) (span : Span) (a : Expr) (f : Ident) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  lintChain
  let (x, t) ← elabExpr { cx with concatOk := true } a
  if t == .string then checkCore cx span .stringAtom true true #[a]
  if let some tys := relRange? t f.name then checkRelational cx span tys #[a]
  checkRelationalCard cx span t f.name a
  if let (.seq _, some m) := (t, Fren.Core.Method.ofName? f.name) then
    checkCore cx span m.seqConstruct true true #[a] (← isConstant cx a)
  -- For `redundant_newtype_roundtrip`, at its span as written, as the
  -- lints see it (`Expr.boolNode`).
  if let (.newtype p _, "0", true) := (t, f.name, cx.noteIndexes) then
    modify fun s => { s with facts := s.facts.push (e.writtenSpan s.src, .unwraps p.toString) }
  readField f.span x t (Name.mkSimple f.name)

/-- `elabExpr` on a record literal. -/
partial def elabRecordExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (tySegs : Array Ident) (fields : Array (Ident × Option Expr)) : M (String × Ty) := do
  let src := (← get).src
  let tySpan := tySegs[0]!.span.to tySegs.back!.span
  let path ← match ← resolveWritten tySegs cx.shadowing cx.noteIndexes with
    | .item { kind := .recordItem, path, .. } => pure path
    | r => err tySpan (Fren.Core.wrongKindMsg "a record" r)
  if (← get).newtypes.contains path then err tySpan (Fren.Core.constructionMsg path true)
  let some d := (← get).dataOf? path | internal tySpan s!"unknown record `{path}`"
  let fs := d.ctors[0]!.2
  match Fren.Core.checkFieldInits path (fs.map (·.1)) (fields.map (Name.mkSimple ·.1.name)) with
  | .ok () => pure ()
  | .error (some i, msg) => err fields[i]!.1.span msg
  | .error (none, msg) => err span msg
  -- `inconsistent_struct_constructor` (`lint::inconsistent_struct_constructor`).
  if cx.noteIndexes then
    let src := (← get).src
    let ranges := fields.map fun (f, e?) =>
      ({ start := f.span.start, stop := (e?.map fun e => (Fren.Core.withParens src (toRange e.span)).stop).getD f.span.stop } : Fren.Core.Range)
    if let some fixed? := Fren.Core.reorderedFields? src (toRange span) ranges (fields.map (Name.mkSimple ·.1.name)) (fs.map (·.1)) then
      lintFix .inconsistentStructConstructor span
        (Fren.Core.inconsistentStructConstructorMsg (Name.mkSimple path.getString!) (fs.map (·.1)) fixed?)
  let mut smts := #[]
  let mut vals := #[]
  for (f, _) in fs do
    let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f) | internal span s!"no field `{f}`"
    noteResolved "name" fi.span fun _ => resolvedPath (path ++ f)
    if let (some e, true) := (e?, cx.noteIndexes) then lintRedundant fi e true
    vals := vals.push (e?.getD (.path fi.span #[fi]))
  let note (k : Nat) (t : Ty) := s!"note: `{fs[k]!.1}` of `{showPath path}` has type `{t.show}`"
  let mut targs := #[]
  if d.params.isEmpty then
    for (_, t) in fs, e in vals, k in [0:fs.size] do
      let (x, te) ← elabExpr { cx with expected? := Fren.Core.ExprSite.recordField.expected (some t) none } e
      liftMsg e.span (Fren.Core.checkType t te (some (note k t)))
      noteObligation cx .field e.span (← partPTy path 0 k) x
      smts := smts.push x
  else
    (smts, targs) ← elabConstruction elabExpr .recordField { cx with expected? } d (fs.map (·.2)) vals span (showPath path) note
    -- Each field's obligation, of its type with the record's arguments.
    for e in vals, x in smts, k in [0:fs.size] do
      noteObligation cx .field e.span (← partPTy path 0 k targs) x
  -- `unnecessary_struct_initialization`
  -- (`lint::unnecessary_struct_initialization`): each field's value as
  -- `r.f`, its own field `f` of `r`, with `r`'s text.
  if cx.noteIndexes then
    let src := (← get).src
    let reads := fields.filterMap fun (f, e?) => do
      match ← e? with
      | .path sp #[seg] =>
        let parts := seg.name.splitOn "."
        guard (parts.length ≥ 2 && parts.getLast! == f.name)
        let r := ".".intercalate parts.dropLast
        some (Expr.path { sp with stop := sp.start + r.length } #[{ name := r, span := { sp with stop := sp.start + r.length } }], r)
      | .field _ r g =>
        guard (g.name == f.name)
        some (r, Fren.Core.textOf src (Fren.Core.withParens src (toRange (r.writtenSpan src))))
      | _ => none
    if let some (r, t) := reads[0]? then
      let same := reads.all (Fren.Core.writtenSame ·.2 t)
      -- A value has a type; a call is not one.
      let ty? := match (elabExpr { cx with noteIndexes := false } r).run (← get) with
        | .ok ((_, ty), _) => some ty
        | .error _ => none
      if Fren.Core.unnecessaryStructInit fields.size (reads.size == fields.size) same ty?.isSome (ty? == some (.record path targs.toList)) then
        lintFix .unnecessaryStructInitialization span (Fren.Core.unnecessaryStructInitMsg t)
  if cx.noteIndexes then
    -- `manual_record_update` (`lint::manual_record_update`): the fields that
    -- read their own field from a value of this record, by the value's text.
    let mut copies : Array (String × Span × Array Nat) := #[]
    for h : i in [0:fields.size] do
      let (fi, e?) := fields[i]
      let some (recv, n) := e?.bind lastName? | continue
      unless n == fi.name do continue
      -- Only its type: what elaborating it reports is reported where it is.
      let saved ← get
      let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, expected? := Fren.Core.ExprSite.receiver.expected none none } recv)
        fun _ => pure none
      set saved
      unless t? == some (Ty.record path targs.toList) do continue
      let w := Fren.Core.writtenForm (← srcAt recv.span)
      match copies.findIdx? (·.1 == w) with
      | some k => copies := copies.modify k fun (w, s, ks) => (w, s, ks.push i)
      | none => copies := copies.push (w, recv.span, #[i])
    -- The value with the most copies, the first of those with as many.
    let best? := copies.foldl (init := none) fun acc c =>
      if acc.all (·.2.2.size < c.2.2.size) then some c else acc
    if let some (_, rs, ks) := best? then
      if Fren.Core.manualRecordUpdate fs.size ks.size then
        let kept ← ((Array.range fields.size).filter (!ks.contains ·)).mapM fun i =>
          let (fi, e?) := fields[i]!
          srcAt ((e?.map (fi.span.to ·.span)).getD fi.span)
        lintFix .manualRecordUpdate span (Fren.Core.manualRecordUpdateMsg (← srcAt rs) ks.size kept)
  return (d.build targs.toList `«{}» smts.toList, .record path targs.toList)

/-- `elabExpr` on a record update. -/
partial def elabUpdateExpr (cx : ExprCtx) (span : Span) (base : Expr) (fields : Array (Ident × Option Expr)) : M (String × Ty) := do
  let (rv, tr) ← elabExpr { cx with expected? := Fren.Core.ExprSite.updatedRecord.expected none none } base
  let .record path targs := tr | err base.span (Fren.Core.updateBaseMsg tr.show)
  let some d := (← get).dataOf? path | internal base.span s!"unknown record `{path}`"
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let fs := (d.instCtors targs)[0]!.2
  match Fren.Core.checkFieldUpdates path (fs.map (·.1)) (fields.map (Name.mkSimple ·.1.name)) with
  | .ok () => pure ()
  | .error (i, msg) => err fields[i]!.1.span msg
  -- The record literal whose other fields are read from `r`, bound once,
  -- so that nested updates grow linearly. No variable's name has `@`.
  let bind := fs.size > fields.size && rv.contains ' '
  let r := if bind then quote s!"update@{span.start}" else rv
  let mut smts := #[]
  for (f, t) in fs, k in [0:fs.size] do
    let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f)
      | smts := smts.push s!"({fieldSym path f} {r})"; continue
    noteResolved "name" fi.span fun _ => resolvedPath (path ++ f)
    let e := e?.getD (.path fi.span #[fi])
    let (x, te) ← elabExpr { cx with expected? := Fren.Core.ExprSite.recordField.expected (some t) none } e
    liftMsg e.span (Fren.Core.checkType t te (some s!"note: `{f}` of `{showPath path}` has type `{t.show}`"))
    noteObligation cx .field e.span (← partPTy path 0 k targs.toArray) x
    smts := smts.push x
  if cx.noteIndexes then
    if Fren.Core.needlessUpdate fs.size fields.size then
      lint .needlessUpdate span (Fren.Core.needlessUpdateMsg (showPath path) (← srcAt base.span))
    -- `redundant_bindings` on each field (`lint::redundant_bindings`, `lint::field_copy`).
    let baseText := Fren.Core.writtenForm (← srcAt base.span)
    let values ← fields.mapM fun (_, e?) => e?.mapM fun e => do pure (Fren.Core.writtenForm (← srcAt e.span))
    let copy (i : Nat) : Bool := Fren.Core.fieldCopy fields[i]!.1.name ((values[i]!).getD "") baseText true
    let others := (Array.range fields.size).any (!copy ·)
    let stop (i : Nat) : Nat := let (fi, e?) := fields[i]!; ((e?.map (·.span.stop)).getD fi.span.stop)
    for h : i in [0:fields.size] do
      let (fi, e?) := fields[i]
      let some e := e? | continue
      lintRedundant fi e true
      if Fren.Core.fieldCopy fi.name ((values[i]!).getD "") baseText others then
        -- The field and the comma before it, or for the first, the comma after it.
        let r : Fren.Core.Range := if i == 0 then { start := fi.span.start, stop := fields[1]!.1.span.start }
          else { start := stop (i - 1), stop := e.span.stop }
        lintEdits .redundantBindings (fi.span.to e.span) (Fren.Core.fieldCopyMsg fi.name (← srcAt base.span)) #[(r, "")]
  let lit := d.build targs `«{}» smts.toList
  return (if bind then s!"(let (({r} {rv})) {lit})" else lit, .record path targs)

/-- `elabExpr` on a `match`. -/
partial def elabMatchExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span) (scrutinee : Expr) (arms : Array (Pattern × Option Expr × Expr)) (isTable : Bool)
    (many? : Option (Array Expr × Array (Array Pattern)) := none) : M (String × Ty) := do
  let scrutinees := many?.map (·.1) |>.getD #[scrutinee]
  let patterns := many?.map (·.2) |>.getD (arms.map fun a => #[a.1])
  for ps in patterns, arm in arms do
    unless ps.size == scrutinees.size do err arm.1.span (Fren.Core.arityMsg `match scrutinees.size ps.size "pattern")
  let origin? := scrutinees.findSome? cx.recOrigin?
  let values ← scrutinees.mapM (elabExpr cx)
  for scr in scrutinees, (_, ts) in values do
    unless ts matches .enum .. | .bool | .int | .nat | .string do err scr.span (Fren.Core.scrutineeMsg ts.show)
  let ts := values[0]!.2
  let mut resolved := #[]
  let mut rows := #[]
  for ps in patterns do
    let parts ← ps.zipIdx |>.mapM fun (p, j) => do
      let (q, bs, test) ← resolvePattern cx values[j]!.2 values[j]!.1 false false p
      return (q, bs.map fun b => { b with source? := some scrutinees[j]! }, test)
    rows := rows.push (parts.map (·.1))
    resolved := resolved.push (parts[0]!.1, parts.flatMap (·.2.1), Fren.Core.allOf? andSmt (parts.filterMap (·.2.2)))
  let baseSigs ← patSigs
  let (sigs, pty, pats) := if many?.isSome then Fren.Core.matchVector baseSigs (values.map (·.2.patTy)) rows
    else (baseSigs, ts.patTy, rows.map (·[0]!))
  let usesBefore := (← get).recUses.size
  let guarded := arms.map (·.2.1.isSome)
  -- In a table over a scrutinee, only the last arm may be `_` without a
  -- guard, the otherwise (`Reqs/Lang/Expressions#tables-over-a-scrutinee`).
  if isTable then
    if let some k := Fren.Core.rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g) then
      err arms[k]!.1.span Fren.Core.armAfterWildMsg
  let checked := if isTable then Fren.Core.checkTableArms sigs pty pats guarded
    else (Fren.Core.checkMatch sigs pty pats guarded).map (·, #[])
  let (unguardedExhaustive, pairs) ← match checked with
    | .ok u => pure u
    | .error (some (i, some j), msg) => err (patterns[i]!.flatMap Pattern.alternatives)[j]!.span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
    | .error (some (i, none), msg) => err arms[i]!.1.span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
    | .error (none, msg) => err span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
  let implicitArg := match scrutinee with | .path _ #[n] => n.name.startsWith "#match" | _ => false
  if cx.noteIndexes then
    -- A lambda match writes no scrutinees; its generated parameters have
    -- no source texts to compare.
    let texts ← if implicitArg then pure #[] else scrutinees.mapM (srcAt ·.span)
    for (j, i, row?) in Fren.Core.duplicateScrutinees texts baseSigs (values.map (·.2.patTy)) rows do
      lint .duplicateScrutinee scrutinees[j]!.span (Fren.Core.duplicateScrutineeMsg i row?)
  if cx.noteIndexes && many?.isNone && !implicitArg then
    lintMatch cx e ts pats (parent?.bind (Expr.operandSlot (← get).src · e))
    lintCouldBeTable e sigs pty pats
    lintGuards cx e sigs pty pats
    lintArmIfElse cx e sigs pty pats
  let mut bodies : Array String := #[]
  let mut ty? : Option Ty := none
  let mut waiting : Array (Nat × ExprCtx × Expr) := #[]
  -- Where each arm is taken, if no earlier one is: its test and its
  -- guard; `none` for an arm taken wherever it is tried.
  let mut taken : Array (Option String) := #[]
  -- Of a table over a scrutinee, that the indexes in each arm's guard are
  -- in range where it evaluates them, if it has any.
  let mut defined : Array (Option String) := #[]
  -- An arm's guard is guarded by its pattern's matching where no earlier
  -- arm is taken (`Fren.Core.GuardedOperand.armGuard`), and its body by
  -- its being the first arm taken (`Fren.Core.GuardedOperand.armBody`).
  -- They are built directly: their negations are never needed, so
  -- `guard` would only return them.
  for (_, guard?, body) in arms, (_, bs, test) in resolved, j in [:arms.size] do
    -- The datatype already excludes distinct, unguarded constructor arms
    -- whose fields are only binders or wildcards. All other paths retain
    -- every earlier exclusion, including tables and match vectors.
    let earlier := (arms.extract 0 j).mapIdx fun i arm => (pats[i]!, arm.2.1)
    let exclusions := if !isTable && many?.isNone && omitMatchExclusions ts.patTy pats[j]! guard? earlier then #[]
      else taken.filterMap (·.map (s!"(not {·})"))
    let before := cx.guards ++ exclusions
    let armGuards := before ++ test.toArray
    -- Distinct names (`lang::distinct_names`), by the names they declare,
    -- without the `!` of shadowing.
    let declared := bs.map fun b => Name.mkSimple (declaredIdent b.ident).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then
      err bs[k]!.ident.span (Fren.Core.dupPatternBinderMsg declared[k]!)
    let mut new : Array CBinder := #[]
    for b in bs do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let x ← declare b.ident locals
      let bn := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkVarName bn (some (b.ty == .bool)))
      lintName .binder bn x.span
      -- A payload of a parameter, or of a binder bound from one, is bound
      -- from a payload of that parameter; so is the whole of such a binder.
      let source := b.source?.getD scrutinee
      let payloadOf? := cx.recOrigin? source |>.bind fun (j, p) => if b.payload || p then some j else none
      new := new.push { name := bn, smt := b.smt, ty := b.ty, scrutinee := some source, outer := cx.binders.size, payloadOf? }
    let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
    -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
    let guardOf (g : Expr) : M (String × Option String) := do
      if !isTable then
        let (x, tg) ← elabExpr { gcx with expected? := Fren.Core.ExprSite.armGuard.expected none none } g
        liftMsg g.span (Fren.Core.checkType .bool tg (some Fren.Core.armGuardNote))
        return (x, none)
      -- In a table over a scrutinee, elaborated under its pattern's test
      -- alone, so that its indexes say where it defines them, for its
      -- disjointness; then they, and the questions about its tables, are
      -- put under the earlier arms' not being taken, as a row's
      -- condition is.
      let (k, kt) := ((← get).indexes.size, (← get).tables.size)
      let (x, tg) ← elabExpr { gcx with expected? := Fren.Core.ExprSite.armGuard.expected none none, guards := test.toArray } g
      liftMsg g.span (Fren.Core.checkType .bool tg (some Fren.Core.armGuardNote))
      let inGuard := (← get).indexes.extract k
      modify fun s => { s with
        indexes := s.indexes.extract 0 k ++ inGuard.map (fun (sp, f, t) => (sp, FrenCli.guarded before f, t)),
        tables := s.tables.extract 0 kt ++ (s.tables.extract kt).map fun (sp, q, f) => (sp, q, FrenCli.guarded before f) }
      return (x, Fren.Core.allOf? andSmt (inGuard.map (·.2.1)))
    let (g?, d?) ← match guard? with
      | some g => do let (x, d?) ← guardOf g; pure (some x, d?)
      | none => pure (none, none)
    defined := defined.push d?
    let own := (test.toArray ++ g?.toArray)
    taken := taken.push (Fren.Core.allOf? andSmt own)
    -- Each body is checked against the whole's type, or another's
    -- (`lang::checked`): one that does not synthesize its own, before any
    -- other has given a type, waits for a later one that does.
    let bcx := { gcx with guards := armGuards ++ g?.toArray }
    -- Another arm's `Nat` is widened: a `Nat` is expected only of the whole.
    -- The whole's type comes before the arms' (`ExprSite.wholeFirst`).
    let shared? := Fren.Core.ExprSite.armBody.expected expected? ty?
    if shared?.isNone && !(← synthesizes cx body) && (← arms.anyM (synthesizes cx ·.2.2)) then
      waiting := waiting.push (bodies.size, bcx, body)
      bodies := bodies.push ""
      continue
    let (x, t) ← elabExpr { bcx with expected? := shared? } body
    ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
    bodies := bodies.push x
  for (k, bcx, body) in waiting do
    let (x, t) ← elabExpr { bcx with expected? := Fren.Core.ExprSite.armBody.expected expected? ty? } body
    if ty?.isSome then ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
    bodies := bodies.set! k x
  let ty := ty?.get!
  noteMatch cx span (arms.map (·.1.span)) taken guarded unguardedExhaustive (if isTable then some pairs else none) defined
  -- A recursive application under a `match` on an enumeration's parameter
  -- or payload that is not a Lean `match` (`lang::recursive_match`).
  if origin?.isSome && values.any (fun (_, t) => t matches .enum ..) then
    let nonLean? := if many?.isSome then (rows.zipIdx.find? fun (ps, j) => ps.any (!·.leanPattern) || guarded[j]!).map (·.2)
      else Fren.Core.firstNonLeanPattern? pats guarded
    if let some k := nonLean? then
      if (← get).recUses.size > usesBefore then
        modify fun s => { s with recMatches := s.recMatches.push arms[k]!.1.span }
  -- The first arm that is taken. Where the arms without guards are
  -- exhaustive, the last arm has none, and takes whatever is left;
  -- otherwise, where none is taken, the `match` is unspecified, as a
  -- table where no row holds is.
  let complete := !Fren.Core.completenessAsked unguardedExhaustive
  let mut out := if complete then bodies.back! else unspecified ty
  if !complete then modify fun s => { s with usesSeqs := true }
  for i in (List.range (if complete then bodies.size - 1 else bodies.size)).reverse do
    if let some t := taken[i]! then
      out := s!"(ite {t} {bodies[i]!} {out})"
    else
      out := bodies[i]!
  return (out, ty)

/-- `elabExpr` on a table. -/
partial def elabTableExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span)
    (rows : Array (Span × Option Expr × Expr)) : M (String × Ty) := do
  -- Only the last row may be `_` (`Reqs/Lang/Expressions#tables`).
  if let some k := Fren.Core.rowAfterWild? (rows.map (·.2.1.isNone)) then err rows[k]!.1 Fren.Core.rowAfterWildMsg
  let wild := rows.back!.2.1.isNone
  -- Each row's condition, other than `_`'s, and value.
  let mut conds : Array String := #[]
  let mut defined : Array (Option String) := #[]
  let mut values : Array String := #[]
  let mut ty? : Option Ty := none
  let mut waiting : Array (Nat × ExprCtx × Expr) := #[]
  for (_, c?, v) in rows do
    -- A row's condition is guarded by the earlier rows' not holding, and
    -- its value by its own holding too (`lang::guard`).
    let before := cx.guards ++ Fren.Core.earlierFail (s!"(not {·})") conds conds.size
    let mut own := #[]
    if let some c := c? then
      -- Elaborated under its own guards alone, so that its indexes say
      -- where it defines them; then they, and the questions about its
      -- tables, are put under the guards around it.
      let (k, kt) := ((← get).indexes.size, (← get).tables.size)
      let (x, tc) ← elabExpr { cx with guards := #[] } c
      liftMsg c.span (Fren.Core.checkType .bool tc (some Fren.Core.rowConditionNote))
      let inCond := (← get).indexes.extract k
      modify fun s => { s with
        indexes := s.indexes.extract 0 k ++ inCond.map (fun (sp, g, t) => (sp, guarded before g, t)),
        tables := s.tables.extract 0 kt ++ (s.tables.extract kt).map fun (sp, q, g) => (sp, q, guarded before g) }
      conds := conds.push x
      defined := defined.push (Fren.Core.allOf? andSmt (inCond.map (·.2.1)))
      own := #[x]
    -- Each value is checked against the whole's type, or another's
    -- (`lang::checked`), as a `match` arm's body is.
    let vcx := { cx with guards := before ++ own }
    let shared? := Fren.Core.ExprSite.rowValue.expected expected? ty?
    if shared?.isNone && !(← synthesizes cx v) && (← rows.anyM (synthesizes cx ·.2.2)) then
      waiting := waiting.push (values.size, vcx, v)
      values := values.push ""
      continue
    let (x, t) ← elabExpr { vcx with expected? := shared? } v
    if let some t0 := ty? then
      liftMsg v.span (Fren.Core.checkRowType t0 t)
    ty? := some ((ty?.map (·.join t)).getD t)
    values := values.push x
  for (k, vcx, v) in waiting do
    let (x, t) ← elabExpr { vcx with expected? := Fren.Core.ExprSite.rowValue.expected expected? ty? } v
    if let some t0 := ty? then
      liftMsg v.span (Fren.Core.checkRowType t0 t)
    ty? := ty?.map (·.join t)
    values := values.set! k x
  -- Each row's condition, or its `_`, which is last.
  noteTable cx span (rows.map fun (st, c?, _) => (c?.map (·.span)).getD st) conds defined wild
  -- `same_branches` on a table (`lint::same_rows`).
  if cx.noteIndexes then
    let src := (← get).src
    let v := rows[0]!.2.2
    let first := (v.text src).text
    let (fires, _) := Fren.Core.sameRows rows.size (rows.all fun r => Fren.Core.writtenSame (r.2.2.text src).text first) wild
    if fires then
      let fixed := (v.text src).inSlot (parent?.bind (Expr.operandSlot src · e)) (← followedSpan span)
      lintFix .sameBranches span (Fren.Core.sameRowsMsg first fixed wild)
  let ty := ty?.get!
  -- The first row whose condition holds; with no `_` row, where none
  -- does, the table is unspecified, as an index out of range is.
  let mut out := if wild then values.back! else
    s!"(ite {conds.back!} {values.back!} {unspecified ty})"
  if !wild then modify fun s => { s with usesSeqs := true }
  for i in (List.range (values.size - 1)).reverse do
    out := s!"(ite {conds[i]!} {values[i]!} {out})"
  return (out, ty)

/-- `elabExpr` on a pattern test `is`, an operand of a chain of `and` that
is a part of `test.1`, at the position and of the size that `test.2` gives,
if it is a chain of more than one. -/
partial def elabIsExpr (cx : ExprCtx) (test : Fren.Core.TestContext × Option (Nat × Nat)) (span : Span)
    (scrutinee : Expr) (p : Pattern) : M (String × Ty) := do
  let (s, ts) ← elabExpr cx scrutinee
  unless ts matches .enum .. | .bool | .int | .nat | .string do
    let shorthand := match scrutinee with
      | .path _ #[b] => b.name == Fren.Core.shorthandBinder
      | _ => false
    err scrutinee.span (Fren.Core.isScrutineeMsg ts.show shorthand)
  -- Whether the names that it binds are in scope anywhere (`lang::test_scope`):
  -- then its or-patterns bind none, as a `match` arm's do.
  let (context, at?) := test
  let (k, n) := at?.getD (0, 1)
  let binds := Fren.Core.testBinds context k n
  let (q, bs, smt) ← resolvePattern cx ts s false (!binds) p
  match Fren.Core.checkPatternTest (← patSigs) ts.patTy q (bs.map (Name.mkSimple ·.ident.name)) binds context with
  | .ok () => pure ()
  | .error (.binder k, msg) => err bs[k]!.ident.span msg
  | .error (.alternative j, msg) => err p.alternatives[j]!.span msg
  | .error (.whole, msg) => err p.span msg
  if cx.noteIndexes && !bs.isEmpty then modify fun s => { s with bindingTests := s.bindingTests.push span }
  if binds && !bs.isEmpty then
    -- Declared as a `match` arm's binders are, for the later operands of the
    -- chain and the body that sees them.
    let declared := bs.map fun b => Name.mkSimple (declaredIdent b.ident).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then
      err bs[k]!.ident.span (Fren.Core.dupPatternBinderMsg declared[k]!)
    let mut new : Array CBinder := #[]
    for b in bs do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let x ← declare b.ident locals
      let bn := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkVarName bn (some (b.ty == .bool)))
      if cx.noteIndexes then lintName .binder bn x.span
      new := new.push { name := bn, smt := b.smt, ty := b.ty, scrutinee := some scrutinee, outer := cx.binders.size }
    modify fun s => { s with bound := s.bound ++ new }
  if cx.noteIndexes then
    -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`).
    let irrefutable := Fren.Core.irrefutableIsAt (← patSigs) ts.patTy q
    if irrefutable then lint .irrefutableIs span (Fren.Core.irrefutableIsMsg ts.show (q matches .wild _))
    lintOrPatterns (patNode (← get).src p q)
    let texts ← p.alts.mapM (srcAt ·.span)
    -- Not of the pattern shorthand's test, whose scrutinee is not written,
    -- and which has no form with `=` (`Reqs/Lang/SubsetTypes#the-pattern-shorthand`).
    let generated := match scrutinee with | .path _ #[x] => Fren.Core.generatedName x.name | _ => false
    if !generated && Fren.Core.isEquality texts.size (Fren.Core.equatable q texts) irrefutable then
      lintFix .isEquality span (Fren.Core.isEqualityMsg (scrutinee.text (← get).src) texts[0]!)
  return (smt.getD "true", .bool)

/-- `elabExpr` on a `let` or `where`. -/
partial def elabLetExpr (cx : ExprCtx) (span : Span) (concatOk : Bool) (expected? : Option Ty) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool) : M (String × Ty) := do
  let appMark := (← get).natApps.size
  let (bcx, binds) ← elabDefinitions cx defs (!isWhere) (usedDefinitions defs body)
  let mark := (← get).indexes.size
  let tableMark := (← get).tables.size
  -- A body that is a membership right after the `in` may have been meant
  -- as part of the last definition, which `in` ended.
  let lastStop := (defs.back?.map (·.2.2.span.stop)).getD body.span.start
  let between := ((Fren.Core.withoutComments (← srcAt { start := lastStop, stop := body.span.start })).toList.filter
    fun c => !c.isWhitespace && c != ')')
  let membership := !isWhere && between == "in".toList && body matches .bin _ "in" ..
  let (b, t) ← tryCatch (elabExpr { bcx with expected? := Fren.Core.ExprSite.letBody.expected expected? none, concatOk } body) fun f =>
    -- The error just thrown is the last.
    throw (if membership then { f with diags := f.diags.modify (f.diags.size - 1) fun d =>
      { d with msg := Fren.Core.membershipNote true d.msg } } else f)
  -- The indexes of the body, and of the names it mentions, are within the
  -- `let`s.
  modify fun s => { s with
    indexes := s.indexes.extract 0 mark ++ (s.indexes.extract mark s.indexes.size).map fun (sp, g, t) => (sp, wrapLets binds g, t),
    tables := s.tables.extract 0 tableMark ++
      (s.tables.extract tableMark s.tables.size).map fun (sp, q, g) => (sp, q, wrapLets binds g) }
  -- So are the applications of `Nat` functions of its definitions and body,
  -- which are asserted to be at least 0 outside it.
  modify fun s => { s with natApps := s.natApps.extract 0 appMark ++
    (s.natApps.extract appMark s.natApps.size).map (wrapLets binds) }
  -- Not of what a function's block lowers to, whose definitions are
  -- written outside it (`Reqs/Lang/Items#function-blocks`).
  let lowered := defs.any fun (x, _, _) => x.span.start < span.start || x.span.stop > span.stop
  if cx.noteIndexes && !lowered then lintClause span defs body isWhere
  return (wrapLets binds b, t)

/-- Elaborates the definitions of a `let` (`inLet`) or `where` clause, in
order, each in the scope of the earlier ones (`Reqs/Lang/Let`), and those
that its body does not mention (`used`) without the rules on mentions: the
context of its body, and each name's SMT-LIB symbol and definition. -/
partial def elabDefinitions (cx : ExprCtx) (defs : Array (Ident × Option (Array Ident) × Expr)) (inLet : Bool)
    (used : Array Bool) : M (ExprCtx × Array (String × String)) := do
  let mut cx := cx
  let mut binds := #[]
  for (x, ty?, e) in defs, k in [0:defs.size] do
    let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
      (cx.binders.map (·.what)) cx.selfFn.isSome
    let y ← declare x locals
    let n := Name.mkSimple y.name
    -- This name and the later ones that hide nothing are not in scope yet.
    let pending := (defs.extract k defs.size).toList.zipIdx.filterMap fun ((z, _, _), j) =>
      let (d, bang) := declaredIdent z
      if bang then none else some (Name.mkSimple d.name, j == 0)
    let pannot? ← ty?.mapM elabPTy
    let annot? := pannot?.map (·.ty)
    -- Its indexes are guarded where the name is mentioned, and so is its
    -- written type's obligation (`Reqs/Lang/Let#definitions`).
    let before := (← get).indexes
    let beforeTables := (← get).tables
    modify fun s => { s with indexes := #[], tables := #[] }
    let site : Fren.Core.ExprSite := if annot?.isSome then .typedDefinition else .untypedDefinition
    let dcx := { cx with guards := #[], pending := pending.toArray, expected? := site.expected annot? none
                         unmentioned := cx.unmentioned || !used[k]! }
    let (smt, t) ← elabExpr dcx e
    if let some a := pannot? then noteObligation dcx .letDefinition e.span a smt
    let obligations := (← get).indexes
    let tableObligations := (← get).tables
    modify fun s => { s with indexes := before, tables := beforeTables }
    let last := inLet && k + 1 == defs.size
    -- A `Nat` widens to an `Int`, as anywhere an `Int` is expected.
    if let some a := annot? then
      unless a == t || (a == .int && t == .nat) do err e.span (Fren.Core.definitionTypeMsg n a.show t.show last)
    let t := annot?.getD t
    liftMsg y.span ((Fren.Core.checkVarName n (some (t == .bool))).mapError (Fren.Core.membershipNote last))
    if cx.noteIndexes then lintName .binder n y.span
    let sym := s!"let@{(← get).nLets}"
    modify fun s => { s with nLets := s.nLets + 1 }
    binds := binds.push (sym, smt)
    cx := { cx with binders := cx.binders.push { name := n, smt := sym, ty := t, scrutinee := e, outer := cx.binders.size,
                                                 isDef := true, obligations, tableObligations } }
  return (cx, binds)
end

/-- Reports `assertions_on_constants` on the constraint `e`, an `assume`,
`ensure` or `expect` as `kind` says (`lint::assertions_on_constants`). -/
def lintConstant (cx : ExprCtx) (kind : String) (e : Expr) : M Unit := do
  if Fren.Core.assertionOnConstant (← mentionedNames cx e) then
    lint .assertionsOnConstants e.span (Fren.Core.assertionOnConstantMsg kind (match e with | .bool _ b => some b | _ => none))

/-- Reports `assertions_on_constants` on the clause `e` of the contract of
the function `f`, a postcondition if `post`, if it mentions nothing, and
otherwise `contract_mentions_nothing` if it mentions nothing of `f`'s own
(`lint::contract_mentions_nothing`). -/
def lintContractClause (cx : ExprCtx) (post : Bool) (clause f : Name) (params : Array Name) (e : Expr) : M Unit := do
  let mentioned ← mentionedNames cx e
  if Fren.Core.assertionOnConstant mentioned then
    lint .assertionsOnConstants e.span (Fren.Core.assertionOnConstantMsg (if post then "postcondition" else "precondition")
      (match e with | .bool _ b => some b | _ => none))
  else if Fren.Core.contractMentionsNothing mentioned
      (f.toString (escape := false)) (params.toList.map (·.toString (escape := false))) then
    lint .contractMentionsNothing e.span (Fren.Core.contractMentionsNothingMsg post (clause.toString (escape := false)) (f.toString (escape := false)) mentioned)

/-- The conditions of a top-level `when`/`unless` chain, and their span. -/
partial def trigger? (cx : ExprCtx) : Expr → M (Option (String × Span))
  | .when span neg c d => do
    -- With the names that its pattern tests bind, which the body may see
    -- (`lang::test_scope`).
    let context : Fren.Core.TestContext := if neg then .unlessCondition else .whenCondition
    let ((cs, _), new) ← withBound (elabExpr { cx with noteIndexes := false, testContext := context } c)
    let cs := if neg then s!"(not {cs})" else cs
    let here : Span := { start := span.start, stop := c.span.stop }
    let seen := if Fren.Core.binderVisible context 0 1 .body then new else #[]
    match ← trigger? { cx with binders := cx.binders ++ seen } d with
    | none => return some (cs, here)
    | some (t, s) => return some (s!"(and {cs} {t})", here.to s)
  -- Through a `let` or `where`, whose names stand for their definitions.
  | .«let» _ defs body isWhere => do
    let saved ← get
    let (bcx, binds) ← elabDefinitions { cx with noteIndexes := false } defs (!isWhere) (usedDefinitions defs body)
    let t? ← trigger? bcx body
    set saved
    return t?.map fun (t, s) => (wrapLets binds t, s)
  | _ => return none

end FrenCli
