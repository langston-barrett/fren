-- keep-sorted start
import Fren.Elab.Comparisons
-- keep-sorted end

/-! # Hosted elaboration: sets -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
    -- Of the expected type, so that what is built from it, such as `{} inter
    -- {}` in a branch of a conditional, has its type before Lean unifies.
    match expected? with
    | some t@(.set _) | some t@(.rel ..) => return ← `((∅ : $(typeSyntax (← leanTypeOf t))))
    | _ => return ← `((∅ : Fren.FinSet _))
  checkCore cx e .setAlgebra true true elems
  if cx.noteIndexes then lintDuplicates e elems
  let synth ← elems.mapM (synthesizes cx)
  -- A member, given the type of the literal expected of it, as the `fren`
  -- command's `member`: a pair's members expect a relation's types. A member
  -- is never a `Nat` (`lang::nat_place`).
  let member (k : Nat) (lit? : Option Core.Ty) (noteIndexes := cx.noteIndexes) : TermElabM Term := do
    let x := elems[k]!
    let mcx := { cx with noteIndexes, emptyOk := Core.ExprSite.element.checked emptyOk ((synth.eraseIdx! k).any id) }
    if x.isOfKind ``Lang.pairExpr then
      let (ea?, eb?) := match lit? with | some (.rel a b) => (some a, some b) | _ => (none, none)
      let pcx := { mcx with emptyOk := Core.ExprSite.pairMember.checked mcx.emptyOk false }
      let (a, b) := (← widenTerm (← toTerm { pcx with expected? := ea? } x[1]), ← widenTerm (← toTerm { pcx with expected? := eb? } x[3]))
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
  xs ← xs.mapM fun value => `(Fren.evalElement $value)
  `(Fren.evalCollection ($(← finSetLit xs) : Fren.FinSet _))

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
    let x ← widenTerm (← pairOrTerm toTerm { cx with emptyOk := Core.ExprSite.membershipLeft.checked false false } a)
    -- The right expects a set or sequence of the left's type, as it is
    -- written, or a relation of a pair's, as in the `fren` command.
    let tx ← instantiateMVars (← typeOf x)
    let elem? ← if a.isOfKind ``Lang.pairExpr && tx.isAppOfArity ``Prod 2 then do
        let (some p, some q) := (← coreTy? tx.appFn!.appArg!, ← coreTy? tx.appArg!) | pure none
        pure (some (Core.Ty.rel p.widen q.widen))
      else pure ((← coreTy? tx).map fun t => if seqShaped b then .seq t.widen else .set t.widen)
    let s ← toTerm { cx with emptyOk := Core.ExprSite.membershipRight.checked false (← synthesizes cx a), expected? := Core.ExprSite.membershipRight.expected none elem? } b
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
  let site : Core.ExprSite :=
    if e.isOfKind ``Lang.joinExpr then .joinOperand
    else if e.isOfKind ``Lang.subsetExpr then .subsetOperand
    else .setOperand
  let cxa := { cx with emptyOk := site.checked cx.emptyOk (← synthesizes cx b) }
  let cxb := { cx with emptyOk := site.checked cx.emptyOk (← synthesizes cx a) }
  let (x, y) ← if e.isOfKind ``Lang.joinExpr then pure (← toTerm cxa a, ← toTerm cxb b)
    else
      -- The whole's expected type is not the operands' for `subset`.
      let expected? := if e.isOfKind ``Lang.subsetExpr then none else expected?
      pairTerms toTerm site { cxa with expected? } { cxb with expected? } a b
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


end Fren
