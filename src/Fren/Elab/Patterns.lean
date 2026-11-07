-- keep-sorted start
import Fren.Elab.ExpressionLints
-- keep-sorted end

/-! # Hosted elaboration: patterns -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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


end Fren
