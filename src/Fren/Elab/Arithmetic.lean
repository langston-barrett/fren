-- keep-sorted start
import Fren.Elab.Mentions
-- keep-sorted end

/-! # Hosted elaboration: arithmetic -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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


end Fren
