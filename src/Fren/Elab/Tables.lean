-- keep-sorted start
import Fren.Elab.Guards
-- keep-sorted end

/-! # Hosted elaboration: tables -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- Translates a table into a chain of `if`s over its rows' conditions,
where `toTerm` translates its parts. Where no row holds, a table without a
`_` row is an index out of range of the empty sequence, `Fren.Seq.nth ∅
0`, as the solver sees it: one unspecified value of each type
(`Reqs/Lang/Expressions#tables`). -/
def tableTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (slot : Option Core.Slot) :
    TermElabM Term := withRef e do
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
  -- The type of the values so far, and those that wait for it.
  let mut rowsTy? : Option Core.Ty := none
  let mut waiting : Array (Nat × ExprCtx × Syntax) := #[]
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
      let c ← toTerm { cx with guards := #[], natOk := false, emptyOk := Core.ExprSite.rowCondition.checked false false, expected? := Core.ExprSite.rowCondition.expected none none } r[1]
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
    -- Each value is checked against the whole's type, or the values' so
    -- far, as the `fren` command does: one that does not synthesize its
    -- own, before any has given one, waits for a later value that does
    -- (`lang::checked`).
    let others := (rows.eraseIdx! k).map (·[3])
    let emptyOk := Core.ExprSite.rowValue.checked cx.emptyOk (← anySynthesizes cx others)
    let vcx := { cx with guards := before ++ own, emptyOk }
    let shared? := Core.ExprSite.rowValue.expected cx.expected? rowsTy?
    if shared?.isNone && !(← synthesizes cx r[3]) && (← rows.anyM (synthesizes cx ·[3])) then
      waiting := waiting.push (k, vcx, r[3])
      values := values.push (← `(sorry))
      continue
    let v ← toTerm { vcx with expected? := shared? } r[3]
    if let some t ← frenTypeOf? v then rowsTy? := some ((rowsTy?.map (·.join t)).getD t)
    values := values.push v
  for (k, vcx, v) in waiting do
    values := values.set! k (← toTerm { vcx with expected? := Core.ExprSite.rowValue.expected cx.expected? rowsTy? } v)
  -- Each value has the type of those before it (`Core.checkRowType`).
  let mut t0? : Option Core.Ty := none
  for r in rows, v in values do
    let some t ← frenTypeOf? v | continue
    if let some t0 := t0? then liftMsg r[3] (Core.checkRowType t0 t)
    t0? := some ((t0?.map (·.join t)).getD t)
  noteTable cx e refs conds defined wild
  -- `same_branches` on a table (`lint::same_rows`).
  if cx.noteIndexes then
    let first := exactText rows[0]![3]
    let (fires, _) := Core.sameRows rows.size (rows.all fun r => Core.writtenSame (exactText r[3]) first) wild
    if fires then
      let v : Core.BText := { text := first, prec := exprPrec rows[0]![3] }
      let msg := Core.sameRowsMsg first (v.inSlot slot (followedStx e)) wild
      recordLint .sameBranches e (if wild && (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  let widened ← widenMixed values
  -- The first row whose condition holds.
  let mut out ← if wild then pure widened.back! else
    `(if $(conds.back!) then $(widened.back!) else Fren.Seq.nth (∅ : Fren.Seq _) 0)
  for i in (List.range (widened.size - 1)).reverse do
    out ← `(if $(conds[i]!) then $(widened[i]!) else $out)
  return out


end Fren
