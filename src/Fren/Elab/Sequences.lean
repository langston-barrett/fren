-- keep-sorted start
import Fren.Elab.Guards
-- keep-sorted end

/-! # Hosted elaboration: sequences -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `[a, b]`, or `[]` where `emptyOk` says that something gives it a type. -/
def seqLitTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk : Bool) (e : Syntax) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  let elems := e[1].getSepArgs
  if elems.isEmpty then
    unless emptyOk do throwErrorAt e Core.emptySeqTypeMsg.text
    if expected?.isSome then discard (liftMsg e (Core.checkEmptyLiteral true expected?))
    if let some t@(.seq _) := expected? then return ← `((∅ : $(typeSyntax (← leanTypeOf t))))
    return ← `((∅ : Fren.Seq _))
  let synth ← elems.mapM (synthesizes cx)
  let ecx (k : Nat) := { cx with emptyOk := Core.ExprSite.element.checked emptyOk ((synth.eraseIdx! k).any id) }
  -- Each element is checked against the literal's element type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  -- An element is never a `Nat` (`lang::nat_place`).
  let elem? ← match expected?.bind fun | .seq t => some t | _ => none with
    | some t => pure (some t)
    | none => if synth[0]! then pure none else
        match synth.findIdx? id with
        | some k => do
          let s ← saveState
          let t? ← frenTypeOf? (← toTerm { ecx k with noteIndexes := false } elems[k]!)
          s.restore
          pure t?
        | none => pure none
  let x0 ← toTerm { ecx 0 with expected? := elem? } elems[0]!
  let t0? := ((← frenTypeOf? x0).orElse fun _ => if synth[0]! then none else elem?).map (·.widen)
  let mut xs := #[← boolTerm (← widenTerm x0)]
  for k in [1:elems.size] do
    let x ← toTerm { ecx k with expected? := t0? } elems[k]!
    if let (some t, some t0) := ((← frenTypeOf? x).map (·.widen), t0?) then
      unless t == t0 do throwErrorAt elems[k]! (Core.membersMsg true t0.show t.show (Core.Ty.seq t0).show).text
    xs := xs.push (← boolTerm (← widenTerm x))
  -- After its elements, as in the `fren` command.
  checkCore cx e .seqArray true true elems
  checkNewtypeMembers cx true elems xs
  let mut t ← `(Fren.Seq.unit $(xs.back!))
  for x in xs.pop.reverse do t ← `(Fren.Seq.unit $x ++ $t)
  return t

/-- `q[i]`, indexing a sequence. -/
def indexTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e do
  let q ← toTerm cx e[0]
  let tq ← typeOf q
  unless tq.isAppOfArity ``Fren.Seq 1 do throwErrorAt e[0] (Core.notIndexableMsg (← typeName tq)).text
  let i ← widenTerm (← toTerm cx e[2])
  let ti ← typeOf i
  unless ti.isConstOf ``Int do throwErrorAt e[2] s!"type mismatch: expected `Int`, found `{← typeName ti}`"
  checkCore cx e .seqArray true true #[e[0], e[2]]
  -- `negative_position` (`lint::negative_position`).
  if let (true, some k) := (cx.noteIndexes, Core.negativeLiteral? (exactText (unparen e[2]))) then
    recordLint .negativePosition e (Core.negativeIndexMsg (exactText e[0]) k)
  -- `Fren.Seq.nth` is `default` out of range, which an abstract type's
  -- placeholder does not have.
  let elem := (← instantiateMVars tq).appArg!
  if (← trySynthInstance (mkApp (Lean.mkConst ``Inhabited [Level.one]) elem)) matches .none then
    throwErrorAt e s!"the Lean front end cannot yet index a sequence of `{← typeName elem}`, which has no default value"
  noteIndex cx e q i
  `(Fren.Seq.nth $q $i)


end Fren
