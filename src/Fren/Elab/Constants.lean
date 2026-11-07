-- keep-sorted start
import Fren.Elab.AbstractTypes
import Fren.Elab.Declarations
import Fren.Elab.Terms
-- keep-sorted end

/-! # Hosted elaboration: constants -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Constants and global expectations -/

@[command_elab Lang.constCmd] def elabConst : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let valueStx := withWhere stx[6] stx[7]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkConstName n)
  checkFresh modName n nameStx
  lintName .constant n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  liftTermElabM do
    let (type, pt) ← elabPType modName stx[4]
    lintRelTypes modName stx[4]
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := (← getState).placeholders.contains type.constName
    unless Core.constantAccepted abstract false do
      throwErrorAt stx[4] (Core.unknownConstantMsg abstract).text
    modifyLocal fun l => { l with outsideCore := false, guardedUsed := false }
    discard (takeIndexes #[])
    let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop, emptyOk := Core.ExprSite.constantValue.checked false false, natOk := type.isConstOf ``Nat, expected? := Core.ExprSite.constantValue.expected (← coreTy? type) none }
    let t ← toTerm cx valueStx
    noteObligation cx .constant valueStx pt t
    let tables := (← takeIndexes #[]).filter fun (_, q, g) => q.isSome || (obligationTy? g).isSome
    checkDeclared valueStx t type fun ty => s!"note: `{n}` has type `{ty}`"
    -- A `Bool` value is decided, classically if need be, as a defined
    -- function's body is: an unbounded quantifier, or equality on an
    -- abstract type, has no other `Decidable` instance.
    let value ← if type.isConstOf ``Bool then do
        let p ← elabProp t
        let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) p) with
          | .some i => pure i
          | _ => pure (mkApp (mkConst ``Classical.propDecidable) p)
        pure (mkApp2 (mkConst ``Decidable.decide) p inst)
      else elabProp t type
    let applies ← applications { modName, vars := #[], insts := #[], place := .prop } valueStx
    unless Core.constantAccepted abstract !applies.isEmpty do
      throwErrorAt applies[0]! (Core.unknownConstantMsg abstract).text
    lintBools valueStx (← hidesIn { modName, vars := #[], insts := #[], place := .prop })
    addDecl (.defnDecl { name := decl, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute decl
    compileGenerated decl type value
    record (.item { item := { kind := .constItem, path, isPub, owner := modName }, ref := nameStx })
    let int? ← if type.isConstOf ``Int || type.isConstOf ``Nat then intConstValue? { modName, vars := #[], insts := #[], place := .prop } valueStx
      else pure none
    record (.itemCore path (!(← getLocal).outsideCore))
    record (.constInfo { path, decl, type, value, int?, guarded := (← getLocal).guardedUsed })
    recordBody path nameStx decl #[] (tables.map fun (r, q, g) => (n, .body, r, q, g))
    unless isPub do recordItem .constant path nameStx
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))


end Fren
