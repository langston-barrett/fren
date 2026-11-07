-- keep-sorted start
import Fren.Elab.Evidence
import Fren.Elab.Terms
-- keep-sorted end

/-! # Hosted elaboration: global expectations -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Elaborates a global expectation in its short form, `expect n: e`, into
a `CompInfo` whose path is its module (`Model.Entry.globalInfo`),
generating `decl` for it. Binders over values, `forall (m: M), e`, are a
quantifier around `e`. -/
def elabGlobalInfo (modName n : Name) (nameStx : Syntax) (binderStxs : Array Syntax) (body : Syntax)
    (decl : Name) : TermElabM CompInfo := do
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binderStxs.flatMap (·[1].getArgs)
  for x in binderIds do discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt binderIds[k]! (Core.dupBinderMsg declared[k]!).text
  let valueBinders := binderStxs
  let cx : ExprCtx := { modName, vars := #[], insts := #[], place := .prop }
  discard (takeIndexes #[])
  let t ← if valueBinders.isEmpty then toTerm cx body else quantTerm toTerm cx body true valueBinders body
  checkDeclared body t (mkConst ``Bool) fun _ => "note: an expectation is a `Bool`"
  let e ← elabProp t
  let indexes := (← takeIndexes #[]).map fun (r, q, g) => (n, Core.IndexPlace.prop, r, q, g)
  -- The body is in the scope of the binders over values too.
  lintBools body (← hidesIn cx (valueBinders.flatMap (·[1].getArgs) |>.map fun x =>
    ((declaredIdent x).1.getId, Core.BindingKind.boundName)))
  lintConstant cx "expect" body
  -- A quantifier leaves it without a trigger.
  let trig ← if valueBinders.isEmpty then triggerOf cx body else pure none
  let trigger? ← trig.mapM fun (t, _) => elabProp t
  let value ← mkArrow (mkAndN []) e
  let uses ← usesOf #[value]
  addUsesDef uses decl value
  let prop : PropInfo := {
    kind := .expect, name := n, ref := nameStx, body := e
    trigger?, triggerRef? := trig.map (·.2), decl }
  discard checkCounts
  return { path := modName, vars := #[], props := #[prop], ref := nameStx, decl, uses
           decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied, indexes
           guarded := (← getLocal).guardedUsed }

/-- The text of the global expectation `stx` that `duplicate_constraint`
compares: after its name, without the parentheses around its body. -/
def globalText (stx : Syntax) : String :=
  let body := unparen stx[4]
  match stx[1].getTailPos?, body.getPos?, stx.getSubstring? false false with
  | some a, some b, some sub => String.Pos.Raw.extract sub.str a b ++ exactText body
  | _, _, _ => exactText body

@[command_elab Lang.globalCmd] def elabGlobal : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let nameStx := stx[1]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  startDeclared
  modifyLocal fun l => { l with currentItem := modName ++ n }
  -- `duplicate_constraint` (`lint::duplicate_constraint`), against the
  -- earlier ones of its module.
  let text := globalText stx
  let l ← getLocal
  if let some (_, earlier, _) := l.globalTexts.find? fun (m, _, t) => m == modName && Core.writtenSame t text then
    let msg := Core.duplicateConstraintMsg .expect .expect earlier.toString
    recordLint .duplicateConstraint nameStx (if l.inMarkdown then msg.note Core.fixHelp else msg)
  modifyLocal fun l => { l with globalTexts := l.globalTexts.push (modName, n, text) }
  let path := modName ++ n
  let decl ← generatedName path
  let binders := if stx[3].isNone then #[] else stx[3][1].getArgs
  let info ← liftTermElabM <| elabGlobalInfo modName n nameStx binders (withWhere stx[4] stx[5]) decl
  lintDeclared .global n nameStx
  let all ← evidenceInEffect
  let info := { info with tested := Core.Tested.ofSettings all.tested #[] #[(n, none)] #[] #[]
                          enumerated := Core.Tested.ofSettings all.enumerated #[] #[(n, none)] #[] #[]
                          enumSize := ← enumSizeInEffect }
  record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
  record (.globalInfo path info)
  elabCommand (← `(attribute [fren_spec] $(mkCIdent decl)))
  modifyLocal fun l => { l with globals := l.globals.push path }.declared path



end Fren
