-- keep-sorted start
import Fren.Elab.ProcedureParts
import Fren.Elab.ProcedureSyntax
-- keep-sorted end

/-! # Hosted elaboration: procedures -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang

@[command_elab Lang.procCmd] def elabProc : CommandElab := recordingErrors fun stx => do
  -- The file's errors so far: `proc_without_outputs` records the procedure
  -- only if it adds no static error, failed checks aside, as the `fren`
  -- command keeps nothing of an item with a static error.
  let errorsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
  let checksBefore := (← getLocal).checkErrors
  checkLexemes stx
  checkProcMembers stx
  let stx := requiresAsAssumes stx 8
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "procedure" nameStx
  checkFresh modName n nameStx
  lintName .component n nameStx
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  let declBase ← generatedName path
  let all ← procMembers stx
  -- The evidence settings, apart from the members they set.
  let (members, tested, enumerated) ← testedOf (← evidenceInEffect) all
  let enumSize ← enumSizeInEffect
  -- Its `use`s, and the scope that its paths resolve in.
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
  -- Distinct names (`lang::distinct_names`): variables, calls and
  -- constraints share one namespace.
  let named := members.filterMap memberName?
  for x in named do
    if let .original .. := x.getHeadInfo then discard (segName x)
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k]! (Core.dupMemberMsg declared[k]!).text
  let raw := stx[8].getArgs
  let body ← raw.mapM fun m => return (← unwrapEvidence m).1
  lintMemberOrder stx stx[7] raw body
  let (ok, generated) ← liftTermElabM <| elabCompMembers scope path modName declBase isPub nameStx members tested enumerated enumSize
  lintDeclared .component n nameStx
  lintLines .component n nameStx stx
  -- `proc_without_outputs`, once the file's paths are known
  -- (`pendingLints`), if the procedure has no static error.
  let errorsAfter := (← get).messages.toList.filter (·.severity == .error) |>.length
  let staticErrors := errorsAfter - errorsBefore - ((← getLocal).checkErrors - checksBefore)
  if ok && staticErrors == 0 then
    let members := (← blockMembers stx).toList.map (·.2)
    if Core.procWithoutOutputs isPub members 0 then
      let r : Core.ProcRecord := { path, isPub, members, level := ← lintLevel .procWithoutOutputs }
      modifyLocal fun l => { l with procs := l.procs.push (r, nameStx) }
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with comps := l.comps.push path }.declared path

/-- The first member of the global expectation `stx`, aligned as a
procedure's, that its block does not accept (`lang::block_member`), with
where it is reported. -/
def blockMemberError? (stx : Syntax) : CommandElabM (Option (Syntax × Core.Msg)) :=
  return (← blockMembers stx).findSome? fun (ref, m, det) => (Core.blockMemberReport? m det).map (ref, ·)


end Fren
