-- keep-sorted start
import Fren.Elab.Induction
import Fren.Elab.Procedures
-- keep-sorted end

/-! # Hosted elaboration: global blocks -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang

/-- `expect n(x: T) { members }`, a global expectation with a block
(`Reqs/Lang/Global`): elaborated as a procedure is, but for the members it
does not accept (`F0417`), and recorded as a global expectation, which
nothing calls. -/
@[command_elab Lang.globalBlockCmd] def elabGlobalBlock : CommandElab := recordingErrors fun stx0 => do
  checkLexemes stx0
  checkGlobalBlockParsed stx0
  -- Aligned as a procedure's, after a `pub` that it does not have.
  -- Its `out` members are reported as members that it does not accept
  -- (`F0417`, `blockMemberError?`), not as a procedure's (`F0444`).
  let stx : Syntax := mkNode ``Lang.procCmd (#[mkNullNode] ++ stx0.getArgs)
  lintItem stx0
  lintTrailingCommas stx0
  let modName := (← getLocal).currentModule
  let nameStx := stx[2]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang n)
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  checkFresh modName n nameStx
  lintName .global n nameStx
  if let some (ref, msg) ← blockMemberError? stx then
    throwErrorAt ref msg.text
  startDeclared
  let path := modName ++ n
  modifyLocal fun l => { l with currentItem := path }
  let declBase ← generatedName path
  let all ← procMembers stx
  let (members, tested, enumerated) ← testedOf (← evidenceInEffect) all
  let enumSize ← enumSizeInEffect
  for m in members do
    if m.isOfKind ``Lang.useMember then declareUse (pathSegs m[1]) (!m[2].isNone) m[1] (some path)
    else if m.isOfKind ``Lang.useGroupMember then
      for p in m[3].getSepArgs do declareUse (pathSegs m[1] ++ pathSegs p) false p (some path)
  let scope := if members.any (fun m => m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember) then path
    else modName
  modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[]
                                inductionArgs := #[], inductionAbstract := false }
  let named := members.filterMap memberName?
  for x in named do
    if let .original .. := x.getHeadInfo then discard (segName x)
  let declared := named.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k]! (Core.dupMemberMsg declared[k]! (global := true)).text
  let raw := stx[8].getArgs
  let body ← raw.mapM fun m => return (← unwrapEvidence m).1
  lintMemberOrder stx stx[7] raw body (global := true)
  let (ok, generated) ← liftTermElabM <|
    elabCompMembers scope path modName declBase false nameStx members tested enumerated enumSize (global := true)
  lintDeclared .global n nameStx
  lintLines .global n nameStx stx0
  if ok = true then
    for d in generated do
      elabCommand (← `(attribute [fren_spec] $(mkCIdent d)))
    modifyLocal fun l => { l with globals := l.globals.push path }.declared path
    elabInductions stx path members


end Fren
