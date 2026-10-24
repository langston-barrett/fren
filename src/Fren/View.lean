-- keep-sorted start
import Fren.Check
import Fren.Elab
-- keep-sorted end

/-!
# `#fren_check` (the view)

Runs the checks on comps from the model and reports the results as Lean
messages, positioned at the relevant part of the spec. The text comes from
`Fren.Core.messages`, shared with the standalone binary.
-/

open Lean Elab Command

namespace Fren

namespace Lang

/-- Run the checks on the comps and global expectations declared in this file
(or just the named one) and report the results. Declared here rather than in `Fren.Syntax`, so that
`Fren.Spec` alone does not accept it. -/
scoped syntax (name := checkCmd) "#fren_check" (ppSpace fren_path)? : command

end Lang

def report (c : CompInfo) (r : CheckResult) : CommandElabM Unit := do
  for msg in Core.messages (c.vars.any fun v => v.role == .output && !v.isPub) r c.decidable do
    let prop? := msg.item?.bind fun n => c.props.find? (·.name == n)
    let index? := msg.atIndex?.bind fun k => msg.item?.bind fun n => (c.indexes.filter (·.1 == n))[k]?.map (·.2.2.1)
    let ref := if let some r := index? then r else match prop?, msg.item? with
      | some p, _ => if msg.atTrigger then p.triggerRef?.getD p.ref else p.ref
      | none, some n => (c.insts.find? (·.name == n)).map (·.ref)
        |>.orElse (fun _ => (c.vars.find? (·.name == n)).map (·.ref)) |>.getD c.ref
      | none, none => c.ref
    match msg.severity with
    | .error => logErrorAt ref msg.text
    | .warning => logWarningAt ref msg.text
    | .info => logInfoAt ref msg.text

/-- Checks the comps and global expectations `paths`, and reports the
results. -/
def checkAndReport (paths : Array Name) : CommandElabM Unit := do
  let s ← getState
  let mut all := #[]
  for p in paths do
    let (c, kinds) ← match s.comps.get? p, s.globals.get? p, s.refinements.get? p with
      | some c, _, _ => pure (c, Core.kindsFor false)
      | none, some g, _ => pure (g, Core.kindsFor true)
      | none, none, some r => pure (r, Core.CheckKind.all.filter Core.refinementRuns)
      | none, none, none => continue
    let results ← liftTermElabM <| checkComp c kinds
    for r in results do
      report c r
    if c.tested.any then
      logInfoAt c.ref m!"the checks of `{Core.showComp c.path}` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)"
    all := all ++ results
  match Core.summarySeverity all with
  | .info => logInfo (Core.summary all)
  | .warning => logWarning (Core.summary all)
  | .error => logError (Core.summary all)

@[command_elab Lang.checkCmd] def elabCheck : CommandElab := fun stx => do
  checkIdentifiers stx
  if stx[1].isNone then
    let l ← getLocal
    checkAndReport (l.comps ++ l.globals ++ l.refinements)
  else
    let r ← resolvePath (← getLocal).currentModule (pathSegs stx[1][0])
    match r with
    | .item { kind := .compItem, path, .. } | .item { kind := .expectItem, path, .. } => checkAndReport #[path]
    | _ => throwErrorAt stx[1] (Core.wrongKindMsg "a component or a global expectation" r).text

end Fren
