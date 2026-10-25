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

/-- The file name of a message logged while a Markdown spec is read that
already starts with the name of the file it is about, if any: the
`#fren_md`s that read the spec place it without labelling it again
(`Fren.elabMd`). No file has this name. -/
def mdLabelled : String := "<#fren_md>"

/-- Logs `text` about the item `path` at `ref`, by the text of the file that
declares it, wherever it is checked (`Reqs/Markdown#in-lean`). A Markdown
spec's item is placed at the outermost `#fren_md`, the one in the Lean
file, with the spec's name and position (`Fren.elabMd`), or, checked from
the Lean file itself, at the `#fren_check`, with them in the text. The Lean
file's item is placed at its own position, even when a spec checks it. An
imported item is placed at the `#fren_check`, since its text is another
module's. -/
def logAbout (path : Name) (ref : Syntax) (text : MessageData) (severity : MessageSeverity) :
    CommandElabM Unit := do
  let l ← getLocal
  -- Without a position, `logAt` would use the current command's, which
  -- another file's line map would misplace: the message is named by the
  -- file that declares the item, if it is a spec, with no position, and
  -- placed at the check.
  if ref.getPos?.isNone then
    let text := match l.mdSources.find? path with
      | some (rel, _) => m!"{rel}: {text}"
      | none => text
    if l.inMarkdown then
      return ← withReader (fun ctx => { ctx with fileName := mdLabelled }) (logAt ref text severity)
    return ← logAt ref text severity
  match l.mdSources.find? path, l.leanFile? with
  | some (rel, fileMap), _ =>
    if l.inMarkdown then
      withReader (fun ctx => { ctx with fileName := rel, fileMap }) (logAt ref text severity)
    else
      let pos := fileMap.toPosition ((ref.getPos?).getD 0)
      logAt (← getRef) m!"{rel}:{pos.line}:{pos.column}: {text}" severity
  -- The Lean file's own item, checked by a spec.
  | none, some (fileName, fileMap) =>
    if l.leanItems.contains path then withReader (fun ctx => { ctx with fileName, fileMap }) (logAt ref text severity)
    else logAt (← getRef) text severity
  | none, none =>
    if l.leanItems.contains path then logAt ref text severity
    -- An imported item, whose syntax has positions in another module's text,
    -- which neither this file nor a spec has: placed at the check.
    else logAt (← getRef) text severity

def report (path : Name) (c : CompInfo) (r : CheckResult) : CommandElabM Unit := do
  for msg in Core.messages (c.vars.any fun v => v.role == .output && !v.isPub) r c.decidable !c.uses.isEmpty do
    let prop? := msg.item?.bind fun n => c.props.find? (·.name == n)
    let index? := msg.atIndex?.bind fun k => msg.item?.bind fun n => (c.indexes.filter (·.1 == n))[k]?.map (·.2.2.1)
    let ref := if let some r := index? then r else match prop?, msg.item? with
      | some p, _ => if msg.atTrigger then p.triggerRef?.getD p.ref else p.ref
      | none, some n => (c.insts.find? (·.name == n)).map (·.ref)
        |>.orElse (fun _ => (c.vars.find? (·.name == n)).map (·.ref)) |>.getD c.ref
      | none, none => c.ref
    let severity := match msg.severity with
      | .error => MessageSeverity.error
      | .warning => .warning
      | .info => .information
    logAbout path ref msg.text severity

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
      report p c r
    if c.tested.any then
      logAbout p c.ref m!"the checks of `{Core.showComp p}` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)" .information
    all := all ++ results
  match Core.summarySeverity all with
  | .info => logInfo (Core.summary all)
  | .warning => logWarning (Core.summary all)
  | .error => logError (Core.summary all)

@[command_elab Lang.checkCmd] def elabCheck : CommandElab := fun stx => do
  checkLexemes stx
  if stx[1].isNone then
    let l ← getLocal
    checkAndReport (l.comps ++ l.globals ++ l.refinements)
  else
    let r ← resolvePath (← getLocal).currentModule (pathSegs stx[1][0])
    match r with
    | .item { kind := .compItem, path, .. } | .item { kind := .expectItem, path, .. } => checkAndReport #[path]
    | _ => throwErrorAt stx[1] (Core.wrongKindMsg "a component or a global expectation" r).text

end Fren
