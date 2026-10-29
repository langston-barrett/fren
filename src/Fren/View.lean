-- keep-sorted start
import Fren.Check
import Fren.Elab
import Fren.Enumerate
import Fren.Prelude
import Fren.RecursiveProof
-- keep-sorted end

/-!
# `#fren_check` (the view)

Runs the checks on procedures from the model and reports the results as Lean
messages, positioned at the relevant part of the spec. The text comes from
`Fren.Core.messages`, shared with the standalone binary.
-/

open Lean Meta Elab Command

namespace Fren

namespace Lang

/-- Run the checks on the procedures and global expectations declared in this file
(or just the named one) and report the results. Declared here rather than in `Fren.Syntax`, so that
`Fren.Spec` alone does not accept it. A Lean keyword after it starts the
next command, though `frenIdent` reads one as a name elsewhere. -/
scoped syntax (name := checkCmd) "#fren_check" (ppSpace notLeanKeyword fren_path)? : command

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
  for msg in Core.messages (c.vars.any fun v => v.role == .output && !v.isPub) { r with global := c.global } c.decidable do
    let message := if let some subset := c.subset? then
        if r.verdict == .fail && msg.severity == .error then
          { msg.msg with code? := some "F0660", headline := s!"subset type `{Core.showPath subset}` is empty"
                         label? := some "no value satisfies its invariants"
                         notes := (msg.msg.notes.filter (!·.startsWith "help:")).map (·.replace "no outputs satisfy" "no value satisfies")
                           |>.push "help: weaken the invariants or choose a base type with a satisfying value" }
        else msg.msg
      else if let some invariant := c.subsetInvariant? then
        if r.verdict == .fail && msg.severity == .error then
          { msg.msg with code? := some "F0662", headline := s!"invariant `{Core.showPath invariant}` may not be defined"
                         label? := some "not defined under the earlier invariants" }
        else msg.msg
      else if let some label := r.patTy?.bind (·.dropPrefix? "@invariant:") then
        if msg.severity == .error then
          { msg.msg with code? := some "F0661", headline := s!"invariant `{label}` does not hold", label? := some "violates the invariant"
                         notes := (msg.msg.notes.filter (·.startsWith "counterexample:")).push
                           "note: a value given for a subset type must satisfy each named invariant" }
        else msg.msg
      else msg.msg
    let msg := { msg with msg := message }
    let prop? := msg.item?.bind fun n => c.props.find? (·.name == n)
    -- The `k`th index, or question about a table, of the item.
    let site? (k : Nat) (table : Bool) := msg.item?.bind fun n =>
      (c.indexes.filter fun x => x.1 == n && x.2.2.2.1.isSome == table)[k]?.map (·.2.2.1)
    let at? := (msg.atIndex?.bind (site? · false)).orElse fun _ => msg.atSite?.bind (site? · true)
    let ref := if let some r := at? then r else match prop?, msg.item? with
      | some p, _ => if msg.atTrigger then p.triggerRef?.getD p.ref else p.ref
      | none, some n => (c.insts.find? (·.name == n)).map (·.ref)
        |>.orElse (fun _ => (c.vars.find? (·.name == n)).map (·.ref)) |>.getD c.ref
      | none, none => c.ref
    let ref ← if let some range := msg.atRange? then do
        let sourceState ← getLocal
        let fallback := (← getFileMap).source
        let source := if let some (_, map) := prop?.bind (·.source?) then map.source else match sourceState.mdSources.find? path, sourceState.leanFile? with
          | some (_, map), _ => map.source
          | none, some (_, map) => map.source
          | _, _ => fallback
        let start : String.Pos.Raw := ⟨(String.ofList (source.toList.take range.start)).utf8ByteSize⟩
        let stop : String.Pos.Raw := ⟨(String.ofList (source.toList.take range.stop)).utf8ByteSize⟩
        pure (Syntax.atom (.synthetic start stop true) "")
      else pure ref
    let severity := match msg.severity with
      | .error => MessageSeverity.error
      | .warning => .warning
      | .info => .information
    -- A closure's obligation names the function that applies it.
    let vias := (← getLocal).vias
    let text := match at?.bind fun r => vias.find? (·.1 == r.getPos?) with
      | some (_, f) => if msg.severity == .error then (msg.msg.note (Core.viaNote f)).text else msg.text
      | none => msg.text
    if let some (fileName, fileMap) := (prop?.filter fun p => msg.atRange?.isSome || p.sourceRef).bind (·.source?) then
      withReader (fun ctx => { ctx with fileName, fileMap }) (logAt ref text severity)
    else logAbout path ref text severity

/-- Of the top-level commands of the current file before `stop`, where the
`#guard_msgs` start, and how many parse errors Lean found, which no
elaborator sees: the file is parsed again, with the syntax in scope here. -/
def scanCommands (stop : String.Pos.Raw) : CommandElabM (Array Nat × Nat) := do
  let inputCtx := Parser.mkInputContext (← getFileMap).source (← getFileName)
  let (_, ps, msgs) ← Parser.parseHeader inputCtx
  let pmctx : Parser.ParserModuleContext :=
    { env := ← getEnv, options := ← getOptions, currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls }
  let mut ps := ps
  let mut msgs := msgs
  let mut guarded := #[]
  while ps.pos < stop do
    let pos := ps.pos
    let (stx, ps', msgs') := Parser.parseCommand inputCtx pmctx ps msgs
    if stx.isOfKind ``Lean.guardMsgsCmd then guarded := guarded.push pos.byteIdx
    if ps'.pos == pos || Parser.isTerminalCommand stx then break
    ps := ps'
    msgs := msgs'
  return (guarded, msgs.toList.filter (·.severity == .error) |>.length)

/-- How many static errors come before this `#fren_check`: those that
Fren's commands logged in any file, but not those that a `#guard_msgs`
expects in this one; Lean's parse errors in this file; and the lints so
far that are errors (`Reqs/View#static-errors`). -/
def staticErrorsBefore : CommandElabM Nat := do
  let (guarded, parse) ← scanCommands (← read).cmdPos
  let file ← getFileName
  let recorded := (← getLocal).staticErrors.foldl (init := 0) fun n (f, p, k) =>
    if f == file && guarded.contains p then n else n + k
  let lints := (← pendingLints).filter (·.2 == .error) |>.size
  return recorded + parse + lints

/-- The errors logged so far by the current command. -/
def errorsLogged : CommandElabM Nat :=
  return (← get).messages.toList.filter (·.severity == .error) |>.length

/-- What checking an item in a task of its own gives: its results and the
theorems of its cover goals (`checkComp`), or the exception it threw, with
the messages, traces and info trees that it logged. -/
abbrev CheckOutcome :=
  Except Exception (Array CheckResult × Array Declaration × Option (Except Core.Msg Core.Enumeration.Enumerated)) ×
    MessageLog × PersistentArray TraceElem × PersistentArray InfoTree

/-- Generate a structural induction theorem for the conjunction of the
postconditions, then expose each clause as a theorem. This is simultaneous
induction, so no successful clause is published if another failed. -/
def proveRecursiveContract (c : CompInfo) (results : Array CheckResult) : CommandElabM Unit := do
  let st ← getState
  let some fn := c.fn? | return
  let some d := st.defined.get? fn | return
  let some i := d.decreasing? | return
  let posts := results.filter (·.kind == .postcondition)
  if posts.isEmpty || posts.any (·.verdict != .pass) then return
  let some k := st.contracts.get? fn | return
  let name := d.decl ++ `contract
  if (← getEnv).contains name then return
  liftTermElabM <| withOptions (fun opts => (warn.sorry.set opts false).setBool `linter.unusedSimpArgs false) <| Term.withoutErrToSorry do
    -- Follow definitions and clauses transitively so unrelated contracts do
    -- not become theorem assumptions (including functions declared later).
    let mut pending := #[d.decl] ++ (k.pres ++ k.posts).map (·.decl)
    let mut reachable : Array Name := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      if reachable.contains n then continue
      reachable := reachable.push n
      if let some info := (← getEnv).find? n then
        if let some value := info.value? then
          pending := pending ++ value.getUsedConstants
    let mut dependencies := #[]
    for (path, other) in st.defined.toArray do
      if path == fn || other.decreasing?.isNone || !reachable.contains other.decl then continue
      let some contract := st.contracts.get? path | continue
      for p in contract.posts do
        let type ← recursiveDependencyType path p
        unless ← hasRecursiveDependencyProof p type do
          dependencies := dependencies.push (p.decl, type)
    withLocalDeclsD (dependencies.map fun (n, t) => (n, fun _ => pure t)) fun deps =>
     withLocalDeclsD (c.vars.map fun v => (v.name, fun _ => pure v.type)) fun xs => do
      let pres := ((c.vars.zip xs).filterMap fun (v, x) => v.fact?.map (·.beta #[x]))
        ++ k.pres.map (fun p => p.at xs)
      let post := mkAndN ((k.posts.map fun p => p.at xs).toList)
      let ty := pres.foldr (fun p b => mkForall `h .default p b) post
      let ty ← mkForallFVars deps (← mkForallFVars xs ty)
      let ids := c.vars.map (·.name.toString)
      let mut dependencyNames := #[]
      for j in [:deps.size] do
        let mut n := s!"dependency_{j}"
        while ids.contains n || dependencyNames.contains n do n := n ++ "_"
        dependencyNames := dependencyNames.push n
      let dependencyIntros := if deps.isEmpty then "" else
        "\n  intro " ++ " ".intercalate dependencyNames.toList
      let clauses := (k.pres ++ k.posts).map (·.decl.toString)
      let generalized := (c.vars.zipIdx.filter (·.2 != i)).map (·.1.name.toString)
      let suffix := "\n  all_goals intros"
        ++ "\n  all_goals try simp only [" ++ d.decl.toString ++ "]"
        ++ "\n  all_goals (repeat' first | split)"
        ++ "\n  all_goals fren_recursive_case " ++ d.decl.toString
      let ordinary := "by" ++ dependencyIntros ++ "\n  intro " ++ " ".intercalate ids.toList
        ++ "\n  induction " ++ ids[i]!
        ++ (if generalized.isEmpty then "" else " generalizing " ++ " ".intercalate generalized.toList)
        ++ "\n  all_goals dsimp only [" ++ ", ".intercalate clauses.toList ++ "] at *" ++ suffix
      let structural := "by" ++ dependencyIntros ++ "\n  intro " ++ " ".intercalate ids.toList
        ++ "\n  dsimp only [" ++ ", ".intercalate clauses.toList ++ "] at *"
        ++ "\n  fun_induction @" ++ d.decl.toString ++ " "
        ++ " ".intercalate ((d.uses.map (·.toString) ++ ids).toList) ++ suffix
      -- Reflection can introduce self-applications below an immediate child.
      -- Well-founded induction supplies their contracts without reflecting again.
      let decreasingType := (← ppExpr c.vars[i]!.type).pretty
      let mut ihName := "recursive_ih"
      while ids.contains ihName do ihName := ihName ++ "_"
      let strong := "by" ++ dependencyIntros ++ "\n  intro " ++ " ".intercalate ids.toList
        ++ (if generalized.isEmpty then "" else "\n  revert " ++ " ".intercalate generalized.toList)
        ++ "\n  induction " ++ ids[i]! ++ " using (@sizeOfWFRel (" ++ decreasingType ++ ") inferInstance).wf.induction with\n  | h " ++ ids[i]! ++ " " ++ ihName ++ " =>\n    cases " ++ ids[i]!
        ++ "\n    all_goals dsimp only [" ++ ", ".intercalate clauses.toList ++ "] at *" ++ (suffix ++ " " ++ ihName).replace "\n  " "\n    "
      let prove (script : String) : TermElabM Expr := do
        let proof ← match Parser.runParserCategory (← getEnv) `term script with
          | .ok proof => pure proof
          | .error error => throwError "could not generate recursive contract proof: {error}"
        let value ← Term.elabTermEnsuringType proof ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        if value.hasMVar || value.hasSyntheticSorry then throwError "recursive contract proof has unproved goals"
        return value
      let saved ← saveState
      let value ← try prove ordinary catch _ =>
        -- A nested payload need not be an immediate child. Lean derives
        -- this induction principle from the same structural definition.
        saved.restore
        try prove structural catch _ =>
          saved.restore
          prove strong
      addDecl (.thmDecl { name, levelParams := [], type := ty, value })
      -- Each postcondition's theorem follows from the simultaneous theorem.
      for p in k.posts, j in [0:k.posts.size] do
        let pty := pres.foldr (fun h b => mkForall `h .default h b) (p.at xs)
        forallTelescope pty fun hs _ => do
          let both := mkAppN (mkAppN (mkAppN (mkConst name) deps) xs) hs
          let selected ← if k.posts.size == 1 then pure both else do
            let mut selected := both
            for _ in [0:j] do selected ← mkAppM ``And.right #[selected]
            if j + 1 < k.posts.size then selected ← mkAppM ``And.left #[selected]
            pure selected
          let type ← mkForallFVars deps (← mkForallFVars xs pty)
          let value ← mkLambdaFVars deps (← mkLambdaFVars xs (← mkLambdaFVars hs selected))
          addDecl (.thmDecl { name := p.decl ++ `holds, levelParams := [], type, value })

/-- Checks each of `items` in a task of its own (`checkComp`), started now,
from the current state. Each runs as `liftTermElabM` would run it here,
with a heartbeat budget of its own, as each `liftTermElabM` has, and with
nothing logged yet: what it logs is kept for `awaitCheck`. -/
def checkItems (items : Array (Name × CompInfo × Array CheckKind)) (sites : Array (Core.InstanceSite × Name × Array Core.Ty))
    (cancel : IO.CancelToken) : CommandElabM (Array (Task (Except Exception CheckOutcome))) := do
  let run ← wrapAsync (cancelTk? := some cancel) fun ((p, c, kinds) : Name × CompInfo × Array CheckKind) => do
    modify fun s => { s with messages := {}, traceState.traces := {}, infoState.trees := {} }
    -- The instances whose contracts it checks (`lang::instance_site`): a
    -- function's own, with its contract, and an item's.
    let own := sites.filterMap fun (site, f, targs) => if site == .function && f == p then some targs else none
    let foreign := sites.filterMap fun (site, f, targs) => if site == .item 1 p then some (f, targs) else none
    let r ← try .ok <$> liftTermElabM (checkComp c kinds (some Enumerate.enumerate) (some elabHooks) own foreign)
      catch ex => pure (.error ex)
    let s ← get
    return (r, s.messages, s.traceState.traces, s.infoState.trees)
  items.mapM fun i => (EIO.asTask (run i) : BaseIO _)

/-- Waits for a task of `checkItems`, adds what it logged to the current
state, and gives its results, or throws its exception, as `liftTermElabM`
would have. -/
def awaitCheck (task : Task (Except Exception CheckOutcome)) :
    CommandElabM (Array CheckResult × Array Declaration × Option (Except Core.Msg Core.Enumeration.Enumerated)) := do
  let (r, msgs, traces, trees) ← ofExcept (← IO.wait task)
  modify fun s => { s with messages := s.messages ++ msgs, traceState.traces := s.traceState.traces ++ traces,
                           infoState.trees := s.infoState.trees ++ trees }
  ofExcept r

/-- Checks the procedures and global expectations `paths`, and reports the
results; after a static error, checks none, as the `fren` command does. -/
def checkAndReport (paths : Array Name) : CommandElabM Unit := do
  let before ← errorsLogged
  try checkAndReport' paths
  finally
    let logged := (← errorsLogged) - before
    modifyLocal fun l => { l with checkErrors := l.checkErrors + logged }
where
  checkAndReport' (paths : Array Name) : CommandElabM Unit := do
  let errors ← staticErrorsBefore
  if errors > 0 then
    return ← logError Core.couldNotHeadline
  let s ← getState
  let mut items := #[]
  for p in paths do
    let (c, kinds) ← match s.comps.get? p, s.globals.get? p, s.refinements.get? p with
      | some c, _, _ => pure (c, Core.CheckedItem.component.kinds)
      | none, some g, _ => pure (g, (if g.global then Core.CheckedItem.global else .shortGlobal).kinds)
      | none, none, some r => pure (r, Core.CheckKind.all.filter Core.refinementRuns)
      | none, none, none => match s.bodies.get? p with
        -- An uninterpreted function's contract has its value as an output.
        | some b => pure (b, (if b.vars.any (·.role == .output) then Core.CheckedItem.contract else .body).kinds)
        | none => continue
    -- Not where `undecidable` is denied, though the error does not stop
    -- `#fren_check` where `#guard_msgs` catches it: the solver is not asked
    -- about constructs outside the decidable core that the spec has not
    -- opted into, on which it may abort
    -- (`Reqs/Lint/Decidability#undecidable-constructs`).
    if c.undecidableDenied then continue
    items := items.push (p, c, kinds)
  -- Each item is checked in a task of its own, all at once; the results are
  -- then reported, and the cover goals' theorems added, in order, as if
  -- each had been checked in turn (`checkItems`).
  let cancel ← IO.CancelToken.new
  -- The instances whose contracts this run checks, each with the first
  -- item that it checks and that uses it, and recorded, so that no later
  -- run checks them again (`lang::instance_site`).
  let keys := items.map (·.1)
  let sites := s.instanceSites (← getMainModule) (keys.contains ·)
  for (_, f, targs) in sites do record (.instanceChecked f targs)
  let tasks ← checkItems items sites cancel
  let mut all := #[]
  let mut byBound := 0
  for (p, c, _) in items, task in tasks do
    let (results, witnesses, enumerated?) ← try awaitCheck task catch ex => cancel.set; throw ex
    -- Proof artifacts are supplementary: preserve the checker report even
    -- if generation fails, and discard any partial declarations/messages.
    let proofState ← get
    try proveRecursiveContract c results catch _ => set proofState
    for d in witnesses do
      liftCoreM <| addCoverWitness d
    for r in results do
      report p c r
    if (c.tested.minus c.enumerated).any then
      logAbout p c.ref m!"the checks of `{Core.showComp p}` set to testing are run by `fren check`, not in Lean (`Reqs/Check#checking-by-testing`)" .information
    all := all ++ results
    -- The checks set to enumeration (`Reqs/Check#checking-by-enumeration`).
    match enumerated? with
    | some (.error msg) => logAbout p c.ref msg.text .error
    | some (.ok e) =>
      for r in e.results do
        report p c r
      all := all ++ e.results
      byBound := byBound + (e.results.filter fun r => r.verdict == .pass && r.bounded?.isSome).size
      if let some msg := e.boundedMsg? s!"`{Core.showComp p}`" c.tested then
        logAbout p c.ref msg.text .information
    | none => pure ()
  match Core.summarySeverity all with
  | .info => logInfo (Core.summary all 0 byBound)
  | .warning => logWarning (Core.summary all 0 byBound)
  | .error => logError (Core.summary all 0 byBound)

@[command_elab Lang.checkCmd] def elabCheck : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  lintInvisible stx
  if stx[1].isNone then
    let l ← getLocal
    checkAndReport (l.comps ++ l.globals ++ l.refinements ++ l.bodies)
  else
    let r ← resolvePath (← getLocal).currentModule (pathSegs stx[1][0])
    match r with
    | .item { kind := .compItem, path, .. } | .item { kind := .expectItem, path, .. } => checkAndReport #[path]
    | _ => throwErrorAt stx[1] (Core.wrongKindMsg "a procedure or a global expectation" r).text

end Fren
