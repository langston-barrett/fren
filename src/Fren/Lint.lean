-- keep-sorted start
import Fren.Model
import FrenCore.Lint
-- keep-sorted end

/-!
# Lints in Lean

The Lean side of `FrenCore.Lint` (`Reqs/Lint`). A lint's level is the Lean
option `fren.lint.NAME`, and a group's `fren.lint.GROUP`. `set_option` for
these options is elaborated here, before Lean's own elaborator: it rejects
levels that do not exist and changes to a forbidden lint, sets each lint of
a group, and gives each `"expect"` its expectation, as the hidden option
`fren.lint.NAME.expectation`. Since `set_option ... in`
is a `section`, both end with it.

Elaborators record what the lints need in the file's `LocalState`, and
`reportLints` reports them at the end of the file, or of a Markdown spec
(`Fren.Literate`).
-/

section
open Lean Elab Command

namespace Fren

-- Each lint's option and each group's, registered from `Core.Lint.all` and
-- `Core.Group.all`, so that a new lint needs no entry here.
run_cmd do
  let reg (n : Name) (dflt descr : String) : CommandElabM Unit := do
    elabCommand (← `(register_option $(mkIdent n) : String := {
      defValue := $(Syntax.mkStrLit dflt)
      descr := $(Syntax.mkStrLit descr)
    }))
  for l in Core.Lint.all do
    reg l.option l.default.name s!"the level of the lint `{l.name}`: allow, expect, warn, deny or forbid"
  for g in Core.Group.all do
    reg g.option g.default.name s!"the level of each lint of the group `{g.name}`: allow, expect, warn, deny or forbid"

/-- The hidden option holding the expectation of a lint at `expect`. -/
def expectationOption (l : Core.Lint) : Name := l.option ++ `expectation

/-- The hidden option holding the identifier of the `set_option` in the
file that set a lint's level (`unused_lint_setting`,
`LocalState.settingIds`). -/
def settingOption (l : Core.Lint) : Name := l.option ++ `setting

/-- The hidden option marking a lint's level as set by its group's
`set_option` in the file. -/
def viaGroupOption (l : Core.Lint) : Name := l.option ++ `via_group

def levelOption? (opts : Options) (n : Name) : Option Core.LintLevel :=
  match opts.find? n with
  | some (.ofString s) => Core.LintLevel.ofName? s
  | _ => none

/-- A lint's level here, from the options. In the file, a group's
`set_option` sets each of its lints' options, in order with theirs; outside
it, the lint's own option wins over its group's (`lint::outside_options`). -/
def lintLevel [Monad m] [MonadOptions m] (l : Core.Lint) : m Core.LevelInEffect := do
  let opts ← getOptions
  let own? := levelOption? opts l.option
  let group? := levelOption? opts l.group.option
  if own?.isNone && group?.isNone then return .ofDefault l
  let level := Core.outsideLevel l.default own? group?
  let expectation? := match opts.find? (expectationOption l) with
    | some (.ofNat n) => some n
    | _ => none
  let viaGroup := own?.isNone || opts.getBool (viaGroupOption l)
  let setting? := match opts.find? (settingOption l) with
    | some (.ofNat n) => some n
    | _ => none
  return { level, isSet := true, group? := if viaGroup then some l.group else none, expectation?, setting? }

variable {m : Type → Type} [Monad m] [MonadEnv m] [MonadOptions m]

/-- Records that a path's first segment resolved through an import. -/
def recordUsed (u : Core.UsedName) : m Unit :=
  modifyLocal fun l => { l with used := l.used.push u }

/-- Records a `use` declared in this file, with the levels here. -/
def recordUse (u : Core.UseDef) (ref : Syntax) : m Unit := do
  let r : Core.UseRecord := {
    module := u.scope, target := u.target, glob := u.glob
    unusedLevel := ← lintLevel .unusedImports, globLevel := ← lintLevel .globImports }
  modifyLocal fun l => { l with useRecords := l.useRecords.push (r, ref) }

/-- Records a lint's message at `ref`, at the level here. -/
def recordLint (lint : Core.Lint) (ref : Syntax) (msg : Core.Msg) : m Unit := do
  let level ← lintLevel lint
  -- Once at a place: a function's block gives a `let` to each expression
  -- that needs it, which elaborates it again (`Reqs/Lang/Items#function-blocks`).
  let same (r : Core.LintReport Syntax) := r.lint == lint && r.ref.getPos? == ref.getPos? && r.ref.getTailPos? == ref.getTailPos?
    && r.msg.headline == msg.headline
  if ref.getPos?.isSome && (← getLocal).lintReports.any same then return
  modifyLocal fun l => { l with lintReports := l.lintReports.push { lint, level, ref, msg } }
  if lint == .undecidable && level.level.severity? == some .error then
    modifyLocal fun l => { l with undecidableDenied := true }

/-- The comments in `t`, as byte offsets in it: in the trivia around a
token, its whitespace and comments, or in the text between two commands,
whose string literals hold no comments. -/
def triviaComments (t : String) : Array (Nat × Nat) := Id.run do
  let cs := t.toList.toArray
  let mut out := #[]
  let mut i := 0
  -- The byte offset of `cs[i]`.
  let mut b := 0
  while i < cs.size do
    if cs[i]! == '-' && cs[i + 1]? == some '-' then
      let start := b
      while i < cs.size && cs[i]! != '\n' do
        b := b + cs[i]!.utf8Size
        i := i + 1
      out := out.push (start, b)
    else if cs[i]! == '/' && cs[i + 1]? == some '-' then
      let start := b
      let mut depth := 0
      while i < cs.size do
        if cs[i]! == '/' && cs[i + 1]? == some '-' then
          depth := depth + 1
          b := b + 2
          i := i + 2
        else if cs[i]! == '-' && cs[i + 1]? == some '/' then
          depth := depth - 1
          b := b + 2
          i := i + 2
          if depth == 0 then break
        else
          b := b + cs[i]!.utf8Size
          i := i + 1
      out := out.push (start, b)
    else if cs[i]! == '"' then
      -- A raw literal is `r`, some `#`, then `"`, and has no escapes.
      let hashes := ((cs.extract 0 i).toList.reverse.takeWhile (· == '#')).length
      let raw := i ≥ hashes + 1 && cs[i - hashes - 1]! == 'r'
      let closes (k : Nat) : Bool :=
        cs[k]! == '"' && (!raw || (List.range hashes).all fun h => cs[k + 1 + h]? == some '#')
      b := b + 1
      i := i + 1
      while i < cs.size && !closes i do
        let n := if !raw && cs[i]! == '\\' then 2 else 1
        for c in cs.extract i (i + n) do b := b + c.utf8Size
        i := i + n
      let n := if raw then hashes + 1 else 1
      for c in cs.extract i (i + n) do b := b + c.utf8Size
      i := i + n
    else
      b := b + cs[i]!.utf8Size
      i := i + 1
  return out

/-- Records `invisible_characters` in the command `stx`: in its string
literals, in the comments around its tokens, and in the comments before it
that no Fren command has read, after a `set_option` or at the start of the
text (`lint::invisible_character`); and `needless_raw_strings` and
`non_ascii_literal` in its string literals, and `needless_raw_string_hashes`
in its raw string literals (`lint::needless_raw_string_hashes`). -/
partial def lintInvisible (stx : Syntax) : m Unit := do
  let fixable := (← getLocal).inMarkdown
  let help (msg : Core.Msg) := if fixable && !msg.fixes.isEmpty then msg.note Core.fixHelp else msg
  let report (ref : Syntax) (comment : Bool) (text : String) : m Unit := do
    if let some (found, fixed) := Core.invisibleFix? comment text then
      recordLint .invisibleCharacters ref (help (Core.invisibleMsg comment found fixed))
    unless comment do
      for (lint, msg) in Core.literalMsgs text do recordLint lint ref (help msg)
  let trivia (sub : Substring.Raw) : m Unit := do
    let t := sub.toString
    for (a, b) in triviaComments t do
      let pos (k : Nat) : String.Pos.Raw := ⟨sub.startPos.byteIdx + k⟩
      report (.atom (.synthetic (pos a) (pos b)) "") true (String.Pos.Raw.extract t ⟨a⟩ ⟨b⟩)
  let rec go (stx : Syntax) : m Unit := do
    match stx with
    | .node _ k args =>
      if k == strLitKind then
        if let some a := args[0]? then
          report stx false a.getAtomVal
          if let some fixed := Core.fewerHashes? a.getAtomVal then
            let msg := Core.needlessRawHashesMsg fixed
            recordLint .needlessRawStringHashes stx (if fixable then msg.note Core.fixHelp else msg)
      for a in args do go a
    | .atom (.original leading _ trailing _) _ | .ident (.original leading _ trailing _) .. =>
      trivia leading
      trivia trailing
    | _ => pure ()
  if let .original leading .. := stx.getHeadInfo then
    let from_ := (← getLocal).invisibleFrom
    if from_ < leading.startPos.byteIdx then trivia { leading with startPos := ⟨from_⟩, stopPos := leading.startPos }
  go stx
  if let .original _ _ trailing _ := stx.getTailInfo then
    modifyLocal fun l => { l with invisibleFrom := trailing.stopPos.byteIdx }

/-- The settings in the file that set `lints` here (`unused_lint_setting`). -/
def settingsHere (lints : Array Core.Lint := Core.Lint.all) : m (Array Nat) := do
  let opts ← getOptions
  return lints.filterMap fun l => match opts.find? (settingOption l) with
    | some (.ofNat n) => some n
    | _ => none

/-- Records that the settings that set `lints` here are in effect at an
item, or at a setting that reads their level (`unused_lint_setting`). -/
def noteSettingsSeen (lints : Array Core.Lint := Core.Lint.all) : m Unit := do
  let here ← settingsHere lints
  let add (acc : Array Nat) (i : Nat) := if acc.contains i then acc else acc.push i
  modifyLocal fun l => { l with seenSettings := here.foldl add l.seenSettings }

/-- Records what the lints need at the start of the item `stx`: its
invisible characters, and that the settings here are in effect at an item. -/
def lintItem (stx : Syntax) : m Unit := do
  noteSettingsSeen
  lintInvisible stx

/-- Records the item that a resolved path uses (`dead_code`). -/
def recordUsedItem (r : Core.Resolved) : m Unit :=
  modifyLocal fun l => { l with usedItems := l.usedItems.push r.usedItem }

/-- Records a private enumeration or constant declared here, with the level
of `dead_code` here, and for a defined function, of `single_call_fn`. -/
def recordItem (what : Core.Named) (path : Name) (ref : Syntax) (defined : Bool := false) : m Unit := do
  let singleCall? ← if defined then some <$> lintLevel .singleCallFn else pure none
  let r : Core.ItemRecord := { what, path, level := ← lintLevel .deadCode, singleCall? }
  modifyLocal fun l => { l with items := l.items.push (r, ref) }

/-- Records the lints about a declared name alone (`Core.nameMsgs`): its
case (`lint::naming_case`), and the lints of the `style` and `restriction`
groups that look only at the name, at the level here; and, for an item
other than a module, `module_name_repetitions`. -/
def lintName (what : Core.Named) (n : Name) (ref : Syntax) : m Unit := do
  if n.toString.startsWith "#match" then return
  for (lint, msg) in Core.nameMsgs what n do
    recordLint lint ref msg
  unless what matches .module do
    if let some msg := Core.moduleNameMsg? what (← getLocal).currentModule n then
      recordLint .moduleNameRepetitions ref msg
  if what matches .variable | .instance | .binder then
    modifyLocal fun l => { l with declaredNames := l.declaredNames.push (n, ref) }

/-- Starts an item whose declared names `lintDeclared` checks. -/
def startDeclared : m Unit := modifyLocal fun l => { l with declaredNames := #[] }

/-- Records `many_single_char_names` and `similar_names` on the names that
the `what` named `n`, at `ref`, declares (`lint::many_single_char_names`,
`lint::similar_names`): each name once, in source order. -/
def lintDeclared (what : Core.Named) (n : Name) (ref : Syntax) : m Unit := do
  let pos (r : Syntax) := (r.getPos?.map (·.byteIdx)).getD 0
  -- Each name once, where it is first declared: `x!` declares `x` again.
  let ds := (← getLocal).declaredNames.qsort fun a b => pos a.2 < pos b.2
  let ds := ds.foldl (init := #[]) fun acc d => if acc.any (·.1 == d.1) then acc else acc.push d
  modifyLocal fun l => { l with declaredNames := #[] }
  let single := ds.filter (Core.singleChar ·.1)
  if Core.manySingleCharNames single.size then
    recordLint .manySingleCharNames ref (Core.manySingleCharNamesMsg what n (single.map (·.1)))
  for i in [0:ds.size] do
    if let some a := (ds.extract 0 i).find? (Core.namesSimilar ·.1 ds[i]!.1) then
      recordLint .similarNames ds[i]!.2 (Core.similarNamesMsg a.1 ds[i]!.1 what n)

/-- The lints of the file, or Markdown spec, elaborated so far, with their
severities. -/
def pendingLints : CommandElabM (Array (Core.LintReport Syntax × Core.Severity)) := do
  let l ← getLocal
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := l.inMarkdown
  -- The settings' indices in `l.settings`, from their identifiers.
  let atEnd := (← settingsHere).filterMap l.settingIds.idxOf?
  let seen := l.seenSettings.filterMap l.settingIds.idxOf?
  let nats := l.natReports.filterMap fun (c, x, r) => if l.natKept.contains (c, x) then none else some r
  let (reports, fulfilled) := Core.finishReports
    (l.lintReports ++ nats ++ Core.importReports l.useRecords l.used fixable ++ Core.deadCodeReports l.items l.usedItems
      ++ Core.unusedAssumptionReports l.assumptions l.globalReads
      ++ Core.unusedSettingReports l.settings seen atEnd fixable
      ++ Core.singleCallReports l.items l.usedItems)
  let (unfulfilled, _) := Core.finishReports (Core.expectationReports l.expectations fulfilled fixable)
  return reports ++ unfulfilled

/-- Reports the lints of the file, or Markdown spec, just elaborated, and
forgets them. -/
def reportLints : CommandElabM Unit := do
  for (r, sev) in ← pendingLints do
    match sev with
    | .error => logErrorAt r.ref r.msg.text
    | .warning => logWarningAt r.ref r.msg.text
    | .info => logInfoAt r.ref r.msg.text
  modifyLocal fun l => { l with useRecords := #[], used := #[], expectations := #[], lintReports := #[],
                                items := #[], usedItems := #[], natReports := #[], natKept := #[], settings := #[], settingIds := #[],
                                seenSettings := #[], assumptions := #[], globalReads := #[] }

/-- `set_option fren.lint.NAME "LEVEL"`, for a lint (`lint::setting`) or a
group (`lint::group_setting`), which sets each of its lints. Other options,
and lints that do not exist, are left to Lean. -/
@[command_elab Lean.Parser.Command.set_option] def elabLintOption : CommandElab := recordingErrors fun stx => do
  let name := stx[1].getId.eraseMacroScopes
  let some target := (Core.Lint.all.map Core.LintTarget.lint ++ Core.Group.all.map Core.LintTarget.group).find?
    (·.option == name) | throwUnsupportedSyntax
  let some v := stx[3].isStrLit? | throwUnsupportedSyntax
  let some requested := Core.LintLevel.ofName? v | throwErrorAt stx[3] (Core.invalidLevelMsg v).text
  let levels ← target.members.mapM fun l => return (l, (← lintLevel l).level)
  -- A forbidden lint's setting decides whether this one is accepted.
  noteSettingsSeen (Core.settingLints ++ (levels.filter (·.2 == .forbid)).map (·.1))
  let levelOf (l : Core.Lint) := ((levels.find? (·.1 == l)).map (·.2)).getD l.default
  if let some lint := target.rejectedBy? levelOf requested then
    throwErrorAt stx (Core.forbiddenMsg target lint requested).text
  -- `allow_attributes` (`lint::allow_attributes`), at the level before the setting.
  let (allows, fix) := Core.allowAttributes requested (target == .lint .unfulfilledExpectations)
  if allows then
    let msg := Core.allowAttributesMsg target fix
    recordLint .allowAttributes stx[3] (if fix && (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  let (opts, _) ← Elab.elabSetOption stx[1] stx[3]
  let expectation? ← if requested == .expect then do
      let e : Core.ExpectationRecord := { target, level := ← lintLevel .unfulfilledExpectations }
      let n := (← getLocal).expectations.size
      modifyLocal fun l => { l with expectations := l.expectations.push (e, stx) }
      pure (some n)
    else pure none
  -- `unused_lint_setting` (`lint::unused_lint_setting`).
  let before ← target.members.mapM fun l => return (l, ← lintLevel l)
  let r : Core.SettingRecord := { target, requested, level := ← lintLevel .unusedLintSetting }
  let n := (← getLocal).nextSetting
  modifyLocal fun l =>
    -- The settings it replaces, as indices in `l.settings`: one of the Lean
    -- file's, in effect in a spec, is not there, and is recorded apart.
    let outer := (target.members.filterMap fun lint => (Core.Levels.get before lint).setting?).filter
      (!l.settingIds.contains ·)
    let before (lint : Core.Lint) := let e := Core.Levels.get before lint
      { e with setting? := e.setting?.bind l.settingIds.idxOf? }
    { l with settings := (Core.SettingRecord.replace l.settings before target requested).push (r, stx)
             settingIds := l.settingIds.push n, nextSetting := n + 1
             outerReplaced := l.outerReplaced ++ outer.map (·, target, requested) }
  let opts := target.members.foldl (init := opts) fun opts lint =>
    let opts := opts.insert lint.option (.ofString v)
    let opts := opts.insert (settingOption lint) (.ofNat n)
    let opts := match expectation? with
      | some n => opts.insert (expectationOption lint) (.ofNat n)
      | none => opts.erase (expectationOption lint)
    if target matches .group _ then opts.insert (viaGroupOption lint) (.ofBool true) else opts.erase (viaGroupOption lint)
  modifyScope fun scope => { scope with opts }

/-- Reports the file's lints at its end. -/
def lintsAtEnd : ModuleLinter where
  run _ := do
    unless (← getLocal).inMarkdown do reportLints

initialize addModuleLinter lintsAtEnd

end Fren

end

/-!
## Name resolution

Adapts Fren's scoping rules (`FrenCore.Names`) to Lean syntax: errors are
reported at the offending path segment. It is part of this module, which it
needs, rather than a module of its own, which would be one more module on
the build's longest chain, and each costs seconds of importing alone.
-/

section
open Lean

namespace Fren

export Core (Resolved showPath showModule)

/-- A single path segment as a simple name, rejecting Lean-style dotted names.
`afterPath` says that it follows a `::`. -/
def segName [Monad m] [MonadError m] (seg : Syntax) (afterPath := false) : m Name := do
  let n := seg.getId
  unless n.isAtomic do
    throwErrorAt seg (Core.dottedNameMsg n #[] (inExpr := false) (afterPath := afterPath)).text
  return n

/-- The segments of a path as simple names. -/
def segNames [Monad m] [MonadError m] (segs : Array Syntax) : m (Array Name) :=
  segs.mapIdxM fun i s => segName s (afterPath := i > 0)

variable {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m]

def liftResolve (segs : Array Syntax) : Except Core.Error α → m α
  | .ok a => pure a
  | .error e => do
    let seg := segs[e.seg]?.getD .missing
    let src := (← getFileMap).source
    let beforeEq := seg.getTailPos?.any fun p => p.get src == '='
    throwErrorAt seg (Core.withBangEqFix e.msg.get (Core.nameText seg.getId) beforeEq).text

def liftMsg (ref : Syntax) : Except Core.Msg α → m α
  | .ok a => pure a
  | .error msg => throwErrorAt ref msg.text

/-- The identifier that `x` declares, without the `!` that marks it as
shadowing (`Core.declaredName`), and whether it has one. Its range leaves
out the `!`, as the `fren` command's does, so that a fix that renames it
keeps the `!`. -/
def declaredIdent (x : Syntax) : Syntax × Bool :=
  let (n, bang) := Core.declaredName x.getId
  if !bang then (x, false) else
  match x.getPos?, x.getTailPos? with
  | some p, some e => (Syntax.ident (.synthetic p ⟨e.byteIdx - 1⟩ true) n.toString.toRawSubstring n [], true)
  | _, _ => (mkIdentFrom x n, true)

/-- The declaration `x` in `scope`, without its `!`, checked to be written
with `!` exactly when it hides something there or among `locals`
(`lang::shadowing`). An import that brings in what it hides counts as
used. -/
def declare (x : Syntax) (scope : Name) (locals : Core.Locals := #[]) : m Syntax := do
  let (y, bang) := declaredIdent x
  if y.getId.toString.startsWith "#match" then return y
  let table := (← getState).table
  liftMsg x (Core.checkDeclaredName y.getId bang)
  liftMsg x (Core.checkShadowing y.getId (table.hidden? scope locals y.getId) bang)
  if let some u := table.shadowedImport? scope locals y.getId bang then recordUsed u
  return y

/-- Resolves a `use` path written in module `from_`. -/
def resolveUsePath (from_ : Name) (segs : Array Syntax) : m Resolved := do
  liftResolve segs ((← getState).table.resolveUse from_ (← segNames segs))

/-- Resolves a path in an expression or type in module `from_`, recording
the import it resolves through, if any (`unused_imports`), and the item it
uses (`dead_code`). -/
def resolvePath (from_ : Name) (segs : Array Syntax) (extra : Array Name := #[]) : m Resolved := do
  let names ← segNames segs
  let table := (← getState).table
  let r ← liftResolve segs (table.resolvePath from_ names extra)
  if let some u := table.importVia from_ names then recordUsed u
  recordUsedItem r
  return r

/-- `resolvePath` for a path written in an expression, a pattern or a type,
which also records `absolute_paths` (`lint::absolute_paths`) if `report`:
an expression translated again, as a trigger is, records nothing. -/
def resolveWritten (from_ : Name) (segs : Array Syntax) (extra : Array Name := #[]) (report : Bool := true) : m Resolved := do
  let r ← resolvePath from_ segs extra
  if report then
    if let some msg := Core.absolutePathMsg? (← segNames segs) r then recordLint .absolutePaths (mkNullNode segs) msg
  return r

/-- The generated Lean inductive for an enum. -/
def enumDecl (path : Name) : m Name := do
  match (← getState).enums.get? path with
  | some e => return e.decl
  | none => throwError "internal error: unknown enum `{path}`"

end Fren

end
