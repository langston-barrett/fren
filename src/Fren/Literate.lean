-- keep-sorted start
import Fren.View
import FrenCore.Literate
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# `#fren_md`: Markdown specs

`#fren_md "file.md"` elaborates the ```` ```fren ```` blocks of a Markdown
file (`Fren.Core.unwrapMarkdown`), with the path relative to the current
file, as if they were written in place of the command.

Messages about the blocks are logged at the command, with text starting
`file.md:line:col:`, except those about the Lean file's own items, which
are logged at the items. They cannot simply carry the Markdown file's name:
Lake replaces the file name of every message with the module's. A spec is
named by its path relative to the Lean file, with `.` and `..` resolved,
even when another spec reads it. The messages of a spec that another reads
are labelled once, by it, and placed at the outermost command
(`Fren.mdLabelled`). An item's syntax has positions in the text of the file
that declares it, so each
spec's item is recorded with that text as it is declared (`mdSources`, from
`mdSource?`), even in a spec that another spec reads, and the Lean file's
text is kept while a spec is read (`leanFile?`). `Fren.logAbout` places each
message about an item by its own file's text, wherever it is checked: a
spec's item at this command, with the spec's name and the position in its
text, and the Lean file's item at its own position.

Lake does not see the dependency on the Markdown file; the library declares
it with `needs`.
-/

open Lean Elab Command

namespace Fren

namespace Lang

scoped syntax (name := mdCmd) "#fren_md " str : command

end Lang

/-- The components of `path`, so that two spellings of one path agree: an
absolute path's root first (`""`, or a drive such as `C:`), then the rest
without `.` or empty components, and with each `..` cancelling the
component before it. At the root, `..` stays at the root. -/
def pathComponents (path : System.FilePath) : List String :=
  let (root, rest) := match path.components with
    | r :: cs => if path.isAbsolute then ([r], cs) else ([], r :: cs)
    | [] => ([], [])
  let parts := rest.foldl (init := []) fun acc c =>
    if c == "." || c == "" then acc
    else if c == ".." then match acc with
      | p :: ps => if p == ".." then c :: acc else ps
      | [] => if root.isEmpty then [c] else []
    else c :: acc
  root ++ parts.reverse

/-- `path` relative to the directory `base`, both normalized
(`pathComponents`), with a `..` for each component of `base` that `path`
does not share, joined with `/` on every system, as names in messages are.
A path that shares no root with `base`, such as an absolute path from a
relative `base`, is kept whole. `base` itself is `.`, and a bare root is
`/`. -/
def relativeTo (base path : System.FilePath) : String :=
  let rec strip : List String → List String → List String
    | b :: bs, p :: ps => if b == p then strip bs ps else (b :: bs).map (fun _ => "..") ++ p :: ps
    | bs, ps => bs.map (fun _ => "..") ++ ps
  let b := pathComponents base
  let p := pathComponents path
  let shared := base.isAbsolute == path.isAbsolute && (!path.isAbsolute || b.head? == p.head?)
  match if shared then strip b p else p with
  | [] => "."
  | [""] => "/"
  | cs => "/".intercalate cs

@[command_elab Lang.mdCmd] def elabMd : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
  openGenerated
  let some rel := stx[1].isStrLit? | throwUnsupportedSyntax
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "cannot compute the directory of `{← getFileName}`"
  let path := dir / rel
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok src => pure src
    | .error e => throwErrorAt stx[1] "could not read `{path}`: {e}"
  let code := Core.unwrapMarkdown src
  -- Lean's parser rejects input that is only whitespace, as when a file is
  -- all prose.
  if code.trimAscii.isEmpty then return
  let inputCtx := Parser.mkInputContext code path.toString
  -- The spec's lints are its own, reported at its end (`Reqs/Lint`), here
  -- rather than by the end-of-file linter, whose messages would bypass the
  -- relocation below.
  let outer ← getLocal
  -- The Lean file's text, for its own items' messages; a spec read by a spec
  -- keeps the outermost. What this spec declares is recorded with its text
  -- as it is declared (`LocalState.declared`).
  let leanFile? ← if outer.inMarkdown then pure outer.leanFile? else pure (some (← getFileName, ← getFileMap))
  -- Its name in messages: its path relative to the Lean file, normalized,
  -- even when another spec reads it, so that every spelling of it agrees.
  let leanName := (leanFile?.map (·.1)).getD (← getFileName)
  let name := relativeTo ((System.FilePath.mk leanName).parent.getD ".") path
  modifyLocal fun l => { l with useRecords := #[], used := #[], expectations := #[], lintReports := #[],
                                items := #[], usedItems := #[], natReports := #[], natKept := #[], inMarkdown := true, leanFile?,
                                mdSource? := some (name, inputCtx.fileMap), globalTexts := #[],
                                invisibleFrom := 0, settings := #[], settingIds := #[], seenSettings := #[],
                                outerReplaced := #[], assumptions := #[], globalReads := #[] }
  let s ← get
  let st ← IO.processCommands inputCtx {} { s with messages := {} }
  set st.commandState
  -- The Lean file's settings in effect at the spec's items, which are its
  -- items too.
  let seen := (← getLocal).seenSettings
  -- The Lean file's settings that the spec's replace, which name them.
  let replaced := (← getLocal).outerReplaced
  let (settings, further) := replaced.foldl (init := (outer.settings, outer.outerReplaced))
    fun (ss, rest) (i, target, requested) => match outer.settingIds.idxOf? i with
      | some k => (ss.modify k fun (r, ref) => ({ r with replacedBy? := some (target, requested) }, ref), rest)
      | none => (ss, rest.push (i, target, requested))
  withReader (fun ctx => { ctx with fileName := path.toString, fileMap := inputCtx.fileMap }) reportLints
  let inner ← get
  let some range := (← getRef).getRange? | throwError "`#fren_md` has no position"
  let fileMap ← getFileMap
  let pos := fileMap.toPosition range.start
  let endPos := fileMap.toPosition range.stop
  let fileName ← getFileName
  -- A message about another spec's item already names that spec, and one
  -- about the Lean file's item is placed in it (`Fren.logAbout`), even
  -- from a spec that another spec reads. Each is labelled once, by the
  -- innermost `#fren_md`, and placed at the outermost.
  let out := if outer.inMarkdown then mdLabelled else fileName
  let msgs := inner.messages.toList.map fun m =>
    if m.fileName == leanName then m
    else if m.fileName == mdLabelled then { m with fileName := out, pos, endPos }
    else
      let shown := if m.fileName == path.toString then name else m.fileName
      { m with fileName := out, pos, endPos, data := m!"{shown}:{m.pos.line}:{m.pos.column}: " ++ m.data }
  -- Info trees refer to the Markdown file's text, so they are dropped.
  set { inner with messages := msgs.foldl (·.add) s.messages, infoState := s.infoState }
  -- The spec's static errors, its parse errors and lints included, are
  -- those of this command, for the `#fren_check`s after it: all its errors
  -- but its checks'.
  let errors := inner.messages.toList.filter (·.severity == .error) |>.length
  let static := errors - ((← getLocal).checkErrors - outer.checkErrors)
  let cmdPos := (← read).cmdPos.byteIdx
  let staticErrors := if static == 0 then outer.staticErrors
    else outer.staticErrors.push (fileName, cmdPos, static)
  modifyLocal fun l => { l with useRecords := outer.useRecords, used := outer.used,
                                expectations := outer.expectations, lintReports := outer.lintReports,
                                natReports := outer.natReports, natKept := outer.natKept,
                                items := outer.items, usedItems := outer.usedItems, inMarkdown := outer.inMarkdown,
                                leanFile? := outer.leanFile?, mdSource? := outer.mdSource?, globalTexts := outer.globalTexts,
                                invisibleFrom := outer.invisibleFrom, staticErrors, settings,
                                outerReplaced := further,
                                settingIds := outer.settingIds, seenSettings := outer.seenSettings ++ seen,
                                assumptions := outer.assumptions,
                                globalReads := outer.globalReads }

end Fren
