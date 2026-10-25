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
`file.md:line:col:`. They cannot simply carry the Markdown file's name:
Lake replaces the file name of every message with the module's. An item's
syntax has positions in the text of the file that declares it, so each
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

@[command_elab Lang.mdCmd] def elabMd : CommandElab := fun stx => do
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
  modifyLocal fun l => { l with useRecords := #[], used := #[], expectations := #[], lintReports := #[],
                                items := #[], usedItems := #[], inMarkdown := true, leanFile?,
                                mdSource? := some (rel, inputCtx.fileMap) }
  let s ← get
  let st ← IO.processCommands inputCtx {} { s with messages := {} }
  set st.commandState
  withReader (fun ctx => { ctx with fileName := path.toString, fileMap := inputCtx.fileMap }) reportLints
  let inner ← get
  let some range := (← getRef).getRange? | throwError "`#fren_md` has no position"
  let fileMap ← getFileMap
  let pos := fileMap.toPosition range.start
  let endPos := fileMap.toPosition range.stop
  let fileName ← getFileName
  -- A message about another spec's item already names that spec, and one
  -- about the Lean file's item is placed in it (`Fren.logAbout`), even
  -- from a spec that another spec reads.
  let leanName := (leanFile?.map (·.1)).getD fileName
  let msgs := inner.messages.toList.map fun m =>
    if m.fileName == leanName then m else
    let shown := if m.fileName == path.toString then rel else m.fileName
    { m with fileName, pos, endPos, data := m!"{shown}:{m.pos.line}:{m.pos.column}: " ++ m.data }
  -- Info trees refer to the Markdown file's text, so they are dropped.
  set { inner with messages := msgs.foldl (·.add) s.messages, infoState := s.infoState }
  modifyLocal fun l => { l with useRecords := outer.useRecords, used := outer.used,
                                expectations := outer.expectations, lintReports := outer.lintReports,
                                items := outer.items, usedItems := outer.usedItems, inMarkdown := outer.inMarkdown,
                                leanFile? := outer.leanFile?, mdSource? := outer.mdSource? }

end Fren
