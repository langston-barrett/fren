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
Lake replaces the file name of every message with the module's. For the
same reason `#fren_check` should be in a block too, since a `#fren_check`
after `#fren_md` would report positions in the Markdown file against this
file's text.

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
  modifyLocal fun l => { l with useRecords := #[], used := #[], expectations := #[], lintReports := #[],
                                items := #[], usedItems := #[], inMarkdown := true }
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
  let msgs := inner.messages.toList.map fun m =>
    { m with fileName, pos, endPos, data := m!"{rel}:{m.pos.line}:{m.pos.column}: " ++ m.data }
  -- Info trees refer to the Markdown file's text, so they are dropped.
  set { inner with messages := msgs.foldl (·.add) s.messages, infoState := s.infoState }
  modifyLocal fun l => { l with useRecords := outer.useRecords, used := outer.used,
                                expectations := outer.expectations, lintReports := outer.lintReports,
                                items := outer.items, usedItems := outer.usedItems, inMarkdown := outer.inMarkdown }

end Fren
