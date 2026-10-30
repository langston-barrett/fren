-- keep-sorted start
import FrenCore.Check
import FrenTest.Ui
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# Each front end's messages

The messages that either front end reports about a `.fren` file, as
`Diagnostic`s, for the ui tests (`FrenTestMain`) and the front-end fuzzer
(`fren_fuzz_frontends`, in `FrenFuzzFrontends`): the binary's from its rendered output, and the
Lean front end's from elaborating the file in an environment that imports
`Fren`.
-/

open Lean

namespace FrenTest.Ui

/-- The header of a rendered diagnostic, `error[F0105]: text`: its severity
(`note` is `info`), code and text. -/
def header? (line : String) : Option (String × Option String × String) :=
  [("error", "error"), ("warning", "warning"), ("note", "info")].findSome? fun (label, sev) => do
    let rest ← (line.dropPrefix? label).map (·.toString)
    let (code?, rest) :=
      if rest.startsWith "[" then
        match rest.drop 1 |>.toString.splitOn "]" with
        | c :: more => (some c, "]".intercalate more)
        | [] => (none, rest)
      else (none, rest)
    let text ← (rest.dropPrefix? ": ").map (·.toString)
    return (sev, code?, text)

/-- The binary's messages about `file`, and its summary line. A message's
text is its headline, then its `= note` lines and `help:` suggestions. With
`keepUnlocated`, a message without a location (such as an internal error)
is kept, on line 0; otherwise it is dropped, as are messages about other
files. -/
def cliDiagnostics (file : String) (out : String) (keepUnlocated := false) : Array Diagnostic × Option String := Id.run do
  -- Each message, and whether to keep it: located in `file`, or unlocated
  -- and kept.
  let mut diags : Array (Diagnostic × Bool) := #[]
  let mut summary := none
  -- Whether the last header's ` --> ` line may still come.
  let mut pending := false
  -- Where the text of the last `= note` line starts, for the lines of a
  -- note that spans several (`Fren.Core.noteRows`).
  let mut noteAt? : Option Nat := none
  for line in out.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if let some (sev, code?, text) := header? line then
      diags := diags.push ({ line := 0, severity := sev, text, code? }, keepUnlocated)
      pending := true
      noteAt? := none
    else if let some loc := trimmed.dropPrefix? "--> " then
      if pending then
        -- `file:line:col`
        let parts := loc.toString.splitOn ":"
        let ours := parts.length ≥ 3 && ":".intercalate (parts.take (parts.length - 2)) == file
        diags := diags.modify (diags.size - 1) fun (d, _) =>
          ({ d with line := if ours then parts[parts.length - 2]!.toNat! else 0 }, ours)
      pending := false
    else if line.startsWith "fren: " then
      summary := some (line.drop 6).toString
    else if let some (d, k) := diags.back? then
      if let some n := trimmed.dropPrefix? "= " then
        diags := diags.pop.push ({ d with text := d.text ++ "\n" ++ n.toString }, k)
        noteAt? := some ((line.toList.takeWhile (· == ' ')).length + 2)
      else if line.startsWith "help: " then
        diags := diags.pop.push ({ d with text := d.text ++ "\n" ++ line }, k)
        noteAt? := none
      else if let some at_ := noteAt? then
        -- A later line of a note, indented under its text.
        if line.length > at_ && (line.take at_).all (· == ' ') then
          diags := diags.pop.push ({ d with text := d.text ++ "\n" ++ (line.drop at_).toString }, k)
        else noteAt? := none
  return (diags.filterMap fun (d, k) => if k then some d else none, summary)

/-- The Lean front end's messages about the Fren source `src`, and its
summary. Its messages have no codes. -/
def hostedDiagnostics (env : Environment) (file : String) (src : String) :
    IO (Array Diagnostic × Option String) := do
  -- One line of header; message lines are shifted back below.
  let input := "open Fren.Lang\n" ++ src ++ "\n#fren_check\n"
  let (_, log) ← Elab.process input env {} file
  -- The lines of `src`; a message below them is at the `#fren_check` added
  -- above, which has no line in `src`.
  let lines := (src.splitOn "\n").length
  let mut diags := #[]
  let mut summary := none
  for m in log.toList do
    let text := (← m.data.toString).trimAscii.toString
    let sev := match m.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "info"
    if sev == "info" && text.startsWith "fren: " then
      summary := some (text.drop 6).toString
    -- At the `#fren_check` added above: the counterpart of the binary's
    -- last line after a static error, which has no location, and so has
    -- none here either; and any other message there, such as an error
    -- that stops the whole check (`--~$`).
    else if (sev == "error" && text == Fren.Core.couldNotHeadline) || m.pos.line - 1 > lines then
      diags := diags.push { line := 0, severity := sev, text }
    else
      diags := diags.push { line := m.pos.line - 1, severity := sev, text }
  return (diags, summary)

end FrenTest.Ui
