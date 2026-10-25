-- keep-sorted start
import FrenTest.Ui
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# Each front end's messages

The messages that either front end reports about a `.fren` file, as
`Diagnostic`s, for the ui tests (`FrenTestMain`) and the front-end fuzzer
(`FrenFuzz`, `--frontends`): the binary's from its rendered output, and the
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
text is its headline, then its `= note` lines and `help:` suggestions. -/
def cliDiagnostics (file : String) (out : String) : Array Diagnostic × Option String := Id.run do
  let mut diags : Array Diagnostic := #[]
  let mut summary := none
  -- A header whose ` --> ` line is still to come
  let mut pending : Option (String × Option String × String) := none
  for line in out.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if let some h := header? line then
      pending := some h
    else if let some loc := trimmed.dropPrefix? "--> " then
      if let some (sev, code?, text) := pending then
        -- `file:line:col`
        let parts := loc.toString.splitOn ":"
        if parts.length ≥ 3 && ":".intercalate (parts.take (parts.length - 2)) == file then
          diags := diags.push { line := parts[parts.length - 2]!.toNat!, severity := sev, text, code? }
        else diags := diags.push { line := 0, severity := "other-file", text }
      pending := none
    else if line.startsWith "fren: " then
      summary := some (line.drop 6).toString
    else if let some d := diags.back? then
      if let some n := trimmed.dropPrefix? "= " then
        diags := diags.pop.push { d with text := d.text ++ "\n" ++ n.toString }
      else if line.startsWith "help: " then
        diags := diags.pop.push { d with text := d.text ++ "\n" ++ line }
  return (diags.filter (·.severity != "other-file"), summary)

/-- The Lean front end's messages about the Fren source `src`, and its
summary. Its messages have no codes. -/
def hostedDiagnostics (env : Environment) (file : String) (src : String) :
    IO (Array Diagnostic × Option String) := do
  -- One line of header; message lines are shifted back below.
  let input := "open Fren.Lang\n" ++ src ++ "\n#fren_check\n"
  let (_, log) ← Elab.process input env {} file
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
    else
      diags := diags.push { line := m.pos.line - 1, severity := sev, text }
  return (diags, summary)

end FrenTest.Ui
