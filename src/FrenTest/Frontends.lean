-- keep-sorted start
import FrenCore.Check
import FrenTest.Ui
-- keep-sorted end

/-!
# Comparing the front ends' reports

How the reports of the two front ends on one spec differ, once what
legitimately differs is normalized away (`Reqs/dev/Testing`, "Front-end
fuzzing"). `fren_fuzz_frontends` compares the front ends with it;
`FrenTest.FrontendsCompare` tests it.

- A parse error (`F01xx`) stops the binary, but Lean recovers at the next
  command: Lean must then report a parse error (`isLeanParseError`) in the
  same item, at or before the parse error's line, and nothing else is
  compared.
- A parse error of Lean's (`isLeanParseError`) stands for the binary's
  static errors on the same line, as `--~[hosted]` does in the ui tests,
  but not for its checks' results. Every other message must agree, type
  errors included. A Lean error with no error of the binary on its line is
  always reported.
- Messages are compared by line, column, severity and first line, with the values
  of a model masked (`normHead`). The requirements that a realizability
  failure names in its note, which are a minimal set that conflicts on its
  input, which comes from the solver's model (`cli::agreement`), are
  compared only when both front ends report the same input
  (`conflictInput?`, `conflictCore?`), and so are its notes at them
  (`isConflictNote`): the outputs that they force to different values, or
  whom they conflict with, which must then be the same in both, at the
  same lines.
- Checks whose evidence is testing, which Lean does not run, are left out.
- A static error, including a denied lint, stops both front ends'
  checks, so neither reports results or a summary. Both report the lints
  of an item with a static error.
- Both front ends say that a static error stopped the checks
  (`isStoppedTrailer`), or neither does; even after a parse error.
- The binary's exit code must follow from Lean's messages
  (`cli::agrees_with_build`): 2 after a static error, else 1 when Lean
  reports an error, 3 when it reports a warning, and 0 otherwise; unless a
  check is tested.
-/

namespace FrenTest.Frontends

open FrenTest.Ui (Diagnostic)

/-- The first line of a message. -/
def headOf (d : Diagnostic) : String := (d.text.splitOn "\n").head!

/-- Replaces the text between `start` and the first `stop` after it (or
the end) with `…`. -/
def maskBetween (s start : String) (stops : List String) : String :=
  match s.splitOn start with
  | pre :: rest@(_ :: _) =>
    let after := start.intercalate rest
    let cut := stops.filterMap fun st => match after.splitOn st with
      | a :: b :: more => some (a.length, st ++ st.intercalate (b :: more))
      | _ => none
    let tail := ((cut.toArray.qsort (·.1 < ·.1))[0]?.map (·.2)).getD ""
    pre ++ start ++ "…" ++ tail
  | _ => s

/-- The first line of a message, with the values of a model masked:
counterexample values may differ (`cli::agreement`), and the Lean front end
may show none. Other names, such as those of a vacuity's constraints, are
kept. The solver's reason for an undecided check, its own words, is
dropped. -/
def normHead (text : String) : String :=
  let head := (text.splitOn "\n").head!
  let head := if head.startsWith "could not decide whether " then (head.splitOn ": ").head! else head
  -- `… is not determined by the inputs: for the input VALUES, it can be A or B`.
  let head := maskBetween head ": for the input " [", it can be "]
  maskBetween head ", it can be " []

/-- The lines of a realizability failure's note (`Fren.Core.conflictNote`),
trimmed, if `text` is one's: its input, one variable to a line, and then
the line that names the requirements. -/
def conflictLines? (text : String) : Option (List String) :=
  let lines := text.splitOn "\n" |>.map (·.trimAscii.toString)
  if !(lines.head!.endsWith " is not realizable") then none else
  match lines.dropWhile fun l => !l.startsWith "note: for the input" && !l.startsWith "note: no outputs satisfy " with
  | [] => none
  | first :: rest =>
    if first.startsWith "note: no outputs satisfy " then some [first.drop 6 |>.toString]
    else
      let (input, more) := rest.span fun l => !l.startsWith "no outputs satisfy "
      some (input ++ more.take 1)

/-- The input of a realizability failure, on which the requirements it
names conflict (`cli::agreement`): its variables, one to a line. -/
def conflictInput? (text : String) : Option String :=
  (conflictLines? text).map fun ls => "\n".intercalate ls.dropLast

/-- The requirements that a realizability failure names, as its note's
last line names them. -/
def conflictCore? (text : String) : Option String :=
  (conflictLines? text).bind (·.getLast?)

/-- The first line of a note at a requirement of a realizability failure
(`isConflictNote`). -/
def isConflictHead (h : String) : Bool :=
  (h.startsWith "`" && (h.splitOn "` forces ").length > 1) || h.startsWith "conflicts with `" || h == "is false for this input"

/-- A note at a requirement of a realizability failure, which depends on
the requirements that conflict on its input: that it and the rest of the
conflict force an output to different values, that it conflicts with the
rest, or that it is false, in a conflict of one. -/
def isConflictNote (d : Diagnostic) : Bool :=
  d.severity == "info" && d.code?.isNone && isConflictHead (headOf d)

/-- The text after a leading subject in backquotes, as in "`c::q` is
vacuous: …", or the whole text. -/
def afterSubject (h : String) : String :=
  if h.startsWith "`" then
    match (h.drop 1).toString.splitOn "`" with
    | _ :: rest@(_ :: _) => "`".intercalate rest
    | _ => h
  else h

/-- The headline of a check's result, as `Fren.Core.messages` and the
testing messages write it. -/
def isCheckHeadline (h : String) : Bool :=
  -- What follows the subject in backquotes after `pre`.
  let rest (pre : String) : Option String := (h.dropPrefix? (pre ++ "`")).map fun r => afterSubject ("`" ++ r.toString)
  let r := afterSubject h
  h.startsWith "could not decide whether "
  || (rest "the assumptions of ").any (·.startsWith " are unsatisfiable: ")
  || r == " is not realizable"
  || (rest "an index of ").any (· == " may be out of range")
  || (rest "a table in ").any (· == " may have no row that holds")
  || (h.startsWith "rows " && (h.splitOn " of a table in `").length > 1 && h.endsWith "` may both hold")
  || (rest "the assumption ").any (·.startsWith " of `")
  || (rest "expectation ").any (· == " does not hold")
  || (rest "cover goal ").any fun r => r == " is met" || r.startsWith " cannot be met: "
  || r.startsWith " is vacuous: its condition can never hold"
  || r.startsWith " is redundant: "
  || r.startsWith " is not determined by the inputs: for the input "
  || h.startsWith "testing found no " || h.startsWith "testing never reached `"
  || isConflictHead h

/-- A check's result, rather than a static error or a lint: by its code
where the front end shows one (the binary), else by its headline. The
binary's notes on a conflict's constraints have no code. -/
def isCheckResult (d : Diagnostic) : Bool :=
  match d.code? with
  | some c => c.startsWith "F06"
  | none => isCheckHeadline (headOf d)

/-- An error of Lean's parser, which Fren's grammar is written in: its
messages start with `unexpected` (`unexpected token 'x'; expected term`,
`unexpected identifier; expected '}'`, `unexpected end of input`), with
`expected` (`expected 'out'`), or with `unterminated`. Fren's own messages
that start with `expected` (`F0210`, `F0319`) go on with `, but`. -/
def isLeanParseError (d : Diagnostic) : Bool :=
  let h := headOf d
  d.severity == "error"
  && (h.startsWith "unexpected " || h.startsWith "unterminated "
      || (h.startsWith "expected " && !h.contains ", but "))

/-- An undecided check, for lack of time rather than a solver error. -/
def isUndecided (d : Diagnostic) : Bool :=
  (d.code? == some "F0608" || (d.code?.isNone && (headOf d).startsWith "could not decide whether `"))
  && !d.text.contains "solver error"

/-- The line of either front end when a static error stops its checks,
which has no location: the binary's last, and Lean's at the
`#fren_check` that ends the spec. -/
def isStoppedTrailer (d : Diagnostic) : Bool := d.line == 0 && headOf d == Fren.Core.couldNotHeadline

/-- The 1-based line where the top-level item containing each line of
`text` starts: an item starts at a line that is neither indented, blank, a
comment, a closing brace nor the `)` that closes a procedure's parameters
or results. -/
def itemOf (text : String) : Array Nat := Id.run do
  let mut out := #[0]
  let mut item := 0
  for line in text.splitOn "\n", k in [1:text.length + 2] do
    if !line.isEmpty && !line.startsWith " " && !line.startsWith "}" && !line.startsWith ")" && !line.startsWith "--" then
      item := k
    out := out.push item
  return out

/-- Each front end's report on a spec. -/
structure Report where
  diags : Array Diagnostic
  summary? : Option String := none
  /-- The binary's exit code; for Lean, unused (it fails when it reports
  an error). -/
  exit? : Option Nat := none
  deriving Inhabited

/-- How the front ends' reports on `text` differ: each difference as a
line, and whether all of them are about undecided checks, which the
solvers' time limits can explain. -/
def compare (text : String) (cli hosted : Report) : Array String × Bool := Id.run do
  let items := itemOf text
  let itemAt (n : Nat) := items[n]?.getD 0
  let render (who : String) (d : Diagnostic) :=
    s!"line {d.line}{if d.line == 0 then "" else s!":{d.col + 1}"}: only {who} reports {d.severity}{if who == "fren" then s!"[{d.code?.getD "-"}]" else ""}: {headOf d}"
  let cliDiags := cli.diags.filter (!isStoppedTrailer ·)
  -- Both say that a static error stopped the checks, or neither does.
  let stopped := match cli.diags.any isStoppedTrailer, hosted.diags.any isStoppedTrailer with
    | true, false => #[s!"only fren says `{Fren.Core.couldNotHeadline}`"]
    | false, true => #[s!"only Lean says `{Fren.Core.couldNotHeadline}`"]
    | _, _ => #[]
  let hosted := { hosted with diags := hosted.diags.filter (!isStoppedTrailer ·) }
  let lines := text.splitOn "\n"
  -- Whether every line strictly between `a` and `b` is blank or a comment.
  let blankBetween (a b : Nat) := (List.range (b - a - 1)).all fun k =>
    let l := (lines[a + k]?.getD "").trimAscii.toString
    l.isEmpty || l.startsWith "--"
  -- A parse error stops the binary; Lean recovers at the next command.
  if let some p := cliDiags.find? (·.code?.any (·.startsWith "F01")) then
    -- Only a parse error of Lean's can stand for it: an item is one Lean
    -- command, so any other error of Lean's in the item means that Lean
    -- parsed the line that the binary rejects. Lean places a parse error
    -- at the end of the token before the offending one, so on the
    -- binary's line or the last line before it with code; the binary
    -- parsed every line before that.
    if hosted.diags.any fun h => isLeanParseError h && h.line ≤ p.line && blankBetween h.line p.line
        && itemAt h.line == itemAt p.line then
      return (stopped, false)
    return (stopped.push (render "fren" p ++ " (and Lean reports no parse error at or just before that line, in its item)"), false)
  -- Checks whose evidence is testing, which Lean does not run.
  let anyTested := text.contains "set_option fren.evidence \"random\""
  let onTested (d : Diagnostic) := (lines[d.line - 1]?.getD "").contains "set_option fren.evidence \"random\""
  let testing (d : Diagnostic) := anyTested &&
    (d.code?.any (["F0609", "F0610", "F0612", "F0616"].contains ·) || (d.severity == "info" && (headOf d).contains " set to random testing are run by `fren check`"))
  let staticError := cliDiags.any fun d => d.severity == "error" && !isCheckResult d
  let keep (d : Diagnostic) := !onTested d && !testing d
  -- A realizability failure's requirements, and so its notes, are compared
  -- only for the same input: each front end's input comes from its model,
  -- and its requirements are a minimal set that conflicts on it.
  let sameInput := (cliDiags.filter keep).filterMap fun c => do
    let i ← conflictInput? c.text
    let h ← (hosted.diags.filter keep).find? fun h => h.line == c.line && conflictInput? h.text == some i
    let (cc, hc) := (conflictCore? c.text, conflictCore? h.text)
    guard (cc != hc)
    return s!"line {c.line}: for the same input, fren says `{cc.getD ""}`, Lean says `{hc.getD ""}`"
  -- For the same input and requirements, the notes at them are the same.
  let notesIn (ds : Array Diagnostic) (line : Nat) :=
    (ds.filter fun d => keep d && isConflictNote d && itemAt d.line == itemAt line)|>.map (fun d => s!"line {d.line}: {headOf d}") |>.qsort (· < ·)
  let sameNotes := (cliDiags.filter keep).filterMap fun c => do
    let i ← conflictInput? c.text
    let h ← (hosted.diags.filter keep).find? fun h => h.line == c.line && conflictInput? h.text == some i
    guard (conflictCore? c.text == conflictCore? h.text)
    let (cn, hn) := (notesIn cliDiags c.line, notesIn hosted.diags c.line)
    guard (cn != hn)
    return s!"line {c.line}: for the same input, fren notes {cn}, Lean notes {hn}"
  let sameInput := sameInput ++ sameNotes
  let keep (d : Diagnostic) := keep d && !isConflictNote d
  let mut cs := cliDiags.filter keep
  let hs := hosted.diags.filter keep
  -- The same message: same line, column, severity and normalized
  -- headline.
  let mut hostedOnly := #[]
  for h in hs do
    match cs.findIdx? fun c => c.line == h.line && c.col == h.col && c.severity == h.severity && normHead c.text == normHead h.text with
    | some i => cs := cs.eraseIdx! i
    | none => hostedOnly := hostedOnly.push h
  -- Lean's parse errors for the binary's errors on the same line: only
  -- those may be worded differently (`Reqs/View`). Only static errors: a
  -- check that fails in the binary is not one that Lean rejects.
  let staticErr (c : Diagnostic) := c.severity == "error" && !isCheckResult c
  let cliErrorLines := cs.filter staticErr |>.map (·.line)
  let leanLines := hostedOnly.filter isLeanParseError |>.map (·.line)
  hostedOnly := hostedOnly.filter fun h => !(isLeanParseError h && cliErrorLines.contains h.line)
  cs := cs.filter fun c => !(staticErr c && leanLines.contains c.line)
  let mut out := stopped ++ sameInput ++ cs.map (render "fren") ++ hostedOnly.map (render "Lean")
  let undecided := cs.all isUndecided && hostedOnly.all isUndecided
  -- The summary, unless a check is tested.
  let sumDiffers := !anyTested && cli.summary? != hosted.summary?
  if sumDiffers then
    out := out.push s!"summary: fren says `{cli.summary?.getD "(none)"}`, Lean says `{hosted.summary?.getD "(none)"}`"
  -- The exit code, from Lean's most severe message (`cli::exit`,
  -- `view::build`): 2 after a static error, else 1 for an error, 3 for a
  -- warning and 0 otherwise.
  let leanWorst := if hosted.diags.any (·.severity == "error") then 1
    else if hosted.diags.any (·.severity == "warning") then 3 else 0
  let expected := if staticError then 2 else leanWorst
  let exitDiffers := !anyTested && cli.exit?.any (· != expected)
  if exitDiffers then
    out := out.push s!"exit: fren exits {cli.exit?.getD 0}, and Lean's messages call for {expected}"
  -- A summary or an exit code that differs is a matter of time only if
  -- some undecided check explains it.
  let explained := undecided && !(cs.isEmpty && hostedOnly.isEmpty)
  return (out, undecided && sameInput.isEmpty && (!sumDiffers || explained) && (!exitDiffers || explained) && !out.isEmpty)

end FrenTest.Frontends
