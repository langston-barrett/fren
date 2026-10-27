/-!
# Messages and their rendering

A message (`Msg`) is shared by both front ends: an error code, a headline,
and notes and fixes. The Lean front end logs its `text`; the `fren` command
renders it the way rustc does, with the source line underlined and fixes
shown as edits:

```
error[F0105]: `==` is not an operator in Fren
 --> test.fren:2:29
  |
2 | proc c(x: Int) { ensure r: x == 1 }
  |                             ^^ not a Fren operator
  |
help: use `=` to test for equality
  |
2 - proc c(x: Int) { ensure r: x == 1 }
2 + proc c(x: Int) { ensure r: x = 1 }
  |
```
-/

namespace Fren.Core

/-- A source range, as character offsets. -/
structure Range where
  start : Nat
  stop : Nat
  deriving Inhabited, Repr, BEq

/-- An edit that fixes the problem: by default, the message's range
replaced by `replacement`. -/
structure Fix where
  msg : String
  replacement : String
  /-- Insert `replacement` after the range instead of replacing it. -/
  after : Bool := false
  /-- A range other than the message's, where only one front end knows it. -/
  range? : Option Range := none
  deriving Inhabited, Repr

structure Msg where
  /-- An error code such as `F0105`, explained by `fren --explain`; `none`
  for internal errors. -/
  code? : Option String
  /-- What is wrong, in one line. -/
  headline : String
  /-- Shown under the carets by the `fren` command. -/
  label? : Option String := none
  /-- Lines such as `help: ...`, `note: ...` and `counterexample: ...`. -/
  notes : Array String := #[]
  fixes : Array Fix := #[]
  deriving Inhabited, Repr

/-- A message with no code, for errors that are Fren's own bugs. -/
def Msg.internal (what : String) : Msg :=
  { code? := none, headline := s!"internal error: {what}", notes := #["note: this is a bug in Fren"] }

/-- The lines of a note: a note may span several, and each after the
first is indented to the text after its label, as rustc aligns them:

```
note: for the input
          x = 1
      no outputs satisfy `r`
```
-/
def noteLines (n : String) : List String :=
  match n.splitOn "\n" with
  | [] => []
  | first :: rest =>
    let pad := match first.splitOn ": " with
      | label :: _ :: _ => String.ofList (List.replicate (label.length + 2) ' ')
      | _ => ""
    first :: rest.map (pad ++ ·)

/-- The text of the message as the Lean front end shows it: the headline,
then a blank line and the notes and fixes, one per line, or more for a
note that spans several (`noteLines`). -/
def Msg.text (m : Msg) : String :=
  let lines := (m.notes.toList.flatMap noteLines) ++ (m.fixes.map ("help: " ++ ·.msg)).toList
  if lines.isEmpty then m.headline else m.headline ++ "\n\n" ++ "\n".intercalate lines

/-- Adds a note at the end. -/
def Msg.note (m : Msg) (line : String) : Msg := { m with notes := m.notes.push line }

/-! ## Rendering -/

/-- How a message is reported. -/
inductive Severity where
  | error
  | warning
  | info
  deriving Inhabited, BEq, Repr

/-- Information is a `note`, as in rustc. -/
def Severity.label : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "note"

/-- A message at a range of a file. -/
structure Diagnostic where
  level : Severity
  msg : Msg
  range : Range
  deriving Inhabited, Repr

/-- The lines of `src`, without their newlines, each with the offset where
it starts. -/
def lines (src : Array Char) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut start := 0
  let mut cur := ""
  for c in src, i in [0:src.size] do
    if c == '\n' then
      out := out.push (start, cur)
      start := i + 1
      cur := ""
    else cur := cur.push c
  out.push (start, cur)

/-- 1-based line and column of a character offset, as rustc counts them. -/
def position (src : Array Char) (off : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for i in [0:min off src.size] do
    if src[i]! == '\n' then line := line + 1; col := 1 else col := col + 1
  return (line, col)

/-- Tabs are shown as four spaces, as rustc does. -/
def expandTabs (s : String) : String := if s.contains '\t' then s.replace "\t" "    " else s

/-- The display width of the first `n` characters of `s`. -/
def widthOf (s : String) (n : Nat) : Nat :=
  (s.foldl (init := (0, 0)) fun (w, k) c => if k < n then (w + if c == '\t' then 4 else 1, k + 1) else (w, k)).1

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

def repeatChar (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

/-- The source line containing `off`: its number, starting offset and text.
Lines end at a newline, which is the last character of its line, and an
offset past the end is on the last line. Only the text up to the end of that
line is read, not the rest of `src`. -/
def lineAt (src : Array Char) (off : Nat) : Nat × Nat × String := Id.run do
  let off := min off src.size
  let mut n := 1
  let mut start := 0
  for i in [0:off] do
    if src[i]! == '\n' then
      n := n + 1
      start := i + 1
  let mut text := ""
  for i in [start:src.size] do
    if src[i]! == '\n' then break
    text := text.push src[i]!
  return (n, start, text)

/-- The offset at which each line of `src` starts: 0, and one past each
newline. -/
def lineStarts (src : Array Char) : Array Nat := Id.run do
  let mut out := #[0]
  for c in src, i in [0:src.size] do
    if c == '\n' then out := out.push (i + 1)
  return out

/-- `lineAt src off`, where `starts` is `lineStarts src`, without reading
`src` before the line: the line's number is that of the starts at most
`off`, which are those of the newlines before it, and the line starts at
the last of them. -/
def lineAtIn (starts : Array Nat) (src : Array Char) (off : Nat) : Nat × Nat × String := Id.run do
  let off := min off src.size
  -- The number of starts at most `off`, at least 1 (`starts[0]` is 0).
  let mut lo := 1
  let mut hi := starts.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if starts[mid]! ≤ off then lo := mid + 1 else hi := mid
  let start := starts[lo - 1]!
  let mut text := ""
  for i in [start:src.size] do
    if src[i]! == '\n' then break
    text := text.push src[i]!
  return (lo, start, text)

/-! ### Colour

ANSI styles in rustc's colours: the severity's colour for the header and
the carets, bold blue for the gutter, and red and green for what a fix
removes and adds. A painter that is off leaves text as it is. -/

structure Paint where
  on : Bool := false

def Paint.style (p : Paint) (sgr s : String) : String :=
  if p.on && !s.isEmpty then s!"\x1b[{sgr}m{s}\x1b[0m" else s

def Paint.bold (p : Paint) (s : String) : String := p.style "1" s
def Paint.blue (p : Paint) (s : String) : String := p.style "1;94" s
def Paint.help (p : Paint) (s : String) : String := p.style "1;96" s
def Paint.removed (p : Paint) (s : String) : String := p.style "91" s
def Paint.added (p : Paint) (s : String) : String := p.style "92" s

def Paint.level (p : Paint) (l : Severity) (s : String) : String :=
  p.style (match l with | .error => "1;91" | .warning => "1;93" | .info => "1;92") s

/-- `note: text` with `note:` in bold; any `label: text` likewise. -/
def Paint.labelled (p : Paint) (line : String) : String :=
  match line.splitOn ": " with
  | label :: rest@(_ :: _) =>
    let label' := if label == "help" then p.help (label ++ ":") else p.bold (label ++ ":")
    label' ++ " " ++ ": ".intercalate rest
  | _ => line

/-! ### Layout -/

/-- `n | text`, with the line number right-aligned in a gutter `w` wide;
`text` is split into what comes before, the part that `sep` marks (removed
or added by a fix), and what comes after. -/
def srcLine (p : Paint) (w n : Nat) (sep : String) (before marked after : String := "") : String :=
  let num := toString n
  let plain := expandTabs (before ++ marked ++ after)
  -- Trailing spaces are trimmed, as rustc does.
  let keep := plain.trimAsciiEnd.toString.length
  let b := expandTabs before
  let m := expandTabs marked
  let (b, m, a) :=
    if keep ≤ b.length then (String.ofList (b.toList.take keep), "", "")
    else if keep ≤ b.length + m.length then (b, String.ofList (m.toList.take (keep - b.length)), "")
    else (b, m, String.ofList ((expandTabs after).toList.take (keep - b.length - m.length)))
  let m := match sep with
    | "-" => p.removed m
    | "+" => p.added m
    | _ => m
  let sepP := match sep with
    | "-" => p.removed sep
    | "+" => p.added sep
    | _ => p.blue sep
  let head := s!"{p.blue s!"{spaces (w - num.length)}{num}"} {sepP}"
  if keep == 0 then head else s!"{head} {b}{m}{a}"

def gutter (p : Paint) (w : Nat) : String := s!"{spaces w} {p.blue "|"}"

/-- Where a fix applies, given the message's range. -/
def Fix.target (f : Fix) (r : Range) : Range :=
  let r := f.range?.getD r
  if f.after then { start := r.stop, stop := r.stop } else r

/-- A fix as rustc shows a suggestion: `+` under an insertion, or the old and
new lines of a replacement. -/
def renderFix (p : Paint) (src : Array Char) (w : Nat) (r : Range) (f : Fix) (starts : Array Nat := lineStarts src) :
    Array String :=
  let r := f.target r
  let (n, lstart, text) := lineAtIn starts src r.start
  let col := r.start - lstart
  let stopCol := min (r.stop - lstart) text.length
  let before := String.ofList (text.toList.take col)
  let old := String.ofList ((text.toList.drop col).take (stopCol - col))
  let after := String.ofList (text.toList.drop stopCol)
  let edit := if r.start == r.stop then
      #[srcLine p w n "|" (before ++ f.replacement ++ after),
        s!"{gutter p w} {spaces (widthOf (before ++ f.replacement) col)}{p.added (repeatChar '+' f.replacement.length)}"]
    else #[srcLine p w n "-" before old after, srcLine p w n "+" before f.replacement after]
  #[p.labelled s!"help: {f.msg}", gutter p w] ++ edit ++ #[gutter p w]

/-- The width of the gutter for a diagnostic: that of the largest line
number it shows. -/
def Diagnostic.gutterWidth (d : Diagnostic) (src : Array Char) (starts : Array Nat := lineStarts src)
    (line : Nat := (lineAtIn starts src d.range.start).1) : Nat :=
  let ns := #[line] ++ d.msg.fixes.map fun f => (lineAtIn starts src (f.target d.range).start).1
  (toString (ns.foldl max 0)).length

/-- A note as rows after `indent`: `= note: text`, and the rest of its
lines (`noteLines`) under its text. Only the first has its label painted. -/
def noteRows (p : Paint) (indent : String) (n : String) : Array String :=
  match noteLines n with
  | [] => #[]
  | first :: rest => #[s!"{indent} {p.blue "="} {p.labelled first}"] ++ rest.toArray.map (s!"{indent}   {·}")

/-- The header line: `error[F0105]: headline`. -/
def header (level : Severity) (msg : Msg) (p : Paint := {}) : String :=
  let code := msg.code?.map (s!"[{·}]") |>.getD ""
  p.level level s!"{level.label}{code}" ++ p.bold s!": {msg.headline}"

/-- The text of a diagnostic about the file at `path`, whose lines start
at `starts` (`lineStarts`), computed once for the file's diagnostics.
Ranges spanning several lines are underlined to the end of the first. -/
def Diagnostic.render (d : Diagnostic) (path : String) (src : Array Char) (p : Paint := {})
    (starts : Array Nat := lineStarts src) : String := Id.run do
  -- The line's number is `position`'s, and so is the column: the
  -- characters from the line's start to the offset, which is at most the
  -- text's end, plus one.
  let (line, lstart, text) := lineAtIn starts src d.range.start
  let col := min d.range.start src.size - lstart + 1
  let w := d.gutterWidth src starts line
  let mut out := #[header d.level d.msg p, s!"{spaces w}{p.blue "-->"} {path}:{line}:{col}", gutter p w,
    srcLine p w line "|" text]
  let startCol := d.range.start - lstart
  let stopCol := min (d.range.stop - lstart) text.length
  let indent := widthOf text startCol
  let len := max 1 (widthOf text stopCol - indent)
  let label := d.msg.label?.map (" " ++ ·) |>.getD ""
  out := out.push s!"{gutter p w} {spaces indent}{p.level d.level (repeatChar '^' len ++ label)}"
  if !d.msg.notes.isEmpty then
    out := out.push (gutter p w)
    for n in d.msg.notes do out := out ++ noteRows p (spaces w) n
  else if !d.msg.fixes.isEmpty then
    out := out.push (gutter p w)
  for f in d.msg.fixes do
    out := out ++ renderFix p src w d.range f starts
  return "\n".intercalate out.toList ++ "\n"

/-- The text of a message with no source position, such as a file that
cannot be read. -/
def renderPlain (level : Severity) (msg : Msg) (p : Paint := {}) : String := Id.run do
  let mut out := #[header level msg p]
  for n in msg.notes ++ msg.fixes.map ("help: " ++ ·.msg) do
    out := out ++ noteRows p " " n
  return "\n".intercalate out.toList ++ "\n"

/-- rustc's pointer to `--explain`, for the codes of a run's errors. -/
def explainHint (codes : Array String) : Option String :=
  match codes.toList.eraseDups.toArray.qsort (· < ·) |>.toList with
  | [] => none
  | [c] => some s!"For more information about this error, try `fren --explain {c}`."
  | cs@(c :: _) => some s!"Some errors have detailed explanations: {", ".intercalate cs}.\n\
      For more information about an error, try `fren --explain {c}`."

end Fren.Core
