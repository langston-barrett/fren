-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Str
-- keep-sorted end

/-!
# Markdown specs

A Markdown file is a spec whose Fren code is in ```` ```fren ```` fenced
blocks (`Reqs/Markdown`). Both front ends read it as the code with
everything else blanked out: each line outside a block becomes empty, and
code lines are kept as they are, so line and column numbers are those of
the Markdown file.

Fences are read much as CommonMark reads them (`Reqs/Markdown#code-blocks`):
`splitLine` splits a line into its indentation, its run of backticks or
tildes, and its info string (`markdown::split`), and `step` reads a line
after the lines before it (`markdown::step`). `fencedBlocks` is `step`
folded over the lines, and every reader of the blocks, the front ends,
`fren fmt` and the tests, reads them with it.
-/

namespace Fren.Core

def isMarkdownFile (path : String) : Bool := path.endsWith ".md"

/-- How many characters of `s`, one after another from position `i`, each
satisfy `p`. -/
def charRun (p : String → Bool) (s : String) (i : Nat) : Nat :=
  if i < s.length ∧ p (Fren.Str.at s i) = true then charRun p s (i + 1) + 1 else 0
termination_by s.length - i

/-- A space or a tab (`markdown::blank?`). -/
def isBlank (c : String) : Bool := c == " " || c == "\t"

/-- A line as the fence reader splits it (`markdown::split`). -/
structure LineParts where
  /-- The spaces that it starts with. -/
  indent : Nat
  /-- The character of the run after them, `` ` `` or `~`, or `""`. -/
  marker : String
  /-- The length of that run. -/
  run : Nat
  /-- The blanks after the run. -/
  lead : Nat
  /-- The rest of the line after them: a fence's info string. -/
  info : String
  /-- The line is a fence. -/
  fence : Bool
  deriving Repr, BEq

/-- `line` split as the fence reader splits it (`markdown::split`). -/
def splitLine (line : String) : LineParts :=
  let indent := charRun (· == " ") line 0
  let c := Fren.Str.at line indent
  let marker := if c = "`" ∨ c = "~" then c else ""
  let run := if marker = "" then 0 else charRun (· == marker) line indent
  let lead := charRun isBlank line (indent + run)
  let info := Fren.Str.slice line ((indent : Int) + run + lead) ((line.length : Int) - indent - run - lead)
  let fence := decide (indent ≤ 3) && decide (3 ≤ run) && (marker == "~" || !Fren.Str.contains info "`")
  { indent, marker, run, lead, info, fence }

/-- The fence that opened the block that the reader is in. -/
structure Opening where
  marker : String
  run : Nat
  info : String
  deriving Repr, BEq, Inhabited

/-- What the reader makes of a line, after the lines before it
(`markdown::step`). -/
structure Step where
  /-- It is in a block after the line. -/
  inside : Bool
  /-- The fence that opened that block. -/
  opening : Opening
  /-- The line is in the body of a block. -/
  body : Bool
  /-- The line opens a block. -/
  opens : Bool
  /-- The line is the spec's: in the body of a `fren` block. -/
  kept : Bool
  deriving Repr, BEq

/-- The lines of a Markdown text: split at each `\n`, and without a `\r`
before it. -/
def markdownLines (src : String) : Array String :=
  (src.splitOn "\n").toArray.map fun l => if l.endsWith "\r" then (l.dropEnd 1).toString else l

/-- A fenced code block of a Markdown text. -/
structure FencedBlock where
  /-- The info string of its opening fence. -/
  info : String
  /-- The line of its opening fence, from 1. -/
  line : Nat
  /-- The lines between its fences. -/
  body : Array String
  /-- The line of its closing fence; `none` if it is still open at the end of
  the text, where it ends. -/
  close? : Option Nat
  deriving Repr, BEq

/-- The info strings of the kinds of block that Fren reads: ```` ```fren ````,
part of the spec, and ```` ```fren example ````, an example of the
reference that its tests check on its own (`Reqs/dev/Style#examples`). -/
def frenInfo : String := "fren"
def frenExampleInfo : String := "fren example"

/-- What Fren makes of a block (`markdown::block_kind`). -/
inductive BlockKind where
  /-- Part of the spec. -/
  | spec
  /-- An example of the reference, checked on its own. -/
  | exampleBlock
  /-- Prose whose info string looks like `fren` but is not, an error. -/
  | looksLikeFren
  /-- Prose. -/
  | prose
  deriving DecidableEq, Repr

/-- What Fren makes of a block whose info string is `info`: one whose first
word, up to a space, tab, `,` or `{`, is `fren`, as in `fren  example` or
`fren,ignore`, looks like `fren` (`markdown::block_kind`). -/
def blockKind (info : String) : BlockKind :=
  if info = frenInfo then .spec
  else if info = frenExampleInfo then .exampleBlock
  else if Fren.Str.startsWith info "fren " || Fren.Str.startsWith info "fren\t"
      || Fren.Str.startsWith info "fren," || Fren.Str.startsWith info "fren{" then .looksLikeFren
  else .prose

/-- Whether a line split as `p` closes a block opened by `o`: a fence of
the same character, at least as long, with no info string. -/
def closesBlock (o : Opening) (p : LineParts) : Bool :=
  p.fence && p.marker == o.marker && decide (o.run ≤ p.run) && p.info == ""

/-- The reader's step at `line`, inside a block opened by `o` or not
(`markdown::step`). -/
def step (inside : Bool) (o : Opening) (line : String) : Step :=
  let p := splitLine line
  let kept := blockKind o.info == .spec
  if inside then
    if closesBlock o p then { inside := false, opening := o, body := false, opens := false, kept := false }
    else { inside := true, opening := o, body := true, opens := false, kept }
  else if p.fence then
    { inside := true, opening := { marker := p.marker, run := p.run, info := p.info }, body := false, opens := true,
      kept := false }
  else { inside := false, opening := o, body := false, opens := false, kept := false }

/-- The fenced code blocks of a Markdown text, in order: `step` folded over
its lines. -/
def fencedBlocks (src : String) : Array FencedBlock := Id.run do
  let mut out := #[]
  let mut inside := false
  let mut o : Opening := default
  -- The open block so far.
  let mut cur : Option FencedBlock := none
  let lines := markdownLines src
  for h : k in [0:lines.size] do
    let line := lines[k]
    let st := step inside o line
    if st.opens then cur := some { info := st.opening.info, line := k + 1, body := #[], close? := none }
    else if st.body then cur := cur.map fun b => { b with body := b.body.push line }
    else if inside && !st.inside then
      if let some b := cur then out := out.push { b with close? := some (k + 1) }
      cur := none
    inside := st.inside
    o := st.opening
  if let some b := cur then out := out.push b
  return out

/-- Whether `line` is the spec's, after the lines before it: in the body of
a `fren` block (`markdown::kept`). -/
def keptLine (inside : Bool) (o : Opening) (line : String) : Bool :=
  (step inside o line).kept

/-- The Fren code of a Markdown spec, with everything else blanked out:
`keptLine` folded over its lines. A block still open at the end of the
text extends to its end. -/
def unwrapMarkdown (src : String) : String := Id.run do
  let raw := (src.splitOn "\n").toArray
  let lines := markdownLines src
  let mut inside := false
  let mut o : Opening := default
  let mut out := #[]
  for h : k in [0:lines.size] do
    let st := step inside o lines[k]
    out := out.push (if keptLine inside o lines[k] then raw[k]! else "")
    inside := st.inside
    o := st.opening
  return "\n".intercalate out.toList

/-- A block that is still open at the end of the file (`F0167`). -/
def unclosedBlockMsg (info : String) (marker : String) (run : Nat) : Msg :=
  let chars := if marker == "~" then "tildes" else "backticks"
  { code? := some "F0167", headline := "this code block is never closed"
    label? := some "opened here"
    notes := #[s!"note: a block that opens at a fence of {run} {chars} closes at a line of at least {run} {chars} and nothing else, \
      so the rest of the file is part of this {if info.isEmpty then "block" else s!"`{info}` block"}",
      s!"help: close it with a line of {chars}"] }

/-- A fence whose info string starts with `fren` but names no kind of
block that Fren reads (`F0168`). -/
def nearFrenFenceMsg (info : String) : Msg :=
  { code? := some "F0168", headline := s!"`{info}` is not a kind of block that Fren reads"
    label? := some "read as prose"
    notes := #["note: Fren reads the blocks whose info string is exactly `fren`, part of the spec, \
      or `fren example`, an example of the reference; every other block is prose",
      "help: write `fren` to make it part of the spec, or `fren example` for an example of the reference"] }

/-- The problems of a Markdown spec's fences, each with the line of its
fence, from 1: a block still open at the end of the file, and a fence whose
info string looks like `fren` but is not. -/
def markdownProblems (src : String) : Array (Nat × Msg) :=
  (fencedBlocks src).foldl (init := #[]) fun acc b =>
    let acc := if blockKind b.info == .looksLikeFren then acc.push (b.line, nearFrenFenceMsg b.info) else acc
    match b.close? with
    | some _ => acc
    | none =>
      let p := splitLine ((markdownLines src)[b.line - 1]!)
      acc.push (b.line, unclosedBlockMsg b.info p.marker p.run)

#guard (fencedBlocks "a\n```fren\nx\n```\n").map (·.info) == #["fren"]
-- Inline code at the start of a line is not a fence.
#guard !(splitLine "```` ```fren example ```` is a block").fence
#guard (fencedBlocks "```` ```fren example ```` block\n```fren\nx\n```\n").map (·.body) == #[#["x"]]
-- A block of four backticks closes only at four or more, so it can show one of three.
#guard (fencedBlocks "````markdown\n```fren\nx\n```\n````\n```fren\ny\n```\n").map (·.info) == #["markdown", "fren"]
#guard unwrapMarkdown "````markdown\n```fren\nx\n```\n````\n```fren\ny\n```\n" == "\n\n\n\n\n\ny\n\n"
-- Four spaces make an indented code block, not a fence.
#guard !(splitLine "    ```fren").fence
#guard (splitLine "   ```fren").fence && (splitLine "   ```fren").info == "fren"
-- A fence with an info string does not close a block.
#guard (fencedBlocks "```fren\n```text\n```\n").map (·.body) == #[#["```text"]]
-- A block still open at the end of the file extends to its end, and is reported.
#guard (fencedBlocks "```fren\nx\n").map (·.close?) == #[none]
#guard unwrapMarkdown "```fren\nx\n" == "\nx\n"
#guard (markdownProblems "```fren\nx\n").map (fun (l, m) => (l, m.code?)) == #[(1, some "F0167")]
#guard (markdownProblems "````text\nx\n```\n").map (·.2.code?) == #[some "F0167"]
-- A tag that looks like `fren` but is not.
#guard (markdownProblems "```fren  example\nx\n```\n").map (fun (l, m) => (l, m.code?)) == #[(1, some "F0168")]
#guard (markdownProblems "```fren,example\nx\n```\n").map (·.2.code?) == #[some "F0168"]
-- Tilde fences, whose info string may hold backticks, close only at tildes.
#guard (fencedBlocks "~~~text `x`\n```fren\ny\n```\n~~~\n").map (fun b => (b.info, b.body)) == #[("text `x`", #["```fren", "y", "```"])]
#guard unwrapMarkdown "~~~\n```fren\ny\n```\n~~~\n" == "\n\n\n\n\n"
-- A `\r` before the `\n` ends the line.
#guard (fencedBlocks "```fren\r\nx\r\n```\r\n").map (fun b => (b.info, b.close?)) == #[("fren", some 3)]
#guard (markdownProblems "```fren example\n```frenzy\n```\n```fren\n```\n").isEmpty

end Fren.Core
