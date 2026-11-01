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

Fences are read as CommonMark reads backtick fences (`markdown::fence`,
`markdown::closes`): at most three spaces, then at least three backticks,
then an info string with no backtick, so that inline code at the start of
a line is not a fence. A block closes at a fence with no info string and
at least as many backticks as its opening fence. Every reader of the
blocks, the front ends, `fren fmt` and the tests, reads them with
`fencedBlocks`.
-/

namespace Fren.Core

def isMarkdownFile (path : String) : Bool := path.endsWith ".md"

/-- A line as the fence reader sees it: how many spaces it starts with, how
many backticks follow them, and the rest of the line without the spaces
and tabs around it, which is a fence's info string. -/
structure FenceParts where
  indent : Nat
  run : Nat
  info : String
  deriving Repr, BEq

/-- `line` split into its leading spaces, the backticks after them, and the
rest. -/
def fenceParts (line : String) : FenceParts :=
  let indent := (line.takeWhile (· == ' ')).toString.length
  let after := (line.drop indent).toString
  let run := (after.takeWhile (· == '`')).toString.length
  { indent, run, info := (after.drop run).trimAscii.toString }

/-- Whether a line of `indent` spaces, `run` backticks and then `info` is a
fence (`markdown::fence`). -/
def isFence (indent run : Nat) (info : String) : Bool :=
  indent ≤ 3 && run ≥ 3 && !Fren.Str.contains info "`"

/-- Whether such a line closes a block opened by a fence of `openRun`
backticks (`markdown::closes`). -/
def closesBlock (openRun indent run : Nat) (info : String) : Bool :=
  isFence indent run info && run ≥ openRun && info == ""

/-- The fence's info string, if `line` is a fence. -/
def fenceInfo? (line : String) : Option String :=
  let p := fenceParts line
  if isFence p.indent p.run p.info then some p.info else none

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

/-- The fenced code blocks of a Markdown text, in order. -/
def fencedBlocks (src : String) : Array FencedBlock := Id.run do
  let mut out := #[]
  -- The open block: its opening fence's backticks, and the block so far.
  let mut cur : Option (Nat × FencedBlock) := none
  for line in src.splitOn "\n", i in [1:src.length + 2] do
    let p := fenceParts line
    match cur with
    | none =>
      if isFence p.indent p.run p.info then cur := some (p.run, { info := p.info, line := i, body := #[], close? := none })
    | some (run, b) =>
      if closesBlock run p.indent p.run p.info then
        out := out.push { b with close? := some i }
        cur := none
      else cur := some (run, { b with body := b.body.push line })
  if let some (_, b) := cur then out := out.push b
  return out

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

/-- The Fren code of a Markdown spec, with everything else blanked out. A
block still open at the end of the text extends to its end. -/
def unwrapMarkdown (src : String) : String := Id.run do
  let lines := (src.splitOn "\n").toArray
  let mut kept := Array.replicate lines.size false
  for b in fencedBlocks src do
    if b.info == frenInfo then
      for k in [0:b.body.size] do kept := kept.set! (b.line + k) true
  let mut out := #[]
  for h : i in [0:lines.size] do
    out := out.push (if kept[i]! then lines[i] else "")
  return "\n".intercalate out.toList

/-- A block that is still open at the end of the file (`F0167`). -/
def unclosedBlockMsg (info : String) (run : Nat) : Msg :=
  { code? := some "F0167", headline := "this code block is never closed"
    label? := some "opened here"
    notes := #[s!"note: a block that opens at a fence of {run} backticks closes at a line of at least {run} backticks and nothing else, \
      so the rest of the file is part of this {if info.isEmpty then "block" else s!"`{info}` block"}",
      "help: close it with a line of backticks"] }

/-- A fence whose info string starts with `fren` but names no kind of
block that Fren reads (`F0168`). -/
def nearFrenFenceMsg (info : String) : Msg :=
  { code? := some "F0168", headline := s!"`{info}` is not a kind of block that Fren reads"
    label? := some "read as prose"
    notes := #["note: Fren reads a block whose info string is exactly `fren`, and every other block is prose",
      "help: write `fren` to make it part of the spec"] }

/-- The problems of a Markdown spec's fences, each with the line of its
fence, from 1: a block still open at the end of the file, and a fence whose
info string looks like `fren` but is not. -/
def markdownProblems (src : String) : Array (Nat × Msg) :=
  (fencedBlocks src).foldl (init := #[]) fun acc b =>
    let acc := if blockKind b.info == .looksLikeFren then acc.push (b.line, nearFrenFenceMsg b.info) else acc
    match b.close? with
    | some _ => acc
    | none =>
      let run := (fenceParts ((src.splitOn "\n")[b.line - 1]!)).run
      acc.push (b.line, unclosedBlockMsg b.info run)

#guard (fencedBlocks "a\n```fren\nx\n```\n").map (·.info) == #["fren"]
-- Inline code at the start of a line is not a fence.
#guard fenceInfo? "```` ```fren example ```` is a block" == none
#guard (fencedBlocks "```` ```fren example ```` block\n```fren\nx\n```\n").map (·.body) == #[#["x"]]
-- A block of four backticks closes only at four or more, so it can show one of three.
#guard (fencedBlocks "````markdown\n```fren\nx\n```\n````\n```fren\ny\n```\n").map (·.info) == #["markdown", "fren"]
#guard unwrapMarkdown "````markdown\n```fren\nx\n```\n````\n```fren\ny\n```\n" == "\n\n\n\n\n\ny\n\n"
-- Four spaces make an indented code block, not a fence.
#guard fenceInfo? "    ```fren" == none
#guard fenceInfo? "   ```fren" == some "fren"
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
#guard (markdownProblems "```fren example\nx\n```\n```frenzy\n```\n```fren\n```\n").isEmpty

end Fren.Core
