-- keep-sorted start
import FrenCli.Parse
import FrenCore.Literate
import FrenCore.Trace
-- keep-sorted end

/-!
# `fren fmt`: Fren's standard layout (`Reqs/Fmt`)

The formatter works on the tokens and comments of a file that parses, and
keeps its line breaks. First it rewrites each block of imports
(`fmt::in_block`, `fmt::group_layout`). Then it decides, for each line, its
indentation (`fmt::indent`), the spaces between its tokens (`fmt::space`),
where its trailing comment goes (`fmt::comment_column`), and how many blank
lines precede it (`fmt::blank_lines`); and it adds or removes the trailing
commas of lists (`fmt::trailing_comma`). The parser says which tokens start
an item, a member or an element, which `-` are unary, which braces open
lists, and where the claims and imports are (`Layout`).
-/

namespace FrenCli.Fmt

open Fren.Core (Msg Paint)

/-! ## Decisions -/

/-- The kind of a token, for spacing (`fmt::space`). -/
inductive Kind where
  | paren
  /-- The `(` after a function's name. -/
  | call
  | closeParen
  | brace
  | closeBrace
  | group
  | closeGroup
  | path
  | comma
  | colon
  | negation
  | comment
  | other
  deriving BEq, DecidableEq, Repr

/-- Whether a space separates two tokens on a line (`fmt::space`). -/
def space (before after : Kind) : Bool :=
  if before == .comment || after == .comment then true
  else if before == .brace && after == .closeBrace then false
  else !(before matches .paren | .call | .group | .path | .negation) &&
    !(after matches .closeParen | .closeGroup | .path | .comma | .colon | .group | .call)

/-- What a line's first token does (`fmt::indent`). -/
inductive LineStart where
  | closing
  | starting
  | continuing
  deriving BEq, DecidableEq, Repr

/-- The indentation of a line, in spaces (`fmt::indent`). -/
def indent (depth : Nat) (start : LineStart) (comment : Bool) : Nat :=
  match start with
  | .closing => 4 * (if comment then depth else depth - 1)
  | .starting => 4 * depth
  | .continuing => 4 * depth + 4

/-- The column of a trailing comment, after code `width` wide, that started
at column `original` (`fmt::comment_column`). -/
def commentColumn (width original : Nat) : Nat :=
  if original ≥ width + 2 then original else width + 2

/-- The blank lines kept before a line (`fmt::blank_lines`). -/
def blankLines (blank : Nat) (first afterOpen beforeClose : Bool) : Nat :=
  if first || afterOpen || beforeClose || blank == 0 then 0 else 1

/-- Whether the last element of a list is followed by a comma
(`fmt::trailing_comma`). -/
def trailingComma (empty vertical : Bool) : Bool := !empty && vertical

/-- Whether the paths of one prefix are written in braces, and whether one
on each line (`fmt::group_layout`). -/
def groupLayout (nPaths : Nat) (wasVertical fits : Bool) : Bool × Bool :=
  (nPaths > 1, nPaths > 1 && (wasVertical || !fits))

/-- Whether a `use` is part of a block of imports (`fmt::in_block`). -/
def inBlock (alone nested : Bool) : Bool := alone && !nested

/-- Whether a file is rewritten, and whether its diff is printed
(`fmt::file`). -/
def fileAction (check ignored parsed formatted : Bool) : Bool × Bool :=
  (!ignored && !check && parsed && !formatted, !ignored && check && parsed && !formatted)

/-- Whether `path` matches one of the `--ignore` globs. -/
def ignored (globs : Array String) (path : String) : Bool :=
  let segs (s : String) := s.splitOn "/" |>.filter (· != ".")
  globs.any fun g => Fren.Core.globMatch (segs g) (segs path)

/-- The exit code of `fren fmt` (`fmt::exit`). -/
def exitCode (check allParsed allFormatted : Bool) : UInt32 :=
  if !allParsed then 2 else if check && !allFormatted then 1 else 0

/-! ## Source positions -/

/-- The line of each offset in `src`, and the offset where each line starts. -/
def lineTable (src : Array Char) : Array Nat × Array Nat := Id.run do
  let mut lineOf := Array.mkEmpty (src.size + 1)
  let mut starts := #[0]
  for h : i in [0:src.size] do
    lineOf := lineOf.push (starts.size - 1)
    if src[i] == '\n' then starts := starts.push (i + 1)
  return (lineOf.push (starts.size - 1), starts)

def text (src : Array Char) (s : Span) : String := String.ofList (src.extract s.start s.stop).toList

/-! ## Imports -/

/-- Segment by segment, by code point. -/
def pathLt (a b : Array String) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return a.size < b.size

/-- Sorts after every segment, so that a glob comes after the paths of its
prefix. -/
def globKey : String := String.singleton (Char.ofNat 0x10FFFF)

/-- The paths imported by the `use` from token `first` to `last`, and
whether it is a glob. -/
def usePaths (toks : Array Token) (first last : Nat) : Array (Array String) × Bool := Id.run do
  let name (k : Nat) : String := match toks[k]!.tok with
    | .ident s => s
    | _ => ""
  let mut pre := #[]
  let mut k := first + 1
  while k ≤ last do
    match toks[k]!.tok with
    | .ident s => pre := pre.push s
    | .kw "::*" => return (#[pre], true)
    | .kw "::{" =>
      let mut out := #[]
      let mut cur := pre
      for j in [k + 1:last] do
        match toks[j]!.tok with
        | .kw "," => if cur.size > pre.size then out := out.push cur; cur := pre
        | .kw "::" => pure ()
        | _ => cur := cur.push (name j)
      if cur.size > pre.size then out := out.push cur
      return (out, false)
    | _ => pure ()
    k := k + 1
  return (#[pre], false)

/-- The lines of one block of imports. `paths` are the paths of its
non-glob imports, each with whether its `use` spanned several lines. -/
def blockLines (paths : Array (Array String × Bool)) (globs : Array (Array String)) : Array String := Id.run do
  -- Paths grouped by prefix, in order of first appearance.
  let mut groups : Array (Array String × Array String × Bool) := #[]
  let mut singles : Array (Array String) := #[]
  for (p, v) in paths do
    if p.size < 2 then singles := singles.push p; continue
    let pre := p.pop
    match groups.findIdx? (·.1 == pre) with
    | some i => groups := groups.modify i fun (pre, es, wv) => (pre, es.push p.back!, wv || v)
    | none => groups := groups.push (pre, #[p.back!], v)
  let mut items : Array (Array String × Array String) := #[]
  for s in singles do items := items.push (s, #[s!"use {"::".intercalate s.toList}"])
  for g in globs do items := items.push (g.push globKey, #[s!"use {"::".intercalate g.toList}::*"])
  for (pre, es, wv) in groups do
    let es := es.qsort (· < ·)
    let preS := "::".intercalate pre.toList
    let line := s!"use {preS}::\{{", ".intercalate es.toList}}"
    let (braces, vertical) := groupLayout es.size wv (line.length ≤ 100)
    let ls := if !braces then #[s!"use {preS}::{es[0]!}"]
      else if vertical then #[s!"use {preS}::\{"] ++ es.map (· ++ ",") |>.push "}"
      else #[line]
    items := items.push (pre.push es[0]!, ls)
  return (items.qsort (pathLt ·.1 ·.1)).flatMap (·.2)

/-- The lines of `src` with each block of imports rewritten
(`fmt::in_block`), each with the line of `src` it comes from. -/
def organizeImports (src : Array Char) (toks : Array Token) (comments : Array Span) (lay : Layout) :
    Array (String × Nat) := Id.run do
  let (lineOf, _) := lineTable src
  let srcLines := ((String.ofList src.toList).splitOn "\n").toArray
  let lineAt (k : Nat) : Nat := lineOf[toks[k]!.span.start]!
  let endLine (s : Span) : Nat := lineOf[s.stop - 1]!
  let mut commentLines : Array Nat := #[]
  for c in comments do
    for l in [lineOf[c.start]!:endLine c + 1] do commentLines := commentLines.push l
  -- Blocks: for each, its first and last lines, and its imports.
  let mut blocks : Array (Nat × Nat × Array (Array String × Bool) × Array (Array String)) := #[]
  for (first, last) in lay.uses do
    let sl := lineAt first
    let el := endLine toks[last]!.span
    let next := toks[last + 1]!
    let alone := (first == 0 || endLine toks[first - 1]!.span < sl) &&
      (next.tok == .eof || lineOf[next.span.start]! > el) &&
      !commentLines.any (fun l => sl ≤ l && l ≤ el)
    let nested := first > 0 && toks[first - 1]!.tok == .kw "in"
    if !inBlock alone nested then continue
    let (ps, glob) := usePaths toks first last
    let (paths, globs) := if glob then (#[], ps) else (ps.map (·, decide (sl < el)), #[])
    match blocks.back? with
    | some (bs, be, bp, bg) =>
      if be + 1 == sl then blocks := blocks.pop.push (bs, el, bp ++ paths, bg ++ globs)
      else blocks := blocks.push (sl, el, paths, globs)
    | none => blocks := blocks.push (sl, el, paths, globs)
  let kept (start stop : Nat) := (srcLines.extract start stop).zipIdx.map fun (l, i) => (l, start + i)
  let mut out := #[]
  let mut line := 0
  for (bs, be, paths, globs) in blocks do
    out := out ++ kept line bs ++ (blockLines paths globs).map (·, bs)
    line := be + 1
  return out ++ kept line srcLines.size

/-! ## Layout -/

/-- A token or a comment, with the lines it starts and ends on, and the
column where it starts. -/
structure Piece where
  text : String
  /-- The token's index, or `none` for a comment. -/
  tok? : Option Nat
  startLine : Nat
  endLine : Nat
  col : Nat
  deriving Inhabited

/-- A line of output: the blank lines before it, its indentation, its
pieces with their kinds, and the column where its last comment started. -/
structure Line where
  blank : Nat
  indent : Nat
  pieces : Array (Kind × String)
  commentCol : Nat := 0
  /-- The line of the source it starts on. -/
  line : Nat
  deriving Inhabited

def isLineComment (s : String) : Bool := s.startsWith "--"

/-- Renders a line, placing its trailing comment, if any
(`fmt::comment_column`). -/
def Line.render (l : Line) : String := Id.run do
  let trailing? := match l.pieces.back? with
    | some (.comment, s) => if l.pieces.size > 1 && isLineComment s then some s else none
    | _ => none
  let code := if trailing?.isSome then l.pieces.pop else l.pieces
  let mut s := "".pushn ' ' l.indent
  let mut prev? : Option Kind := none
  for (k, t) in code do
    if let some p := prev? then if space p k then s := s.push ' '
    s := s ++ t
    prev? := some k
  let some c := trailing? | return s
  let width := ((s.splitOn "\n").getLast?.getD "").length
  return s.pushn ' ' (commentColumn width l.commentCol - width) ++ c

/-- A brace on the stack: whether it is `::{`, whether it opens a list, and
its token. -/
structure Brace where
  group : Bool
  list : Bool
  tok : Nat

/-- Lays out the tokens and comments of a file that parses. A line in a
different `segment` from the line before it is laid out as the first of a
file. -/
def layout (src : Array Char) (toks : Array Token) (comments : Array Span) (lay : Layout)
    (segment : Nat → Nat) : Array Line := Id.run do
  let (lineOf, lineStarts) := lineTable src
  let mkPiece (s : Span) (tok? : Option Nat) : Piece :=
    let startLine := lineOf[s.start]!
    { text := (text src s).trimAsciiEnd.toString, tok?, startLine, endLine := lineOf[s.stop - 1]!
      col := s.start - lineStarts[startLine]! }
  -- Tokens and comments, in order.
  let mut sorted : Array (Nat × Piece) := #[]
  for k in [0:toks.size - 1] do
    sorted := sorted.push (toks[k]!.span.start, mkPiece toks[k]!.span (some k))
  for c in comments do
    sorted := sorted.push (c.start, mkPiece c none)
  let pieces := (sorted.qsort (·.1 < ·.1)).map (·.2)
  let tokLine (k : Nat) : Nat := lineOf[toks[k]!.span.start]!
  let isTok (k : Nat) (s : String) : Bool := toks[k]!.tok == .kw s
  -- `tested` claims: whether each is vertical, by its last string.
  let claimVertical (k : Nat) : Option Bool :=
    (lay.claims.find? (·.2 == k)).map fun (t, _) => tokLine k > tokLine t
  let lineStart (stack : Array Brace) (k : Nat) : LineStart :=
    if isTok k "}" && !stack.isEmpty then .closing
    else if lay.starts.contains k then .starting
    else .continuing
  let mut out : Array Line := #[]
  let mut stack : Array Brace := #[]
  -- The last token: its line in `out`, its index there, and its index.
  let mut last? : Option (Nat × Nat × Nat) := none
  for h : i in [0:pieces.size] do
    let p := pieces[i]
    let newLine := i == 0 || p.startLine > pieces[i - 1]!.endLine
    if let some k := p.tok? then
      -- The trailing comma of a claim that is not vertical.
      if isTok k "," && k > 0 && claimVertical (k - 1) == some false then continue
      -- Trailing commas, at the `}` that closes a list.
      if isTok k "}" then
        if let some o := stack.back? then
          if o.list then
            if let some (li, pi, lk) := last? then
              let had := isTok lk ","
              let want := trailingComma (lk == o.tok) newLine
              if want && !had then
                out := out.modify li fun l => { l with pieces := l.pieces.insertIdxIfInBounds (pi + 1) (.comma, ",") }
              else if !want && had then
                out := out.modify li fun l => { l with pieces := l.pieces.eraseIdxIfInBounds pi }
    let kind : Kind := match p.tok? with
      | none => .comment
      | some k =>
        match toks[k]!.tok with
        | .kw "(" => if lay.calls.contains k then .call else .paren
        | .kw ")" => .closeParen
        -- An index's `[` is spaced like a call's `(`, and a literal's like `(`.
        | .kw "[" => if lay.calls.contains k then .call else .paren
        | .kw "]" => .closeParen
        -- A set literal's braces are spaced like parentheses.
        | .kw "{" => if lay.sets.contains k then .paren else .brace
        | .kw "::{" => .group
        | .kw "}" =>
          if stack.back?.any (·.group) then .closeGroup
          else if stack.back?.any (lay.sets.contains ·.tok) then .closeParen
          else .closeBrace
        | .kw "::" | .kw "." => .path
        -- Ends a path, so a space follows it, as one follows `)`.
        | .kw "::*" => .closeParen
        | .kw "," => .comma
        | .kw ":" => .colon
        | .kw "-" => if lay.unary.contains k then .negation else .other
        | _ => .other
    if newLine then
      -- A comment is indented as the next token.
      let next? := match p.tok? with
        | some k => some k
        | none => (pieces.extract (i + 1)).findSome? (Piece.tok?)
      let start := (next?.map (lineStart stack ·)).getD .starting
      let columns := indent stack.size start p.tok?.isNone
      let first := i == 0 || segment p.startLine != segment pieces[i - 1]!.endLine
      let blank := if first then 0 else p.startLine - pieces[i - 1]!.endLine - 1
      let afterOpen := out.back?.any fun l => l.pieces.back?.any (·.1 matches .brace | .group)
      let beforeClose := p.tok?.any (isTok · "}")
      let kept := blankLines blank first afterOpen beforeClose
      out := out.push { blank := kept, indent := columns, pieces := #[], line := p.startLine }
    out := out.modify (out.size - 1) fun l =>
      { l with pieces := l.pieces.push (kind, p.text), commentCol := if kind == .comment then p.col else l.commentCol }
    if let some k := p.tok? then
      last? := some (out.size - 1, out.back!.pieces.size - 1, k)
      if claimVertical k == some true && !isTok (k + 1) "," then
        out := out.modify (out.size - 1) fun l => { l with pieces := l.pieces.push (.comma, ",") }
      match toks[k]!.tok with
      | .kw "{" => stack := stack.push { group := false, list := lay.lists.contains k, tok := k }
      | .kw "::{" => stack := stack.push { group := true, list := true, tok := k }
      | .kw "}" => stack := stack.pop
      | _ => pure ()
  return out

/-- An error that stops a file from being formatted. -/
abbrev Error := Span × Msg

def parseAll (src : Array Char) : Except Error (Array Token × Array Span × Layout) := do
  let (toks, comments) ← (lexWithComments src).mapError fun e => (e.span, e.msg)
  let lay ← (parseLayout toks).mapError fun e => (e.span, e.msg)
  return (toks, comments, lay)

/-- Formats Fren source, as lines, each with the line of `src` it comes
from. Each `segment` of `src` is laid out as a file of its own. -/
def formatLines (src : Array Char) (segment : Nat → Nat := fun _ => 0) : Except Error (Array (String × Nat)) := do
  let (toks, comments, lay) ← parseAll src
  let organized := organizeImports src toks comments lay
  let src' := ("\n".intercalate (organized.map (·.1)).toList).toList.toArray
  let (toks, comments, lay) ← if src' == src then pure (toks, comments, lay) else parseAll src'
  let origin (l : Nat) : Nat := (organized[l]?.map (·.2)).getD l
  return (layout src' toks comments lay (segment ∘ origin)).flatMap fun l =>
    (Array.replicate l.blank ("", origin l.line)).push (l.render, origin l.line)

/-- Formats a `.fren` file. -/
def formatFren (src : String) : Except Error String := do
  let lines ← formatLines src.toList.toArray
  return if lines.isEmpty then "" else "\n".intercalate (lines.map (·.1)).toList ++ "\n"

/-- The text that a file is parsed as: for a Markdown spec, its Fren code
with everything else blanked out. Errors are at offsets in it. -/
def parsedText (path src : String) : String :=
  if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src

/-- Formats a Markdown spec: its ```` ```fren ```` blocks are parsed
together, as `fren check` reads them, and each is laid out as a file of its
own. -/
def formatMarkdown (src : String) : Except Error String := do
  let lines := (src.splitOn "\n").toArray
  -- The block of each line inside a ```` ```fren ```` block.
  let mut blockOf : Array (Option Nat) := #[]
  let mut block : Option Nat := none
  let mut n := 0
  for line in lines do
    match block, Fren.Core.fenceInfo? line with
    | none, some "fren" => blockOf := blockOf.push none; block := some n; n := n + 1
    | some _, some "" => blockOf := blockOf.push none; block := none
    | some b, _ => blockOf := blockOf.push (some (b + 1))
    | none, _ => blockOf := blockOf.push none
  let segment (l : Nat) : Nat := (blockOf[l]?.join).getD 0
  let code ← formatLines (Fren.Core.unwrapMarkdown src).toList.toArray segment
  let mut out := #[]
  for h : i in [0:lines.size] do
    match blockOf[i]! with
    | none => out := out.push lines[i]
    | some b =>
      -- The block's code, in place of its first line.
      if i > 0 && blockOf[i - 1]! == some b then continue
      out := out ++ (code.filter (segment ·.2 == b)).map (·.1)
  return "\n".intercalate out.toList

/-- Formats a file, as Markdown if its name ends in `.md`. -/
def formatFile (path src : String) : Except Error String :=
  if Fren.Core.isMarkdownFile path then formatMarkdown src else formatFren src

/-! ## Diffs -/

/-- A unified diff from `old` to `new`, without context, as `diff -U0`
prints it. -/
def diff (p : Paint) (path old new : String) : String := Id.run do
  let a := (old.splitOn "\n").toArray
  let b := (new.splitOn "\n").toArray
  -- Common prefix and suffix, then the longest common subsequence.
  let mut pre := 0
  while pre < a.size && pre < b.size && a[pre]! == b[pre]! do pre := pre + 1
  let mut suf := 0
  while suf < a.size - pre && suf < b.size - pre && a[a.size - 1 - suf]! == b[b.size - 1 - suf]! do suf := suf + 1
  let a' := a.extract pre (a.size - suf)
  let b' := b.extract pre (b.size - suf)
  let n := a'.size
  let m := b'.size
  -- `lcs[i * (m + 1) + j]`: the LCS of `a'[i:]` and `b'[j:]`.
  let mut lcs := Array.replicate ((n + 1) * (m + 1)) 0
  for di in [0:n] do
    let i := n - 1 - di
    for dj in [0:m] do
      let j := m - 1 - dj
      let v := if a'[i]! == b'[j]! then lcs[(i + 1) * (m + 1) + j + 1]! + 1
        else max lcs[(i + 1) * (m + 1) + j]! lcs[i * (m + 1) + j + 1]!
      lcs := lcs.set! (i * (m + 1) + j) v
  -- Hunks: where they start in `a'` and `b'`, and their removed and added lines.
  let mut hunks : Array (Nat × Array String × Nat × Array String) := #[]
  let mut cur : Option (Nat × Array String × Nat × Array String) := none
  let mut i := 0
  let mut j := 0
  while i < n || j < m do
    if i < n && j < m && a'[i]! == b'[j]! then
      if let some h := cur then hunks := hunks.push h; cur := none
      i := i + 1; j := j + 1
    else
      let (ai, rs, bj, as) := cur.getD (i, #[], j, #[])
      if j < m && (i == n || lcs[i * (m + 1) + j + 1]! ≥ lcs[(i + 1) * (m + 1) + j]!) then
        cur := some (ai, rs, bj, as.push b'[j]!); j := j + 1
      else
        cur := some (ai, rs.push a'[i]!, bj, as); i := i + 1
  if let some h := cur then hunks := hunks.push h
  -- An empty range is named by the line before it.
  let range (start len : Nat) : String :=
    let start := if len == 0 then start else start + 1
    if len == 1 then s!"{start}" else s!"{start},{len}"
  let mut s := p.bold s!"--- {path}" ++ "\n" ++ p.bold s!"+++ {path}" ++ "\n"
  for (ai, rs, bj, as) in hunks do
    s := s ++ p.blue s!"@@ -{range (pre + ai) rs.size} +{range (pre + bj) as.size} @@" ++ "\n"
    for r in rs do s := s ++ p.removed s!"-{r}" ++ "\n"
    for x in as do s := s ++ p.added s!"+{x}" ++ "\n"
  return s

end FrenCli.Fmt
