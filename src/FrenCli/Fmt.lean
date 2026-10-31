-- keep-sorted start
import FrenCli.Parse
import FrenCore.Literate
import FrenCore.Trace
-- keep-sorted end

/-!
# `fren fmt`: Fren's standard layout (`Reqs/Fmt`)

The formatter works on the tokens and comments of a file that parses.
First it rewrites each block of imports (`fmt::in_block`,
`fmt::group_layout`). Then it decides whether each list or block is on one
line or has one element to a line (`fmt::list_layout`), from the inside
out whether it may be on one line, and from the outside in whether its
line fits, where it is its line's expression (`fmt::own_line`). It keeps
the other line breaks. It decides, for each line, its indentation
(`fmt::indent`), the spaces between its tokens (`fmt::space`), where its
trailing comment goes (`fmt::comment_column`), and how many blank lines
precede it (`fmt::blank_lines`); and it adds or removes the trailing
commas of lists (`fmt::trailing_comma`). The parser says which tokens start
an item, a member or an element, which `-` are unary, where each list or
block opens, separates its elements and closes, which other braces open
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
  /-- A range's `..=` or `..` with a bound after it but none before, as
  in `..=9`. -/
  | rangeLeading
  /-- A range's `..` with a bound before it but none after, as in `1..`. -/
  | rangeTrailing
  | comment
  | other
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Whether a space separates two tokens on a line (`fmt::space`). -/
def space (before after : Kind) : Bool :=
  if before == .comment || after == .comment then true
  else if before == .brace && after == .closeBrace then false
  -- `--` starts a comment.
  else if before == .negation && after == .negation then true
  else !(before matches .paren | .call | .group | .path | .negation | .rangeLeading) &&
    !(after matches .closeParen | .closeGroup | .path | .comma | .colon | .group | .call | .rangeTrailing)

/-- What a line's first token does (`fmt::indent`). -/
inductive LineStart where
  | closing
  | starting
  | continuing
  deriving BEq, DecidableEq, Repr

/-- An opening bracket (`fmt::Bracket`). -/
inductive Bracket where
  | paren
  | square
  | curly
  /-- `::{`. -/
  | pathCurly
  deriving BEq, DecidableEq, Repr

/-- Whether a bracket indents the lines inside it (`fmt::indents?`): a
brace, or one that opens a list or block. -/
def bracketIndents (b : Bracket) (list : Bool) : Bool := b matches .curly | .pathCurly || list

/-- A bracket open at the start of a line: its kind, whether it opens a
list or block, and the indentation of the line that opens it. -/
abbrev OpenBracket := Bracket × Bool × Nat

/-- Four more than the line that opens the innermost of the open brackets,
given innermost first, that indents, or 0 outside every one
(`fmt::base`). -/
def base : List OpenBracket → Nat
  | [] => 0
  | (b, l, line) :: rest => if bracketIndents b l then line + 4 else base rest

/-- The indentation of a line, in spaces (`fmt::indent`), inside the
open `brackets`, the innermost first. -/
def indent (brackets : List OpenBracket) (start : LineStart) (comment : Bool) : Nat :=
  match start with
  | .closing => if comment then base brackets else (brackets.head?.map (·.2.2)).getD 0
  | .starting => base brackets
  | .continuing => base brackets + 4

/-- The column of a trailing comment, after code `width` wide, that started
at column `original` (`fmt::comment_column`). -/
def commentColumn (width original : Nat) : Nat :=
  if original ≥ width + 2 then original else width + 2

/-- The blank lines kept before a line (`fmt::blank_lines`). -/
def blankLines (blank : Nat) (first afterOpen beforeClose : Bool) : Nat :=
  if first || afterOpen || beforeClose || blank == 0 then 0 else 1

/-- The widest that a list of kind `k` may be on one line, its elements
separated by `, `, as rustfmt's defaults have it (`fmt::width_limit`). -/
def widthLimit : ListKind → Nat
  | .arms => 0
  | .arguments | .applicationArguments => 60
  | .parameters | .functionParameters => 100
  | .elements => 60
  | .fields => 18

/-- The widest a line may be, as rustfmt's `max_width`. -/
def maxWidth : Nat := 100

/-- Whether a vertical list of kind `k` ends with a comma
(`fmt::ends_with_comma?`): the syntax allows one but for the arguments of
an application and the parameters of a function. -/
def endsWithComma : ListKind → Bool
  | .applicationArguments | .functionParameters => false
  | _ => true

/-- Whether a list of kind `k`, with `n` elements, is vertical
(`fmt::one_line`): its elements `width` wide on one line, separated by `, `,
the first starting at column `start`, and the line ending at column `end_`,
which counts only if `ownLine` and the line fits up to the first element. -/
def vertical (k : ListKind) (n : Nat) (broken : Bool) (width start end_ : Nat) (ownLine : Bool) : Bool :=
  n > 0 && ((k matches .arms) || broken || width > widthLimit k || (ownLine && start ≤ maxWidth && end_ > maxWidth))

/-- The width of elements `ws` wide on one line, separated by `, `. -/
def joinedWidth : List Nat → Nat
  | [] => 0
  | [w] => w
  | w :: ws => w + 2 + joinedWidth ws

/-- Whether a list of kind `k` is vertical (`fmt::list_layout`), from its
elements, each with its width on one line and whether it cannot be written
on one line, the column where its first element would start, the width
of what would follow its last on that line, and whether it is its line's
expression. -/
def listLayout (k : ListKind) (es : List (Nat × Bool)) (start after : Nat) (ownLine : Bool) : Bool :=
  let width := joinedWidth (es.map (·.1))
  vertical k es.length (es.any (·.2)) width start (start + width + after) ownLine

/-- A token that follows a list's closing bracket on its line
(`fmt::Follower`). -/
inductive Follower where
  /-- `)`, `]` or `}`. -/
  | closing
  | comma
  /-- `=>`. -/
  | arrow
  /-- The `>` that closes a type's arguments. -/
  | typeClosing
  /-- A bracket that indents. -/
  | opening
  | other
  deriving BEq, DecidableEq, Repr

/-- Whether only closing tokens follow a list (`fmt::only_closing?`). -/
def onlyClosing : List Follower → Bool
  | [] => true
  | f :: fs => !(f matches .other) && onlyClosing fs

/-- Whether a list from offset `head` to offset `close` is the whole of
the right operand `operand`, its start and end, if any (`fmt::whole?`). -/
def whole (operand : Option (Nat × Nat)) (head close : Nat) : Bool :=
  match operand with
  | none => false
  | some (start, stop) => decide (start = head) && decide (stop = close)

/-- Whether, in each expression that holds a list of kind `k` from offset
`head` to offset `close`, given by the columns before the list's head and
its right operand, at most 4 columns come before the head, but where a
record is that whole operand (`fmt::heads_near?`). -/
def headsNear (k : ListKind) (head close : Nat) : List (Nat × Option (Nat × Nat)) → Bool
  | [] => true
  | (cols, operand) :: hs => (cols ≤ 4 || (k matches .fields && whole operand head close)) && headsNear k head close hs

/-- Whether a list of kind `k`, from offset `head` to offset `close`, is
its line's expression (`fmt::own_line`): it is a signature's parameters or
results, or only closing tokens `follows` it, and in each expression that
holds it and starts on its line, given by the columns before its head and
its right operand, at most 4 columns come before its head, but where a
record is that whole operand. -/
def ownLine (k : ListKind) (follows : List Follower) (head close : Nat)
    (holders : List (Nat × Option (Nat × Nat))) : Bool :=
  (k matches .parameters | .functionParameters) || (onlyClosing follows && headsNear k head close holders)

/-- Whether the last element of a list is followed by a comma
(`fmt::trailing_comma`), where `allowed` says that its syntax allows one. -/
def trailingComma (empty vertical allowed : Bool) : Bool := !empty && vertical && allowed

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
  /-- Its last piece opens a bracket that indents the lines after it. -/
  endsOpen : Bool := false
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

/-- The width of a line's last row, rendered. -/
def Line.width (l : Line) : Nat := ((l.render.splitOn "\n").getLast?.getD "").length

/-- Where a line break between two pieces is decided by a list or block:
after its opening bracket, after the comma that ends one of its elements,
or before its closing bracket. -/
inductive Role where
  | afterOpen
  | afterComma
  | beforeClose
  /-- After the `{` of a record update, before the record it updates: never
  a line break. -/
  | joined
  deriving BEq, Inhabited

/-- What the layout of a list or block is decided from: each element's
width on one line and whether it cannot be written on one line, and the
pieces where each element ends, at its comma or the closing bracket. -/
structure ListInfo where
  elements : Array (Nat × Bool) := #[]
  /-- It, and every list and block in it, may be written on one line
  (`fmt::one_line`, with the line's end left out). -/
  flat : Bool := true
  deriving Inhabited

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
  let tokLine (k : Nat) : Nat := lineOf[toks[k]!.span.start]!
  let isTok (k : Nat) (s : String) : Bool := toks[k]!.tok == .kw s
  let lists := lay.bracketed
  -- The trailing comma of each list or block, which its layout decides.
  let mut trailing : Std.HashSet Nat := {}
  for b in lists do
    if let some k := b.commas.back? then
      if k + 1 == b.closing then trailing := trailing.insert k
  -- `tested` claims: whether each is vertical, by its last string.
  let claimVertical (k : Nat) : Option Bool :=
    (lay.claims.find? (·.2 == k)).map fun (t, _) => tokLine k > tokLine t
  -- Tokens and comments, in order, but for the trailing commas that the
  -- layout decides.
  let mut sorted : Array (Nat × Piece) := #[]
  for k in [0:toks.size - 1] do
    if trailing.contains k then continue
    -- The trailing comma of a claim that is not vertical.
    if isTok k "," && k > 0 && claimVertical (k - 1) == some false then continue
    sorted := sorted.push (toks[k]!.span.start, mkPiece toks[k]!.span (some k))
  for c in comments do
    sorted := sorted.push (c.start, mkPiece c none)
  let pieces := (sorted.qsort (·.1 < ·.1)).map (·.2)
  let mut pieceOf : Std.HashMap Nat Nat := {}
  for h : i in [0:pieces.size] do
    if let some k := pieces[i].tok? then pieceOf := pieceOf.insert k i
  let pieceAt (k : Nat) : Nat := pieceOf.getD k 0
  -- Each closing bracket's opening one.
  let mut openerOf : Std.HashMap Nat Nat := {}
  let mut unclosed : Array Nat := #[]
  for k in [0:toks.size] do
    match toks[k]!.tok with
    | .kw "(" | .kw "[" | .kw "{" | .kw "::{" => unclosed := unclosed.push k
    | .kw ")" | .kw "]" | .kw "}" =>
      if let some o := unclosed.back? then openerOf := openerOf.insert k o; unclosed := unclosed.pop
    | _ => pure ()
  let mut listOf : Std.HashMap Nat Nat := {}
  let mut listAtLead : Std.HashMap Nat Nat := {}
  for h : c in [0:lists.size] do
    listOf := listOf.insert lists[c].opening c
    listAtLead := listAtLead.insert lists[c].lead c
  -- Brackets that indent the lines inside them: braces, and those of the
  -- lists and blocks.
  let indents (k : Nat) : Bool := isTok k "{" || isTok k "::{" || listOf.contains k
  let bracketAt? (k : Nat) : Option Bracket :=
    if isTok k "(" then some .paren else if isTok k "[" then some .square
    else if isTok k "{" then some .curly else if isTok k "::{" then some .pathCurly else none
  let kindOf (p : Piece) : Kind := match p.tok? with
    | none => .comment
    | some k =>
      match toks[k]!.tok with
      | .kw "(" => if lay.calls.contains k then .call else .paren
      | .kw ")" => .closeParen
      -- A closure's parameters, spaced like a call's arguments.
      | .kw "|" => if lay.closureOpens.contains k then .paren else if lay.closureCloses.contains k then .closeParen else .other
      -- An index's `[` is spaced like a call's `(`, and a literal's like `(`.
      | .kw "[" => if lay.calls.contains k then .call else .paren
      | .kw "]" => .closeParen
      -- Type arguments' and type parameters' `<` and `>` are spaced like
      -- a call's `(` and `)`; a comparison's are not.
      | .kw "<" => if lay.calls.contains k then .call else .other
      | .kw ">" => if lay.calls.contains k then .closeParen else .other
      -- A set literal's braces are spaced like parentheses.
      | .kw "{" => if lay.sets.contains k then .paren else .brace
      | .kw "::{" => .group
      | .kw "}" =>
        match openerOf[k]? with
        | some o => if isTok o "::{" then .closeGroup else if lay.sets.contains o then .closeParen else .closeBrace
        | none => .closeBrace
      | .kw "::" | .kw "." => .path
      -- A range's operator touches its bounds.
      | .kw ".." | .kw "..=" =>
        match lay.rangeLower.contains k, lay.rangeUpper.contains k with
        | true, true => .path
        | false, true => .rangeLeading
        | true, false => .rangeTrailing
        | false, false => .other
      -- Ends a path, so a space follows it, as one follows `)`.
      | .kw "::*" => .closeParen
      | .kw "," => .comma
      | .kw ":" => .colon
      | .kw "-" => if lay.unary.contains k then .negation else .other
      | _ => .other
  let kinds := pieces.map kindOf
  let isComment (i : Nat) : Bool := pieces[i]!.tok?.isNone
  let lineComment (i : Nat) : Bool := isComment i && isLineComment pieces[i]!.text
  -- The gap before each piece: whether a line ends in it in the source,
  -- whether it is between segments, and its blank lines.
  let inBreak (i : Nat) : Bool := i > 0 && pieces[i]!.startLine > pieces[i - 1]!.endLine
  let boundary (i : Nat) : Bool := i == 0 || segment pieces[i]!.startLine != segment pieces[i - 1]!.endLine
  let blankIn (i : Nat) : Nat := if boundary i then 0 else pieces[i]!.startLine - pieces[i - 1]!.endLine - 1
  -- The gaps whose line breaks a list or block decides: each is before a
  -- token.
  let mut governed : Array (Option (Nat × Role)) := Array.replicate pieces.size none
  for h : c in [0:lists.size] do
    let b := lists[c]
    if b.closing == b.opening + 1 then continue
    governed := governed.set! (pieceAt (b.lead + 1)) (some (c, .afterOpen))
    if b.lead != b.opening then governed := governed.set! (pieceAt (b.opening + 1)) (some (c, .joined))
    for k in b.commas do
      if !trailing.contains k then governed := governed.set! (pieceAt (k + 1)) (some (c, .afterComma))
    governed := governed.set! (pieceAt b.closing) (some (c, .beforeClose))
  -- The gaps where a line must end whatever the layout: between segments,
  -- after a line comment, where the source breaks the line and no list
  -- decides, and at a blank line between two elements.
  let forced (i : Nat) : Bool :=
    boundary i || (i > 0 && lineComment (i - 1)) || (governed[i]!.isNone && inBreak i)
      || (governed[i]! matches some (_, .afterComma) && blankIn i > 0)
  -- The width of pieces `a` to `b`, exclusive, on one line.
  let flatWidth (a b : Nat) : Nat := Id.run do
    let mut w := 0
    for j in [a:b] do
      w := w + pieces[j]!.text.length + (if j > a && space kinds[j - 1]! kinds[j]! then 1 else 0)
    return w
  -- Each list's elements, from the innermost out (`fmt::list_layout`).
  let mut infos : Array ListInfo := Array.replicate lists.size {}
  let order := (Array.range lists.size).qsort fun a b =>
    lists[a]!.closing - lists[a]!.opening < lists[b]!.closing - lists[b]!.opening
  for c in order do
    let b := lists[c]!
    if b.closing == b.opening + 1 then continue
    let ends := (b.commas.filter (!trailing.contains ·)).map pieceAt |>.push (pieceAt b.closing)
    let mut start := pieceAt b.lead
    let mut elements := #[]
    for e in ends do
      let mut broken := false
      for j in [start + 1:e + 1] do
        if forced j || (j < e && pieces[j]!.startLine != pieces[j]!.endLine) then broken := true
        if j < e then
          if let some k := pieces[j]!.tok? then
            if let some d := listOf[k]? then
              if !infos[d]!.flat then broken := true
      elements := elements.push (flatWidth (start + 1) e, broken)
      start := e
    let es := elements.toList
    let width := joinedWidth (es.map (·.1))
    infos := infos.set! c { elements, flat := !vertical b.kind es.length (es.any (·.2)) width 0 0 false }
  -- What a token that follows a list's closing bracket on its line is
  -- (`fmt::Follower`).
  let follower (k : Nat) : Follower :=
    if isTok k ")" || isTok k "]" || isTok k "}" then .closing
    else if isTok k "," then .comma
    else if isTok k "=>" then .arrow
    else if isTok k ">" && lay.calls.contains k then .typeClosing
    else if indents k then .opening
    else .other
  -- The width of what follows piece `i`, which closes a list of kind `kind`,
  -- on its line, up to where a line may end, with the comma that a vertical
  -- list adds, and what those tokens are. After parameters, it counts only
  -- up to the signature's `:=`, as rustfmt counts a signature to its ` {`.
  let suffix (vertical : Array Bool) (kind : ListKind) (i : Nat) : Nat × List Follower := Id.run do
    let signature := kind matches .parameters | .functionParameters
    let mut w := 0
    let mut follows := #[]
    let mut j := i + 1
    while j < pieces.size do
      if isComment j || forced j || governed[j]!.isSome then break
      w := w + pieces[j]!.text.length + (if space kinds[j - 1]! kinds[j]! then 1 else 0)
      j := j + 1
      if let some k := pieces[j - 1]!.tok? then
        follows := follows.push (follower k)
        if signature && isTok k ":=" then return (w, follows.toList)
        -- A line may end after an opening bracket that indents.
        if indents k then return (w, follows.toList)
    if let some (some (c, .beforeClose)) := governed[j]? then
      if vertical[c]! && endsWithComma lists[c]!.kind then w := w + 1
    return (w, follows.toList)
  let mut out : Array Line := #[]
  let mut vertical : Array Bool := Array.replicate lists.size false
  -- The open brackets, the innermost first, each with its token
  -- (`fmt::indent`'s `brackets`).
  let mut stack : List (Nat × OpenBracket) := []
  -- The closing bracket of the list on one line that the pieces are in.
  let mut flatUntil : Option Nat := none
  -- The last token: its line in `out`, its index there, and its index.
  let mut last? : Option (Nat × Nat × Nat) := none
  -- The line in `out` of each token placed so far.
  let mut outLine : Std.HashMap Nat Nat := {}
  -- The first token of the last line, and whether that line continues an
  -- item, a member or an element.
  let mut lineFirst : Option Nat := none
  let mut continues := false
  let mut tokAt : Std.HashMap Nat Nat := {}
  for h : k in [0:toks.size] do tokAt := tokAt.insert toks[k].span.start k
  for h : i in [0:pieces.size] do
    let p := pieces[i]
    let brk := i == 0 || forced i || (governed[i]!.any fun (c, r) => r != .joined && vertical[c]!)
    -- Token `k` closes the innermost open bracket, which indents.
    let closesTop (k : Nat) : Bool :=
      openerOf[k]?.any fun o => stack.head?.any fun (t, b, l, _) => t == o && bracketIndents b l
    if let some k := p.tok? then
      -- Trailing commas, at the closing bracket of a list.
      let comma? : Option Bool :=
        if let some c := (openerOf[k]?.bind (listOf[·]?)) then
          let b := lists[c]!
          some (trailingComma (b.closing == b.opening + 1) vertical[c]! (endsWithComma b.kind))
        else if (openerOf[k]?.any lay.lists.contains) then
          openerOf[k]?.map fun o => trailingComma (last?.any (·.2.2 == o)) brk true
        else none
      if let some want := comma? then
        if let some (li, pi, lk) := last? then
          let had := isTok lk ","
          if want && !had then
            out := out.modify li fun l => { l with pieces := l.pieces.insertIdxIfInBounds (pi + 1) (.comma, ",") }
          else if !want && had then
            out := out.modify li fun l => { l with pieces := l.pieces.eraseIdxIfInBounds pi }
    if brk then
      -- A comment is indented as the next token.
      let next? := match p.tok? with
        | some k => some (k, i)
        | none => ((pieces.extract (i + 1)).zipIdx.findSome? fun ((q : Piece), j) => q.tok?.map (·, i + 1 + j))
      let start := match next? with
        | some (k, j) =>
          if closesTop k then LineStart.closing
          else if lay.starts.contains k || governed[j]!.any (fun (_, r) => r == .afterOpen || r == .afterComma) then .starting
          else .continuing
        | none => .starting
      let columns := indent (stack.map (·.2)) start p.tok?.isNone
      let first := boundary i
      let afterOpen := out.back?.any (·.endsOpen)
      let beforeClose := p.tok?.any closesTop
      let kept := blankLines (blankIn i) first afterOpen beforeClose
      out := out.push { blank := kept, indent := columns, pieces := #[], line := p.startLine }
      lineFirst := none
      continues := start == .continuing
    let opens := p.tok?.any indents
    out := out.modify (out.size - 1) fun l =>
      { l with pieces := l.pieces.push (kinds[i]!, p.text), commentCol := if p.tok?.isNone then p.col else l.commentCol
               endsOpen := opens }
    let some k := p.tok? | continue
    last? := some (out.size - 1, out.back!.pieces.size - 1, k)
    outLine := outLine.insert k (out.size - 1)
    if lineFirst.isNone then lineFirst := some k
    -- The head of list `b`, the names before its opening bracket.
    let headOf (b : Bracketed) : Nat := Id.run do
      let mut h := b.opening
      while h > 0 && (toks[h - 1]!.tok matches .ident _ || isTok (h - 1) "::" || isTok (h - 1) ".") do h := h - 1
      return h
    -- The expressions that hold list `b`, on the last line, and start on
    -- that line (`fmt::own_line`'s `holders`): for each, the columns before
    -- the list's head, and the span of its right operand, as the parser
    -- reads it, where it is the operation of a binary operator. A line
    -- that continues an expression starts one, after its operator.
    let holders (b : Bracketed) : List (Nat × Option (Nat × Nat)) := Id.run do
      let h := headOf b
      let here := out.size - 1
      let closeStop := toks[b.closing]!.span.stop
      let before (f : Nat) : Nat := if f ≥ h then 0 else flatWidth (pieceAt f) (pieceAt h)
      let mut hs : Array (Nat × Option (Nat × Nat)) := #[]
      if let some f := lineFirst then
        if continues then
          hs := hs.push (before (if toks[f]!.tok matches .kw _ && !indents f then f + 1 else f), none)
      for e in lay.exprs do
        if let some f := tokAt[e.start]? then
          if outLine[f]? == some here && closeStop ≤ e.stop then
            let operand := (lay.pairs.find? (·.1 == e)).map fun (_, r) => (r.start, r.stop)
            hs := hs.push (before f, operand)
      return hs.toList
    if claimVertical k == some true && !isTok (k + 1) "," then
      out := out.modify (out.size - 1) fun l => { l with pieces := l.pieces.push (.comma, ",") }
    if let some br := bracketAt? k then stack := (k, br, listOf.contains k, out.back!.indent) :: stack
    if let some c := listAtLead[k]? then
      let b := lists[c]!
      -- A list inside one on one line is on that line too.
      if flatUntil.isNone && b.closing != b.opening + 1 then
        let info := infos[c]!
        let v := if !info.flat then true else
          let close := pieceAt b.closing
          let gap (j : Nat) : Nat := if space kinds[j - 1]! kinds[j]! then 1 else 0
          let (after, follows) := suffix vertical b.kind close
          let own := ownLine b.kind follows toks[headOf b]!.span.start toks[b.closing]!.span.stop (holders b)
          listLayout b.kind info.elements.toList (out.back!.width + gap (i + 1))
            (gap close + pieces[close]!.text.length + after) own
        vertical := vertical.set! c v
        if !v then flatUntil := some b.closing
    if (openerOf[k]?.any fun o => stack.head?.any (·.1 == o)) then stack := stack.tail
    if flatUntil == some k then flatUntil := none
  return out

/-- An error that stops a file from being formatted. -/
abbrev Error := Span × Msg

def parseAll (src : Array Char) : Except Error (Array Token × Array Span × Layout) := do
  let (toks, comments) ← (lexWithComments src).mapError fun e => (e.span, e.msg)
  let lay ← (parseLayout toks src).mapError fun e => (e.span, e.msg)
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
