-- keep-sorted start
import FrenCli.Fmt
import Impls.View
import Reqs.Fmt
-- keep-sorted end
open Fren.Lang

/-! # Formatting (`Reqs/Fmt`) -/

namespace Fren.Impls

open FrenCli (ListKind)
open FrenCli.Fmt (Bracket Follower Kind LineStart OpenBracket)

instance : Fren.Finite Kind :=
  ⟨[.paren, .call, .closeParen, .brace, .closeBrace, .group, .closeGroup, .path, .comma, .colon, .negation, .rangeLeading, .rangeTrailing, .comment, .other],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite LineStart := ⟨[.closing, .starting, .continuing], by intro x; cases x <;> simp⟩

instance : Fren.Finite ListKind :=
  ⟨[.arms, .arguments, .applicationArguments, .parameters, .functionParameters, .elements, .fields, .members],
    by intro x; cases x <;> simp⟩

def toFmtKind : Kind → fmt.Kind
  | .paren => .Open
  | .call => .Call
  | .closeParen => .Close
  | .brace => .Brace
  | .closeBrace => .CloseBrace
  | .group => .Group
  | .closeGroup => .CloseGroup
  | .path => .Path
  | .comma => .Comma
  | .colon => .Colon
  | .negation => .Negation
  | .rangeLeading => .RangeLeading
  | .rangeTrailing => .RangeTrailing
  | .comment => .Comment
  | .other => .Other

def toFmtListKind : ListKind → fmt.ListKind
  | .arms => .Arms
  | .arguments => .Arguments
  | .applicationArguments => .ApplicationArguments
  | .parameters => .Parameters
  | .functionParameters => .FunctionParameters
  | .elements => .Elements
  | .fields => .Fields
  | .members => .Members

/-- A list's elements, each with its width on one line and whether it must
span several lines. -/
def toElementList : List (Nat × Bool) → fmt.ElementList
  | [] => .Nil
  | (w, b) :: es => .Cons w b (toElementList es)

def toFmtBracket : Bracket → fmt.Bracket
  | .paren => .Paren
  | .square => .Square
  | .curly => .Curly
  | .pathCurly => .PathCurly

/-- The brackets open at the start of a line, the innermost first. -/
def toOpenBrackets : List OpenBracket → fmt.OpenBrackets
  | [] => .Nil
  | (b, l, line) :: rest => .Within (toFmtBracket b) l line (toOpenBrackets rest)

def toFollower : Follower → fmt.Follower
  | .closing => .Closing
  | .comma => .Comma
  | .arrow => .Arrow
  | .typeClosing => .TypeClosing
  | .opening => .Opening
  | .other => .Other

def toFollowers : List Follower → fmt.Followers
  | [] => .Nil
  | f :: fs => .Then (toFollower f) (toFollowers fs)

def toOperand : Option (Nat × Nat) → fmt.Operand
  | none => .Absent
  | some (start, stop) => .Spans start stop

def toHolders : List (Nat × Option (Nat × Nat)) → fmt.Holders
  | [] => .Nil
  | (c, o) :: hs => .Holder c (toOperand o) (toHolders hs)

def toFmtLineStart : LineStart → fmt.LineStart
  | .closing => .Closing
  | .starting => .Starting
  | .continuing => .Continuing

impl space: fmt::space for (b a : Kind) {
  before := toFmtKind b,
  after := toFmtKind a,
  space? := FrenCli.Fmt.space b a,
} by
  intro b a _
  revert a
  cases b <;> decide

theorem indents_toFmtBracket (b : Bracket) (l : Bool) :
    fmt.«indents?» (toFmtBracket b) l = FrenCli.Fmt.bracketIndents b l := by
  cases b <;> cases l <;> rfl

theorem base_toOpenBrackets (o : List OpenBracket) :
    fmt.base (toOpenBrackets o) = (FrenCli.Fmt.base o : Int) := by
  induction o with
  | nil => simp [toOpenBrackets, fmt.base, FrenCli.Fmt.base]
  | cons e o ih =>
    obtain ⟨b, l, line⟩ := e
    simp only [toOpenBrackets, fmt.base, FrenCli.Fmt.base, indents_toFmtBracket, ih]
    split <;> simp_all

-- Over `Nat`, so `decide` does not apply: proofs by cases.
impl indent: fmt::indent for (o : List OpenBracket) (s : LineStart) (c : Bool) {
  brackets := toOpenBrackets o,
  start := toFmtLineStart s,
  comment? := c,
  columns := FrenCli.Fmt.indent o s c,
} by
  intro o s c _
  cases o with
  | nil =>
    cases s <;> cases c <;> simp_all [fren_spec, FrenCli.Fmt.indent, FrenCli.Fmt.base, toFmtLineStart, toOpenBrackets]
  | cons e o =>
    obtain ⟨b, l, line⟩ := e
    have hb := base_toOpenBrackets ((b, l, line) :: o)
    cases hi : FrenCli.Fmt.bracketIndents b l <;> cases s <;> cases c <;>
      simp_all [fren_spec, FrenCli.Fmt.indent, FrenCli.Fmt.base, toFmtLineStart, toOpenBrackets] <;> omega

impl comment_column: fmt::comment_column for (w o : Nat) {
  width := w,
  original := o,
  column := FrenCli.Fmt.commentColumn w o,
} by
  intro w o _
  unfold FrenCli.Fmt.commentColumn
  split <;> simp [fren_spec] <;> omega

impl blank_lines: fmt::blank_lines for (b : Nat) (f ao bc : Bool) {
  blank := b,
  first? := f,
  after_open? := ao,
  before_close? := bc,
  kept := FrenCli.Fmt.blankLines b f ao bc,
} by
  intro b f ao bc _
  cases f <;> cases ao <;> cases bc <;> rcases b with _ | b <;> simp [fren_spec, FrenCli.Fmt.blankLines] <;> omega

impl trailing_comma: fmt::trailing_comma for (e v a : Bool) {
  empty? := e,
  vertical? := v,
  allowed? := a,
  comma? := FrenCli.Fmt.trailingComma e v a,
}

impl one_line: fmt::one_line for (k : ListKind) (n : Nat) (b : Bool) (w s e : Nat) (l : Bool) {
  list := toFmtListKind k,
  n := n,
  broken? := b,
  width := w,
  start := s,
  line_end := e,
  own_line? := l,
  vertical? := FrenCli.Fmt.vertical k n b w s e l,
} by
  intro k n b w s e l _
  cases k <;> cases b <;> cases l <;> simp [fren_spec, FrenCli.Fmt.vertical, FrenCli.Fmt.widthLimit, FrenCli.Fmt.maxWidth,
    toFmtListKind] <;> omega

theorem only_closing_toFollowers (fs : List Follower) :
    fmt.«only_closing?» (toFollowers fs) = FrenCli.Fmt.onlyClosing fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [toFollowers, toFollower, fmt.«only_closing?», FrenCli.Fmt.onlyClosing, ih]

theorem whole_toOperand (o : Option (Nat × Nat)) (head close : Nat) :
    fmt.«whole?» (toOperand o) head close = FrenCli.Fmt.whole o head close := by
  rcases o with _ | ⟨start, stop⟩
  · rfl
  · simp only [toOperand, fmt.«whole?», FrenCli.Fmt.whole, fmt.Operand.Spans.x0, fmt.Operand.Spans.x1]
    have e1 : ((start : Int) = head) ↔ start = head := by omega
    have e2 : ((stop : Int) = close) ↔ stop = close := by omega
    simp [e1, e2]

theorem heads_near_toHolders (k : ListKind) (head close : Nat) (hs : List (Nat × Option (Nat × Nat))) :
    fmt.«heads_near?» (toFmtListKind k) head close (toHolders hs) = FrenCli.Fmt.headsNear k head close hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    obtain ⟨c, o⟩ := h
    have hc : ((c : Int) ≤ 4) ↔ c ≤ 4 := by omega
    simp only [toHolders, fmt.«heads_near?», FrenCli.Fmt.headsNear, ih, whole_toOperand]
    cases k <;> simp [toFmtListKind, hc]

impl own_line: fmt::own_line for (k : ListKind) (fs : List Follower) (head close : Nat)
    (hs : List (Nat × Option (Nat × Nat))) {
  list := toFmtListKind k,
  followers := toFollowers fs,
  head := head,
  close := close,
  holders := toHolders hs,
  own_line? := FrenCli.Fmt.ownLine k fs head close hs,
} by
  intro k fs head close hs _
  simp only [fren_spec, only_closing_toFollowers, heads_near_toHolders, FrenCli.Fmt.ownLine]
  generalize FrenCli.Fmt.onlyClosing fs = a
  generalize FrenCli.Fmt.headsNear k head close hs = b
  cases k <;> cases a <;> cases b <;> simp [toFmtListKind]

theorem count_toElementList (es : List (Nat × Bool)) : fmt.count (toElementList es) = es.length := by
  induction es with
  | nil => simp [toElementList, fmt.count]
  | cons e es ih => simp [toElementList, fmt.count, ih]; omega

theorem any_broken_toElementList (es : List (Nat × Bool)) :
    fmt.«any_broken?» (toElementList es) = es.any (·.2) := by
  induction es with
  | nil => simp [toElementList, fmt.«any_broken?»]
  | cons e es ih => simp [toElementList, fmt.«any_broken?», ih]

theorem joined_toElementList (es : List (Nat × Bool)) :
    fmt.joined (toElementList es) = FrenCli.Fmt.joinedWidth (es.map (·.1)) := by
  induction es with
  | nil => simp [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]
  | cons e es ih =>
    cases es with
    | nil => simp [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]
    | cons f fs => simp_all [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]

impl list_layout: fmt::list_layout for (k : ListKind) (es : List (Nat × Bool)) (s a : Nat) (l : Bool) {
  list := toFmtListKind k,
  elements := toElementList es,
  start := s,
  after := a,
  own_line? := l,
  vertical? := FrenCli.Fmt.listLayout k es s a l,
} by
  intro k es s a l _
  simp only [fren_spec, count_toElementList, any_broken_toElementList, joined_toElementList,
    FrenCli.Fmt.listLayout]
  generalize es.any (·.2) = b
  generalize FrenCli.Fmt.joinedWidth (es.map (·.1)) = w
  generalize es.length = n
  cases k <;> cases b <;> cases l <;> simp [FrenCli.Fmt.vertical, FrenCli.Fmt.widthLimit, FrenCli.Fmt.maxWidth,
    toFmtListKind] <;> omega

impl group_layout: fmt::group_layout for (n : Nat) (wv fits : Bool) {
  n_paths := n,
  was_vertical? := wv,
  fits? := fits,
  braces? := (FrenCli.Fmt.groupLayout n wv fits).1,
  vertical? := (FrenCli.Fmt.groupLayout n wv fits).2,
} by
  intro n wv fits _
  cases wv <;> cases fits <;> simp [fren_spec, FrenCli.Fmt.groupLayout] <;> omega

def toNeighbour : Option Nat → fmt.Neighbour
  | none => .Edge
  | some l => .OnLine l

impl in_block: fmt::in_block for (f l : Nat) (b a : Option Nat) (c n : Bool) {
  first_line := f,
  last_line := l,
  before := toNeighbour b,
  after := toNeighbour a,
  commented? := c,
  nested? := n,
  alone? := FrenCli.Fmt.useAlone f l b a c,
  sorted? := FrenCli.Fmt.inBlock (FrenCli.Fmt.useAlone f l b a c) n,
} by
  intro f l b a c n _
  cases b <;> cases a <;> cases c <;> cases n <;>
    simp [fren_spec, FrenCli.Fmt.useAlone, FrenCli.Fmt.inBlock, toNeighbour]

impl file: fmt::file for (c i p f : Bool) {
  check? := c,
  ignored? := i,
  parsed? := p,
  formatted? := f,
  written? := (FrenCli.Fmt.fileAction c i p f).1,
  diff? := (FrenCli.Fmt.fileAction c i p f).2,
} by
  intro c i p f _
  cases c <;> cases i <;> cases p <;> cases f <;> decide

impl exit: fmt::exit for (c p f : Bool) {
  check? := c,
  all_parsed? := p,
  all_formatted? := f,
  code := (FrenCli.Fmt.exitCode c p f).toNat,
}

end Fren.Impls
