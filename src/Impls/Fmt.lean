-- keep-sorted start
import FrenCli.Fmt
import Impls.View
import Reqs.Fmt
-- keep-sorted end
open Fren.Lang

/-! # Formatting (`Reqs/Fmt`) -/

namespace Fren.Impls

open FrenCli (ListKind)
open FrenCli.Fmt (Kind LineStart)

instance : Fren.Finite Kind :=
  ⟨[.paren, .call, .closeParen, .brace, .closeBrace, .group, .closeGroup, .path, .comma, .colon, .negation, .rangeLeading, .rangeTrailing, .comment, .other],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite LineStart := ⟨[.closing, .starting, .continuing], by intro x; cases x <;> simp⟩

instance : Fren.Finite ListKind :=
  ⟨[.arms, .arguments, .applicationArguments, .parameters, .functionParameters, .elements, .fields],
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

/-- A list's elements, each with its width on one line and whether it must
span several lines. -/
def toElementList : List (Nat × Bool) → fmt.ElementList
  | [] => .Nil
  | (w, b) :: es => .Cons w b (toElementList es)

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

-- Over `Nat`, so `decide` does not apply: proofs by cases.
impl indent: fmt::indent for (d : Nat) (s : LineStart) (c : Bool) {
  base := d,
  start := toFmtLineStart s,
  comment? := c,
  columns := FrenCli.Fmt.indent d s c,
} by
  intro d s c _
  cases s <;> cases c <;> simp_all [fren_spec, FrenCli.Fmt.indent, toFmtLineStart] <;> omega

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

impl in_block: fmt::in_block for (a n : Bool) {
  alone? := a,
  nested? := n,
  sorted? := FrenCli.Fmt.inBlock a n,
}

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
