-- keep-sorted start
import FrenCli.Fmt
import Impls.View
import Reqs.Fmt
-- keep-sorted end
open Fren.Lang

/-! # Formatting (`Reqs/Fmt`) -/

namespace Fren.Impls

open FrenCli.Fmt (Kind LineStart)

/-! ## Claims -/

tested fmt::safe: "src/FrenTestMain.lean"

/-! ## Implementations -/

instance : Fren.Finite Kind :=
  ⟨[.paren, .call, .closeParen, .brace, .closeBrace, .group, .closeGroup, .path, .comma, .colon, .negation, .comment, .other],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite LineStart := ⟨[.closing, .starting, .continuing], by intro x; cases x <;> simp⟩

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
  | .comment => .Comment
  | .other => .Other

def toFmtLineStart : LineStart → fmt.LineStart
  | .closing => .Closing
  | .starting => .Starting
  | .continuing => .Continuing

impl space: fmt::space for (b a : Kind) {
  before := toFmtKind b,
  after := toFmtKind a,
  space? := FrenCli.Fmt.space b a,
}

-- Over `Nat`, so `decide` does not apply: proofs by cases.
impl indent: fmt::indent for (d : Nat) (s : LineStart) (c : Bool) {
  depth := d,
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

impl trailing_comma: fmt::trailing_comma for (e v : Bool) {
  empty? := e,
  vertical? := v,
  comma? := FrenCli.Fmt.trailingComma e v,
}

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
