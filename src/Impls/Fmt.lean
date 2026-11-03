-- keep-sorted start
import FrenCli.Fmt
import Impls.View
import Reqs.Fmt
-- keep-sorted end
open Fren.Lang

/-! # Formatting (`Reqs/Fmt`) -/

namespace Fren.Impls

open FrenCli (ListKind)
open FrenCli.Fmt (Bracket Follower Kind LineStart OpenBracket PieceKind)

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

/-- A list's elements, each with its width on one line, whether it must
span several lines and whether it holds a wide record. -/
def toElementList : List (Nat × Bool × Bool) → fmt.ElementList
  | [] => .Nil
  | (w, b, d) :: es => .Cons w b d (toElementList es)

def toFmtBracket : Bracket → fmt.Bracket
  | .paren => .Paren
  | .square => .Square
  | .curly => .Curly
  | .pathCurly => .PathCurly
  | .operator => .Operator

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
  cases b <;> cases a <;> decide

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

impl comment_column: fmt::comment_column for (w o : Nat) (p : Bool) {
  width := w,
  original := o,
  split? := p,
  column := FrenCli.Fmt.commentColumn w o p,
} by
  intro w o p _
  unfold FrenCli.Fmt.commentColumn
  cases p <;> split <;> simp_all [fren_spec] <;> omega

def toBetween : List (Bool × Nat) → fmt.Between
  | [] => .Nil
  | (a, b) :: rest => .Line a (b : Int) (toBetween rest)

theorem leading_toBetween (xs : List (Bool × Nat)) :
    fmt.leading (toBetween xs) = (FrenCli.Fmt.leading xs : Int) := by
  induction xs with
  | nil => simp [toBetween, fmt.leading, FrenCli.Fmt.leading]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    cases a <;> rcases b with _ | b <;> simp_all [toBetween, fmt.leading, FrenCli.Fmt.leading] <;> omega

def toAnnotations : List (Nat × Nat) → fmt.Annotations
  | [] => .Nil
  | (d, r) :: rest => .At (d : Int) (r : Int) (toAnnotations rest)

theorem reaches_toAnnotations (xs : List (Nat × Nat)) (n : Nat) :
    fmt.«reaches_above?» (toAnnotations xs) (n : Int) = FrenCli.Fmt.reachesAbove xs n := by
  induction xs with
  | nil => simp [toAnnotations, fmt.«reaches_above?», FrenCli.Fmt.reachesAbove]
  | cons x xs ih =>
    obtain ⟨d, r⟩ := x
    simp only [toAnnotations, fmt.«reaches_above?», ih, FrenCli.Fmt.reachesAbove, List.any_cons]
    by_cases h : r > d + n
    · simp [h, show (r : Int) > d + n by omega]
    · simp [h, show ¬ ((r : Int) > d + n) by omega]

impl apart: fmt::apart for (n : Nat) (xs : List (Bool × Nat)) (ys : List (Nat × Nat)) (pf pl f l : Nat) {
  above := n,
  between := toBetween xs,
  annotations := toAnnotations ys,
  previous_first := pf,
  previous_last := pl,
  first := f,
  last := l,
  apart? := FrenCli.Fmt.apart n xs ys pf pl f l,
} by
  intro n xs ys pf pl f l _
  simp only [fren_spec, FrenCli.Fmt.apart, leading_toBetween, reaches_toAnnotations]
  by_cases h : n = FrenCli.Fmt.leading xs <;> simp_all <;> omega

def toTrailing : List (Nat × Nat) → fmt.Trailing
  | [] => .Nil
  | (s, e) :: rest => .Comment (s : Int) (e : Int) (toTrailing rest)

def toAfter : Option Nat → fmt.After
  | none => .End
  | some n => .Line (n : Int)

theorem run_end_toTrailing (ts : List (Nat × Nat)) (line : Nat) :
    fmt.run_end (line : Int) (toTrailing ts) = (FrenCli.Fmt.runEnd line ts : Int) := by
  induction ts generalizing line with
  | nil => simp [toTrailing, fmt.run_end, FrenCli.Fmt.runEnd]
  | cons t ts ih =>
    obtain ⟨s, e⟩ := t
    by_cases h : s = line
    · subst h; simp [toTrailing, fmt.run_end, FrenCli.Fmt.runEnd, ih]
    · simp [toTrailing, fmt.run_end, FrenCli.Fmt.runEnd, h, show ¬((s : Int) = line) by omega]

impl item_lines: fmt::item_lines for (f l : Nat) (ts : List (Nat × Nat)) (o : Option Nat) {
  first_token := f,
  last_token := l,
  trailing := toTrailing ts,
  next := toAfter o,
  first := (FrenCli.Fmt.itemLines f l ts o).1,
  last := (FrenCli.Fmt.itemLines f l ts o).2,
} by
  intro f l ts o _
  simp only [fren_spec, FrenCli.Fmt.itemLines]
  refine ⟨_, rfl, ?_⟩
  simp only [run_end_toTrailing]
  refine ⟨trivial, ?_⟩
  rcases o with _ | n
  · simp [toAfter]
  · by_cases h : n ≤ FrenCli.Fmt.runEnd l ts <;> simp [toAfter, h]

impl blank_lines: fmt::blank_lines for (b : Nat) (f ao bc a : Bool) {
  blank := b,
  first? := f,
  after_open? := ao,
  before_close? := bc,
  apart? := a,
  kept := FrenCli.Fmt.blankLines b f ao bc a,
} by
  intro b f ao bc a _
  cases f <;> cases ao <;> cases bc <;> cases a <;> rcases b with _ | b <;> simp [fren_spec, FrenCli.Fmt.blankLines] <;> omega

impl trailing_comma: fmt::trailing_comma for (e v a : Bool) {
  empty? := e,
  vertical? := v,
  allowed? := a,
  comma? := FrenCli.Fmt.trailingComma e v a,
}

impl one_line: fmt::one_line for (k : ListKind) (n : Nat) (b d : Bool) (w s e r : Nat) (l c i : Bool) {
  list := toFmtListKind k,
  n := n,
  broken? := b,
  wide? := d,
  width := w,
  start := s,
  line_end := e,
  rest_end := r,
  own_line? := l,
  continued? := c,
  within? := i,
  vertical? := FrenCli.Fmt.vertical k n b d w s e r l c i,
} by
  intro k n b d w s e r l c i _
  cases k <;> cases b <;> cases d <;> cases l <;> cases c <;> cases i <;> simp [fren_spec, FrenCli.Fmt.vertical, FrenCli.Fmt.widthLimit, FrenCli.Fmt.maxWidth,
    toFmtListKind] <;> omega

def toIndices : List Nat → fmt.Indices
  | [] => .Nil
  | i :: xs => .Index i (toIndices xs)

theorem has_toIndices (xs : List Nat) (i : Nat) : fmt.«has?» (toIndices xs) i = xs.contains i := by
  induction xs with
  | nil => simp [toIndices, fmt.«has?»]
  | cons j xs ih =>
    simp only [toIndices, fmt.«has?», ih, List.contains_cons]
    by_cases h : i = j
    · simp [h]
    · simp [beq_false_of_ne h, show ¬((j : Int) = i) by omega]

impl continued: fmt::continued for (o : Option Nat) (xs : List Nat) {
  tokens? := o.isSome,
  first := o.getD 0,
  items := toIndices xs,
  continued? := FrenCli.Fmt.continuedLine o xs,
} by
  intro o xs _
  rcases o with _ | i <;> simp [fren_spec, FrenCli.Fmt.continuedLine, has_toIndices]

def toGap : FrenCli.Fmt.Role → fmt.Gap
  | .afterOpen => .AfterOpen
  | .afterComma => .AfterComma
  | .beforeClose => .BeforeClose
  | .joined => .UpdatedRecord
  | .blockBrace => .BlockBrace
  | .rightSide => .RightSide

impl line_break: fmt::line_break for (r : FrenCli.Fmt.Role) (v b l c : Bool) (n : Nat) {
  gap := toGap r,
  vertical? := v,
  blank := n,
  boundary? := b,
  after_line_comment? := l,
  comment_follows? := c,
  break? := FrenCli.Fmt.lineBreak r v b l c n,
} by
  intro r v b l c n _
  cases r <;> cases v <;> cases b <;> cases l <;> cases c <;> simp [fren_spec, FrenCli.Fmt.lineBreak, FrenCli.Fmt.Role.betweenElements, FrenCli.Fmt.Role.vertical, toGap]

def toForm : FrenCli.RightForm → fmt.Form
  | .arms => .Arms
  | .conditional => .Conditional
  | .bracketed => .Bracketed
  | .other => .Other

impl right_side: fmt::right_side for (f : FrenCli.RightForm) (h w l a b i : Bool) (e n x y : Nat) {
  form := toForm f,
  chained? := h,
  written? := w,
  ladder? := l,
  after_close? := a,
  broken? := b,
  inner? := i,
  line_end := e,
  next_end := n,
  first_end := x,
  head_end := y,
  next_line? := FrenCli.Fmt.rightSide f h w l a b i e n x y,
} by
  intro f h w l a b i e n x y _
  cases f <;> cases h <;> cases w <;> cases l <;> cases a <;> cases b <;> cases i <;>
    simp [fren_spec, FrenCli.Fmt.rightSide, FrenCli.Fmt.overflows, FrenCli.Fmt.maxWidth, toForm] <;> omega

impl break_before: fmt::break_before for (n : Nat) (s : Bool) {
  comments := n,
  starts_line? := s,
  before := FrenCli.Fmt.breakBefore n s,
} by
  intro n s _
  cases s <;> simp [fren_spec, FrenCli.Fmt.breakBefore]

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

theorem count_toElementList (es : List (Nat × Bool × Bool)) : fmt.count (toElementList es) = es.length := by
  induction es with
  | nil => simp [toElementList, fmt.count]
  | cons e es ih => simp [toElementList, fmt.count, ih]; omega

theorem any_broken_toElementList (es : List (Nat × Bool × Bool)) :
    fmt.«any_broken?» (toElementList es) = es.any (·.2.1) := by
  induction es with
  | nil => simp [toElementList, fmt.«any_broken?»]
  | cons e es ih => simp [toElementList, fmt.«any_broken?», ih]

theorem any_wide_toElementList (es : List (Nat × Bool × Bool)) :
    fmt.«any_wide?» (toElementList es) = es.any (·.2.2) := by
  induction es with
  | nil => simp [toElementList, fmt.«any_wide?»]
  | cons e es ih => simp [toElementList, fmt.«any_wide?», ih]

theorem joined_toElementList (es : List (Nat × Bool × Bool)) :
    fmt.joined (toElementList es) = FrenCli.Fmt.joinedWidth (es.map (·.1)) := by
  induction es with
  | nil => simp [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]
  | cons e es ih =>
    cases es with
    | nil => simp [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]
    | cons f fs => simp_all [toElementList, fmt.joined, FrenCli.Fmt.joinedWidth]

impl list_layout: fmt::list_layout for (k : ListKind) (es : List (Nat × Bool × Bool)) (s a r : Nat) (l c i : Bool) {
  list := toFmtListKind k,
  elements := toElementList es,
  start := s,
  after := a,
  rest := r,
  own_line? := l,
  continued? := c,
  within? := i,
  vertical? := FrenCli.Fmt.listLayout k es s a r l c i,
} by
  intro k es s a r l c i _
  simp only [fren_spec, count_toElementList, any_broken_toElementList, any_wide_toElementList,
    joined_toElementList, FrenCli.Fmt.listLayout, FrenCli.Fmt.listWide]
  refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
  generalize es.any (·.2.1) = b
  generalize es.any (·.2.2) = d
  generalize FrenCli.Fmt.joinedWidth (es.map (·.1)) = w
  generalize es.length = n
  cases k <;> cases b <;> cases d <;> cases l <;> cases c <;> cases i <;> simp [FrenCli.Fmt.vertical, FrenCli.Fmt.widthLimit, FrenCli.Fmt.maxWidth,
    toFmtListKind] <;> omega

impl wide_list: fmt::wide_list for (k : ListKind) (es : List (Nat × Bool × Bool)) {
  list := toFmtListKind k,
  elements := toElementList es,
  wide? := FrenCli.Fmt.listWide k es,
} by
  intro k es _
  simp only [fren_spec, any_wide_toElementList, joined_toElementList, FrenCli.Fmt.listWide]
  generalize es.any (·.2.2) = d
  generalize FrenCli.Fmt.joinedWidth (es.map (·.1)) = w
  cases k <;> cases d <;> simp [toFmtListKind] <;> omega

impl wide_within: fmt::wide_within for (k : ListKind) (es : List (Nat × Bool × Bool)) (s a r : Nat) (l c i : Bool) {
  list := toFmtListKind k,
  elements := toElementList es,
  start := s,
  after := a,
  rest := r,
  own_line? := l,
  continued? := c,
  within? := i,
  inner? := FrenCli.Fmt.wideWithin k es s a r l c i,
} by
  intro k es s a r l c i _
  simp only [fren_spec, count_toElementList, any_broken_toElementList, any_wide_toElementList,
    joined_toElementList, FrenCli.Fmt.wideWithin, FrenCli.Fmt.listWide]
  refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
  generalize es.any (·.2.1) = b
  generalize es.any (·.2.2) = d
  generalize FrenCli.Fmt.joinedWidth (es.map (·.1)) = w
  generalize es.length = n
  cases k <;> cases b <;> cases d <;> cases l <;> cases c <;> cases i <;> simp [FrenCli.Fmt.vertical, FrenCli.Fmt.widthLimit,
    FrenCli.Fmt.maxWidth, toFmtListKind] <;> omega

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

/-- The lines that comments are on. -/
def toLines : List Nat → fmt.Lines
  | [] => .Nil
  | c :: cs => .Line c (toLines cs)

theorem any_within_toLines (cs : List Nat) (f l : Nat) :
    fmt.«any_within?» (toLines cs) f l = cs.any (fun c => decide (f ≤ c ∧ c ≤ l)) := by
  induction cs with
  | nil => simp [toLines, fmt.«any_within?»]
  | cons c cs ih =>
    simp only [toLines, fmt.«any_within?», ih, List.any_cons, Int.ofNat_le]
    cases cs.any (fun c => decide (f ≤ c ∧ c ≤ l)) <;> simp

impl in_block: fmt::in_block for (f l : Nat) (b a : Option Nat) (cs : List Nat) (n : Bool) {
  first_line := f,
  last_line := l,
  before := toNeighbour b,
  after := toNeighbour a,
  comments := toLines cs,
  nested? := n,
  alone? := FrenCli.Fmt.useAlone f l b a cs,
  sorted? := FrenCli.Fmt.inBlock (FrenCli.Fmt.useAlone f l b a cs) n,
} by
  intro f l b a cs n _
  simp only [fren_spec, any_within_toLines, FrenCli.Fmt.useAlone, FrenCli.Fmt.inBlock]
  generalize cs.any (fun c => decide (f ≤ c ∧ c ≤ l)) = c
  cases b <;> cases a <;> cases c <;> cases n <;> simp [toNeighbour]

def toPiece : PieceKind → fmt.Piece
  | .token => .Token
  | .separator => .Separator
  | .lineComment => .LineComment
  | .blockComment => .BlockComment
  | .lineBreak => .LineBreak

impl comment_piece: fmt::comment_piece for (l s : Bool) {
  line_comment? := l,
  starts_line? := s,
  piece := toPiece (FrenCli.Fmt.commentPiece l s),
} by
  intro l s _
  cases l <;> cases s <;> simp [fren_spec, FrenCli.Fmt.commentPiece, toPiece]

def toPieces : List PieceKind → fmt.Pieces
  | [] => .Nil
  | p :: ps => .Next (toPiece p) (toPieces ps)

theorem put_toPieces (p : PieceKind) (ps : List PieceKind) :
    fmt.put (toPiece p) (toPieces ps) = toPieces (FrenCli.Fmt.putPiece id p ps) := by
  induction ps with
  | nil => rfl
  | cons c ps ih =>
    cases c <;> cases p <;> simp_all [toPieces, toPiece, fmt.put, fmt.«after_line?», FrenCli.Fmt.putPiece,
      FrenCli.Fmt.afterLine]

theorem place_toPieces (ps : List PieceKind) :
    fmt.place (toPieces ps) = toPieces (FrenCli.Fmt.placeSeparators id ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [toPieces, fmt.place, FrenCli.Fmt.placeSeparators, ih, put_toPieces]

/-- The formatter places the pieces themselves, by their kinds: the kinds
of what it places are those that `fmt::separators` places. -/
theorem placeSeparators_map {α} (kind : α → PieceKind) (ps : List α) :
    (FrenCli.Fmt.placeSeparators kind ps).map kind = FrenCli.Fmt.placeSeparators id (ps.map kind) := by
  have put_map (p : α) (qs : List α) :
      (FrenCli.Fmt.putPiece kind p qs).map kind = FrenCli.Fmt.putPiece id (kind p) (qs.map kind) := by
    induction qs with
    | nil => rfl
    | cons c qs ih =>
      simp only [FrenCli.Fmt.putPiece, List.map_cons, id]
      split <;> simp_all
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [FrenCli.Fmt.placeSeparators, put_map, ih]

impl separators: fmt::separators for (ps : List PieceKind) {
  input := toPieces ps,
  output := toPieces (FrenCli.Fmt.placeSeparators id ps),
} by
  intro ps _
  simp [fren_spec, place_toPieces]

theorem unbroken_toPieces (ps : List PieceKind) :
    fmt.unbroken (toPieces ps) = toPieces (ps.filter fun p => !FrenCli.Fmt.isLineBreak p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp_all [toPieces, toPiece, fmt.unbroken, FrenCli.Fmt.isLineBreak]

/-- The formatting job orders the pieces by their kinds: the kinds of what
it orders are those that `fmt::ordering` orders. -/
theorem keptOrder_map {α} (kind : α → PieceKind) (ps : List α) :
    (FrenCli.Fmt.keptOrder kind ps).map kind = FrenCli.Fmt.keptOrder id (ps.map kind) := by
  rw [FrenCli.Fmt.keptOrder, FrenCli.Fmt.keptOrder, ← placeSeparators_map]
  induction FrenCli.Fmt.placeSeparators kind ps with
  | nil => rfl
  | cons p ps ih => cases h : kind p <;> simp_all [FrenCli.Fmt.isLineBreak]

impl ordering: fmt::ordering for (ps : List PieceKind) {
  input := toPieces ps,
  output := toPieces (FrenCli.Fmt.keptOrder id ps),
} by
  intro ps _
  simp only [fren_spec, FrenCli.Fmt.keptOrder, fmt.order, place_toPieces, unbroken_toPieces, id, and_true]

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
