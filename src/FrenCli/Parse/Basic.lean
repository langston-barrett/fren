-- keep-sorted start
import FrenCli.Parse.State
import FrenCore.Names
-- keep-sorted end

/-! Token, layout, diagnostic and bracket helpers for the parser. -/

namespace FrenCli

namespace Parser

def peek : P Token := do let s ← get; return s.toks[s.pos]!
def bump : P Token := do
  let t ← peek
  if t.tok != .eof then modify fun s => { s with pos := s.pos + 1 }
  return t
/-- The span of the last token consumed. -/
def lastSpan : P Span := do let s ← get; return s.toks[s.pos - 1]!.span
def range (s : Span) : Fren.Core.Range := { start := s.start, stop := s.stop }

/-- Records that the next token starts an item, a member or an element. -/
def markStart : P Unit := modify fun s => { s with layout.starts := s.layout.starts.push s.pos }
/-- Records that the next token opens a list. -/
def markList : P Unit := modify fun s => { s with layout.lists := s.layout.lists.push s.pos }
/-- Records that the next token is the `(` of a call. -/
def markCall : P Unit := modify fun s => { s with layout.calls := s.layout.calls.push s.pos }
/-- Records that the next token opens a list or block of kind `k`, whose
line breaks the formatter decides. -/
def openList (k : ListKind) : P Unit :=
  modify fun s => { s with openLists := s.openLists.push { kind := k, opening := s.pos, lead := s.pos, items := s.items } }
/-- Records that the innermost open list or block is a record update's
fields, which start after the next token, its `with`. -/
def updateList : P Unit :=
  modify fun s => { s with openLists := s.openLists.modify (s.openLists.size - 1) fun b => { b with kind := .fields, lead := s.pos } }
/-- Eats a comma after an element of the innermost open list or block,
recording it. -/
def listComma : P Bool := do
  let s ← get
  unless s.toks[s.pos]!.tok == .kw "," do return false
  modify fun s => { s with openLists := s.openLists.modify (s.openLists.size - 1) fun b => { b with commas := b.commas.push s.pos } }
  modify fun s => { s with pos := s.pos + 1 }
  return true
/-- Records that the last token consumed ends a member of the innermost
open block, which another member follows (`Bracketed.commas`). -/
def memberEnd : P Unit :=
  modify fun s => { s with openLists := s.openLists.modify (s.openLists.size - 1) fun b => { b with commas := b.commas.push (s.pos - 1) } }
/-- Runs `x`, which parses the right side of the `:=` or `=>` just
consumed, recording it (`Layout.rightSides`). -/
def rightSide (x : P Expr) : P Expr := do
  let first := (← get).pos
  let e ← x
  let s ← get
  let last := s.pos - 1
  if first > 0 && last ≥ first then
    let whole := e.span.start == s.toks[first]!.span.start && e.span.stop == s.toks[last]!.span.stop
    -- Its form, from its outermost expression where that is all of it, and
    -- otherwise a parenthesized expression, the parser keeping no node for
    -- the parentheses, where it is in the brackets of its first and last tokens.
    let form : RightForm :=
      if whole then match e with
        | .match _ _ _ _ | .matches _ _ _ _ | .table _ _ => .arms
        | .ite _ _ _ _ => .conditional
        | .app _ _ _ | .method _ _ _ _ | .record _ _ _ | .update _ _ _ | .set _ _ | .seq _ _ | .block _ _ _
        | .pair _ _ _ => .bracketed
        | _ => .other
      else if s.toks[first]!.tok == .kw "(" && s.toks[last]!.tok == .kw ")" && s.toks[first]!.span.start < e.span.start
          && e.span.stop < s.toks[last]!.span.stop then .bracketed
      else .other
    modify fun s => { s with layout.rightSides := s.layout.rightSides.push (first - 1, first, last, form) }
  return e
/-- Records that the next token closes the innermost open list or block. -/
def closeList : P Unit := modify fun s =>
  match s.openLists.back? with
  | some b => { s with openLists := s.openLists.pop, layout.bracketed := s.layout.bracketed.push { b with closing := s.pos } }
  | none => s

def err (span : Span) (code headline : String) (label? : Option String := none)
    (notes : Array String := #[]) (fixes : Array Fren.Core.Fix := #[]) : P α :=
  throw { span, msg := { code? := some code, headline, label?, notes, fixes } }

/-- `t` where `expected` was. Operators of other languages say what to
write instead. -/
def fail (t : Token) (expected : String) (keywords : Array String := #[]) : P α := do
  match t.tok with
  | .kw op@"==" | .kw op@"&&" | .kw op@"||" | .kw op@"|" | .kw op@"=>" => throw { span := t.span, msg := Fren.Core.foreignOpMsg op }
  | .kw "<-" => throw { span := t.span, msg := Fren.Core.leftArrowMsg }
  | _ => pure ()
  -- At the end of the file, point just after the last token, as rustc does.
  let s ← get
  let span := if t.tok == .eof && s.pos > 0 then
      let prev := s.toks[s.pos - 1]!.span
      { start := prev.stop, stop := prev.stop }
    else t.span
  let fixes := match t.tok with
    | .ident w => (Fren.Core.similarStr w keywords).toArray.map fun k => { msg := s!"a keyword with a similar name exists: `{k}`", replacement := k }
    | _ => #[]
  let notes := if t.tok == .kw "where" then
      #["note: a `where` clause follows the whole expression of a constraint, a cover goal, a definition, a function's body or a constant's value, not a part of one"]
    else #[]
  err span "F0104" s!"expected {expected}, found {t.tok.describe}" (some s!"expected {expected}") notes fixes

def isKw (t : Token) (s : String) : Bool := match t.tok with | .kw k => k == s | _ => false
def isWord (t : Token) (s : String) : Bool := match t.tok with | .ident w => w == s | _ => false

def eatKw (s : String) : P (Option Token) := do
  let t ← peek
  if isKw t s then return some (← bump) else return none

def expectKw (s : String) : P Token := do
  match ← eatKw s with
  | some t => return t
  | none => fail (← peek) s!"`{s}`"

def ident (afterPath := false) : P Ident := do
  let t ← peek
  match t.tok with
  | .ident s =>
    discard bump
    if s.contains '.' then
      let n := (s.splitOn ".").foldl Lean.Name.mkStr .anonymous
      throw { span := t.span, msg := Fren.Core.dottedNameMsg n #[] (inExpr := false) (afterPath := afterPath) }
    return { name := s, span := t.span }
  | _ => fail t "a name"

/-- `a::b::c`; with `allowGlob`, a trailing `::*` is returned as `true`. -/
def path (allowGlob : Bool) : P (Array Ident × Bool) := do
  let mut segs := #[← ident]
  repeat
    if (← eatKw "::").isSome then segs := segs.push (← ident (afterPath := true))
    else if allowGlob then
      if (← eatKw "::*").isSome then return (segs, true)
      break
    else break
  return (segs, false)

/-- The span from `start` to the last token consumed, which includes any
parentheses around the last operand. -/
def spanFrom (start : Span) : P Span := return start.to (← lastSpan)

/-- `l op r`, where `start` is the span of its first token, which may be a
`(` around `l`. -/
def bin (start : Span) (op : String) (l r : Expr) : P Expr := do
  let sp ← spanFrom start
  modify fun st => { st with layout.exprs := st.layout.exprs ++ #[sp, l.span, r.span], layout.pairs := st.layout.pairs.push (sp, r.span) }
  return .bin sp op l r

/-- Runs `x` within brackets: a record literal may appear, even in a
`match`'s scrutinee, and `in` is a membership, even in a definition of a
`let`. -/
def withRecords (x : P α) : P α := do
  let s0 ← get
  modify fun s => { s with noRecord := false, noIn := false }
  let r ← x
  modify fun s => { s with noRecord := s0.noRecord, noIn := s0.noIn }
  return r

/-- Runs `x` where `in` is a membership, even in a definition of a `let`:
in a delimited part of an `if` or a `match`. -/
def withIn (x : P α) : P α := do
  let saved := (← get).noIn
  modify fun s => { s with noIn := false }
  let r ← x
  modify fun s => { s with noIn := saved }
  return r

/-- If the next token is a `(` after a space, reports it (`F0144`): the
`(` that opens what a name takes follows it directly, as in Lean
(`Reqs/Lang/Lexical#punctuators`). `name` is the name before it, and
`what` what the `(` would open. -/
def noSpaceBeforeParen (name what : String) : P Unit := do
  let s ← get
  let some t := s.toks[s.pos]? | return
  unless isKw t "(" do return
  let some prev := s.toks[s.pos - 1]? | return
  if s.pos == 0 || prev.span.stop == t.span.start then return
  err t.span "F0144" s!"a space before the `(` of {what}" (some "after a space")
    #["note: the `(` that opens what a name takes follows the name directly, as in Lean",
      s!"help: remove the space: `{name}(`"]

/-- The bracket after the last token, and whether it follows it directly
(`Fren.Core.afterName`). -/
def bracketAfter : P (Fren.Core.Bracket × Bool) := do
  let s ← get
  let some t := s.toks[s.pos]? | return (.other, false)
  let b := match t.tok with | .kw p => Fren.Core.Bracket.of p | _ => .other
  let adjacent := s.pos > 0 && (s.toks[s.pos - 1]?).any (·.span.stop == t.span.start)
  return (b, adjacent)

/-- Reports a `<` after a space where it would open what the name `name`
takes, `what` (`F0144`), as `noSpaceBeforeParen` does a `(`. -/
def spacedAngle (name what : String) : P α := do
  err (← peek).span "F0144" s!"a space before the `<` of {what}" (some "after a space")
    #["note: the `<` that opens a type's arguments or a declaration's type parameters follows the name directly",
      s!"help: remove the space: `{name}<`"]

/-- The `>` that closes type arguments or type parameters, recorded for
the formatter as a call's `)` is. -/
def closeAngle : P Token := do
  markCall
  expectKw ">"

/-- `.x` reading a field of `e`, an atom that ends in `)` or `}`; the `.`
touches both. After `.`, `x.y` is one (dotted) identifier. If `(` follows
the last of them, without a space, it is a method call, whose arguments
`args` parses. -/
def fieldReads (args : P (Array Expr)) (index : P Expr) (e : Expr) (start? : Option Span := none) : P Expr := do
  let mut e := e
  -- Where the expression starts: before the parentheses of `(e).f`.
  let mut first := start?.getD e.span
  repeat
    let s ← get
    -- `q[i]`: indexing, with no space before `[`.
    if let (some b, some prev) := (s.toks[s.pos]?, s.toks[s.pos - 1]?) then
      if isKw b "[" && prev.span.stop == b.span.start then
        let i ← index
        e := .index (first.to (← lastSpan)) e i
        first := e.span
        continue
    let some dot := s.toks[s.pos]? | break
    let some next := s.toks[s.pos + 1]? | break
    let some prev := s.toks[s.pos - 1]? | break
    unless isKw dot "." && prev.span.stop == dot.span.start && dot.span.stop == next.span.start do break
    -- `x.0`, a field named by decimal digits: of a newtype, which the
    -- elaborator checks. It is read as Lean reads a field index, so a
    -- number of another base, or with `_`, does not parse.
    if let .num digits _ := next.tok then
      unless digits.all Char.isDigit do fail next "a field"
      discard bump
      discard bump
      e := .field (first.to next.span) e { name := digits, span := next.span }
      first := e.span
      continue
    let .ident name := next.tok | break
    discard bump
    discard bump
    let mut start := next.span.start
    let parts := name.splitOn "."
    for f in parts.dropLast do
      let span : Span := { start, stop := start + f.length }
      e := .field (first.to span) e { name := f, span }
      first := e.span
      start := span.stop + 1
    let last : Ident := { name := parts.getLast!, span := { start, stop := next.span.stop } }
    noSpaceBeforeParen last.name s!"the arguments of `{last.name}`"
    let s ← get
    if (s.toks[s.pos]?).any fun t => isKw t "(" && t.span.start == next.span.stop then
      let as ← args
      e := .method (first.to (← lastSpan)) e last as
      first := e.span
    else
      e := .field (first.to last.span) e last
      first := e.span
  return e

/-- Records that the next token is a unary `-`. -/
def markUnary : P Unit := modify fun s => { s with layout.unary := s.layout.unary.push s.pos }

/-- Whether the next token touches the last one consumed. -/
def touching : P Bool := do
  let s ← get
  return match s.toks[s.pos]?, s.toks[s.pos - 1]? with
    | some t, some prev => prev.span.stop == t.span.start
    | _, _ => false

end Parser

end FrenCli
