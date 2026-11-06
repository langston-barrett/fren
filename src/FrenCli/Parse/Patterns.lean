-- keep-sorted start
import FrenCli.Parse.Basic
-- keep-sorted end

/-! Parsing patterns, including ranges and alternatives. -/

namespace FrenCli

namespace Parser

/-- Whether `t` can start a bound of a range. -/
def boundStart (t : Token) : Bool := t.tok matches .num .. | .ident _ | .kw "-"

/-- The bound of a range: `["-"] INT`, or a path. -/
def bound : P Bound := do
  let t ← peek
  match t.tok with
  | .kw "-" =>
    markUnary
    discard bump
    let n ← peek
    let .num _ v := n.tok | fail n "an integer"
    discard bump
    return .num (t.span.to n.span) (-(v : Int))
  | .num _ v => discard bump; return .num t.span v
  | .ident _ =>
    let (segs, _) ← path false
    return .path (segs[0]!.span.to segs.back!.span) segs
  | _ => fail t "a bound of a range"

/-- Spaces around the `..=` or `..` of a range (`F0128`). -/
def rangeSpaceErr (op : Token) : P α :=
  err op.span "F0128" s!"spaces around `{if isKw op "..=" then "..=" else ".."}` in a range pattern"
    (some "spaced") #["note: a range is written without spaces around its `..=` or `..`, as in `0..=9`"]

/-- The rest of a range after its lower bound `lo?`, at its `..=` or
`..`: its upper bound, if any. `..=` needs one, and `..` with no lower
bound is not a range (`F0129`). -/
def rangeRest (start : Span) (lo? : Option Bound) : P Pattern := do
  let at_ := (← get).pos
  if lo?.isSome then modify fun s => { s with layout.rangeLower := s.layout.rangeLower.push at_ }
  let op ← bump
  let inclusive := isKw op "..="
  let next ← peek
  -- An upper bound touches the operator, as Lean's parser reads it: what
  -- follows a space is not part of the range. After `..=`, a spaced bound
  -- is reported as such.
  let upper := boundStart next && (← touching)
  if inclusive && !upper && boundStart next && !next.nlBefore then rangeSpaceErr op
  if upper then modify fun s => { s with layout.rangeUpper := s.layout.rangeUpper.push at_ }
  let hi? ← if upper then some <$> bound else pure none
  if inclusive && hi?.isNone then
    err op.span "F0129" "an inclusive range needs an upper bound" (some "no upper bound")
      #["note: the ranges are `a..=b`, `a..b`, `a..` and `..=b`"]
  if !inclusive && lo?.isNone then
    err op.span "F0129" "a range with `..` needs a lower bound" (some "no lower bound")
      #["note: the ranges are `a..=b`, `a..b`, `a..` and `..=b`", "help: for the integers below `b`, write `..=` and the integer before `b`"]
  return .range (← spanFrom start) lo? hi? inclusive

/-- After the lower bound `lo` of a pattern, a range if `..=` or `..`
follows, touching it. -/
def maybeRange (lo : Bound) (otherwise : Pattern) : P Pattern := do
  let t ← peek
  unless isKw t "..=" || isKw t ".." do return otherwise
  unless ← touching do rangeSpaceErr t
  rangeRest lo.span (some lo)

mutual
/-- An alternative of an or-pattern, or a pattern of a payload: `_`, a
binder or variant, a literal, or a range. -/
partial def primaryPattern : P Pattern := do
  let t ← peek
  match t.tok with
  | .ident "_" => discard bump; return .wild t.span
  | .str v => discard bump; return .str t.span v
  | .num .. | .kw "-" =>
    let b ← bound
    let .num sp v := b | fail t "a pattern"
    maybeRange b (.num sp v)
  | .kw "..=" => rangeRest t.span none
  | .kw ".." => rangeRest t.span none
  | .ident _ =>
    let (segs, _) ← path false
    let start := segs[0]!.span
    let pathSpan := start.to segs.back!.span
    let name := "::".intercalate (segs.map (·.name)).toList
    noSpaceBeforeParen name s!"the binders of `{name}`"
    let next ← peek
    if isKw next "(" && (← touching) then
      markCall
      discard bump
      let mut args := #[← orPattern]
      while (← eatKw ",").isSome do args := args.push (← orPattern)
      discard (expectKw ")")
      return .variant (← spanFrom start) segs (some args)
    maybeRange (.path pathSpan segs) (.variant pathSpan segs none)
  | _ => fail t "a pattern"

/-- `A | B`, an or-pattern, or one pattern. -/
partial def orPattern : P Pattern := do
  let first ← primaryPattern
  let mut alts := #[first]
  while isKw (← peek) "|" do
    discard bump
    alts := alts.push (← primaryPattern)
  if alts.size == 1 then return first
  return .or (← spanFrom first.span) alts
end

/-- A pattern, of a `match` arm or of `is`. In an arm (`arm`), each `|`
starts its alternative, so that they line up one per line; after `is`, a
line that starts with `|` continues the expression. -/
def pattern (arm := true) : P Pattern := do
  if arm then markStart
  let lead ← eatKw "|"
  let first ← primaryPattern
  let mut alts := #[first]
  while isKw (← peek) "|" do
    if arm then markStart
    discard bump
    alts := alts.push (← primaryPattern)
  if alts.size == 1 && lead.isNone then return first
  return .or (← spanFrom ((lead.map (·.span)).getD first.span)) alts

end Parser

end FrenCli
