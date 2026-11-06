-- keep-sorted start
import FrenCore.Lint.Tree
import FrenCore.Nfc
-- keep-sorted end

/-!
# Arithmetic, parentheses and normalized literals

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Arithmetic and parentheses -/

/-- Whether `double_parens` fires on `depth` pairs of parentheses, each
directly around the next (`lint::double_parens`). -/
def doubleParens (depth : Nat) : Bool := depth ≥ 2

/-- `((e))`, where `inner` is the text of the innermost pair, `(e)`. -/
def doubleParensMsg (inner : String) : Msg :=
  { code? := some Lint.doubleParens.code, headline := "parentheses directly around parentheses"
    label? := some "double parentheses"
    fixes := #[{ msg := "remove the outer parentheses", replacement := inner }] }

/-- Whether `double_neg` fires on a negation, whose operand, through
parentheses, is a negation if `negatedOperand` (`lint::double_neg`). -/
def doubleNeg (negatedOperand : Bool) : Bool := negatedOperand

def doubleNegMsg (replacement : String) : Msg :=
  { code? := some Lint.doubleNeg.code, headline := "negating twice is the operand itself", label? := some "a double negation"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- An operand of a comparison, as `int_plus_one` sees it
(`lint::Offset`): `e + 1` or `1 + e`, `e - 1`, or neither. -/
inductive Offset where
  | zero
  | plusOne
  | minusOne
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `int_plus_one` fires on `l op r`, the strict comparison of its
fix, and whether the fix drops the offset of `l`, rather than of `r`
(`lint::int_plus_one`). -/
def intPlusOne (op : Comparison) (l r : Offset) : Bool × Comparison × Bool :=
  match op, l, r with
  | .ge, _, .plusOne => (true, .gt, false)
  | .ge, l, _ => (l matches .minusOne, .gt, true)
  | .le, .plusOne, _ => (true, .lt, true)
  | .le, _, r => (r matches .minusOne, .lt, false)
  | _, _, _ => (false, op, false)

/-- Whether `int_plus_one` fires on the comparison `i` of a chained
comparison of `n`, where its fix of that comparison alone drops the
offset of its left operand if `dropLeft`: only if that operand is at an
end of the chain, in no other comparison (`lint::int_plus_one_in_chain`). -/
def intPlusOneInChain (dropLeft : Bool) (i n : Nat) : Bool := if dropLeft then i == 0 else i + 1 == n

def intPlusOneMsg (replacement : String) : Msg :=
  { code? := some Lint.intPlusOne.code, headline := "over integers, this is a strict comparison"
    label? := some "compares with an operand off by one"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- Whether `neg_multiply` fires on `a * b`, where each says whether that
operand is `-1`, and whether the fix negates `a`, rather than `b`
(`lint::neg_multiply`). -/
def negMultiply (aMinusOne bMinusOne : Bool) : Bool × Bool := (aMinusOne || bMinusOne, bMinusOne)

def negMultiplyMsg (replacement : String) : Msg :=
  { code? := some Lint.negMultiply.code, headline := "multiplying by `-1` is negation", label? := some "a product with `-1`"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- Whether `unicode_not_nfc` fires on a string literal, and whether its
message suggests the literal in NFC (`lint::unicode_not_nfc`): if its value
is not in NFC, and this version of Unicode assigns each of its code points,
and a suggestion if it has no escape sequence. -/
def unicodeNotNfc (nfc assigned escapes : Bool) : Bool × Bool :=
  let fires := assigned && !nfc
  (fires, fires && !escapes)

/-- What `unicode_not_nfc` says of the string literal written `t`: `none`
if it does not fire, and else its value, the value in NFC, and the literal
it suggests, if any: `t` with its value in NFC. A raw literal, or one
without a `\`, has no escape sequence, so its value is the text between its
delimiters, and the suggestion keeps them. -/
def unicodeNotNfc? (t : String) : Option (String × String × Option String) := do
  let value ← Lean.Syntax.decodeStrLit t
  let raw := t.startsWith "r"
  let normal? := Nfc.nfc? value
  let (fires, suggested) := unicodeNotNfc (normal? == some value) normal?.isSome (!raw && t.contains '\\')
  guard fires
  let some normal := normal? | none
  -- `r#"`: the `r`, its `#`s and the `"`.
  let hashes := ((t.toList.drop 1).takeWhile (· == '#')).length
  let (pre, post) := if raw then ((t.take (hashes + 2)).toString, "\"" ++ String.ofList (List.replicate hashes '#'))
    else ("\"", "\"")
  return (value, normal, if suggested then some (pre ++ normal ++ post) else none)

/-- The code points `cs`, as `U+0065 U+0301`. -/
def codePoints (cs : List Char) : String :=
  " ".intercalate (cs.map fun c =>
    let h := (String.ofList (Nat.toDigits 16 c.toNat)).toUpper
    "U+" ++ String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h)

/-- A string literal whose value, `value`, is not in NFC, where it is
`normal`, and the literal in NFC that it suggests, `suggested?`. The note
names the code points that differ, between the longest prefix and suffix
that the two share. There is no fix, which would change the value. -/
def unicodeNotNfcMsg (value normal : String) (suggested? : Option String) : Msg :=
  let (a, b) := (value.toList, normal.toList)
  let pre := ((a.zip b).takeWhile fun (x, y) => x == y).length
  let (a, b) := (a.drop pre, b.drop pre)
  let post := ((a.reverse.zip b.reverse).takeWhile fun (x, y) => x == y).length
  let (a, b) := (a.take (a.length - post), b.take (b.length - post))
  { code? := some Lint.unicodeNotNfc.code, headline := "this string literal is not in Unicode NFC"
    label? := some "not in NFC"
    notes := #[s!"note: {codePoints a} is {codePoints b} in NFC",
      "note: strings compare by code point, so it never equals text in NFC, which most text is in"]
      ++ #[match suggested? with
        | some t => s!"help: write it in NFC, `{t}`"
        | none => "help: write it so that its value is in NFC",
        "note: `fren fix` does not, since that changes the literal's value"] }

/-- Whether `zero_prefixed_literal` fires on the integer literal `s`: a
decimal one, a `0` and then another digit (`lint::zero_prefixed_literal`). -/
def zeroPrefixed (s : String) : Bool :=
  match s.toList with
  | '0' :: c :: _ => isDecimalDigit c
  | _ => false

/-- The message of `zero_prefixed_literal` on `s`. It names the octal
literal only where its digits are octal and it would mean something else,
from `8` on. -/
def zeroPrefixedMsg (s : String) : Msg :=
  let fixed := dropLeadingZeros s
  let value := (integerValue? s).getD 0
  let octal := s.toList.all (fun c => isOctalDigit c || c == '_') && value ≥ 8
  { code? := some Lint.zeroPrefixedLiteral.code
    headline := s!"`{s}` is {value}" ++ (if octal then s!"; for octal write `0o{fixed}`" else "")
    label? := some "leading zero"
    notes := #["note: a leading `0` does not make a literal octal"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `zero_prefixed_literal` on an integer literal written at `r` in `src`,
in an expression or a pattern, after a `-` if it is negated: the literal's
range, and the message. A literal needs no parentheses. -/
def zeroPrefixedReport? (src : Array Char) (r : Range) : Option (Range × Msg) := do
  let neg := if src[r.start]? == some '-' then 1 else 0
  let start := ((List.range' (r.start + neg) (r.stop - min r.stop (r.start + neg))).find?
    fun i => !(src[i]?.getD ' ').isWhitespace).getD r.stop
  let t := textOf src { start, stop := r.stop }
  guard (integerLiteral t && zeroPrefixed t)
  return ({ start, stop := r.stop }, zeroPrefixedMsg t)

/-- A report of `double_neg`, `int_plus_one`, `neg_multiply` or
`unicode_not_nfc`: the lint, where, and the fix, if any, which replaces the
range. -/
structure ShapeReport (α : Type) where
  lint : Lint
  ref : α
  range : Range
  msg : Msg
  deriving Inhabited

/-- The reports of `double_neg`, `int_plus_one`, `neg_multiply` and
`unicode_not_nfc` in `n`, which is in `slot` within `parent`, and in its
operands, in order. An
atom's operands, such as an application's arguments, are where any
expression can be written. -/
partial def shapeReports [Inhabited α] (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Array (ShapeReport α) :=
  let .mk kind range ref kids := n
  let text (k : BNode α) : BText := match k with | .mk kk kr .. => { text := textOf src kr, prec := kk.prec }
  let isOne (k : BNode α) : Bool := match k with | .mk .atom kr _ _ => textOf src kr == "1" | _ => false
  let isMinusOne (k : BNode α) : Bool := match k with | .mk .neg _ _ #[o] => isOne o | _ => false
  -- The text of the replacement, parenthesized where the expression is.
  let place (t : BText) : String := if enclosed src parent range then t.text else t.inSlot slot (followedAt src range)
  let report (l : Lint) (msg : String → Msg) (t : BText) : Array (ShapeReport α) :=
    let replacement := place t
    #[{ lint := l, ref, range, msg := msg replacement }]
  -- An operand as `int_plus_one` sees it, and its text without the offset.
  let offset (k : BNode α) : Offset × BText := match k with
    | .mk (.bin "+") _ _ #[x, y] => if isOne y then (.plusOne, text x) else if isOne x then (.plusOne, text y) else (.zero, text k)
    | .mk (.bin "-") _ _ #[x, y] => if isOne y then (.minusOne, text x) else (.zero, text k)
    | _ => (.zero, text k)
  let own := match kind, kids with
    | .neg, #[.mk .neg _ _ #[b]] =>
      if doubleNeg true then report .doubleNeg doubleNegMsg (text b) else #[]
    | .bin "*", #[a, b] =>
      match negMultiply (isMinusOne a) (isMinusOne b) with
      | (true, negA) =>
        let t := (text (if negA then a else b)).inSlot (some ⟨BKind.neg.prec, .right, true⟩)
        report .negMultiply negMultiplyMsg { text := negText t, prec := BKind.neg.prec }
      | _ => #[]
    | .bin op, #[a, b] =>
      match Comparison.ofOp? op with
      | some c =>
        let ((oa, ta), (ob, tb)) := (offset a, offset b)
        match intPlusOne c oa ob with
        | (true, strict, dropLeft) =>
          let (l, r) := if dropLeft then (ta, text b) else (text a, tb)
          let slot (right : Bool) : Option Slot := some ⟨kind.prec, kind.assoc, right⟩
          report .intPlusOne intPlusOneMsg { text := s!"{l.inSlot (slot false)} {strict.op} {r.inSlot (slot true)}", prec := kind.prec }
        | _ => #[]
      | none => #[]
    -- A literal is an atom, which needs no parentheses.
    | .atom, #[] =>
      match unicodeNotNfc? (textOf src range) with
      | some (value, normal, suggested?) =>
        #[{ lint := .unicodeNotNfc, ref, range, msg := unicodeNotNfcMsg value normal suggested? }]
      | none => #[]
    | .chain ops, _ =>
      -- In a chained comparison, only an operand at either end, which is
      -- in one comparison: the first comparison's left, the last's right.
      let n := ops.size
      let at_ (i : Nat) : Array (ShapeReport α) := Id.run do
        let some c := Comparison.ofOp? ops[i]! | return #[]
        let ((oa, ta), (ob, tb)) := (offset kids[i]!, offset kids[i + 1]!)
        let (fires, strict, dropLeft) := intPlusOne c oa ob
        unless fires && intPlusOneInChain dropLeft i n do return #[]
        let texts := kids.mapIdx fun j k => if dropLeft && j == 0 then ta else if !dropLeft && j == n then tb else text k
        let slots := kind.slots
        let ops' := ops.set! i strict.op
        let ts := texts.mapIdx fun j t => t.inSlot (slots[j]?.join) (j < n)
        let body := (ops'.zip (ts.extract 1)).foldl (fun acc (op, t) => s!"{acc} {op} {t}") (ts[0]?.getD "")
        return report .intPlusOne intPlusOneMsg { text := body, prec := kind.prec }
      if kids.size == n + 1 && n ≥ 1 then at_ 0 ++ (if n ≥ 2 then at_ (n - 1) else #[]) else #[]
    | _, _ => #[]
  (kids.zipIdx.foldl (init := own) fun acc (k, i) => acc ++ shapeReports src k (kind.slots[i]?.join) range)

/-- The reports of `double_neg`, `int_plus_one`, `neg_multiply` and
`unicode_not_nfc` in an expression written in `src`, in the order they start, the outer of two
that start together first. -/
def arithReports [Inhabited α] (src : Array Char) (root : BNode α) : Array (ShapeReport α) :=
  let range := match root with | .mk _ r .. => r
  (shapeReports (upTo src range) root none range).qsort fun a b =>
    a.range.start < b.range.start || (a.range.start == b.range.start && a.range.stop > b.range.stop)

end Fren.Core
