-- keep-sorted start
import FrenCli.Quote
import FrenCore.Lint.Cardinality
-- keep-sorted end

/-!
# Pattern tests written as comparisons

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Pattern tests written out -/

/-- An alternative of a pattern, as `manual_pattern_test` reads it
(`lint::Alt`, whose meaning is `lint::alt_pattern`): the integers from
`lo` to `hi`, where `none` leaves that side unbounded, so that a literal
is a range of one integer; a string literal, as written; or a variant, by
its name, with or without a payload. -/
inductive PatAlt where
  | ints (lo hi : Option Int)
  | str (s : String)
  | variant (name : String)
  deriving Inhabited, DecidableEq, Repr

/-- Whether the bound `hi` is below the bound `lo`, so that no integer is
at most `hi` and at least `lo`. -/
def boundBelow : Option Int → Option Int → Bool
  | some h, some l => h < l
  | _, _ => false

/-- Whether no value matches both `a` and `b`, as their text shows
(`lint::alts_disjoint?`): two ranges of integers that do not meet, two string
literals written differently, without escape sequences, or two variants
of different names. A pattern's alternatives are of one type, so two
alternatives of different kinds are never both in a pattern that checks,
and are not disjoint here. -/
def PatAlt.disjoint : PatAlt → PatAlt → Bool
  | .ints l1 h1, .ints l2 h2 => boundBelow h1 l2 || boundBelow h2 l1
  | .str s, .str t => s != t && !Fren.Str.contains s "\\" && !Fren.Str.contains t "\\"
  | .variant v, .variant w => v != w
  | _, _ => false

/-- Whether each two alternatives of `as` are disjoint (`PatAlt.disjoint`). -/
def pairwiseDisjoint : List PatAlt → Bool
  | [] => true
  | a :: as => as.all (a.disjoint ·) && pairwiseDisjoint as

/-- Whether `manual_pattern_test` fires on a run of `nOperands` adjacent
operands of `or`, or of `and`, each an equation, or a disequation, of one
expression with a value that a pattern writes, or a pattern test of it,
or its negation, `nEquations` of them equations, whose alternatives are
`alts`, in order, where `chain` says that `membership_chain` reads the
chain they are in (`lint::run_fires?`). -/
def manualPatternTest (alts : List PatAlt) (nOperands nEquations : Nat) (chain : Bool) : Bool :=
  nOperands ≥ 2 && nEquations ≥ 1 && !chain && pairwiseDisjoint alts

/-- The last segment of a path written `p`, with `::` or `.` between its
segments. -/
def lastSegment (p : String) : String :=
  let p := ((p.splitOn "::").getLast?.getD p)
  (p.splitOn ".").getLast?.getD p

/-- An integer literal written `t`, possibly negated, in decimal. -/
def decimalLiteral? (t : String) : Option Int :=
  let w := writtenForm t
  if w.isEmpty || !(w.toList.all fun c => c.isDigit || c == '-') then none else w.toInt?

/-- A value as written, as `manual_pattern_test` reads it (`lint::Literal`):
a decimal integer literal, possibly negated, by its value; a string literal
without `"` in it, by its text; a variant without a payload, by the last
segment of its name; or anything else, `true` and `false` among them. -/
inductive ValueForm where
  | decimal (k : Int)
  | quoted (t : String)
  | variant (name : String)
  | truth (b : Bool)
  | other
  deriving Inhabited, DecidableEq, Repr

/-- The form of the value written `t`, where `variant?` gives its name if it
is a variant without a payload: the step that reads the text, before
`ValueForm.alt?` decides on its structure. -/
def valueForm (t : String) (variant? : Option String) : ValueForm :=
  let t := t.trimAscii.toString
  if let some k := decimalLiteral? t then .decimal k
  else if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" && t.toList.count '"' == 2 then .quoted t
  else if t == "true" then .truth true
  else if t == "false" then .truth false
  else match variant? with
    | some v => .variant (lastSegment v)
    | none => .other

/-- The alternative of a pattern that writes the value `v`, if there is
one (`lint::value_alt`): none for a negative literal where `nat` says that
the operands are `Nat`s, as an alternative that never matches is an
error. -/
def ValueForm.alt? (nat : Bool) : ValueForm → Option PatAlt
  | .decimal k => if nat && k < 0 then none else some (.ints (some k) (some k))
  | .quoted t => some (.str t)
  | .variant v => some (.variant v)
  | .truth _ => none
  | .other => none

/-- The value written `t` as a pattern's alternative, if a pattern writes it
as `t` is written (`valueForm`, `ValueForm.alt?`). `true` and `false` are
left to `bool_equality`. -/
def valueAlt? (t : String) (variant? : Option String) : Option PatAlt :=
  (valueForm t variant?).alt? false

/-- Whether `t`, written as a value, is one that a pattern writes, as
`membership_chain` asks of each value it puts in a set: as
`valueAlt?` reads it, or `true` or `false`, where `variant` says that it
is a variant without a payload. -/
def patternValue (t : String) (variant : Bool) : Bool :=
  valueForm t (if variant then some t else none) != .other

/-- Splits `t` at each `|` outside parentheses and string literals. -/
def splitAlternatives (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut depth : Nat := 0
  let mut inStr := false
  let mut esc := false
  for c in t.toList do
    if inStr then
      cur := cur.push c
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then
      inStr := true
      cur := cur.push c
    else if c == '(' then
      depth := depth + 1
      cur := cur.push c
    else if c == ')' then
      depth := depth - 1
      cur := cur.push c
    else if c == '|' && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else cur := cur.push c
  return out.push cur.trimAscii.toString

/-- Whether `t` is a path: identifiers joined by `::`. -/
def isPathText (t : String) : Bool :=
  !t.isEmpty && (t.splitOn "::").all fun s =>
    !s.isEmpty && (s.toList.all fun c => c.isAlphanum || c == '_') && !(s.toList.head?.any Char.isDigit)

/-- A bound of a range written `t`, if it is a decimal integer literal:
`some none` where it is left out. -/
def rangeBound? (t : String) : Option (Option Int) :=
  let t := t.trimAscii.toString
  if t.isEmpty then some none else (decimalLiteral? t).map some

/-- An alternative of a pattern test, written `t`, as `manual_pattern_test`
reads it (`PatAlt`), if it can: an integer literal, a range whose bounds
are integer literals, a string literal, or a variant, applied to patterns
or not. `_`, `true`, `false`, and a range with a constant as a bound are
not read. -/
def patternAlt? (t : String) : Option PatAlt :=
  let t := t.trimAscii.toString
  -- A variant, applied or not, before a range, which a payload may hold.
  let head := (t.splitOn "(").head!.trimAscii.toString
  if t == "_" || t == "true" || t == "false" then none
  else if let some k := decimalLiteral? t then some (.ints (some k) (some k))
  else if t.startsWith "\"" then
    if t.length ≥ 2 && t.endsWith "\"" && t.toList.count '"' == 2 then some (.str t) else none
  else if isPathText head && (head == t || t.endsWith ")") then some (.variant (lastSegment head))
  else if let [lo, hi] := t.splitOn "..=" then do
    let (l, h) := (← rangeBound? lo, ← rangeBound? hi)
    guard (h.isSome)
    some (.ints l h)
  else if let [lo, hi] := t.splitOn ".." then do
    let (l, h) := (← rangeBound? lo, ← rangeBound? hi)
    guard (l.isSome)
    some (.ints l (h.map (· - 1)))
  else none

/-- The alternatives of the pattern written `t`, if `patternAlt?` reads
each, with their texts. -/
def patternAlts? (t : String) : Option (Array (PatAlt × String)) := do
  guard (!hasComment t)
  let t := t.trimAscii.toString
  let t := if t.startsWith "|" then (t.drop 1).toString else t
  (splitAlternatives t).mapM fun a => return (← patternAlt? a, a)

/-- An operand of a run that `manual_pattern_test` reads (`lint::Reading`):
the expression it tests, as written, its alternatives, with their texts,
and whether it is an equation, or a disequation, rather than a pattern
test. -/
structure PatternOperand (σ : Type) where
  scrutinee : σ
  alts : List (PatAlt × String)
  equation : Bool

/-- A side of a comparison (`lint::Side`): the expression, its text, and its
value as `valueForm` reads it. -/
structure ComparisonSide (σ : Type) where
  node : σ
  text : String
  value : ValueForm

/-- An operand of a run of `or` or `and`, as `manual_pattern_test` reads its
structure (`lint::Shape`): `l = r` (`equal`) or `l != r`, where `nat` says
that the operands are `Nat`s; `x is P`, or its negation, with `P`'s
alternatives where `patternAlts?` reads each; or anything else. -/
inductive OperandShape (σ : Type) where
  | comparison (equal nat : Bool) (left right : ComparisonSide σ)
  | test (negated : Bool) (scrutinee : σ) (alts : Option (List (PatAlt × String)))
  | other

/-- How `manual_pattern_test` reads an operand of a run of `or`, or of
`and` if `conj`, from its shape (`lint::reading`): an equation for `or`
and a disequation for `and`, with exactly one side a value that a pattern
writes, or a pattern test for `or` and its negation for `and`, whose
alternatives are read. -/
def readOperand (conj : Bool) : OperandShape σ → Option (PatternOperand σ)
  | .comparison equal nat l r =>
    if equal == conj then none
    else match l.value.alt? nat, r.value.alt? nat with
      | none, some a => some { scrutinee := l.node, alts := [(a, r.text)], equation := true }
      | some a, none => some { scrutinee := r.node, alts := [(a, l.text)], equation := true }
      | _, _ => none
  | .test negated x alts =>
    if negated != conj then none
    else alts.map fun as => { scrutinee := x, alts := as, equation := false }
  | .other => none

/-- The shape of `d`, an operand of a run: the step that reads the syntax
tree and the text, before `readOperand` decides on the structure. A side
of a comparison has a value only if it is an atom or a negation, which
`valueForm` reads, with `variant?` saying whether it is a variant without
a payload, and `fact?` whether the comparison's operands are `Nat`s. -/
def operandShape (src : Array Char) (variant? : α → Option String) (fact? : α → Option NodeFact) (d : BNode α) :
    OperandShape (BNode α) :=
  let side (k : BNode α) : ComparisonSide (BNode α) :=
    { node := k, text := textOf src k.range
      value := match k.kind with
        | .atom | .neg | .lit _ => valueForm (textOf src k.range) (variant? k.ref)
        | _ => .other }
  match d.kind, d.kids with
  | .bin op, #[l, r] =>
    if op == "=" || op == "!=" then .comparison (op == "=") (fact? d.ref == some .natOperands) (side l) (side r)
    else .other
  | .not, #[t] => match test? t with
    | some (x, alts) => .test true x alts
    | none => .other
  | _, _ => match test? d with
    | some (x, alts) => .test false x alts
    | none => .other
where
  /-- `x is P`: `x`, and `P`'s alternatives, with their texts, where
  `patternAlts?` reads each. -/
  test? (t : BNode α) : Option (BNode α × Option (List (PatAlt × String))) := do
    let (.patternTest, #[x]) := (t.kind, t.kids) | none
    let rest := (textOf src { start := (withParensIn src t.range x.range).stop, stop := t.range.stop }).trimAscii.toString
    let alts := if rest.startsWith "is" && ((rest.drop 2).toString.toList.head?.any Char.isWhitespace)
      then (patternAlts? (rest.drop 2).toString).map (·.toList) else none
    return (x, alts)

/-- `d`, an operand of a run of `or`, or of `and` if `conj`, as
`manual_pattern_test` reads it: `readOperand` of its `operandShape`. -/
def patternOperand? (src : Array Char) (variant? : α → Option String) (fact? : α → Option NodeFact) (conj : Bool)
    (d : BNode α) : Option (PatternOperand (BNode α)) :=
  readOperand conj (operandShape src variant? fact? d)

/-- The length of the run at the head of `rs` of operands that test the
expression written `f`. -/
def runLength (f : String) : List (Option String) → Nat
  | some g :: rs => if g == f then runLength f rs + 1 else 0
  | _ => 0

theorem runLength_le (f : String) (rs : List (Option String)) : runLength f rs ≤ rs.length := by
  induction rs with
  | nil => simp [runLength]
  | cons r rs ih => cases r with
    | none => simp [runLength]
    | some g => simp only [runLength]; split <;> simp <;> omega

/-- The longest runs of adjacent operands that test one expression, each
from its first position to its last, where `rs` gives, for each operand
from position `i`, the expression it tests, as written, if it is read. -/
def runSpans (i : Nat) : List (Option String) → List (Nat × Nat)
  | [] => []
  | none :: rs => runSpans (i + 1) rs
  | some f :: rs =>
    let k := runLength f rs
    (i, i + k) :: runSpans (i + k + 1) (rs.drop k)
termination_by rs => rs.length
decreasing_by all_goals simp_wf; all_goals omega

/-- The runs that `manual_pattern_test` reports, of operands each read, if
it is, as the expression it tests, as written, its alternatives, and
whether it is an equation, each from its first position to its last
(`lint::manual_pattern_test_runs`): the longest runs of operands that test
one expression, on which `manualPatternTest` fires. -/
def runsOf (vs : List (Option (String × List PatAlt × Bool))) (chain : Bool) : List (Nat × Nat) :=
  (runSpans 0 (vs.map (·.map (·.1)))).filter fun (i, j) =>
    let run := (vs.extract i (j + 1)).filterMap id
    manualPatternTest (run.flatMap (·.2.1)) run.length (run.filter (·.2.2)).length chain

/-- The runs that `manual_pattern_test` reports, of the operands read as
`ps`, where `form` writes the expression that each tests (`runsOf`). -/
def patternRuns (form : σ → String) (ps : List (Option (PatternOperand σ))) (chain : Bool) : List (Nat × Nat) :=
  runsOf (ps.map (·.map fun p => (form p.scrutinee, p.alts.map (·.1), p.equation))) chain

/-- The alternatives of the fix of the run from position `i` to position
`j` of the operands read as `ps`, operand by operand and in order, each
with its text (`lint::manual_pattern_test_fix_alts`). -/
def runAlternatives (ps : List (Option (PatternOperand σ))) (i j : Nat) : List (List (PatAlt × String)) :=
  ((ps.extract i (j + 1)).filterMap id).map (·.alts)

/-- The operands of the chain of `op` that `n` is the top of, as
`membership_chain` reads it: through each operand that is an `op`, in
parentheses or not. -/
partial def chainOperandsOf (op : String) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin o, #[l, r] => if o == op then chainOperandsOf op l ++ chainOperandsOf op r else #[n]
  | _, _ => #[n]

/-- Whether `membership_chain` reads a chain of `or`, or of `and` if
`conj`, whose operands, through parentheses, have the shapes `shapes`
(`lint::membership_chain?`): three or more, each an equation, or a
disequation, with the same left operand, written as `form` writes it,
and some value that is not one that a pattern writes. -/
def membershipChainShapes (form : σ → String) (conj : Bool) (shapes : List (OperandShape σ)) : Bool :=
  match shapes with
  | [] => false
  | s :: _ =>
    shapes.length ≥ 3 && (shapes.all fun t => (chainLeft? t).isSome && chainLeft? t == chainLeft? s)
      && shapes.any unwrittenRight
where
  /-- The left operand of an equation, or for `and` a disequation. -/
  chainLeft? : OperandShape σ → Option String
    | .comparison equal _ l _ => if equal != conj then some (form l.node) else none
    | _ => none
  /-- The right operand of a comparison is a value that no pattern writes. -/
  unwrittenRight : OperandShape σ → Bool
    | .comparison _ _ _ r => r.value == .other
    | _ => false

/-- Whether `membership_chain` reads the chain of `or`, or of `and` if
`conj`, that `n` is the top of: `membershipChainShapes` of its operands,
through parentheses, whose values are read as `patternValue` reads them,
whether or not a later value indexes a sequence, which that lint also
asks. -/
def membershipChainOf (src : Array Char) (variant? : α → Option String) (conj : Bool) (n : BNode α) : Bool :=
  membershipChainShapes (fun b => writtenForm (textOf src b.range)) conj
    ((chainOperandsOf (if conj then "and" else "or") n).toList.map (operandShape src variant? (fun _ => none)))

/-- `manual_pattern_test`'s message, on `x` if `conj` is not set, and
otherwise on its negation, whose fix is `fixed`, at `range`, the
operands with the parentheses around them, or none but a note if a
comment within them would be lost (`commented`). -/
def manualPatternTestMsg (x fixed : String) (conj : Bool) (range : Range) (commented : Bool) : Msg :=
  { code? := some Lint.manualPatternTest.code
    headline := if conj then s!"this says that `{x}` matches none of these patterns" else s!"this says that `{x}` matches one of these patterns"
    label? := some (if conj then "disequations of one expression with values that patterns write" else "equations of one expression with values that patterns write")
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the pattern test would lose the comment within the operands"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed, range? := some range }] }

/-- `manual_pattern_test` on `n`, an `or`, or an `and` if `conj`, in `slot`
within `parent`, if it is the top of a run of them, where `chain` says
that `membershipChainOf` holds of the chain it is in
(`lint::manual_pattern_test_runs`): one report for each longest run of
adjacent operands that `patternOperand?` reads, of an expression written
the same, from the first to the last. -/
def manualPatternTestAt [Inhabited α] (src : Array Char) (variant? : α → Option String) (fact? : α → Option NodeFact)
    (n : BNode α) (conj : Bool) (chain : Bool) (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let op := if conj then "and" else "or"
  unless runTop op src n slot parent do return #[]
  let cs := runOperands op src n
  let ps := cs.map (patternOperand? src variant? fact? conj)
  let form (b : BNode α) := writtenForm (textOf src b.range)
  let mut out := #[]
  for (i, j) in patternRuns form ps.toList chain do
    let some p := ps[i]! | continue
    let alts := (runAlternatives ps.toList i j).flatten
    let x := p.scrutinee.text src
    let pats := alts.toArray.map (·.2)
    let t := (if conj then fren_expr!{ not $x is $pats|* } else fren_expr!{ $x is $pats|* }).print.toBText
    let whole := i == 0 && j + 1 == cs.size
    -- The whole run, in parentheses that the test does not need, is
    -- replaced with them.
    let outer := withParensIn src parent n.range
    let unwrapped := whole && outer != n.range && t.dropsParens slot (followedAt src outer)
    let range : Range := if unwrapped then outer
      else { start := (withParensIn src n.range cs[i]!.range).start, stop := (withParensIn src n.range cs[j]!.range).stop }
    let fixed := if unwrapped then t.text else if whole then placed src n slot parent t
      else t.inSlot (some ⟨(BKind.bin op).prec, .left, i > 0⟩) (j + 1 < cs.size)
    -- Where `manual_ordering` reports the run too, its fix is made,
    -- if `fren fix` makes it.
    let unless? := if whole && (manualOrderingAt? src fact? n slot parent).isSome then some (.manualOrdering, n.ref)
      else none
    out := out.push { lint := .manualPatternTest, ref := cs[i]!.ref, last? := some cs[j]!.ref, unless?
                      msg := manualPatternTestMsg (textOf src p.scrutinee.range) fixed conj range
                        (hasComment (textOf src range)) }
  return out

/-- The variant of an ordered enumeration that `k` is, or that the
newtype `k` builds holds, as its position and the number of variants. -/
def extremeOf? (fact? : α → Option NodeFact) (k : BNode α) : Option (Nat × Nat) :=
  let at_ (k : BNode α) := (ordinalOf? fact? k).map fun (_, p, c) => (p, c)
  match fact? k.ref, k.kids with
  | some (.wraps ..), #[v] => at_ v
  | _, _ => at_ k

/-- Whether `absurd_extreme_comparisons` fires on `x OP v`, or on `v OP x`
if not `right`, where `v` is the variant at `pos` of an ordered
enumeration of `count`, or a newtype of one, and what the comparison
always is (`lint::absurd_ordered`): only the first and the last variants
fix it. -/
def absurdOrdered (op : Comparison) (pos count : Nat) (right : Bool) : Bool × Bool :=
  let first := pos == 0
  let last := pos + 1 == count
  match if right then op else op.mirror with
  | .ge => (first, true)
  | .lt => (first, false)
  | .le => (last, true)
  | .gt => (last, false)
  | _ => (false, false)

/-- A comparison with `v`, the least value of its type if `least` and the
greatest otherwise, that is always `value`. -/
def absurdOrderedMsg (v : String) (least value : Bool) : Msg :=
  { code? := some Lint.absurdExtremeComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{v}` is the {if least then "least" else "greatest"} value of its type"
    notes := #["note: the bound or the operator is probably not the one meant"] }

/-- `absurd_extreme_comparisons` on `n`, a comparison that orders, with
the first or last variant of an ordered enumeration
(`lint::absurd_ordered`). -/
def absurdOrderedAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let #[a, b] := n.kids | none
  let c ← Comparison.ofOp? op
  let try_ (v : BNode α) (right : Bool) : Option (OpReport α) := do
    let (pos, count) ← extremeOf? fact? v
    let (fires, value) := absurdOrdered c pos count right
    guard fires
    let least := if right then c matches .ge | .lt else c matches .le | .gt
    return { lint := .absurdExtremeComparisons, ref := n.ref, msg := absurdOrderedMsg (textOf src v.range) least value }
  try_ b true <|> try_ a false

/-- Whether `unnecessary_min_or_max` fires on `x.min(v)`, or `x.max(v)` if
`max`, where `v` is the variant at `pos` of an ordered enumeration of
`count`, and if it does, whether the call is always `v`, rather than `x`
(`lint::unnecessary_min_or_max`). -/
def unnecessaryMinOrMax (max : Bool) (pos count : Nat) : Option Bool :=
  if pos == 0 then some !max else if pos + 1 == count then some max else none

def unnecessaryMinOrMaxMsg (fixed v : String) (first : Bool) : Msg :=
  { code? := some Lint.unnecessaryMinOrMax.code, headline := s!"this is always `{fixed}`"
    label? := some s!"`{v}` is the {if first then "least" else "greatest"} value of its enumeration"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `unnecessary_min_or_max` on `n`, a call of `min` or `max`, in `slot`
within `parent` (`lint::unnecessary_min_or_max`). -/
def minOrMaxAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  let .method m := n.kind | none
  guard (m == "min" || m == "max")
  let #[x, v] := n.kids | none
  let (_, p, count) ← ordinalOf? fact? v
  let first := p == 0
  let toV ← unnecessaryMinOrMax (m == "max") p count
  let fixed := placed src n slot parent ((if toV then v else x).text src)
  return { lint := .unnecessaryMinOrMax, ref := n.ref, msg := unnecessaryMinOrMaxMsg fixed (textOf src v.range) first }

/-- The value a newtype is built from, of newtypes `β`
(`lint::Inner`): the field of a value of a newtype, or another
expression, with a type of its own or not. -/
inductive RoundtripInner (β : Type) where
  | fieldOf (t : β)
  | typed
  | untyped

/-- `T(e)`, or `T(e).0` (`lint::Roundtrip`). -/
inductive Roundtrip (β : Type) where
  | built (t : β) (e : RoundtripInner β)
  | read (t : β) (e : RoundtripInner β)

/-- Whether `redundant_newtype_roundtrip` fires, and with a fix
(`lint::RoundtripFix`). -/
inductive RoundtripFix where
  | unchanged
  | reported
  | fixed
  deriving DecidableEq

/-- What `redundant_newtype_roundtrip` does on `r`
(`lint::redundant_newtype_roundtrip`): `T(x.0)` is `x` where `x` is a `T`,
and `T(e).0` is `e`, but for `T(x.0).0`, which is reported at `T(x.0)`,
and without a fix where `e` takes its type from the newtype. -/
def redundantNewtypeRoundtrip [DecidableEq β] : Roundtrip β → RoundtripFix
  | .built t (.fieldOf u) => if t = u then .fixed else .unchanged
  | .built _ _ => .unchanged
  | .read t (.fieldOf u) => if t = u then .unchanged else .fixed
  | .read _ .untyped => .reported
  | .read _ .typed => .fixed

/-- `Ms(x.0)`, or `Ms(n).0` if `read`, whose fix is `fixed`, or none but
a note if `n` takes its type from the newtype (`untyped`). -/
def roundtripMsg (newtype fixed : String) (read untyped : Bool) : Msg :=
  { code? := some Lint.redundantNewtypeRoundtrip.code
    headline := if read then "this reads the field of a newtype just built" else "this builds a newtype from the field of one of its own"
    label? := some s!"a round trip through `{newtype}`"
    notes := if untyped then #[s!"note: `fren fix` leaves this, since `{fixed}` takes its type from the newtype, and has none without it"]
      else #[]
    fixes := if untyped then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `redundant_newtype_roundtrip` on `n`, in `slot` within `parent`
(`lint::redundant_newtype_roundtrip`). -/
def roundtripAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  let #[k] := n.kids | none
  let #[x] := k.kids | none
  let inner (synth : Bool) : RoundtripInner String := match fact? x.ref with
    | some (.unwraps u) => .fieldOf u
    | _ => if synth then .typed else .untyped
  let (t, shape) ← match fact? n.ref, fact? k.ref with
    | some (.wraps t _), some (.unwraps u) => some (t, Roundtrip.built t (.fieldOf u))
    | some (.unwraps _), some (.wraps t synth) => some (t, Roundtrip.read t (inner synth))
    | _, _ => none
  let fix := redundantNewtypeRoundtrip shape
  guard (fix != .unchanged)
  let read := shape matches .read ..
  let untyped := fix == .reported
  let fixed := placed src n slot parent (x.text src)
  let name := (t.splitOn ".").getLast?.getD t
  return { lint := .redundantNewtypeRoundtrip, ref := n.ref, msg := roundtripMsg name fixed read untyped }

end Fren.Core
