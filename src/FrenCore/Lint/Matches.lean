-- keep-sorted start
import FrenCli.Quote
import FrenCore.Lint.Tree
-- keep-sorted end

/-!
# Match, pattern and guard lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Matches -/

/-- `r` with the parentheses directly around it in `src`. -/
partial def withParens (src : Array Char) (r : Range) : Range :=
  if enclosed src { start := 0, stop := src.size } r then Id.run do
    let mut i := r.start
    while src[i - 1]!.isWhitespace do i := i - 1
    let mut j := r.stop
    while src[j]!.isWhitespace do j := j + 1
    return withParens src { start := i - 1, stop := j + 1 }
  else r

/-- An arm of a `match`, as the match lints see it. -/
structure ArmInfo where
  /-- The texts of its pattern's alternatives, as written; none for `_`. -/
  alts : Array String
  /-- Its pattern binds a name. -/
  binds : Bool
  /-- Each alternative is a variant without a payload. -/
  noPayload : Bool
  /-- Each alternative is a variant without a payload or a literal
  (`equatable`). -/
  equatable : Bool := false
  /-- Its pattern overlaps another only where one contains the other
  (`disjointPat`); so does `_`. -/
  disjoint : Bool := false
  /-- Its body, as written, with the parentheses around it. -/
  body : BText
  deriving Inhabited

def ArmInfo.wildcard (a : ArmInfo) : Bool := a.alts.isEmpty

/-- The pattern as written, with ` | ` between alternatives. -/
def ArmInfo.pattern (a : ArmInfo) : String := if a.wildcard then "_" else " | ".intercalate a.alts.toList

/-- Whether `match_same_arms` fires on two arms (`lint::match_same_arms`). -/
def sameArmsFires (sameBody binds : Bool) : Bool := sameBody && !binds

/-- The fix of `match_same_arms` for a group of arms (`lint::ArmsFix`). -/
inductive ArmsFix where
  | merge
  | remove
  | replace
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The fix for a group of arms with the same body, from whether it is
every arm of the `match` and whether one of them is `_`
(`lint::match_same_arms`). -/
def sameArmsFix (all wildcard : Bool) : ArmsFix :=
  if all then .replace else if wildcard then .remove else .merge

/-- The groups of arms that `match_same_arms` fires on, in order, each in
order: the arms that bind no names, by their bodies, where two or more have
one. -/
def sameArmGroups (arms : Array ArmInfo) : Array (Array Nat) := Id.run do
  -- Each body's form once, not once for each group it is compared with.
  let forms := arms.map (writtenForm ·.body.text)
  let mut groups : Array (Array Nat) := #[]
  for a in arms, i in [0:arms.size] do
    let fires (g : Array Nat) :=
      let b := arms[g[0]!]!
      sameArmsFires (forms[g[0]!]! == forms[i]!) (b.binds || a.binds)
    match groups.findIdx? fires with
    | some j => groups := groups.modify j (·.push i)
    | none => if !a.binds then groups := groups.push #[i]
  return groups.filter (·.size ≥ 2)

/-- The fix of a group of `sameArmGroups`. -/
def groupFix (arms : Array ArmInfo) (g : Array Nat) : ArmsFix :=
  sameArmsFix (g.size == arms.size) (g.any (arms[·]!.wildcard))

/-- The arms of a group that its fix removes: all but `_`, or the first. -/
def groupRemoved (arms : Array ArmInfo) (g : Array Nat) : Array Nat :=
  if groupFix arms g == .remove then g.filter (!arms[·]!.wildcard) else g.extract 1 g.size

/-- The message of `match_same_arms` for a group, and the arm it is
reported at, the first that the fix removes. `slot` is where the `match`
is, for the body that replaces it, and `followed` whether an operator
follows it (`BText.inSlot`). -/
def sameArmsMsg (arms : Array ArmInfo) (g : Array Nat) (slot : Option Slot) (followed : Bool) : Nat × Msg :=
  let fix := groupFix arms g
  let removed := groupRemoved arms g
  let first := arms[g[0]!]!
  let body := first.body.text
  let headline := if fix == .remove then "this arm has the same body as the `_` arm"
    else s!"this arm has the same body as the arm `{first.pattern}`"
  let others := (removed.extract 1 removed.size).map (arms[·]!.pattern)
  let so := if others.isEmpty then #[]
    else #[s!"note: so {if others.size == 1 then "does the arm" else "do the arms"} {proseList others}"]
  let help := match fix with
    | .merge => s!"help: merge them into one arm, `{" | ".intercalate (g.flatMap (arms[·]!.alts)).toList} => {body}`"
    | .remove => s!"help: remove {if removed.size == 1 then "it" else "them"}, so that `_` covers {if removed.size == 1 then "its" else "their"} variants too"
    | .replace => s!"help: replace the `match` with its body, `{first.body.inSlot slot followed}`"
  let notes := so ++ (if fix == .replace then #["note: every arm of the `match` has this body"] else #[]) ++ #[help]
  (removed[0]!, { code? := some Lint.matchSameArms.code, headline, label? := some "the same body", notes })

/-- The edits that fix `match_same_arms` in a `match` written at `range`,
where `slot` is and `followed` whether an operator follows it, given each
arm's range, its pattern's and its body's, with the parentheses around it. An arm that the fixes remove is removed
with the `,` between it and a kept arm. -/
def sameArmsEdits (range : Range) (arms : Array ArmInfo) (armRanges patRanges bodyRanges : Array Range)
    (slot : Option Slot) (followed : Bool) : Array (Range × String) := Id.run do
  let groups := sameArmGroups arms
  if let some g := groups.find? (groupFix arms · == .replace) then
    -- The body of the first arm, without what is around it.
    let b := arms[g[0]!]!.body
    let bare := b.inSlot slot followed == b.text
    let r := bodyRanges[g[0]!]!
    return #[({ start := range.start, stop := r.start }, if bare then "" else "("),
             ({ start := r.stop, stop := range.stop }, if bare then "" else ")")]
  let mut edits := #[]
  for g in groups do
    if groupFix arms g == .merge then
      edits := edits.push (patRanges[g[0]!]!, " | ".intercalate (g.flatMap (arms[·]!.alts)).toList)
  let removed := groups.flatMap (groupRemoved arms)
  let mut i := 0
  while i < arms.size do
    if !removed.contains i then i := i + 1; continue
    let mut j := i
    while j + 1 < arms.size && removed.contains (j + 1) do j := j + 1
    edits := edits.push <| if j + 1 < arms.size then ({ start := armRanges[i]!.start, stop := armRanges[j + 1]!.start }, "")
      else ({ start := armRanges[i - 1]!.stop, stop := armRanges[j]!.stop }, "")
    i := j + 1
  return edits

/-- Whether `match_like_membership` fires, whether its fix is negated, of
the alternatives whose arms are `false`, and whether it is a pattern test
rather than an equation: unless it lists one alternative, which `=` can
write (`lint::match_like_membership`). -/
def matchMembership (boolBodies binds disjoint trueFirst falseFirst equatableTrue equatableFalse wildcard
    wildcardTrue : Bool) (nTrue nFalse : Nat) : Bool × Bool × Bool :=
  let negated := if wildcard then wildcardTrue else if disjoint then nTrue > nFalse else falseFirst
  (boolBodies && !binds && (disjoint || if negated then falseFirst else trueFirst), negated,
    !(if negated then equatableFalse else equatableTrue) || (if negated then nFalse else nTrue) != 1)

/-- The fix of `match_like_membership`, if it fires, as the texts before
and after the scrutinee, which is `scrutinee` as written, with the
parentheses around it, and whether it is a pattern test; `slot` is where
the `match` is. -/
def membershipParts? (arms : Array ArmInfo) (scrutinee : BText) (slot : Option Slot) :
    Option (String × String × Bool) := do
  let lit (b : Bool) (a : ArmInfo) := a.body.text == toString b
  let boolBodies := arms.all (fun a => lit true a || lit false a) && arms.any (lit true) && arms.any (lit false)
  let wild? := arms.find? (·.wildcard)
  let named (b : Bool) := (arms.filter fun a => !a.wildcard && lit b a).flatMap (·.alts)
  -- Whether every arm whose body is `b` comes before every other arm but `_`.
  let first (b : Bool) := Id.run do
    let mut other := false
    for a in arms do
      if a.wildcard then continue
      if !lit b a then other := true
      else if other then return false
    return true
  let equatable (b : Bool) := arms.all fun a => a.wildcard || !lit b a || a.equatable
  let (fires, negated, test) := matchMembership boolBodies (arms.any (·.binds)) (arms.all (·.disjoint)) (first true)
    (first false) (equatable true) (equatable false) wild?.isSome (wild?.any (lit true)) (named true).size
    (named false).size
  guard fires
  let vs := named !negated
  let (op, prec) := if test then (s!" is {" | ".intercalate vs.toList}", if negated then 4 else 5)
    else (s!" {if negated then "!=" else "="} {vs[0]!}", 5)
  let bareScrutinee := bareOperand 5 scrutinee.prec .nonAssoc false
  let pre := (if negated && test then "not " else "") ++ (if bareScrutinee then "" else "(")
  let post := (if bareScrutinee then "" else ")") ++ op
  let bare := match slot with | some s => bareOperand s.outer prec s.assoc s.right | none => true
  return if bare then (pre, post, test) else ("(" ++ pre, post ++ ")", test)

/-- `match_like_membership`'s message, whose fix is `replacement`, a
pattern test if `test`. -/
def membershipMsg (replacement : String) (test : Bool) : Msg :=
  { code? := some Lint.matchLikeMembership.code, headline := "this `match` only tests which of its patterns its scrutinee matches"
    label? := some "each arm is `true` or `false`"
    fixes := #[{ msg := if test then "write it as a pattern test" else "write it as an equation", replacement }] }

/-! ## Pattern tests -/

/-- Whether the pattern `p` matches every value of `ty`: `_` is not useful
after it, as for an arm after it (`Reqs/Lang/Patterns`). -/
def matchesEvery (sigs : Sigs) (ty : PatTy) (p : Pat) : Bool := !useful sigs [ty] #[[p]] [.wild]

/-- Whether the pattern `p` contains a binder. -/
partial def Pat.bindsName : Pat → Bool
  | .wild b => b
  | .ctor _ args => args.any (·.bindsName)
  | .or alts => alts.any (·.bindsName)
  | _ => false

/-- Whether `irrefutable_is` fires on `e is P`, from whether `P` binds a
name, which what follows the test needs, and whether it matches every
value of `e`'s type (`lint::irrefutable_is`). -/
def irrefutableIs (binds matchesEvery : Bool) : Bool := !binds && matchesEvery

/-- `irrefutable_is` on `e is p`, where `e` is a `ty`: both front ends call
this, with the pattern (`lint::irrefutable_is`). -/
def irrefutableIsAt (sigs : Sigs) (ty : PatTy) (p : Pat) : Bool := irrefutableIs p.bindsName (matchesEvery sigs ty p)

/-- `e is P` that is always `true`, where `e` is a `ty`. -/
def irrefutableIsMsg (ty : String) (wildcard : Bool) : Msg :=
  { code? := some Lint.irrefutableIs.code, headline := "this pattern test is always `true`"
    label? := some (if wildcard then "`_` matches every value" else s!"matches every value of `{ty}`") }

/-- The alternatives of `p`'s own or-pattern, or `p` itself. -/
def Pat.top : Pat → Array Pat
  | .or alts => alts
  | p => #[p]

/-- Whether an alternative, written `text`, is one that `=` and `in` can
write: a variant without a payload, `true`, `false`, a string literal, or
an integer literal, not a range of one value. -/
def equatableAlt (p : Pat) (text : String) : Bool :=
  match p with
  | .ctor _ args => args.isEmpty
  | .bool _ | .str _ => true
  | .int (some a) (some b) => a == b && writtenForm text == toString a
  | _ => false

/-- Whether each alternative of `p`, written `texts`, is one that `=` and
`in` can write (`equatableAlt`). -/
def equatable (p : Pat) (texts : Array String) : Bool :=
  p.top.size == texts.size && (p.top.zip texts).all fun (a, t) => equatableAlt a t

/-- Whether `p`, written `texts`, overlaps another such pattern only where
one contains the other: each alternative is a literal, `true`, `false`, or
a variant whose payload's patterns are `_` (`lint::match_like_membership`). -/
def disjointPat (p : Pat) (texts : Array String) : Bool :=
  p.top.size == texts.size && (p.top.zip texts).all fun (a, t) =>
    equatableAlt a t || match a with | .ctor _ args => args.all (· matches .wild false) | _ => false

/-- Whether `is_equality` fires on `e is P`, from the number of
alternatives of `P`, whether each is a variant without a payload or a
literal, and whether `irrefutable_is` fires on it (`lint::is_equality`). -/
def isEquality (nAlts : Nat) (equatable irrefutable : Bool) : Bool := nAlts == 1 && equatable && !irrefutable

/-- `is_equality`'s message on `e is P`, from `e` as written, with the
parentheses around it, and the alternative that is `P`. -/
def isEqualityMsg (scrutinee : BText) (alt : String) : Msg :=
  let fixed := (fren_expr!{ $scrutinee = $(Tree.atom alt) }).print.text
  { code? := some Lint.isEquality.code, headline := "this pattern test is an equation"
    label? := some "names a variant without a payload, or a literal"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `single_match_else` fires on a `match` of `nArms` arms, from
whether its first arm's pattern is a test, a pattern other than `_` that
binds nothing, on a scrutinee that is not a `Bool`, whether the second is
`_`, and whether `match_like_membership`, `needless_match`,
`trivial_match` or `match_same_arms` fires on it
(`lint::single_match_else`). -/
def singleMatchElse (nArms : Nat) (test wildcard other : Bool) : Bool :=
  nArms == 2 && test && wildcard && !other

/-- The fix of `single_match_else`, if it fires, where `other` says that
another match lint fires on it, and `bool` that the scrutinee is a `Bool`:
`if x = V then a else b`, or with `x in {V, W}` for several variants
without a payload or literals, or `x is P` for another pattern, from the
scrutinee `x` as written, with the parentheses around it, in parentheses
where `slot` requires them, or where it is `followed` (`BText.inSlot`). -/
def singleMatchElseFix? (arms : Array ArmInfo) (scrutinee : BText) (slot : Option Slot) (other : Bool)
    (followed : Bool := false) (bool : Bool := false) : Option String := do
  let #[a, b] := arms | none
  let sameBodies := writtenSame a.body.text b.body.text
  guard (singleMatchElse arms.size (!a.wildcard && !a.binds && !bool) b.wildcard (other || sameBodies))
  let alts := a.alts.map Tree.atom
  let test := if a.equatable && a.alts.size == 1 then fren_expr!{ $scrutinee = $(alts[0]!) }
    else if a.equatable then fren_expr!{ $scrutinee in {$alts,*} }
    else fren_expr!{ $scrutinee is $(a.pattern) }
  return (fren_expr!{ if $test then $(a.body) else $(b.body) }).inSlot slot followed

/-- A match lint's message about a table over a scrutinee, which means a
`match` whose arms are disjoint, and which the lints look at as at that
`match`: it calls it a table (`Reqs/Lint/Pedantic/Matches#arms`). -/
def Msg.ofTable (m : Msg) : Msg :=
  let f (t : String) := t.replace "`match`" "table"
  { m with headline := f m.headline, label? := m.label?.map f, notes := m.notes.map f
           fixes := m.fixes.map fun x => { x with msg := f x.msg } }

/-- `single_match_else` on a `match` whose fix is `replacement`, which it
does not have where the `match` is `commented`: the fix would drop its
comments. -/
def singleMatchElseMsg (replacement : String) (commented : Bool := false) : Msg :=
  { code? := some Lint.singleMatchElse.code, headline := "this `match` tests for one pattern"
    label? := some "one pattern, then `_`"
    notes := if commented then #["note: the fix would drop the comments in the `match`, so it has none"] else #[]
    fixes := if commented then #[] else #[{ msg := "write it as an `if`", replacement }] }

/-- Whether `wildcard_single_variant` fires on a `_` arm, from the number
of variants it covers (`lint::wildcard_single_variant`). -/
def wildcardSingle (nCovered : Nat) : Bool := nCovered == 1

/-- How a pattern in module `from_` names the variant `v` of the
enumeration `enum`, with `extra` shadowing, if one of these resolves to
it: a path that another pattern of the `match` writes, `siblings`, with
its last segment replaced; `V`; or `E::V`. -/
def Table.variantPath? (t : Table) (from_ : Name) (extra : Array Name) (enum v : Name) (siblings : Array (Array Name)) :
    Option (Array Name) :=
  let candidates := siblings.filterMap (fun s => if s.size ≥ 2 then some (s.pop.push v) else none)
    ++ #[#[v], #[Name.mkSimple enum.getString!, v]]
  candidates.find? fun segs => match t.resolvePath from_ segs extra with
    | .ok (.variant en idx) => en.path == enum && en.variants[idx]? == some v
    | _ => false

/-- The pattern of a variant whose path is `segs` and whose payload has `n`
values: `E::V`, or `E::V(_, _)` with one `_` for each. -/
def variantPattern (segs : Array Name) (n : Nat) : String :=
  "::".intercalate (segs.map toString).toList ++ (if n == 0 then "" else s!"({", ".intercalate (List.replicate n "_")})")

/-- A `_` arm that covers only the variant `v`, with the pattern that names
it, if one resolves. -/
def wildcardMsg (v : Name) (pattern? : Option String) : Msg :=
  { code? := some Lint.wildcardSingleVariant.code, headline := s!"`_` matches only `{showPath v}`"
    label? := some "matches one variant"
    notes := #[s!"note: named, a variant added later makes the `match` non-exhaustive, an error, rather than matched by `_`"]
    fixes := pattern?.toArray.map fun p => { msg := "name the variant", replacement := p } }

/-- Whether `wildcard_enum_match_arm` fires on an arm, if it is `_`, and
whether it has a fix, from the number of variants it matches that no
pattern names (`lint::wildcard_enum_match_arm`). -/
def wildcardEnumMatchArm (wildcard : Bool) (nUnnamed : Nat) : Bool × Bool := (wildcard, wildcard && nUnnamed == 0)

/-- A `_` arm that matches the variants `vs`, with the or-pattern that
names them, if each has a pattern that resolves. -/
def wildcardEnumMsg (vs : Array Name) (pattern? : Option String) : Msg :=
  { code? := some Lint.wildcardEnumMatchArm.code, headline := s!"`_` matches {proseList (vs.map showPath)}"
    label? := some "matches every variant that no other arm names"
    notes := #["note: a variant added later is matched by `_` too, without notice"]
    fixes := pattern?.toArray.map fun p =>
      { msg := if vs.size == 1 then "name the variant" else "name the variants", replacement := p } }

/-! ## Patterns as written -/

/-- A pattern as written: what it resolves to, its text, where it is in a
front end's representation (`α`), and its parts, an or-pattern's
alternatives or a variant's payload's patterns. -/
inductive PatNode (α : Type) where
  | mk (pat : Pat) (text : String) (at_ : α) (kids : Array (PatNode α))

instance [Inhabited α] : Inhabited (PatNode α) := ⟨.mk default "" default #[]⟩

def PatNode.pat : PatNode α → Pat | .mk p .. => p
def PatNode.text : PatNode α → String | .mk _ t .. => t
def PatNode.at_ : PatNode α → α | .mk _ _ a _ => a
def PatNode.kids : PatNode α → Array (PatNode α) | .mk _ _ _ k => k

/-- The or-patterns of two or more alternatives within `n`, `n` too if it
is one, in preorder. -/
partial def PatNode.orPatterns (n : PatNode α) : Array (PatNode α) :=
  (if n.pat matches .or _ && n.kids.size ≥ 2 then #[n] else #[]) ++ n.kids.flatMap PatNode.orPatterns

/-- Whether `wildcard_in_or_patterns` fires on an or-pattern, from whether
one of its alternatives is `_` (`lint::wildcard_in_or_patterns`). -/
def wildcardInOr (wildcard : Bool) : Bool := wildcard

/-- An or-pattern with a `_` alternative. -/
def wildcardInOrMsg : Msg :=
  { code? := some Lint.wildcardInOrPatterns.code, headline := "this or-pattern has `_` as an alternative"
    label? := some "matches every value"
    notes := #["note: `_` matches every value, so the other alternatives add nothing"]
    fixes := #[{ msg := "write `_`", replacement := "_" }] }

/-- Whether a bound of a range, written `s`, after the `..` and any `=`,
is an integer literal, possibly negated, or absent, rather than a
constant. -/
def literalBound (s : String) : Bool :=
  match s.toList.dropWhile (fun c => c == '=' || c.isWhitespace) with
  | [] => true
  | c :: rest => c.isDigit || (c == '-' && (rest.dropWhile Char.isWhitespace).head?.any Char.isDigit)

/-- Whether the integer pattern written `text`, a literal or a range, has
only literal bounds. -/
def literalBounds (text : String) : Bool := (text.splitOn "..").all literalBound

/-- Whether the lower bound `lo` is at most the upper bound `hi`, where
`none` is unbounded. -/
def lowerAtMost : Option Int → Option Int → Bool
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- The one interval that the intervals `ivs` make together, if they leave
no gap between them. -/
def unionInterval? (ivs : Array (Option Int × Option Int)) : Option (Option Int × Option Int) := do
  let sorted := ivs.qsort fun a b => match a.1, b.1 with
    | none, some _ => true
    | some x, some y => decide (x < y)
    | _, _ => false
  let (lo, hi₀) ← sorted[0]?
  let mut hi := hi₀
  for (l, h) in sorted.extract 1 sorted.size do
    let some h₀ := hi | continue
    unless lowerAtMost l (some (h₀ + 1)) do failure
    hi := h.map (max h₀)
  return (lo, hi)

/-- Whether `manual_range_patterns` fires on an or-pattern, from the number
of its alternatives, whether each is an integer literal or a range with
literal bounds, whether one is a range, and whether together they make
one interval, bounded on some side (`lint::manual_range_patterns`). -/
def manualRangePatterns (nAlts : Nat) (integers range interval : Bool) : Bool :=
  integers && interval && (nAlts ≥ 3 || (nAlts ≥ 2 && range))

/-- The range that matches the integers of the interval `iv`. -/
def rangeText : Option Int × Option Int → String
  | (some l, some h) => s!"{l}..={h}"
  | (some l, none) => s!"{l}.."
  | (none, some h) => s!"..={h}"
  | (none, none) => "_"

/-- The range that replaces an or-pattern whose alternatives are `alts`,
each resolved and written, if `manual_range_patterns` fires on it. -/
def manualRangeFix? (alts : Array (Pat × String)) : Option String :=
  let ivs := alts.filterMap fun (p, t) => match p with
    | .int lo hi => if literalBounds t then some (lo, hi) else none
    | _ => none
  let iv? := (unionInterval? ivs).filter fun iv => iv.1.isSome || iv.2.isSome
  let range := ivs.any fun (lo, hi) => lo.isNone || hi.isNone || lo != hi
  if manualRangePatterns alts.size (ivs.size == alts.size) range iv?.isSome then iv?.map rangeText else none

/-- An or-pattern that matches the integers of the range `fixed`. -/
def manualRangeMsg (fixed : String) : Msg :=
  { code? := some Lint.manualRangePatterns.code, headline := s!"this or-pattern matches the range `{fixed}`"
    label? := some "integers without a gap"
    fixes := #[{ msg := "write the range", replacement := fixed }] }

/-- Whether `unnested_or_patterns` fires on two alternatives of an
or-pattern next to each other, from whether they name the same variant,
and the number of values of its payload whose patterns are not written
the same (`lint::unnested_or_patterns`). -/
def unnestedOr (sameVariant : Bool) (nDiffer : Nat) : Bool := sameVariant && nDiffer == 1

/-- The value of the payload at which two alternatives differ, if
`unnested_or_patterns` fires on them. -/
def differAt? [Inhabited α] (a b : PatNode α) : Option Nat :=
  match a.pat, b.pat with
  | .ctor i _, .ctor j _ =>
    let n := a.kids.size
    let ds := (Array.range n).filter fun k => (writtenForm ·.text) <$> a.kids[k]? != (writtenForm ·.text) <$> b.kids[k]?
    if unnestedOr (i == j && b.kids.size == n) ds.size then ds[0]? else none
  | _, _ => none

/-- The alternatives `run`, of one variant, with the or-pattern of their
patterns of the value `k` of its payload nested there. -/
def nestedText [Inhabited α] (run : Array (PatNode α)) (k : Nat) : String :=
  let a := run[0]!
  let path := String.ofList (a.text.toList.takeWhile (· != '('))
  let args := (Array.range a.kids.size).map fun m =>
    if m == k then " | ".intercalate (run.map (·.kids[k]!.text)).toList else a.kids[m]!.text
  s!"{path}({", ".intercalate args.toList})"

/-- The runs of two or more alternatives of `alts`, next to each other,
that `unnested_or_patterns` fires on: each differs from the first of its
run at the same value of the payload. Each is its first and last index,
and the pattern that replaces it. -/
def unnestedRuns [Inhabited α] (alts : Array (PatNode α)) : Array (Nat × Nat × String) := Id.run do
  let mut out := #[]
  let mut i := 0
  while i + 1 < alts.size do
    match differAt? alts[i]! alts[i + 1]! with
    | none => i := i + 1
    | some k =>
      let mut j := i + 1
      while j + 1 < alts.size && differAt? alts[i]! alts[j + 1]! == some k do j := j + 1
      out := out.push (i, j, nestedText (alts.extract i (j + 1)) k)
      i := j + 1
  return out

/-- Alternatives of one variant that `fixed` writes as one. -/
def unnestedOrMsg (fixed : String) : Msg :=
  { code? := some Lint.unnestedOrPatterns.code, headline := "these alternatives differ only in one value of the payload"
    label? := some "one variant, written more than once"
    fixes := #[{ msg := "nest the or-pattern", replacement := fixed }] }

/-- Whether two intervals have an integer in common. -/
def intervalsMeet (a b : Option Int × Option Int) : Bool := lowerAtMost a.1 b.2 && lowerAtMost b.1 a.2

/-- Whether `match_overlapping_arm` fires on a range of an arm and one of
an earlier arm, from whether they have an integer in common, and whether
the later is within the earlier, or contains it
(`lint::match_overlapping_arm`). -/
def matchOverlappingArm (meet within contains : Bool) : Bool := meet && !within && !contains

/-- For the arms of a `match`, each its alternatives' intervals, `none`
for an alternative that is not an integer pattern: each alternative that
`match_overlapping_arm` fires on, by arm and alternative, with the first
alternative of an earlier arm that it overlaps, by arm and alternative. -/
def overlappingArms (arms : Array (Array (Option (Option Int × Option Int)))) : Array ((Nat × Nat) × (Nat × Nat)) :=
  (Array.range arms.size).flatMap fun j => (Array.range arms[j]!.size).filterMap fun b => do
    let J ← arms[j]![b]!
    let earlier := (Array.range j).flatMap fun i => (Array.range arms[i]!.size).map (i, ·)
    let hit ← earlier.find? fun (i, a) => match arms[i]![a]! with
      | some I => matchOverlappingArm (intervalsMeet I J) (intervalWithin J I) (intervalWithin I J)
      | none => false
    return ((j, b), hit)

/-- A range that overlaps `earlier`, an earlier arm's pattern, without
either containing the other. -/
def overlappingArmMsg (earlier : String) : Msg :=
  { code? := some Lint.matchOverlappingArm.code, headline := s!"this range overlaps `{earlier}`, an earlier arm's pattern"
    label? := some "overlaps an earlier arm"
    notes := #[s!"note: where they overlap, the earlier arm is taken, so this arm matches only part of its range"] }

/-! ## Matches on a binder -/

/-- Whether the text `s` mentions the name `x`: has an identifier, outside
comments and string literals, whose first segment is `x`, with or without
`!`. A path `E::x` names an item, not `x`. An over-approximation, which
keeps a lint that drops `x` from firing. -/
def mentionsName (s : String) (x : String) : Bool := Id.run do
  let cs := (withoutComments s).toList.toArray
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
      i := i + 1
    else if isWordChar c then
      let start := i
      while i < cs.size && isWordChar cs[i]! do i := i + 1
      let w := String.ofList (cs.extract start i).toList
      let afterPath := start ≥ 2 && cs[start - 1]! == ':' && cs[start - 2]! == ':'
      let afterDot := start ≥ 1 && cs[start - 1]! == '.'
      if w == x && !afterPath && !afterDot then return true
    else i := i + 1
  return false

/-- Whether `collapsible_match` fires on an arm whose body is a `match`:
from whether its scrutinee is a binder of the arm's pattern, which is one
variant whose payload's patterns are `_` or binders; whether the inner
`match`'s last arm is `_`, and the first later arm of the outer `match`
that matches the variant is `_` with a body written the same; whether the
binder is mentioned elsewhere in the inner `match`, or the inner `_` arm's
body mentions a binder of the arm's pattern; whether an inner
pattern binds a name that the arm's pattern binds; and the number of
inner arms (`lint::collapsible_match`). -/
def collapsibleMatch (onBinder flat innerWildcard sameWildcard mentioned clash : Bool) (nInner : Nat) : Bool :=
  onBinder && flat && innerWildcard && sameWildcard && !mentioned && !clash && nInner ≥ 2

/-- The arms that replace an arm whose pattern is the variant written
`path` with the payload's patterns `args`, whose body is a `match` on the
binder at `k` with the arms `inner`, as their patterns and bodies, but for
its last, `_`. -/
def collapsedArms (path : String) (args : Array String) (k : Nat) (inner : Array (String × String)) : String :=
  ", ".intercalate (inner.toList.map fun (p, b) => s!"{path}({", ".intercalate (args.modify k fun _ => p).toList}) => {b}")

/-- A `match` on the binder `x` of its arm that the arm's pattern can
match instead, with the arms `fixed?` that replace the arm, unless the
arm has a comment. -/
def collapsibleMatchMsg (x : String) (fixed? : Option String) : Msg :=
  { code? := some Lint.collapsibleMatch.code, headline := s!"this `match` on `{x}` can be part of the arm's pattern"
    label? := some s!"a `match` on `{x}`"
    notes := #["note: its `_` arm has the body of the outer `match`'s `_` arm"] ++
      (if fixed?.isNone then #["note: the fix would drop the comments in the arm, so it has none"] else #[])
    fixes := fixed?.toArray.map fun r => { msg := "match the payload in the arm's pattern", replacement := r } }

/-! ## Matches on a `Bool` -/

/-- Whether `match_bool` fires on a `match` on a `Bool` of `nArms` arms,
from whether the first is `true` or `false` and the second the other or
`_`, and whether `match_like_membership`, `match_same_arms` or
`trivial_match` fires on it (`lint::match_bool`). -/
def matchBool (nArms : Nat) (literals other : Bool) : Bool := nArms == 2 && literals && !other

/-- The fix of `match_bool`, if it fires, where `other` says that another
match lint fires on it: `if x then a else b`, from the scrutinee `x` as
written, and the bodies of the arms, `a` that of the arm that `true`
takes, in parentheses where `slot` requires them, or where it is
`followed` (`BText.inSlot`). -/
def matchBoolFix? (pats : Array Pat) (arms : Array ArmInfo) (scrutinee : String) (slot : Option Slot) (other : Bool)
    (followed : Bool := false) : Option String := do
  let #[p, q] := pats | none
  let #[a, b] := arms | none
  let first? : Option Bool := match p with | .bool v => some v | _ => none
  let literals := first?.any fun v => match q with
    | .bool w => w != v
    | .wild false => true
    | _ => false
  guard (matchBool pats.size literals (other || writtenSame a.body.text b.body.text))
  let (t, f) := if first? == some true then (a, b) else (b, a)
  return (fren_expr!{ if $(Tree.atom scrutinee) then $(t.body) else $(f.body) }).inSlot slot followed

/-- `match_bool` on a `match` whose fix is `replacement`, which it does not
have where the `match` is `commented`. -/
def matchBoolMsg (replacement : String) (commented : Bool := false) : Msg :=
  { code? := some Lint.matchBool.code, headline := "this `match` on a `Bool` is an `if`"
    label? := some "a `match` on a `Bool`"
    notes := if commented then #["note: the fix would drop the comments in the `match`, so it has none"] else #[]
    fixes := if commented then #[] else #[{ msg := "write it as an `if`", replacement }] }

/-! ## Matches that could be tables -/

/-- Whether the static rules accept the arms of a `match` on a value of
`ty`, whose patterns are `pats`, of which those that have a guard are
`guarded`, as the arms of a table over a scrutinee
(`Reqs/Lang/Expressions#tables-over-a-scrutinee`): only the last arm is
`_` without a guard, and `checkTableArms` accepts them. -/
def acceptedAsTable (sigs : Sigs) (ty : PatTy) (pats : Array Pat) (guarded : Array Bool) : Bool :=
  (rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g)).isNone &&
    (checkTableArms sigs ty pats guarded).toBool

/-- Whether `match_could_be_table` fires on a `match` of `nArms` arms, from
whether one has a guard, and whether the static rules accept its arms as
a table's (`acceptedAsTable`) (`lint::match_could_be_table`). -/
def matchCouldBeTable (nArms : Nat) (anyGuard tableAccepted : Bool) : Bool := nArms ≥ 2 && !anyGuard && tableAccepted

/-- `match_could_be_table`, whose fix writes `table` in place of `match`. -/
def matchCouldBeTableMsg : Msg :=
  { code? := some Lint.matchCouldBeTable.code, headline := "the arms of this `match` are disjoint, so it can be a table"
    label? := some "disjoint arms"
    notes := #["note: a table over a scrutinee states that its arms are disjoint, which is checked, so that their order does not matter"]
    fixes := #[{ msg := "write `table` in place of `match`", replacement := "table" }] }

/-! ## Guards -/

/-- Whether the static rules accept a `match`, or a table over a scrutinee
(`table`), on a value of `ty` whose arms' patterns are `pats`, of which
those that have a guard are `guarded`: what the lints that change its
arms' guards ask of their fixes (`lang::match_arms`,
`Reqs/Lang/Expressions#tables-over-a-scrutinee`). -/
def matchAccepted (sigs : Sigs) (ty : PatTy) (pats : Array Pat) (guarded : Array Bool) (table : Bool) : Bool :=
  if table then acceptedAsTable sigs ty pats guarded else (checkMatch sigs ty pats guarded).toBool

/-- A guard of a `match` arm as `trivial_guard` reads it, without the
parentheses around it (`lint::Guard`): none, the literal `true` or `false`,
or another expression. -/
inductive GuardForm where
  | absent
  | literal (b : Bool)
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The fix of `trivial_guard` (`lint::GuardFix`). -/
inductive GuardFix where
  | unchanged
  | dropGuard
  | dropArm
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `trivial_guard` fires on an arm whose guard is `g`, and its fix,
where `accepted` says that the static rules accept the `match` after the
fix, and `commented` that the text the fix removes has a comment
(`lint::trivial_guard`): the guard `true` is removed, and the arm whose
guard is `false`. -/
def trivialGuard (g : GuardForm) (accepted commented : Bool) : Bool × GuardFix :=
  match g with
  | .literal b => (true, if !accepted || commented then .unchanged else if b then .dropGuard else .dropArm)
  | _ => (false, .unchanged)

/-- `trivial_guard` on the guard `b`, whose fix is `fix`; `rejected` says
that the `match` without it is rejected, rather than that the text has a
comment, where it has none. -/
def trivialGuardMsg (b : Bool) (fix : GuardFix) (rejected : Bool) : Msg :=
  let why := if rejected then
      if b then "note: without the guard, the `match` would have an arm that is never reached, an error, so it has no fix"
      else "note: without the arm, the `match` would not be exhaustive, an error, so it has no fix"
    else if b then "note: the fix would drop the comments in the guard, so it has none"
    else "note: the fix would drop the comments in the arm, so it has none"
  { code? := some Lint.trivialGuard.code
    headline := if b then "this guard is always `true`" else "this guard is always `false`, so the arm is never taken"
    label? := some (if b then "always `true`" else "always `false`")
    notes := (if b then #["note: an arm whose guard is `true` is taken wherever its pattern matches"] else #[]) ++
      (if fix == .unchanged then #[why] else #[])
    fixes := match fix with
      | .dropGuard => #[{ msg := "remove the guard", replacement := "" }]
      | .dropArm => #[{ msg := "remove the arm", replacement := "" }]
      | .unchanged => #[] }

/-- The other operand of a guard `x = v` or `v = x`, where `x` is a binder
of the arm's pattern, as `redundant_guards` reads it (`lint::GuardValue`):
a literal or a variant without a payload, which the pattern `p` writes, or
anything else, such as a constant. -/
inductive GuardValue where
  | pattern (p : Pat)
  | other
  deriving Inhabited

/-- Whether `p` has an or-pattern, at any depth. -/
partial def Pat.hasOr : Pat → Bool
  | .or _ => true
  | .ctor _ args => args.any (·.hasOr)
  | _ => false

/-- The positions of `p`'s binders, in preorder, each the positions within
the payloads from the top that lead to it; those within an or-pattern
are left out. -/
partial def Pat.binderPaths : Pat → Array (List Nat)
  | .wild true => #[[]]
  | .ctor _ args => (args.mapIdx fun j a => (a.binderPaths).map (j :: ·)).flatten
  | _ => #[]

/-- `p` with `q` in place of its binder at `path`, if one is there. -/
def Pat.replaceAt (p : Pat) (path : List Nat) (q : Pat) : Option Pat :=
  match path, p with
  | [], .wild true => some q
  | j :: rest, .ctor idx args => do
    let a ← args[j]?
    return .ctor idx (args.set! j (← a.replaceAt rest q))
  | _, _ => none
termination_by structural path

/-- The pattern that `redundant_guards` gives an arm whose pattern is `p`,
whose guard compares its binder at `path?`, if it is one, with `v`
(`lint::redundant_guards`): `v`'s pattern in place of the binder, where `v`
is a value that a pattern writes. The front ends give no path where `p`
has an or-pattern, whose alternatives each bind the name. -/
def redundantGuard? (p : Pat) (path? : Option (List Nat)) (v : GuardValue) : Option Pat := do
  let path ← path?
  let .pattern q := v | none
  p.replaceAt path q

/-- The path of the binder at `k` of the arm's pattern `p`, in preorder, for
`redundantGuard?`: none where `p` has an or-pattern. -/
def guardBinderPath? (p : Pat) (k? : Option Nat) : Option (List Nat) := do
  guard !p.hasOr
  p.binderPaths[← k?]?

/-- The text `s` with each mention of the name `x` (`mentionsName`)
replaced by `r`, if each is one that a value can replace: none followed by
`!`, which declares the name again, by `.`, `(` or `[`, or by `:=`, and
none between `{` or `,` and `,` or `}`, which may be a field of a record
literal written with its name alone; and none where `s` has a comment,
which may mention it in prose. -/
def replaceMentions? (s : String) (x r : String) : Option String := Id.run do
  if hasComment s then return none
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let next (j : Nat) : Option Char := (cs.extract j cs.size).find? (!·.isWhitespace)
  let prev (j : Nat) : Option Char := (cs.extract 0 j).reverse.find? (!·.isWhitespace)
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      let start := i
      i := i + 1
      while i < cs.size && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
      i := min cs.size (i + 1)
      out := out ++ cs.extract start i
    else if isWordChar c then
      let start := i
      while i < cs.size && isWordChar cs[i]! do i := i + 1
      let w := String.ofList (cs.extract start i).toList
      let afterPath := start ≥ 2 && cs[start - 1]! == ':' && cs[start - 2]! == ':'
      let afterDot := start ≥ 1 && cs[start - 1]! == '.'
      if w == x && !afterPath && !afterDot then
        let after := next i
        if after == some '!' || after == some '.' || after == some '(' || after == some '[' then return none
        let rest := ((cs.extract i cs.size).toList.dropWhile Char.isWhitespace).drop 1
        if after == some ':' && rest.head? == some '=' then return none
        if (prev start == some '{' || prev start == some ',') && (after == some ',' || after == some '}') then return none
        out := out ++ r.toList.toArray
      else out := out ++ cs.extract start i
    else
      out := out.push c
      i := i + 1
  return some (String.ofList out.toList)

/-- `redundant_guards` on a guard that compares the binder `x` with
`value`, as written, with the arm's head and body that replace it from
its pattern to its body's end, `fixed?`; where it has none, `why?` says
why. -/
def redundantGuardsMsg (x value : String) (fixed? : Option String) (why? : Option String) : Msg :=
  { code? := some Lint.redundantGuards.code
    headline := s!"this guard only compares `{x}` with `{value}`, which the arm's pattern can match"
    label? := some s!"`{x}` compared with `{value}`"
    notes := why?.toArray
    fixes := fixed?.toArray.map fun r => { msg := s!"match `{value}` in the pattern, in place of `{x}`", replacement := r } }

/-- An arm's body as `match_arm_if_else` reads it, over written forms
`β` (`lint::IfBody`): without parentheses, `if C then a else d`, with `d`,
or another expression. -/
inductive IfArmBody (β : Type) where
  | ifElse (d : β)
  | plain (b : β)
  deriving Inhabited

/-- An arm of a `match` as `match_arm_if_else` reads it
(`lint::IfArm`). -/
structure IfArmInfo (β : Type) where
  /-- Its pattern is `_` or a binder. -/
  wild : Bool
  body : IfArmBody β
  /-- Its body is an `if` whose condition is a pattern test that binds
  names, which `a` sees: a guard cannot bind them (`F0334`). -/
  binds : Bool := false
  deriving Inhabited

/-- Whether `match_arm_if_else` moves the condition of the arm `a` into a
guard, where the `else` branch is `d` (`lint::moved?`): its body is `if C
then a else d`, and its pattern is not `_` or a binder. -/
def IfArmInfo.moved {β} (same : β → β → Bool) (d : β) (a : IfArmInfo β) : Bool :=
  !a.wild && match a.body with | .ifElse e => same e d | .plain _ => false

/-- Whether the body of the arm `a` is `d`, but not an `if`. -/
def IfArmInfo.plainIs {β} (same : β → β → Bool) (d : β) (a : IfArmInfo β) : Bool :=
  match a.body with | .plain b => same b d | .ifElse _ => false

/-- Whether `match_arm_if_else`'s fix adds `_ => d` after the arms `arms`:
unless the last is `_` or a binder with the body `d`, not as an `if`
(`lint::match_arm_if_else`'s `appended`). -/
def matchArmIfElseAppends {β} (same : β → β → Bool) (arms : List (IfArmInfo β)) (d : β) : Bool :=
  !(arms.getLast?.any fun a => a.wild && a.plainIs same d)

/-- What `match_arm_if_else` does with the arms `arms` of a `match` without
guards, where the arms whose bodies are `if C then a else d` share the
`else` branch `d`, if it fires (`lint::match_arm_if_else`): the arms whose
conditions it moves into guards, and whether it adds a `_` arm. `same`
says that two bodies are written the same, `mentions d j` that `d`
mentions a binder of arm `j`'s pattern, and `overlap i j` that the
patterns of arms `i` and `j` may have a value in common
(`Pat.overlapWit?`). It fires where it moves two or more arms, `d`
mentions a binder of none of them, and after each, every arm whose
pattern overlaps its own has the body `d`, not as an `if`, and `d`
mentions none of its binders: the values that the arm's condition leaves
reach those arms, and the `_` arm, where `d` must mean what it meant in the
arm. It adds `_ => d` unless the last arm is `_` or a binder with the body
`d`. The front ends also ask that the static rules accept the arms with
the fix (`matchAccepted`). -/
def matchArmIfElseFor {β} (same : β → β → Bool) (mentions : β → Nat → Bool) (overlap : Nat → Nat → Bool)
    (arms : List (IfArmInfo β)) (d : β) : Option (List Nat × Bool) :=
  let moved (i : Nat) : Bool := (arms[i]?.map (·.moved same d)).getD false
  let ix := List.range arms.length
  let binds (i : Nat) : Bool := (arms[i]?.map (·.binds)).getD false
  let fires := ix.any (fun i => ix.any fun j => decide (i < j) && moved i && moved j) &&
    ix.all (fun i => !moved i || !mentions d i) &&
    ix.all (fun i => !moved i || !binds i) &&
    ix.all (fun i => !moved i || ix.all fun j =>
      !decide (i < j) || !overlap i j || ((arms[j]?.map (·.plainIs same d)).getD false && !mentions d j))
  if fires then some (ix.filter moved, matchArmIfElseAppends same arms d) else none

/-- `match_arm_if_else` on the arms `arms`, as `matchArmIfElseFor`, with
the first `else` branch, of an arm whose pattern is not `_` or a binder,
for which it fires, if any: the arms that it changes, their `else`
branch, and whether it adds a `_` arm. -/
def matchArmIfElse? {β} (same : β → β → Bool) (mentions : β → Nat → Bool) (overlap : Nat → Nat → Bool)
    (arms : List (IfArmInfo β)) : Option (Array Nat × β × Bool) :=
  arms.findSome? fun a => match a with
    | { wild := false, body := .ifElse d, .. } =>
      (matchArmIfElseFor same mentions overlap arms d).map fun (g, ap) => (g.toArray, d, ap)
    | _ => none

/-- `match_arm_if_else` on `n` arms whose `else` branch is `d`; the fix
is a set of edits, which it does not make where the text they replace
has a comment (`commented`). -/
def matchArmIfElseMsg (n : Nat) (d : String) (commented : Bool) : Msg :=
  { code? := some Lint.matchArmIfElse.code
    headline := s!"{n} arms of this `match` are `if`s with the same `else` branch"
    label? := some s!"`else {d}`, as in other arms"
    notes := #["note: with each condition as its arm's guard, the values that it leaves fall through to one `_` arm with the `else` branch",
      "help: move each condition into its arm's guard, and give the `else` branch to a `_` arm"] ++
      (if commented then #["note: the fix would drop the comments in the arms, so it has none"] else #[]) }

/-- Whether an arm that matches one variant gives it back, where
`sameVariant` says that its body builds that variant, `binders` are the
texts of the pattern's binders, `_` included, and `args` those of the
body's arguments: the binders, in order, none of them `_`
(`lint::needless_match`). -/
def givesBack (sameVariant : Bool) (binders args : Array String) : Bool :=
  sameVariant && binders.size == args.size && (binders.zip args).all fun (b, a) => b != "_" && writtenSame b a

/-- Whether `needless_match` fires on a `match`, from whether each arm but
`_` gives back the variant it matches, there is a `_` arm, its body is
written the same as the scrutinee, and `trivial_match` fires on it
(`lint::needless_match`). -/
def needlessMatch (givenBack wildcard scrutineeBack trivial : Bool) : Bool :=
  givenBack && (!wildcard || scrutineeBack) && !trivial

/-- A `match` that gives back its scrutinee, whose text, as the fix writes
it, is `fixed`. -/
def needlessMatchMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessMatch.code, headline := "this `match` gives back its scrutinee"
    label? := some "each arm gives back the value it matches"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

end Fren.Core
