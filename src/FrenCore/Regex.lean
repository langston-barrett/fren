-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Str
import Lean.ToExpr
-- keep-sorted end

/-!
# Patterns

The patterns of `s.matches?(p)` (`Reqs/Lang/Expressions#patterns`), shared by
both front ends: the parser, their meaning, which the Lean mapping and the
evaluator use, and their SMT-LIB form, which the `fren` command and the
Lean translator use.
-/

namespace Fren.Core

/-- A pattern. `p+`, `p?` and `p{m,n}` are written with these. -/
inductive Re where
  /-- Matches nothing: what a class with no characters would match. -/
  | none
  /-- Exactly these characters; `str []` matches the empty string. -/
  | str (cs : List Char)
  /-- One character in the ranges, or, if `neg`, not in them. -/
  | cls (neg : Bool) (ranges : List (Char × Char))
  /-- Any one character. -/
  | any
  | union (a b : Re)
  | cat (a b : Re)
  | star (a : Re)
  deriving Inhabited, BEq, Repr, Lean.ToExpr

/-- Whether `c` is in one of `ranges`. -/
def inRanges (ranges : List (Char × Char)) (c : Char) : Bool := ranges.any fun (lo, hi) => lo ≤ c && c ≤ hi

/-- Whether the whole of `cs` matches `r`. -/
def Re.mat : Re → List Char → Bool
  | .none, _ => false
  | .str s, cs => cs == s
  | .cls neg rs, cs => match cs with
    | [c] => inRanges rs c != neg
    | _ => false
  | .any, cs => cs.length == 1
  | .union a b, cs => a.mat cs || b.mat cs
  | .cat a b, cs => (List.range (cs.length + 1)).any fun i => a.mat (cs.take i) && b.mat (cs.drop i)
  | .star a, cs => match cs with
    | [] => true
    | c :: rest => (List.range (rest.length + 1)).any fun i =>
      a.mat (c :: rest.take i) && (Re.star a).mat (rest.drop i)
termination_by r cs => sizeOf r + cs.length
decreasing_by
  all_goals simp_wf
  all_goals
    try simp only [List.length_take, List.length_drop, List.length_cons]
    omega

/-! ### What patterns mean -/

theorem Re.mat_cls (n : Bool) (rs : List (Char × Char)) (cs : List Char) :
    (Re.cls n rs).mat cs = (match cs with | [c] => inRanges rs c != n | _ => false) := by
  match cs with
  | [] => rw [Re.mat]; simp
  | [_] => rw [Re.mat]
  | _ :: _ :: _ => rw [Re.mat]; simp

theorem Re.mat_any (cs : List Char) : Re.any.mat cs = (cs.length == 1) := by rw [Re.mat]

theorem Re.mat_cat (a b : Re) (cs : List Char) :
    (Re.cat a b).mat cs = (List.range (cs.length + 1)).any fun i => a.mat (cs.take i) && b.mat (cs.drop i) := by
  rw [Re.mat]

theorem Re.mat_star_nil (a : Re) : (Re.star a).mat [] = true := by rw [Re.mat]

theorem Re.mat_star_cons (a : Re) (c : Char) (rest : List Char) :
    (Re.star a).mat (c :: rest) =
      (List.range (rest.length + 1)).any fun i => a.mat (c :: rest.take i) && (Re.star a).mat (rest.drop i) := by
  rw [Re.mat]

/-- A repeated class: every character is in it. -/
theorem Re.mat_star_cls (n : Bool) (rs : List (Char × Char)) (cs : List Char) :
    (Re.star (.cls n rs)).mat cs = cs.all fun c => inRanges rs c != n := by
  induction cs with
  | nil => simp [Re.mat_star_nil]
  | cons c rest ih =>
    rw [Re.mat_star_cons, List.all_cons, ← ih]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, _, h1, h2⟩
      rw [Re.mat_cls] at h1
      cases ht : rest.take i with
      | cons _ _ => simp [ht] at h1
      | nil =>
        simp only [ht] at h1
        have : rest.drop i = rest := by
          rcases List.take_eq_nil_iff.mp ht with h | h
          · simp [h]
          · simp [h]
        exact ⟨h1, this ▸ h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨0, by omega, by simpa [Re.mat_cls] using h1, by simpa using h2⟩

/-- `.*` matches everything. -/
theorem Re.mat_star_any (cs : List Char) : (Re.star .any).mat cs = true := by
  induction cs with
  | nil => simp [Re.mat_star_nil]
  | cons c rest ih =>
    rw [Re.mat_star_cons]
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    exact ⟨0, by omega, by simp [Re.mat_any], by simpa using ih⟩

/-- A class, then `r`: the first character is in the class. -/
theorem Re.mat_cat_cls (n : Bool) (rs : List (Char × Char)) (r : Re) (cs : List Char) :
    (Re.cat (.cls n rs) r).mat cs = match cs with
      | [] => false
      | c :: t => (inRanges rs c != n) && r.mat t := by
  rw [Re.mat_cat]
  cases cs with
  | nil => simp [Re.mat_cls]
  | cons c t =>
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, _, h1, h2⟩
      rw [Re.mat_cls] at h1
      match i, h1, h2 with
      | 1, h1, h2 => simp at h1 h2; exact ⟨by simpa using h1, h2⟩
      | 0, h1, _ => simp at h1
      | k + 2, h1, h2 =>
        cases t with
        | nil => simp at h1 h2; exact ⟨by simpa using h1, h2⟩
        | cons _ _ => simp at h1
    · rintro ⟨h1, h2⟩
      exact ⟨1, by simp, by simpa [Re.mat_cls] using h1, by simpa using h2⟩

/-- `.*`, then `r`: some suffix matches `r`. -/
theorem Re.mat_cat_star_any (r : Re) (cs : List Char) :
    (Re.cat (.star .any) r).mat cs = (List.range (cs.length + 1)).any fun i => r.mat (cs.drop i) := by
  rw [Re.mat_cat]
  simp [Re.mat_star_any]

/-! ### Matching by derivatives

`Re.mat` tries every split of the string, which takes time exponential in
the pattern's nesting. Compiled code matches by Brzozowski derivatives
instead, one character at a time (`Re.mat_eq_matchD`). -/

/-- Whether `r` matches the empty string. -/
def Re.nullable : Re → Bool
  | .none | .cls .. | .any => false
  | .str s => s.isEmpty
  | .union a b => a.nullable || b.nullable
  | .cat a b => a.nullable && b.nullable
  | .star _ => true

/-- `.cat a b`, or `.none` if either matches nothing. -/
def Re.cat' : Re → Re → Re
  | .none, _ | _, .none => .none
  | a, b => .cat a b

/-- `.union a b`, without an operand that matches nothing. -/
def Re.union' : Re → Re → Re
  | .none, b => b
  | a, .none => a
  | a, b => .union a b

/-- What `r` matches after the character `c`. -/
def Re.deriv (c : Char) : Re → Re
  | .none | .str [] => .none
  | .str (d :: s) => if c == d then .str s else .none
  | .cls neg rs => if inRanges rs c != neg then .str [] else .none
  | .any => .str []
  | .union a b => .union' (a.deriv c) (b.deriv c)
  | .cat a b => if a.nullable then .union' (.cat' (a.deriv c) b) (b.deriv c) else .cat' (a.deriv c) b
  | .star a => .cat' (a.deriv c) (.star a)

/-- Whether the whole of `cs` matches `r`, by derivatives. -/
def Re.matchD (r : Re) (cs : List Char) : Bool := (cs.foldl (fun r c => r.deriv c) r).nullable

theorem Re.mat_none (cs : List Char) : Re.none.mat cs = false := by rw [Re.mat]

theorem Re.mat_str (s cs : List Char) : (Re.str s).mat cs = (cs == s) := by rw [Re.mat]

theorem Re.mat_union (a b : Re) (cs : List Char) : (Re.union a b).mat cs = (a.mat cs || b.mat cs) := by
  rw [Re.mat]

theorem Re.mat_cat' (a b : Re) (cs : List Char) : (Re.cat' a b).mat cs = (Re.cat a b).mat cs := by
  unfold Re.cat'
  split <;> simp [Re.mat_cat, Re.mat_none]

theorem Re.mat_union' (a b : Re) (cs : List Char) : (Re.union' a b).mat cs = (a.mat cs || b.mat cs) := by
  unfold Re.union'
  split <;> simp [Re.mat_union, Re.mat_none]

theorem Re.nullable_eq (r : Re) : r.nullable = r.mat [] := by
  induction r with
  | none => simp [Re.nullable, Re.mat_none]
  | str s => cases s <;> simp [Re.nullable, Re.mat_str]
  | cls n rs => simp [Re.nullable, Re.mat_cls]
  | any => simp [Re.nullable, Re.mat_any]
  | union a b iha ihb => simp [Re.nullable, Re.mat_union, iha, ihb]
  | cat a b iha ihb => simp [Re.nullable, Re.mat_cat, iha, ihb]
  | star a => simp [Re.nullable, Re.mat_star_nil]

/-- A derivative matches what follows its character. -/
theorem Re.mat_deriv (c : Char) (r : Re) (cs : List Char) : (r.deriv c).mat cs = r.mat (c :: cs) := by
  induction r generalizing cs with
  | none => simp [Re.deriv, Re.mat_none]
  | str s =>
    cases s with
    | nil => simp [Re.deriv, Re.mat_none, Re.mat_str]
    | cons d s =>
      simp only [Re.deriv, Re.mat_str, List.cons_beq_cons]
      split <;> simp_all [Re.mat_none, Re.mat_str]
  | cls n rs =>
    simp only [Re.deriv, Re.mat_cls]
    split <;> cases cs <;> simp_all [Re.mat_none, Re.mat_str]
  | any => cases cs <;> simp [Re.deriv, Re.mat_any, Re.mat_str]
  | union a b iha ihb => simp [Re.deriv, Re.mat_union', Re.mat_union, iha, ihb]
  | cat a b iha ihb =>
    have split : (Re.cat a b).mat (c :: cs) = ((a.mat [] && b.mat (c :: cs)) ||
        (List.range (cs.length + 1)).any fun j => a.mat (c :: cs.take j) && b.mat (cs.drop j)) := by
      rw [Re.mat_cat, List.length_cons, List.range_succ_eq_map, List.any_cons, List.any_map]
      simp [Function.comp_def]
    rw [split, ← Re.nullable_eq, ← ihb]
    simp only [Re.deriv, ← iha]
    cases a.nullable <;> simp [Re.mat_union', Re.mat_cat', Re.mat_cat, Bool.or_comm]
  | star a ih => simp [Re.deriv, Re.mat_cat', Re.mat_cat, Re.mat_star_cons, ih]

theorem Re.mat_eq_matchD' (r : Re) (cs : List Char) : r.mat cs = r.matchD cs := by
  induction cs generalizing r with
  | nil => simp [Re.matchD, Re.nullable_eq]
  | cons c cs ih => rw [← Re.mat_deriv, ih]; rfl

@[csimp] theorem Re.mat_eq_matchD : @Re.mat = @Re.matchD := by
  funext r cs
  exact Re.mat_eq_matchD' r cs

/-- Whether the whole of `s` matches `r`. -/
def Re.matches (r : Re) (s : String) : Bool := r.mat s.toList

/-- `p` repeated `n` times. -/
def Re.pow (p : Re) : Nat → Re
  | 0 => .str []
  | n + 1 => .cat p (p.pow n)

/-- `p` repeated from `m` to `n` times. -/
def Re.loop (p : Re) (m n : Nat) : Re :=
  let opt := (List.range (n - m)).foldr (fun _ acc => .union (.str []) (.cat p acc)) (.str [])
  .cat (p.pow m) opt

/-- A pattern that does not parse, with the column of the problem in the
pattern. -/
structure ReError where
  column : Nat
  msg : Msg

/-- The characters that `\` escapes, and that are not literal unescaped. -/
def reSpecials : List Char := ['\\', '.', '[', ']', '(', ')', '*', '+', '?', '{', '}', '|', '^', '-']

def reErr (column : Nat) (headline label : String) (notes : Array String := #[]) : ReError :=
  { column, msg := { code? := some "F0117", headline := s!"invalid pattern: {headline}", label? := some label, notes } }

/-- A reversed range, `z-a` (`lang::char_range`). -/
def reversedRangeMsg (lo hi : Char) : Msg :=
  { code? := some "F0118", headline := s!"the range `{lo}-{hi}` in a pattern is reversed", label? := some "reversed range"
    notes := #[s!"note: a range is written from the lower character to the higher, as in `{hi}-{lo}`"] }

/-- Whether a range is accepted, from the code points of its ends
(`lang::char_range`). -/
def charRangeAccepted (low high : Int) : Bool := low ≤ high

/-- The parser's state: the pattern's characters and a position. -/
abbrev ReP := StateT Nat (Except ReError)

section
variable (cs : Array Char)

def rePeek : ReP (Option Char) := do return cs[← get]?

def reAdvance : ReP Unit := modify (· + 1)

/-- A character of a class, which `\` may escape. -/
def classChar : ReP Char := do
  match ← rePeek cs with
  | some '\\' =>
    reAdvance
    let some c ← rePeek cs | throw (reErr (← get) "a pattern cannot end with `\\`" "nothing to escape")
    reAdvance
    return c
  | some c => reAdvance; return c
  | none => throw (reErr (← get) "unclosed `[`" "expected `]`")

/-- A count of a repetition. -/
def reNum : ReP (Option Nat) := do
  let mut digits := ""
  while (← rePeek cs).any Char.isDigit do
    digits := digits.push (← rePeek cs).get!
    reAdvance
  return digits.toNat?

mutual
partial def reAlt : ReP Re := do
  let mut r ← reSeq
  while (← rePeek cs) == some '|' do
    reAdvance
    r := .union r (← reSeq)
  return r

partial def reSeq : ReP Re := do
  let mut parts : Array Re := #[]
  repeat
    match ← rePeek cs with
    | none | some '|' | some ')' => break
    | _ => parts := parts.push (← reRep)
  return parts.foldr (fun p acc => if acc == .str [] then p else .cat p acc) (.str [])

partial def reRep : ReP Re := do
  let mut a ← reAtom
  repeat
    match ← rePeek cs with
    | some '*' => reAdvance; a := .star a
    | some '+' => reAdvance; a := .cat a (.star a)
    | some '?' => reAdvance; a := .union (.str []) a
    | some '{' =>
      let start ← get
      reAdvance
      let some m ← reNum cs | throw (reErr start "expected a count after `{`" "expected a number")
      let n ← if (← rePeek cs) == some ',' then do
          reAdvance
          let some n ← reNum cs | throw (reErr start "expected a count after `,`" "expected a number")
          pure n
        else pure m
      unless (← rePeek cs) == some '}' do throw (reErr start "unterminated `{`" "expected `}`")
      reAdvance
      if n < m then throw (reErr start s!"`\{{m},{n}}` repeats at least {m} and at most {n} times" "fewer than at least")
      a := a.loop m n
    | _ => break
  return a

partial def reAtom : ReP Re := do
  let pos ← get
  match ← rePeek cs with
  | some '(' =>
    reAdvance
    let r ← reAlt
    unless (← rePeek cs) == some ')' do throw (reErr pos "unclosed `(`" "this `(` is not closed")
    reAdvance
    return r
  | some '[' =>
    reAdvance
    let neg := (← rePeek cs) == some '^'
    if neg then reAdvance
    let mut ranges : Array (Char × Char) := #[]
    repeat
      match ← rePeek cs with
      | none => throw (reErr pos "unclosed `[`" "this `[` is not closed")
      | some ']' => reAdvance; break
      | _ =>
        let lo ← classChar cs
        if (← rePeek cs) == some '-' && cs[(← get) + 1]? != some ']' then
          reAdvance
          let hi ← classChar cs
          unless charRangeAccepted lo.toNat hi.toNat do
            throw { column := pos, msg := reversedRangeMsg lo hi }
          ranges := ranges.push (lo, hi)
        else ranges := ranges.push (lo, lo)
    if ranges.isEmpty then throw (reErr pos "an empty class matches no character" "empty class")
    return .cls neg ranges.toList
  | some '.' => reAdvance; return .any
  | some '\\' =>
    reAdvance
    match ← rePeek cs with
    | some c =>
      unless reSpecials.contains c do
        throw (reErr pos s!"unknown escape `\\{c}`" "not an escape"
          #["note: `\\` escapes only `\\ . [ ] ( ) * + ? { } | ^ -`; there are no classes such as `\\d`",
            "help: write a class, such as `[0-9]`"])
      reAdvance
      return .str [c]
    | none => throw (reErr pos "a pattern cannot end with `\\`" "nothing to escape")
  | some c =>
    if ['*', '+', '?', '{'].contains c then
      throw (reErr pos s!"`{c}` repeats nothing" "nothing to repeat" #[s!"help: escape it to match it, as `\\{c}`"])
    if c == '^' then
      throw (reErr pos "patterns have no anchors" "not an anchor"
        #["note: the whole string must match, so `^` and `$` are not needed", "help: escape it to match it, as `\\^`"])
    if [']', '}', ')'].contains c then
      throw (reErr pos s!"unmatched `{c}`" "unmatched" #[s!"help: escape it to match it, as `\\{c}`"])
    reAdvance
    return .str [c]
  | none => throw (reErr pos "expected a pattern" "expected a pattern")
end

/-- The whole pattern. -/
def reTop : ReP Re := do
  let r ← reAlt cs
  if let some c ← rePeek cs then
    throw (reErr (← get) s!"unmatched `{c}`" "unmatched" #[s!"help: escape it to match it, as `\\{c}`"])
  return r

end

/-- Parses a pattern. -/
def parseRe (pat : String) : Except ReError Re := (reTop pat.toList.toArray).run' 0

/-- The code points from 0 to `maxChar` outside `rs`, as ranges. -/
def complementRanges (rs : List (Nat × Nat)) : List (Nat × Nat) := Id.run do
  let sorted := (rs.toArray.qsort fun a b => a.1 < b.1).toList
  let mut out := #[]
  let mut next := 0
  for (lo, hi) in sorted do
    if lo > next then out := out.push (next, lo - 1)
    next := max next (hi + 1)
  if next ≤ maxChar then out := out.push (next, maxChar)
  return out.toList

/-- `r` in SMT-LIB. -/
def Re.toSmt : Re → String
  | .none => "re.none"
  | .str cs => s!"(str.to_re {smtStringLit (String.ofList cs)})"
  | .cls neg rs =>
    -- Code points, since surrogates are characters of the solver's strings.
    let lit (n : Nat) := s!"\"\\u\{{String.ofList (Nat.toDigits 16 n)}}\""
    let one (r : Nat × Nat) := s!"(re.range {lit r.1} {lit r.2})"
    -- A negated class as the ranges between the class's: the solver
    -- decides ranges better than complements.
    let ranges := if neg then complementRanges (rs.map fun (lo, hi) => (lo.toNat, hi.toNat)) else rs.map fun (lo, hi) => (lo.toNat, hi.toNat)
    match ranges with
    | [] => "re.none"
    | [r] => one r
    | _ => s!"(re.union {" ".intercalate (ranges.map one)})"
  | .any => "re.allchar"
  | .union a b => s!"(re.union {a.toSmt} {b.toSmt})"
  | .cat a b => s!"(re.++ {a.toSmt} {b.toSmt})"
  | .star a => s!"(re.* {a.toSmt})"

end Fren.Core

namespace Fren.Str

/-- `s.matches?(p)`: whether the whole of `s` matches the pattern `p`; a
pattern that does not parse, which the front ends reject, matches nothing. -/
def «matches» (s p : String) : Bool :=
  match Fren.Core.parseRe p with
  | .ok r => r.matches s
  | .error _ => false

end Fren.Str
