-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Patterns
-- keep-sorted end

/-!
# Pattern types

The types as declared, with the pattern of each pattern type within them
(`Reqs/Lang/Types#pattern-types`), and what a value of such a type must
satisfy: the *constraint* that a variable, parameter or application of it
brings, and the *obligation* of a value given where it is declared. Both
front ends build a `PTy` for each declared type and call `PTy.cons` and
`PTy.obligation`, so that their constraints and obligations have the same
parts in the same order, and each renders a `Cons` in its own terms: Lean
propositions in the Lean-hosted front end, SMT-LIB in the `fren` command.
-/

namespace Fren.Core

open Lean (Name)

/-- A type as it is declared: `ty`, the type that the type checker sees,
without patterns; `pat?`, the pattern of the type itself, if it is a
pattern type; and `elems`, the same for each of its element types, one
for a set or a sequence, two for a relation, and none otherwise. -/
structure PTy where
  ty : Ty
  pat? : Option Pat := none
  elems : Array PTy := #[]
  /-- The type as written, for messages (`typeText`). -/
  text : String := ""
  deriving Inhabited

/-- `s`, as a type is shown in messages: with each run of whitespace one
space, so that both front ends show a type as written in the same way. -/
def typeText (s : String) : String :=
  let (words, last) := s.toList.foldl (init := (#[], "")) fun (ws, w) c =>
    if c.isWhitespace then (if w.isEmpty then (ws, w) else (ws.push w, "")) else (ws, w.push c)
  " ".intercalate (if last.isEmpty then words else words.push last).toList

/-- The declared type `t`, without patterns anywhere within it. -/
def PTy.plain (t : Ty) : PTy :=
  match t with
  | .set e | .seq e => { ty := t, elems := #[PTy.plain e] }
  | .rel a b => { ty := t, elems := #[PTy.plain a, PTy.plain b] }
  | _ => { ty := t }

/-- Whether the declared type `t` is ordered (`lang::ordered_type`): its
type without patterns is, a pattern type's base type or the type an alias
names (`Ty.ordered`). -/
def PTy.ordered (orderedDecl : Name → Bool) (t : PTy) : Bool := t.ty.ordered orderedDecl

/-- The position of the first of the declared types `ts`, a record's
fields or a newtype's underlying type, that is not ordered, if one is not
(`lang::ordered_declaration`). -/
def PTy.firstUnordered? (orderedDecl : Name → Bool) : List PTy → Option Nat
  | [] => none
  | t :: ts => if t.ordered orderedDecl then (PTy.firstUnordered? orderedDecl ts).map (· + 1) else some 0

/-- Whether `t` has a pattern, at the top or in an element type
(`lang::pattern_widening`). -/
partial def PTy.patterned (t : PTy) : Bool := t.pat?.isSome || t.elems.any (·.patterned)

/-- What a front end knows of a record's fields, of an enumeration's
variants' payloads, or of a newtype's field, for their constraints. -/
structure DataShape where
  /-- A record, or a newtype, rather than an enumeration. -/
  isRecord : Bool := false
  isNewtype : Bool := false
  /-- An enumeration that is recursive (`Reqs/Lang/Types#recursive-and-unbounded-types`). -/
  recursive : Bool := false
  /-- The types of the payload of each variant, or of the fields of the
  record's one constructor. -/
  parts : Array (Array PTy) := #[]
  deriving Inhabited

/-- What a value of a type must satisfy beyond its type, as a formula about
the value, built from parts (`Reqs/Lang/Types#meaning`). -/
inductive Cons where
  /-- The value, of type `base`, matches the pattern. -/
  | pat (base : Ty) (p : Pat)
  /-- The value, a `Nat` within a record or a payload, which is an `Int`
  there, is at least 0. -/
  | atLeast0
  /-- Each field of the record `path`, by its index, meets its constraint. -/
  | fields (path : Name) (cs : Array (Nat × Cons))
  /-- The newtype `path`'s field meets the constraint. -/
  | newtype (path : Name) (c : Cons)
  /-- When the value is the variant `v` of the enumeration `path`, the
  `k`th value of its payload meets the constraint: `(v, k, c)`. -/
  | payloads (path : Name) (cs : Array (Nat × Nat × Cons))
  /-- Each element of the set or sequence, of type `elem`, meets the
  constraint. -/
  | elems (seq : Bool) (elem : Ty) (c : Cons)
  /-- Each pair of the relation, of types `a` and `b`, meets the
  constraints of its two members. -/
  | pairs (a b : Ty) (ca cb : Option Cons)
  /-- All of them, in order. -/
  | all (cs : Array Cons)
  deriving Inhabited

/-- Whether the constraint quantifies over the elements of a collection
(`lang::pattern_place`). -/
partial def Cons.quantifies : Cons → Bool
  | .pat .. | .atLeast0 => false
  | .fields _ cs => cs.any (·.2.quantifies)
  | .newtype _ c => c.quantifies
  | .payloads _ cs => cs.any (·.2.2.quantifies)
  | .elems .. | .pairs .. => true
  | .all cs => cs.any (·.quantifies)

/-- `cs`, as one constraint, `none` if there are none. -/
def Cons.allOf? (cs : Array Cons) : Option Cons :=
  if cs.isEmpty then none else if cs.size == 1 then cs[0]? else some (.all cs)

mutual
/-- The constraint that a value of the declared type `t` brings, `none` if
it brings none (`Reqs/Lang/Types#meaning`): its pattern; that a `Nat` is at
least 0, where `nat` says that one brings that here, which it does within
a record or a payload, where it is an `Int`; the constraints of a record's
fields, a newtype's field, and an enumeration's payloads, guarded by their
variants, unless the enumeration is recursive, whose payloads bring theirs
where they are read (`PTy.readCons`); and those of a collection's elements,
for every element. `shapes` gives what is known of each record and
enumeration. -/
partial def PTy.cons (shapes : Name → Option DataShape) (t : PTy) (nat : Bool := false) : Option Cons :=
  let own : Array Cons := match t.ty with
    | .nat => if nat then #[.atLeast0] else #[]
    | .record p | .enum p => (dataCons shapes p).toArray
    | .newtype p _ => (dataCons shapes p).toArray
    | .set e | .seq e =>
      ((t.elems[0]?.getD (PTy.plain e)).cons shapes true).toArray.map (.elems (t.ty matches .seq _) e)
    | .rel a b =>
      let ca := (t.elems[0]?.getD (PTy.plain a)).cons shapes true
      let cb := (t.elems[1]?.getD (PTy.plain b)).cons shapes true
      if ca.isNone && cb.isNone then #[] else #[.pairs a b ca cb]
    | _ => #[]
  Cons.allOf? (own ++ (t.pat?.map (.pat t.ty)).toArray)

/-- The constraints of the fields or payloads of the record, newtype or
enumeration `p`, which is not recursive. -/
partial def dataCons (shapes : Name → Option DataShape) (p : Name) : Option Cons := do
  let d ← shapes p
  if d.recursive then none
  if d.isNewtype then
    let c ← (d.parts[0]?.bind (·[0]?)).bind (·.cons shapes true)
    return .newtype p c
  if d.isRecord then
    let cs := ((d.parts[0]?.getD #[]).zipIdx.filterMap fun (f, k) => (f.cons shapes true).map (k, ·))
    if cs.isEmpty then none else return .fields p cs
  let cs := d.parts.zipIdx.flatMap fun (ts, v) => ts.zipIdx.filterMap fun (t, k) => (t.cons shapes true).map (v, k, ·)
  if cs.isEmpty then none else return .payloads p cs
end

/-- The constraint that the `k`th value of the payload of the variant `v`
of the recursive enumeration `p` brings where it is read, of the value
read (`Reqs/Lang/Types#meaning`). A selector of another variant reads a
value that nothing determines, so the constraint holds of it too. -/
def readCons (shapes : Name → Option DataShape) (p : Name) (v k : Nat) : Option Cons := do
  let d ← shapes p
  unless d.recursive do none
  let t ← (d.parts[v]?).bind (·[k]?)
  t.cons shapes true

/-- The obligation of a value of type `ty`, of the pattern `top?`, if it
is a pattern type, whose element types' obligations are `e1?` and, for a
relation, `e2?` (`lang::obligation`): that it matches its pattern, and
that each element, or each pair's members, meets theirs. -/
def obligationCons (ty : Ty) (top? : Option Pat) (e1? e2? : Option Cons) : Option Cons :=
  let own : Array Cons := match ty with
    | .set e | .seq e => (e1?.map (.elems (ty matches .seq _) e)).toArray
    | .rel a b => if e1?.isNone && e2?.isNone then #[] else #[.pairs a b e1? e2?]
    | _ => #[]
  Cons.allOf? (own ++ (top?.map (.pat ty)).toArray)

/-- The obligation of a value given where the type `t` is declared, `none`
if it has none (`lang::pattern_widening`, `lang::obligation`): its
pattern, and its elements' patterns, for every element. A record's or an
enumeration's own constraints need no obligation: its values were built to
meet them. -/
partial def PTy.obligation (t : PTy) : Option Cons :=
  obligationCons t.ty t.pat? (t.elems[0]?.bind (·.obligation)) (t.elems[1]?.bind (·.obligation))

/-- Where a value is given for a declared type (`lang::ValuePlace`). -/
inductive ValuePlace where
  | definition
  | argument
  | field
  | payload
  /-- A newtype's constructor's argument. -/
  | construction
  /-- A typed `let` or `where` definition. -/
  | letDefinition
  /-- A defined function's body. -/
  | body
  | constant
  /-- An instance's binding, which the instance check asks instead. -/
  | binding
  deriving Inhabited, DecidableEq, Repr

/-- The obligation of a value given at `place` where the type `t` is
declared, `none` if it has none there (`lang::obligation`). -/
def siteObligation (place : ValuePlace) (o? : Option Cons) : Option Cons :=
  if place == .binding then none else o?

/-! ## Finite pattern types -/

/-- The integers that the pattern `p` matches, in increasing order, if they
are finitely many: every alternative is a bounded range or an integer
(`lang::pattern_finite`). -/
partial def Pat.intValues? : Pat → Option (Array Int)
  | .int (some lo) (some hi) =>
    some ((List.range (hi - lo + 1).toNat).toArray.map fun (i : Nat) => lo + (i : Int))
  | .or alts => do
    let vs ← alts.mapM Pat.intValues?
    let all := (vs.flatMap id).qsort (· < ·)
    return all.foldl (init := #[]) fun acc v => if acc.back? == some v then acc else acc.push v
  | _ => none

/-- Whether a pattern type is finite, from whether its base type is,
whether that is `Int` or `Nat`, and whether its pattern bounds it
(`lang::pattern_finite`). -/
def patternFinite (baseFinite integers bounded : Bool) : Bool := baseFinite || (integers && bounded)

/-- Where a pattern type is written (`lang::pattern_place`). -/
inductive PatternPlace where
  /-- At the top of a declared type. -/
  | top
  | field
  | payload
  | element
  deriving Inhabited, DecidableEq, Repr

/-- Whether a pattern type written at `place` is in the decidable core,
where `recursive` says whether a payload's enumeration is recursive
(`lang::pattern_place`). -/
def patternPlaceDecidable (place : PatternPlace) (recursive : Bool) : Bool :=
  !(place == .element || (place == .payload && recursive))

/-- Whether a value is accepted where a type is declared, and whether it
has an obligation, from whether `widening` accepts the types without their
patterns and whether the declared type has a pattern
(`lang::pattern_widening`). -/
def patternWidening (widened patterned : Bool) : Bool × Bool := (widened, widened && patterned)

/-! ## Messages -/

/-- An element type whose values bring a constraint, which holds of every
element (`lang::pattern_place`). -/
def undecidableElementsMsg : Msg :=
  { code? := some "F0714", headline := "this is outside the decidable core: the constraint of an element type holds of every element, which quantifies over them"
    label? := some "outside the decidable core"
    notes := #["help: give the element type no pattern, and say of the elements that the spec reads what it needs"] }

/-- A pattern type as a payload of a recursive enumeration, whose
constraint holds of every payload, at every depth (`lang::pattern_place`). -/
def undecidableRecursivePayloadMsg : Msg :=
  { code? := some "F0714", headline := "this is outside the decidable core: a recursive enumeration's payload's constraint holds of every payload, at every depth"
    label? := some "outside the decidable core"
    notes := #["help: give the payload no pattern, and say of the payloads that the spec reads what it needs"] }

/-- A pattern on the type alias `alias`, which names a pattern type
(`Reqs/Lang/Types#pattern-types`). -/
def nestedAliasMsg (alias : String) : Msg :=
  { code? := some "F0369", headline := s!"`{alias}` is a pattern type, so it cannot have a pattern of its own"
    label? := some "already a pattern type"
    notes := #["note: pattern types are not nested: the base type of `T is P` is never itself a pattern type",
      "help: write one pattern type, whose pattern matches what both patterns do"] }

/-- A second `is` after a pattern type, which the grammar excludes. -/
def nestedPatternMsg : Msg :=
  { code? := some "F0137", headline := "a pattern type cannot have a second pattern"
    label? := some "a second `is`"
    notes := #["note: pattern types are not nested: the base type of `T is P` is never itself a pattern type",
      "help: write one pattern, which matches what both patterns do"] }

/-- A binder `x` in a pattern type's pattern, which binds no names
(`Reqs/Lang/Types#pattern-types`). -/
def patternTypeBinderMsg (x : Name) : Msg :=
  let x := binderName x
  { code? := some "F0370", headline := s!"a pattern type's pattern cannot bind `{x}`"
    label? := some "binds a name"
    notes := #["note: a pattern type's pattern binds no names, and a name here would match every value",
      "help: write `_` to match every value, or a variant's or a constant's path"] }

/-- The headline of a failed obligation: a value in `subject` that may not
be a value of the declared type `ty`. -/
def obligationHeadline (subject ty : String) : String := s!"a value in {subject} may not have the type `{ty}`"

/-- The messages of a failed obligation, with the counterexample `cex`. -/
def obligationMsg (subject ty cex : String) (priv : Array String) : Msg :=
  { code? := some "F0622", headline := obligationHeadline subject ty, label? := some s!"may not have the type `{ty}`"
    notes := #[s!"counterexample: {cex}"] ++ priv ++
      #["note: a value given where a pattern type is declared must match its pattern",
        "help: guard the value with a condition that makes it match, or add an assumption that ensures it"] }

/-- The message of an instance's binding of the input `x` of `sub`, whose
type `ty` its value may not have, with the counterexample `cex`. -/
def instanceTypeMsg (subject sub x ty cex : String) : Msg :=
  { code? := some "F0623", headline := s!"the input `{x}` of `{sub}` may not have its type `{ty}` for instance {subject}"
    label? := some s!"may not have the type `{ty}`"
    notes := #[s!"counterexample: {cex}",
      s!"note: `{sub}` assumes that `{x}` has the type `{ty}`",
      "help: bind the input to a value of its type, or add an `assume` that guarantees it"] }

end Fren.Core

namespace Fren.Core

open Lean (Name)

/-! ## The values of a finite type -/

/-- A value of a type that a quantifier ranges over, as both front ends
list them (`Reqs/Lang/Quantifiers#meaning`): a `Bool`, an integer, or a
variant, the `idx`th of an enumeration, or a record's or newtype's one
constructor, with its payload's or fields' values. -/
inductive PVal where
  | bool (b : Bool)
  | int (i : Int)
  | ctor (idx : Nat) (args : Array PVal)
  deriving Inhabited, BEq

/-- Whether the integer `x` is in the range from `lo` to `hi`, both
included, where `none` is unbounded (`lang::pattern_member`). -/
def intervalHolds (lo hi : Option Int) (x : Int) : Bool := lo.all (· ≤ x) && hi.all (x ≤ ·)

/-- Whether the integer `x` is in one of the ranges `ivs`: whether an
integer pattern of those alternatives matches it (`lang::pattern_member`). -/
def intervalsHold (ivs : List (Option Int × Option Int)) (x : Int) : Bool :=
  ivs.any fun (lo, hi) => intervalHolds lo hi x

/-- The first of the ranges `ivs` that `x` is in, if any. -/
def intervalIndex? : List (Option Int × Option Int) → Int → Option Nat
  | [], _ => none
  | (lo, hi) :: rest, x => if intervalHolds lo hi x then some 0 else (intervalIndex? rest x).map (· + 1)

/-- `acc`, intervals in increasing order, none of which overlap or touch,
with the nonempty interval `(lo, hi)` added: merged with those it
overlaps or touches. -/
def addInterval : List (Int × Int) → Int × Int → List (Int × Int)
  | [], iv => [iv]
  | (l, h) :: rest, (lo, hi) =>
    if hi + 1 < l then (lo, hi) :: (l, h) :: rest
    else if h + 1 < lo then (l, h) :: addInterval rest (lo, hi)
    else addInterval rest (min l lo, max h hi)

/-- Whether the ranges `ivs` match finitely many integers: each is
bounded on both sides, or empty (`lang::pattern_count`). -/
def intervalsFinite (ivs : List (Option Int × Option Int)) : Bool :=
  ivs.all fun
    | (some _, some _) => true
    | _ => false

/-- `acc` with the bounded range `iv` added, if it is nonempty. -/
def mergeInterval (acc : List (Int × Int)) : Option Int × Option Int → List (Int × Int)
  | (some lo, some hi) => if lo ≤ hi then addInterval acc (lo, hi) else acc
  | _ => acc

/-- The bounded ranges of `ivs`, merged into intervals in increasing order
that neither overlap nor touch. -/
def mergeIntervals (ivs : List (Option Int × Option Int)) : List (Int × Int) := ivs.foldl mergeInterval []

/-- How many integers the intervals `ivs` have together, if they do not
overlap. -/
def totalWidth (ivs : List (Int × Int)) : Nat := ivs.foldl (fun n iv => n + (iv.2 - iv.1 + 1).toNat) 0

/-- How many integers the ranges `ivs` match, if finitely many, counted
from their bounds, by merging them, without listing the integers
(`lang::pattern_count`). -/
def intervalsCount? (ivs : List (Option Int × Option Int)) : Option Nat :=
  if intervalsFinite ivs then some (totalWidth (mergeIntervals ivs)) else none

/-- The ranges of the alternatives of the integer pattern `p`, if it is
one: a range, an integer, or an or-pattern of them. -/
partial def Pat.ranges? : Pat → Option (List (Option Int × Option Int))
  | .int lo hi => some [(lo, hi)]
  | .or alts => do return (← alts.toList.mapM Pat.ranges?).flatten
  | _ => none

/-- How many integers at least `low` the pattern `p` matches, if finitely
many, counted from its bounds without listing them
(`lang::pattern_finite`, `lang::pattern_count`). -/
def Pat.intCount? (p : Pat) (low : Option Int := none) : Option Nat := do
  let ivs := (← p.ranges?).map fun (lo, hi) =>
    match low, lo with
    | some l, some lo => (some (max lo l), hi)
    | some l, none => (some l, hi)
    | none, lo => (lo, hi)
  intervalsCount? ivs

/-- The bounds of the ranges and the integers of the pattern `p`. -/
partial def Pat.bounds : Pat → Array Int
  | .int lo hi => lo.toArray ++ hi.toArray
  | .ctor _ ps | .or ps => ps.flatMap Pat.bounds
  | _ => #[]

/-- Whether the pattern `p` matches the value `v`. -/
partial def Pat.matchesVal (p : Pat) (v : PVal) : Bool :=
  match p, v with
  | .wild _, _ => true
  | .bool b, .bool c => b == c
  | .int lo hi, .int i => intervalHolds lo hi i
  | .ctor i args, .ctor j vs => i == j && args.size == vs.size && (args.zip vs).all fun (a, w) => a.matchesVal w
  | .or alts, v => alts.any (·.matchesVal v)
  | _, _ => false

/-- The values of the declared type `t`, in order, if a quantifier ranges
over it and it has at most `cap` of them: those of its base type that match
its pattern, an integer type's when its pattern bounds it
(`lang::pattern_finite`), and a record's, newtype's or enumeration's by
their parts' values, the last part varying fastest. `shapes` gives what is
known of each record, newtype and enumeration. -/
partial def PTy.values (shapes : Name → Option DataShape) (t : PTy) (cap : Nat := 64) : Option (Array PVal) := do
  let base : Array PVal ← match t.ty with
    | .bool => some #[.bool true, .bool false]
    | .int | .nat => do
      -- Counted first, so that a wide range is never listed.
      let n ← t.pat?.bind (·.intCount? (if t.ty == .nat then some 0 else none))
      if n > cap then none
      let vs ← t.pat?.bind Pat.intValues?
      some ((if t.ty == .nat then vs.filter (0 ≤ ·) else vs).map .int)
    | .enum p | .record p | .newtype p _ => do
      let d ← shapes p
      if d.recursive then none
      let mut out := #[]
      for parts in d.parts, idx in [0:d.parts.size] do
        let mut combos : Array (Array PVal) := #[#[]]
        for part in parts do
          let vs ← part.values shapes cap
          combos := combos.flatMap fun pre => vs.map pre.push
          if combos.size > cap then none
        out := out ++ combos.map (.ctor idx)
        if out.size > cap then none
      some out
    | _ => none
  let vs := match t.pat? with
    | some p => if t.ty matches .int | .nat then base else base.filter p.matchesVal
    | none => base
  if vs.size > cap then none
  return vs

/-- How many values the declared type `t` has, if a quantifier ranges over
it (`lang::pattern_finite`): an integer type's counted from its pattern's
bounds, and any other's from its values, if there are at most `cap` of
them, or else from its parts, without its pattern. -/
partial def PTy.count? (shapes : Name → Option DataShape) (t : PTy) (cap : Nat := 100000) : Option Nat :=
  match t.ty with
  | .int | .nat => t.pat?.bind (·.intCount? (if t.ty == .nat then some 0 else none))
  | _ => match t.values shapes cap with
    | some vs => some vs.size
    | none => do
      match t.ty with
      | .bool => some 2
      | .enum p | .record p | .newtype p _ =>
        let d ← shapes p
        if d.recursive then none
        let counts ← d.parts.mapM fun parts => parts.mapM (·.count? shapes cap)
        some (counts.foldl (fun n cs => n + cs.foldl (· * ·) 1) 0)
      | _ => none

end Fren.Core
