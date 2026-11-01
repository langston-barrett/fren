-- keep-sorted start
import FrenCore.Check
import FrenCore.Evidence
import FrenCore.SubsetTypes
-- keep-sorted end

/-!
# Checking by enumeration (`Reqs/Check#checking-by-enumeration`)

A size-ordered enumerator of values, in the style of SmallCheck: each type
is unfolded, for a size bound `n`, into a `Shape`, a finite tree, whose
values of size at most `n` `Shape.vals` lists, each once, and `Shape.ordered`
lists smallest first. A procedure's checks are then decided by the shared
check algorithms (`Fren.Core.checkComp`) with a backend (`backend`) that
answers each query by searching the assignments of its variables, smallest
first and fairly (`search`): by the largest size of a variable's value, then
in the order of the variables and of each one's values. The formulas are
`EF`s, over *atoms*, the formulas of the procedure, which each front end
evaluates in its own terms: the `fren` command with its evaluator, and the
Lean-hosted front end by Lean's evaluation of the generated propositions.
So the two front ends ask the same queries, search them in the same order
and report the same first model.
-/

namespace Fren.Core.Enumeration

open Lean (Name)

/-! ## Values and shapes -/

/-- A value as the enumerator builds it: a `Bool`, an integer, the `k`th
value of an abstract type, a string, a set by its members, a sequence by
its elements, a pair of a relation, or the variant `idx` of an
enumeration, with its payload, or a record or newtype, as its one
constructor `0`, with its fields. A set's members are distinct, in
increasing `EVal.code` (`membersOrdered`), as `Shape.vals` and
`Shape.random` give them. -/
inductive EVal where
  | bool (b : Bool)
  | int (i : Int)
  | abs (k : Nat)
  | str (s : String)
  | set (members : List EVal)
  | seq (elems : List EVal)
  | pair (a b : EVal)
  | ctor (idx : Nat) (args : List EVal)
  deriving Inhabited, Repr, BEq

/-- A code of the value, by which a set's members are ordered: their codes
increase, in the lexicographic order of lists of integers. -/
partial def EVal.code : EVal → List Int
  | .bool b => [0, if b then 1 else 0]
  | .int i => [1, i]
  | .abs k => [2, (k : Int)]
  | .str s => [3, (s.length : Int)] ++ s.toList.map fun c => (c.toNat : Int)
  | .set ms => [4, (ms.length : Int)] ++ ms.flatMap EVal.code
  | .seq vs => [5, (vs.length : Int)] ++ vs.flatMap EVal.code
  | .pair a b => [6] ++ a.code ++ b.code
  | .ctor idx args => [7, (idx : Int), (args.length : Int)] ++ args.flatMap EVal.code

/-- Whether the values `vs` are a set's members as `EVal.set` has them:
their codes strictly increase. -/
def membersOrdered (vs : List EVal) : Bool := decide (vs.Pairwise (·.code < ·.code))

/-- The value as a value of a pattern, if it has no abstract value in it. -/
partial def EVal.toPVal? : EVal → Option PVal
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .abs _ | .str _ | .set _ | .seq _ | .pair .. => none
  | .ctor idx args => do return .ctor idx (← args.mapM EVal.toPVal?).toArray

/-- Whether a declared constraint needs semantic evaluation beyond Shape's
literal-pattern filters. Function-result tables with such constraints require
an additional world filter; frontends must not silently use unconstrained tables. -/
partial def needsSemanticFilter (shapeOf : Name → Option DataShape) (t : PTy) (seen : List Name := []) : Bool :=
  let own := !t.invariants.isEmpty && (t.invariants.size != 1 || t.pat?.isNone)
  let nested := t.elems.any (needsSemanticFilter shapeOf · seen)
  let fields := match t.ty with
    | .record path _ | .enum path _ | .newtype path _ =>
      !seen.contains path && ((shapeOf path).any fun shape => (shape.inst t.parts).parts.any
        (·.any (needsSemanticFilter shapeOf · (path :: seen))))
    | _ => false
  own || nested || fields

mutual
/-- A type, unfolded for a size bound: a finite tree, whose recursive
enumerations are unfolded as deep as the bound allows
(`Reqs/Check#sizes-and-order`). -/
inductive Shape where
  | bool
  /-- `Int`: `i` has size `|i|`. -/
  | int
  /-- `Nat`: `k` has size `k`. -/
  | nat
  /-- `String`: the largest of its length and its characters' sizes, the
  character with code point `c` having size `c + 1`. -/
  | string
  /-- A sequence: the largest of its length and its elements' sizes. -/
  | seq (elem : Shape)
  /-- A set: the largest of its cardinality and its members' sizes. -/
  | set (elem : Shape)
  /-- A pair of a relation: the larger of its two values' sizes. -/
  | pair (a b : Shape)
  /-- A finite integer subset type: its integers, in increasing order, each
  of size 0. -/
  | ints (vs : List Int)
  /-- An abstract type: its `k`th value has size `k`. -/
  | abstract
  /-- An enumeration: a variant without a payload has size 0, and one with
  a payload one more than the largest of its values'. -/
  | ctors (cs : Ctors)
  /-- A record, or a newtype: the largest size of its fields. -/
  | record (fs : Shapes)
  /-- A subset type of the shape `s`: its values that `keep` keeps. -/
  | filter (s : Shape) (keep : EVal → Bool)
  /-- No values: a payload beyond the bound. -/
  | empty

/-- The shapes of a payload's values, or of a record's fields. -/
inductive Shapes where
  | nil
  | cons (s : Shape) (rest : Shapes)

/-- The variants of an enumeration, each with the shapes of its payload. -/
inductive Ctors where
  | nil
  | cons (payload : Shapes) (rest : Ctors)
end

instance : Inhabited Shape := ⟨.empty⟩

/-- The product of `xs` and `rest`, the first varying slowest, with the
largest of the sizes. -/
def prodWith (xs : List (EVal × Nat)) (rest : List (List EVal × Nat)) : List (List EVal × Nat) :=
  xs.flatMap fun (v, k) => rest.map fun (vs, l) => (v :: vs, max k l)

/-- What kind of value a size is of (`check::value_size`). -/
inductive SizeKind where
  | bool
  | int
  | nat
  /-- An integer of a finite integer subset type. -/
  | finiteInt
  | abstract
  /-- A variant without a payload. -/
  | nullary
  /-- A variant with a payload. -/
  | variant
  /-- A record or a newtype. -/
  | record
  /-- A character, by its code point. -/
  | char
  /-- A string, a sequence or a set, by its length or cardinality. -/
  | collection
  /-- A pair, a member of a relation. -/
  | pair
  deriving Inhabited, BEq, DecidableEq, Repr

/-- How many code points there are, valid or not. -/
def codePoints : Nat := 0x110000

/-- The size of the character with code point `c`: one more than its
distance from `a`, wrapping around, so that `a` is 1, `b` 2, ..., `z` 26,
`{` 27, and the characters below `a` come last. -/
def charSize (c : Nat) : Nat := (c + codePoints - 'a'.toNat) % codePoints + 1

/-- The size of a value (`check::value_size`): of an integer `i`, its
magnitude, and of a `Nat` or the `i`th value of an abstract type, `i`;
of a variant with a payload, one more than `largest`, the largest of its
payload's values' sizes, of a record, `largest`, its fields', and of a
pair, `largest`, its two values'; of a character with code point `c`,
`charSize c`; of a string, a sequence or a set of length `len`, the larger
of `len` and `largest`; and of anything else 0. -/
def valueSize : SizeKind → Int → Nat → Nat
  | .int, i, _ => i.natAbs
  | .nat, i, _ => i.toNat
  | .abstract, i, _ => i.toNat
  | .variant, _, largest => largest + 1
  | .record, _, largest | .pair, _, largest => largest
  | .char, c, _ => charSize c.toNat
  | .collection, len, largest => max len.toNat largest
  | _, _, _ => 0

/-- The integers of size at most `n`, by size: `0, 1, -1, 2, -2, ...`. -/
def intsUpTo (n : Nat) : List Int :=
  (List.range (n + 1)).flatMap fun (k : Nat) => if k = 0 then [(0 : Int)] else [(k : Int), -(k : Int)]

/-- The lists of exactly `length` values of `vs`, each with the largest of
their sizes, the first varying slowest: a sequence's elements, or a
string's characters. -/
def listsOf {α : Type} (vs : List (α × Nat)) : Nat → List (List α × Nat)
  | 0 => [([], 0)]
  | len + 1 => vs.flatMap fun (v, k) => (listsOf vs len).map fun (ws, l) => (v :: ws, max k l)

/-- The sublists of `vs` of at most `card` values, each with the largest of
their sizes: each value's presence before its absence, the first varying
slowest, so that among sets of a size they are in lexicographic order. -/
def subsetsOf : List (EVal × Nat) → Nat → List (List EVal × Nat)
  | [], _ => [([], 0)]
  | (_ :: rest), 0 => subsetsOf rest 0
  | ((v, k) :: rest), card + 1 =>
    (subsetsOf rest card).map (fun (vs, l) => (v :: vs, max k l)) ++ subsetsOf rest (card + 1)

/-- The characters of size at most `n` (`charSize`), smallest first. -/
def charsUpTo (n : Nat) : List (Char × Nat) :=
  (List.range (min n codePoints)).filterMap fun r =>
    let c := (r + 'a'.toNat) % codePoints
    if c.isValidChar then some (Char.ofNat c, r + 1) else none

mutual
/-- Every value of `s` of size at most `n`, each with its size, once, in
the structural order: variants in order, and payloads and fields by their
values' order, the first varying slowest (`Reqs/Check#sizes-and-order`). -/
def Shape.vals : Shape → Nat → List (EVal × Nat)
  | .bool, _ => [(.bool false, valueSize .bool 0 0), (.bool true, valueSize .bool 1 0)]
  | .int, n => (intsUpTo n).map fun i => (.int i, valueSize .int i 0)
  | .nat, n => (List.range (n + 1)).map fun (k : Nat) => (.int (k : Int), valueSize .nat k 0)
  | .ints vs, _ => vs.map fun i => (.int i, valueSize .finiteInt i 0)
  | .string, n => (List.range (n + 1)).flatMap fun len =>
    (listsOf (charsUpTo n) len).map fun (w, k) => (.str (String.ofList w), max len k)
  | .seq e, n => (List.range (n + 1)).flatMap fun len =>
    (listsOf (e.vals n) len).map fun (vs, k) => (.seq vs, max len k)
  | .set e, n => ((subsetsOf ((e.vals n).mergeSort fun a b => a.1.code ≤ b.1.code) n).filter
      fun (vs, _) => membersOrdered vs).map fun (vs, k) => (.set vs, max vs.length k)
  | .pair a b, n => (a.vals n).flatMap fun (x, k) => (b.vals n).map fun (y, l) => (.pair x y, max k l)
  | .abstract, n => (List.range (n + 1)).map fun (k : Nat) => (.abs k, valueSize .abstract k 0)
  | .ctors cs, n => cs.vals 0 n
  | .record fs, n => (fs.vals n).map fun (vs, k) => (.ctor 0 vs, valueSize .record 0 k)
  | .filter s keep, n => (s.vals n).filter fun (v, _) => keep v
  | .empty, _ => []

/-- Every combination of values of `ss` of sizes at most `n`, with the
largest of their sizes. -/
def Shapes.vals : Shapes → Nat → List (List EVal × Nat)
  | .nil, _ => [([], 0)]
  | .cons s rest, n => prodWith (s.vals n) (rest.vals n)

/-- Every value of the variants `cs`, the first numbered `i`, of size at
most `n`. -/
def Ctors.vals : Ctors → Nat → Nat → List (EVal × Nat)
  | .nil, _, _ => []
  | .cons .nil rest, i, n => (.ctor i [], valueSize .nullary i 0) :: rest.vals (i + 1) n
  | .cons ps rest, i, n =>
    (match n with
      | 0 => []
      | m + 1 => (ps.vals m).map fun (vs, k) => (.ctor i vs, valueSize .variant i k)) ++ rest.vals (i + 1) n
end

/-- Every value of `s` of size at most `n`, smallest first, and in the
structural order among those of a size (`Reqs/Check#sizes-and-order`). -/
def Shape.ordered (s : Shape) (n : Nat) : List (EVal × Nat) :=
  let vs := s.vals n
  (List.range (n + 1)).flatMap fun k => vs.filter (·.2 == k)

mutual
/-- Whether every value of `s` has size at most `n`, so that `Shape.vals`
lists every value of the type it stands for: `s` has no value of size
`n + 1`, being finite, and, if it was unfolded for the bound `n`, no
variant was cut off. -/
def Shape.exhausted : Shape → Nat → Bool
  | .bool, _ | .ints _, _ | .empty, _ => true
  | .int, _ | .nat, _ | .abstract, _ | .string, _ => false
  -- A sequence of any length but none has a value of every size, so only
  -- one whose elements have no value at all is exhausted.
  | .seq e, n => (e.vals n).isEmpty && e.exhausted n
  -- Every set of `e`'s values is within the bound when they all are, and
  -- there are at most `n` of them.
  | .set e, n => e.exhausted n && (e.vals n).length ≤ n
  | .pair a b, n => a.exhausted n && b.exhausted n
  | .ctors cs, n => cs.exhausted n
  | .record fs, n => fs.exhausted n
  | .filter s _, n => s.exhausted n

def Shapes.exhausted : Shapes → Nat → Bool
  | .nil, _ => true
  | .cons s rest, n => s.exhausted n && rest.exhausted n

def Ctors.exhausted : Ctors → Nat → Bool
  | .nil, _ => true
  | .cons .nil rest, n => rest.exhausted n
  | .cons ps rest, n => (match n with | 0 => false | m + 1 => ps.exhausted m) && rest.exhausted n
end

/-! ## Shapes of declared types -/

/-- Why a type cannot be enumerated (`Reqs/Check#enumerable-types`). -/
def notEnumerable (t : PTy) : String :=
  s!"`{if t.text.isEmpty then t.ty.show else t.text}`"

/-- Whether the pattern `p` matches the value `v`, over every kind of value
(`Pat.matchesVal` over the values that patterns have). A value of a kind
that `p` does not describe does not match it. -/
partial def matchesEVal : Pat → EVal → Bool
  | .wild _, _ => true
  | .bool b, .bool c => b == c
  | .int lo hi, .int i => intervalHolds lo hi i
  | .str s, .str t => s == t
  | .ctor i ps, .ctor j vs => i == j && ps.size == vs.length && (ps.toList.zip vs).all fun (p, v) => matchesEVal p v
  | .or alts, v => alts.any (matchesEVal · v)
  | _, _ => false

/-- The shape of the declared type `t` for the bound `n`
(`Reqs/Check#enumerable-types`): every declared type has one: `Bool`,
`Int`, `Nat`, `String`, sets, relations, sequences, enumerations, records,
newtypes, instances of generic types, subset types and abstract types.
`shapes` gives what is known of each record, newtype and enumeration. A
recursive enumeration is unfolded `n` deep. -/
partial def shapeOf (shapes : Name → Option DataShape) (n : Nat) (t : PTy) : Except String Shape := do
  let keep (p : Pat) : EVal → Bool := matchesEVal p
  let elem (i : Nat) (e : Ty) : Except String Shape := shapeOf shapes n (t.elems[i]?.getD (PTy.plain e))
  let base : Shape ← match t.ty with
    | .bool => pure .bool
    | .int | .nat =>
      let nat := t.ty == .nat
      match t.pat? with
      | none => pure (if nat then .nat else .int)
      | some p =>
        -- A finite integer subset type: all of its integers, of size 0.
        match p.intCount? (if nat then some 0 else none), Pat.intValues? p with
        | some _, some vs => return .ints (vs.toList.filter fun i => !nat || 0 ≤ i)
        -- A `Nat` pattern bounded only above, as `Nat is ..=5`: from 0 to
        -- its largest bound.
        | some _, none =>
          let top := (p.bounds.foldl max 0).toNat
          return .ints (((List.range (top + 1)).map fun (k : Nat) => (k : Int)).filter fun i => p.matchesVal (.int i))
        | _, _ => pure (if nat then .nat else .int)
    | .string => pure .string
    | .seq e => pure (.seq (← elem 0 e))
    | .set e => pure (.set (← elem 0 e))
    | .rel a b => pure (.set (.pair (← elem 0 a) (← elem 1 b)))
    | .abstract _ => pure .abstract
    | .enum p _ | .record p _ | .newtype p _ =>
      let some d := shapes p | throw (notEnumerable t)
      let d := d.inst t.parts
      let parts (m : Nat) (ts : Array PTy) : Except String Shapes :=
        ts.toList.foldrM (init := .nil) fun pt acc => return .cons (← shapeOf shapes m pt) acc
      if d.isRecord || d.isNewtype then
        pure (.record (← parts n (d.parts[0]?.getD #[])))
      else
        let cs ← d.parts.toList.foldrM (init := Ctors.nil) fun ts acc => do
          if ts.isEmpty then return .cons .nil acc
          match n with
          -- Beyond the bound: a payload of no values, which still marks
          -- the variant as having one.
          | 0 => return .cons (.cons .empty .nil) acc
          | m + 1 => return .cons (← parts m ts) acc
        pure (.ctors cs)
    | _ => throw (notEnumerable t)
  -- A subset type that is not a finite integer one: its base's values that match.
  match t.pat?, base with
  | some _, .ints _ => return base
  | some p, s => return .filter s (keep p)
  | none, s => return s

/-- How many values of size at most `n` a shape has. -/
def Shape.count (s : Shape) (n : Nat) : Nat := (s.vals n).length

/-- The most assignments that enumeration searches for a procedure
(`check::enumeration_limit`). -/
def maxBehaviours : Nat := 65536

/-- `x`, or one more than `maxBehaviours` if it is larger. -/
def saturate (x : Nat) : Nat := min x (maxBehaviours + 1)

/-- `1 + k + k ^ 2 + ... + k ^ len`, saturated. -/
def geometric (k len : Nat) : Nat :=
  (List.range len).foldl (init := (1, 1)) (fun (sum, power) _ =>
    let power := saturate (power * k)
    (saturate (sum + power), power)) |>.1

/-- How many sets of at most `card` of `k` values there are, saturated:
the sum of the binomial coefficients `C(k, c)` for `c ≤ card`. -/
def subsetCount (k card : Nat) : Nat :=
  if k > maxBehaviours then maxBehaviours + 1 else
  -- Row `j` holds, for each `c ≤ card`, how many sets of exactly `c` of
  -- `j` values there are.
  let row := (List.range k).foldl (init := (List.range (card + 1)).map fun c => if c == 0 then 1 else 0)
    fun row _ => row.zipIdx.map fun (x, c) => saturate (x + if c == 0 then 0 else row.getD (c - 1) 0)
  row.foldl (fun acc x => saturate (acc + x)) 0

mutual
/-- At least as many as the values of size at most `n` of the shape `s`
(`Shape.count`): exactly as many, but that a subset type may have fewer,
and `maxBehaviours + 1` if there are more (`saturate`).
Computed without listing them, so that a slot with too many values is
refused before they are listed. -/
def Shape.estimate : Shape → Nat → Nat
  | .bool, _ => 2
  | .int, n => 2 * n + 1
  | .nat, n | .abstract, n => n + 1
  | .ints vs, _ => vs.length
  | .string, n => geometric (charsUpTo n).length n
  | .seq e, n => geometric (e.estimate n) n
  | .set e, n => subsetCount (e.estimate n) n
  | .pair a b, n => saturate (a.estimate n * b.estimate n)
  | .ctors cs, n => cs.estimate n
  | .record fs, n => fs.estimate n
  | .filter s _, n => s.estimate n
  | .empty, _ => 0

def Shapes.estimate : Shapes → Nat → Nat
  | .nil, _ => 1
  | .cons s rest, n => saturate (s.estimate n * rest.estimate n)

def Ctors.estimate : Ctors → Nat → Nat
  | .nil, _ => 0
  | .cons .nil rest, n => saturate (1 + rest.estimate n)
  | .cons ps rest, n => saturate ((match n with | 0 => 0 | m + 1 => ps.estimate m) + rest.estimate n)
end

/-! ## Random values, for testing beyond the bound -/

/-- How many variants there are. -/
def Ctors.size : Ctors → Nat
  | .nil => 0
  | .cons _ rest => rest.size + 1

/-- A step of SplitMix64: the next state and a number. -/
def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let s := state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

/-- A number below `n`, and the next state; 0 if `n` is 0. -/
def below (state : UInt64) (n : Nat) : Nat × UInt64 :=
  let (s, z) := splitMix state
  (if n == 0 then 0 else z.toNat % n, s)

mutual
/-- A random value of `s`, of size at most `m`, with its size, from the
state `st`; `none` where none was found in a few tries. -/
partial def Shape.random (s : Shape) (m : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
  match s with
  | .bool => let (b, st) := below st 2; (some (.bool (b == 1), 0), st)
  | .int =>
    let (k, st) := below st (m + 1)
    let (neg, st) := below st 2
    let i : Int := if neg == 1 then -(k : Int) else k
    (some (.int i, valueSize .int i 0), st)
  | .nat => let (k, st) := below st (m + 1); (some (.int k, valueSize .nat k 0), st)
  | .ints vs => let (k, st) := below st vs.length; ((vs[k]?).map fun i => (.int i, 0), st)
  | .string =>
    let (len, st) := below st (m + 1)
    -- Each character of size at most `m` (`charSize`).
    let (cs, st) := (List.range len).foldl (init := ([], st)) fun (cs, st) _ =>
      let (r, st) := below st (min m codePoints)
      ((Char.ofNat ((r + 'a'.toNat) % codePoints), r + 1) :: cs, st)
    (some (.str (String.ofList (cs.map (·.1))), cs.foldl (fun k (_, l) => max k l) len), st)
  | .seq e =>
    let (len, st) := below st (m + 1)
    let (vs, st) := (List.range len).foldl (init := (some [], st)) fun (vs, st) _ =>
      let (v, st) := e.random m st
      ((do let vs ← vs; let v ← v; return v :: vs), st)
    (vs.map fun vs => (.seq vs.reverse.unzip.1, vs.foldl (fun k (_, l) => max k l) len), st)
  | .set e =>
    let (len, st) := below st (m + 1)
    let (vs, st) := (List.range len).foldl (init := (some [], st)) fun (vs, st) _ =>
      let (v, st) := e.random m st
      ((do let vs ← vs; let v ← v; return if vs.any (·.1 == v.1) then vs else v :: vs), st)
    -- Its members in increasing code, as `EVal.set` has them.
    (vs.map fun vs => (.set (vs.unzip.1.mergeSort fun a b => !(b.code < a.code)), vs.foldl (fun k (_, l) => max k l) vs.length), st)
  | .pair a b =>
    let (x, st) := a.random m st
    let (y, st) := b.random m st
    ((do let (x, k) ← x; let (y, l) ← y; return (.pair x y, max k l)), st)
  | .abstract => let (k, st) := below st (m + 1); (some (.abs k, valueSize .abstract k 0), st)
  | .ctors cs =>
    let (k, st) := below st cs.size
    cs.random k 0 m st
  | .record fs =>
    let (r, st) := fs.random m st
    (r.map fun (vs, k) => (.ctor 0 vs, valueSize .record 0 k), st)
  | .filter s keep =>
    let rec go (tries : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
      match tries with
      | 0 => (none, st)
      | t + 1 =>
        let (r, st) := s.random m st
        match r with
        | some (v, k) => if keep v then (some (v, k), st) else go t st
        | none => go t st
    go 8 st
  | .empty => (none, st)

/-- Random values of each of `ss`, with the largest of their sizes. -/
partial def Shapes.random (ss : Shapes) (m : Nat) (st : UInt64) : Option (List EVal × Nat) × UInt64 :=
  match ss with
  | .nil => (some ([], 0), st)
  | .cons s rest =>
    let (a, st) := s.random m st
    let (b, st) := rest.random m st
    ((do let (v, k) ← a; let (vs, l) ← b; return (v :: vs, max k l)), st)

/-- A random value of the `k`th of the variants `cs`, the first numbered
`i`. -/
partial def Ctors.random (cs : Ctors) (k i m : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
  match cs, k with
  | .nil, _ => (none, st)
  | .cons .nil _, 0 => (some (.ctor i [], valueSize .nullary i 0), st)
  | .cons ps _, 0 =>
    match m with
    | 0 => (none, st)
    | m' + 1 =>
      let (r, st) := ps.random m' st
      (r.map fun (vs, l) => (.ctor i vs, valueSize .variant i l), st)
  | .cons _ rest, k + 1 => rest.random k (i + 1) m st
end

/-- The largest size of the values that testing draws, beyond the bound `n`. -/
def testSize (n : Nat) : Nat := 10 * (n + 1)

/-- How many random tests a check set to `"enumerated+random"` runs. -/
def testCount : Nat := 100

/-- Up to `count` random values of the declared type `t` of size more than
the bound `n`, at most `testSize n`, from the state `st`, for testing
beyond the bound (`Reqs/Check#enumeration-then-testing`): none for a type
whose values are all within the bound. -/
def extrasOf (shapes : Name → Option DataShape) (n : Nat) (t : PTy) (count : Nat) (st : UInt64) :
    Array (EVal × Nat) := Id.run do
  let m := testSize n
  let .ok s := shapeOf shapes m t | return #[]
  let mut out := #[]
  let mut st := st
  for _ in [0:count] do
    -- A few tries for a value beyond the bound.
    for _ in [0:8] do
      let (r, st') := s.random m st
      st := st'
      if let some (v, k) := r then
        if k > n then
          out := out.push (v, k)
          break
  return out

/-! ## Formulas -/

/-- A formula of the check algorithms, as enumeration evaluates it: over
the procedure's formulas, its *atoms*, which a front end evaluates, and
over its variables' *slots*, each holding the position of its value in its
slot's values (`Space`). -/
inductive EF where
  /-- The procedure's `k`th atom. -/
  | atom (k : Nat)
  | tt
  | ff
  | not (f : EF)
  | conj (fs : Array EF)
  /-- `∃ outputs, f`, over the procedure's own outputs that are not
  defined. -/
  | exOutputs (f : EF)
  /-- The slot `x` holds the value `v`. -/
  | pin (x v : Nat)
  /-- The slot `x` holds one of the values `vs`: a variant's tester. -/
  | oneOf (x : Nat) (vs : List Nat)
  /-- `f` over the second copy of the variables. -/
  | primed (f : EF)
  /-- `x = x'`, for the variable `x`. -/
  | same (x : Name)
  deriving Inhabited, BEq, Hashable

/-- Where enumeration searches: a slot for each variable whose value is
enumerated, the procedure's own and its calls' that are not defined
outputs, in their order, then one for the second copy of each that
determinism copies, and last one for each type whose unspecified value
some atom reads, which an interpretation gives
(`Reqs/Check#checking-by-enumeration`). -/
structure Space where
  /-- Each slot's variable; a hidden slot's name is its type's. -/
  names : Array Name
  /-- The sizes of each slot's values, smallest first (`Shape.ordered`). -/
  sizes : Array (Array Nat)
  /-- The second copy of each slot, if determinism copies it. -/
  primeOf : Array (Option Nat)
  /-- The slots of the procedure's own outputs that are not defined, which
  `∃ outputs` ranges over. -/
  outputs : Array Nat
  /-- How many of the slots, at the end, are hidden: an interpretation's,
  not a variable's. -/
  hidden : Nat := 0
  /-- The bound. -/
  bound : Nat
  deriving Inhabited

/-- What a front end says of its atoms: the slots that each reads, the
defined outputs that each mentions, and how to evaluate each. -/
structure Atoms where
  slots : Array (Array Nat)
  defs : Array (Array Name) := #[]
  eval : Nat → Array Nat → Bool
  /-- Whether the atom's truth is known in an assignment: it is not where
  a quantifier over a domain that the bound does not exhaust has no
  instance that decides it (`Reqs/Check#quantifiers-up-to-the-bound`).
  `eval` is its truth where it is known. -/
  known : Nat → Array Nat → Bool := fun _ _ => true
  /-- Whether every atom's truth is known in every assignment, so that the
  search need not read `known`. -/
  total : Bool := true
  /-- Whether the defined output `d` has the same value in two
  assignments, where `sameKnown` says that it is known whether it has. -/
  sameDefined : Name → Array Nat → Array Nat → Bool := fun _ _ _ => true
  /-- Whether the defined output `d`'s values in two assignments are both
  known: a quantifier up to the bound may leave one unknown, and then so
  is whether they are the same (`Reqs/Check#quantifiers-up-to-the-bound`). -/
  sameKnown : Name → Array Nat → Array Nat → Bool := fun _ _ _ => true
  /-- The slots that each defined output's definition reads, through the
  definitions of the defined outputs that it mentions too. -/
  defSlots : Name → Array Nat := fun _ => #[]
  /-- Whether the `k`th atom has an index, in itself or in the
  definitions of the defined outputs that it mentions or the bodies it
  applies, whose value out of range is the hidden slot's, one
  interpretation of all (`Reqs/Check#searching`): if none has,
  `unknown` is never true, and the backend does not look for it. -/
  readsIndex : Nat → Bool := fun _ => false
  /-- Whether the definition of the defined output `d` has one. -/
  defReadsIndex : Name → Bool := fun _ => false
  /-- Whether the `k`th atom's value in an assignment depends on an index
  out of range: evaluated with every such index unknown, it is unknown. -/
  unknown : Nat → Array Nat → Bool := fun _ _ => false
  /-- Whether the defined output `d`'s value in an assignment depends on
  one. -/
  defUnknown : Name → Array Nat → Bool := fun _ _ => false
  /-- The `k`th atom's truth in an assignment, `none` where it is not
  known: `eval` where `known` says that it is (`Atoms.TruthAgrees`). A
  front end that finds both with one evaluation gives all three by
  `Atoms.ofTruth`, so that they agree by construction, and the search
  evaluates the atom once rather than twice; `Atoms.truthOf` reads it. -/
  truth? : Option (Nat → Array Nat → Option Bool) := none
  /-- Runs a computation that evaluates the atoms, giving its value, which
  is always the computation's: a front end that evaluates them in Lean's
  interpreter runs it within one interpreter, so that each evaluation
  does not start one of its own (`Atoms.within`). -/
  batch : (Unit → Array Nat) → Array Nat := fun f => f ()

instance : Inhabited Atoms := ⟨{ slots := #[], eval := fun _ _ => false }⟩

/-- Atoms over `slots` whose truth, `none` where it is not known, is
`truth`: their `eval`, `known` and `truth?` all come from it, so that
they agree (`Atoms.ofTruth_agrees`). -/
def Atoms.ofTruth (slots : Array (Array Nat)) (truth : Nat → Array Nat → Option Bool) : Atoms :=
  { slots, eval := fun k env => truth k env == some true, known := fun k env => (truth k env).isSome
    truth? := some truth }

/-- `truth?`, where it is given, is `eval` where `known` says the truth is
known, and `none` elsewhere, so that reading it (`Atoms.truthOf`), as the
search does (`EF.truth`), agrees with reading those two, as the proofs do
(`truth3`); `EF.truth_atom_truth3` proves it at an atom. -/
def Atoms.TruthAgrees (ats : Atoms) : Prop :=
  ∀ f, ats.truth? = some f → ∀ k env, f k env = if ats.known k env then some (ats.eval k env) else none

theorem Atoms.ofTruth_agrees (slots : Array (Array Nat)) (truth : Nat → Array Nat → Option Bool) :
    (Atoms.ofTruth slots truth).TruthAgrees := by
  intro f h k env
  simp only [Atoms.ofTruth, Option.some.injEq] at h
  subst h
  simp only [Atoms.ofTruth]
  rcases truth k env with _ | _ | _ <;> rfl

/-- `f ()`, run by `Atoms.batch`. -/
def Atoms.within (ats : Atoms) (f : Unit → Bool) : Bool :=
  (ats.batch fun _ => #[if f () then 1 else 0])[0]? == some 1

/-- `f ()`, run by `Atoms.batch`: `none` written as `#[0]`, and `some a`
as `1` before `a`. -/
def Atoms.withinOption (ats : Atoms) (f : Unit → Option (Array Nat)) : Option (Array Nat) :=
  let r := ats.batch fun _ => match f () with
    | none => #[0]
    | some a => #[1] ++ a
  if r[0]? == some 1 then some (r.extract 1) else none

/-- The `k`th atom's truth in `env`, `none` where it is not known
(`Atoms.known`), else its value (`Atoms.eval`). -/
@[inline] def Atoms.truthOf (ats : Atoms) (k : Nat) (env : Array Nat) : Option Bool :=
  match ats.truth? with
  | some f => f k env
  | none => if ats.known k env then some (ats.eval k env) else none

/-- Where `truth?` agrees with `eval` and `known`, as `Atoms.ofTruth`
makes it, `truthOf` reads what they say. -/
theorem Atoms.truthOf_of_agrees (ats : Atoms) (h : ats.TruthAgrees) (k : Nat) (env : Array Nat) :
    ats.truthOf k env = if ats.known k env then some (ats.eval k env) else none := by
  unfold Atoms.truthOf
  split
  · next f hf => exact h f hf k env
  · rfl

def Space.slotOf? (sp : Space) (n : Name) : Option Nat := sp.names.idxOf? n

/-- `env` with each copied slot holding its second copy's value. -/
def Space.primedEnv (sp : Space) (env : Array Nat) : Array Nat :=
  env.mapIdx fun i v => match sp.primeOf[i]?.join with
    | some p => env.getD p 0
    | none => v

/-- The slots that `f` reads, perhaps more than once. -/
def EF.slots (sp : Space) (ats : Atoms) : EF → List Nat
  | .atom k => (ats.slots[k]?.getD #[]).toList
  | .tt | .ff => []
  | .not f => f.slots sp ats
  | .conj fs => (fs.attach.toList.map fun ⟨f, _⟩ => f.slots sp ats).flatten
  | .exOutputs f => (f.slots sp ats).filter (!sp.outputs.contains ·)
  | .pin x _ => [x]
  | .oneOf x _ => [x]
  | .primed f => (f.slots sp ats).map fun x => (sp.primeOf[x]?.join).getD x
  | .same x => match sp.slotOf? x with
    | some s => s :: (sp.primeOf[s]?.join).toList
    | none =>
      -- A defined output: the slots that its definition reads, and their
      -- second copies.
      let ss := (ats.defSlots x).toList
      ss ++ ss.filterMap (sp.primeOf[·]?.join)

/-- Whether `f` reads an index, through an atom or a defined output that
it compares (`Atoms.readsIndex`). -/
def EF.readsIndex (ats : Atoms) : EF → Bool
  | .atom k => ats.readsIndex k
  | .not f | .exOutputs f | .primed f => f.readsIndex ats
  | .conj fs => fs.attach.any fun ⟨f, _⟩ => f.readsIndex ats
  | .same x => ats.defReadsIndex x
  | .tt | .ff | .pin .. | .oneOf .. => false

/-- `xs` without repeats, in order of first occurrence. -/
def dedup (xs : List Nat) : List Nat := xs.foldl (fun a x => if a.contains x then a else a ++ [x]) []

/-- The defined outputs that `f` mentions, each with whether it is the
second copy's. -/
partial def EF.defsOf (ats : Atoms) : EF → Array (Name × Bool)
  | .atom k => (ats.defs[k]?.getD #[]).map (·, false)
  | .not f | .exOutputs f => f.defsOf ats
  | .conj fs => fs.flatMap (·.defsOf ats)
  | .primed f => (f.defsOf ats).map fun (d, _) => (d, true)
  | .same x => #[(x, false), (x, true)]
  | _ => #[]

/-! ## Searching -/

/-- Every choice of a value for each of a list of slots, of `lims` values
each, in order, the last varying fastest (`check::fair_order`). -/
def lexAll : List Nat → List (List Nat)
  | [] => [[]]
  | l :: ls => (List.range l).flatMap fun j => (lexAll ls).map (j :: ·)

/-- The first choice, after `pre`, of a value for each of the slots with
`lims` values each, in the order of `lexAll`, each of whose prefixes `ok`
accepts as it is made: a prefix that `ok` refuses is not extended
(`check::search_first`). -/
def dfs (ok : List Nat → Bool) (pre : List Nat) : List Nat → Option (List Nat)
  | [] => some pre
  | l :: ls => (List.range l).findSome? fun j => if ok (pre ++ [j]) then dfs ok (pre ++ [j]) ls else none

/-- `base` with the slots `slots` holding the values `choice`. -/
def setAll (base : Array Nat) (slots choice : List Nat) : Array Nat :=
  (slots.zip choice).foldl (fun e (s, j) => e.set! s j) base

/-- After how many of `slots` are chosen a part that reads `ss` can be
tried: once the last of them is; 0 if it reads none of them. -/
def readyAt (slots ss : List Nat) : Nat :=
  ss.foldl (fun m s => if slots.contains s then max m (slots.idxOf s + 1) else m) 0

/-- Whether the parts `parts`, each with where it can be tried
(`readyAt`), that can be tried once `choice` is made, and not before,
hold in `base` with `slots` holding `choice`: each part is tried once,
as soon as it can be (`check::pruning`). -/
def newlyHold (base : Array Nat) (slots : List Nat) (parts : List (Nat × (Array Nat → Bool))) (choice : List Nat) : Bool :=
  let ready := parts.filter (·.1 == choice.length)
  ready.isEmpty || (let e := setAll base slots choice; ready.all (·.2 e))

/-- The first choice of values for `slots`, of `lims` values each, in the
order of `lexAll`, with which `base` makes `parts` true, each part tried
as soon as the slots it reads are chosen (`dfs`); `base` with it. -/
def firstChoice (base : Array Nat) (slots lims : List Nat) (parts : List (List Nat × (Array Nat → Bool))) :
    Option (Array Nat) :=
  let ps := parts.map fun (ss, f) => (readyAt slots ss, f)
  if newlyHold base slots ps [] then (dfs (newlyHold base slots ps) [] lims).map (setAll base slots) else none

/-- How many of the slot `s`'s values have size at most `k`: they are
smallest first, so these are the first. -/
def Space.within (sp : Space) (s k : Nat) : Nat :=
  ((sp.sizes[s]?.getD #[]).toList.takeWhile (· ≤ k)).length

/-- The value of `f` in `env`. -/
def EF.eval (sp : Space) (ats : Atoms) (env : Array Nat) : EF → Bool
  | .atom k => ats.eval k env
  | .tt => true
  | .ff => false
  | .not f => !f.eval sp ats env
  | .conj fs => fs.attach.all fun ⟨f, _⟩ => f.eval sp ats env
  | .exOutputs (.conj fs) =>
    -- Some values of the outputs make `f` true: searched with each
    -- conjunct tried as soon as it can be.
    let outs := sp.outputs.toList.filter fun o => (EF.conj fs).slots sp ats |>.contains o
    let lims := outs.map fun s => (sp.sizes[s]?.getD #[]).size
    (firstChoice env outs lims (fs.attach.toList.map fun ⟨g, _⟩ => (g.slots sp ats, fun e => g.eval sp ats e))).isSome
  | .exOutputs f =>
    let outs := sp.outputs.toList.filter fun o => (f.slots sp ats).contains o
    let lims := outs.map fun s => (sp.sizes[s]?.getD #[]).size
    (firstChoice env outs lims [(f.slots sp ats, fun e => f.eval sp ats e)]).isSome
  | .pin x v => env[x]? == some v
  | .oneOf x vs => (env[x]?.map vs.contains).getD false
  | .primed f => f.eval sp ats (sp.primedEnv env)
  | .same x => match sp.slotOf? x with
    | some s => match sp.primeOf[s]?.join with
      | some p => env[s]? == env[p]?
      | none => true
    | none => ats.sameDefined x env (sp.primedEnv env)

/-- A formula's truth where the indexes out of range are unknown: the
strong Kleene truth values (`check::Truth`). -/
inductive Truth where
  | yes
  | no
  | unknown
  deriving Inhabited, BEq, DecidableEq, Repr

def Truth.ofBool (b : Bool) : Truth := if b then .yes else .no

def Truth.not : Truth → Truth
  | .yes => .no
  | .no => .yes
  | .unknown => .unknown

/-- The conjunction of `ts`: false if one is, else unknown if one is. -/
def Truth.all (ts : List Truth) : Truth :=
  if ts.contains .no then .no else if ts.contains .unknown then .unknown else .yes

/-- The disjunction of `ts`: true if one is, else unknown if one is. -/
def Truth.any (ts : List Truth) : Truth :=
  if ts.contains .yes then .yes else if ts.contains .unknown then .unknown else .no

/-- The truth of `f` in `env`, with each index out of range unknown: an
atom is unknown where its value depends on one (`Atoms.unknown`), or
where a quantifier up to the bound leaves it unknown (`Atoms.known`), and
otherwise its value; `∃ outputs` is true if some values of the outputs
make it true, else unknown if some make it unknown. -/
def EF.truth (sp : Space) (ats : Atoms) (env : Array Nat) : EF → Truth
  | .atom k => if ats.unknown k env then .unknown else match ats.truthOf k env with
    | some b => .ofBool b
    | none => .unknown
  | .tt => .yes
  | .ff => .no
  | .not f => (f.truth sp ats env).not
  | .conj fs => Truth.all (fs.attach.toList.map fun ⟨f, _⟩ => f.truth sp ats env)
  | .exOutputs f =>
    let outs := sp.outputs.toList.filter fun o => (f.slots sp ats).contains o
    let lims := outs.map fun s => (sp.sizes[s]?.getD #[]).size
    Truth.any ((lexAll lims).map fun a => f.truth sp ats (setAll env outs a))
  | .pin x v => .ofBool (env[x]? == some v)
  | .oneOf x vs => .ofBool ((env[x]?.map vs.contains).getD false)
  | .primed f => f.truth sp ats (sp.primedEnv env)
  | .same x => match sp.slotOf? x with
    | some s => match sp.primeOf[s]?.join with
      | some p => .ofBool (env[s]? == env[p]?)
      | none => .yes
    | none =>
      let e' := sp.primedEnv env
      if ats.defUnknown x env || ats.defUnknown x e' || !ats.sameKnown x env e' then .unknown
      else .ofBool (ats.sameDefined x env e')

/-- Whether the truths of a query's formulas in an assignment leave it
open: none is false, and one is unknown, so that some interpretation of
the indexes out of range may make them all true (`check::doubtful`). -/
def doubtfulRow (ts : List Truth) : Bool := ts.all (· != .no) && ts.any (· == .unknown)

/-! ## Partial truth -/

/-- The most values that a range a quantifier ranges over may have
(`eval::MAX_ENUMERATED`): with more, the quantifier has no value that the
evaluators know (`Reqs/Eval#quantifiers`), in both front ends. -/
def maxEnumerated : Int := 1024

/-- Whether some atom's truth may be unknown to the model search
(`Atoms.known`), given whether each of a procedure's formulas, and each of
the definitions they read, has a quantifier: only a quantifier, guarded or
not, can leave one unknown there, where its domain is too large or an
instance is unknown (`Reqs/Check#quantifiers-up-to-the-bound`). Both front
ends set `Atoms.total` to its negation. -/
def mayBeUnknown (quantified : Array Bool) : Bool := quantified.any id

/-- Why a query that a quantifier undecided up to the bound leaves open
is unknown without a model (`Detail.undecidedQuantifier`). -/
def undecidedQuantifierReason : String := "a quantifier is undecided"

/-- The strong Kleene conjunction of two truths, `none` being unknown: a
false one settles it. -/
def andTruth (a b : Option Bool) : Option Bool :=
  match a, b with
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- The strong Kleene negation (`check::partial_not`). -/
def notTruth (a : Option Bool) : Option Bool := a.map (!·)

/-- The strong Kleene disjunction, the conjunction's dual: a true one
settles it. -/
def orTruth (a b : Option Bool) : Option Bool := notTruth (andTruth (notTruth a) (notTruth b))

/-- The truth of a quantifier, a `forall` if `universal`, whose instances,
over values all of its domain's if `exact`, have the truths of `body` at
`values`, `none` being unknown (`check::quantified_truth`): an instance that
decides it, `false` for a `forall` and `true` for an `exists`, does so;
otherwise it has the other value if every instance is known and the domain
exhausted, and is unknown if not. The instances after a deciding one are
not evaluated. -/
def quantifiedTruth {α : Type} (exact universal : Bool) (body : α → Option Bool) : List α → Option Bool
  | [] => if exact then some universal else none
  | v :: vs => match body v with
    | some b => if b != universal then some b else quantifiedTruth exact universal body vs
    | none => if quantifiedTruth exact universal body vs == some (!universal) then some (!universal) else none

/-- The name under which `EF.polarize` reads whether the defined output
`x` is the same in both copies as whether it may be: no variable's name
has a `#`. -/
def possiblySame (x : Name) : Name := .str x "#possibly"

/-- The defined output that `possiblySame` names. -/
def unPossibly? : Name → Option Name
  | .str x "#possibly" => some x
  | _ => none

/-- The atoms of `ats`, each twice: the `k`th, of `n`, as whether it is
known to be true, and the `n + k`th as whether it may be, not being known
to be false (`EF.polarize`). Each copy reads what the atom reads. So is
whether a defined output is the same in both copies: under its own name,
whether it is known to be, and under `possiblySame`, whether it may be. -/
def Atoms.polarized (ats : Atoms) : Atoms :=
  let n := ats.slots.size
  { slots := ats.slots ++ ats.slots
    defs := (List.range (2 * n)).toArray.map fun k => ats.defs[k % n]?.getD #[]
    eval := fun k env => if k < n then ats.known k env && ats.eval k env
      else !ats.known (k - n) env || ats.eval (k - n) env
    sameDefined := fun d e₁ e₂ => match unPossibly? d with
      | some x => !ats.sameKnown x e₁ e₂ || ats.sameDefined x e₁ e₂
      | none => ats.sameKnown d e₁ e₂ && ats.sameDefined d e₁ e₂
    defSlots := fun d => ats.defSlots ((unPossibly? d).getD d)
    -- What each copy reads of the indexes out of range is its atom's.
    readsIndex := fun k => ats.readsIndex (k % n)
    defReadsIndex := fun d => ats.defReadsIndex ((unPossibly? d).getD d)
    unknown := fun k env => ats.unknown (k % n) env
    defUnknown := fun d env => ats.defUnknown ((unPossibly? d).getD d) env
    batch := ats.batch }

/-- `f` with each of its atoms read under `Atoms.polarized` of `n` atoms:
where `f` is read positively, if `positive?`, as known to be true, and
where it is read under a negation, as possibly true. So `f` holds of the
polarized atoms, positively, exactly where it is known to be true, and,
negatively, where it may be. -/
def EF.polarize (sp : Space) (n : Nat) (positive? : Bool) : EF → EF
  | .atom k => .atom (if positive? then k else n + k)
  | .not f => .not (f.polarize sp n (!positive?))
  | .conj fs => .conj (fs.attach.map fun ⟨f, _⟩ => f.polarize sp n positive?)
  | .exOutputs f => .exOutputs (f.polarize sp n positive?)
  | .primed f => .primed (f.polarize sp n positive?)
  | .same x => .same (if positive? || (sp.slotOf? x).isSome then x else possiblySame x)
  | f => f

/-- The slots that `parts` read, in order. -/
def slotsOf (sp : Space) (ats : Atoms) (parts : Array EF) : List Nat :=
  (dedup (parts.toList.flatMap (·.slots sp ats))).mergeSort

/-- Each of `parts`, with the slots it reads, as a function of an
assignment. -/
def partsOf (sp : Space) (ats : Atoms) (parts : Array EF) : List (List Nat × (Array Nat → Bool)) :=
  parts.toList.map fun f => (f.slots sp ats, fun e => f.eval sp ats e)

/-- The size of the `j`th value of the slot `s`. -/
def Space.sizeAt (sp : Space) (s j : Nat) : Nat := (sp.sizes[s]?.getD #[])[j]?.getD 0

/-- That some of `slots` holds a value of size `k`, in an assignment: the
part that makes an assignment's level `k`. -/
def Space.levelPart (sp : Space) (slots : List Nat) (k : Nat) : List Nat × (Array Nat → Bool) :=
  (slots, fun e => slots.any fun s => sp.sizeAt s (e[s]?.getD 0) == k)

/-- The level of the choice `a` of values for `slots`: the largest size of
its values (`check::fair_order`). -/
def Space.levelOf (sp : Space) (slots a : List Nat) : Nat :=
  (slots.zip a).foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) 0

/-- The assignments of the slots `slots`, `lims k` values each at the
level `k`, by level, from 0 to `bound`, and in the order of `lexAll` within
a level, where `atLevel k` says that one is of level `k`
(`check::fair_order`). -/
def fairList (bound : Nat) (lims : Nat → List Nat) (atLevel : Nat → List Nat → Bool) : List (List Nat) :=
  (List.range (bound + 1)).flatMap fun k => (lexAll (lims k)).filter (atLevel k)

/-- The fair order of the assignments of `slots` up to the bound, set in
`base`: by level, the largest size of their values, then in the order of
the slots and of each slot's values, the last varying fastest. -/
def Space.fairList (sp : Space) (base : Array Nat) (slots : List Nat) : List (List Nat) :=
  Fren.Core.Enumeration.fairList sp.bound (fun k => slots.map (sp.within · k))
    (fun k a => (sp.levelPart slots k).2 (setAll base slots a))

/-- Whether some assignment up to the bound of the slots that `parts` read
is doubtful for them (`doubtfulRow`): where the search finds no model,
the query is then unknown, not `unsat` (`check::enumerated_answer`). -/
def doubtful (sp : Space) (ats : Atoms) (parts : Array EF) : Bool :=
  let slots := slotsOf sp ats parts
  let env0 := Array.replicate sp.names.size 0
  (if slots.isEmpty then [[]] else sp.fairList env0 slots).any fun a =>
    doubtfulRow (parts.toList.map (·.truth sp ats (setAll env0 slots a)))

/-- The first assignment of the slots that `parts` read that makes them
all true, smallest first and fairly (`Reqs/Check#searching`): the first
of `Space.fairList` (`check::search_first`), each level searched with
`firstChoice`. With the level. -/
def search (sp : Space) (ats : Atoms) (parts : Array EF) : Option (Array Nat × Nat) :=
  let ps := partsOf sp ats parts
  let slots := slotsOf sp ats parts
  let env0 := Array.replicate sp.names.size 0
  if slots.isEmpty then
    if ps.all (·.2 env0) then some (env0, 0) else none
  else
    (List.range (sp.bound + 1)).findSome? fun k =>
      (firstChoice env0 slots (slots.map (sp.within · k)) (ps ++ [sp.levelPart slots k])).map (·, k)

/-- Testing beyond the bound (`Reqs/Check#enumeration-then-testing`): for
each of `testCount` tests, an assignment of the slots that `parts` read,
each slot's value one of its random values beyond the bound, the `t`th for
test `t` (a second copy's, another), or, for a slot whose values are all
within it, one drawn from `seed`; the first that makes them all true. -/
def testSearch (sp : Space) (ats : Atoms) (parts : Array EF) (seed : UInt64) : Option (Array Nat) := Id.run do
  let ps := partsOf sp ats parts
  let slots := slotsOf sp ats parts
  let primes := sp.primeOf.filterMap id
  let mut st := seed
  for t in [0:testCount] do
    let mut env := Array.replicate sp.names.size 0
    for s in slots do
      let all := (sp.sizes[s]?.getD #[]).size
      let within := sp.within s sp.bound
      let extra := all - within
      if extra > 0 then
        let k := if primes.contains s then (t + extra / 2 + 1) % extra else t % extra
        env := env.set! s (within + k)
      else
        let (j, st') := below st all
        st := st'
        env := env.set! s j
    if ps.all (·.2 env) then return some env
  return none

/-- The answer to a query (`check::enumerated_answer`): the search's
model up to the bound, if it found one, else, if `testing`, testing's
beyond it; with whether it is testing's. -/
def answerOf (found? : Option α) (testing : Bool) (test : Unit → Option α) : Option (α × Bool) :=
  match found? with
  | some a => some (a, false)
  | none => if testing then (test ()).map (·, true) else none

/-- What a query answers, from whether a model was found and whether
some assignment is doubtful (`check::enumerated_answer`): a model is a
behaviour, so `sat`; without one, `unsat`, unless the indexes out of
range of a doubtful assignment, whose values the search sees for one
interpretation only, may make one, so `unknown`. -/
def answerKind (found doubtful : Bool) : Answer :=
  if found then .sat else if doubtful then .unknown else .unsat

/-- Why a query with a doubtful assignment is unknown without a model. -/
def indexUnknownReason : String := "an index out of range may decide it"

/-! ## The backend -/

/-- A value of a model: its slot and the position of its value there, if
it is enumerated rather than a defined output's, and the value as Fren
writes it. -/
structure EV where
  at? : Option (Nat × Nat)
  shown : String
  /-- Exact assignment, including hidden function tables, for observations. -/
  environment? : Option (Array Nat) := none
  deriving Inhabited

/-- The checks' backend over the space `sp`, whose atoms are `ats`
(`Reqs/Check#checking-by-enumeration`): each query is answered by `search`,
`unsat` if no assignment within the bound refutes it, nor, with
`testing?`'s seed, any of `testSearch`'s, and otherwise `sat` with the
first that does, which gives the slots it reads, but the hidden
ones, and the defined outputs that its formulas mention, as `render` and
`defValue` show them. -/
def backend [Monad m] (sp : Space) (ats : Atoms) (render : Nat → Nat → m String)
    (defValue : Name → Array Nat → m (Option String)) (testing? : Option UInt64 := none)
    (variantOf : Nat → Nat → Option Variant := fun _ _ => none)
    (facts : Array EF := #[]) (outputFacts : Array EF := #[]) : Backend m EF EV where
  query hyps goal _ := do
    -- Type-domain facts hold in each copy, independently of named clauses.
    let domain := facts ++ facts.map EF.primed
    let parts := (domain ++ hyps.map (·.2)).push (.not goal)
    -- Where a quantifier may leave an atom unknown, a model is an
    -- assignment where every part is known to be true (`check::polarized`).
    -- An index out of range is read as `[][0]` there: a model is a
    -- behaviour either way.
    let known := if ats.total then parts else parts.map (·.polarize sp ats.slots.size true)
    let searched := if ats.total then ats else ats.polarized
    -- Within `Atoms.batch`, with whether testing found it after the
    -- assignment.
    let found := (ats.withinOption fun _ =>
      (answerOf ((search sp searched known).map (·.1)) testing?.isSome fun _ =>
        testSearch sp searched known (testing?.getD 0)).map fun (e, t) => e.push (if t then 1 else 0)).map
      fun a => (a.pop, a.back? == some 1)
    match found with
    | none =>
      -- Only a query with an index or a quantifier can be doubtful, and it
      -- is unknown if some assignment is (`check::enumerated_answer`): by
      -- a quantifier if one is with only the quantifiers unknown.
      let open? := (!ats.total || parts.any (·.readsIndex ats)) && ats.within fun _ => doubtful sp ats parts
      if answerKind false open? != .unknown then return .unsat
      let byQuantifier := !ats.total && ats.within fun _ =>
        doubtful sp { ats with unknown := fun _ _ => false, defUnknown := fun _ _ => false } parts
      return .unknown (if byQuantifier then undecidedQuantifierReason else indexUnknownReason)
    | some (env, _) =>
      let slots := slotsOf sp ats parts
      let shown ← (slots.toArray.filter (· < sp.names.size - sp.hidden)).mapM fun x => do
        return (sp.names[x]!, ({ at? := some (x, env[x]!), shown := ← render x env[x]! } : EV))
      let defs := (parts.flatMap (·.defsOf ats)).foldl (init := #[]) fun acc d => if acc.contains d then acc else acc.push d
      let defd ← defs.filterMapM fun (d, primed) => do
        let e := if primed then sp.primedEnv env else env
        return (← defValue d e).map fun v => (if primed then primed' d else d, ({ at? := none, shown := v } : EV))
      return .sat (shown ++ defd ++ #[(Lean.Name.mkSimple "#member_model", { at? := none, shown := "", environment? := some env })])
  modelBool? := some fun model formula => pure do
    let (_, token) ← model.find? (·.1 == Lean.Name.mkSimple "#member_model")
    let env ← token.environment?
    if ats.total then return ats.within fun _ => formula.eval sp ats env
    -- Known to be true, known to be false, or unknown.
    let n := ats.slots.size
    if ats.within fun _ => (formula.polarize sp n true).eval sp ats.polarized env then return true
    if !(ats.within fun _ => (formula.polarize sp n false).eval sp ats.polarized env) then return false
    none
  falseF := .ff
  notF := .not
  conj := .conj
  existsOutputs f := pure (.exOutputs (if outputFacts.isEmpty then f else .conj (outputFacts.push f)))
  pin _ v := pure (v.at?.map fun (x, j) => .pin x j)
  -- That the slot holds a value of the same variant: one of those of its
  -- values that are.
  pinVariant _ v := pure do
    let (x, j) ← v.at?
    let k ← variantOf x j
    let n := (sp.sizes[x]?.getD #[]).size
    return (k, .oneOf x ((List.range n).filter fun i => variantOf x i == some k))
  render _ v := pure v.shown
  prime := .primed
  samePrimed := .same
  -- Defined outputs are computed, never enumerated.
  subst _ f := f
where
  primed' (n : Name) : Name := Fren.Core.primed n

/-- `c` with each formula an atom, numbered in the order of its fields, and
the formulas, in that order: each front end evaluates its own. A
definition's equation, and its term, always hold: defined outputs are
computed, not enumerated. The questions about tables, `match`es and
applications are atoms too; those about indexes are not enumerated
(`check::by_evidence`). -/
def _root_.Fren.Core.Comp.atoms (c : Comp F) : Comp EF × Array F := Id.run do
  let mut fs : Array F := #[]
  let mut next := 0
  let mut out : Comp EF := { path := c.path, vars := c.vars, assumes := #[], reqs := #[], expects := #[], triggers := #[]
                             typesInterpreted := c.typesInterpreted, fn? := c.fn?, inhabitation := c.inhabitation }
  let mut named : Array (Array (Name × EF)) := #[]
  for xs in #[c.assumes, c.reqs, c.expects, c.covers, c.triggers, c.posts] do
    let mut ys := #[]
    for (n, f) in xs do
      fs := fs.push f
      ys := ys.push (n, EF.atom next)
      next := next + 1
    named := named.push ys
  let mut insts := #[]
  for i in c.insts do
    fs := fs.push i.bindings
    let b := EF.atom next
    fs := fs.push i.behaviour
    let h := EF.atom (next + 1)
    next := next + 2
    let mut as := #[]
    for (n, f) in i.assumes do
      fs := fs.push f
      as := as.push (n, EF.atom next)
      next := next + 1
    insts := insts.push { name := i.name, comp := i.comp, bindings := b, behaviour := h, assumes := as, typed := i.typed }
  let mut tables := #[]
  for t in c.tables do
    fs := fs.push t.site.goal
    tables := tables.push { t with site := { t.site with goal := EF.atom next } }
    next := next + 1
  let mut groups := #[]
  for group in c.branchGroups do
    let mut members := #[]
    for member in group.members do
      fs := fs.push member.formula
      let formula := EF.atom next
      next := next + 1
      let value ← match member.valueFormula? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      let guard ← match member.evaluationGuard? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      members := members.push {
        name := member.name
        formula := formula
        valueFormula? := value
        evaluationGuard? := guard
        range? := member.range?
        text := member.text
      }
    let guard ← match group.guard? with
      | none => pure none
      | some f => do
        fs := fs.push f
        let atom := some (EF.atom next)
        next := next + 1
        pure atom
    groups := groups.push { owner := group.owner, kind := group.kind, members, guard? := guard }
  let mut observations := #[]
  for group in c.memberGroups do
    let mut members := #[]
    for member in group.members do
      fs := fs.push member.formula
      let formula := EF.atom next
      next := next + 1
      let value ← match member.valueFormula? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      let guard ← match member.evaluationGuard? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      members := members.push {
        name := member.name
        formula := formula
        valueFormula? := value
        evaluationGuard? := guard
        range? := member.range?
        text := member.text
      }
    observations := observations.push { owner := group.owner, op := group.op, wanted := group.wanted, members }
  out := { out with assumes := named[0]!, reqs := named[1]!, expects := named[2]!, covers := named[3]!, triggers := named[4]!
                    posts := named[5]!, insts, tables, branchGroups := groups, memberGroups := observations
                    defs := c.defs.map fun (d, _, _) => (d, .tt, .tt) }
  return (out, fs)

/-! ## Which checks, and their verdicts -/

/-- How a check is run, given its evidence (`check::by_evidence`). -/
inductive Method where
  | solver
  | testing
  | enumeration
  /-- Enumeration, then testing where enumeration is not complete. -/
  | enumerationThenTesting
  | skipped
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The checks that enumeration decides: all but definedness, of indexes,
which only sequences have, and of values of subset types, and the
postconditions of defined functions, which only their bodies have: those
that `dispatchOf` runs (`check::by_evidence`). -/
def enumerable (kind : CheckKind) : Bool :=
  (dispatchOf kind .component .enumerated).1 == .run

/-- How a check of kind `kind` is run, given its evidence, and whether it
is the definedness of a value given where a subset type is declared,
which the solver always checks: as `dispatchOf` runs it under enumeration,
if the evidence includes it, and otherwise under testing
(`check::by_evidence`). -/
def methodOf (kind : CheckKind) (ev : Evidence) (obligation : Bool := false) : Method :=
  let dispatch (m : ProofMethod) := (dispatchOf kind .component m obligation).1
  if ev.enumerated then
    match dispatch .enumerated with
    | .run => if ev.tested then .enumerationThenTesting else .enumeration
    | .skip => .skipped
    | .bySolver | .reject => .solver
  else if ev.tested then
    match dispatch .random with
    | .run => .testing
    | .skip => .skipped
    | .bySolver | .reject => .solver
  else .solver

/-- `c` with only the checks of `t`, those that enumeration decides, and
the kinds of check to run of them. -/
def _root_.Fren.Core.Comp.only (t : Tested) (c : Comp F) (kinds : Array CheckKind) : Comp F × Array CheckKind :=
  ({ c with
      expects := c.expects.filter (t.props.contains ·.1)
      covers := c.covers.filter (t.props.contains ·.1)
      triggers := c.triggers.filter (t.props.contains ·.1)
      insts := c.insts.map fun i => if t.insts.contains i.name then i else { i with assumes := #[] }
      vars := c.vars.map fun v => if t.dets.contains v.name then v else { v with isDet := false }
      indexes := #[], posts := #[]
      tables := c.tables.filter fun s => t.props.contains s.site.prop || t.insts.contains s.site.prop },
    kinds.filter fun k => enumerable k && (k != .realizable || t.realizable) && (k != .redundancy || t.redundancy))

/-- Whether a check passes on a proof, rather than on a model
(`check::proof?`, `Reqs/Check#verdict-families`). -/
def provesFamily (kind : CheckKind) : Bool := kind.proof

/-- What enumeration within the bound shows of a check
(`check::enumerated_verdict`): `exact` when every slot's values are all of
its type's, and `outputsExact` when every output's are, so that a
realizability conflict, whose input is pinned, is decided. A verdict that
rests on an `unsat` answer is otherwise only bounded: a pass that holds
for every behaviour up to the bound, or, for a check that fails on `unsat`,
inconclusive. -/
def enumeratedVerdict (kind : CheckKind) (verdict : Verdict) (conflict exact outputsExact : Bool) : Verdict × Bool :=
  if exact then (verdict, false)
  else match verdict with
    | .pass => (.pass, provesFamily kind)
    | .fail =>
      if kind == .realizable then (if conflict && outputsExact then (.fail, false) else (.inconclusive, true))
      else if provesFamily kind then (.fail, false)
      else (.inconclusive, true)
    | .inconclusive => (.inconclusive, false)

/-- `r`, a result of enumeration within the bound `n`, with its verdict as
`enumeratedVerdict` gives it, marked bounded if it is; sealed, since the
verdict changes, so that it shows a behaviour only where its verdict
allows it (`view::report_shows`). -/
def classify (n : Nat) (exact outputsExact : Bool) (r : CheckResult) (indexed : Bool := false) : CheckResult :=
  CheckResult.sealShown <|
  -- A bounded search does not prove properties of all admitted models.
  -- Keep its concrete evidence, but not unqualified global explanations.
  let r := if exact then r else { r with clashes := #[], branchConflicts := #[], explanationPremises := #[] }
  let conflict := r.detail matches .conflict ..
  -- A quantifier undecided up to the bound left a query open
  -- (`answerKind`).
  if r.verdict == .inconclusive && (match r.detail with | .unknown w => w == undecidedQuantifierReason | _ => false) then
    { r with detail := .undecidedQuantifier n, bounded? := some n } else
  let (verdict, bounded) := enumeratedVerdict r.kind r.verdict conflict exact outputsExact
  -- An index out of range left a query open (`answerKind`).
  let r := match r.detail with
    | .unknown w => if w == indexUnknownReason then { r with detail := .outOfRange } else r
    | _ => r
  if !bounded then { r with verdict } else
  if verdict == .inconclusive then
    let why := match r.kind, r.detail with
      | .realizable, .vacuousAssumptions _ => s!"no input meets the assumptions up to size {n}, but a larger one may"
      | .realizable, _ => s!"no outputs up to size {n}, but larger ones may exist"
      | _, _ => s!"no witness up to size {n}, but a larger one may exist"
    { r with verdict, detail := .unknown why, bounded? := some n, oneInterpretation := indexed }
  else { r with verdict, bounded? := some n }

/-! ## The space of a procedure -/


/-- Whether a procedure whose enumeration would search `count` assignments
is enumerated (`check::enumeration_limit`). -/
def withinLimit (count : Nat) : Bool := count ≤ maxBehaviours

/-- A variable for `spaceOf`: its signature, its declared type, and whether
it is a defined output. -/
structure SlotVar where
  sig : VarSig
  pty : PTy
  defined : Bool := false
  deriving Inhabited

/-- An uninterpreted function, for `spaceOf`: its name, and its
parameters' and result's declared types. -/
structure FunVar where
  name : Name
  params : Array PTy
  result : PTy
  deriving Inhabited

/-- The hidden slot of an uninterpreted function: its interpretations, each
a table from the tuples of its arguments up to the bound, the first
varying slowest, to its results up to the bound, numbered in base `results.size`,
the first tuple's digit the least significant; listed by the largest size of
their results, then by number (`Reqs/Check#searching`). -/
structure FunSlot where
  name : Name
  slot : Nat
  /-- Each parameter's values up to the bound. -/
  params : Array (Array EVal)
  results : Array EVal
  /-- The number of the table that each of the slot's values is. -/
  tables : Array Nat
  /-- Every interpretation of the function is among them. -/
  exhausted : Bool
  /-- How many interpretations there are up to the bound. -/
  count : Nat
  deriving Inhabited

/-- The position of the tuple of arguments at the positions `idx` in their
parameters' values, of sizes `sizes`, the first varying slowest; `none` if
one is not among them. -/
def tupleIndex (sizes idx : Array Nat) : Option Nat :=
  (sizes.zip idx).foldlM (init := 0) fun acc (k, i) => if i < k then some (acc * k + i) else none

/-- The result, by its position among the results, of `results` many, that
the table numbered `table` gives the tuple at position `pos`. -/
def tableEntry (results table pos : Nat) : Nat :=
  if results == 0 then 0 else (table / results ^ pos) % results

/-- The tables from `domain` tuples to results whose sizes are `sizes`,
each with its size, the largest of its results', smallest first, then by
number; none if there are more than `limit`. -/
def tablesBySize (domain : Nat) (sizes : Array Nat) (limit : Nat) : Option (Array (Nat × Nat)) :=
  let r := sizes.size
  let count := r ^ domain
  if count > limit then none else
  let tables := (List.range count).toArray.map fun j =>
    (j, (List.range domain).foldl (init := 0) fun m p => max m (sizes[tableEntry r j p]!))
  some (tables.qsort fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 < b.1))

/-- What `spaceOf` throws for a slot with more values than the limit, for
`tooManyMsg`. -/
def tooManyMarker : String := "#too-many"

/-- The space of a procedure for the bound `n` (`Space`), with each slot's
values, smallest first, then, if `tests` is not 0, as many random values
beyond the bound (`extrasOf`), and its shape, and the slots of its
uninterpreted functions `funs`, after the others; or the variable whose type is not
enumerable, and why. `hidden` are the types whose unspecified values some
atom reads, each with what names it. -/
def spaceOf (shapes : Name → Option DataShape) (n : Nat) (vars : Array SlotVar) (hidden : Array (Name × PTy))
    (funs : Array FunVar := #[]) (tests : Nat := 0) (seed : UInt64 := 0) :
    Except (Option Name × String) (Space × Array (Array EVal) × Array Shape × Array FunSlot) := do
  let own := vars.filter (!·.defined)
  let copied := own.filter fun v => (Symbol.ofRole v.sig.role).copied
  let all := own.map (fun v => (v.sig.name, v.pty)) ++ copied.map (fun v => (primed v.sig.name, v.pty)) ++ hidden
  let visible := own.size + copied.size
  let shapesOf ← all.zipIdx.mapM fun ((x, t), i) => match shapeOf shapes n t with
    | .ok s => pure s
    | .error why => throw (if i < visible then some x else none, why)
  -- A slot with more values than the limit is refused before they are
  -- listed (`F0644`).
  if shapesOf.any (·.estimate n > maxBehaviours) then throw (none, tooManyMarker)
  -- With testing, each slot's values are followed by random ones beyond
  -- the bound; a second copy has its original's.
  let extras := all.zipIdx.map fun ((_, t), i) =>
    if tests == 0 then #[] else extrasOf shapes n t tests (splitMix (seed + i.toUInt64 * 0x2545F4914F6CDD1D)).2
  let ordered : Array (List (EVal × Nat)) := (shapesOf.zip extras).zipIdx.map fun ((sh, ex), i) =>
    let ex := if own.size ≤ i && i < visible then
        (own.findIdx? (fun (v : SlotVar) => v.sig.name == copied[i - own.size]!.sig.name)).map (extras[·]!) |>.getD ex
      else ex
    sh.ordered n ++ ex.toList
  let primeOf := (List.range (all.size + funs.size)).toArray.map fun i =>
    if h : i < own.size then
      (copied.findIdx? (·.sig.name == own[i].sig.name)).map (own.size + ·)
    else none
  let outputs := (List.range own.size).toArray.filter fun i => own[i]!.sig.role == .output
  -- Each function's slot, after the others.
  let mut fslots : Array FunSlot := #[]
  let mut fsizes : Array (Array Nat) := #[]
  for f in funs, k in [0:funs.size] do
    let shape (t : PTy) := match shapeOf shapes n t with
      | .ok s => pure s
      | .error why => throw (none, why)
    let ps ← f.params.mapM shape
    let r ← shape f.result
    if (ps.push r).any (·.estimate n > maxBehaviours) then throw (none, tooManyMarker)
    let params := ps.map fun s => (s.ordered n).toArray
    let results := (r.ordered n).toArray
    let domain := params.foldl (· * ·.size) 1
    -- More interpretations than the limit: the slot holds none, and
    -- `Space.behaviours` counts them all (`interpretations`).
    let tables := (tablesBySize domain (results.map (·.2)) maxBehaviours).getD #[]
    fslots := fslots.push { name := f.name, slot := all.size + k, params := params.map (·.map (·.1)), results := results.map (·.1)
                            tables := tables.map (·.1), exhausted := ps.all (·.exhausted n) && r.exhausted n
                            count := results.size ^ domain }
    fsizes := fsizes.push (tables.map (·.2))
  let sp : Space := { names := all.map (·.1) ++ funs.map (·.name), sizes := ordered.map (·.toArray.map (·.2)) ++ fsizes
                      primeOf, outputs, hidden := hidden.size + funs.size, bound := n }
  return (sp, ordered.map (·.toArray.map (·.1)), shapesOf, fslots)

/-- How many assignments the enumeration of a procedure searches, at
most: the product of its variables' and hidden slots' counts, its
functions' interpretations among them, and, if determinism is checked,
of their second copies' too
(`check::enumeration_limit`). -/
def Space.behaviours (sp : Space) (determinism : Bool) (funs : Array FunSlot := #[]) : Nat :=
  let primes := sp.primeOf.filterMap id
  (List.range sp.names.size).foldl (init := 1) fun acc i =>
    if !determinism && primes.contains i then acc
    else match funs.find? (·.slot == i) with
      | some f => acc * f.count
      -- Not the random values beyond the bound, which testing draws from.
      | none => acc * sp.within i sp.bound

/-- Whether every slot of `slots` holds every value of its type within the
bound. -/
def exhaustedAll (shapes : Array Shape) (n : Nat) (slots : Array Nat) : Bool :=
  slots.all fun i => (shapes[i]?.map (·.exhausted n)).getD true

/-- What enumerating a procedure found: its results, each marked bounded
as `classify` says, and the bound. -/
structure Enumerated where
  results : Array CheckResult := #[]
  bound : Nat := 0
  /-- Every slot's values are all of its type's: the results are decided. -/
  exact : Bool := true
  /-- Some checks were tested beyond the bound too. -/
  tested : Bool := false
  deriving Inhabited

/-- The results of enumerating the checks of `alone`, without testing, and
of `both`, with testing beyond the bound, together; `keep` selects the
results to report. -/
def Enumerated.merge (n : Nat) (alone both : Option Enumerated) (keep : CheckResult → Bool) : Enumerated :=
  { results := ((alone.map (·.results)).getD #[] ++ (both.map (·.results)).getD #[]).filter keep, bound := n
    exact := (alone.map (·.exact)).getD true && (both.map (·.exact)).getD true
    tested := both.any (!·.exact) }


/-! ## Messages -/

/-- A procedure, or a global expectation, `subject`, written as it is shown,
whose enumeration would search more than `maxBehaviours` assignments
(`F0644`): `count` of them, or, if `estimated`, more than the limit, since
a variable has more values than it, which are not listed. -/
def tooManyMsg (subject : String) (count n : Nat) (estimated : Bool := false) : Msg :=
  { code? := some "F0644", headline :=
      if estimated then s!"{subject} has a slot whose type, without its invariants, has more than {maxBehaviours} values up to size {n}, too many to enumerate"
      else s!"{subject} has {count} behaviours up to size {n}, too many to enumerate"
    label? := some "too many behaviours"
    notes := #[s!"note: enumeration searches at most {maxBehaviours} behaviours, counting a second copy of each for determinism",
      "help: lower `fren.enumeration.size`, or have the solver check it"] }

/-- `subject` quantifies over a type with more than `maxBehaviours`
values up to size `n` (`Reqs/Check#quantifiers-up-to-the-bound`), which
enumeration does not list (`F0644`). -/
def quantifiedTooManyMsg (subject : String) (n : Nat) : Msg :=
  { code? := some "F0644", headline :=
      s!"{subject} has a quantifier over a type with more than {maxBehaviours} values up to size {n}, too many to enumerate"
    label? := some "too many values"
    notes := #[s!"note: enumeration evaluates a quantifier at each of its type's values up to the bound, at most {maxBehaviours} of them",
      "note: a type's values are counted without its patterns",
      "help: lower `fren.enumeration.size`, give the quantifier a guard with a domain, or have the solver check it"] }

/-- Why a component that applies the generic function `f`, which has no
body, cannot be enumerated (`check::enumerable`): each instance is a
function of its own, which enumeration does not enumerate. -/
def genericNotEnumerable (f : Name) : String :=
  s!"it applies the generic function `{showComp f}`, which has no body"

/-- Why a procedure that applies a recursive function whose body indexes
a sequence cannot be enumerated (`F0645`). -/
def recursiveIndexWhy : String :=
  "it applies a recursive function that indexes a sequence, whose value out of range enumeration cannot give"

/-- `subject` cannot be enumerated, for the reason `why` (`F0645`). -/
def notEnumerableMsg (subject why : String) : Msg :=
  { code? := some "F0645", headline := s!"{subject} cannot be enumerated: {why}", label? := some "not enumerable"
    notes := #["note: enumeration cannot apply an uninterpreted function with a contract or type parameters, nor evaluate an index within a recursive function",
      "help: have the solver or testing check it"] }

/-- The checks of `subject` that enumeration decided only up to the bound
`n` (`F0646`): `passed` of them hold for every behaviour up to size `n`,
and `tests` random tests found no counterexample beyond it, if they ran. -/
def boundedMsg (subject : String) (passed n : Nat) (tests : Option Nat := none) : Msg :=
  let testing := match tests with
    | some t => s!", and for {t} random tests"
    | none => ""
  { code? := some "F0646"
    headline := s!"{passed} {if passed == 1 then "check" else "checks"} of {subject} {if passed == 1 then "holds" else "hold"} \
      for every behaviour up to size {n}{testing}"
    notes := #["note: not every behaviour was enumerated, so this is weaker than a proof"] }

/-- Why the slot `x` cannot be enumerated, its type's `why` (`notEnumerable`):
a variable's, or a hidden slot's, the type of a table or `match`. -/
def notEnumerableWhy (x? : Option Name) (why : String) : String :=
  match x? with
  | none => s!"a table or `match` has a value of the type {why}, which is not enumerable"
  | some x => s!"`{x}` has the type {why}, which is not enumerable"

/-- The message about the checks that hold up to the bound, if any
(`F0646`), of `e`'s results, of a procedure shown as `subject`, whose
checks of `tested` were tested beyond the bound too. -/
def Enumerated.boundedMsg? (e : Enumerated) (subject : String) (tested : Tested) : Option Msg :=
  let bounded := e.results.filter fun r => r.verdict == .pass && r.bounded?.isSome
  if bounded.isEmpty then none
  else some (boundedMsg subject bounded.size e.bound
    (if e.tested && bounded.any tested.covers then some testCount else none))

/-- The size bound, `fren.enumeration.size`, is too large (`F0154`). -/
def sizeTooLargeMsg (n : Nat) : Msg :=
  { code? := some "F0154", headline := s!"enumeration size {n} is too large", label? := some s!"more than {maxSize}"
    notes := #[s!"note: `fren.enumeration.size` is at most {maxSize}"] }
where
  maxSize : Nat := 64

/-- The default size bound (`fren.enumeration.size`). -/
def defaultSize : Nat := 3

/-- The largest size bound. -/
def maxSize : Nat := 64

end Fren.Core.Enumeration
