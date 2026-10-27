-- keep-sorted start
import FrenCore.Guards
import FrenCore.Mentions
-- keep-sorted end

/-!
# Meaning (`Reqs/Lang/Meaning`)

The meaning of one layer of an expression, as total functions: a value
(`Value`), a layer (`Head`), an environment (`Env`), and `step`, the value
of a layer from its environment and its parts' values. `Expr.eval` folds
`step` over a tree of layers, the start of an evaluator that both front
ends can share. `Impls/Meaning` interprets the core's abstract type and
functions with these definitions, and proves `lang::node` of them. No front
end evaluates through it yet.

The values that the spec fixes (`fixedValue?`) are read through a `Ctx`:
what the declarations of a `Program`, evaluated in order, give a layer
(`Program.context`). They are given for some layers and left unspecified
for the others, as `lang::fixed_specified?` allows:

- the operators `not`, `iff`, `-` (negation and subtraction), `+`, `*`,
  `div` and `mod` (by a divisor other than `0`), and `<`, `<=`, `>` and
  `>=`, over integers; `=` and `!=` over plain values (`Value.plain`);
  `++` over two strings or two lists; `at_most_one?` and `exactly_one?`,
  at any parts; the pattern test `is`; indexing in range (`[]`); and a
  field read (`.`);
- the methods `abs`, `min` and `max` of integers, and `len` of a string
  or a list;
- a binder, at a path of variants and positions (`binderValue?`);
- a `match` or table, by the first arm that fires;
- a constant or a defined function, by its body (`bodyValue`), where each
  of its layers is specified.

Every other operator and method is unspecified.
-/

namespace Fren.Core.Meaning

/-- A value (`lang::Value`): a `Bool`, an integer, a string, a list as
`nil` and `cons`, or a variant, record or newtype `c` with its payload's or
fields' values as a list. -/
inductive Value where
  | b (x : Bool)
  | i (n : Int)
  | s (x : String)
  | nil
  | cons (head tail : Value)
  | c (name : String) (payload : Value)
  deriving DecidableEq, Inhabited, Repr

/-- `vs` as a list value. -/
def Value.ofList : List Value → Value
  | [] => .nil
  | v :: vs => .cons v (Value.ofList vs)

/-- The members of a list value, and `none` for any other value. -/
def Value.toList? : Value → Option (List Value)
  | .nil => some []
  | .cons v rest => (Value.toList? rest).map (v :: ·)
  | _ => none

/-- One layer of an expression (`lang::Head`): its form, with everything in
it that is not an expression. -/
inductive Head where
  | literal (v : Value)
  | bound (v : Value)
  | constant (c : String)
  | variable (x : String)
  | definition (x : String)
  | binder (b : String)
  | construction (c order : String)
  | method (m : String)
  | uninterpreted (f : String)
  | defined (f : String)
  | op (o s : String)
  deriving DecidableEq, Inhabited, Repr

/-- An expression, as a tree of layers. A definition of a `let` is a part of
each `definition` layer that mentions it. -/
inductive Expr where
  | node (head : Head) (parts : List Expr)
  deriving Inhabited, Repr

/-- An environment (`lang::Env`): a behaviour and an interpretation, read
as the values of variables and bound names (`lookup`), of uninterpreted
functions (`meaning`), and of layers that the language leaves unspecified
(`unspecified`). Every three such functions are an environment, so a
theorem over every `Env` holds in every behaviour. -/
structure Env where
  lookup : String → Value
  meaning : String → List Value → Value
  unspecified : Head → List Value → Value
  deriving Inhabited

/-- A declaration of the spec being read (`lang::Program`): a constant, as a
definition without parameters, or a defined function, with its parameters
and its body; or a record, with its fields in order. Declarations come in
the order the spec reads them, and a body applies only earlier ones, so
evaluation is well-founded on the declaration's position. -/
inductive Decl where
  | definition (name : String) (params : List String) (body : Expr)
  | record (name : String) (fields : List String)
  deriving Inhabited

/-- The spec being read: its declarations, in order. -/
abbrev Program := List Decl

/-- What the declarations before a point give a layer: the value of each
constant and defined function at its arguments, where it is specified, and
each record's fields. -/
structure Ctx where
  value : String → List Value → Option Value
  fields : String → Option (List String)

/-- No declarations. -/
def Ctx.empty : Ctx := ⟨fun _ _ => none, fun _ => none⟩

variable {ctx : Ctx}

/-! ## Parts and connectives -/

/-- The value of the part at position `k`, and `nil` where there is none
(`lang::part`). -/
def part (vs : List Value) (k : Int) : Value := if 0 ≤ k then vs[k.toNat]?.getD .nil else .nil

/-- The operator of a layer, and `""` for a layer that is not an operator. -/
def Head.operator : Head → String
  | .op o _ => o
  | _ => ""

def connective (o : String) : Bool := o == "and" || o == "or" || o == "when" || o == "unless" || o == "if"

/-- The operators whose value is always specified (`lang::total?`). -/
def total (o : String) : Bool := connective o || o == "at_most_one?" || o == "exactly_one?"

/-- What guards a connective's second part (`lang::second_guard`). -/
def secondGuard (o : String) : GuardedOperand :=
  if o == "or" then .orRight else if o == "when" then .whenBody else if o == "unless" then .unlessBody
  else if o == "if" then .thenBranch else .andRight

/-- Whether `v` is `true`. -/
def Value.isTrue (v : Value) : Bool := v == .b true

/-- Whether the operand `g`, guarded by the condition `c`, is evaluated
(`lang::guard`). -/
def evaluated (g : GuardedOperand) (c : Value) : Bool := g.guard c.isTrue (!c.isTrue)

/-- The value of the connective `o` at its parts' values
(`lang::connective_value`). -/
def connectiveValue (o : String) (vs : List Value) : Value :=
  let c := (part vs 0).isTrue
  let second := part vs 1
  if o == "and" then (if c then second else .b false)
  else if o == "or" then (if c then .b true else second)
  else if o == "when" then (if c then second else .b true)
  else if o == "unless" then (if c then .b true else second)
  else if c then second else part vs 2

/-! ## Patterns

The static part of a `match`, `Op("match", s)`, is its arms' patterns, and
that of a pattern test, `Op("is", s)`, its pattern, written as Fren writes
patterns, with a binder written `_`, a variant by its qualified path, as
its construction names it, and the arms' patterns separated by `;`:
`Option::Some(_); Option::None` (`Reqs/Lang/Patterns#patterns-as-text`).
A name of one segment, not applied, is a constant, matched by its value
in the declarations before the layer (`Ctx`); applied, as `Some(_)`, it
does not decode, since a variant is written qualified. `Pattern.decode` reads only
`_`, `true` and `false`, integer literals, ranges with literal bounds,
string literals without escapes, variants, constants and or-patterns. Any
other text does not decode, and then no arm matches, so the choice is
unspecified rather than wrong. -/

inductive Pattern where
  /-- `_` or a binder: any value. -/
  | wild
  /-- A literal: the value it denotes. -/
  | lit (v : Value)
  /-- The integers from `lo` to `hi`, each bound included where there is one. -/
  | range (lo hi : Option Int)
  /-- The variant `c`, whose payload's values match `args`. -/
  | ctor (c : String) (args : List Pattern)
  /-- What any of the alternatives matches. -/
  | alt (ps : List Pattern)
  /-- A constant: its value, where it is specified. -/
  | const (c : String)
  deriving Inhabited, Repr

mutual
/-- Whether `p` matches `v`. -/
def Pattern.matches (ctx : Ctx) : Pattern → Value → Bool
  | .wild, _ => true
  | .lit v, w => v == w
  | .range lo hi, .i n => (lo.all (· ≤ n)) && (hi.all (n ≤ ·))
  | .range _ _, _ => false
  | .ctor c ps, .c c' l => c == c' && Pattern.matchesList ctx ps l
  | .ctor _ _, _ => false
  | .alt ps, v => Pattern.matchesAny ctx ps v
  | .const c, v => ctx.value c [] == some v

/-- Whether `ps` match the members of the list value `l`, one each. -/
def Pattern.matchesList (ctx : Ctx) : List Pattern → Value → Bool
  | [], .nil => true
  | p :: ps, .cons v rest => p.matches ctx v && Pattern.matchesList ctx ps rest
  | _, _ => false

/-- Whether one of `ps` matches `v`. -/
def Pattern.matchesAny (ctx : Ctx) : List Pattern → Value → Bool
  | [], _ => false
  | p :: ps, v => p.matches ctx v || Pattern.matchesAny ctx ps v
end

mutual
/-- The constants that `p` names. -/
def Pattern.constants : Pattern → List String
  | .const c => [c]
  | .ctor _ ps => Pattern.constantsList ps
  | .alt ps => Pattern.constantsList ps
  | _ => []

def Pattern.constantsList : List Pattern → List String
  | [] => []
  | p :: ps => p.constants ++ Pattern.constantsList ps
end

/-- Whether every constant that `ps` name has a value in `ctx`: where one
does not, what they match is not known. -/
def Pattern.known (ctx : Ctx) (ps : List Pattern) : Bool :=
  (Pattern.constantsList ps).all fun c => (ctx.value c []).isSome

namespace Pattern

def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == ':' || c == '?' || c == '!'

def skipWs (cs : List Char) : List Char := cs.dropWhile Char.isWhitespace

/-- An integer literal, possibly negated, at the start of `cs`. -/
def readInt (cs : List Char) : Option (Int × List Char) :=
  let (neg, rest) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let digits := rest.takeWhile Char.isDigit
  if digits.isEmpty then none
  else (String.ofList digits).toNat?.map fun n => (if neg then -(n : Int) else n, rest.drop digits.length)

/-- A string literal's contents and what follows it, after its opening `"`.
A literal with an escape does not decode: its text is not its value. -/
def readString : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | '"' :: rest, acc => some (String.ofList acc.reverse, rest)
  | '\\' :: _, _ => none
  | c :: rest, acc => readString rest (c :: acc)

/-- The upper bound of a range that starts at `lo`, after its `..`. -/
def readRange (lo : Option Int) (cs : List Char) : Option (Pattern × List Char) :=
  match cs with
  | '=' :: rest => (readInt rest).map fun (hi, rest) => (.range lo (some hi), rest)
  | _ => match readInt cs with
    | some (hi, rest) => some (.range lo (some (hi - 1)), rest)
    | none => some (.range lo none, cs)

mutual
/-- An or-pattern at the start of `cs`, within `fuel` nested patterns. -/
def readOr : Nat → List Char → Option (Pattern × List Char)
  | 0, _ => none
  | fuel + 1, cs => do
    let (p, rest) ← readPrimary fuel cs
    match readAlts fuel (skipWs rest) with
    | some ([], rest) => some (p, rest)
    | some (ps, rest) => some (.alt (p :: ps), rest)
    | none => none

/-- The alternatives after the first, each after a `|`. -/
def readAlts : Nat → List Char → Option (List Pattern × List Char)
  | 0, _ => none
  | fuel + 1, '|' :: cs => do
    let (p, rest) ← readPrimary fuel cs
    let (ps, rest) ← readAlts fuel (skipWs rest)
    some (p :: ps, rest)
  | _ + 1, cs => some ([], cs)

/-- A pattern other than an or-pattern. -/
def readPrimary : Nat → List Char → Option (Pattern × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | '"' :: rest => (readString rest []).map fun (s, rest) => (.lit (.s s), rest)
    | '.' :: '.' :: '=' :: rest => (readInt rest).map fun (hi, rest) => (.range none (some hi), rest)
    | cs@(c :: _) =>
      if c.isDigit || c == '-' then do
        let (n, rest) ← readInt cs
        match rest with
        | '.' :: '.' :: rest => readRange (some n) rest
        | _ => some (.lit (.i n), rest)
      else
        let name := cs.takeWhile identChar
        let rest := cs.drop name.length
        let s := String.ofList name
        if name.isEmpty then none
        else if s == "_" then some (.wild, rest)
        else if s == "true" then some (.lit (.b true), rest)
        else if s == "false" then some (.lit (.b false), rest)
        else match skipWs rest with
          -- A variant is written by its qualified path, as its construction
          -- names it: an applied name of one segment does not decode, since
          -- it would match no construction.
          | '(' :: rest =>
            if (s.splitOn "::").length ≤ 1 then none
            else (readArgs fuel rest).map fun (ps, rest) => (.ctor s ps, rest)
          -- A name of one segment, not applied, is a constant: a binder is
          -- written `_`.
          | _ => some (if (s.splitOn "::").length ≤ 1 then .const s else .ctor s [], rest)
    | [] => none

/-- A payload's patterns, separated by `,`, up to the closing `)`. -/
def readArgs : Nat → List Char → Option (List Pattern × List Char)
  | 0, _ => none
  | fuel + 1, cs => do
    let (p, rest) ← readOr fuel cs
    match skipWs rest with
    | ',' :: rest => do
      let (ps, rest) ← readArgs fuel rest
      some (p :: ps, rest)
    | ')' :: rest => some ([p], rest)
    | _ => none
end

/-- Patterns separated by `;`, to the end of `cs`. -/
def readList : Nat → List Char → Option (List Pattern)
  | 0, _ => none
  | fuel + 1, cs => do
    let (p, rest) ← readOr fuel cs
    match skipWs rest with
    | [] => some [p]
    | ';' :: rest => (readList fuel rest).map (p :: ·)
    | _ => none

/-- The patterns that the static part `s` writes, or `none` where it does
not write patterns as above. -/
def decode (s : String) : Option (List Pattern) := readList (s.length + 1) s.toList

end Pattern

-- A name of one segment is a constant.
#guard (Pattern.decode "ZERO; _").isSome
-- An unqualified variant does not decode, so the choice is unspecified
-- rather than matching nothing.
#guard (Pattern.decode "Some(_); _").isNone
#guard (Pattern.decode "Option::Some(Pair(_, _)); _").isNone
-- An escape is not its text: `"\n"` does not decode, so it matches no `"n"`.
#guard (Pattern.decode "\"\\n\"").isNone
#guard (Pattern.decode "Option::Some(_); Option::None | 0..=5; \"a;b\"").isSome

/-! ## Arms -/

def choice (o : String) : Bool := o == "match" || o == "table"

/-- The position of arm `i`'s guard (`lang::guard_at`); its body is just after it. -/
def guardAt (i : Nat) : Nat := 1 + 2 * i

def armGuard (vs : List Value) (i : Nat) : Value := part vs (guardAt i)

def armBody (vs : List Value) (i : Nat) : Value := part vs (guardAt i + 1)

/-- Whether the pattern of arm `i` of the choice `h` matches `v`
(`lang::arm_matches?`): every row of a table does. -/
def armMatches (ctx : Ctx) (h : Head) (i : Int) (v : Value) : Bool :=
  match h with
  | .op "table" _ => true
  | .op "match" s => match Pattern.decode s with
    | some ps => if 0 ≤ i ∧ Pattern.known ctx ps then (ps[i.toNat]?.map (·.matches ctx v)).getD false else false
    | none => false
  | _ => false

/-- Arm `i` exists and is open: its pattern matches the scrutinee's value
(`lang::arm_open?`). -/
def armOpen (ctx : Ctx) (h : Head) (vs : List Value) (i : Nat) : Bool :=
  choice h.operator && decide (guardAt i + 1 < vs.length)
    && (h.operator == "table" || armMatches ctx h i (part vs 0))

/-- Arm `i` is open and its guard holds. -/
def armHolds (ctx : Ctx) (h : Head) (vs : List Value) (i : Nat) : Bool := armOpen ctx h vs i && (armGuard vs i).isTrue

/-- No arm before arm `i` fires. -/
def noneBefore (ctx : Ctx) (h : Head) (vs : List Value) (i : Nat) : Bool := (List.range i).all fun j => !armHolds ctx h vs j

/-- Arm `i` fires: it is open, its guard holds, and no earlier arm fires. -/
def armFires (ctx : Ctx) (h : Head) (vs : List Value) (i : Nat) : Bool := armHolds ctx h vs i && noneBefore ctx h vs i

/-- The arm that fires, if one does. -/
def firstFired (ctx : Ctx) (h : Head) (vs : List Value) : Option Nat := (List.range vs.length).find? (armHolds ctx h vs)

/-- The positions of arm `i`'s guard and body that are not evaluated. -/
def armUnevaluated (ctx : Ctx) (h : Head) (vs : List Value) (i : Nat) : List Int :=
  (if armOpen ctx h vs i && noneBefore ctx h vs i then [] else [(guardAt i : Int)])
    ++ (if armFires ctx h vs i then [] else [(guardAt i + 1 : Int)])

/-- Of the arms after the third, the positions of the guards and bodies
that are not evaluated (`lang::later_unevaluated`). -/
def laterUnevaluated (ctx : Ctx) (h : Head) (vs : List Value) : List Int :=
  (List.range' 3 vs.length).flatMap (armUnevaluated ctx h vs)

/-- Of the first three arms, the positions of the guards and bodies that
are not evaluated. -/
def statedUnevaluated (ctx : Ctx) (h : Head) (vs : List Value) : List Int :=
  armUnevaluated ctx h vs 0 ++ armUnevaluated ctx h vs 1 ++ armUnevaluated ctx h vs 2

/-- The positions of a choice's parts that it does not evaluate. -/
def choiceUnevaluated (ctx : Ctx) (h : Head) (vs : List Value) : List Int :=
  statedUnevaluated ctx h vs ++ (if choice h.operator && vs.length > 7 then laterUnevaluated ctx h vs else [])


/-! ## Arms, by position -/

theorem armHolds_lt {h : Head} {vs : List Value} {i : Nat} (hh : armHolds ctx h vs i = true) : i < vs.length := by
  simp only [armHolds, armOpen, guardAt, Bool.and_eq_true, decide_eq_true_eq] at hh
  omega

theorem firstFired_eq_some {h : Head} {vs : List Value} {i : Nat} :
    firstFired ctx h vs = some i ↔ armFires ctx h vs i = true := by
  simp only [firstFired, List.find?_range_eq_some, armFires, noneBefore, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, List.mem_range]
  constructor
  · rintro ⟨hh, _, hb⟩; exact ⟨hh, hb⟩
  · rintro ⟨hh, hb⟩; exact ⟨hh, armHolds_lt hh, hb⟩

theorem armFires_zero (h : Head) (vs : List Value) : armFires ctx h vs 0 = armHolds ctx h vs 0 := by
  simp [armFires, noneBefore]

theorem armFires_one (h : Head) (vs : List Value) : armFires ctx h vs 1 = (!armHolds ctx h vs 0 && armHolds ctx h vs 1) := by
  simp [armFires, noneBefore, List.range_succ, Bool.and_comm]

theorem armFires_two (h : Head) (vs : List Value) :
    armFires ctx h vs 2 = (!armHolds ctx h vs 0 && !armHolds ctx h vs 1 && armHolds ctx h vs 2) := by
  simp [armFires, noneBefore, List.range_succ, Bool.and_comm, Bool.and_assoc]

theorem noneBefore_zero (h : Head) (vs : List Value) : noneBefore ctx h vs 0 = true := by
  simp [noneBefore]

theorem noneBefore_one (h : Head) (vs : List Value) : noneBefore ctx h vs 1 = !armFires ctx h vs 0 := by
  simp [noneBefore, armFires_zero]

theorem noneBefore_two (h : Head) (vs : List Value) :
    noneBefore ctx h vs 2 = (!armFires ctx h vs 0 && !armFires ctx h vs 1) := by
  cases h0 : armHolds ctx h vs 0 <;> simp [noneBefore, armFires_zero, armFires_one, List.range_succ, h0]

/-- The later arms' positions are those after the first three's. -/
theorem le_of_mem_laterUnevaluated {h : Head} {vs : List Value} {k : Int} (hk : k ∈ laterUnevaluated ctx h vs) :
    7 ≤ k := by
  simp only [laterUnevaluated, List.mem_flatMap, List.mem_range', armUnevaluated, guardAt, List.mem_append] at hk
  obtain ⟨i, ⟨j, _, rfl⟩, hm⟩ := hk
  rcases hm with hm | hm <;> split at hm <;> simp at hm <;> omega

/-- The arm that fires is one of the first three, or a later one of a
choice of more than seven parts. -/
theorem firstFired_cases (h : Head) (vs : List Value) :
    firstFired ctx h vs = if armFires ctx h vs 0 then some 0 else if armFires ctx h vs 1 then some 1
      else if armFires ctx h vs 2 then some 2 else if vs.length > 7 then firstFired ctx h vs else none := by
  by_cases h0 : armFires ctx h vs 0
  · simp [h0, firstFired_eq_some]
  by_cases h1 : armFires ctx h vs 1
  · simp [h0, h1, firstFired_eq_some]
  by_cases h2 : armFires ctx h vs 2
  · simp [h0, h1, h2, firstFired_eq_some]
  by_cases hl : vs.length > 7
  · simp [h0, h1, h2, hl]
  simp only [h0, h1, h2, hl, Bool.false_eq_true, if_false]
  cases e : firstFired ctx h vs with
  | none => rfl
  | some i =>
    have hf := firstFired_eq_some.1 e
    have hl' := armHolds_lt (Bool.and_eq_true _ _ ▸ hf).1
    have hh := (Bool.and_eq_true _ _ ▸ hf).1
    simp only [armHolds, armOpen, guardAt, Bool.and_eq_true, decide_eq_true_eq] at hh
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all

/-! ## Fixed values -/

/-- The value of the variant, record or newtype `c` built from its parts'
values (`lang::construct`). -/
def construct (c : String) (vs : List Value) : Value := .c c (Value.ofList vs)

mutual
/-- Whether `v` is a `Bool`, an integer or a string, or a variant, record
or newtype of such values. A list may stand for a set, whose order the
spec does not fix, so `=` on one is not structural, and is not stated. -/
def Value.plain : Value → Bool
  | .b _ | .i _ | .s _ => true
  | .c _ payload => Value.plainList payload
  | .nil | .cons _ _ => false

/-- Whether `l` is a list of plain values: a payload's or fields' values. -/
def Value.plainList : Value → Bool
  | .nil => true
  | .cons v rest => v.plain && Value.plainList rest
  | _ => false
end

/-- The position of `x` in `l`. -/
def indexOf? (l : List String) (x : String) : Option Nat := l.findIdx? (· == x)

/-- The value of the field `f` of `v`: a record's by its name, from the
record's declaration, and a newtype's `0`. -/
def fieldValue? (ctx : Ctx) (f : String) : Value → Option Value
  | .c r payload => do
    let l ← payload.toList?
    let k ← (match f.toNat? with
      | some k => some k
      | none => (ctx.fields r).bind (indexOf? · f))
    l[k]?
  | _ => none

/-- The number of `true`s among `vs`. -/
def countTrue (vs : List Value) : Nat := (vs.filter Value.isTrue).length

/-- The value of the operator `o`, with static part `s`, at its operands'
values, where this model states it. -/
def opValue? (ctx : Ctx) (o s : String) (vs : List Value) : Option Value :=
  match o, vs with
  | "not", [.b x] => some (.b !x)
  | "iff", [.b x, .b y] => some (.b (x == y))
  | "-", [.i n] => some (.i (-n))
  | "+", [.i a, .i b] => some (.i (a + b))
  | "-", [.i a, .i b] => some (.i (a - b))
  | "*", [.i a, .i b] => some (.i (a * b))
  | "div", [.i a, .i b] => if b = 0 then none else some (.i (a / b))
  | "mod", [.i a, .i b] => if b = 0 then none else some (.i (a % b))
  | "<", [.i a, .i b] => some (.b (decide (a < b)))
  | "<=", [.i a, .i b] => some (.b (decide (a ≤ b)))
  | ">", [.i a, .i b] => some (.b (decide (a > b)))
  | ">=", [.i a, .i b] => some (.b (decide (a ≥ b)))
  | "=", [a, b] => if a.plain && b.plain then some (.b (a == b)) else none
  | "!=", [a, b] => if a.plain && b.plain then some (.b (a != b)) else none
  | "[..]", vs => some (Value.ofList vs)
  | "[]", [q, .i k] => q.toList?.bind fun l => if 0 ≤ k then l[k.toNat]? else none
  | ".", [v] => fieldValue? ctx s v
  | "++", [.s a, .s b] => some (.s (a ++ b))
  | "++", [a, b] => match a.toList?, b.toList? with
    | some l, some r => some (Value.ofList (l ++ r))
    | _, _ => none
  | "at_most_one?", vs => some (.b (decide (countTrue vs ≤ 1)))
  | "exactly_one?", vs => some (.b (decide (countTrue vs = 1)))
  | "is", [v] => (Pattern.decode s).bind fun
    | [p] => if Pattern.known ctx [p] then some (.b (p.matches ctx v)) else none
    | _ => none
  | _, _ => none

/-- The value of the method `m` at its receiver's and arguments' values,
where this model states it. -/
def methodValue? (m : String) (vs : List Value) : Option Value :=
  match m, vs with
  | "abs", [.i n] => some (.i (if n < 0 then -n else n))
  | "min", [.i a, .i b] => some (.i (if a ≤ b then a else b))
  | "max", [.i a, .i b] => some (.i (if a ≥ b then a else b))
  | "len", [.s x] => some (.i x.length)
  | "len", [v] => v.toList?.map fun l => .i l.length
  | _, _ => none

/-- The value at the path `p` within `v`: each step a variant, record or
newtype's name and a position in its payload or fields, as `Pair.1`. -/
def binderValue? : List String → Value → Option Value
  | [], v => some v
  | c :: k :: rest, .c c' payload => do
    let k ← k.toNat?
    if c == c' then
      let l ← payload.toList?
      binderValue? rest (← l[k]?)
    else none
  | _, _ => none

/-- The value that the spec fixes for the layer `h` at its parts' values,
where this model states it (`lang::fixed_value`, `lang::fixed_specified?`):
a choice by the body of the arm that fires. -/
def fixedValue? (ctx : Ctx) (h : Head) (vs : List Value) : Option Value :=
  match h with
  | .op o s => if choice o then (firstFired ctx h vs).map (armBody vs) else opValue? ctx o s vs
  | .method m => methodValue? m vs
  | .binder b => binderValue? (if b.isEmpty then [] else b.splitOn ".") (part vs 0)
  | .constant c => if vs.isEmpty then ctx.value c [] else none
  | .defined f => ctx.value f vs
  | _ => none

def fixedValue (ctx : Ctx) (h : Head) (vs : List Value) : Value := (fixedValue? ctx h vs).getD .nil

def fixedSpecified (ctx : Ctx) (h : Head) (vs : List Value) : Bool := (fixedValue? ctx h vs).isSome

/-! ## One layer -/

/-- The value of a layer from its environment and its parts' values
(`lang::step`). -/
def step (ctx : Ctx) (h : Head) (env : Env) (vs : List Value) : Value :=
  match h with
  | .literal v | .bound v => v
  | .variable x => env.lookup x
  | .definition _ => part vs 0
  | .construction c _ => construct c vs
  | .uninterpreted f => env.meaning f vs
  | .op o _ =>
    if connective o then connectiveValue o vs
    else if choice o then match firstFired ctx h vs with
      | some i => armBody vs i
      | none => env.unspecified h []
    else if total o || fixedSpecified ctx h vs then fixedValue ctx h vs
    else env.unspecified h vs
  | _ => if fixedSpecified ctx h vs then fixedValue ctx h vs else env.unspecified h vs

/-- What a layer reads of its environment at its own name (`lang::node`'s
`read`). -/
def read (h : Head) (env : Env) (vs : List Value) : Value :=
  match h with
  | .variable x => env.lookup x
  | .uninterpreted f => env.meaning f vs
  | _ => .nil

/-- What a layer mentions, from what its parts mention (`lang::mentioned_by`). -/
def mentionedBy (h : Head) (parts : List Mention) : List Mention :=
  match h with
  | .literal _ | .bound _ | .constant _ => []
  | .variable x => [.var x]
  | .uninterpreted f => parts ++ [.fn f]
  | _ => parts

/-- Whether a layer's value is not the unspecified one. -/
def specified (ctx : Ctx) (h : Head) (vs : List Value) : Bool :=
  match h with
  | .literal _ | .bound _ | .variable _ | .definition _ | .construction _ _ | .uninterpreted _ => true
  | .op o _ => if choice o then (firstFired ctx h vs).isSome else total o || fixedSpecified ctx h vs
  | _ => fixedSpecified ctx h vs

/-- The positions of a layer's parts that it does not evaluate. -/
def unevaluated (ctx : Ctx) (h : Head) (vs : List Value) : List Int :=
  let o := h.operator
  (if connective o && !evaluated (secondGuard o) (part vs 0) then [1] else [])
    ++ (if o == "if" && !evaluated .elseBranch (part vs 0) then [2] else [])
    ++ (if choice o then choiceUnevaluated ctx h vs else [])

/-- Whether a layer is defined, from the positions of its parts that are
not: it is specified, and every part it evaluates is defined. -/
def defined (ctx : Ctx) (h : Head) (vs : List Value) (undefinedParts : List Int) : Bool :=
  specified ctx h vs && undefinedParts.all (· ∈ unevaluated ctx h vs)

/-- The value of an operator's layer, with the arms of a choice after the
first three by `fixedValue`, as `lang::step` states it. -/
theorem step_op (o s : String) (env : Env) (vs : List Value) :
    step ctx (.op o s) env vs =
      if connective o then connectiveValue o vs
      else if choice o then
        (if armFires ctx (.op o s) vs 0 then armBody vs 0
        else if armFires ctx (.op o s) vs 1 then armBody vs 1
        else if armFires ctx (.op o s) vs 2 then armBody vs 2
        else if (choice o && decide (vs.length > 7)) = true ∧ fixedSpecified ctx (.op o s) vs = true then
          fixedValue ctx (.op o s) vs
        else env.unspecified (.op o s) [])
      else if total o = true ∨ fixedSpecified ctx (.op o s) vs = true then fixedValue ctx (.op o s) vs
      else env.unspecified (.op o s) vs := by
  by_cases hc : connective o
  · simp [step, hc]
  by_cases hch : choice o
  · simp only [step, hc, hch, Bool.false_eq_true, if_false, if_true, Bool.true_and, fixedSpecified, fixedValue,
      fixedValue?]
    rw [firstFired_cases]
    by_cases h0 : armFires ctx (.op o s) vs 0
    · simp [h0]
    by_cases h1 : armFires ctx (.op o s) vs 1
    · simp [h0, h1]
    by_cases h2 : armFires ctx (.op o s) vs 2
    · simp [h0, h1, h2]
    by_cases hl : vs.length > 7
    · simp only [h0, h1, h2, hl, Bool.false_eq_true, if_false, if_true, decide_true]
      cases firstFired ctx (.op o s) vs <;> simp
    · simp [h0, h1, h2, hl]
  · simp [step, hc, hch, Bool.or_eq_true]

/-- A choice is specified where one of its first three arms fires, or,
with more than seven parts, where its value is fixed: where some arm fires. -/
theorem firstFired_isSome (h : Head) (vs : List Value) :
    (firstFired ctx h vs).isSome = (armFires ctx h vs 0 || armFires ctx h vs 1 || armFires ctx h vs 2
      || (choice h.operator && decide (vs.length > 7) && fixedSpecified ctx h vs)) := by
  have hf : choice h.operator = true → fixedSpecified ctx h vs = (firstFired ctx h vs).isSome := by
    intro hc
    cases h <;> simp_all [Head.operator, choice, fixedSpecified, fixedValue?]
  rw [firstFired_cases]
  by_cases h0 : armFires ctx h vs 0 <;> by_cases h1 : armFires ctx h vs 1 <;> by_cases h2 : armFires ctx h vs 2 <;>
    simp only [h0, h1, h2, if_true, if_false, Bool.false_eq_true, Option.isSome_some, Bool.true_or, Bool.or_true,
      Bool.false_or] <;> try rfl
  by_cases hl : vs.length > 7
  · by_cases hc : choice h.operator
    · simp [hl, hc, hf hc]
    · have : firstFired ctx h vs = none := by
        cases e : firstFired ctx h vs with
        | none => rfl
        | some i =>
          have := (Bool.and_eq_true _ _ ▸ firstFired_eq_some.1 e).1
          simp [armHolds, armOpen, hc] at this
      simp [hl, hc, this]
  · simp [hl]

/-! ## Laws

The laws of `Reqs/Lang/MeaningLaws`, of these definitions. `unevaluated`
is checked by the solver only. -/

/-- `frame`: a specified layer reads its environment only at its own name. -/
theorem step_frame {h : Head} {vs : List Value} {e₁ e₂ : Env} (hs : specified ctx h vs = true)
    (hr : read h e₁ vs = read h e₂ vs) : step ctx h e₁ vs = step ctx h e₂ vs := by
  cases h with
  | «variable» x => simpa [step, read] using hr
  | uninterpreted f => simpa [step, read] using hr
  | op o s =>
    simp only [specified] at hs
    simp only [step]
    split
    · rfl
    · split
      · rename_i hc
        simp only [hc, if_true] at hs
        cases e : firstFired ctx (.op o s) vs <;> simp_all
      · rename_i hc
        simp only [hc, Bool.false_eq_true, if_false, Bool.or_eq_true] at hs
        simp only [Bool.or_eq_true, hs, if_true]
  | _ => simp_all [step, specified]

/-- `own_mentioned`: a layer that mentions nothing reads the same in every
environment. -/
theorem read_own_mentioned {h : Head} {vs : List Value} {ps : List Mention} (e₁ e₂ : Env)
    (hm : mentionedBy h ps = []) : read h e₁ vs = read h e₂ vs := by
  cases h <;> simp_all [mentionedBy, read]

/-- `frame_mentioned`: environments that give a specified layer different
values differ at something that it mentions. -/
theorem step_frame_mentioned {h : Head} {vs : List Value} {ps : List Mention} {e₁ e₂ : Env}
    (hs : specified ctx h vs = true) (hne : step ctx h e₁ vs ≠ step ctx h e₂ vs) :
    (∃ x, Mention.var x ∈ mentionedBy h ps ∧ e₁.lookup x ≠ e₂.lookup x)
      ∨ (∃ f, Mention.fn f ∈ mentionedBy h ps ∧ e₁.meaning f vs ≠ e₂.meaning f vs) := by
  have hr : read h e₁ vs ≠ read h e₂ vs := fun hr => hne (step_frame hs hr)
  cases h <;> simp_all [read, mentionedBy]

/-- `field_order`: a construction's value does not depend on the order in
which its fields are written. -/
theorem step_field_order (c o₁ o₂ : String) (e₁ e₂ : Env) (vs : List Value) :
    step ctx (.construction c o₁) e₁ vs = step ctx (.construction c o₂) e₂ vs := rfl

/-! ## Expressions -/

/-- The value of `e` in `env`: `step` at each layer, from its parts' values. -/
def Expr.eval (ctx : Ctx) (env : Env) : Expr → Value
  | .node h ps => step ctx h env (ps.attach.map fun ⟨p, _⟩ => p.eval ctx env)

/-- Whether `e` is defined in `env`: each layer is, from which of its parts
are. -/
def Expr.defined (ctx : Ctx) (env : Env) : Expr → Bool
  | .node h ps =>
    let vs := ps.attach.map fun ⟨p, _⟩ => p.eval ctx env
    let undefinedParts := ((ps.attach.map fun ⟨p, _⟩ => p.defined ctx env).zipIdx.filter (!·.1)).map fun (_, k) => (k : Int)
    Meaning.defined ctx h vs undefinedParts

theorem Expr.eval_node (env : Env) (h : Head) (ps : List Expr) :
    (Expr.node h ps).eval ctx env = step ctx h env (ps.map (·.eval ctx env)) := by
  simp [Expr.eval]

/-- What `e` mentions, perhaps more than once (`lang::mentioned_by` at each
layer). -/
def Expr.mentioned : Expr → List Mention
  | .node h ps => mentionedBy h (ps.attach.flatMap fun ⟨p, _⟩ => p.mentioned)

/-- Every layer of `e` is specified in `env`. -/
def Expr.specifiedIn (ctx : Ctx) (env : Env) : Expr → Prop
  | .node h ps => specified ctx h (ps.map (·.eval ctx env)) = true ∧ ∀ p : {p // p ∈ ps}, p.1.specifiedIn ctx env
decreasing_by have := List.sizeOf_lt_of_mem p.2; simp_wf; omega

/-- The laws over the whole tree (`Reqs/Lang/MeaningLaws#the-whole-tree`): an
expression that mentions nothing, and each of whose layers is specified,
has the same value in every environment, by `step_frame` and
`read_own_mentioned` at each layer. -/
theorem Expr.eval_unmentioned (e₁ e₂ : Env) : ∀ (e : Expr), e.mentioned = [] → e.specifiedIn ctx e₁ →
    e.eval ctx e₁ = e.eval ctx e₂
  | .node h ps, hm, hs => by
    unfold Expr.specifiedIn at hs
    unfold Expr.mentioned at hm
    have parts : (ps.attach.flatMap fun ⟨p, _⟩ => p.mentioned) = [] → ps.map (·.eval ctx e₁) = ps.map (·.eval ctx e₂) := by
      intro hp
      apply List.map_congr_left
      intro p hp'
      have hpm : p.mentioned = [] := by
        rw [List.flatMap_eq_nil_iff] at hp
        exact hp ⟨p, hp'⟩ (List.mem_attach _ _)
      exact Expr.eval_unmentioned e₁ e₂ p hpm (hs.2 ⟨p, hp'⟩)
    rw [eval_node, eval_node]
    cases h with
    | literal v => rfl
    | bound v => rfl
    | constant c =>
      have : ps = [] := by
        cases ps with
        | nil => rfl
        | cons _ _ => simp [specified, fixedSpecified, fixedValue?] at hs
      subst this
      exact step_frame (by simpa using hs.1) rfl
    | «variable» x => simp [mentionedBy] at hm
    | uninterpreted f => simp [mentionedBy] at hm
    | _ =>
      rw [parts hm] at hs ⊢
      exact step_frame hs.1 (read_own_mentioned (ps := []) e₁ e₂ rfl)
termination_by e => e
decreasing_by
  all_goals simp_wf
  all_goals have := List.sizeOf_lt_of_mem hp'
  all_goals omega

/-! ## Declarations

The values of constants and defined functions, by the order of the
declarations: each definition is evaluated with the declarations before
it, so the evaluation is well-founded on the declaration's position, and
needs no fuel. -/

/-- The value of `e` where each of its layers is specified, with the
variables that `b` binds, and `none` elsewhere: the value of a
definition's body at its parameters' values. A body reads no other
variable, and applies no uninterpreted function. -/
def bodyValue (ctx : Ctx) (b : List (String × Value)) : Expr → Option Value
  | .node h ps => do
    let vs ← ps.attach.mapM fun ⟨p, _⟩ => bodyValue ctx b p
    match h with
    | .variable x => b.lookup x
    | .uninterpreted _ => none
    | h => if specified ctx h vs then some (step ctx h default vs) else none

/-- `ctx`, and the declaration `d` after it. A function's value at
arguments of the wrong number is unspecified. -/
def Ctx.extend (ctx : Ctx) : Decl → Ctx
  | .definition n ps body =>
    { ctx with value := fun m vs =>
        if m = n then (if vs.length = ps.length then bodyValue ctx (ps.zip vs) body else none) else ctx.value m vs }
  | .record r fs => { ctx with fields := fun m => if m = r then some fs else ctx.fields m }

/-- What `ctx` and the declarations `ds` after it give a layer. -/
def Program.ctxFrom (ctx : Ctx) : Program → Ctx
  | [] => ctx
  | d :: ds => Program.ctxFrom (ctx.extend d) ds

/-- What the whole program gives a layer (`lang::fixed_value`). -/
def Program.context (p : Program) : Ctx := Program.ctxFrom .empty p

/-- A definition, with the declarations before it, its parameters and its
body. -/
abbrev Definition := Ctx × List String × Expr

/-- The value of the definition `d` at `vs`. -/
def Definition.value : Option Definition → List Value → Option Value
  | some (c, ps, body), vs => if vs.length = ps.length then bodyValue c (ps.zip vs) body else none
  | none, _ => none

/-- The last definition named `n` among `ds`, after `ctx`, or `found`. -/
def Program.definitionFrom (ctx : Ctx) (n : String) (found : Option Definition) : Program → Option Definition
  | [] => found
  | d :: ds => Program.definitionFrom (ctx.extend d) n
      (match d with
        | .definition m ps body => if m = n then some (ctx, ps, body) else found
        | .record _ _ => found) ds

/-- The definition named `n` (`lang::parameters`, `lang::definition_value`). -/
def Program.definition (p : Program) (n : String) : Option Definition := Program.definitionFrom .empty n none p

theorem Program.ctxFrom_value (n : String) (vs : List Value) :
    ∀ (ds : Program) (ctx : Ctx) (found : Option Definition), ctx.value n vs = Definition.value found vs →
      (Program.ctxFrom ctx ds).value n vs = Definition.value (Program.definitionFrom ctx n found ds) vs
  | [], _, _, h => h
  | d :: ds, ctx, found, h => by
    apply Program.ctxFrom_value n vs ds
    cases d with
    | definition m ps body =>
      by_cases e : m = n
      · subst e; simp [Ctx.extend, Definition.value]
      · have e' : n ≠ m := fun h => e h.symm
        simp [Ctx.extend, e, e', h]
    | record r fs => simpa [Ctx.extend] using h

/-- A constant's or defined function's value is its definition's body at
its arguments. -/
theorem Program.ctx_value (p : Program) (n : String) (vs : List Value) :
    (Program.context p).value n vs = Definition.value (Program.definition p n) vs :=
  Program.ctxFrom_value n vs p .empty none rfl

theorem mapM_some {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α} {ys : List β}, (∀ a ∈ l, ∀ y, f a = some y → g a = y) → l.mapM f = some ys → l.map g = ys
  | [], ys, _, h => by simp_all
  | a :: l, ys, hg, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    simp [hg a (by simp) y hy, mapM_some (fun a' h' => hg a' (by simp [h'])) hys]

/-- Substitution (`lang::fixed_value`'s `declared`): where a body is
specified, its value is its expression's, in every environment that binds
its variables as `b` does. -/
theorem bodyValue_eval (b : List (String × Value)) (env : Env)
    (hb : ∀ x w, b.lookup x = some w → env.lookup x = w) :
    ∀ (e : Expr) (v : Value), bodyValue ctx b e = some v → e.eval ctx env = v
  | .node h ps, v, he => by
    unfold bodyValue at he
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨vs, hvs, hv⟩ := he
    have hparts : ps.map (·.eval ctx env) = vs := by
      have := mapM_some (g := fun (p : {p // p ∈ ps}) => p.1.eval ctx env)
        (fun ⟨p, hp⟩ _ y hy => bodyValue_eval b env hb p y hy) hvs
      simpa using this
    rw [Expr.eval_node, hparts]
    cases h with
    | «variable» x => exact hb x v hv
    | uninterpreted f => simp at hv
    | _ =>
      dsimp only at hv
      split at hv
      · injection hv with hv
        all_goals exact (step_frame (e₁ := env) (e₂ := default) (by assumption) rfl).trans hv
      · cases hv
termination_by e => e
decreasing_by
  all_goals simp_wf
  all_goals have := List.sizeOf_lt_of_mem hp
  all_goals omega

theorem lookup_zip {x : String} {w : Value} :
    ∀ {ps : List String} {vs : List Value}, (ps.zip vs).lookup x = some w →
      ∃ i, ∃ (h₁ : i < ps.length) (h₂ : i < vs.length), ps[i] = x ∧ vs[i] = w
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, v :: vs, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    split at h
    · rename_i e
      injection h with h
      exact ⟨0, by simp, by simp, by simpa using (beq_iff_eq.1 e).symm, h⟩
    · obtain ⟨i, h₁, h₂, hx, hw⟩ := lookup_zip h
      exact ⟨i + 1, by simp; omega, by simp; omega, hx, hw⟩

/-- An environment binds the parameters `ps` to the values `vs`. -/
def Binds (env : Env) (ps : List String) (vs : List Value) : Prop :=
  ps.length = vs.length ∧ ∀ i (h₁ : i < ps.length) (h₂ : i < vs.length), env.lookup ps[i] = vs[i]

/-- A constant's or defined function's value, where it is specified, is its
body's, in every environment that binds its parameters to the arguments. -/
theorem definition_eval (p : Program) (n : String) (vs : List Value) (v : Value) (env : Env)
    (hv : (Program.context p).value n vs = some v) :
    match Program.definition p n with
    | some (c, ps, body) => Binds env ps vs → body.eval c env = v
    | none => False := by
  rw [Program.ctx_value] at hv
  cases e : Program.definition p n with
  | none => simp [e, Definition.value] at hv
  | some d =>
    obtain ⟨c, ps, body⟩ := d
    simp only [e, Definition.value] at hv
    split at hv
    · intro hb
      apply bodyValue_eval (ps.zip vs) env _ body v hv
      intro x w hl
      obtain ⟨i, h₁, h₂, rfl, rfl⟩ := lookup_zip hl
      exact hb.2 i h₁ h₂
    · simp at hv

/-- A constant has the same value in every environment, where it is
specified. -/
theorem step_constant {c : String} {vs : List Value} (e₁ e₂ : Env) (hs : specified ctx (.constant c) vs = true) :
    step ctx (.constant c) e₁ vs = step ctx (.constant c) e₂ vs :=
  step_frame hs rfl

-- The choices whose patterns do not decode are unspecified, not wrong: with
-- `Some(_)` unqualified, `match o { Some(_) => 1, _ => 2 }` is not `2`.
#guard specified .empty (.op "match" "Some(_); _") [.c "Option::Some" (.cons (.i 0) .nil), .b true, .i 1, .b true, .i 2]
  == false
#guard fixedValue? .empty (.op "match" "Option::Some(_); _") [.c "Option::Some" (.cons (.i 0) .nil), .b true, .i 1,
  .b true, .i 2] == some (.i 1)
-- The choices whose patterns do not decode are unspecified, not wrong.
#guard specified .empty (.op "match" "ZERO; _") [.i 0, .b true, .i 1, .b true, .i 2] == false
#guard armMatches .empty (.op "match" "\"\\n\"") 0 (.s "n") == false
#guard armMatches .empty (.op "match" "Option::Some(_); Option::None") 1 (.c "Option::None" .nil)

-- With `const ZERO: Int := 0`, `match x { ZERO => 1, _ => 2 }` at `x = 0`
-- is `1`, and `fn double(n: Int): Int := 2 * n` at `3` is `6`.
def exampleProgram : Program :=
  [.definition "ZERO" [] (.node (.literal (.i 0)) []),
   .definition "double" ["n"] (.node (.op "*" "") [.node (.literal (.i 2)) [], .node (.variable "n") []]),
   .record "Point" ["x", "y"]]
#guard fixedValue? (Program.context exampleProgram) (.op "match" "ZERO; _") [.i 0, .b true, .i 1, .b true, .i 2] == some (.i 1)
#guard fixedValue? (Program.context exampleProgram) (.defined "double") [.i 3] == some (.i 6)
#guard fixedValue? (Program.context exampleProgram) (.op "." "y") [construct "Point" [.i 1, .i 2]] == some (.i 2)

end Fren.Core.Meaning
