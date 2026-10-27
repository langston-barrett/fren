-- keep-sorted start
import FrenCore.Guards
import FrenCore.Mentions
import FrenCore.Scope
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

The values that the spec fixes (`fixedValue?`) are given for some layers
and left unspecified for the others, as `lang::fixed_specified?` allows:

- the operators `not`, `iff`, `-` (negation and subtraction), `+`, `*`,
  `div` and `mod` (by a divisor other than `0`), and `<`, `<=`, `>` and
  `>=`, over integers; `=` and `!=` over two `Bool`s, two integers or two
  strings; `++` over two strings or two lists; `at_most_one?` and
  `exactly_one?`, at any parts; and the pattern test `is`;
- the methods `abs`, `min` and `max` of integers, and `len` of a string
  or a list;
- a binder, at a path of variants and positions (`binderValue?`);
- a `match` or table, by the first arm that fires.

Constants, defined functions and every other operator and method are
unspecified: their values depend on the spec's declarations, which no
layer holds.
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

/-- The layer that a name written alone is, from the binding it resolves to
(`lang::named_head`): a variable, a parameter, an instance, a global
expectation's binder or a bound name is read from the environment, a name
of a `let` or `where` is its definition, a binder is named by where its
pattern declares it, and anything else, a constant or a variant above
all, is a constant by its full path. -/
def namedHead (b : Binding String String) : Head :=
  match b.kind with
  | .input | .output | .parameter | .inst | .expectBinder | .boundName => .variable b.name
  | .definition => .definition b.name
  | .patternBinder => .binder b.target
  | _ => .constant b.target

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
`Pattern.decode` reads only `_`, `true` and `false`, integer literals,
ranges with literal bounds, string literals without escapes, qualified
variants and or-patterns. Any other text, such as a name of one segment,
which may be a constant, does not decode, and then no arm matches, so the
choice is unspecified rather than wrong. -/

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
  deriving Inhabited, Repr

mutual
/-- Whether `p` matches `v`. -/
def Pattern.matches : Pattern → Value → Bool
  | .wild, _ => true
  | .lit v, w => v == w
  | .range lo hi, .i n => (lo.all (· ≤ n)) && (hi.all (n ≤ ·))
  | .range _ _, _ => false
  | .ctor c ps, .c c' l => c == c' && Pattern.matchesList ps l
  | .ctor _ _, _ => false
  | .alt ps, v => Pattern.matchesAny ps v

/-- Whether `ps` match the members of the list value `l`, one each. -/
def Pattern.matchesList : List Pattern → Value → Bool
  | [], .nil => true
  | p :: ps, .cons v rest => p.matches v && Pattern.matchesList ps rest
  | _, _ => false

/-- Whether one of `ps` matches `v`. -/
def Pattern.matchesAny : List Pattern → Value → Bool
  | [], _ => false
  | p :: ps, v => p.matches v || Pattern.matchesAny ps v
end

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
        -- A name of one segment may be a binder or a constant, whose value
        -- needs the spec's declarations.
        else if (s.splitOn "::").length ≤ 1 then none
        else match skipWs rest with
          | '(' :: rest => do
            let (ps, rest) ← readArgs fuel rest
            some (.ctor s ps, rest)
          | _ => some (.ctor s [], rest)
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

-- A name of one segment may be a constant: with `const ZERO: Int := 0`,
-- `match x { ZERO => 1, _ => 2 }` at `x = 0` is unspecified here, not `2`.
#guard (Pattern.decode "ZERO; _").isNone
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
def armMatches (h : Head) (i : Int) (v : Value) : Bool :=
  match h with
  | .op "table" _ => true
  | .op "match" s => match Pattern.decode s with
    | some ps => if 0 ≤ i then (ps[i.toNat]?.map (·.matches v)).getD false else false
    | none => false
  | _ => false

/-- Arm `i` exists and is open: its pattern matches the scrutinee's value
(`lang::arm_open?`). -/
def armOpen (h : Head) (vs : List Value) (i : Nat) : Bool :=
  choice h.operator && decide (guardAt i + 1 < vs.length)
    && (h.operator == "table" || armMatches h i (part vs 0))

/-- Arm `i` is open and its guard holds. -/
def armHolds (h : Head) (vs : List Value) (i : Nat) : Bool := armOpen h vs i && (armGuard vs i).isTrue

/-- No arm before arm `i` fires. -/
def noneBefore (h : Head) (vs : List Value) (i : Nat) : Bool := (List.range i).all fun j => !armHolds h vs j

/-- Arm `i` fires: it is open, its guard holds, and no earlier arm fires. -/
def armFires (h : Head) (vs : List Value) (i : Nat) : Bool := armHolds h vs i && noneBefore h vs i

/-- The arm that fires, if one does. -/
def firstFired (h : Head) (vs : List Value) : Option Nat := (List.range vs.length).find? (armHolds h vs)

/-- The positions of arm `i`'s guard and body that are not evaluated. -/
def armUnevaluated (h : Head) (vs : List Value) (i : Nat) : List Int :=
  (if armOpen h vs i && noneBefore h vs i then [] else [(guardAt i : Int)])
    ++ (if armFires h vs i then [] else [(guardAt i + 1 : Int)])

/-- Of the arms after the third, the positions of the guards and bodies
that are not evaluated (`lang::later_unevaluated`). -/
def laterUnevaluated (h : Head) (vs : List Value) : List Int :=
  (List.range' 3 vs.length).flatMap (armUnevaluated h vs)

/-- Of the first three arms, the positions of the guards and bodies that
are not evaluated. -/
def statedUnevaluated (h : Head) (vs : List Value) : List Int :=
  armUnevaluated h vs 0 ++ armUnevaluated h vs 1 ++ armUnevaluated h vs 2

/-- The positions of a choice's parts that it does not evaluate. -/
def choiceUnevaluated (h : Head) (vs : List Value) : List Int :=
  statedUnevaluated h vs ++ (if choice h.operator && vs.length > 7 then laterUnevaluated h vs else [])


/-! ## Arms, by position -/

theorem armHolds_lt {h : Head} {vs : List Value} {i : Nat} (hh : armHolds h vs i = true) : i < vs.length := by
  simp only [armHolds, armOpen, guardAt, Bool.and_eq_true, decide_eq_true_eq] at hh
  omega

theorem firstFired_eq_some {h : Head} {vs : List Value} {i : Nat} :
    firstFired h vs = some i ↔ armFires h vs i = true := by
  simp only [firstFired, List.find?_range_eq_some, armFires, noneBefore, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, List.mem_range]
  constructor
  · rintro ⟨hh, _, hb⟩; exact ⟨hh, hb⟩
  · rintro ⟨hh, hb⟩; exact ⟨hh, armHolds_lt hh, hb⟩

theorem armFires_zero (h : Head) (vs : List Value) : armFires h vs 0 = armHolds h vs 0 := by
  simp [armFires, noneBefore]

theorem armFires_one (h : Head) (vs : List Value) : armFires h vs 1 = (!armHolds h vs 0 && armHolds h vs 1) := by
  simp [armFires, noneBefore, List.range_succ, Bool.and_comm]

theorem armFires_two (h : Head) (vs : List Value) :
    armFires h vs 2 = (!armHolds h vs 0 && !armHolds h vs 1 && armHolds h vs 2) := by
  simp [armFires, noneBefore, List.range_succ, Bool.and_comm, Bool.and_assoc]

theorem noneBefore_zero (h : Head) (vs : List Value) : noneBefore h vs 0 = true := by
  simp [noneBefore]

theorem noneBefore_one (h : Head) (vs : List Value) : noneBefore h vs 1 = !armFires h vs 0 := by
  simp [noneBefore, armFires_zero]

theorem noneBefore_two (h : Head) (vs : List Value) :
    noneBefore h vs 2 = (!armFires h vs 0 && !armFires h vs 1) := by
  cases h0 : armHolds h vs 0 <;> simp [noneBefore, armFires_zero, armFires_one, List.range_succ, h0]

/-- The later arms' positions are those after the first three's. -/
theorem le_of_mem_laterUnevaluated {h : Head} {vs : List Value} {k : Int} (hk : k ∈ laterUnevaluated h vs) :
    7 ≤ k := by
  simp only [laterUnevaluated, List.mem_flatMap, List.mem_range', armUnevaluated, guardAt, List.mem_append] at hk
  obtain ⟨i, ⟨j, _, rfl⟩, hm⟩ := hk
  rcases hm with hm | hm <;> split at hm <;> simp at hm <;> omega

/-- The arm that fires is one of the first three, or a later one of a
choice of more than seven parts. -/
theorem firstFired_cases (h : Head) (vs : List Value) :
    firstFired h vs = if armFires h vs 0 then some 0 else if armFires h vs 1 then some 1
      else if armFires h vs 2 then some 2 else if vs.length > 7 then firstFired h vs else none := by
  by_cases h0 : armFires h vs 0
  · simp [h0, firstFired_eq_some]
  by_cases h1 : armFires h vs 1
  · simp [h0, h1, firstFired_eq_some]
  by_cases h2 : armFires h vs 2
  · simp [h0, h1, h2, firstFired_eq_some]
  by_cases hl : vs.length > 7
  · simp [h0, h1, h2, hl]
  simp only [h0, h1, h2, hl, Bool.false_eq_true, if_false]
  cases e : firstFired h vs with
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

/-- Whether `a` and `b` are both `Bool`s, both integers or both strings. -/
def sameScalar : Value → Value → Bool
  | .b _, .b _ | .i _, .i _ | .s _, .s _ => true
  | _, _ => false

/-- The number of `true`s among `vs`. -/
def countTrue (vs : List Value) : Nat := (vs.filter Value.isTrue).length

/-- The value of the operator `o`, with static part `s`, at its operands'
values, where this model states it. -/
def opValue? (o s : String) (vs : List Value) : Option Value :=
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
  | "=", [a, b] => if sameScalar a b then some (.b (a == b)) else none
  | "!=", [a, b] => if sameScalar a b then some (.b (a != b)) else none
  | "++", [.s a, .s b] => some (.s (a ++ b))
  | "++", [a, b] => match a.toList?, b.toList? with
    | some l, some r => some (Value.ofList (l ++ r))
    | _, _ => none
  | "at_most_one?", vs => some (.b (decide (countTrue vs ≤ 1)))
  | "exactly_one?", vs => some (.b (decide (countTrue vs = 1)))
  | "is", [v] => (Pattern.decode s).bind fun
    | [p] => some (.b (p.matches v))
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
def fixedValue? (h : Head) (vs : List Value) : Option Value :=
  match h with
  | .op o s => if choice o then (firstFired h vs).map (armBody vs) else opValue? o s vs
  | .method m => methodValue? m vs
  | .binder b => binderValue? (if b.isEmpty then [] else b.splitOn ".") (part vs 0)
  | _ => none

def fixedValue (h : Head) (vs : List Value) : Value := (fixedValue? h vs).getD .nil

def fixedSpecified (h : Head) (vs : List Value) : Bool := (fixedValue? h vs).isSome

/-! ## One layer -/

/-- The value of a layer from its environment and its parts' values
(`lang::step`). -/
def step (h : Head) (env : Env) (vs : List Value) : Value :=
  match h with
  | .literal v | .bound v => v
  | .variable x => env.lookup x
  | .definition _ => part vs 0
  | .construction c _ => construct c vs
  | .uninterpreted f => env.meaning f vs
  | .op o _ =>
    if connective o then connectiveValue o vs
    else if choice o then match firstFired h vs with
      | some i => armBody vs i
      | none => env.unspecified h []
    else if total o || fixedSpecified h vs then fixedValue h vs
    else env.unspecified h vs
  | _ => if fixedSpecified h vs then fixedValue h vs else env.unspecified h vs

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
def specified (h : Head) (vs : List Value) : Bool :=
  match h with
  | .literal _ | .bound _ | .variable _ | .definition _ | .construction _ _ | .uninterpreted _ => true
  | .op o _ => if choice o then (firstFired h vs).isSome else total o || fixedSpecified h vs
  | _ => fixedSpecified h vs

/-- The positions of a layer's parts that it does not evaluate. -/
def unevaluated (h : Head) (vs : List Value) : List Int :=
  let o := h.operator
  (if connective o && !evaluated (secondGuard o) (part vs 0) then [1] else [])
    ++ (if o == "if" && !evaluated .elseBranch (part vs 0) then [2] else [])
    ++ (if choice o then choiceUnevaluated h vs else [])

/-- Whether a layer is defined, from the positions of its parts that are
not: it is specified, and every part it evaluates is defined. -/
def defined (h : Head) (vs : List Value) (undefinedParts : List Int) : Bool :=
  specified h vs && undefinedParts.all (· ∈ unevaluated h vs)

/-- The value of an operator's layer, with the arms of a choice after the
first three by `fixedValue`, as `lang::step` states it. -/
theorem step_op (o s : String) (env : Env) (vs : List Value) :
    step (.op o s) env vs =
      if connective o then connectiveValue o vs
      else if choice o then
        (if armFires (.op o s) vs 0 then armBody vs 0
        else if armFires (.op o s) vs 1 then armBody vs 1
        else if armFires (.op o s) vs 2 then armBody vs 2
        else if (choice o && decide (vs.length > 7)) = true ∧ fixedSpecified (.op o s) vs = true then
          fixedValue (.op o s) vs
        else env.unspecified (.op o s) [])
      else if total o = true ∨ fixedSpecified (.op o s) vs = true then fixedValue (.op o s) vs
      else env.unspecified (.op o s) vs := by
  by_cases hc : connective o
  · simp [step, hc]
  by_cases hch : choice o
  · simp only [step, hc, hch, Bool.false_eq_true, if_false, if_true, Bool.true_and, fixedSpecified, fixedValue,
      fixedValue?]
    rw [firstFired_cases]
    by_cases h0 : armFires (.op o s) vs 0
    · simp [h0]
    by_cases h1 : armFires (.op o s) vs 1
    · simp [h0, h1]
    by_cases h2 : armFires (.op o s) vs 2
    · simp [h0, h1, h2]
    by_cases hl : vs.length > 7
    · simp only [h0, h1, h2, hl, Bool.false_eq_true, if_false, if_true, decide_true]
      cases firstFired (.op o s) vs <;> simp
    · simp [h0, h1, h2, hl]
  · simp [step, hc, hch, Bool.or_eq_true]

/-- A choice is specified where one of its first three arms fires, or,
with more than seven parts, where its value is fixed: where some arm fires. -/
theorem firstFired_isSome (h : Head) (vs : List Value) :
    (firstFired h vs).isSome = (armFires h vs 0 || armFires h vs 1 || armFires h vs 2
      || (choice h.operator && decide (vs.length > 7) && fixedSpecified h vs)) := by
  have hf : choice h.operator = true → fixedSpecified h vs = (firstFired h vs).isSome := by
    intro hc
    cases h <;> simp_all [Head.operator, choice, fixedSpecified, fixedValue?]
  rw [firstFired_cases]
  by_cases h0 : armFires h vs 0 <;> by_cases h1 : armFires h vs 1 <;> by_cases h2 : armFires h vs 2 <;>
    simp only [h0, h1, h2, if_true, if_false, Bool.false_eq_true, Option.isSome_some, Bool.true_or, Bool.or_true,
      Bool.false_or] <;> try rfl
  by_cases hl : vs.length > 7
  · by_cases hc : choice h.operator
    · simp [hl, hc, hf hc]
    · have : firstFired h vs = none := by
        cases e : firstFired h vs with
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
theorem step_frame {h : Head} {vs : List Value} {e₁ e₂ : Env} (hs : specified h vs = true)
    (hr : read h e₁ vs = read h e₂ vs) : step h e₁ vs = step h e₂ vs := by
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
        cases e : firstFired (.op o s) vs <;> simp_all
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
    (hs : specified h vs = true) (hne : step h e₁ vs ≠ step h e₂ vs) :
    (∃ x, Mention.var x ∈ mentionedBy h ps ∧ e₁.lookup x ≠ e₂.lookup x)
      ∨ (∃ f, Mention.fn f ∈ mentionedBy h ps ∧ e₁.meaning f vs ≠ e₂.meaning f vs) := by
  have hr : read h e₁ vs ≠ read h e₂ vs := fun hr => hne (step_frame hs hr)
  cases h <;> simp_all [read, mentionedBy]

/-- `field_order`: a construction's value does not depend on the order in
which its fields are written. -/
theorem step_field_order (c o₁ o₂ : String) (e₁ e₂ : Env) (vs : List Value) :
    step (.construction c o₁) e₁ vs = step (.construction c o₂) e₂ vs := rfl

/-! ## Expressions -/

/-- An expression, as a tree of layers. A definition of a `let` is a part of
each `definition` layer that mentions it. -/
inductive Expr where
  | node (head : Head) (parts : List Expr)
  deriving Inhabited

/-- The value of `e` in `env`: `step` at each layer, from its parts' values. -/
def Expr.eval (env : Env) : Expr → Value
  | .node h ps => step h env (ps.attach.map fun ⟨p, _⟩ => p.eval env)

/-- Whether `e` is defined in `env`: each layer is, from which of its parts
are. -/
def Expr.defined (env : Env) : Expr → Bool
  | .node h ps =>
    let vs := ps.attach.map fun ⟨p, _⟩ => p.eval env
    let undefinedParts := ((ps.attach.map fun ⟨p, _⟩ => p.defined env).zipIdx.filter (!·.1)).map fun (_, k) => (k : Int)
    Meaning.defined h vs undefinedParts

theorem Expr.eval_node (env : Env) (h : Head) (ps : List Expr) :
    (Expr.node h ps).eval env = step h env (ps.map (·.eval env)) := by
  simp [Expr.eval]

/-- What `e` mentions, perhaps more than once (`lang::mentioned_by` at each
layer). -/
def Expr.mentioned : Expr → List Mention
  | .node h ps => mentionedBy h (ps.attach.flatMap fun ⟨p, _⟩ => p.mentioned)

/-- Every layer of `e` is specified in `env`. -/
def Expr.specifiedIn (env : Env) : Expr → Prop
  | .node h ps => specified h (ps.map (·.eval env)) = true ∧ ∀ p : {p // p ∈ ps}, p.1.specifiedIn env
decreasing_by have := List.sizeOf_lt_of_mem p.2; simp_wf; omega

/-- The laws over the whole tree (`Reqs/Lang/MeaningLaws#the-whole-tree`): an
expression that mentions nothing, and each of whose layers is specified,
has the same value in every environment, by `step_frame` and
`read_own_mentioned` at each layer. -/
theorem Expr.eval_unmentioned (e₁ e₂ : Env) : ∀ (e : Expr), e.mentioned = [] → e.specifiedIn e₁ →
    e.eval e₁ = e.eval e₂
  | .node h ps, hm, hs => by
    unfold Expr.specifiedIn at hs
    unfold Expr.mentioned at hm
    have parts : (ps.attach.flatMap fun ⟨p, _⟩ => p.mentioned) = [] → ps.map (·.eval e₁) = ps.map (·.eval e₂) := by
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
    | constant c => simp [specified, fixedSpecified, fixedValue?] at hs
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

-- The choices whose patterns do not decode are unspecified, not wrong.
#guard specified (.op "match" "ZERO; _") [.i 0, .b true, .i 1, .b true, .i 2] == false
#guard armMatches (.op "match" "\"\\n\"") 0 (.s "n") == false
#guard armMatches (.op "match" "Option::Some(_); Option::None") 1 (.c "Option::None" .nil)

end Fren.Core.Meaning
