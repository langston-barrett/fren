# Expressions

```
expr  := ("when" | "unless") iff "," expr
       | "let" definition ("," definition)* "in" expr
       | ("forall" | "exists") binder+ "," expr
       | iff
binder := "(" DECL+ ":" type ")"
iff   := or ["iff" or]
or    := or "or" and | and
and   := and "and" not | not
not   := "not" not | cmp
cmp   := sum [("=" | "!=" | "in" | "subset") sum]
       | sum (("<" | "<=") sum)+
       | sum ((">" | ">=") sum)+
       | sum "is" pattern
sum   := sum ("+" | "-" | "++" | "union" | "minus") prod | prod
prod  := prod ("*" | "div" | "mod" | "inter" | "join") neg | neg
neg   := "-" neg | atom
atom  := INT | STRING | "true" | "false" | path | IDENT ("." IDENT)+ | "(" expr ")"
       | "if" expr "then" expr "else" expr
       | path "(" expr ("," expr)* ")"
       | path "{" field-init ("," field-init)* [","] "}"
       | atom "." IDENT ["(" expr ("," expr)* ")"]
       | atom "." DIGITS
       | IDENT ("." IDENT)+ "(" expr ("," expr)* ")"
       | "match" atom "{" arm ("," arm)* [","] "}"
       | "table" "{" row ("," row)* [","] "}"
       | "table" atom "{" arm ("," arm)* [","] "}"
       | "{" [expr ("," expr)* [","]] "}"
       | "{" expr "with" field-init ("," field-init)* [","] "}"
field-init := IDENT [":=" expr]
arm   := pattern ["if" iff] "=>" expr
definition := DECL [":" type] ":=" iff
row   := ["|"] (iff | "_") "=>" iff
```

A `let` names subexpressions within its body, and a `where` clause after
a whole constraint does the same for it: see [Local definitions](Let.md).

In `atom "." IDENT`, the atom is one that ends in `)` or `}`, and there
are no spaces around the `.`: after a name, `.` is part of the
[identifier](Lexical.md#identifiers), as in `p.x`. In `atom "." DIGITS`,
which reads the field of a [newtype](#newtypes), the atom may also be a
name, since digits never continue an identifier: `x.0` reads the field
`0` of `x`, and `x.0.0` reads it twice. The notation is [the
grammar's](../Grammar.md#notation), where `DECL` is an identifier that
declares a name, and `DIGITS` decimal digits. Patterns are in [their own
chapter](Patterns.md), and so are quantifiers, `forall` and `exists`, in
[Quantifiers](Quantifiers.md).

## Operators

From lowest to highest precedence, where forms of the same level bind
equally tightly:

| Level | Form | Meaning | Operand types | Result | Associativity |
|---|---|---|---|---|---|
| 1 | `let x := e in B` | `B`, with `x` standing for `e` | any | the type of `B` | right |
| 1 | `when C, D` | C implies D | `Bool` | `Bool` | right |
| 1 | `unless C, D` | not C implies D | `Bool` | `Bool` | right |
| 1 | `forall (x: T), E`, `exists (x: T), E` | [quantifiers](Quantifiers.md): `E` for every value `x` of `T`, or for some | `Bool` | `Bool` | right |
| 2 | `A iff B` | A if and only if B | `Bool` | `Bool` | none |
| 3 | `A or B` | disjunction | `Bool` | `Bool` | left |
| 4 | `A and B` | conjunction | `Bool` | `Bool` | left |
| 5 | `not A` | negation | `Bool` | `Bool` | |
| 6 | `A = B`, `A != B` | equality, disequality | any, both the same, or `Int` and `Nat` | `Bool` | none |
| 6 | `A < B`, `A <= B`, `A > B`, `A >= B` | ordering | `Int` or `Nat`, or both of one other [ordered type](Types.md#ordered-types): `String`, or an enumeration, record or newtype declared [`ordered`](Items.md#ordered-declarations) | `Bool` | [chains](#chained-comparisons) |
| 6 | `A in S` | membership | `T` and `Set<T>` or `Seq<T>`, or a pair `(a, b)` and `Rel<A, B>` | `Bool` | none |
| 6 | `S subset T` | `S` is a subset of `T`, not necessarily strict | `Set<T>`, or `Rel<A, B>` | `Bool` | none |
| 6 | `A is P` | [pattern test](#pattern-tests): the pattern `P` matches `A` | an enumeration, `Bool`, `Int`, `Nat` or `String`, and a pattern | `Bool` | none |
| 7 | `A + B` | addition | `Int` or `Nat`, or one newtype of `Int` or `Nat` | the newtype if both are one, `Nat` if both are, else `Int` | left |
| 7 | `A - B` | subtraction | `Int` or `Nat`, or one newtype of `Int` | the newtype if both are one, else `Int` | left |
| 7 | `A ++ B` | concatenation | `String`, or `Seq<T>` | the same | left |
| 7 | `S union T`, `S minus T` | union, difference | `Set<T>`, or `Rel<A, B>` | the same | left |
| 8 | `A * B` | multiplication | `Int` or `Nat` | `Nat` if both are, else `Int` | left |
| 8 | `A div K`, `A mod K` | [division and remainder](#division-and-remainder) by a constant | `Int` or `Nat` | `Nat` if `A` is one and `K` is positive, else `Int` | left |
| 8 | `S inter T` | intersection | `Set<T>`, or `Rel<A, B>` | the same | left |
| 8 | `R join Q` | composition | `Rel<A, B>` and `Rel<B, C>` | `Rel<A, C>` | left |
| 9 | `-A` | negation | `Int` or `Nat` | `Int` | |

- In `when C, D` and `unless C, D`, `C` ends at the first top-level `,`, and
  `D` extends as far right as possible. `D` may itself be a `when` or
  `unless` without parentheses: `when a?, when b?, c?`. A `when` or `unless`
  that is the operand of another operator must be parenthesized, and so
  must a `let` or a quantifier, whose body also extends as far right as
  possible. A quantifier may likewise be `D`, or have a `when` as its
  body, without them.
- `iff` and `=` agree on `Bool`, but `iff` binds more loosely:
  `a? iff b? = c?` means `a? iff (b? = c?)`.
- Prefix operators, `not` and `-`, apply to everything to their right that
  binds more tightly: `not a? and b?` means `(not a?) and b?`, and
  `x div -2` means `x div (-2)`.
- The `mod` of a remainder is on the line of its left operand, as the `in`
  of a membership is: a `mod` at the start of a line starts a
  [module](Modules.md) (see [Keywords](Lexical.md#keywords)).

`lang::operand` states when an operand can be written without parentheses,
from the precedence of its operator (`inner`) and of the operator it is an
operand of (`outer`), and the associativity of `outer`. A precedence is any
number that orders the operators as the table's levels do, so that the
operators of one level share one. An atom binds
more tightly than any operator, and a prefix operator counts as
right-associative, with its operand on the right.

```fren
pub mod lang

-- `NonAssoc` contains `Assoc`, as "non-associative" does.
set_option fren.lint.enum_variant_names "allow" in
pub enum Assoc { Left, Right, NonAssoc }

pub comp operand {
    in outer: Int        -- the precedence of the operator
    in inner: Int        -- the precedence of its operand's operator
    in assoc: Assoc      -- the associativity of the operator
    in right?            -- the operand is on the operator's right
    pub out bare?        -- the operand can be written without parentheses

    ensure tighter: when inner > outer, bare?
    ensure looser: when inner < outer, not bare?
    ensure left: when inner = outer and assoc = Assoc::Left, bare? iff not right?
    ensure right: when inner = outer and assoc = Assoc::Right, bare? iff right?
    ensure non_assoc: when inner = outer and assoc = Assoc::NonAssoc, not bare?

    expect parenthesize_looser: when bare?, inner >= outer
    expect chains_by_assoc: when inner = outer and bare?,
        (assoc = Assoc::Left and not right?) or (assoc = Assoc::Right and right?)
}
```

So `a? iff b? iff c?` and `x = y = z` are errors, and so is `a? and when
b?, c?`, since `when` binds more loosely than `and`. `x < y < z` is not an
ordering with an ordering as its operand, but one [chained
comparison](#chained-comparisons); `(x < y) = z?` compares the `Bool`
`x < y` with `z?`.

## Chained comparisons

`<` and `<=` chain with each other, and `>` and `>=` with each other, to
any length: `0 <= i < q.len` means `0 <= i and i < q.len`, and `a > b >=
c > d` means `a > b and b >= c and c > d`. Each operand between two
operators is one expression, written once, and is an operand of both. An
expression has no effects, so reading it twice changes nothing. Each
comparison is typed as if written alone, so `lo <= s < hi` compares
`String`s if `s` is one, and values of an [ordered
enumeration](Items.md#enumerations), record or newtype if `s` is one, as in
`Info <= worst < Error`. The `fren` command's message about a
comparison's operands names its operator: in `0 <= i < "a"`, `"a"` is not
an `Int`, as the operands of `<` must be. In Lean, the message is Lean's
type mismatch, at the same operand.

A chain that mixes directions, such as `a < b > c`, is an error: it reads
as a mistake more often than as `a < b and c < b`. So is a chain with `=`,
`!=`, `in`, `subset` or `is`, which do not chain: `a? = b? = c?` would read as
either `a? = b? and b? = c?` or `(a? = b?) = c?`, and those differ. The
message points at the first operator that does not chain, or else at the
first that orders the other way from the first. A comparison in
parentheses is an operand like any other, as in `(a < b) =
c?`. `lang::comparison_chain` states which chains are accepted, from how
many of their operators are of each kind; one operator alone is a
comparison, not a chain:

```fren
pub comp comparison_chain {
    in n_ascending: Nat     -- operators `<` and `<=`
    in n_descending: Nat    -- operators `>` and `>=`
    in n_other: Nat         -- operators `=`, `!=`, `in`, `subset` and `is`

    assume compares: n_ascending + n_descending + n_other >= 1
    pub det out accepted?

    ensure rule: accepted? iff (n_ascending + n_descending + n_other = 1
        or (n_other = 0 and (n_ascending = 0 or n_descending = 0)))

    expect single: when n_ascending + n_descending + n_other = 1, accepted?
    expect one_direction: when accepted?, n_ascending = 0 or n_descending = 0
    expect orderings_only: when accepted? and n_ascending + n_descending + n_other > 1, n_other = 0
}
```

## Mentions

Some rules ask whether an expression *mentions* a variable or an
uninterpreted [function](Items.md#functions): those of [linear
arithmetic](#linear-arithmetic), of the [decidable
core](Decidability.md#strings), and of the
[lint](../Lint/Complexity.md#constant-outputs) `constant_output`. An expression that mentions
neither has the same value in every behaviour, unless it is
unspecified there, as an index out of range within a constant's value is
(see [The whole tree](MeaningLaws.md#the-whole-tree)). What an expression mentions is decided from its parts, as `lang::mentions` states:

- A literal mentions nothing, and neither does a
  [constant](Items.md#constants), a variant without a payload, or any
  other path of more than one segment, such as `m::RATE`.
- A variable mentions itself, and so does a variable of an
  [instance](Instances.md#instance-variables) or a field read from a
  variable. A variable declared as `RATE!` shadows the constant `RATE`
  (see [Shadowing](Components.md#shadowing)), so `RATE` is then a
  variable.
- A [defined output](Components.md#defined-outputs) mentions what its
  definition mentions, a [binder](#matches) what its scrutinee
  mentions, and a name of a [`let` or `where`](Let.md) what its
  definition mentions. A [quantifier's](Quantifiers.md) bound name of a
  listed type mentions nothing: in each instance, it is one value. A bound
  name of any other type, of an [unbounded
  quantifier](Quantifiers.md#unbounded-quantifiers), mentions itself, as
  a variable does: it stands for every value of its type at once.
- A [variant](#variants-with-payloads), a [record literal](#records) or
  a [newtype](#newtypes) built from its value mentions what its arguments
  or fields mention: its value is fixed. So does a [record
  update](#record-updates), which mentions what its record and its new
  values mention.
- A [method](#methods) call mentions what its receiver and arguments
  mention: a method has a fixed meaning.
- An application of an uninterpreted function mentions the function: its
  value is unknown even at fixed arguments.
- An application of a defined function mentions what its arguments
  mention: its value is fixed by theirs.
- Every other expression mentions what its parts mention: an operator,
  `when` and `unless`, a `let`, a quantifier (its body), a conditional, a
  `match` (its scrutinee, and the guards and bodies of its arms), a [table](#tables) (its rows' conditions and
  values), a [pattern
  test](#pattern-tests) (its scrutinee), a [cardinality
  operator](#cardinality) (its arguments), indexing `q[i]`, a field read
  from an expression that is not a name, such as `R { a := x }.a`, and a
  literal of a set, pair or sequence.

Each kind of expression is the head of a [layer](Meaning.md#layers), a
`lang::Head`, and what it mentions is a set of names, of variables and
uninterpreted functions as `Mention`s, given by `mentioned_by`. `lang::mentions` states
it, from the head and what the parts mention together:

```fren
pub comp mentions {
    use self::Head::{Bound, Constant, Construction, Defined, Literal, Method, Uninterpreted, Variable}
    in head: Head
    in parts_mentioned: Set<Mention>  -- what its parts mention, together

    assume leaves: when head is Literal(_) | Bound(_) | Constant(_) | Variable(_), parts_mentioned = {}

    pub det out mentioned: Set<Mention> := mentioned_by(head, parts_mentioned)
    pub det out mentions? := mentioned != {}    -- it mentions a variable or an uninterpreted function

    expect fixed_meaning: when head is Defined(_) | Method(_) | Construction(_, _), mentioned = parts_mentioned
    expect unknown: when head is Variable(_) | Uninterpreted(_), mentions?
    expect bound_fixed: when head is Bound(_), not mentions?
    expect itself: match head {
        Variable(x) => mentioned = {Mention::Var(x)},
        _ => true,
    }

    cover through_parts: parts_mentioned != {} and mentions?
}
```

Each layer of an expression mentions what `lang::mentions` says, so
`lang::node` refines it:

```fren
refine layer_mentions: node refines mentions
```

The parts of a defined output, of a binder and of a name of a `let` or
`where` are its definition, its scrutinee and its definition. The only
part of a `let` is its body, so a definition that the body never
mentions counts for nothing. So `double(3)`, `"abc".len` and `Shape::Circle(2)` mention
nothing, and `s.len`, `double(x)` and `rate(1)` mention something.

## Linear arithmetic

One operand of `*` must mention no variable and no uninterpreted function
(see [Mentions](#mentions)): it is built from literals,
[constants](Items.md#constants), and defined functions and methods applied
to those, such as `2`, `-RATE`, `2 * 3`, `(MAX - MIN)` or `double(3)`. Its
value is then fixed, so the product is linear in the other operand, which
the solver decides. `x * y` is an error, and so is `x * RATE` within a
component that declares a variable `RATE!`, which shadows the constant
(see [Shadowing](Components.md#shadowing)). So is `x * rate(1)`,
with `rate` uninterpreted: its value is unknown even at a fixed argument.
`lang::linear_product` states this, from what each operand mentions:

```fren
pub comp linear_product {
    in a_mentioned: Set<Mention>  -- what the left operand mentions (`lang::mentions`)
    in b_mentioned: Set<Mention>  -- what the right operand mentions

    pub det out accepted?

    ensure rule: accepted? iff (a_mentioned = {} or b_mentioned = {})

    expect scaling: when a_mentioned = {}, accepted?
    expect no_variable_products: when a_mentioned != {} and b_mentioned != {}, not accepted?
}
```

An operand that mentions less never makes a product nonlinear:

```fren
expect fewer_mentions: forall (p q: linear_product),
    when q.a_mentioned subset p.a_mentioned and q.b_mentioned subset p.b_mentioned and p.accepted?,
    q.accepted?
```

A defined function applied to constants scales a product like a literal,
whatever the other operand:

```fren
expect defined_scales: forall (m: node) (p: linear_product),
    when m.head is Head::Defined(_) and m.parts_mentioned = {} and p.a_mentioned = m.mentioned, p.accepted?
```

The rule is what makes the product linear: of an accepted product, one
operand is a *fixed factor*, with the same value in every environment
where it is specified, and so where it is defined, by the [laws of a
layer](MeaningLaws.md). Where it is not, as `get([1], 5)` with `fn get(q: Seq<Int>, i: Int): Int := q[i]`,
a check reports why: the [definedness check](../Check.md#definedness)
reports the index in `get`'s body, as the [precondition
check](../Check.md#preconditions) reports an application outside a
function's preconditions. Here `a` is the layer of the operand that the
rule makes the factor, the left one where the right mentions something,
and `a2` the same layer, with the same parts' values, in any other
environment; that the parts' values are the same follows by induction
(see [The whole tree](MeaningLaws.md#the-whole-tree)):

```fren
expect fixed_factor: forall (p: linear_product) (a a2: node),
    when p.accepted? and p.b_mentioned != {} and p.a_mentioned = a.mentioned
    and a2.head = a.head and a2.values = a.values and a.specified?,
    a2.value = a.value

expect fixed_factor_right: forall (p: linear_product) (b b2: node),
    when p.accepted? and p.a_mentioned != {} and p.b_mentioned = b.mentioned
    and b2.head = b.head and b2.values = b.values and b.specified?,
    b2.value = b.value
```

## Division and remainder

`a div k` and `a mod k` are the quotient and the remainder of `a` divided
by `k`. They are Euclidean, as SMT-LIB's `div` and `mod` and Lean's
`Int.ediv` and `Int.emod` are: the remainder is never negative and is less
than `k.abs`, and `a = (a div k) * k + a mod k`. So `7 div 2` is `3` and
`7 mod 2` is `1`, `-7 div 2` is `-4` and `-7 mod 2` is `1`, and
`7 div -2` is `-3` and `7 mod -2` is `1`. For a positive `k`, `div` rounds
down; for a negative one, up. So `a div -k` is `-(a div k)`, and
`a mod -k` is `a mod k`, as `lang::division` states.

The divisor `k` is an integer literal or a [constant](Items.md#constants),
possibly negated or in parentheses, such as `2`, `-2`, `N` or `-N`, and its
value is not `0`. Dividing by a constant stays within linear integer
arithmetic, which the solver decides, as multiplying by one does (see
[Linear arithmetic](#linear-arithmetic)). So `x div y`, with `y` a
variable, is an error, as `x * y` is. So is `x mod 0`: SMT-LIB leaves
division by zero unspecified, where Lean's is `0`, so the two front ends
would disagree. Any other expression, such as `x div (2 * 3)`, is an error
too: declare a constant for it.

A constant divisor's value must be known when the spec is read, without
evaluating it: the constant's value is an *integer constant expression*,
built from integer literals and constants, of type `Int` or `Nat`, whose
values are integer constant expressions by `+`, `-`, `*`, `div`, `mod`,
`abs`, `min` and `max`, and parentheses. So with `const N: Int := 2 * 4`, `x mod N` is
accepted, but with `const N: Int := "abcd".len`, it is an error.
`lang::divisor` states the rule, from the form of the divisor without its
`-` and parentheses, and its value:

```fren
-- `KnownConstant` is a constant whose value is an integer constant
-- expression, and `UnknownConstant` one whose value is not; `OtherDivisor`
-- is any other expression, such as a variable or `2 * 3`.
pub enum DivisorForm { LiteralDivisor, KnownConstant, UnknownConstant, OtherDivisor }

pub comp divisor {
    use self::DivisorForm::{KnownConstant, LiteralDivisor, OtherDivisor}
    in form: DivisorForm
    in value: Int            -- its value, for a literal or a known constant
    pub det out accepted?

    ensure rule: accepted? iff (form in {LiteralDivisor, KnownConstant} and value != 0)

    expect no_zero: when value = 0, not accepted?
    expect literals: when form = LiteralDivisor and value != 0, accepted?
    expect no_variables: when form = OtherDivisor, not accepted?
}
```

`lang::division` states the laws of `div` and `mod`, for a positive and a
negative divisor. It allows `identity_op` and `modulo_one`, which fire on
`x div 1` and `x mod 1`, since those laws are what the lints rely on:

```fren
const NEGATIVE_DIVISOR: Int := -3

set_option fren.lint.identity_op "allow" in
set_option fren.lint.modulo_one "allow" in
pub comp division {
    in x: Int
    in y: Int

    expect euclidean: x = (x div 3) * 3 + x mod 3
    expect remainder_range: 0 <= x mod 3 < 3
    expect euclidean_negative: x = (x div NEGATIVE_DIVISOR) * NEGATIVE_DIVISOR + x mod NEGATIVE_DIVISOR
    expect remainder_range_negative: 0 <= x mod NEGATIVE_DIVISOR < NEGATIVE_DIVISOR.abs
    expect negated_divisor: x div -3 = -(x div 3) and x mod -3 = x mod 3
    expect multiples: (3 * x) div 3 = x and (3 * x) mod 3 = 0
    expect periodic: (x + 3) mod 3 = x mod 3 and (x + 3) div 3 = x div 3 + 1
    expect rounds_down: (x div 3) * 3 <= x < (x div 3) * 3 + 3
    expect monotone: when x <= y, x div 3 <= y div 3
    expect by_one: x div 1 = x and x mod 1 = 0
}
```

## Natural numbers

`+` and `*` of two `Nat`s are `Nat`s. Of a `Nat` and an `Int`, the `Nat`
is [widened](Types.md#natural-numbers) to an `Int`, as Lean's `binop%`
elaboration inserts `↑`, and the result is an `Int`. `a - b` and `-a` are
always `Int`s, even of `Nat`s, so that Fren never truncates: Lean's
subtraction on `Nat` gives `0` for `3 - 5`, and it never appears in a Fren
spec. Likewise the operands of a comparison or an equality, the branches
of a conditional and the bodies of a `match`'s arms may be a `Nat` and an
`Int`, and the `Nat` is widened: `n = -1` compares two `Int`s, and `if c?
then n else -1` is an `Int`.

An integer literal is a `Nat` where a `Nat` is expected, and an `Int`
elsewhere. A `Nat` is expected for the definition of a defined output,
the value of a constant, a binding, an argument, or the body of a defined
function, whose type is `Nat`; and, where the whole is expected to be a
`Nat`, for the operands of `+` and `*`, the dividend of `div` and `mod`,
the argument of `min` and `max` on a `Nat`, the branches of a conditional,
the bodies of a `match`'s arms, and what is in parentheses. So in `out m:
Nat := n + 1`, `1` is a `Nat`, but in `n + 1 > 0` it is an `Int`, and `n`
is widened. The operand of `-` is never expected to be a `Nat`, so `-1`
is an `Int`. `lang::literal_type` states the type of a literal:

```fren
pub comp literal_type {
    in nat_expected?         -- a `Nat` is expected where the literal is
    pub det out result: ValueType

    ensure rule: result = (if nat_expected? then ValueType::NatTy else ValueType::IntTy)

    expect a_number: result in {ValueType::IntTy, ValueType::NatTy}
}
```

## Conditionals

`if C then A else B` has the value of `A` if `C` holds, and of `B` otherwise.
`C` must be a `Bool`, and `A` and `B` must have the same type, which is the
type of the conditional. A conditional is an atom, so it can be an operand
without parentheses, but `B` extends as far right as possible:
`2 * if c? then x else y + 1` means `2 * (if c? then x else (y + 1))`.

`lang::conditional` states when a conditional is accepted and what its
type is, from the types of its condition and branches: they are one type,
or a `Nat` and an `Int`, and then the conditional is an `Int`. A condition that is
not a `Bool` is reported at the condition, and branches of different types
at the conditional, with both types. It is
[`lang::operator_type`](#types-of-operators)'s rule for a conditional,
stated over the types themselves, which both front ends compare; the
conditions of `when` and `unless` follow that component's rule for logical
operators. The branches' types are those they have after being checked
against the conditional's, where it is
[checked](Types.md#checking-and-synthesis), so `if c? then {} else s` has
`s`'s type.

```fren
pub comp conditional {
    in condition_bool?       -- the condition is a `Bool`
    in then_ty: Ty           -- the type of `A`
    in else_ty: Ty           -- the type of `B`
    in then_widens?          -- `A`'s type widens to `B`'s (`lang::widening`)
    in else_widens?          -- `B`'s type widens to `A`'s
    pub det out accepted?
    pub det out ty: Ty       -- the conditional's type: the wider of the two

    ensure rule: accepted? iff condition_bool? and (then_widens? or else_widens?)
    ensure typed: ty = (if then_widens? then else_ty else then_ty)

    expect needs_bool: when not condition_bool?, not accepted?
    expect else_wider: when accepted? and not then_widens?, ty = then_ty
}
```

## Function applications

`f(e1, ..., en)` applies the [function](Items.md#functions) `f` to the
arguments `e1` to `en`. Its value is the function's value at the
arguments' values, and its type is the function's result type. For a
[defined function](Items.md#defined-functions), that is the value of its
body, with each parameter standing for the value of its argument: with
`fn double(n: Int): Int := 2 * n`, `double(x + 1)` is `2 * (x + 1)`. An
application is an atom. A function is mentioned only by applying it: a
path to a function on its own is an error, as is an application of
anything other than a function.

An application must give as many arguments as the function has
parameters, and each argument must have the type of its parameter, or be a
`Nat` where the parameter is an `Int` (see [Natural
numbers](#natural-numbers)). `lang::application` states this, from the
types of the parameters and of the arguments, in order, where an argument
of type `Nat` whose parameter is an `Int` counts as an `Int`:

```fren
pub comp application {
    in params: Seq<Ty>   -- the parameters' types
    in args: Seq<Ty>     -- the arguments' types
    in k: Int            -- any position, for `typed`

    assume some_param: params != []
    pub det out accepted?

    ensure rule: accepted? iff args = params

    expect arity: when args.len != params.len, not accepted?
    expect typed: when 0 <= k < args.len and k < params.len and args[k] != params[k], not accepted?
}
```

A function is not a variable, so the rules for which variables an
expression may mention (see [Instances](Instances.md#instance-variables))
apply to its arguments, not to the function. An argument of an
uninterpreted function may not mention an output of the enclosing
component, so that the checks stay decidable: in `comp c { in i: Name out
o: Name ... }`, `f(i)` and `f(w.o)`, for an instance `w`, are accepted, but
`f(o)` is not. A [defined function](Items.md#defined-functions)'s body
applies no uninterpreted function, so its arguments may mention anything.
`lang::argument` states this:

```fren
pub comp argument {
    in defined?          -- the function is defined
    in mentions_output?  -- the argument mentions an output of the enclosing component
    pub det out accepted?

    ensure rule: accepted? iff (defined? or not mentions_output?)

    expect defined_any: when defined?, accepted?
}
```

## Cardinality

`exactly_one?(e1, ..., en)` holds when exactly one of its arguments is
`true`, and `at_most_one?(e1, ..., en)` when at most one is. These are the
*cardinality operators*: built-in functions of one or more `Bool`
arguments, whose result is a `Bool`. "Exactly one mode is active" is
`exactly_one?(heating?, cooling?, idle?)`, where writing out
`at_most_one?` would take a conjunct for each pair of arguments, which is
quadratic and easy to get wrong by missing a pair. "At least one" is `or`.
An argument is any `Bool` expression, such as `x > 0` or another
cardinality operator, and may be written more than once:
`at_most_one?(a?, a?)` is `not a?`.

Each counts its arguments that are `true`, as the sum of `if e then 1 else
0` over them, and compares the count with 1: `exactly_one?` is the sum
`= 1`, and `at_most_one?` the sum `<= 1`. Both front ends translate them
so, which is linear integer arithmetic and keeps them in the [decidable
core](Decidability.md#integers). `lang::cardinality` states their value,
from how many of their arguments are `true`:

```fren
pub enum Cardinality { Exactly, AtMost }

pub comp cardinality {
    use self::Cardinality::{AtMost, Exactly}
    in op: Cardinality
    in n_args: Nat           -- how many arguments it has
    in n_true: Nat           -- how many of them are `true`

    assume some_argument: n_args >= 1
    assume counted: n_true <= n_args
    pub det out value?

    ensure rule: value? iff match op {
        Exactly => n_true = 1,
        AtMost => n_true <= 1,
    }

    expect exactly_is_at_most: when op = Exactly and value?, n_true <= 1
    expect one_argument: when n_args = 1 and op = AtMost, value?
    expect none_true: when n_true = 0, value? iff op = AtMost
}
```

`lang::cardinality_laws` states their laws, over `Bool`s: of one
argument, `at_most_one?` is `true` and `exactly_one?` is the argument; of
two, `exactly_one?` is `!=`; `exactly_one?` implies `at_most_one?`; and
`at_most_one?` is the conjunction over each pair:

```fren
set_option fren.lint.eq_op "allow" in
set_option fren.lint.manual_at_most_one "allow" in
set_option fren.lint.nonminimal_bool "allow" in
pub comp cardinality_laws {
    in a?
    in b?
    in c?

    expect at_most_one_single: at_most_one?(a?)
    expect exactly_one_single: exactly_one?(a?) = a?
    expect exactly_one_pair: exactly_one?(a?, b?) = (a? != b?)
    expect at_most_one_pair: at_most_one?(a?, b?) iff not (a? and b?)
    expect exactly_implies_at_most: when exactly_one?(a?, b?, c?), at_most_one?(a?, b?, c?)
    expect exactly_is_some: exactly_one?(a?, b?, c?) iff ((a? or b? or c?) and at_most_one?(a?, b?, c?))
    expect pairwise: at_most_one?(a?, b?, c?) iff (not (a? and b?) and not (a? and c?) and not (b? and c?))
    expect unordered: exactly_one?(a?, b?, c?) = exactly_one?(c?, a?, b?)
    expect repeated: at_most_one?(a?, a?) iff not a?
}
```

A cardinality operator has at least one argument, as any application
does, and each argument must be a `Bool`: the arguments are typed as a
function's whose parameters are all `Bool`s. `lang::cardinality_args`
states this, from how many arguments it has and how many of them are
`Bool`s:

```fren
pub comp cardinality_args {
    in n_args: Nat           -- how many arguments it has
    in n_bool: Nat           -- how many of them are `Bool`s

    assume counted: n_bool <= n_args
    pub det out accepted?

    ensure rule: accepted? iff (n_args >= 1 and n_bool = n_args)

    expect needs_one: when n_args = 0, not accepted?
    expect only_bools: when n_bool < n_args, not accepted?
}
```

So `exactly_one?()` is an error, which both front ends report alike, and
so is `exactly_one?(1)`: a message about an argument that is not a `Bool`
says which argument it is. `{}` and `[]` are never `Bool`s, so as
arguments they are reported as arguments of the wrong type, not as
literals whose type cannot be known.

Like a method, a cardinality operator has a fixed meaning, so it mentions
what its arguments mention (see [Mentions](#mentions)), and it is not an
application of an uninterpreted function for the rules of constants and of
defined functions: `const ONE_ACTIVE: Bool := exactly_one?(true, false)` is
a constant, and a defined function's body may apply one. Nor does the rule
that an uninterpreted function's arguments mention no output apply to its
arguments. Its arguments are all evaluated, as a function's are: unlike
the operands of `and` and `or`, none of them [guards](#sequences) another.

Their names are reserved: they are not items, so they are never imported,
and no [function](Items.md#functions) may be declared with either name.
`exactly_one?` alone, without arguments, is an error, as a function that
is not applied is, and so is a path such as `self::exactly_one?`, which
names no item. A variable, parameter or binder may
[shadow](Components.md#shadowing) them, written with `!` as for any other
function, and is then a variable, which cannot be applied.

## Records

`Point { x := 1, y := 2 }` builds a value of the [record](Items.md#records)
`Point`, with `1` for `x` and `2` for `y`. A field `x` alone means `x :=
x`, as for an instance's [bindings](Instances.md#bindings). The literal
must give each field of the record exactly once, in any order, and
nothing else, and each value must have its field's type. As in a binding,
a value cannot be a top-level `when`, `unless`, `let` or quantifier. `lang::field_init`
states this, from what a given name is in the record and how many times
the literal gives it, as `inst::binding` does for bindings:

```fren
pub comp field_init {
    in field?            -- the name is a field of the record
    in n: Nat            -- times the literal gives the name
    pub det out accepted?

    ensure rule: accepted? iff ((field? and n = 1) or (not field? and n = 0))

    expect each_field_once: when field? and accepted?, n = 1
}
```

`lang::record_literal` states the rule for the whole literal, which the
rule for each name cannot: that every field is given. A set cannot see a
name given twice, so repeats are counted:

```fren
pub type FieldName

pub comp record_literal {
    in fields: Set<FieldName>        -- the record's fields
    in given: Set<FieldName>         -- the names the literal gives
    in n_repeated: Nat               -- names given more than once, counting each repeat
    pub det out accepted?

    ensure rule: accepted? iff (given = fields and n_repeated = 0)

    expect missing_field: when not fields subset given, not accepted?
    expect unknown_field: when not given subset fields, not accepted?
}
```

`e.x` is the field `x` of the record `e`. For a name, `p.x` is the field
`x` of the variable `p`, `w.p.x` the field `x` of the [instance
variable](Instances.md#instance-variables) `w.p`, and `p.x.y` the field
`y` of `p.x`; `f(p).x`, `(e).x` and `Point { x := 1, y := 2 }.x` read the
field of any other record value. In `a.b`, `a` is an instance if the
component has one named `a`, and a variable otherwise. A field read
mentions the variables that its record mentions: `p.x` mentions `p`.

## Record updates

```text
{ s with count := s.count + 1 }
{ s with count := s.count + 1, mode }
```

A *record update*, `{ r with x := e }`, is the value of `r`'s record that
has `e` for `x` and the value of `r` for every other field: with `struct
Point { x: Int, y: Int }`, `{ p with x := 1 }` is `Point { x := 1, y :=
p.y }`. `r` must have a record type (`F0339`), which is the type of the
update. The fields given are written as in a [record literal](#records):
a field `x` alone means `x := x`, each value must have its field's type,
and a value cannot be a top-level `when` or `unless`. Each field given is
a field of `r`'s record, given at most once (`F0340`). An update gives at
least one field, and may give all of them, though it then has the value
of the record literal of those fields: `r` still counts for what the
update [mentions](#mentions) and for the [definedness
check](../Check.md#definedness) of the indexes within it.

Like a [set literal](#sets), an update starts with `{`: after the
expression that follows the `{`, `with` makes it an update, and `,` or
`}` a set literal. So `{ r with x := 1 }` is an update and `{r}` a set,
and an update is written only where a set literal could be: after a
path, `{` starts a record literal, and after `match e` or `table e`, the arms. An
update is an atom, so `{ p with x := 1 }.y` reads a field of it.

`lang::record_update` states which updates are accepted, from whether
`r` has a record type, the fields of its record and the names the update
gives, with repeats counted, as for `lang::record_literal`:

```fren
pub comp record_update {
    in record?                       -- `r` has a record type
    in fields: Set<FieldName>        -- the fields of its record
    in given: Set<FieldName>         -- the names the update gives
    in n_repeated: Nat               -- names given more than once, counting each repeat

    assume some_given: given != {}
    pub det out accepted?

    ensure rule: accepted? iff (record? and given subset fields and n_repeated = 0)

    expect records_only: when not record?, not accepted?
    expect unknown_field: when not given subset fields, not accepted?
    expect repeated_field: when n_repeated > 0, not accepted?
    expect some_fields: when record? and given subset fields and n_repeated = 0, accepted?
}
```

An update that names every field of its record is accepted exactly when
the record literal of the same fields is: naming every field is allowed,
and then the two rules agree. Where they differ is in fields not named,
which only an update may leave out:

```fren
expect every_field: forall (l: record_literal) (u: record_update),
    when u.record? and u.fields = l.fields and u.given = l.given and u.n_repeated = l.n_repeated
    and u.given = u.fields,
    u.accepted? iff l.accepted?

expect fields_left_out: forall (l: record_literal) (u: record_update),
    when u.record? and u.fields = l.fields and u.given = l.given and u.n_repeated = l.n_repeated
    and u.given subset u.fields and u.given != u.fields and u.n_repeated = 0,
    u.accepted? and not l.accepted?
```

## Newtypes

```text
Ms(5)
elapsed.0
budget - elapsed
```

`Ms(e)` builds the value of the [newtype](Items.md#newtypes) `Ms` whose
field is `e`, which must have `Ms`'s underlying type, or be a `Nat`
where it is an `Int` (`F0304`). `e` is [checked](Types.md#checking-and-synthesis)
against the underlying type, so with `struct Tags(Set<Int>)`, `Tags({})`
is the newtype's empty set. It is written as an application of one
argument (`F0308`). A newtype is never built as a record literal, `Ms {
... }`, nor a record with named fields as a newtype, `Point(1, 2)`
(`F0364`). `x.0` reads the field of `x`, of the underlying type, as in
`elapsed.0 + 1`. A newtype has no other field (`F0315`) and no methods: a
method of its value is applied to `x.0`, as in `name.0.len`. Nor is its
field given new values by a [record update](#record-updates) (`F0339`):
`Ms(e)` builds another value.

No literal is a newtype's: `5` is an `Int` wherever it is written, so with
`elapsed: Ms`, `elapsed < 5` is an error, and `elapsed < Ms(5)` is
written instead.

A newtype has few operators. Two values of one newtype are compared with
`=` and `!=`. They are ordered with `<`, `<=`, `>` and `>=`, as their
fields are, when the newtype is declared
[`ordered`](Items.md#ordered-declarations), which its underlying type
must then be, and such comparisons [chain](#chained-comparisons), as in
`Ms(0) <= elapsed < budget`; a newtype declared without `ordered` has no
orderings, even of an `Int` (`F0352`). `+` and `-` of two values of one
newtype give the newtype, whose field is the sum or difference of theirs:
`budget - elapsed` is `Ms(budget.0 - elapsed.0)`, and is accepted, and
means, exactly what that is. So a newtype of `Int` has both; a newtype of
`Nat` has `+`, a `Nat` again, but not `-`, since `budget.0 - elapsed.0`
is an `Int`, which is never [narrowed](#natural-numbers) to a `Nat`; a
newtype of a newtype has those that its underlying type has; and a
newtype of a [pattern type](Types.md#pattern-types), such as `struct
Byte(Int is 0..=255)`, has its base type's, with the obligation, as for
`Byte(e)`, that the sum or difference matches the pattern. No other
operator applies to a newtype, neither `*`, `div`, `mod`, `++` nor a
prefix `-` (`F0362`): the field is read and the result built again, as in
`Ms(elapsed.0 * 2)`. An operator whose operands are a newtype and any
other type, including the underlying type, is an error (`F0363`), and a
newtype written where another type is expected is a type mismatch
(`F0304`). `lang::newtype_operator` states which operators a newtype has,
from the operator, its underlying type, whether it is ordered, and
whether its underlying type, if that is a newtype, has the operator
itself, and `lang::operator_type` types them:

```fren
-- `Order` is `<`, `<=`, `>` and `>=`; `Addition` is `+`; `Subtraction`
-- is `-` between two operands; `Other` is any other operator but `=` and
-- `!=`, such as `*`, `div`, `mod`, `++` or a prefix `-`.
pub enum NewtypeOp { Equality, Order, Addition, Subtraction, Other }

pub comp newtype_operator {
    use self::NewtypeOp::{Addition, Equality, Order, Other, Subtraction}
    use self::ValueType::{IntTy, NatTy, StringTy}
    in op: NewtypeOp
    in underlying: Ty            -- the newtype's underlying type
    in ordered?                  -- the newtype is ordered (`ordered_type`): declared `ordered`
    in inner_has?                -- the underlying type is a newtype that has `op` itself

    -- A newtype is a record.
    assume inner_newtypes: when inner_has?, newtype?(underlying) and kind(underlying) = ValueType::RecordTy
    pub det out accepted?

    ensure rule: accepted? iff match op {
        Equality => true,
        Order => ordered?,
        Addition => kind(underlying) in {IntTy, NatTy} or inner_has?,
        Subtraction => kind(underlying) = IntTy or inner_has?,
        Other => false,
    }

    expect equality_always: when op = Equality, accepted?
    expect orderings_opt_in: when op = Order, accepted? iff ordered?
    expect integers_sum: when kind(underlying) = IntTy and op in {Addition, Subtraction}, accepted?
    expect naturals_add: when kind(underlying) = NatTy and op in {Addition, Subtraction}, accepted? iff op = Addition
    expect strings_never_sum: when kind(underlying) = StringTy and op in {Addition, Subtraction}, not accepted?
    expect nothing_else: when op = Other, not accepted?
}
```

The solver sees a newtype as its underlying type: `Ms(e)` is `e`, `x.0`
is `x`, and each operator is its underlying type's, so that a newtype
costs nothing in the solver (see [Solver queries](../Cli.md#solver-queries)).
In Lean, a newtype is a structure (see [Generated Lean
declarations](../Generated.md#newtypes)).

## Variants with payloads

`Shape::Circle(2)` builds the value of the enumeration `Shape` that is the
variant `Circle` with the payload `2`, written as a [function
application](#function-applications) is. A variant with a payload is
mentioned only by applying it, and a variant without one only by its
path: `Shape::Circle` and `Shape::Empty()` are errors. The same holds for
a variant in a [pattern](Patterns.md), whose payload's values patterns
match. `lang::variant_mention` states this:

```fren
pub mod lang

pub comp variant_mention {
    in payload: Nat          -- how many values the variant's payload has
    in applied?              -- it is written with parentheses, around values or, in a pattern, patterns
    pub det out accepted?

    ensure rule: accepted? iff (applied? iff payload > 0)

    expect plain: when payload = 0 and not applied?, accepted?
    expect applied: when payload > 0 and applied?, accepted?
    expect unapplied: when payload > 0 and not applied?, not accepted?
    expect empty_parentheses: when payload = 0 and applied?, not accepted?
}
```

As for a function, `lang::application` gives whether the application is
accepted, where the parameters are the payload's types. Of a variant of a
[generic type](Generics.md), those are the payload's types with its
inferred [type arguments](Generics.md#type-arguments) for its parameters. Unlike a
function's value, a variant's value is fixed: building one is not an
application for the rules of [linear arithmetic](#linear-arithmetic) or of
constants, and its arguments may mention any variable that its place
allows.

## Matches

```text
match r {
    Reply::Ok(Shape::Circle(radius)) => radius > 0,
    Reply::Ok(_) => true,
    Reply::Err(0) => false,
    Reply::Err(code) => code > 100,
}
```

A `match` reads the value of its *scrutinee*, the expression after
`match`. The scrutinee is a value of an enumeration, a `Bool`, an `Int`, a
`Nat` or a `String` (`F0316`). It is an atom, so an operator in it is
written in parentheses, and it is not a record literal: in `match s {`,
the `{` starts the arms. Each arm has a [pattern](Patterns.md) and a body, and the
`match` has the value of the body of the first arm whose pattern matches
the scrutinee. A pattern is `_`, a binder, a literal, a range, a variant
whose payload's values match patterns of their own, nested to any depth, or
an or-pattern. An or-pattern may start with `|`, so that its alternatives
can be written one per line, each starting with `|`:

```text
match method {
    | Method::Len
    | Method::Card => 0,
    _ => 1,
}
```

```text
match n {
    ..=-1 => Sign::Negative,
    0 => Sign::Zero,
    1.. => Sign::Positive,
}
```

An arm may have a *guard*, `if C` after its pattern, where `C` is a
`Bool`. The `match` then has the value of the body of the first arm whose
pattern matches the scrutinee and whose guard holds: an arm whose guard is
false falls through to the arms after it, as if its pattern had not
matched. An arm without a guard is *taken* wherever its pattern matches and
no earlier arm is taken, and an arm with one where its guard holds too. The
guard follows the whole pattern, so in `Gt | Ne if bound = -1 => Found`, it
guards both alternatives:

```text
match op {
    Ge if bound = 0 => Found,
    Gt | Ne if bound = -1 => Found,
    Eq if bound = -1 => Absent,
    Eq if bound = 0 => AtStart,
    _ => Other,
}
```

Within its arm's guard and body, each binder of the arm's pattern, at any depth,
names the value it matches: the scrutinee, or a value of a payload. The
binders of a pattern have distinct names, and follow the [Boolean
names](Types.md#boolean-names) rule for the types of their values. A binder
is not a variable. Within its arm's guard and body, it may shadow a variable, a
constant or another name in scope, written with `!`, as in
`Shape::Circle(r!)` (see [Shadowing](Components.md#shadowing)); a mention
of it there is not a mention of what it shadows. Mentioning it counts as
mentioning everything its scrutinee mentions, whatever its depth, for the
rules of [Instances](Instances.md#instance-variables), of [function
applications](#function-applications) and of [linear
arithmetic](#linear-arithmetic). So in `comp c { out s: Shape ... }`,
`match s { Shape::Circle(r) => f(r), _ => ... }` mentions the output `s`
in an argument of `f`, which is an error.

The bodies of all arms have the same type, or are `Nat`s and `Int`s, and
the `match` has that type, or `Int` if they are mixed. As in a binding, a
body cannot be a top-level `when`, `unless`, `let` or
[quantifier](Quantifiers.md), which would run on into the next arm, and
neither can a guard, which would run on into its arm's `=>`: write those
in parentheses. A guard is a `Bool` (`F0304`), as a table's row's
condition is, and is checked as one, without an expected type from the
arms.

The bodies are checked in order, each against the type of the arms
before it, as both front ends do. An arm of another type is reported at
its body (`F0320`), with that type and its own. `lang::arm_type` states
this for one arm, from its type and the type of the arms before it: as for
a [conditional's](#conditionals) branches, one widens to the other
(`lang::widening`), and the arms so far then have the wider type. A body
that does not [synthesize](Types.md#checking-and-synthesis) its type, as
`{}` does, has the type of the arms it is checked against.

```fren
pub comp arm_type {
    in before: Ty            -- the type of the arms before it
    in arm: Ty               -- the type of its body
    in arm_widens?           -- `arm` widens to `before` (`lang::widening`)
    in before_widens?        -- `before` widens to `arm`
    pub det out accepted?
    pub det out ty: Ty       -- the type of the arms so far: the wider of the two

    ensure rule: accepted? iff (arm_widens? or before_widens?)
    ensure typed: ty = (if before_widens? then arm else before)

    expect same_type: when arm = before, ty = before
    expect arm_wider: when accepted? and not arm_widens?, ty = arm
}
```

A `match` is *exhaustive*, and each of its arms and alternatives is
*reachable*: every value of the scrutinee's type matches some arm's pattern
(`F0317`), and each arm, and each alternative of its or-patterns, matches
some value that no arm before it without a guard matches (`F0318`). Both are decided by the
[usefulness](Patterns.md#usefulness) of patterns: an arm is reachable when
its pattern is useful with respect to those of the arms before it that
have no guard, an
alternative when some case of its arm that takes it is, and the `match` is
exhaustive when `_` would not be useful after its last arm, each arm with a
guard counted as if it had none. So `true` and
`false` together cover a `Bool`, ranges and literals cover an `Int` only
when they match every integer, as `..=-1`, `0` and `1..` do, and a `Nat`
when they match every integer that is at least 0, as `0` and `1..` do, and
a `match` on a `String` needs a last arm `_` or a binder. An arm with a
guard may not be taken where its pattern matches, so it hides nothing from
the arms after it, as `Eq if bound = 0` above does not hide `Eq` from the
next arm. `lang::match_arms` states
this, from the numbers of arms and alternatives that are not useful, and
whether the arms are exhaustive:

```fren
pub comp match_arms {
    in n_useless_arms: Nat           -- arms not useful with respect to the arms before them without guards
    in n_useless_alternatives: Nat   -- alternatives of the other arms that no useful case of their arm takes
    in exhaustive?                   -- `_` is not useful with respect to all the arms, guards ignored
    pub det out accepted?

    ensure rule: accepted? iff (n_useless_arms = 0 and n_useless_alternatives = 0 and exhaustive?)

    expect exhaustive: when accepted?, exhaustive?
    expect reachable: when accepted?, n_useless_arms = 0 and n_useless_alternatives = 0

    cover accepted: accepted?
    cover useless_rejected: n_useless_arms > 0 and not accepted?
    cover not_exhaustive_rejected: not exhaustive? and not accepted?
}
```

The static rules never ask what a guard's value is. Whether an arm with a
guard, or an arm after one, can be taken, and whether some arm is always
taken in a `match` that is exhaustive only when its arms with guards are
counted as if they had none, are [checks](../Check.md#reachability), with
verdicts, as an index's [definedness](../Check.md#definedness) is. Where
no arm is taken, a `match` is unspecified, as a [table](#tables) where no
row holds is: its value is the same unknown value of its type, that of
`[][0]` of the empty sequence of its type. The [completeness
check](../Check.md#completeness) reports a `match` where no arm may be
taken, and the [reachability check](../Check.md#reachability) an arm that
can never be.

`lang::guarded_match` states what a `match` with guards means, at one
value of its scrutinee: from what each arm does there, in order, and the
value of each arm's body there. An arm's pattern may not match
(`NoMatch`); it may match, with a guard that fails (`GuardFails`); or it
may match, without a guard or with one that holds (`Taken`). The arm
*taken* is the first that is `Taken`, and the `match` has its body's
value. An arm whose guard fails is passed over as one whose pattern does
not match is, so the arms after it are tried. Where no arm is taken, the
guarantees say nothing of the value: it is unspecified. A table is the
same, with every pattern `_`, which matches: a row is `Taken` where its
condition holds, and `GuardFails` where it fails, and a `_` row is always
`Taken`. The position of the arm taken is that of the first `Taken`,
`index_of` a sequence of one `Taken`, which is outside the decidable core,
and `-1` where there is none. `k` stands for any position, so
`none_before` holds of every arm before the one taken:

```fren
pub enum ArmAt { NoMatch, GuardFails, Taken }

set_option fren.lint.undecidable "allow" in
pub comp guarded_match {
    use self::ArmAt::{GuardFails, NoMatch, Taken}
    in arms: Seq<ArmAt>      -- what each arm does at the scrutinee's value, in order
    in bodies: Seq<Int>      -- each arm's body's value there
    in k: Int                -- any position, for `none_before`

    assume aligned: bodies.len = arms.len
    pub out first: Int := arms.index_of([Taken], 0)  -- the position of the arm taken, `-1` if none is
    pub out value: Int       -- the `match`'s value

    ensure valued: when first >= 0, value = bodies[first]

    expect in_range: -1 <= first < arms.len
    expect first_taken: when first >= 0, arms[first] = Taken
    expect none_before: when 0 <= k < arms.len and (first = -1 or k < first), arms[k] != Taken

    -- An arm whose guard fails is passed over, as one that does not match.
    expect falls_through: when arms != [] and arms[0] = GuardFails, first != 0
    expect no_match: when arms != [] and arms[0] = NoMatch, first != 0
    -- An arm that is taken, and none before it, is the first.
    expect some_taken: when 0 <= k < arms.len and arms[k] = Taken, 0 <= first <= k
}
```

## Pattern tests

```text
s is Shape::Circle(_)
s is Shape::Rect(_, _) | Shape::Empty
r is Reply::Ok(Shape::Circle(_))
n is 0..=9
when s is Shape::Circle(radius), radius > 0
```

A *pattern test*, `e is P`, is `true` exactly when the pattern `P` matches
`e`: it means `match e { P => true, _ => false }`. `e` is a value of an
enumeration, a `Bool`, an `Int`, a `Nat` or a `String`, as a `match`'s scrutinee is
(`F0335`), and `P` is a [pattern](Patterns.md) as in a [`match`
arm](#matches), nested, literal, range and or-patterns included. Its
binders name parts of the value only where something follows the test
that is evaluated where the pattern matches (see [Binding
names](#binding-names)); elsewhere, each of them is `_`. The pattern
matches some value, and each alternative of its
or-patterns is reachable, as in a `match` (`F0318`): so `k is -5..=-1`, on
a `Nat`, is an error, as an arm with that pattern would be. A pattern that
matches every value, such as `_`, is allowed, though the test is then
always `true`. A pattern test takes no guard: `e is P if C` is an error
(`F0140`), and is written `e is P and C`.

`is` is a comparison: it binds as `=` does, below `+` and above `not`, and
is not associative. So `not s is Shape::Circle(_)` means `not (s is
Shape::Circle(_))`, `a is A(_) and b is B(_)` tests both, and `s is
Shape::Circle(_) = true` and `x < y is A(_)` are errors (`F0108`), since
`is` does not [chain](#chained-comparisons). Its pattern extends as far right as
its alternatives do, so `s is A(_) | B(_) and t?` means `(s is A(_) |
B(_)) and t?`.

`=` compares with one value, and `is` tests against several, and against
the patterns that `=` cannot express: those with a payload, and ranges. So
write `x = E::A` and `x is E::A | E::B`, not `x is E::A` or `x = E::A or x
= E::B`, and likewise `x != E::A` and `not x is E::A | E::B`. Test a `Bool`
with `iff` or `not` rather than `is true`, and compare an `Int`, a `Nat` or
a `String` with a literal with `=`, but test it against several literals or
a range with `is`, as in `n is 0 | 1` and `n is 0..=9`. A pattern test
writes its alternatives in the syntax of a [pattern
type](Types.md#pattern-types), and a range or a payload extends it as it
is, as in `status is 429 | 500..=599`; `in` is for collections, such as a
set constant or a set that is computed. A pattern with a payload may still
have alternatives without one, as in `s is Shape::Rect(_, _) |
Shape::Empty`.

### Binding names

A pattern test binds the names of its pattern's binders for what follows
it where it holds, as Rust's `if let` and its chains of `let` do:

- `when x is P, D`: the names are in scope in `D`, and the `when` means
  `match x { P => D, _ => true }`.
- `x is P and E`: the names are in scope in `E`, and the `and` means
  `match x { P => E, _ => false }`. `E` is evaluated only where the
  pattern matches, as the right operand of `and` is
  [guarded](#sequences) by its left.
- `if x is P then a else b`: the names are in scope in `a` alone, and the
  `if` means `match x { P => a, _ => b }`.

The operands of `and`, through parentheses, form a *chain*, and a
pattern test that is not an operand of `and` is a chain of one. A name
that a test of a chain binds is in scope in the operands of the chain
after the test, and, if the chain is the condition of a `when` or an
`if`, in the `when`'s body or the `if`'s `then` branch. So in `x is P(d)
and y is Q(e) and d < e`, `d` is in scope in `y is Q(e)` and in `d < e`,
and `e` in `d < e`, however the chain is parenthesized: `(x is P(d) and
y is Q(e)) and d < e` and `x is P(d) and (y is Q(e) and d < e)` are the
same chain. `when a and b, D` means `when a, when b, D`, so `when x is
P(d) and d > 0, D` is `match x { P(d) => (when d > 0, D), _ => true }`.
Nothing else sees the names: not the operands before the test, not the
`else` branch, and not what is around the chain.

A test whose names would be in scope nowhere cannot bind any (`F0334`):
the last operand of a chain, or a chain of one, that is not the condition
of a `when` or an `if`. That is a test on its own, an operand of `iff`,
of a comparison or of a function, and a test under `or` or `not`, where
what follows need not be evaluated where the pattern matches. It is also
the condition of `unless`, whose body holds where the condition does not:
`unless x is P(d), D` would mention `d` where `x` does not match `P`.
`unless x is P(d) and d > 0, D` is accepted, as `d` is in scope in `d >
0`, but not in `D`. Write `_` for each binder of such a test, or read the
payload with a [`match`](#matches).

The binders of a pattern test are a `match` arm's binders: each names a
value of the scrutinee, their names are distinct (`F0213`) and follow the
[Boolean names](Types.md#boolean-names) rule, an or-pattern binds none
(`F0333`), and one that shadows a name in scope, a binder of an earlier
test of its chain included, is written with `!` (see
[Shadowing](Components.md#shadowing)). A binder is not a variable, and
mentioning it counts as mentioning everything its scrutinee mentions.

A guarantee `when x is P(d), D` is one constraint, as a `match` is: the
checks that count constraints, such as [vacuity](../Check.md#vacuity),
[redundancy](../Check.md#redundancy) and [minimal
sets](../Check.md#minimal-sets), treat it as one, so a conflict names it
apart from the guarantees beside it. Its trigger, for vacuity, is its
condition, `x is P(_)`, and for `when x is P(d), when d > 0, D`, the
pattern's matching and `d > 0`, with `d` the payload's value.

`lang::test_scope` states where a name that a pattern test binds is in
scope, from what its chain is a part of, `context`, the chain's number of
operands and the test's position among them, and where the name is
mentioned, `site`; and so whether the test may bind names at all:

```fren
-- What a chain of `and` that holds a pattern test is a part of.
pub enum TestContext {
    WhenCondition,     -- the condition of `when`
    UnlessCondition,   -- the condition of `unless`
    IfCondition,       -- the condition of `if`
    OrOperand,         -- an operand of `or`
    NotOperand,        -- the operand of `not`
    Standalone,        -- anything else: a whole constraint, an operand of `iff`
}

-- Where, in and around such a chain, a name is mentioned.
pub enum Site {
    Operand(Nat),      -- the chain's operand at this position, from 0
    Body,              -- the body of the `when` or `unless`, or the `then` branch of the `if`
    ElseBranch,        -- the `else` branch of the `if`
    Outside,           -- anywhere else
}

pub comp test_scope {
    in context: TestContext
    in operands: Nat         -- the chain's operands
    in test_at: Nat          -- the test's position among them, from 0
    in site: Site            -- where a name that the test binds is mentioned
    pub det out visible?     -- the name is in scope there
    pub det out binds?       -- the test may bind names

    assume within: test_at < operands

    ensure later: when site is Site::Operand(k), visible? iff test_at < k < operands
    ensure body: when site = Site::Body, visible? iff context is TestContext::WhenCondition | TestContext::IfCondition
    ensure nowhere_else: when site is Site::ElseBranch | Site::Outside, not visible?
    ensure binds: binds? iff (test_at + 1 < operands or context is TestContext::WhenCondition | TestContext::IfCondition)

    expect unless_body: when context = TestContext::UnlessCondition and site = Site::Body, not visible?
    expect alone: when operands = 1 and not context is TestContext::WhenCondition | TestContext::IfCondition, not binds?
    expect next_operand: when test_at + 1 < operands, binds?
    expect earlier: when site is Site::Operand(k) and k <= test_at, not visible?
}
```

`lang::pattern_binding` states what a pattern test that binds a name
means, over an enumeration whose one variant has a payload: each form
means the `match` that the rules above give it.

```fren
pub enum Reading { Missing, Value(Int) }

pub comp pattern_binding {
    in r: Reading
    in limit: Int
    pub det out at_most_limit?      -- `when r is Reading::Value(v), v <= limit`
    pub det out exceeds?       -- `r is Reading::Value(v) and v > limit`
    pub det out clamped: Int  -- `if r is Reading::Value(v) and v <= limit then v else limit`

    ensure within_rule: at_most_limit? iff (when r is Reading::Value(v), v <= limit)
    ensure above_rule: exceeds? iff r is Reading::Value(v) and v > limit
    ensure clamped_rule: clamped = (if r is Reading::Value(v) and v <= limit then v else limit)

    expect within_match: at_most_limit? iff match r { Reading::Value(v) => v <= limit, _ => true }
    expect above_match: exceeds? iff match r { Reading::Value(v) => v > limit, _ => false }
    expect clamped_match: clamped = match r { Reading::Value(v) if v <= limit => v, _ => limit }
    expect complement: when r is Reading::Value(_), at_most_limit? iff not exceeds?
    expect missing: when r = Reading::Missing, at_most_limit? and not exceeds? and clamped = limit
    expect at_most: clamped <= limit
}
```

`lang::pattern_test` states which patterns are accepted, from whether the
test may bind names, by `lang::test_scope`, the numbers of their binders
that are not `_` and of their alternatives that are not reachable, and
whether they match some value:

```fren
pub comp pattern_test {
    in binds?                        -- the test may bind names (`lang::test_scope`)
    in n_bound: Nat                  -- binders that are not `_`
    in n_useless_alternatives: Nat   -- alternatives that no useful case of the pattern takes
    in matches_some?                 -- some value matches the pattern
    pub det out accepted?

    ensure rule: accepted? iff ((binds? or n_bound = 0) and n_useless_alternatives = 0 and matches_some?)

    expect binds_nothing: when accepted? and not binds?, n_bound = 0
    expect every_alternative: when accepted?, n_useless_alternatives = 0
    expect matches_something: when accepted?, matches_some?

    cover accepted: accepted?
    cover binding: accepted? and n_bound > 0
    cover empty_rejected: not matches_some? and not accepted?
}
```

## Tables

```text
table {
    | not ran? => 2,
    | worst = Severity::Error => 1,
    | worst = Severity::Warning => 3,
    | _ => 0,
}
```

A *table* chooses a value by conditions, as the tabular guarantees of
Parnas and of SCR do, or by the patterns of a scrutinee (see [Tables over
a scrutinee](#tables-over-a-scrutinee)). Each row has a condition and a value, and the table
has the value of the first row whose condition holds, as a chain of
conditionals has. A last row `_ => e` holds wherever no earlier row does.
The rows are separated by commas, as the arms of a `match` are, and each
may start with `|`, so that they line up one per line. A table is an
atom, so it can be an operand without parentheses.

A table is a [`match`](#matches) with guards and nothing to match on: each
row `C => e` is an arm `_ if C => e`, and a row `_ => e` the arm `_ => e`.
So the table above means what a `match` would whose arms were `_ if not
ran? => 2`, `_ if worst = Severity::Error => 1`, `_ if worst =
Severity::Warning => 3` and `_ => 0`, on any scrutinee, and its rules, its
value and its checks are that `match`'s, but for what follows.

Each row's condition is a `Bool`, as a guard is, and the values of all rows have the
same type, which is the type of the table, as the bodies of a `match`'s
arms do, or are `Nat`s and `Int`s, which make an `Int` (see [Natural
numbers](#natural-numbers)). The values are [checked](Types.md#checking-and-synthesis)
as the bodies of a `match`'s arms are. As in a `match` arm, neither a
condition nor a value can be a top-level `when` or `unless`, which would
run on into the next row. Only the last row can be `_`: a row after it
could never be reached, which is an error (`F0359`), as an arm after a
`_` arm is. That is the static rule of a `match`'s arms, which a row
breaks only there, reported in the words of a table: the arms of rows other than
`_` have guards, so they hide nothing from the rows after them, and every
arm's pattern is `_`, so the arms are exhaustive when guards are ignored.

Where no row holds, a table without a `_` row is unspecified, as a `match`
where no arm is taken is, and an
[index out of range](#sequences) is: its value is that of `[][0]` of the
empty sequence of its type, an unknown value of that type, which the
checks hold for every interpretation of. It is the same for every such
table and `match` of that type: two incomplete tables of one type coincide where
neither has a row that holds, so `table { x > 0 => 1 } = table { x > 0 =>
2 }` holds wherever `x <= 0`, and an expectation that compares such
values can pass by that coincidence alone. The constraint then says
nothing useful there, which is almost always a
mistake: the [completeness check](../Check.md#completeness) of the
`match` reports a table
where no row may hold, given its [guard](#sequences), and its
[reachability check](../Check.md#reachability) a row that can never be the
first that holds. Rows whose
conditions can hold at once make the order of the rows matter, which is
easy to misread: the [disjointness check](../Check.md#disjointness), which
only tables have, reports
two rows that may both hold. A table with a `_` row is always complete,
and its `_` row overlaps no other.

A row's condition is evaluated where no earlier row's holds, and its value
where the row is the first that holds, which guards their indexes (see
[Sequences](#sequences)). A table in the definition of a [`let` or
`where`](Let.md#meaning) name is checked where the name is mentioned, as
the definition's indexes are. Mentioning a table mentions what its conditions
and values mention (see [Mentions](#mentions)).

### Tables over a scrutinee

```text
table m {
    Mode::Off => 0,
    Mode::On(x) if x > 0 => x,
    Mode::On(x) if x <= 0 => 1,
}
```

A table may have a scrutinee, written after `table` as a `match`'s is
after `match`: an atom that is not a record literal. Its rows are then
arms, written as a [`match`'s](#matches) are, each with a pattern, a
guard if it has one, and a body, and the table means what the `match`
with the same scrutinee and arms means: its static rules, its value and
its checks are that `match`'s, but for what follows. `{` right after
`table` starts the rows of a table by conditions, so a scrutinee that
starts with `{`, a set literal or a record update, is written in
parentheses, though no such value is matched (`F0316`).

Where a `match` has the value of the first arm that is taken, the arms of
a table are *disjoint*: no two of them are taken at one value of the
scrutinee, each where its pattern matches and its guard holds. So the
table's value does not depend on the order of the arms: each can be read
alone, they can be reordered or split, and the table has the value of the
body of the one arm that is taken. Their order still matters to the
[definedness](../Check.md#definedness) of the indexes in their guards,
as a `match`'s does: a guard is evaluated where no earlier arm is taken,
so an index in it may rest on an earlier arm's guard, and reordering two
arms with guards can leave it out of range (`F0611`). Overlapping arms, which a `match` would quietly read in
order, as it would `n if n > 0` and `n if n >= 0`, are reported instead.
Disjointness is decided in two parts:

- Two arms without guards whose patterns [overlap](Patterns.md#overlap),
  that is, which some value matches both, are an error (`F0391`), at the
  later arm's pattern, with such a value. Of several such pairs, the first
  is reported, by its later arm and then by its earlier one. The static rules decide it from
  the patterns alone, nested and range patterns among them, as they decide
  [usefulness](Patterns.md#usefulness). So `Mode::On(_)` and `Mode::On(x)`
  are an error, and so are `1..=5` and `5..`, which both match `5`.
- Two arms whose patterns overlap, of which at least one has a guard, are
  asked about by the [disjointness check](../Check.md#disjointness): only
  the solver can tell whether their guards can hold at once, as for two
  rows of a table by conditions.

Two arms whose patterns do not overlap are disjoint, whatever their guards.

A last arm `_ => e`, without a guard, means *otherwise*: it is taken
wherever no other arm is, as a table's `_` row is. It overlaps no other
arm, so it is neither an error nor asked about, and like the `_` row, it
is last: an arm after it is an error (`F0359`). Where the arms without
guards before it cover every value, it is never taken, an error
(`F0318`), as a `_` arm after them is in a `match`: in `table b? { true
=> 0, false => 1, _ => 2 }`, the `_` arm is dead. An arm whose pattern is
a binder, or that is `_` with a guard, is not *otherwise*, and overlaps
every other arm.

The arms are exhaustive as a `match`'s are (`F0317`), each arm with a guard
counted as if it had none, and each alternative of an arm's or-patterns
matches some value that the alternatives before it in the same arm do not
(`F0318`). No arm hides the arms after it, as an arm without a guard does
in a `match`: an arm that the arms without guards before it would cover
overlaps one of them, and is reported as such, wherever it is written.
Where the arms without guards are not exhaustive, the [completeness
check](../Check.md#completeness) asks whether some arm is always taken,
and reports a table where none may be at its `table` (`F0637`), and the
[reachability check](../Check.md#reachability) asks of each arm that has a
guard or follows one whether it can be taken, and reports one that never
is at its pattern (`F0638`), as for a `match`. Where no arm is taken, the
table is unspecified, as a `match` is.

`lang::table_arm_pair` states the rule for two arms of a table over a
scrutinee, from whether their patterns overlap, whether one of them has a
guard, and whether one of them is the last arm `_`, which has none:

```fren
pub comp table_arm_pair {
    in overlap?              -- some value matches both patterns (`lang::overlap`)
    in guarded?              -- one of the arms has a guard
    in otherwise?            -- one of the arms is the last arm `_`, without a guard
    pub det out rejected?    -- the static rules reject the table (`F0391`)
    pub det out asked?       -- the disjointness check asks whether both can be taken at once

    ensure static: rejected? iff (overlap? and not guarded? and not otherwise?)
    ensure checked: asked? iff (overlap? and guarded? and not otherwise?)

    expect never_both: not (rejected? and asked?)
    -- Arms whose patterns do not overlap are disjoint, whatever their guards.
    expect apart: when not overlap?, not rejected? and not asked?
    expect otherwise_alone: when otherwise?, not rejected? and not asked?

    cover rejected: rejected?
    cover asked: asked?
}
```

`lang::table_arms` states the same over the arms of a table as written,
in order, each `_` without a guard, or another pattern with a guard or
without, for two arms `i` and `j` of them, `i` before `j`, with whether
each arm's pattern overlaps `j`'s, as `lang::pattern_overlap` decides it.
The otherwise is the last arm, `_` without a guard; no other arm is `_`
without one (`F0359`). Of the
pairs that the static rules reject, the table is reported at the first,
in order, as above: `earlier_rejected?` says whether a pair before `(i,
j)` is rejected, either of an arm before `j`, or of `j` and an arm before
`i`. `table_arms_refines` confirms that it refines `table_arm_pair`:

```fren
pub enum TableArm { Unguarded, Guarded, Wildcard }

pub enum Overlap { Apart, Overlapping }

set_option fren.lint.undecidable "allow" in
pub comp table_arms {
    use self::Overlap::Overlapping
    use self::TableArm::{Guarded, Wildcard}
    in arms: Seq<TableArm>       -- each arm, in order: `_` without a guard, or another, with a guard or without
    in overlaps: Seq<Overlap>    -- whether each arm's pattern overlaps arm `j`'s
    in i: Int                    -- an arm before `j`
    in j: Int                    -- an arm
    in earlier_rejected?         -- the static rules reject a pair before `(i, j)`, in order
    pub out rejected?            -- the static rules reject arms `i` and `j`
    pub out asked?               -- the disjointness check asks whether both can be taken at once
    pub out reported?            -- the table is reported at arm `j`, naming arm `i` (`F0391`)

    -- Whether arm `i`'s pattern overlaps arm `j`'s, whether one of them
    -- has a guard, and whether arm `j` is the otherwise: the last, `_`
    -- without a guard.
    ensure rule: rejected? iff (0 <= i < overlaps.len and overlaps[i] = Overlapping)
        and not ((0 <= i < arms.len and arms[i] = Guarded) or (0 <= j < arms.len and arms[j] = Guarded))
        and not (0 <= j and j = arms.len - 1 and arms[j] = Wildcard)
    ensure check: asked? iff (0 <= i < overlaps.len and overlaps[i] = Overlapping)
        and ((0 <= i < arms.len and arms[i] = Guarded) or (0 <= j < arms.len and arms[j] = Guarded))
        and not (0 <= j and j = arms.len - 1 and arms[j] = Wildcard)
    ensure first: reported? iff (0 <= i < j < arms.len and rejected? and not earlier_rejected?)

    expect otherwise_alone: when 0 <= j and j = arms.len - 1 and arms[j] = Wildcard, not rejected? and not asked?
    expect reported_rejected: when reported?, rejected?
}

set_option fren.lint.undecidable "allow" in
refine table_arms_refines: table_arms refines table_arm_pair {
    overlap? := 0 <= i < overlaps.len and overlaps[i] = Overlap::Overlapping,
    guarded? := (0 <= i < arms.len and arms[i] = TableArm::Guarded) or (0 <= j < arms.len and arms[j] = TableArm::Guarded),
    otherwise? := 0 <= j and j = arms.len - 1 and arms[j] = TableArm::Wildcard,
}
```

`lang::table_match` states what a table over a scrutinee means, at one
value of its scrutinee: from what each of its arms but the last `_` does
there, as [`lang::guarded_match`](#matches) has it with its `ArmAt`, the
value of each arm's body there, and the value of the body of its `_` arm,
the *otherwise*, if it has one. An arm *holds* where it is `Taken`: its
pattern matches the value and its guard, if it has one, holds there. The
arms are *disjoint* there when no two of them hold: none holds after the
first that does. The table then has the value of the body of the one arm
that holds, `one`, and where none does, that of the otherwise. Where the
arms overlap, or none holds and there is no otherwise, the guarantees say
nothing of the value. The position of the arm that holds is found as in
`lang::guarded_match`, and `k` stands for any position:

```fren
set_option fren.lint.undecidable "allow" in
pub comp table_match {
    use self::ArmAt::Taken
    in arms: Seq<ArmAt>      -- what each arm but `_` does at the scrutinee's value, in order
    in values: Seq<Int>      -- each arm's body's value there
    in otherwise: Seq<Int>   -- `[v]` where the table has a last arm `_ => e` and `e`'s value there is `v`, `[]` where it has none
    in k: Int                -- any position, for `only` and `none_holds`

    assume aligned: values.len = arms.len
    pub out one: Int := arms.index_of([Taken], 0)  -- the arm that holds, `-1` if none does
    pub out disjoint? := arms.index_of([Taken], one + 1) = -1  -- no two arms hold
    pub out value: Int       -- the table's value

    ensure held: when disjoint? and one >= 0, value = values[one]
    ensure otherwise_held: when one = -1 and otherwise != [], value = otherwise[0]

    -- Where the arms are disjoint, the arm that holds is the only one, so
    -- the value does not depend on the order of the arms.
    expect only: when disjoint? and 0 <= k < arms.len and arms[k] = Taken, k = one
    expect none_holds: when one = -1 and 0 <= k < arms.len, arms[k] != Taken
}
```

`lang::table_eval` states how both front ends and the evaluator give a
table over a scrutinee its value: as the `match` it means, whose arms are
tried in order, its `_` arm last. So its value is that of the first arm
that holds, or the otherwise where none does, as `lang::guarded_match` has
it. `table_eval_refines` confirms that this is the meaning above: where
the arms are disjoint, the first arm that holds is the one that does.

```fren
set_option fren.lint.undecidable "allow" in
pub comp table_eval {
    use self::ArmAt::Taken
    in arms: Seq<ArmAt>      -- what each arm but `_` does at the scrutinee's value, in order
    in values: Seq<Int>      -- each arm's body's value there
    in otherwise: Seq<Int>   -- the value of the `_` arm's body there, `[]` without one

    assume aligned: values.len = arms.len
    pub out first: Int := arms.index_of([Taken], 0)  -- the first arm that holds, `-1` if none does
    pub out value: Int       -- the table's value

    ensure first_held: when first >= 0, value = values[first]
    ensure otherwise_held: when first = -1 and otherwise != [], value = otherwise[0]
}

set_option fren.lint.undecidable "allow" in
refine table_eval_refines: table_eval refines table_match {
    k := 0,                  -- only the expectations read `k`
    one := first,
    disjoint? := arms.index_of([ArmAt::Taken], first + 1) = -1,
}
```

## Sets

`{a, b}` is the set of `a` and `b`, whose types must be the same, and `{}`
is the empty set. Membership, `x in s`, is a comparison, so `x in s in t`
is an error, and `not x in s` is `not (x in s)`. A membership's `in` must
be on the line where its left operand ends (see
[Lexical structure](Lexical.md#keywords)). After a path, `{` starts a
record literal, and after `match e`, the arms, so a set literal is never
written there. A `{` whose first expression is followed by `with` starts
a [record update](#record-updates) instead.

`{(a, b), (c, d)}` is a relation, the set of the pairs `(a, b)` and `(c,
d)`. A pair is written only as a member of a relation literal and as the
left operand of `in`, as in `(a, b) in r`: there is no type of pairs.
Parentheses make an expression, which a pair is not, so a pair in
parentheses is neither, as in `((a, b)) in r` and `{((a, b))}`.

`{}` has no member to give it a type, so it takes its type from where it
is written: it can only be [checked](Types.md#checking-and-synthesis)
against a type, as in `s = {}` or `s union {}`. Where it would have to
synthesize its own, as in `{}.card` or `{} = {}`, it is an error.

## Sequences

`[a, b]` is the sequence of `a` and then `b`, whose types must be the
same, and `[]` is the empty sequence, which takes its type from where it
is written, as `{}` does ([Checking and
synthesis](Types.md#checking-and-synthesis)). `q[i]` is the element of `q` at the position `i`,
counted from `0`. It is written without a space before `[`, as an
application is written without one before `(`, so `q[i][j]` indexes twice.
`x in q` says that `x` is an element of `q`; that a sequence occurs within
`q` is `q.contains?(t)`.

`q[i]` is unspecified unless `0 <= i < q.len`: out of range, it is the
value of an unknown function of `q` and `i`, which the checks hold for
every interpretation of, like a [function](Items.md#functions)'s. Such an
index is almost always a mistake, so the [definedness
check](../Check.md#definedness) reports an index that may be out of range,
given the conditions under which it is evaluated, its *guard*, read from
left to right:

- in `when C, D`, `D` is guarded by `C`, and in `unless C, D` by `not C`;
- in `if c then x else y`, `x` is guarded by `c`, and `y` by `not c`;
- in `a and b`, `b` is guarded by `a`, and in `a or b` by `not a`;
- in a [chained comparison](#chained-comparisons), as in its expansion
  with `and`, an operand is guarded by the comparisons before it: in
  `0 <= i < q.len < q[i]`, `q[i]` is guarded by `0 <= i and i < q.len`;
- in a `match` arm, the guard is guarded by the arm's pattern's matching
  where no earlier arm is taken, and the body by the arm's being the first
  that is taken: that and its guard's holding;
- a definition of a [`let` or `where`](Let.md#meaning) is guarded where its
  name is mentioned, as if written there, and not at all if it is never
  mentioned;
- in a [quantifier](Quantifiers.md#names), the body is guarded in each
  instance by what guards the quantifier, and the instances do not guard
  each other: an index must be in range in every instance where its guard
  holds;
- in a [table](#tables)'s row, as in the arm `_ if C => e` that it is,
  the condition is guarded by no earlier
  row's condition holding, and the value by that and the row's own
  condition: by the row's being the first that holds;
- guards nest by conjunction.

So `q != [] and q[0] = x` is defined, and `q[0] = x and q != []` is not,
though the two mean the same: the order of `and` and `or` changes only
definedness, never meaning.

`lang::guard` (see [Guards](Meaning.md#guards)) states which operands
are guarded, and by what, from the operand and the value of its
*condition*: that of `when`, `unless` or the conditional, or the left
operand of `and` or `or`. `lang::node` uses it to say which parts a layer
evaluates, and a layer is defined where every part it evaluates is. That a
part that is not evaluated changes neither the value nor the definedness
is the law `unevaluated` (see [Laws](MeaningLaws.md)), which is why the
definedness check asks for an index's range only under its guard.

## Relations

The relational operators, where `r` is a `Rel<A, B>`:

| Form | Meaning | Operands | Result |
|---|---|---|---|
| `r join q` | `(a, c)` for each `(a, b)` in `r` and `(b, c)` in `q` | `q: Rel<B, C>` | `Rel<A, C>` |
| `r.inverse` | `(b, a)` for each `(a, b)` in `r` | | `Rel<B, A>` |
| `r.closure` | the transitive closure: `(a, c)` if a chain of pairs of `r` leads from `a` to `c` | `A` and `B` the same | `Rel<A, A>` |
| `r.image(s)` | `b` for each `(a, b)` in `r` with `a` in `s` | `s: Set<A>` | `Set<B>` |
| `r.domain` | the first members of the pairs | | `Set<A>` |
| `r.range` | the second members of the pairs | | `Set<B>` |
| `r.card` | the number of pairs | | `Int` |

The closure is not reflexive: `(a, a)` is in `r.closure` only if a chain
leads from `a` back to `a`. `join` binds like `*` and `inter`, so `r union
q join p` is `r union (q join p)`.

`lang::relation_op` states which operand types each takes, and
`lang::pair_membership` which a pair's membership takes:

```fren
pub enum RelOp { Join, Inverse, Closure, Image, Domain, Range }

pub comp relation_op {
    use self::RelOp::{Closure, Domain, Image, Inverse, Join, Range}
    use self::ValueType::{RelTy, SetTy}
    in op: RelOp
    in r: Ty             -- the relation
    in s: Ty             -- the right operand of `join`, or the argument of `image`
    pub det out accepted?

    ensure rule: accepted? iff match op {
        Join => kind(r) = RelTy and kind(s) = RelTy and right(r) = left(s),
        Closure => kind(r) = RelTy and left(r) = right(r),
        Image => kind(r) = RelTy and kind(s) = SetTy and elem(s) = left(r),
        Inverse | Domain | Range => kind(r) = RelTy,
    }

    expect closure_endo: when op = Closure and accepted?, left(r) = right(r)
    expect only_relations: when accepted?, kind(r) = RelTy
    expect composable: when op = Join and kind(r) = RelTy and kind(s) = RelTy and right(r) = left(s), accepted?
    expect not_composable: when op = Join and kind(r) = RelTy and kind(s) = RelTy and right(r) != left(s), not accepted?
    expect join_relations_only: when op = Join and kind(s) != RelTy, not accepted?
    expect image_of_domain: when op = Image and kind(r) = RelTy and kind(s) = SetTy and elem(s) = left(r), accepted?
    expect image_of_other: when op = Image and kind(r) = RelTy and kind(s) = SetTy and elem(s) != left(r), not accepted?
    expect image_of_sets_only: when op = Image and kind(s) != SetTy, not accepted?
}

pub comp pair_membership {
    in x: Ty             -- the type of the pair's first member
    in y: Ty             -- of its second
    in r: Ty             -- the type of the right operand of `in`
    pub det out accepted?

    ensure rule: accepted? iff (kind(r) = ValueType::RelTy and left(r) = x and right(r) = y)

    expect pair_of_relation: when kind(r) = ValueType::RelTy and left(r) = x and right(r) = y, accepted?
    expect wrong_first: when kind(r) = ValueType::RelTy and left(r) != x, not accepted?
    expect wrong_second: when kind(r) = ValueType::RelTy and right(r) != y, not accepted?
    expect relations_only: when kind(r) != ValueType::RelTy, not accepted?
}
```

## Methods

`e.m` and `e.m(a, ...)` call the *method* `m` of the type of `e`, its
receiver. Methods belong to their type, as fields belong to a record: they
are not items, so they are never imported, and a spec's own `fn len`
never clashes with one. In `a.b`, `a` is first a binder of a `match`
arm, then an instance, then a variable, and then a
[constant](Items.md#constants): a record value, whose field `b` it reads,
or a value of a type with methods. A record has no methods.

A method's arguments are typed as a function's are. As for a function, a
method whose name ends in `?` returns a `Bool`, and only those do. A
method call mentions what its receiver and arguments mention, as a field
read does, and it is not a function application for the rules of
[linear arithmetic](#linear-arithmetic) and of constants: like a variant,
a method has a fixed meaning. So `2 * s.len` is linear, and
`const N: Int := "abc".len` is a constant.

The methods of `Int`, and of `Nat`, where `x` is the receiver:

| Method | Meaning | Result |
|---|---|---|
| `x.abs` | the absolute value: `x` if `x >= 0`, else `-x` | `Int` |
| `x.min(y)` | the lesser of `x` and `y` | `Nat` if both are, else `Int` |
| `x.max(y)` | the greater of `x` and `y` | `Nat` if both are, else `Int` |

Each is a conditional, such as `if x < 0 then -x else x`, so each stays
within linear arithmetic: `(a - b).abs <= TOLERANCE` and `2 * x.min(y)`
are linear. A literal is not a receiver as written, since `3.abs` is not
an identifier: write `(3).abs`, or `(-3).abs`. `lang::int_methods` states
their laws. It allows `eq_op`, which fires on `x.min(x)` and `x.max(x)`,
since those laws are what the lint relies on:

```fren
set_option fren.lint.eq_op "allow" in
pub comp int_methods {
    in x: Int
    in y: Int

    expect abs_nonnegative: x.abs >= 0
    expect abs_cases: (x >= 0 and x.abs = x) or (x < 0 and x.abs = -x)
    expect abs_negation: (-x).abs = x.abs
    expect abs_triangle: (x + y).abs <= x.abs + y.abs
    expect abs_bounds: -x.abs <= x <= x.abs
    expect min_below: x.min(y) <= x and x.min(y) <= y
    expect min_either: x.min(y) = x or x.min(y) = y
    expect max_above: x.max(y) >= x and x.max(y) >= y
    expect max_either: x.max(y) = x or x.max(y) = y
    expect min_max_sum: x.min(y) + x.max(y) = x + y
    expect commutative: x.min(y) = y.min(x) and x.max(y) = y.max(x)
    expect abs_is_max: x.abs = x.max(-x)
    expect idempotent: x.min(x) = x and x.max(x) = x
}
```

`div` and `mod` of a [`Nat`](#natural-numbers) by a positive constant are
`Nat`s, as Lean's division and remainder on `Nat` are, which agree with
the Euclidean ones there. By a negative constant, they are `Int`s: `n div
-2` is at most 0, and though `n mod -2` is never negative, Lean has no
`Nat` remainder by a negative number, so it stays an `Int` rather than
needing a conversion. `min` and `max` of two `Nat`s are `Nat`s, and of a
`Nat` and an `Int`, the `Nat` is widened. `abs` is always an `Int`, even of
a `Nat`, where it is the `Nat` itself, widened: Lean's `Int.natAbs` would
be a `Nat`, but a `Nat`'s `abs` is better written as the `Nat`.
`lang::nat_result` states when these are `Nat`s:

```fren
pub enum NatOp { Div, Mod, Min, Max, Abs }

pub comp nat_result {
    use self::NatOp::{Abs, Div, Max, Min, Mod}
    in op: NatOp
    in a_nat?                -- the dividend, or the receiver, is a `Nat`
    in b_nat?                -- the argument of `min` or `max` is a `Nat`
    in positive?             -- the divisor of `div` or `mod` is positive
    pub det out nat?

    ensure rule: nat? iff match op {
        Div | Mod => a_nat? and positive?,
        Min | Max => a_nat? and b_nat?,
        Abs => false,
    }

    expect only_of_nats: when nat?, a_nat?
    expect abs_widens: when op = Abs, not nat?
}
```

The values of every other [ordered type](Types.md#ordered-types) have the
methods `min` and `max` too, where `x` is the receiver and `y` a value of
the same type: the lesser and the greater of the two, in the type's order.
So `String`s have them, as do the values of an enumeration, record or
newtype declared [`ordered`](Items.md#ordered-declarations). With
`pub ordered enum Severity { Silent, Info, Warning, Error }`,
`worst.max(Info)` is `Info` if `worst` is `Silent` or `Info`, and `worst`
otherwise. Like an `Int`'s, each is a conditional: `x.min(y)` is
`if x <= y then x else y`, so that it is in the [decidable
core](Decidability.md) exactly when `x <= y` is. A variant is a receiver
too, as in `Info.max(worst)` or `(Severity::Info).max(worst)`. An
enumeration, record or newtype that is not ordered has neither, and its
`x.min(y)` is an error that says to declare it `ordered`; nor has it any
other method. `lang::enumeration_order` and `lang::lexicographic` (see
[Items](Items.md#ordered-declarations)) state their orders.

The methods of `String`, where `s` is the receiver:

| Method | Meaning | Result |
|---|---|---|
| `s.len` | the number of characters | `Int` |
| `s.starts_with?(p)` | `p` is a prefix of `s` | `Bool` |
| `s.ends_with?(p)` | `p` is a suffix of `s` | `Bool` |
| `s.contains?(t)` | `t` occurs in `s`; every string contains `""` | `Bool` |
| `s.matches?(p)` | the whole of `s` matches the [pattern](#patterns) `p`, a string literal | `Bool` |
| `s.at(i)` | the character at position `i`, from 0, as a string; `""` unless `0 <= i < s.len` | `String` |
| `s.slice(i, n)` | up to `n` characters from position `i`, fewer at the end of `s`; `""` unless `0 <= i < s.len` and `n > 0` | `String` |
| `s.index_of(t, i)` | the first position at or after `i` where `t` occurs; `i` if `t` is `""` and `0 <= i <= s.len`; otherwise `-1` | `Int` |
| `s.replace(a, b)` | `s` with the first occurrence of `a` replaced by `b`; `b ++ s` if `a` is `""` | `String` |
| `s.replace_all(a, b)` | `s` with each occurrence of `a`, from the left and not overlapping, replaced by `b`; `s` if `a` is `""` | `String` |
| `s.min(t)`, `s.max(t)` | the lesser and the greater of `s` and `t`, as `<` orders them | `String` |

`lang::string_methods` states the table as laws, for every string and
position. Several of them search a string or slice it at a position that
is not a constant, which is outside the [decidable
core](Decidability.md#strings), so it allows that. It also allows
`empty_argument`, `manual_method` and `redundant_slicing`, which fire on
some of the laws, such as `s.contains?("")`, since those laws are what the
lints rely on:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.empty_argument "allow" in
set_option fren.lint.manual_method "allow" in
set_option fren.lint.redundant_slicing "allow" in
pub comp string_methods {
    in s: String
    in t: String
    in i: Int
    in n: Int

    expect empty_everywhere: s.contains?("") and s.starts_with?("") and s.ends_with?("")
    expect prefix_occurs: when s.starts_with?(t), s.contains?(t)
    expect suffix_occurs: when s.ends_with?(t), s.contains?(t)
    expect concat_length: (s ++ t).len = s.len + t.len
    expect concat_prefix: (s ++ t).starts_with?(s) and (s ++ t).ends_with?(t)
    expect at_is_slice: s.at(i) = s.slice(i, 1)
    expect at_outside: when i < 0 or i >= s.len, s.at(i) = ""
    expect slice_outside: when i < 0 or i >= s.len or n <= 0, s.slice(i, n) = ""
    expect slice_short: when n >= 0, s.slice(i, n).len <= n
    expect slice_whole: s.slice(0, s.len) = s
    expect slice_occurs: s.contains?(s.slice(i, n))
    expect index_of_empty: when 0 <= i <= s.len, s.index_of("", i) = i
    expect index_of_found: when s.index_of(t, i) >= 0, s.slice(s.index_of(t, i), t.len) = t
    expect index_of_absent: when not s.contains?(t), s.index_of(t, i) = -1
    expect replace_empty: s.replace("", t) = t ++ s
    expect replace_absent: when not s.contains?(t), s.replace(t, "x") = s
    expect replace_all_empty: s.replace_all("", t) = s
    expect replace_all_absent: when not s.contains?(t), s.replace_all(t, "x") = s
}
```

The methods of `Set<T>`:

| Method | Meaning | Result |
|---|---|---|
| `s.card` | the number of members | `Int` |

A relation has the method `card` and the [relational](#relations) methods
`inverse`, `closure`, `image`, `domain` and `range`.

The methods of `Seq<T>` are those of `String` but `matches?` and
`replace_all`, with the same meanings and values at the edges: an argument
that is a `String` for a string is a `Seq<T>` here, `q.at(i)` is `[q[i]]`
or `[]`, and `q.len` is the number of elements. Two more are a sequence's
only:

| Method | Meaning | Result |
|---|---|---|
| `q.update(i, x)` | `q` with `x` at position `i`; `q` itself unless `0 <= i < q.len` | `Seq<T>` |
| `q.rev` | `q` reversed | `Seq<T>` |

Every method is total: its value at the edges, such as `"abc".at(5)`, is the
one the solver's theory of strings gives it, so that Lean and the solver
agree.

`lang::collection_methods` states laws of the methods and operators of
sequences, sets and relations: the methods of `Seq<T>` that it shares
with `String`, with the same meanings, and those of its own; the set
operators `union`, `inter`, `minus` and `subset`, and `card`; and the
relational methods and `join`, which a relation over a finite type keeps
in the core. `rev`, `++`, `at`, `slice`, `contains?`, `index_of` and
`replace` on sequences, and `starts_with?` and `ends_with?` with an
argument that is not a literal, are outside the [decidable
core](Decidability.md#sequences), so it allows that. As
`lang::string_methods` does, it also allows the lints that fire on the laws
they rely on, `empty_argument`, `manual_method`,
`redundant_method_chain` and `redundant_slicing`:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.empty_argument "allow" in
set_option fren.lint.manual_method "allow" in
set_option fren.lint.redundant_method_chain "allow" in
set_option fren.lint.redundant_slicing "allow" in
pub comp collection_methods {
    in p: Seq<Int>
    in q: Seq<Int>
    in i: Int
    in n: Int
    in x: Int
    in s: Set<Int>
    in t: Set<Int>
    in r: Rel<Bool, Bool>

    expect rev_twice: q.rev.rev = q
    expect rev_length: q.rev.len = q.len
    expect concat_length: (p ++ q).len = p.len + q.len
    expect update_length: q.update(i, x).len = q.len
    expect update_reads: when 0 <= i < q.len, q.update(i, x)[i] = x
    expect update_outside: when i < 0 or i >= q.len, q.update(i, x) = q
    expect at_outside: when i < 0 or i >= q.len, q.at(i) = []
    expect at_inside: when 0 <= i < q.len, q.at(i) = [q[i]]
    expect at_is_slice: q.at(i) = q.slice(i, 1)
    expect slice_outside: when i < 0 or i >= q.len or n <= 0, q.slice(i, n) = []
    expect slice_whole: q.slice(0, q.len) = q
    expect slice_short: when n >= 0, q.slice(i, n).len <= n
    expect slice_occurs: q.contains?(q.slice(i, n))
    expect empty_contained: q.contains?([]) and q.starts_with?([]) and q.ends_with?([])
    expect prefix_occurs: when q.starts_with?(p), q.contains?(p)
    expect suffix_occurs: when q.ends_with?(p), q.contains?(p)
    expect concat_prefix: (p ++ q).starts_with?(p) and (p ++ q).ends_with?(q)
    expect index_of_empty: when 0 <= i <= q.len, q.index_of([], i) = i
    expect index_of_found: when q.index_of(p, i) >= 0, q.slice(q.index_of(p, i), p.len) = p
    expect index_of_absent: when not q.contains?(p), q.index_of(p, i) = -1
    expect replace_empty: q.replace([], p) = p ++ q
    expect replace_absent: when not q.contains?(p), q.replace(p, [x]) = q

    expect union_contains: s subset (s union t) and t subset (s union t)
    expect inter_within: (s inter t) subset s and (s inter t) subset t
    expect minus_disjoint: ((s minus t) inter t) = {}
    expect union_card: (s union t).card <= s.card + t.card

    expect inverse_twice: r.inverse.inverse = r
    expect inverse_swaps: r.inverse.domain = r.range and r.inverse.range = r.domain
    expect closure_contains: r subset r.closure
    expect closure_transitive: r.closure join r.closure subset r.closure
    expect image_of_domain: r.image(r.domain) = r.range
}
```

`lang::method_type` states the table, and checks it against the
[Boolean names](Types.md#boolean-names) rule. Its result is the kind after
widening: `nat_result` says when `min` and `max` are `Nat`s instead,
and `ordered?` that the receiver is of an [ordered
type](Types.md#ordered-types) other than a number: a `String`, or an
enumeration, record or newtype declared `ordered`, whose `min` and `max`
are of its type:

```fren
pub enum Method {
    Len, StartsWith, EndsWith, Contains, Matches, At, Slice, IndexOf, Replace, ReplaceAll, Card,
    Inverse, Closure, Image, Domain, Range, Update, Rev, Abs, Min, Max,
}

pub comp method_type {
    use self::Method::{
        Abs,
        At,
        Card,
        Closure,
        Contains,
        Domain,
        EndsWith,
        Image,
        IndexOf,
        Inverse,
        Len,
        Matches,
        Max,
        Min,
        Range,
        Replace,
        ReplaceAll,
        Rev,
        Slice,
        StartsWith,
        Update,
    }
    use self::ValueType::{BoolTy, EnumTy, IntTy, NatTy, RecordTy, RelTy, SeqTy, SetTy, StringTy}
    in method: Method
    in receiver: ValueType
    in ordered?

    assume ordered_kinds: when ordered?, receiver in {StringTy, EnumTy, RecordTy}
    pub det out accepted?
    pub det out result: ValueType
    pub det out n_params: Int

    ensure receivers: accepted? iff match method {
        Card => receiver in {SetTy, RelTy},
        Inverse | Closure | Image | Domain | Range => receiver = RelTy,
        Update | Rev => receiver = SeqTy,
        Matches | ReplaceAll => receiver = StringTy,
        Abs => receiver in {IntTy, NatTy},
        Min | Max => receiver in {IntTy, NatTy} or ordered?,
        _ => receiver in {StringTy, SeqTy},
    }
    ensure results: result = match method {
        StartsWith | EndsWith | Contains | Matches => BoolTy,
        Len | IndexOf | Card | Abs => IntTy,
        Min | Max => if ordered? then receiver else IntTy,
        Inverse | Closure => RelTy,
        Image | Domain | Range => SetTy,
        _ => receiver,
    }
    ensure arities: n_params = match method {
        Len | Card | Inverse | Closure | Domain | Range | Rev | Abs => 0,
        Slice | IndexOf | Replace | ReplaceAll | Update => 2,
        _ => 1,
    }

    expect bool_methods_named: when accepted?, result = BoolTy iff (match method {
        Len => "len",
        StartsWith => "starts_with?",
        EndsWith => "ends_with?",
        Contains => "contains?",
        Matches => "matches?",
        At => "at",
        Slice => "slice",
        IndexOf => "index_of",
        Replace => "replace",
        ReplaceAll => "replace_all",
        Card => "card",
        Inverse => "inverse",
        Closure => "closure",
        Image => "image",
        Domain => "domain",
        Range => "range",
        Update => "update",
        Rev => "rev",
        Abs => "abs",
        Min => "min",
        Max => "max",
    }).ends_with?("?")
    expect unordered_enumerations: when receiver = EnumTy and not ordered?, not accepted?
    expect unordered_records: when receiver = RecordTy and not ordered?, not accepted?
    expect ordered_bounds: when ordered? and method in {Min, Max}, accepted? and result = receiver
}
```

### Patterns

The argument of `matches?` is a pattern, a regular expression written as
a string literal, usually a raw one: `s.matches?(r"[a-z][a-z0-9_]*")`. It
is a subset of POSIX extended regular expressions, and the whole of `s`
must match it:

| Pattern | Matches |
|---|---|
| `c` | the character `c`, other than `\`, `.`, `[`, `]`, `(`, `)`, `*`, `+`, `?`, `{`, `}`, `\|` and `^` |
| `\c` | `c`, for `c` one of those, or `-`, which is literal outside a class but marks a range in one |
| `.` | any character |
| `[a-z_]` | a character in the class: each item is a character or a range `a-z` |
| `[^...]` | a character not in the class |
| `p q` | `p`, then `q` |
| `p\|q` | `p` or `q` |
| `p*`, `p+`, `p?` | `p` any number of times, at least once, at most once |
| `p{m}`, `p{m,n}` | `p` exactly `m` times, from `m` to `n` times |
| `(p)` | `p` |

There are no anchors, since the whole string must match, no
back-references, and no classes such as `\d`: `[0-9]` is short enough.
A pattern is not a value: the argument of `matches?` must be a literal,
not a variable or a constant. A pattern that does not parse is an error at
the literal. A range must not be reversed: `lang::char_range` states this,
from the code points of the characters before and after its `-`:

```fren
type CodePoint := Int is 0..=MAX_CHAR

pub comp char_range {
    in low: CodePoint    -- the code point of the character before `-`
    in high: CodePoint   -- the code point of the character after it
    pub det out accepted?

    ensure rule: accepted? iff low <= high

    expect singleton_ok: when low = high, accepted?
}
```

## Orderings of ordered types

How two values of an ordered type compare is planned from the type alone,
before any value is compared, and the plan is what both front ends render
and the evaluator follows: a number's and a string's own order, an
enumeration's variants' positions, a newtype's field's plan, and, for a
record, a plan for each of its fields, in the order declared. Where
`lang::Plan` is the kind of a plan, `lang::plan_of` the kind that a type's
plan has, and `lang::FieldName` a record's field's name (see
[Records](#records)), `lang::order_plan` states it, from
the type, the types declared `ordered`, and, for a record, its fields'
names and types, and what its plan compares, which the plan gives:

```fren
-- `Number` is an `Int`'s or a `Nat`'s order, `Text` a `String`'s,
-- `Position` that of an enumeration's variants, `AsField` a newtype's
-- field's, and `Fields` a record's fields', lexicographically.
pub enum Plan { Number, Text, Position, AsField, Fields }

-- The kind of plan of a type of the kind `k`, a newtype if `wrapper?`.
pub fn plan_of(k: ValueType, wrapper?): Plan := match k {
    ValueType::IntTy | ValueType::NatTy => Plan::Number,
    ValueType::StringTy => Plan::Text,
    ValueType::EnumTy => Plan::Position,
    _ => if wrapper? then Plan::AsField else Plan::Fields,
}

set_option fren.lint.undecidable "allow" in
pub comp order_plan {
    in t: Ty
    in ordered_items: Set<TypeName>   -- the enumerations, records and newtypes declared `ordered`
    in fields: Seq<FieldName>         -- for a record: its fields, in the order declared
    in field_types: Seq<Ty>           -- their types, in the same order
    in compared: Seq<FieldName>       -- for a record: the fields that its plan compares, in order
    in field_plans: Seq<Plan>         -- and the kind of each one's plan
    in k: Int                         -- any position among the fields

    assume aligned: field_types.len = fields.len
    pub out planned?                  -- `t` has a plan
    pub out plan: Plan

    ensure only_ordered: when planned?, ordered_in?(kind(t), type_name(t), ordered_items)
    ensure kind_of_plan: when planned?, plan = plan_of(kind(t), newtype?(t))
    ensure in_order: when planned? and plan = Plan::Fields, compared = fields and field_plans.len = fields.len
    ensure each_field: when planned? and plan = Plan::Fields and 0 <= k < fields.len, field_plans[k] = plan_of(kind(field_types[k]), newtype?(field_types[k]))

    expect unordered_unplanned: unless ordered_in?(kind(t), type_name(t), ordered_items), not planned?
}
```

A record's plan compares its fields in turn: where `fields` says how each
of one value's fields compares with the other's, in the order declared,
the values compare as the first field that differs, and are equal when
none does. `lang::lexicographic` states this, and so the laws of an
order hold of an ordered record's, as they do of its fields' types: it is
total, asymmetric, transitive and antisymmetric, and `min` and `max` are a
least and a greatest of their operands, as `test/ui/lang/ordered_structs.fren`
checks in both front ends:

```fren
pub enum Comparison { Less, Equal, Greater }

set_option fren.lint.undecidable "allow" in
pub comp lexicographic {
    use self::Comparison::Equal
    in fields: Seq<Comparison>    -- how each field of one value compares with the other's, in order
    in k: Int                     -- any position among the fields
    pub out decider: Int          -- the first field that differs, `-1` if none does
    pub out result: Comparison    -- how the values compare

    ensure decided: when decider != -1, 0 <= decider < fields.len and fields[decider] != Equal
    ensure earliest: when 0 <= k < fields.len and fields[k] != Equal, 0 <= decider <= k
    ensure rule: result = (if decider = -1 then Equal else fields[decider])

    expect no_fields: when fields = [], result = Equal
    expect first_decides: when k = 0 and fields != [] and fields[0] != Equal, result = fields[0]
    expect differs: when 0 <= k < fields.len and fields[k] != Equal, result != Equal
}
```

## Types of operators

`lang::operator_type` states the operand and result types of the
[operators](#operators) and of conditionals. `a` and `b` are the types of
the operands, or of a conditional's branches, and `cond` the type of its
condition. For a prefix operator, `b` is `a`. `result` is the kind of the
result's type, after [widening](#natural-numbers). `Ty`, `kind`, `type_name` and `ValueType` are declared in
[Types](Types.md), where `ordered_type` says which types are ordered, and
`newtype_operator` above says which operators a newtype has. A [pattern test](#pattern-tests), whose right is a
pattern rather than an operand, is typed in its own section.

```fren
-- `Logic` is `when`, `unless`, `iff`, `or`, `and` and `not`; `Ordering` is
-- `<`, `<=`, `>` and `>=`; `Addition` is `+`; `Multiplication` is `*`; `Subtraction` is
-- an infix `-`; `Negation` is a prefix `-`, and `div` and `mod` are typed as it is,
-- unless `nat_result` makes them `Nat`s; `Concat` is `++`;
-- `SetAlgebra` is `union`, `inter` and `minus`, on sets or relations. For
-- `Membership`, `a` is the element and `b` the set; a pair's membership,
-- and `join`, are typed by `pair_membership` and `relation_op`. The arms of a `match` are typed as a
-- conditional's branches, pairwise.
pub enum Operator {
    Logic, Equality, Ordering, Addition, Multiplication, Subtraction, Negation, Concat, Membership, SetAlgebra, Subset,
    Conditional,
}

pub comp operator_type {
    use self::Operator::{
        Addition,
        Concat,
        Conditional,
        Equality,
        Logic,
        Membership,
        Multiplication,
        Negation,
        Ordering,
        SetAlgebra,
        Subset,
        Subtraction,
    }
    use self::ValueType::{
        AbstractTy,
        BoolTy,
        EnumTy,
        IntTy,
        NatTy,
        RecordTy,
        RelTy,
        SeqTy,
        SetTy,
        StringTy,
    }
    in op: Operator
    in a: Ty
    in b: Ty
    in cond: Ty
    in inner_has?            -- for `+` or `-` of a newtype `a`: its underlying type is a newtype that has it itself
    in ordered_items: Set<TypeName>  -- the enumerations, records and newtypes declared `ordered`

    -- There is one `Bool` type, one `Int` type and one `Nat` type.
    assume primitive_unique: when kind(a) = kind(b) and kind(a) in {BoolTy, IntTy, NatTy, StringTy}, a = b
    -- A newtype is a record.
    assume newtype_record: (when newtype?(a), kind(a) = RecordTy) and (when newtype?(b), kind(b) = RecordTy)
    assume inner_newtypes: when inner_has?, newtype?(under(a)) and kind(under(a)) = RecordTy
    pub out accepted?
    pub out result: ValueType

    -- Whether `a` is ordered, and whether a newtype `a` has `+` or `-`.
    inst order: ordered_type { base := a, patterned? := false, ordered_items }
    inst sums: newtype_operator {
        op := if op = Subtraction then NewtypeOp::Subtraction else NewtypeOp::Addition,
        underlying := under(a),
        ordered? := order.ordered?,
        inner_has?,
    }

    ensure accepted: accepted? iff match op {
        Logic => kind(a) = BoolTy and kind(b) = BoolTy,
        Equality => a = b or (kind(a) in {IntTy, NatTy} and kind(b) in {IntTy, NatTy}),
        Ordering => (kind(a) in {IntTy, NatTy} and kind(b) in {IntTy, NatTy}) or (a = b and order.ordered?),
        Addition | Subtraction => (kind(a) in {IntTy, NatTy} and kind(b) in {IntTy, NatTy})
            or (a = b and newtype?(a) and sums.accepted?),
        Multiplication | Negation => kind(a) in {IntTy, NatTy} and kind(b) in {IntTy, NatTy},
        Concat => a = b and kind(a) in {StringTy, SeqTy},
        Membership => kind(b) in {SetTy, SeqTy} and (elem(b) = a or (kind(a) = NatTy and kind(elem(b)) = IntTy)),
        SetAlgebra | Subset => a = b and kind(a) in {SetTy, RelTy},
        Conditional => kind(cond) = BoolTy and (a = b or (kind(a) in {IntTy, NatTy} and kind(b) in {IntTy, NatTy})),
    }
    ensure results: result = match op {
        Addition | Multiplication => if newtype?(a) then RecordTy else if kind(a) = NatTy and kind(b) = NatTy then NatTy else IntTy,
        Subtraction => if newtype?(a) then RecordTy else IntTy,
        Negation => IntTy,
        Conditional => if a = b then kind(a) else IntTy,
        Concat | SetAlgebra => kind(a),
        _ => BoolTy,
    }

    -- Only a `Nat` is widened.
    expect no_mixing: when accepted? and op != Membership and kind(a) != NatTy and kind(b) != NatTy, a = b
    expect member_typed: when op = Membership and accepted? and kind(a) != NatTy, elem(b) = a
    expect bool_valued: unless op in {Addition, Multiplication, Subtraction, Negation, Concat, SetAlgebra, Conditional},
        result = BoolTy
    expect strings_ordered: when op = Ordering and kind(a) = StringTy and a = b, accepted?
    expect concat_closed: when op = Concat and accepted?, result = kind(a)
    expect sequences_unordered: when op = Ordering and kind(a) = SeqTy, not accepted?
    expect unordered_enumerations: when op = Ordering and kind(a) = EnumTy and not type_name(a) in ordered_items,
        not accepted?
    expect records_opt_in: when op = Ordering and kind(a) = RecordTy and a = b, accepted? iff type_name(a) in ordered_items
    -- A value of an abstract type is only compared, or found in a set.
    expect abstract_equality_only: when accepted? and op != Conditional and kind(a) = AbstractTy,
        op in {Equality, Membership}

    -- Rows of the table of operators.
    expect same_types_equal: when op = Equality and a = b, accepted?
    expect bools_equal: when op = Equality and kind(a) = BoolTy and kind(b) = BoolTy, accepted?
    expect ints_ordered: when op = Ordering and kind(a) = IntTy and kind(b) = IntTy, accepted?
    expect enumerations_ordered: when op = Ordering and kind(a) = EnumTy and type_name(a) in ordered_items and a = b,
        accepted?
    expect strings_concatenate: when op = Concat and kind(a) = StringTy and kind(b) = StringTy, accepted?
    expect sequences_concatenate: when op = Concat and kind(a) = SeqTy and a = b, accepted?
    expect set_members: when op = Membership and kind(b) = SetTy and elem(b) = a, accepted?
    expect sequence_members: when op = Membership and kind(b) = SeqTy and elem(b) = a, accepted?
    expect members_of_collections: when op = Membership and not kind(b) in {SetTy, SeqTy}, not accepted?
    expect sets_combine: when op = SetAlgebra and kind(a) = SetTy and a = b, accepted?
    expect relations_subset: when op = Subset and kind(a) = RelTy and a = b, accepted?
    expect boolean_condition: when op = Conditional and kind(cond) != BoolTy, not accepted?
    expect no_mixed_arithmetic: when op = Addition and kind(a) = IntTy and kind(b) = BoolTy, not accepted?
    expect nats_add: when op = Addition and kind(a) = NatTy and kind(b) = NatTy, accepted? and result = NatTy
    expect widened_sums: when op = Addition and kind(a) = NatTy and kind(b) = IntTy, accepted? and result = IntTy
    expect never_truncates: when op in {Subtraction, Negation} and kind(a) in {IntTy, NatTy}, result = IntTy

    -- A newtype has the orderings if it is declared `ordered`, an `Int`'s
    -- `+` and `-` and a `Nat`'s `+`, which give the newtype, but nothing
    -- else of its underlying type, and never mixes.
    expect newtypes_ordered: when op = Ordering and a = b and newtype?(a), accepted? iff type_name(a) in ordered_items
    expect nat_newtypes_add: when op = Addition and a = b and newtype?(a) and kind(under(a)) = NatTy, accepted?
    expect nat_newtypes_no_difference: when op = Subtraction and newtype?(a) and kind(under(a)) = NatTy, not accepted?
    expect newtype_sums: when op in {Addition, Subtraction} and newtype?(a) and accepted?, a = b and result = RecordTy
    expect newtypes_not_multiplied: when op in {Multiplication, Negation} and newtype?(a), not accepted?
    expect newtypes_apart: when not op is Membership | Conditional and newtype?(a) and a != b, not accepted?
    expect nat_compared_with_int: when op in {Equality, Ordering} and kind(a) = NatTy and kind(b) = IntTy, accepted?
    -- Sets of different element types are different types.
    expect sets_of_different_types: when op = Equality and kind(a) = SetTy and kind(b) = SetTy and elem(a) != elem(b),
        not accepted?
}

-- The checks for every chapter under Lang/ that shares the module `lang`.
#fren_check
```

## Names

A path names a variable of the enclosing component, a binder of an
enclosing [`match` arm](#matches), a bound name of an enclosing
[quantifier](Quantifiers.md) or a name of an enclosing [`let` or
`where`](Let.md) (the innermost, which may
[shadow](Components.md#shadowing) the others and the variables), a
[constant](Items.md#constants), a [function](#function-applications) that
it applies, a record that it builds, or a variant (see [Modules and
visibility](Modules.md#resolution)). A constant stands for its value. A variant can be written
with its enumeration's name, `Mode::Heat`, or by its bare name once brought
into scope by `use`. `w.x` names the variable `x` of the instance `w` (see
[Instances](Instances.md#instance-variables)), or of the binder `w` of a
[global expectation](Global.md), and otherwise reads the field `x` of
the value `w`, a variable or a [constant](Items.md#constants) (see
[Records](#records)), or applies its [method](#methods) `x`.
