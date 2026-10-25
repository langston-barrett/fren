# Expressions

```
expr  := ("when" | "unless") iff "," expr
       | iff
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
       | IDENT ("." IDENT)+ "(" expr ("," expr)* ")"
       | "match" expr "{" arm ("," arm)* [","] "}"
       | "{" [expr ("," expr)* [","]] "}"
field-init := IDENT [":=" expr]
arm   := pattern "=>" expr
pattern := "_" | ["|"] alternative ("|" alternative)*
alternative := path ["(" pattern-binder ("," pattern-binder)* ")"]
pattern-binder := DECL | "_"
```

In `atom "." IDENT`, the atom is one that ends in `)` or `}`, and there
are no spaces around the `.`: after a name, `.` is part of the
[identifier](Lexical.md#identifiers), as in `p.x`. The notation is
[the grammar's](../Grammar.md#notation), where `DECL` is an identifier that
declares a name.

## Operators

From lowest to highest precedence, where forms of the same level bind
equally tightly:

| Level | Form | Meaning | Operand types | Result | Associativity |
|---|---|---|---|---|---|
| 1 | `when C, D` | C implies D | `Bool` | `Bool` | right |
| 1 | `unless C, D` | not C implies D | `Bool` | `Bool` | right |
| 2 | `A iff B` | A if and only if B | `Bool` | `Bool` | none |
| 3 | `A or B` | disjunction | `Bool` | `Bool` | left |
| 4 | `A and B` | conjunction | `Bool` | `Bool` | left |
| 5 | `not A` | negation | `Bool` | `Bool` | |
| 6 | `A = B`, `A != B` | equality, disequality | any, both the same | `Bool` | none |
| 6 | `A < B`, `A <= B`, `A > B`, `A >= B` | ordering | `Int`, or `String` | `Bool` | [chains](#chained-comparisons) |
| 6 | `A in S` | membership | `T` and `Set(T)` or `Seq(T)`, or a pair `(a, b)` and `Rel(A, B)` | `Bool` | none |
| 6 | `S subset T` | `S` is a subset of `T`, not necessarily strict | `Set(T)`, or `Rel(A, B)` | `Bool` | none |
| 6 | `A is P` | [pattern test](#pattern-tests): the pattern `P` matches `A` | an enumeration, and a pattern | `Bool` | none |
| 7 | `A + B`, `A - B` | addition, subtraction | `Int` | `Int` | left |
| 7 | `A ++ B` | concatenation | `String`, or `Seq(T)` | the same | left |
| 7 | `S union T`, `S minus T` | union, difference | `Set(T)`, or `Rel(A, B)` | the same | left |
| 8 | `A * B` | multiplication | `Int` | `Int` | left |
| 8 | `A div K`, `A mod K` | [division and remainder](#division-and-remainder) by a constant | `Int` | `Int` | left |
| 8 | `S inter T` | intersection | `Set(T)`, or `Rel(A, B)` | the same | left |
| 8 | `R join Q` | composition | `Rel(A, B)` and `Rel(B, C)` | `Rel(A, C)` | left |
| 9 | `-A` | negation | `Int` | `Int` | |

- In `when C, D` and `unless C, D`, `C` ends at the first top-level `,`, and
  `D` extends as far right as possible. `D` may itself be a `when` or
  `unless` without parentheses: `when a?, when b?, c?`. A `when` or `unless`
  that is the operand of another operator must be parenthesized.
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

pub enum Assoc { Left, Right, NonAssoc }

pub comp operand {
    in outer: Int        -- the precedence of the operator
    in inner: Int        -- the precedence of its operand's operator
    in assoc: Assoc      -- the associativity of the operator
    in right?            -- the operand is on the operator's right
    pub out bare?        -- the operand can be written without parentheses

    req tighter: when inner > outer, bare?
    req looser: when inner < outer, not bare?
    req left: when inner = outer and assoc = Assoc::Left, bare? iff not right?
    req right: when inner = outer and assoc = Assoc::Right, bare? iff right?
    req non_assoc: when inner = outer and assoc = Assoc::NonAssoc, not bare?

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
`String`s if `s` is one, and a message about a comparison's operands
names its operator: in `0 <= i < "a"`, `"a"` is not an `Int`, as the
operands of `<` must be.

A chain that mixes directions, such as `a < b > c`, is an error: it reads
as a mistake more often than as `a < b and c < b`. So is a chain with `=`,
`!=`, `in` or `subset`, which do not chain: `a? = b? = c?` would read as
either `a? = b? and b? = c?` or `(a? = b?) = c?`, and those differ. The
message points at the first operator that does not chain, or else at the
first that orders the other way from the first. A comparison in
parentheses is an operand like any other, as in `(a < b) =
c?`. `lang::comparison_chain` states which chains are accepted, from how
many of their operators are of each kind; one operator alone is a
comparison, not a chain:

```fren
pub comp comparison_chain {
    in n_ascending: Int     -- operators `<` and `<=`
    in n_descending: Int    -- operators `>` and `>=`
    in n_other: Int         -- operators `=`, `!=`, `in` and `subset`
    pub det out accepted?

    assume counts: n_ascending >= 0 and n_descending >= 0 and n_other >= 0
    assume compares: n_ascending + n_descending + n_other >= 1

    req rule: accepted? iff (n_ascending + n_descending + n_other = 1
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
neither has the same value in every behaviour. What an expression
mentions is decided from its parts, as `lang::mentions` states:

- A literal mentions nothing, and neither does a
  [constant](Items.md#constants), a variant without a payload, or any
  other path of more than one segment, such as `m::RATE`.
- A variable mentions itself, and so does a variable of an
  [instance](Instances.md#instance-variables) or a field read from a
  variable. A variable declared as `RATE!` shadows the constant `RATE`
  (see [Shadowing](Components.md#shadowing)), so `RATE` is then a
  variable.
- A [defined output](Components.md#defined-outputs) mentions what its
  definition mentions, and a [binder](#matches) what its scrutinee
  mentions.
- A [variant](#variants-with-payloads) or a [record literal](#records)
  mentions what its arguments or fields mention: its value is fixed.
- A [method](#methods) call mentions what its receiver and arguments
  mention: a method has a fixed meaning.
- An application of an uninterpreted function mentions the function: its
  value is unknown even at fixed arguments.
- An application of a defined function mentions what its arguments
  mention: its value is fixed by theirs.
- Every other expression mentions what its parts mention: an operator,
  `when` and `unless`, a conditional, a `match` (its scrutinee and the
  bodies of its arms), a [pattern test](#pattern-tests) (its scrutinee),
  indexing `q[i]`, a field read from an expression that is not a name,
  such as `R { a := x }.a`, and a literal of a set, pair or sequence.

```fren
-- The kinds of expression, for what one mentions. `Literal` is a literal;
-- `Constant` is a constant, a variant without a payload, or a path of more
-- than one segment; `Variable` is a variable, an instance's variable, or a
-- field read from one; `Construction` is a variant with a payload or a
-- record literal; `Uninterpreted` and `Defined` are applications of
-- uninterpreted and defined functions; `Compound` is an operator, `when`
-- or `unless`, a conditional, a `match`, a pattern test, indexing, a field
-- read from an expression that is not a name, or a literal of a set, pair
-- or sequence.
pub enum ExprKind {
    Literal, Constant, Variable, DefinedOutput, Binder, Construction, Method, Uninterpreted, Defined, Compound,
}

pub comp mentions {
    use self::ExprKind::{
        Binder,
        Compound,
        Constant,
        Construction,
        Defined,
        DefinedOutput,
        Literal,
        Method,
        Uninterpreted,
        Variable,
    }
    in expr_kind: ExprKind
    in parts?                -- one of its parts mentions a variable or an uninterpreted function
    pub det out mentions?    -- it mentions a variable or an uninterpreted function

    req rule: mentions? iff match expr_kind {
        Literal | Constant => false,
        Variable | Uninterpreted => true,
        DefinedOutput | Binder | Construction | Method | Defined | Compound => parts?,
    }

    expect fixed_meaning: when expr_kind = Defined or expr_kind = Method or expr_kind = Construction, mentions? iff parts?
    expect unknown: when expr_kind = Variable or expr_kind = Uninterpreted, mentions?
}
```

The parts of a defined output and of a binder are its definition and its
scrutinee. So `double(3)`, `"abc".len` and `Shape::Circle(2)` mention
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
`lang::linear_product` states this, from whether each operand mentions a
variable or an uninterpreted function:

```fren
pub comp linear_product {
    in a_mentions?    -- the left operand mentions a variable or an uninterpreted function
    in b_mentions?    -- the right operand mentions a variable or an uninterpreted function
    pub det out accepted?

    req rule: accepted? iff not (a_mentions? and b_mentions?)

    expect scaling: when not a_mentions?, accepted?
    expect no_variable_products: when a_mentions? and b_mentions?, not accepted?
}
```

An operand that mentions less never makes a product nonlinear:

```fren
expect fewer_mentions: forall (p q: linear_product),
    when (not q.a_mentions? or p.a_mentions?) and (not q.b_mentions? or p.b_mentions?) and p.accepted?,
    q.accepted?
```

A defined function applied to constants scales a product like a literal,
whatever the other operand:

```fren
expect defined_scales: forall (m: mentions) (p: linear_product),
    when m.expr_kind = ExprKind::Defined and not m.parts? and (p.a_mentions? iff m.mentions?), p.accepted?
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
built from integer literals and constants whose values are integer
constant expressions by `+`, `-`, `*`, `div`, `mod`, `abs`, `min` and
`max`, and parentheses. So with `const N: Int := 2 * 4`, `x mod N` is
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

    req rule: accepted? iff (form in {LiteralDivisor, KnownConstant} and value != 0)

    expect no_zero: when value = 0, not accepted?
    expect literals: when form = LiteralDivisor and value != 0, accepted?
    expect no_variables: when form = OtherDivisor, not accepted?
}
```

`lang::division` states the laws of `div` and `mod`, for a positive and a
negative divisor:

```fren
const NEGATIVE_DIVISOR: Int := -3

pub comp division {
    in x: Int
    in y: Int

    expect euclidean: x = (x div 3) * 3 + x mod 3
    expect remainder_range: 0 <= x mod 3 and x mod 3 < 3
    expect euclidean_negative: x = (x div NEGATIVE_DIVISOR) * NEGATIVE_DIVISOR + x mod NEGATIVE_DIVISOR
    expect remainder_range_negative: 0 <= x mod NEGATIVE_DIVISOR and x mod NEGATIVE_DIVISOR < NEGATIVE_DIVISOR.abs
    expect negated_divisor: x div -3 = -(x div 3) and x mod -3 = x mod 3
    expect multiples: (3 * x) div 3 = x and (3 * x) mod 3 = 0
    expect periodic: (x + 3) mod 3 = x mod 3 and (x + 3) div 3 = x div 3 + 1
    expect rounds_down: (x div 3) * 3 <= x and x < (x div 3) * 3 + 3
    expect monotone: when x <= y, x div 3 <= y div 3
    expect by_one: x div 1 = x and x mod 1 = 0
}
```

## Conditionals

`if C then A else B` has the value of `A` if `C` holds, and of `B` otherwise.
`C` must be a `Bool`, and `A` and `B` must have the same type, which is the
type of the conditional. A conditional is an atom, so it can be an operand
without parentheses, but `B` extends as far right as possible:
`2 * if c? then x else y + 1` means `2 * (if c? then x else (y + 1))`.

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
parameters, and each argument must have the type of its parameter.
`lang::application` states this, from the types of the parameters and of
the arguments, in order:

```fren
pub comp application {
    in params: Seq(Ty)   -- the parameters' types
    in args: Seq(Ty)     -- the arguments' types
    in k: Int            -- any position, for `typed`
    pub det out accepted?

    assume some_param: params != []

    req rule: accepted? iff args = params

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

    req rule: accepted? iff (defined? or not mentions_output?)

    expect defined_any: when defined?, accepted?
}
```

## Records

`Point { x := 1, y := 2 }` builds a value of the [record](Items.md#records)
`Point`, with `1` for `x` and `2` for `y`. A field `x` alone means `x :=
x`, as for an instance's [bindings](Instances.md#bindings). The literal
must give each field of the record exactly once, in any order, and
nothing else, and each value must have its field's type. As in a binding,
a value cannot be a top-level `when` or `unless`. `lang::field_init`
states this, from what a given name is in the record and how many times
the literal gives it, as `inst::binding` does for bindings:

```fren
pub comp field_init {
    in field?            -- the name is a field of the record
    in n: Int            -- times the literal gives the name
    pub det out accepted?

    assume counts: n >= 0

    req rule: accepted? iff ((field? and n = 1) or (not field? and n = 0))

    expect each_field_once: when field? and accepted?, n = 1
}
```

`lang::record_literal` states the rule for the whole literal, which the
rule for each name cannot: that every field is given. A set cannot see a
name given twice, so repeats are counted:

```fren
pub type FieldName

pub comp record_literal {
    in fields: Set(FieldName)        -- the record's fields
    in given: Set(FieldName)         -- the names the literal gives
    in n_repeated: Int               -- names given more than once, counting each repeat
    pub det out accepted?

    assume counts: n_repeated >= 0

    req rule: accepted? iff (given = fields and n_repeated = 0)

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

## Variants with payloads

`Shape::Circle(2)` builds the value of the enumeration `Shape` that is the
variant `Circle` with the payload `2`, written as a [function
application](#function-applications) is. A variant with a payload is
mentioned only by applying it, and a variant without one only by its
path: `Shape::Circle` and `Shape::Empty()` are errors. The same holds for
a variant in a [`match` arm](#matches)'s pattern, which binds the payload's
values. `lang::variant_mention` states this:

```fren
pub mod lang

pub comp variant_mention {
    in payload: Int          -- how many values the variant's payload has
    in applied?              -- it is written with parentheses, around values or, in a pattern, binders
    pub det out accepted?

    assume counted: payload >= 0

    req rule: accepted? iff (applied? iff payload > 0)

    expect plain: when payload = 0 and not applied?, accepted?
    expect applied: when payload > 0 and applied?, accepted?
    expect unapplied: when payload > 0 and not applied?, not accepted?
    expect empty_parentheses: when payload = 0 and applied?, not accepted?
}
```

As for a function, `lang::application` gives whether the application is
accepted, where the parameters are the payload's types. Unlike a
function's value, a variant's value is fixed: building one is not an
application for the rules of [linear arithmetic](#linear-arithmetic) or of
constants, and its arguments may mention any variable that its place
allows.

## Matches

```text
match s {
    Shape::Circle(r) => r > 0,
    Shape::Rect(w, h) => w > 0 and h > 0,
    _ => true,
}
```

A `match` reads which variant a value of an enumeration is, and its
payload. The expression after `match`, the *scrutinee*, must have an
enumeration type. The scrutinee is not a record literal: in `match s {`,
the `{` starts the arms. Each arm has a pattern and a body, and the
`match` has the value of the body of the first arm whose pattern matches
the scrutinee:

- `E::V(a, b)` matches the variant `V` of `E`, which must have a payload
  of as many values as the pattern has binders. Within the arm's body,
  each binder names the corresponding value of the payload, and `_`
  ignores it. The binders of a pattern have distinct names, and follow
  the [Boolean names](Types.md#boolean-names) rule for the payload's
  types.
- `E::V`, or `V` once brought into scope by `use`, matches the variant
  `V`, which has no payload.
- `A | B`, an *or-pattern*, matches what any of its alternatives `A` and
  `B` matches. Its alternatives bind no names: each is a variant without a
  payload, or one whose binders are all `_`, as in `E::V(_, _)`. `_` is
  not an alternative. An or-pattern may start with `|`, so that its
  alternatives can be written one per line, each starting with `|`:

  ```text
  match method {
      | Method::Len
      | Method::Card => 0,
      _ => 1,
  }
  ```
- `_` matches any value.

A binder is not a variable. Within its arm's body, it may shadow a
variable, a constant or another name in scope, written with `!`, as in
`Shape::Circle(r!)` (see [Shadowing](Components.md#shadowing)); a mention
of it there is not a mention of what it shadows. Mentioning it counts as
mentioning everything its scrutinee mentions, for the rules of
[Instances](Instances.md#instance-variables), of [function
applications](#function-applications) and of [linear
arithmetic](#linear-arithmetic). So in `comp c { out s: Shape ... }`,
`match s { Shape::Circle(r) => f(r), _ => ... }` mentions the output `s`
in an argument of `f`, which is an error.

The bodies of all arms have the same type, which is the type of the
`match`. As in a binding, a body cannot be a top-level `when` or `unless`,
which would run on into the next arm.

A `match` is *exhaustive*, and each of its arms is *reachable*: every
variant has an arm, unless there is a `_` arm, which comes last and covers
at least one variant; and no variant is named twice, whether by two arms or
by two alternatives of one or-pattern. `lang::match_arms` states this, from
the variants of the enumeration, those that have an arm, whether there is
a `_` arm, and the alternatives that cannot match. A set cannot see a
repeated alternative, so repeats are counted:

```fren
pub comp match_arms {
    in variants: Set(VariantName)
    in covered: Set(VariantName)     -- variants with an arm of their own
    in wildcard?                     -- there is a `_` arm
    in n_repeated: Int               -- alternatives naming a variant that an earlier one names
    in n_after: Int                  -- arms after a `_` arm
    pub det out accepted?

    assume shapes: variants != {} and covered subset variants and n_repeated >= 0 and n_after >= 0
    assume after_wildcard: unless wildcard?, n_after = 0

    req rule: accepted? iff (n_repeated = 0 and n_after = 0
        and (if wildcard? then covered != variants else covered = variants))

    expect exhaustive: when accepted? and not wildcard?, covered = variants
    expect wildcard_reachable: when accepted? and wildcard?, (variants minus covered) != {}
}
```

## Pattern tests

```text
s is Shape::Circle(_)
s is Shape::Rect(_, _) | Shape::Empty
```

A *pattern test*, `e is P`, is `true` exactly when the pattern `P` matches
`e`: it means `match e { P => true, _ => false }`. `e` must have an
enumeration type, as a `match`'s scrutinee must (`F0335`), and `P` is a
pattern as in a [`match` arm](#matches), an or-pattern included, but it
binds no names: each of its binders is `_` (`F0334`), since a test has no
body in which a name could be mentioned. To read a payload, write a
`match`. No variant is named twice by its alternatives (`F0318`). A
pattern that matches every value, such as `_`, is allowed, though the
test is then always `true`.

`is` is a comparison: it binds as `=` does, below `+` and above `not`, and
is not associative. So `not s is Shape::Circle(_)` means `not (s is
Shape::Circle(_))`, `a is A(_) and b is B(_)` tests both, and `s is
Shape::Circle(_) = true` is an error. Its pattern extends as far right as
its alternatives do, so `s is A(_) | B(_) and t?` means `(s is A(_) |
B(_)) and t?`.

`=` and `in` compare with values, and `is` is for the patterns that `=`
cannot express, those with a payload. So write `x = E::A` and `x in {E::A,
E::B}`, not `x is E::A` or `x is E::A | E::B`, and likewise `x != E::A`
and `not x in {E::A, E::B}`, not `not x is E::A` or `not x is E::A |
E::B`. Test a `Bool` with `iff` or `not`, never with `is`: for now that is
an error (`F0335`), since a `Bool` is not an enumeration, until patterns
of literals are added. A pattern with a payload may still have
alternatives without one, as in `s is Shape::Rect(_, _) | Shape::Empty`.

`lang::pattern_test` states which patterns are accepted, from the variants
of the enumeration, those that the alternatives name, whether the pattern
is `_`, and the binders that are not `_` and the alternatives that cannot
match, counted as for `lang::match_arms`:

```fren
pub comp pattern_test {
    in variants: Set(VariantName)
    in named: Set(VariantName)       -- variants that an alternative names
    in wildcard?                     -- the pattern is `_`
    in n_bound: Int                  -- binders that are not `_`
    in n_repeated: Int               -- alternatives naming a variant that an earlier one names
    pub det out accepted?

    assume shapes: variants != {} and named subset variants and n_bound >= 0 and n_repeated >= 0
    assume wildcard_alone: when wildcard?, named = {} and n_bound = 0 and n_repeated = 0

    req rule: accepted? iff (n_bound = 0 and n_repeated = 0)

    expect binds_nothing: when accepted?, n_bound = 0
    expect every_value: when n_bound = 0 and n_repeated = 0 and (wildcard? or named = variants), accepted?
}
```

## Sets

`{a, b}` is the set of `a` and `b`, whose types must be the same, and `{}`
is the empty set. Membership, `x in s`, is a comparison, so `x in s in t`
is an error, and `not x in s` is `not (x in s)`. A membership's `in` must
be on the line where its left operand ends (see
[Lexical structure](Lexical.md#keywords)). After a path, `{` starts a
record literal, and after `match e`, the arms, so a set literal is never
written there.

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
- in a `match` arm, the body is guarded by the arm's being the first that
  matches: no earlier arm's pattern matches, and its own does;
- guards nest by conjunction.

So `q != [] and q[0] = x` is defined, and `q[0] = x and q != []` is not,
though the two mean the same: the order of `and` and `or` changes only
definedness, never meaning.

`lang::guard` states which operands are guarded, and by what, from the
operand and whether its *condition* holds. The condition is that of
`when`, `unless` or the conditional, the left operand of `and` or `or`, or,
for a `match` arm's body, that the arm is the first whose pattern matches.
An operand is evaluated exactly when its guard holds, and an operand that
is not one of these is evaluated whenever the expression it is in is.

```fren
-- The operands evaluated only under a condition.
pub enum GuardedOperand { WhenBody, UnlessBody, ThenBranch, ElseBranch, AndRight, OrRight, ArmBody }

pub comp guard {
    use self::GuardedOperand::{AndRight, ArmBody, ElseBranch, OrRight, ThenBranch, UnlessBody, WhenBody}
    in operand: GuardedOperand
    in holds?                -- its condition holds
    pub det out evaluated?   -- it is evaluated: its guard holds

    req rule: evaluated? iff match operand {
        WhenBody | ThenBranch | AndRight | ArmBody => holds?,
        UnlessBody | ElseBranch | OrRight => not holds?,
    }

    -- `a and b` is false without `b` once `a` is, and `a or b` true once `a` is.
    expect and_short_circuits: when operand = AndRight and not holds?, not evaluated?
    expect or_short_circuits: when operand = OrRight and holds?, not evaluated?
    -- The bodies of `when C` and `unless C` are evaluated under opposite conditions.
    expect opposite: when operand = WhenBody or operand = UnlessBody, evaluated? iff (holds? iff operand = WhenBody)
}
```

The branches of a conditional have opposite guards, as do the bodies of
`when C, D` and `unless C, D`: of each pair, exactly one is evaluated,
whatever `C`.

## Relations

The relational operators, where `r` is a `Rel(A, B)`:

| Form | Meaning | Operands | Result |
|---|---|---|---|
| `r join q` | `(a, c)` for each `(a, b)` in `r` and `(b, c)` in `q` | `q: Rel(B, C)` | `Rel(A, C)` |
| `r.inverse` | `(b, a)` for each `(a, b)` in `r` | | `Rel(B, A)` |
| `r.closure` | the transitive closure: `(a, c)` if a chain of pairs of `r` leads from `a` to `c` | `A` and `B` the same | `Rel(A, A)` |
| `r.image(s)` | `b` for each `(a, b)` in `r` with `a` in `s` | `s: Set(A)` | `Set(B)` |
| `r.domain` | the first members of the pairs | | `Set(A)` |
| `r.range` | the second members of the pairs | | `Set(B)` |
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

    req rule: accepted? iff match op {
        Join => kind(r) = RelTy and kind(s) = RelTy and right(r) = left(s),
        Closure => kind(r) = RelTy and left(r) = right(r),
        Image => kind(r) = RelTy and kind(s) = SetTy and elem(s) = left(r),
        Inverse | Domain | Range => kind(r) = RelTy,
    }

    expect closure_endo: when op = Closure and accepted?, left(r) = right(r)
    expect only_relations: when accepted?, kind(r) = RelTy
    expect composable: when op = Join and kind(r) = RelTy and kind(s) = RelTy and right(r) = left(s), accepted?
    expect not_composable: when op = Join and kind(s) = RelTy and right(r) != left(s), not accepted?
    expect join_relations_only: when op = Join and kind(s) != RelTy, not accepted?
    expect image_of_domain: when op = Image and kind(r) = RelTy and kind(s) = SetTy and elem(s) = left(r), accepted?
    expect image_of_other: when op = Image and kind(s) = SetTy and elem(s) != left(r), not accepted?
    expect image_of_sets_only: when op = Image and kind(s) != SetTy, not accepted?
}

pub comp pair_membership {
    in x: Ty             -- the type of the pair's first member
    in y: Ty             -- of its second
    in r: Ty             -- the type of the right operand of `in`
    pub det out accepted?

    req rule: accepted? iff (kind(r) = ValueType::RelTy and left(r) = x and right(r) = y)

    expect pair_of_relation: when kind(r) = ValueType::RelTy and left(r) = x and right(r) = y, accepted?
    expect wrong_first: when left(r) != x, not accepted?
    expect wrong_second: when right(r) != y, not accepted?
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

The methods of `Int`, where `x` is the receiver:

| Method | Meaning | Result |
|---|---|---|
| `x.abs` | the absolute value: `x` if `x >= 0`, else `-x` | `Int` |
| `x.min(y)` | the lesser of `x` and `y` | `Int` |
| `x.max(y)` | the greater of `x` and `y` | `Int` |

Each is a conditional, such as `if x < 0 then -x else x`, so each stays
within linear arithmetic: `(a - b).abs <= TOLERANCE` and `2 * x.min(y)`
are linear. A literal is not a receiver as written, since `3.abs` is not
an identifier: write `(3).abs`, or `(-3).abs`. `lang::int_methods` states
their laws:

```fren
pub comp int_methods {
    in x: Int
    in y: Int

    expect abs_nonnegative: x.abs >= 0
    expect abs_cases: (x >= 0 and x.abs = x) or (x < 0 and x.abs = -x)
    expect abs_negation: (-x).abs = x.abs
    expect abs_triangle: (x + y).abs <= x.abs + y.abs
    expect abs_bounds: -x.abs <= x and x <= x.abs
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

`lang::string_methods` states the table as laws, for every string and
position. Several of them search a string or slice it at a position that
is not a constant, which is outside the [decidable
core](Decidability.md#strings), so it allows that. It also allows
`empty_argument` and `manual_method`, which fire on some of the laws, such
as `s.contains?("")`, since those laws are what the lints rely on:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.empty_argument "allow" in
set_option fren.lint.manual_method "allow" in
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

The methods of `Set(T)`:

| Method | Meaning | Result |
|---|---|---|
| `s.card` | the number of members | `Int` |

A relation has the method `card` and the [relational](#relations) methods
`inverse`, `closure`, `image`, `domain` and `range`.

The methods of `Seq(T)` are those of `String` but `matches?` and
`replace_all`, with the same meanings and values at the edges: an argument
that is a `String` for a string is a `Seq(T)` here, `q.at(i)` is `[q[i]]`
or `[]`, and `q.len` is the number of elements. Two more are a sequence's
only:

| Method | Meaning | Result |
|---|---|---|
| `q.update(i, x)` | `q` with `x` at position `i`; `q` itself unless `0 <= i < q.len` | `Seq(T)` |
| `q.rev` | `q` reversed | `Seq(T)` |

Every method is total: its value at the edges, such as `"abc".at(5)`, is the
one the solver's theory of strings gives it, so that Lean and the solver
agree.

`lang::collection_methods` states laws of the methods and operators of
sequences, sets and relations: the methods of `Seq(T)` that it shares
with `String`, with the same meanings, and those of its own; the set
operators `union`, `inter`, `minus` and `subset`, and `card`; and the
relational methods and `join`, which a relation over a finite type keeps
in the core. `rev`, `++`, `at`, `slice`, `contains?`, `index_of` and
`replace` on sequences, and `starts_with?` and `ends_with?` with an
argument that is not a literal, are outside the [decidable
core](Decidability.md#sequences), so it allows that. As
`lang::string_methods` does, it also allows the lints that fire on the laws
they rely on, `empty_argument`, `manual_method` and
`redundant_method_chain`:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.empty_argument "allow" in
set_option fren.lint.manual_method "allow" in
set_option fren.lint.redundant_method_chain "allow" in
pub comp collection_methods {
    in p: Seq(Int)
    in q: Seq(Int)
    in i: Int
    in n: Int
    in x: Int
    in s: Set(Int)
    in t: Set(Int)
    in r: Rel(Bool, Bool)

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
[Boolean names](Types.md#boolean-names) rule:

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
    use self::ValueType::{BoolTy, IntTy, RelTy, SeqTy, SetTy, StringTy}
    in method: Method
    in receiver: ValueType
    pub det out accepted?
    pub det out result: ValueType
    pub det out n_params: Int

    req receivers: accepted? iff match method {
        Card => receiver in {SetTy, RelTy},
        Inverse | Closure | Image | Domain | Range => receiver = RelTy,
        Update | Rev => receiver = SeqTy,
        Matches | ReplaceAll => receiver = StringTy,
        Abs | Min | Max => receiver = IntTy,
        _ => receiver in {StringTy, SeqTy},
    }
    req results: result = match method {
        StartsWith | EndsWith | Contains | Matches => BoolTy,
        Len | IndexOf | Card | Abs | Min | Max => IntTy,
        Inverse | Closure => RelTy,
        Image | Domain | Range => SetTy,
        _ => receiver,
    }
    req arities: n_params = match method {
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
pub comp char_range {
    in low: Int          -- the code point of the character before `-`
    in high: Int         -- the code point of the character after it
    pub det out accepted?

    assume characters: 0 <= low <= MAX_CHAR and 0 <= high <= MAX_CHAR

    req rule: accepted? iff low <= high

    expect singleton_ok: when low = high, accepted?
}
```

## Types of operators

`lang::operator_type` states the operand and result types of the
[operators](#operators) and of conditionals. `a` and `b` are the types of
the operands, or of a conditional's branches, and `cond` the type of its
condition. For a prefix operator, `b` is `a`. `result` is the kind of the
result's type. `Ty`, `kind` and `ValueType` are declared in
[Types](Types.md). A [pattern test](#pattern-tests), whose right is a
pattern rather than an operand, is typed in its own section.

```fren
-- `Logic` is `when`, `unless`, `iff`, `or`, `and` and `not`; `Ordering` is
-- `<`, `<=`, `>` and `>=`; `Arithmetic` is `+`, `-`, `*`, `div` and `mod`; `Concat` is `++`;
-- `SetAlgebra` is `union`, `inter` and `minus`, on sets or relations. For
-- `Membership`, `a` is the element and `b` the set; a pair's membership,
-- and `join`, are typed by `pair_membership` and `relation_op`. The arms of a `match` are typed as a
-- conditional's branches, pairwise.
pub enum Operator { Logic, Equality, Ordering, Arithmetic, Concat, Membership, SetAlgebra, Subset, Conditional }

pub comp operator_type {
    use self::Operator::{
        Arithmetic,
        Concat,
        Conditional,
        Equality,
        Logic,
        Membership,
        Ordering,
        SetAlgebra,
        Subset,
    }
    use self::ValueType::{AbstractTy, BoolTy, IntTy, RelTy, SeqTy, SetTy, StringTy}
    in op: Operator
    in a: Ty
    in b: Ty
    in cond: Ty
    pub out accepted?
    pub out result: ValueType

    -- There is one `Bool` type and one `Int` type.
    assume primitive_unique: when kind(a) = kind(b) and kind(a) in {BoolTy, IntTy, StringTy}, a = b

    req accepted: accepted? iff match op {
        Logic => kind(a) = BoolTy and kind(b) = BoolTy,
        Equality => a = b,
        Ordering => a = b and kind(a) in {IntTy, StringTy},
        Arithmetic => kind(a) = IntTy and kind(b) = IntTy,
        Concat => a = b and kind(a) in {StringTy, SeqTy},
        Membership => kind(b) in {SetTy, SeqTy} and elem(b) = a,
        SetAlgebra | Subset => a = b and kind(a) in {SetTy, RelTy},
        Conditional => kind(cond) = BoolTy and a = b,
    }
    req results: result = match op {
        Arithmetic => IntTy,
        Concat | SetAlgebra | Conditional => kind(a),
        _ => BoolTy,
    }

    expect no_mixing: when accepted? and op != Membership, a = b
    expect member_typed: when op = Membership and accepted?, elem(b) = a
    expect bool_valued: unless op in {Arithmetic, Concat, SetAlgebra, Conditional}, result = BoolTy
    expect strings_ordered: when op = Ordering and kind(a) = StringTy and a = b, accepted?
    expect concat_closed: when op = Concat and accepted?, result = kind(a)
    expect sequences_unordered: when op = Ordering and kind(a) = SeqTy, not accepted?
    -- A value of an abstract type is only compared, or found in a set.
    expect abstract_equality_only: when accepted? and op != Conditional and kind(a) = AbstractTy,
        op in {Equality, Membership}

    -- Rows of the table of operators.
    expect same_types_equal: when op = Equality and a = b, accepted?
    expect bools_equal: when op = Equality and kind(a) = BoolTy and kind(b) = BoolTy, accepted?
    expect ints_ordered: when op = Ordering and kind(a) = IntTy and kind(b) = IntTy, accepted?
    expect strings_concatenate: when op = Concat and kind(a) = StringTy and kind(b) = StringTy, accepted?
    expect sequences_concatenate: when op = Concat and kind(a) = SeqTy and a = b, accepted?
    expect set_members: when op = Membership and kind(b) = SetTy and elem(b) = a, accepted?
    expect sequence_members: when op = Membership and kind(b) = SeqTy and elem(b) = a, accepted?
    expect members_of_collections: when op = Membership and not kind(b) in {SetTy, SeqTy}, not accepted?
    expect sets_combine: when op = SetAlgebra and kind(a) = SetTy and a = b, accepted?
    expect relations_subset: when op = Subset and kind(a) = RelTy and a = b, accepted?
    expect boolean_condition: when op = Conditional and kind(cond) != BoolTy, not accepted?
    expect no_mixed_arithmetic: when op = Arithmetic and kind(a) = IntTy and kind(b) = BoolTy, not accepted?
    -- Sets of different element types are different types.
    expect sets_of_different_types: when op = Equality and kind(a) = SetTy and kind(b) = SetTy and elem(a) != elem(b),
        not accepted?
}

-- The checks for every chapter under Lang/ that shares the module `lang`.
#fren_check
```

## Names

A path names a variable of the enclosing component, a binder of an
enclosing [`match` arm](#matches) (the innermost, which may
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
