# Complexity

The lints of the `complexity` group find a simpler expression with the
same meaning, and `fren fix` fixes each of them but `constant_output`.

## Simpler `Bool` expressions

`nonminimal_bool` reports a `Bool` expression that has a simpler form with
the same meaning, in any constraint, binding, constant or global
expectation:

| Written | Simpler form |
|---|---|
| `A = true`, `A != false`, `A iff true` | `A` |
| `A = false`, `A != true`, `A iff false` | `not A` |
| `not not A` | `A` |
| `not (A = B)`, and so on for every comparison | `A != B`, the complement of the comparison, simplified again if it compares with a literal |
| `if C then true else false` | `C` |
| `if C then false else true` | `not C` |
| `if C then A else false` | `C and A` |
| `if C then true else B` | `C or B` |
| `if C then false else B` | `not C and B` |
| `if C then A else true` | `not C or A` |

A literal may be on either side of `=`, `!=` and `iff`; when both sides are
literals, the right one is taken as the literal. The rules are tried in the
order of the table, so `if C then true else false` is `C`, not `C and
true`. The rules for `if` keep the guards (see
[Expressions](../Lang/Expressions.md#sequences)): in `if C then A else B`, `A`
is guarded by `C` and `B` by `not C`, as they are in `C and A`, `C or B`,
`not C and B` and `not C or A`. A [pattern
test](../Lang/Expressions.md#pattern-tests) is not looked inside but for
its scrutinee, and keeps its parentheses where a comparison would need
them, so `ok? = if s is A(_) then true else false` becomes `ok? = (s is
A(_))`. So does a [chained
comparison](../Lang/Expressions.md#chained-comparisons), which is not
looked inside but for its operands. `lint::literal_comparison` gives the simpler form of a comparison
with a literal:

```fren
pub mod lint

pub comp literal_comparison {
    in equal?            -- the operator is `=` or `iff`, rather than `!=`
    in literal?          -- the literal is `true`
    pub det out negated?  -- the simpler form is `not A`, rather than `A`

    req rule: negated? iff (equal? != literal?)

    expect equal_true: when equal? and literal?, not negated?
    expect unequal_true: when not equal? and literal?, negated?
}
```

`lint::complement` gives the complement of a
[comparison](Style.md#empty-collections), the one that holds exactly when it does
not:

```fren
pub comp complement {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    in op: Comparison
    pub det out result: Comparison

    req rule: result = match op { Eq => Ne, Ne => Eq, Lt => Ge, Ge => Lt, Gt => Le, Le => Gt }

    expect changes: result != op
}

expect complement_involutive: forall (p q: complement), when q.op = p.result, q.result = p.op
```

The message is reported at the expression, and suggests the simpler form,
in which the operands are simplified too: the suggestion for `not not (a? =
true)` is `a?`. An operand keeps the text it is written with, and it and
the simpler form itself are put in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes). So `x? and not not (a? or b?)` becomes `x? and
(a? or b?)`, and `not (x = 1)` becomes `x != 1`.

The simpler form means what the expression means. Whatever values its
paths, numbers and function applications have, if the expression has a
value, the simpler form has the same one. This is proved in Lean, over a
model of expressions that follows the [operators](../Lang/Expressions.md#operators):
the rules above decide what the simpler form is, as an expression rather
than as text, and the proof covers every expression, every rule, and the
simplification of the operands. In the model, as in a spec that
elaborates, the branches of an `if` have the same type, so that in `if C
then A else false`, `A` is a `Bool`. The proof does not cover the text:
that the simpler form, written with its parentheses, parses as the
expression the rules chose.

`lint::nonminimal_bool_keeps_meaning` states the rules as laws (see
[Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.nonminimal_bool "expect" in
pub comp nonminimal_bool_keeps_meaning {
    in a?
    in c?
    in x: Int
    in y: Int

    expect true_literals: ((a? = true) iff a?) and ((a? != false) iff a?) and ((a? iff true) iff a?)
    expect false_literals: ((a? = false) iff not a?) and ((a? != true) iff not a?) and ((a? iff false) iff not a?)
    expect literals_left: ((true = a?) iff a?) and ((true iff a?) iff a?) and ((false = a?) iff not a?)
    expect double_negation: (not not a?) iff a?
    expect negated_literal: (not (a? = true)) iff not a?
    expect complements: ((not (x = y)) iff x != y) and ((not (x != y)) iff x = y)
        and ((not (x < y)) iff x >= y) and ((not (x <= y)) iff x > y)
        and ((not (x > y)) iff x <= y) and ((not (x >= y)) iff x < y)
    expect conditionals: ((if c? then true else false) iff c?) and ((if c? then false else true) iff not c?)
    expect conditional_operands: ((if c? then a? else false) iff (c? and a?))
        and ((if c? then true else a?) iff (c? or a?))
        and ((if c? then false else a?) iff (not c? and a?))
        and ((if c? then a? else true) iff (not c? or a?))
}
```

## Singleton membership

`singleton_membership` fires on `x in {a}`, which is `x = a`, and is
fixable. `lint::singleton_membership_keeps_meaning` states the fix as a law
(see [Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.singleton_membership "expect" in
pub comp singleton_membership_keeps_meaning {
    in x: Int
    in y: Int

    expect singleton: (x in {y}) iff x = y
}
```

## Constant outputs

`constant_output` fires on a [defined output](../Lang/Components.md#defined-outputs)
whose definition mentions no variable and no uninterpreted function (see
[Mentions](../Lang/Expressions.md#mentions)): it is the same in every behaviour,
so it is a constant. Its counterpart in the `pedantic` group,
[`definable_output`](Pedantic.md#definable-outputs), fires on an output
that is not defined but could be. `lint::output_lints` states both:

```fren
pub comp output_lints {
    in defined?              -- the output is defined
    in mentions?             -- its definition mentions a variable or an uninterpreted function, if defined
    in n_reqs: Int           -- requirements that mention it, if not defined
    in equation?             -- the only one is `x = e` or `x? iff e`, with `e` not mentioning `x`
    pub det out constant?    -- `constant_output` fires
    pub det out definable?   -- `definable_output` fires

    assume counts: n_reqs >= 0

    req constant: constant? iff (defined? and not mentions?)
    req definable: definable? iff (not defined? and n_reqs = 1 and equation?)

    expect exclusive: not (constant? and definable?)
}
```

## Chains of methods

`redundant_method_chain` fires on a chain of methods without arguments,
`e.m1.m2...`, that has a shorter form with the same value, and is fixable.
The shorter form rewrites each pair of methods in this table, until none is
left:

| Written | Shorter form | Since |
|---|---|---|
| `q.rev.rev` | `q` | reversing twice gives the elements back in their order |
| `r.inverse.inverse` | `r` | swapping the members of each pair twice gives the pair back |
| `r.closure.closure` | `r.closure` | the transitive closure is idempotent: a chain of pairs of `r.closure` joins chains of pairs of `r` into one |
| `r.inverse.domain` | `r.range` | the first members of the pairs `(b, a)` are the second members of the pairs `(a, b)` |
| `r.inverse.range` | `r.domain` | and the other way around |
| `r.inverse.card` | `r.card` | swapping the members of a pair is one-to-one, so the pairs are as many |
| `q.rev.len` | `q.len` | reversing keeps every element |
| `r.closure.domain` | `r.domain` | `r` is within `r.closure`, and a chain from `a` starts with a pair `(a, b)` of `r` |
| `r.closure.range` | `r.range` | and a chain to `c` ends with a pair `(b, c)` of `r` |

Each holds for every relation and sequence, empty ones included: the
inverse and the closure of an empty relation are empty, and so are its
domain and range, and `[].rev` is `[]`. Each rewrite shortens the chain, so
rewriting ends, and the form it ends with does not depend on which pair is
rewritten first: where two pairs overlap, as in `r.inverse.inverse.domain`,
either order gives `r.domain`. The message is reported once, at the whole
chain. The fix replaces it with its shorter form, in which the receiver
keeps the text it is written with. When no method is left, the receiver
alone is written without the parentheses a receiver may need, and put in
parentheses where [fixes need them](../Lint.md#parentheses-in-fixes), so `(a ++ b).rev.rev = c`
becomes `a ++ b = c`. A method has no guard of its own, and the fix
evaluates the receiver where the chain did, so it keeps every guard: it
only stops evaluating methods, which index nothing.

`lint::method_chain` states the rewrite of a pair, `e.inner.outer`: to `e`,
to `e.single`, or none:

```fren
use lang::Method

pub enum ChainFix { Keep, Receiver, Single }

pub comp method_chain {
    use lang::Method::{Card, Closure, Domain, Inverse, Len, Range, Rev}
    in inner: Method     -- the method of `e.inner`
    in outer: Method     -- the method called on `e.inner`
    pub det out fix: ChainFix
    pub det out single: Method  -- for `Single`, the method of the shorter form

    req rule: fix = if inner = outer and inner in {Rev, Inverse} then ChainFix::Receiver
        else if (inner = Inverse and outer in {Domain, Range, Card}) or (inner = Rev and outer = Len)
        or (inner = Closure and outer in {Closure, Domain, Range}) then ChainFix::Single
        else ChainFix::Keep
    req shorter: single = if inner = Inverse and outer = Domain then Range
        else if inner = Inverse and outer = Range then Domain
        else outer

    expect receiver_twice: when fix = ChainFix::Receiver, inner = outer
    expect closure_kept: when inner = Closure and fix = ChainFix::Single, single = outer
}
```

## Trivial matches

`trivial_match` fires on a `match` of one arm, whose pattern binds no name:
`_`, the variant of an enumeration with one variant, without a payload or
with `_` for each of its values, or an or-pattern. A `match` is exhaustive
(see [Matches](../Lang/Expressions.md#matches)), so that arm matches every
value of the scrutinee, and the `match` is the arm's body. Like Clippy's
`match_single_binding`, it is in `complexity`, and it is fixable. The fix
replaces the `match` with the body, which keeps the text it is written
with, and is put in parentheses where [fixes need them](../Lint.md#parentheses-in-fixes):
`x = 2 * match e { _ =>
x - 1 }` becomes `x = 2 * (x - 1)`. The body's guard is the guard of the
`match` and its pattern's test, which every value passes, so it is the
guard of the `match`, where the fix puts the body. The fix only drops the
scrutinee, which removes what was evaluated, so no guard is weaker.
`lint::trivial_match` states when it fires:

```fren
pub comp trivial_match {
    in n_arms: Int
    in binds?            -- the first arm's pattern binds a name
    pub det out fires?

    assume counts: n_arms >= 1

    req rule: fires? iff (n_arms = 1 and not binds?)
}
```

## Comparisons

The lints of this section and the next three, and
[`bool_equality`](Pedantic.md#boolean-equality), look at the operators and
method calls of an expression, in any constraint, binding, definition,
constant or global expectation, and are fixable. Like `nonminimal_bool`,
each fix puts its operands, and itself, in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes). Operands are compared as
[written the same](../Lint.md#written-the-same).

`double_comparison` fires on two comparisons of the same two operands,
written the same, joined by `and` or `or`, that together are one
comparison of those operands other than either of them:

| Written | Fix |
|---|---|
| `a < b or a = b` | `a <= b` |
| `a > b or a = b` | `a >= b` |
| `a < b or a > b` | `a != b` |
| `a <= b and a >= b` | `a = b` |
| `a <= b and a != b` | `a < b` |
| `a >= b and a != b` | `a > b` |
| `a subset b and b subset a` | `a = b` |

The two comparisons may come in either order, and the second may have its
operands the other way around, as in `b > a`, which is `a < b`; the fix
keeps the first's order. Orderings compare `Int`s or `String`s, which are
totally ordered, so whether a comparison holds depends only on whether `a`
is below, equal to or above `b`, and `lint::double_comparison_meaning`
checks that the fix holds in exactly the same cases as the two. Two sets
or relations are equal exactly when each is a subset of the other. The fix
keeps the guards: the second comparison is guarded by the first or by its
negation, but both evaluate the same operands, which the first does
unguarded, so the second is defined wherever the first is, and so is the
fix.

```fren
pub enum Order { Below, Same, Above }

pub comp comparison_holds {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    in op: Comparison
    in order: Order      -- how the left operand compares with the right
    pub det out holds?

    req rule: holds? iff match op {
        Eq => order = Order::Same,
        Ne => order != Order::Same,
        Lt => order = Order::Below,
        Le => order != Order::Above,
        Gt => order = Order::Above,
        Ge => order != Order::Below,
    }
}

pub comp double_comparison {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    in conjunction?      -- the comparisons are joined by `and`, rather than `or`
    in first: Comparison
    in second: Comparison  -- with its operands in the first's order
    pub det out fires?
    pub det out result: Comparison  -- the fix, if it fires; otherwise `first`

    req fires: fires? iff first != second and (if conjunction?
        then first in {Le, Ge, Ne} and second in {Le, Ge, Ne}
        else first in {Lt, Gt, Eq} and second in {Lt, Gt, Eq})
    req fix: result = if not fires? then first
        else if conjunction? then (if first != Ne and second != Ne then Eq else if Le in {first, second} then Lt else Gt)
        else (if first != Eq and second != Eq then Ne else if Lt in {first, second} then Le else Ge)
}

expect double_comparison_meaning: forall (d: double_comparison) (x y z: comparison_holds),
    when d.fires? and x.op = d.first and y.op = d.second and z.op = d.result
    and x.order = z.order and y.order = z.order,
    z.holds? iff (if d.conjunction? then x.holds? and y.holds? else x.holds? or y.holds?)
```

## Searches

`manual_method` fires on a search written with `index_of` or `slice` that
a [method](../Lang/Expressions.md#methods) says directly, on a string or a
sequence, whose methods have the same values:

| Written | Fix |
|---|---|
| `s.index_of(t, 0) >= 0`, `s.index_of(t, 0) > -1`, `s.index_of(t, 0) != -1` | `s.contains?(t)` |
| `s.index_of(t, 0) < 0`, `s.index_of(t, 0) <= -1`, `s.index_of(t, 0) = -1` | `not s.contains?(t)` |
| `s.index_of(t, 0) = 0` | `s.starts_with?(t)` |
| `s.slice(0, t.len) = t` | `s.starts_with?(t)` |

The bound, or the `t` that the slice is compared with, may be on the left.
For the slice, the receiver of `len` is written the same as the other
operand, or is it in parentheses.

`s.index_of(t, 0)` is the first position at which `t` occurs in `s`, which
is at least `0`, or `-1` if there is none. If `t` is `""`, it is `0`, since
`0 <= 0 <= s.len`, and `""` occurs in every `s`, as its prefix. If `s` is
shorter than `t`, `t` occurs nowhere in it, and it is `-1`. So the index is
at least `0` exactly when `t` occurs in `s`, which is `s.contains?(t)`, and
it is `0` exactly when `t` occurs at position `0`, which is
`s.starts_with?(t)`. `s.slice(0, t.len)` is the first `t.len` elements of
`s`, or all of `s` if it is shorter, and `""` if `t` is `""` (`n > 0`
fails) or `s` is (`0 < s.len` fails). It is `t` exactly when `t` is a
prefix of `s`: if `t` is `""`, both are `""`, and if `s` is shorter than
`t`, so is the slice. Every method is total, and the fix evaluates `s` and
`t` where the comparison did, so it keeps the guards.

`lint::index_test` states which comparisons of `index_of` fire, from the
operator and the bound, with the call on the left, and checks each against
every value that the call can take:

```fren
pub enum IndexTest { Found, Absent, AtStart, Other }

pub comp index_test {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    use self::IndexTest::{Absent, AtStart, Found, Other}
    in op: Comparison
    in bound: Int
    in position: Int     -- any value of `s.index_of(t, 0)`
    pub det out test: IndexTest

    assume positions: position >= -1

    req rule: test = match op {
        Ge => if bound = 0 then Found else Other,
        Gt | Ne => if bound = -1 then Found else Other,
        Lt => if bound = 0 then Absent else Other,
        Le => if bound = -1 then Absent else Other,
        Eq => if bound = -1 then Absent else if bound = 0 then AtStart else Other,
    }

    expect found: when test = Found, compares?(op, position, bound) iff position >= 0
    expect absent: when test = Absent, compares?(op, position, bound) iff position = -1
    expect at_start: when test = AtStart, compares?(op, position, bound) iff position = 0
}
```

The fix can bring a spec into the [decidable core](../Lang/Decidability.md).
`index_of`, and `slice` of a sequence, are outside it unless every operand
is a constant, but `contains?` and `starts_with?` of a string are in it
when `t` is a constant, and `starts_with?` of a sequence is in it when `t`
is a literal. So on strings, each fix of `index_of` with a constant `t`
brings the comparison into the core, and the fix of `slice` changes
nothing, since `s.slice(0, t.len) = t` is already in the core when `t` is a
constant. On sequences, the fixes to `starts_with?` with a literal `t` do,
and those to `contains?` do not, since `contains?` of a sequence is outside
the core too.

## Conditional operands

A conditional is an atom, but its `else` branch extends as far right as
possible (see [Conditionals](../Lang/Expressions.md#conditionals)): `2 * if
c? then x else y + 1` means `2 * (if c? then x else (y + 1))`, not `(2 * if
c? then x else y) + 1`. `else_extends` fires on a conditional, not in
parentheses, that is an operand of a binary operator, and whose `else`
branch would need parentheses in its place, as an operand of that
operator, under `lang::operand`. If the `else` branch is itself a
conditional not in parentheses, its own `else` branch counts instead, and
so on. The fix puts that branch in parentheses, as it is parsed, which
keeps the meaning and the guards, and shows where it ends:

```fren
use lang::{Assoc, operand}

pub comp else_extends {
    in outer: Int        -- the precedence of the operator
    in inner: Int        -- the precedence of the `else` branch's operator
    in assoc: Assoc      -- the associativity of the operator
    in right?            -- the conditional is the operator's right operand
    pub det out fires?

    inst place: operand { outer, inner, assoc, right? }

    req rule: fires? iff not place.bare?
}
```

## Identities

`identity_op` fires on an operation that leaves one operand as it is, and
its fix is that operand:

| Written | Fix |
|---|---|
| `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` | `x` |
| `s ++ ""`, `"" ++ s`, `q ++ []`, `[] ++ q` | `s`, `q` |
| `a union {}`, `{} union a`, `a minus {}` | `a` |

It also fires on `x + -y`, whose fix is `x - y`, and on `x - -y`, whose fix
is `x + y`. The fix has the operation's value and its type: the operands
of `+`, `-`, `*`, `++`, `union` and `minus` have the same type as the
result, and `""`, `[]` and `{}` are their identities, as `0` is of `+` and
`-` and `1` of `*`; `[]` and `{}` take their type from the other operand,
which keeps it. The operand removed is a literal, or a negation whose
operand the fix evaluates where it was, so the fix keeps the guards.
`lint::identity_op` states what the fix is, from the operator and what
each operand is:

```fren
pub enum IdentityOperator { Add, Sub, Mul, Concat, Union, Minus }

-- An operand as written: `Empty` is `""`, `[]` or `{}`, and `Negation` is `-y`.
pub enum IdentityOperand { Zero, One, Empty, Negation, Other }

pub enum Rewrite { KeepLeft, KeepRight, Flip, Unchanged }

pub comp identity_op {
    use self::IdentityOperand::{Empty, Negation, One, Zero}
    use self::IdentityOperator::{Add, Concat, Minus, Mul, Sub, Union}
    use self::Rewrite::{Flip, KeepLeft, KeepRight, Unchanged}
    in op: IdentityOperator
    in left: IdentityOperand
    in right: IdentityOperand
    pub det out rewrite: Rewrite  -- `Flip` is `x - y` for `x + -y`, and `x + y` for `x - -y`

    req rule: rewrite = match op {
        Add => if right = Zero then KeepLeft else if left = Zero then KeepRight
            else if right = Negation then Flip else Unchanged,
        Sub => if right = Zero then KeepLeft else if right = Negation then Flip else Unchanged,
        Mul => if right = One then KeepLeft else if left = One then KeepRight else Unchanged,
        Concat | Union => if right = Empty then KeepLeft else if left = Empty then KeepRight else Unchanged,
        Minus => if right = Empty then KeepLeft else Unchanged,
    }

    expect flips_only_sums: when rewrite = Flip, op in {Add, Sub}
}
```

## Off-by-one comparisons

`int_plus_one` fires on a non-strict comparison of integers with an
operand off by one, where its fix is the strict comparison without the
offset. Where `1` is the literal, and `1 + b` is the same as `b + 1`:

| Written | Fix |
|---|---|
| `a >= b + 1`, `a >= 1 + b`, `a - 1 >= b` | `a > b` |
| `b + 1 <= a`, `1 + b <= a`, `b <= a - 1` | `b < a` |

Where both operands are off by one, as in `a - 1 >= b + 1`, the fix drops
the `+ 1`: `a - 1 > b`. `lint::int_plus_one` states this, from the offset
of each operand of the comparison:

```fren
pub enum Offset { Zero, PlusOne, MinusOne }

use self::Offset::{MinusOne, PlusOne, Zero}

pub comp int_plus_one {
    use self::Comparison::{Ge, Gt, Le, Lt}
    in op: Comparison
    in left: Offset      -- `e + 1` and `1 + e` are `PlusOne`, `e - 1` is `MinusOne`, and any other operand `Zero`
    in right: Offset
    pub det out fires?
    pub det out result: Comparison  -- the comparison of the fix
    pub det out drop_left?          -- the fix drops the offset of the left operand, rather than the right

    req rule: fires? iff ((op = Ge and (right = PlusOne or left = MinusOne))
        or (op = Le and (left = PlusOne or right = MinusOne)))
    req strict: result = (if op = Ge then Gt else if op = Le then Lt else op)
    req drop: drop_left? iff (if op = Ge then right != PlusOne else op = Le and left = PlusOne)
}
```

The fix is exact: over the integers, where the lint fires, the comparison
of the operands, `a` and `b` with their offsets, holds exactly when the
fix does:

```fren
fn offset_value(o: Offset): Int := match o { Zero => 0, PlusOne => 1, MinusOne => -1 }

comp int_plus_one_exact {
    in op: Comparison
    in left: Offset
    in right: Offset
    in a: Int            -- the left operand, without its offset
    in b: Int            -- the right operand, without its offset

    inst p: int_plus_one { op, left, right }

    expect exact: when p.fires?, compares?(op, a + offset_value(left), b + offset_value(right))
        iff compares?(p.result, if p.drop_left? then a else a + offset_value(left),
        if p.drop_left? then b + offset_value(right) else b)
}
```

Its fix writes its operands, and is put in parentheses itself, as the
fixes of [`double_neg` and `neg_multiply`](Style.md#negations) are, and
keeps the guards for the same reasons.

## Parentheses

`double_parens` fires on parentheses directly around parentheses, with
nothing but whitespace between them: `((e))` means what `(e)` means. It
fires once for each run of such pairs, at the outermost, and its fix keeps
only the innermost: `(((e)))` becomes `(e)`. The parentheses of an
application, a method call or a pair are its own, not around an argument
or an element, so `f((x))` and `(1, (x))` each have one pair around `x`.
Parentheses around a receiver are around it alone, so `(({1}).card)` has
one pair around `{1}` and one around `({1}).card`, not two around `{1}`.
Parentheses only group, so the fix
changes neither the meaning nor the guards. `lint::double_parens` states
when it fires:

```fren
pub comp double_parens {
    in depth: Int        -- pairs of parentheses, each directly around the next
    pub det out fires?

    assume counts: depth >= 1

    req rule: fires? iff depth >= 2
}
```
