# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant.

## Indexes

`index_after_use` fires on `a and b`, where `a` indexes a sequence `q` and
`b` bounds it: it mentions `q.len`, or compares `q` with `[]`. The index is
probably meant to be guarded by `b`, but `and` guards its right operand by
its left (see [Expressions](../Lang/Expressions.md#sequences)), so the
[definedness check](../Check.md#definedness) fails. The fix swaps the
operands, which does not change the meaning. The lint looks only at the
text, never at the solver:

```fren
pub mod lint

pub comp index_after_use {
    in indexes_left?     -- `a` indexes a sequence `q`
    in bounds_right?     -- `b` mentions `q.len`, or compares `q` with `[]`
    pub det out fires?

    req rule: fires? iff (indexes_left? and bounds_right?)
}
```

`negative_position` fires on a position written as a negative integer
literal, `-k` for a `k` other than `0`: the index of `q[-k]`, the first
argument of `at`, `slice` and `update`, and the second of `index_of`.
Fren has no negative indexing, so `q[-1]` is not the last element, as it
would be in Python: it is unspecified, which the definedness check reports
only as an index that may be out of range. The
[methods](../Lang/Expressions.md#methods) are total, so `s.at(-1)` and
`s.slice(-3, 3)` are always `""`, `q.update(-1, x)` is always `q`, and
`s.index_of(t, -1)` is always `-1`, which no check reports. It is reported
at the index or the method call, and the message says what it is and
suggests counting from the end, as in `q[q.len - 1]` or `s.at(s.len - 1)`,
or, for `index_of`, searching from `0`. It has no fix, since which
position was meant is not certain. `lint::negative_position` states when
it fires:

```fren
pub comp negative_position {
    use lang::Method
    use lang::Method::{At, IndexOf, Slice, Update}
    in index?            -- the position is the index of `q[i]`, not an argument
    in method: Method    -- the method, for an argument
    in arg: Int          -- the position of the argument, from 0
    in negative?         -- it is written `-k`, for an integer literal `k` other than `0`
    pub det out fires?

    assume position: arg >= 0

    req rule: fires? iff (negative? and (index? or match method {
        At | Slice | Update => arg = 0,
        IndexOf => arg = 1,
        _ => false,
    }))
}
```

## Repeated constraints

`duplicate_constraint` fires on a constraint of a component that is
written the same as an earlier one of the component, whatever their
kinds, `assume`, `req` or `expect`, and on a global expectation written
the same as an earlier one of its module in the same file. Two
constraints are written the same if their expressions are (see
[Written the same](../Lint.md#written-the-same)), and two global
expectations if all they say after their names is, binders included. It is
reported at the later one's name, and the message names the first one it
repeats.

Of two `req`s that say the same, the [redundancy
check](../Check.md#redundancy) reports each as following from the other,
which invites removing both; this lint says which to remove. Two
expectations that say the same are reported by no check. Where the two are
of one kind, the fix removes the later one, with a `--` comment after it
on its last line, and for a global expectation any `set_option ... in`
before it. This keeps the meaning: a constraint
that repeats one of its kind adds nothing to the component, and an
expectation that repeats one claims nothing more. An `expect` that repeats
a `req` or an `assume` is not fixed: it tests nothing, since it follows
from what it repeats, and was probably meant to say something stronger,
which the message says. Nor is a `req` that repeats an `assume`, or the
reverse, since the two mean different things. `lint::duplicate_constraint`
states this:

```fren
pub enum ConstraintKind { Assume, Req, Expect }

pub comp duplicate_constraint {
    in earlier: ConstraintKind
    in later: ConstraintKind
    in same?             -- the later is written the same as the earlier
    pub det out fires?
    pub det out fixed?   -- the fix removes the later

    req rule: fires? iff same?
    req fix: fixed? iff (same? and earlier = later)

    expect weaker_kept: when later = ConstraintKind::Expect and earlier != later, not fixed?
}
```

## Invisible characters

`invisible_characters` fires on a string literal that contains a
zero-width or invisible character: U+200B (zero width space), U+00AD (soft
hyphen) or U+2060 (word joiner). It also fires on a string literal or a
comment that contains a bidirectional control, U+202A to U+202E or U+2066
to U+2069, or U+FEFF (zero width no-break space). An invisible character
makes two literals that look the same differ. A bidirectional control can
make text display in an order other than the one it is read in, so that
what a reader sees is not what it means, as in the "trojan source"
attacks.

It is reported once for each literal or comment, at it, and the message
names the characters. In a literal, the fix writes each as an escape, such
as `\u200B` (see [Literals](../Lang/Lexical.md#literals)), which keeps the
value and lets a deliberate use stay; a raw literal, which has no escapes,
becomes an ordinary one, with `\\` and `\"` for its `\` and `"`. In a
comment, the fix removes them, which changes no meaning.
`lint::invisible_character` states which characters it reports, by code
point:

```fren
pub comp invisible_character {
    in code: Int         -- the character's code point
    in comment?          -- it is in a comment, rather than a string literal
    pub det out fires?

    assume code_point: code >= 0

    -- U+202A to U+202E, U+2066 to U+2069 and U+FEFF anywhere; U+00AD,
    -- U+200B and U+2060 in a literal.
    req rule: fires? iff ((8234 <= code and code <= 8238) or (8294 <= code and code <= 8297)
        or code = 65279 or (not comment? and code in {173, 8203, 8288}))

    expect controls_in_comments: when code = 8238, fires?
    expect ascii_never: when code < 128, not fires?
}
```

The level that applies to it is the one in effect at the item that the
literal or comment is in. A comment between two items is in the one
before it, and a comment before the first item is in the first. In Lean,
only the comments within and after Fren items are read.

## Suspicious expressions

These lints fire on expressions that are legal but probably not what the
writer meant. Two operands are compared as [written the
same](../Lint.md#written-the-same), where the parentheses around an operand
are not part of it, so the operands of `f(x) = f(x)` are written the same,
and those of `x = (x)`, but not those of `x + 1 = 1 + x`.

`eq_op` fires on an infix operator whose two operands are written the
same, where the expression is then always the same value, or the same as
its operand: `x = x`, `x <= x`, `x >= x`, `a? iff a?` and `s subset s`
are always `true`; `x != x`, `x < x` and `x > x` are always `false`;
`x - x` is always `0` and `s minus s` always `{}`; `a? and a?`, `a? or
a?`, `s union s` and `s inter s` are the operand. The message says which.
It has no fix: the likely mistake is a typo in one operand, which no
rewrite can repair. It does not fire on `+`, `*`, `++` or `join`, where `x
+ x` and `r join r` mean something, nor on `in`, nor on the comparisons
of a [chained comparison](../Lang/Expressions.md#chained-comparisons),
such as `x < x < y`, which it leaves to a later lint on chains.
`lint::eq_op` states this:

```fren
pub enum InfixOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset, Add, Sub, Concat, Union, Minus, Mul, Inter, Join,
}

pub enum EqOpValue { AlwaysTrue, AlwaysFalse, Zero, Empty, Operand }

pub comp eq_op {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Operand, Zero}
    use self::InfixOp::{Add, Concat, Eq, Ge, Gt, Iff, In, Join, Le, Lt, Minus, Mul, Ne, Sub, Subset}
    in op: InfixOp
    in same?             -- the operands are written the same
    pub det out fires?
    pub out value: EqOpValue  -- what the expression is, where it fires

    req rule: fires? iff (same? and not op in {Add, Mul, Concat, Join, In})
    req values: when fires?, value = match op {
        Eq | Le | Ge | Iff | Subset => AlwaysTrue,
        Ne | Lt | Gt => AlwaysFalse,
        Sub => Zero,
        Minus => Empty,
        _ => Operand,
    }

    expect needs_same: when fires?, same?
}
```

`eq_op` also fires on `when C, D` and `unless C, D` where `C` and `D` are
written the same. `when C, C` is always `true`, and `unless C, C` is `C`.
The body is then almost always a copy of the condition, pasted where the
consequent was meant. `lint::eq_op_conditional` states this:

```fren
pub comp eq_op_conditional {
    use self::EqOpValue::{AlwaysTrue, Operand}
    in unless?           -- `unless`, rather than `when`
    in same?             -- the condition and the body are written the same
    pub det out fires?
    pub out value: EqOpValue  -- what the expression is, where it fires

    req rule: fires? iff same?
    req values: when fires?, value = if unless? then Operand else AlwaysTrue
}
```

`same_branches` fires on `if c then a else b`, where `a` and `b` are
written the same: the condition decides nothing. The fix replaces the
conditional with `a`, in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes), from the operator that the conditional is an
operand of and what follows it, as for
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions). The value is `a`'s, and
the [guards](../Lang/Expressions.md#sequences) of what remains get no
weaker: the copy of `a` guarded by `c` and the one guarded by `not c` are
both defined exactly when `a` is defined under the guard of the
conditional, which is `a`'s guard after the fix, and removing `c` only
removes something that is evaluated. A `match` whose arms are all written
the same is left to other lints. `lint::same_branches` states when it
fires:

```fren
pub comp same_branches {
    in same?             -- the branches are written the same
    pub det out fires?

    req rule: fires? iff same?
}
```

`duplicate_elements` fires on a set or relation literal with an element
written the same as an earlier one, as in `{a, b, a}` or `{(a, b), (a,
b)}`, and is reported once for the literal. A set has no repeats, so the
fix, which removes each repeat with the `,` before it, keeps the meaning,
and it keeps the guards, which are the same for every element of the
literal. It does not fire on a sequence literal, where a repeat means
something. `lint::duplicate_elements` states when it fires:

```fren
pub comp duplicate_elements {
    in n_repeats: Nat    -- elements written the same as an earlier one
    pub det out fires?

    req rule: fires? iff n_repeats > 0
}
```

`empty_argument` fires on a method applied to an empty argument, where
its value at that [edge](../Lang/Expressions.md#methods) does not depend on
the receiver as it seems to. An argument is empty if it is written `""`
or `[]`, or, as the length of `slice`, `0`. Where `s` is the receiver, a
string or a sequence, and `e` the empty argument:

| Written | Value |
|---|---|
| `s.starts_with?(e)`, `s.ends_with?(e)`, `s.contains?(e)` | `true` |
| `s.replace(e, b)` | `b ++ s` |
| `s.replace_all(e, b)` | `s` |
| `s.index_of(e, i)` | `i` if `0 <= i <= s.len`, and `-1` otherwise |
| `s.slice(i, 0)` | `""`, or `[]` |

The message says what the expression is. It has no fix: the likely
mistake is the argument, and writing the value instead would keep the
mistake and hide it. `lint::empty_argument` states when it fires, from the
method and the position of an empty argument:

```fren
pub comp empty_argument {
    use lang::Method
    use lang::Method::{Contains, EndsWith, IndexOf, Replace, ReplaceAll, Slice, StartsWith}
    in method: Method
    in index: Nat        -- the position of the argument, from 0
    in empty?            -- it is written `""` or `[]`, or `0`
    pub det out fires?

    req rule: fires? iff (empty? and match method {
        StartsWith | EndsWith | Contains | Replace | ReplaceAll | IndexOf => index = 0,
        Slice => index = 1,
        _ => false,
    })
}
```

## Negations after operators

`suspicious_unary_op_formatting` fires on a binary operator that is a
[punctuator](../Lang/Lexical.md#punctuators), directly followed by a
negation, `-`, that whitespace follows, as in `x >=- 1`, `a =- b` and `a
*- b`: the reader may take the operator and the `-` for one operator.
`-` itself is never directly followed by a `-`, which starts a comment,
and `<` never is, since `<-` is one punctuator, an
[error](../Lang/Lexical.md#punctuators). The lint looks only at the text,
in any constraint, binding, definition, constant or global expectation,
and is fixable. The fix moves the whitespace from after the `-` to before
it, so `x >=- 1` becomes `x >= -1`, and keeps the rest as it is written;
before an operand that starts with `-`, it keeps one space after the `-`
too, as in `x >= - -1`. Only whitespace moves, so the fix changes neither
the meaning nor the guards. [`fren fmt`](../Fmt.md) writes the negation so
too. `lint::suspicious_unary_op_formatting` states when it fires:

```fren
pub comp suspicious_unary_op_formatting {
    in punctuator?       -- the operator is a punctuator other than `-`
    in adjacent?         -- the `-` directly follows it
    in spaced?           -- whitespace directly follows the `-`
    pub det out fires?

    req rule: fires? iff (punctuator? and adjacent? and spaced?)
}
```

`no_effect_replace` fires on `s.replace(a, b)` and `s.replace_all(a, b)`,
where `a` and `b` are written the same, and is fixable: replacing an
occurrence of `a` with `a` leaves `s` as it was. At the
[edge](../Lang/Expressions.md#methods) where `a` is `""`, `s.replace("",
"")` is `"" ++ s` and `s.replace_all("", "")` is `s`, which are both `s`,
so the fix is `s` for every `s` and `a`, of a string or, for `replace`, a
sequence; [`empty_argument`](#suspicious-expressions) fires there too. The
fix keeps the receiver's text, and puts it in parentheses where it is an
operand or a receiver that requires them
([`lang::operand`](../Lang/Expressions.md#operators)). It only stops
evaluating `a` and `b`, so no guard is weaker, and it brings the expression
into the [decidable core](../Lang/Decidability.md#strings), which `replace`
and `replace_all` are outside of. `lint::no_effect_replace` states when it
fires, and the values of the calls, compared with any string `u`, which its
`impl` proves for strings:

```fren
set_option fren.lint.undecidable "allow" in
pub comp no_effect_replace {
    in same?             -- the arguments are written the same
    in s: String         -- the receiver
    in a: String         -- the first argument
    in b: String         -- the second
    in u: String         -- any string
    pub det out fires?
    pub out replaced?    -- `s.replace(a, b) = u`
    pub out replaced_all?  -- `s.replace_all(a, b) = u`

    assume written: when same?, a = b

    req rule: fires? iff same?
    req first: when fires?, replaced? iff s = u
    req all: when fires?, replaced_all? iff s = u
}
```

## Tests of literals

`const_is_empty` fires on a test of a literal whose value is fixed by the
literal, which is probably not the literal meant. It has no fix, and its
message says what the test always is. It fires on:

- a comparison of the `len` of a string or sequence literal with an integer
  literal, such as `"ab".len = 0` or `[1, 2].len > 0`, with the literal on
  either side;
- a comparison of the `card` of a set or relation literal that
  [`card_zero`](Style.md#empty-collections) fires on, a test of whether it
  is empty, such as `{a}.card = 0`;
- `e = E` or `e != E`, where `E` is `""`, `[]` or `{}`, and `e` a string,
  sequence, set or relation literal that is not empty, such as `"ab" = ""`,
  on either side.

A string literal has as many characters as its value, and a sequence
literal as many elements as it is written with, so the length is fixed. A
set literal's elements may be equal, so `{a, b}.card` is `1` or `2`, but it
is `0` exactly when the literal is `{}`, so only whether it is empty is
fixed. Where `const_is_empty` fires on a length, [`length_zero` and
`card_zero`](Style.md#empty-collections) do not, since writing `"ab" = ""`
would keep the mistake. `"" = ""` is left to [`eq_op`](#suspicious-expressions),
and `[].len` and `{}.card` are errors, since `[]` and `{}` have no type
there. `lint::const_is_empty` states when it fires on a length, and what
the comparison always is, and `lint::const_empty_equation` the same for an
equation with an empty literal:

```fren
pub comp const_is_empty {
    in op: Comparison
    in bound: Int        -- the integer literal compared with
    in left?             -- the length is the left operand, rather than the right
    in set?              -- the literal is a set's or relation's
    in n: Int            -- its characters, or the elements it is written with
    pub det out fires?
    pub det out value?   -- what the comparison always is, where it fires

    assume counts: n >= 0

    inst p: length_zero { op, bound, left? }

    req rule: fires? iff (not set? or p.fires?)
    req value: value? iff (if set? then (p.empty? iff n = 0)
        else compares?(op, if left? then n else bound, if left? then bound else n))
}

pub comp const_empty_equation {
    in equal?            -- the operator is `=`, rather than `!=`
    in n: Int            -- the characters or elements of the literal that is not `E`
    pub det out fires?
    pub det out value?

    assume counts: n >= 0

    req rule: fires? iff n > 0
    req value: value? iff (equal? iff n = 0)
}
```

The value is exact: where the lint fires, the comparison has it for every
length that the literal can have, its number of characters or elements, or
for a set, any `card` from `1` to that number if it is not empty:

```fren
comp const_is_empty_exact {
    in op: Comparison
    in bound: Int
    in left?
    in set?
    in n: Int
    in length: Int       -- the literal's `len` or `card`

    assume lengths: n >= 0 and (if set? then (if n = 0 then length = 0 else 1 <= length and length <= n)
        else length = n)

    inst p: const_is_empty { op, bound, left?, set?, n }

    expect exact: when p.fires?,
        compares?(op, if left? then length else bound, if left? then bound else length) iff p.value?
}
```

## Ranges of characters

`almost_complete_range` fires on a range in a class of a
[pattern](../Lang/Expressions.md#patterns) that is one character short of a
whole alphabet, and is fixable: `a-y` and `b-z`, `A-Y` and `B-Z`, and `0-8`.
A range is from its first character to its last, both included, so `[a-y]`
leaves out `z`, which is probably a mistake. The fix is the whole range,
`a-z`, `A-Z` or `0-9`, and the message is reported once for the literal,
whose fix completes each such range in it, writing the literal as
[`manual_pattern_char_comparison`](Style.md#classes-of-characters)'s fix
does. Only the literal changes, so the fix keeps the guards.

`1-9` is not one of them: it is often meant, as in `[1-9][0-9]*`, a number
without a leading zero. `0-8` has no such use, since `0-7` is the octal
digits. `lint::almost_complete_range` states this, from the code points of
the characters before and after `-`, as [`lang::char_range`](../Lang/Expressions.md#patterns)
does: `a` is 97, `A` is 65 and `0` is 48:

```fren
pub comp almost_complete_range {
    in low: Int          -- the code point of the character before `-`
    in high: Int         -- of the character after it
    pub det out fires?
    pub det out whole_low: Int   -- the range of the fix, from this code point
    pub det out whole_high: Int  -- to this one

    req rule: fires? iff ((low in {97, 98, 65, 66} and high = low + 24) or (low = 48 and high = 56))
    req fix_low: whole_low = (if fires? and low in {98, 66} then low - 1 else low)
    req fix_high: whole_high = (if fires? and high in {121, 89, 56} then high + 1 else high)

    expect not_digits: when low = 49 and high = 57, not fires?
    expect whole: when fires?, whole_high - whole_low = 25 or (whole_low = 48 and whole_high = 57)
}
```

`erasing_op` fires on an operation whose value ignores an operand: `x * 0`
and `0 * x` are always `0`, and `s inter {}`, `{} inter s`, `{} minus s`
and `r join {}` are always `{}`. It mirrors
[`identity_op`](Complexity.md#identities), and an operand is `0` or `{}` as
it is there. The message says what the value is. It has no fix: the
likely mistake is the literal, and writing the value instead would keep
the mistake and hide it. Where both operands are written the same, as in
`{} inter {}`, `eq_op` fires instead. `lint::erasing_op` states this:

```fren
pub comp erasing_op {
    use self::IdentityOperand::{Empty, Zero}
    use self::InfixOp::{Inter, Join, Minus, Mul}
    in op: InfixOp
    in left: IdentityOperand
    in right: IdentityOperand
    in same?             -- the operands are written the same
    pub det out fires?

    req rule: fires? iff (not (same? and op in {Inter, Minus}) and match op {
        Mul => left = Zero or right = Zero,
        Inter | Join => left = Empty or right = Empty,
        Minus => left = Empty,
        _ => false,
    })
}

expect erasing_not_eq_op: forall (e: erasing_op) (q: eq_op), when q.op = e.op and q.same? = e.same?,
    not (e.fires? and q.fires?)
```

`ifs_same_cond` fires on a test of a chain of `else if` written the same
as an earlier test of the chain, as the second `x > 0` in `if x > 0 then a
else if x > 0 then b else c`. Its branch is never taken: it is guarded by
the negation of the earlier test, so wherever the test holds, the earlier
branch is taken. It is reported at the repeated test, and the message names
the earlier one. A test in parentheses, `else (if ...)`, is still in the
chain. It has no fix: one of the tests is probably not the one meant.
`lint::ifs_same_cond` states when it fires:

```fren
pub comp ifs_same_cond {
    in earlier?          -- an earlier test of the chain is written the same
    pub det out fires?

    req rule: fires? iff earlier?
}
```

## Comparisons

These lints fire on comparisons whose value is fixed. The
[checks](../Check.md) can see such a comparison only where it fixes a whole
constraint, which is then vacuous or never holds; the lints also find it as
an operand, such as in the condition of an `if`, where it fixes nothing that
a check reports. They have no fix: the likely mistake is the bound, the
operator, or `and` written for `or`, and writing the value instead would
keep the mistake and hide it.

`absurd_extreme_comparisons` fires on a comparison of a string's or
sequence's `len`, or a set's or relation's `card`, with an integer literal,
whose value is fixed because a length is never negative: `s.len < 0` is
always `false`, and `q.card >= 0` always `true`. So is every comparison
with a negative literal: `s.len > -1` is always `true`, and `s.len = -1`
always `false`. The length may be on either side, as in `0 > s.len`. The
message says what the comparison always is. It does not fire on an `Int`,
which may be negative, such as an input `n` in `n >= 0`, nor on the
comparisons with `0` that say whether the collection is empty, such as
`s.len > 0`, which are [`length_zero`'s](Style.md#empty-collections).
`lint::absurd_extreme_comparisons` states when it fires:

```fren
pub comp absurd_extreme_comparisons {
    use self::Comparison::{Ge, Gt, Le, Lt, Ne}
    in op: Comparison
    in bound: Int        -- the literal compared with
    in left?             -- the length is the left operand, rather than the right
    pub det out fires?
    pub det out value?   -- what the comparison always is, where it fires

    req rule: fires? iff (bound < 0 or (bound = 0 and (if left? then op in {Lt, Ge} else op in {Gt, Le})))
    req fixed: value? iff (if left? then op in {Ne, Gt, Ge} else op in {Ne, Lt, Le})
}

comp absurd_extreme_comparisons_exact {
    in op: Comparison
    in bound: Int
    in left?
    in n: Int            -- the length

    assume length: n >= 0

    inst p: absurd_extreme_comparisons { op, bound, left? }
    inst q: length_zero { op, bound, left? }

    expect exact: when p.fires?, compares?(op, if left? then n else bound, if left? then bound else n) iff p.value?
    expect not_length_zero: not (p.fires? and q.fires?)
}
```

`contradictory_comparisons` fires on two comparisons of one operand,
written the same, joined by `and` and never both true, or joined by `or`
and never both false:

| Written | Value |
|---|---|
| `x = a and x = b`, where `a` and `b` are distinct | `false` |
| `x != a or x != b`, where `a` and `b` are distinct | `true` |
| `x < 3 and x > 5`, `x <= 3 and x >= 4`, `x = 3 and x > 3` | `false` |
| `x > 3 or x < 5`, `x >= 4 or x <= 3`, `x != 3 or x <= 3` | `true` |

Two values are distinct if they are integer literals of different
values, string literals written differently, without escape sequences,
`true` and `false`, or two different variants without payloads, such as
`Mode::Heat` and `Mode::Cool`, by what their paths resolve to. The usual
mistake is `and` and `or` swapped: `m != Mode::Heat or m != Mode::Cool`
always holds. Each comparison may have its operand on either side, as in
`5 < x`. With integer literals, any two comparisons are looked at, with
the cases exactly those that
[`disjoint?`](Complexity.md#comparisons) gives: under `and`, the two are
disjoint, and under `or`, their complements are, so that no integer
fails both. The message says which value the two always have. It fires
inside any expression, such as the condition of an `if`.
`lint::contradictory_comparisons` states when it fires on integers, and
`lint::contradictory_equalities` on other values:

```fren
pub comp contradictory_comparisons {
    in conjunction?      -- the comparisons are joined by `and`, rather than `or`
    in first: Comparison  -- `x OP k`, with `x` on the left
    in first_bound: Int
    in second: Comparison
    in second_bound: Int
    pub det out fires?

    req rule: fires? iff (if conjunction?
        then disjoint?(first, first_bound, second, second_bound)
        else disjoint?(complement_of(first), first_bound, complement_of(second), second_bound))
}

comp contradictory_comparisons_exact {
    in conjunction?
    in first: Comparison
    in first_bound: Int
    in second: Comparison
    in second_bound: Int
    in x: Int

    inst p: contradictory_comparisons { conjunction?, first, first_bound, second, second_bound }

    expect exact: when p.fires?,
        (if conjunction? then both?(first, first_bound, second, second_bound, x)
        else compares?(first, x, first_bound) or compares?(second, x, second_bound))
        iff not conjunction?
}

pub comp contradictory_equalities {
    use self::Comparison::{Eq, Ne}
    in conjunction?
    in first: Comparison
    in second: Comparison
    in distinct?         -- the values compared with are distinct
    pub det out fires?

    req rule: fires? iff (distinct? and (if conjunction? then first = Eq and second = Eq else first = Ne and second = Ne))
}
```

Where one of two comparisons of an operand with integer literals implies
the other, [`redundant_comparisons`](Complexity.md#comparisons) fires
instead: that is never where this lint does, since a single comparison of
an integer always holds for some integer and fails for another.
