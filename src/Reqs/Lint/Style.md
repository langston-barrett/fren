# Style

The lints of the `style` group find a clearer way to write the same
thing, and `fren fix` fixes each of them.

## Glob imports

`use E::*` brings every variant of `E` into scope, including variants
added later, so a reader cannot tell where a name comes from, and adding a
variant to one enumeration can make a name in another module
[ambiguous](../Lang/Modules.md#resolution). `glob_imports` reports every
`use ...::*`. Its message suggests importing by name the variants the file
uses through it, or writing them qualified, as in `Mode::Heat`.

A glob import that is unused is reported by both `glob_imports` and
[`unused_imports`](Unused.md#unused-imports).

## Conditionals

`unless_not` and `collapsible_when` report a conditional that reads more
simply written another way, in the same places as
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions), and suggest the rewritten
form, which keeps the meaning and the guards (see
[Expressions](../Lang/Expressions.md#sequences)). A condition is a
*negation* if it is `not A` or `a != b`; the condition it negates is `A`,
or `a = b`. [`if_not_else`](Pedantic.md#negated-conditions), in the
`pedantic` group, is a third such lint.

- `unless_not` fires on `unless C, D` where `C` is a negation: `unless not
  A, D` becomes `when A, D`, and `unless a != b, D` becomes `when a = b,
  D`. It does not fire on any other condition, such as `unless x < 3, D`:
  saying when `D` need not hold is what `unless` is for. `D` is guarded by
  `not C` before, and by the condition `C` negates after, which is the
  same.
- `collapsible_when` fires on a conditional whose body is a conditional
  with the same keyword: `when A, when B, D` becomes `when A and B, D`, and
  `unless A, unless B, D` becomes `unless A or B, D`. It does not fire on a
  nest of `when` and `unless`, such as `unless A, when B, D`, which keeps
  apart an exception and a case, as `modules::resolve` does (see
  [Resolution](../Lang/Modules.md#resolution)). The guards are the same: `B`
  is guarded by `A` in `A and B`, as it is in `when A, when B, D`, and `D`
  by `A` and `B`. For `unless`, `B` is guarded by `not A` in `A or B`, and
  `D` by `not A` and `not B`, which is `not (A or B)`.

`A`, `B` and the other operands keep their text, in parentheses where
[`lang::operand`](../Lang/Expressions.md#operators) requires them, and only
there, as for `nonminimal_bool`: `unless a? iff b?, unless c?, d?` becomes
`unless (a? iff b?) or c?, d?`. That each rewritten form means what the
expression means is proved in Lean, over the model of expressions of
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions), with each lint's rules
alone, so that the fix of one lint makes none of the changes another
suggests.

What these lints and `if_not_else` look at in an operand is its outermost
operator, `lint::Head`: `Not` for `not A`, `Unequal` for `a != b`, `If`,
`When` and `Unless` for the conditionals, and `Other` for the rest.
`lint::unless_not` and `lint::collapsible_when` state when they fire:

```fren
pub mod lint

pub enum Head { Not, Unequal, If, When, Unless, Other }

pub comp unless_not {
    in unless?           -- the conditional is `unless`, rather than `when`
    in condition: Head
    pub det out fires?

    req rule: fires? iff (unless? and condition in {Head::Not, Head::Unequal})

    expect other: when condition = Head::Other, not fires?
}

pub comp collapsible_when {
    in unless?           -- the conditional is `unless`, rather than `when`
    in body: Head
    pub det out fires?

    req rule: fires? iff body = (if unless? then Head::Unless else Head::When)

    expect mixed: when unless? and body = Head::When, not fires?
}
```

## Empty collections

`length_zero` fires on a comparison of a string's or sequence's `len` with
`0` or `1` that says that it is empty, or that it is not. A length is never
negative, so `n = 0`, `n <= 0` and `n < 1` each say that it is empty, and
become `s = ""`, or `q = []`, and `n != 0`, `n > 0` and `n >= 1` each say
that it is not, and become `s != ""`. So does each with the length on the
right: `0 < s.len` is `s.len > 0`. `card_zero` is the same for a set's or
relation's `card`, with `{}`. Both are fixable. Other comparisons with `0`
or `1`, such as `n >= 0`, which always holds, are left as they are.
`lint::Comparison` is the comparison operators, and `lint::length_zero`
states which comparisons they fire on:

```fren
pub enum Comparison { Eq, Ne, Lt, Le, Gt, Ge }

use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}

pub comp length_zero {
    in op: Comparison
    in bound: Int        -- the literal compared with
    in left?             -- the length is the left operand, rather than the right
    pub det out fires?
    pub det out empty?   -- the fix says that it is empty, rather than not

    req rule: fires? iff (if left?
        then (bound = 0 and op in {Eq, Ne, Le, Gt}) or (bound = 1 and op in {Lt, Ge})
        else (bound = 0 and op in {Eq, Ne, Ge, Lt}) or (bound = 1 and op in {Gt, Le}))
    req fix: empty? iff (if left? then op in {Eq, Le, Lt} else op in {Eq, Ge, Gt})

    expect not_negative: when op = Lt and bound = 0 and left?, not fires?
}
```

Each fix is exact: where the lint fires, the comparison of a length `n`
holds exactly when the fix does, `n = 0` if it says that the collection is
empty and `n != 0` if not. `compares?` is the value of a comparison:

```fren
fn compares?(op: Comparison, a: Int, b: Int) := match op {
    Eq => a = b,
    Ne => a != b,
    Lt => a < b,
    Le => a <= b,
    Gt => a > b,
    Ge => a >= b,
}

comp length_zero_exact {
    in op: Comparison
    in bound: Int
    in left?
    in n: Int            -- the length

    assume length: n >= 0

    inst p: length_zero { op, bound, left? }

    expect exact: when p.fires?,
        compares?(op, if left? then n else bound, if left? then bound else n) iff (p.empty? iff n = 0)
}
```

`lint::length_zero_keeps_meaning` states the fixes as laws, for strings,
sequences, sets and relations (see [Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.length_zero "expect" in
set_option fren.lint.card_zero "expect" in
pub comp length_zero_keeps_meaning {
    in s: String
    in q: Seq(Int)
    in t: Set(Int)
    in r: Rel(Bool, Bool)

    expect string_length_zero: ((s.len = 0) iff s = "") and ((s.len <= 0) iff s = "") and ((s.len > 0) iff s != "")
    expect sequence_length_zero: ((q.len = 0) iff q = []) and ((q.len <= 0) iff q = []) and ((q.len > 0) iff q != [])
    expect length_one: ((s.len < 1) iff s = "") and ((s.len >= 1) iff s != "") and ((s.len != 0) iff s != "")
    expect length_right: ((0 = q.len) iff q = []) and ((0 < q.len) iff q != []) and ((1 > q.len) iff q = [])
    expect card_zero: ((t.card = 0) iff t = {}) and ((t.card <= 0) iff t = {}) and ((t.card > 0) iff t != {})
    expect relation_card_zero: ((r.card = 0) iff r = {}) and ((r.card > 0) iff r != {})
}
```

## Trivial patterns

`trivial_pattern` fires on `s.matches?(p)`, where the
[pattern](../Lang/Expressions.md#patterns) `p` is a nonempty string `lit`,
written with characters that are not special and escapes `\c`, with `.*`
at its start, its end, both or neither, and is fixable:

| Pattern | Fix |
|---|---|
| `lit` | `s = "lit"` |
| `lit.*` | `s.starts_with?("lit")` |
| `.*lit` | `s.ends_with?("lit")` |
| `.*lit.*` | `s.contains?("lit")` |

The fix writes `lit` as a string literal that is not raw, with each `\c` as
the character `c`, and with the escapes that a [literal](../Lang/Lexical.md#literals)
needs: `\\` for `\`, `\"` for `"`, `\n` and `\t`, and `\xHH` for the other
control characters. So `s.matches?(r"a\.b.*")` becomes
`s.starts_with?("a.b")`. The receiver keeps the text it is written with; in
`s = "lit"`, it is written without the parentheses a receiver may need, and
put in parentheses where it is an operand of `=` that requires them, and so
is the equation, where it is an operand that requires them
([`lang::operand`](../Lang/Expressions.md#operators)). The fix evaluates the
receiver where the pattern did, and nothing else, so it keeps every guard.

Clippy's `trivial_regex` is in its `nursery` group, because of the quirks
of Rust's `regex` crate. Fren's patterns have none: a pattern always
matches the whole string, and has no flags, anchors or classes of
characters such as `\d`. So `trivial_pattern` is in `style`. For
[decidability](../Lang/Decidability.md#strings), the four forms are the same:
`matches?` with a literal pattern, `starts_with?`, `ends_with?` and
`contains?` with a constant, and an equation with a constant are each in
the decidable core, so the fix never changes whether a component is
decidable.

`lint::trivial_pattern` states when it fires, from the value of the
literal, and which fix it makes:

```fren
pub enum PatternFix { Equality, StartsWith, EndsWith, Contains }

pub comp trivial_pattern {
    in pattern: String       -- the value of the literal
    pub det out fires?
    pub det out fix: PatternFix

    req rule: fires? iff pattern.matches?(r"(\.\*)?([^\\.\[\]()*+?{}|^]|\\[\\.\[\]()*+?{}|^-])+(\.\*)?")
    req which: fix = if pattern.starts_with?(".*") then (if pattern.ends_with?(".*") then PatternFix::Contains
        else PatternFix::EndsWith)
        else if pattern.ends_with?(".*") then PatternFix::StartsWith
        else PatternFix::Equality

    expect not_everything: when pattern = ".*", not fires?
    expect classes_kept: when pattern = "[a-z]", not fires?
}
```

## Boolean types

A name that ends in `?` is a `Bool`, so `in ready?: Bool` declares the same
input as `in ready?` (see [Boolean names](../Lang/Types.md#boolean-names)).
`redundant_bool_type` fires on a `: Bool` that the rule implies: on a
variable, input or output, defined or not, on a field of a record, on a
parameter of a defined function, and on a function's result type. It is
reported at `: Bool`, and the fix removes it, with the spaces before it,
from the end of the name, or of the `)` before a result type: `fn ok?(n:
Int): Bool := n > 0` becomes `fn ok?(n: Int) := n > 0`. A declaration has no
guard. `lint::redundant_bool_type` states when it fires, from a declaration
that [`lang::bool_naming`](../Lang/Types.md#boolean-names) accepts:

```fren
use lang::Annot

pub comp redundant_bool_type {
    in name: String      -- the declared name
    in annot: Annot
    pub det out fires?

    req rule: fires? iff (name.ends_with?("?") and annot = Annot::BoolTy)

    expect written: when fires?, annot != Annot::Missing
}
```

## Matches that are memberships

`match_like_membership` looks at the arms of a
[`match`](../Lang/Expressions.md#matches) as written, as the [match
lints](Pedantic.md#matches) of the `pedantic` group do.

`match_like_membership` fires on a `match` on `x` whose bodies are the
literals `true` and `false`, each at least once, and whose patterns name
only variants without a payload, or are `_`. It says whether `x` is one of
the variants whose arms are `true`. The fix is `x in {E::A, E::B}`, of
those variants, or `x = E::A` for one, if the `_` arm is `false`, or if
there is no `_` arm and no more variants are `true` than `false`.
Otherwise it is `not x in {...}`, or `x != E::A`, of the variants that are
`false`. The variants are written as the patterns write them, so a variant
brought into scope by `use` stays unqualified, and `x` and the result are
in parentheses where `lang::operand` requires them. The bodies are
literals, which guard nothing, and `x` is evaluated as before. A `match`
whose arms are all `true`, or all `false`, is left to
[`match_same_arms`](Pedantic.md#matches).
`lint::match_like_membership` states when it fires, and when its fix is
negated:

```fren
pub comp match_like_membership {
    in bool_bodies?      -- every body is `true` or `false`, and each is some body
    in no_payloads?      -- every pattern names variants without a payload, or is `_`
    in wildcard?         -- there is a `_` arm
    in wildcard_true?    -- its body is `true`
    in n_true: Int       -- variants named by arms whose body is `true`
    in n_false: Int      -- and by arms whose body is `false`
    pub det out fires?
    pub det out negated?  -- the fix is a negated membership, of the `false` variants

    assume counts: n_true >= 0 and n_false >= 0

    req rule: fires? iff (bool_bodies? and no_payloads?)
    req negated: negated? iff (if wildcard? then wildcard_true? else n_true > n_false)

    expect fewer_listed: when not wildcard? and negated?, n_false < n_true
}
```

## Bindings

`redundant_bindings` fires on a binding of an instance, or a field of a
record literal, written `x := x`, and is fixable. The fix is `x`, which
means `x := x` by definition, for [bindings](../Lang/Instances.md)
and [fields](../Lang/Expressions.md#records) alike, so it keeps the meaning
and the guards. `lint::redundant_bindings` states when it fires, from the
texts of the name and of the expression after `:=`:

```fren
pub comp redundant_bindings {
    in name: String      -- the name bound, or the field given
    in value: String     -- the expression after `:=`, as written
    pub det out fires?

    req rule: fires? iff value = name
}
```

## Negations

`double_neg` fires on a negation of a negation, `- -x`, through
parentheses, as in `-(-x)` and `-(-(x))`: it is `x`, which is its fix.
`neg_multiply` fires on a product with `-1`, the negation of the literal
`1`, through parentheses: `x * -1` and `-1 * x` are `-x`, which is its fix.
`Int` is the integers, without overflow, so both fixes are exact. Both are
fixable:

```fren
pub comp double_neg {
    in negated_operand?  -- the operand of the negation, through parentheses, is a negation
    pub det out fires?

    req rule: fires? iff negated_operand?
}

pub comp neg_multiply {
    in left_minus_one?   -- the left operand, through parentheses, is `-1`
    in right_minus_one?  -- the right operand is
    pub det out fires?
    pub det out negate_left?  -- the fix negates the left operand, rather than the right

    req rule: fires? iff (left_minus_one? or right_minus_one?)
    req fix: negate_left? iff right_minus_one?
}
```

Each of these fixes, and that of
[`int_plus_one`](Complexity.md#off-by-one-comparisons), writes its operands
with the text they are written with, in parentheses where [`lang::operand`](../Lang/Expressions.md#operators)
requires them, and only there, and the fix itself in parentheses where it
is an operand that requires them and is not already in parentheses, as for
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions): `2 * - -(x + y)` becomes `2
* (x + y)`, `(a + b) * -1` becomes `-(a + b)`, and `(x) >= y + 1` becomes
`x > y`. A negation of an operand that starts with `-` is written with a
space, `- -y`, since `--` starts a comment. No fix adds or removes an
`and`, `or`, `when`, `unless`, `if` or `match`, and each operand is
evaluated where it was, so the guards are kept.
