# Pattern tests and chained comparisons

The lints of the `style` group that write a [pattern
test](../../Lang/Expressions.md#pattern-tests) or a [chained
comparison](../../Lang/Expressions.md#chained-comparisons) more clearly.

## Pattern tests

A [pattern test](../../Lang/Expressions.md#pattern-tests), `e is P`, is for
the [patterns](../../Lang/Patterns.md) that `=` and `in` cannot write:
those with a payload, ranges and nested patterns. `is_equality` fires on
`e is P` where each alternative of `P` is a variant without a payload,
`true`, `false`, a string literal or an integer literal, and is fixable:
`x is E::A` becomes `x = E::A`, `n is 0 | 1` becomes `n in {0, 1}`, and `x
is E::A | E::B` becomes `x in {E::A, E::B}`, with each alternative written
as `P` writes it. A range of one value, such as `3..=3`, and a literal
written otherwise than its value, such as `0x10`, are left as they are,
as is a pattern with any other alternative, such as `x is E::A | E::B(_)`
or `n is 0 | 5..`. It does not fire where
[`irrefutable_is`](../Suspicious.md#pattern-tests) does, since the test is
then always `true`, however it is written. `e` keeps its text, in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes);
an equation and a membership bind as a pattern test does, as comparisons,
so the fix needs no parentheses that the test does not. `not x is E::A`
becomes `not x = E::A`, and `b? is true` becomes `b? = true`, which
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions) then fixes
to `x != E::A` and `b?`. `e` is evaluated where it was, and the
alternatives guard nothing, so the fix keeps the guards.
[`match_like_membership`](../Style.md#matches-that-are-memberships)
writes a pattern test only where this lint would not fire on it.

Clippy's nearest lint, `equatable_if_let`, is in its `nursery` group, but
that group is about a lint's maturity rather than a judgment of style.
`style`, and so `warn`, fits here: there should be one way to write each
test, and Fren's other lints already write tests of variants without a
payload with `=` and `in` (`membership_chain`, `match_like_membership`).
`lint::is_equality` states when it fires:

```fren
pub mod lint

pub comp is_equality {
    in equatable?        -- each alternative of the pattern is a variant without a payload or a literal
    in irrefutable?      -- `irrefutable_is` fires on the test
    pub det out fires?

    ensure rule: fires? iff (equatable? and not irrefutable?)
}
```

The [refinements](../../Lang/Refinement.md) below check the fixes of
[`match_like_membership`](../Style.md#matches-that-are-memberships) to a
pattern test, for a `match` with a `_` arm and one without, negated and
not. Here, as in the rest of these chapters, an operand of a rewrite is a
variable, which stands for any expression of its type: an expression has
no effects, so a rewrite that holds for every value of its operands holds
for every expression. `Shade` is an enumeration with a payload:

```fren
pub enum Shade { Light, Dark, Tinted(Int) }

set_option fren.lint.match_like_membership "allow" in
pub comp membership_test_written {
    in s: Shade
    in n: Int
    pub det out tinted? := match s { Shade::Tinted(_) => true, _ => false }
    pub det out shaded? := match s { Shade::Light => false, Shade::Dark | Shade::Tinted(_) => true }
    pub det out light? := match s { Shade::Light => true, _ => false }
    pub det out untinted? := match s { Shade::Tinted(_) => false, _ => true }
    pub det out small? := match n { 0 | 1 => true, _ => false }
    pub det out digit? := match n { 0..=9 => true, _ => false }
    pub det out clear? := match s { Shade::Tinted(0) => true, _ => false }
    pub det out positive? := match n { ..=0 => false, _ => true }
}

pub comp membership_test_fixed {
    in s: Shade
    in n: Int
    pub det out tinted? := s is Shade::Tinted(_)
    pub det out shaded? := s != Shade::Light
    pub det out light? := s = Shade::Light
    pub det out untinted? := not s is Shade::Tinted(_)
    pub det out small? := n in {0, 1}
    pub det out digit? := n is 0..=9
    pub det out clear? := s is Shade::Tinted(0)
    pub det out positive? := not n is ..=0
}

refine membership_test_sound: membership_test_fixed refines membership_test_written
refine membership_test_complete: membership_test_written refines membership_test_fixed
```

The refinements check the fixes of `is_equality`:

```fren
set_option fren.lint.is_equality "allow" in
pub comp is_equality_written {
    in s: Shade
    in n: Int
    in b?
    pub det out light? := s is Shade::Light
    pub det out plain? := s is Shade::Light | Shade::Dark
    pub det out dark? := not s is Shade::Dark
    pub det out small? := n is 0 | 1
    pub det out negative? := n is -1
    pub det out set? := b? is true
}

set_option fren.lint.nonminimal_bool "allow" in
pub comp is_equality_fixed {
    in s: Shade
    in n: Int
    in b?
    pub det out light? := s = Shade::Light
    pub det out plain? := s in {Shade::Light, Shade::Dark}
    pub det out dark? := not s = Shade::Dark
    pub det out small? := n in {0, 1}
    pub det out negative? := n = -1
    pub det out set? := b? = true
}

refine is_equality_sound: is_equality_fixed refines is_equality_written
refine is_equality_complete: is_equality_written refines is_equality_fixed
```

## Chained comparisons

`chainable_comparison` fires on two adjacent conjuncts of a run of `and`
that one [chained comparison](../../Lang/Expressions.md#chained-comparisons)
writes, and is fixable: `lo <= x and x < hi` becomes `lo <= x < hi`. Each
conjunct is a comparison with `<`, `<=`, `>` or `>=`, or a chained
comparison, and the two order the same way, with the last operand of the
first [written the same](../../Lint.md#written-the-same) as the first operand
of the second. A conjunct that is one comparison may be written the other
way round to chain: `x >= lo and x < hi` becomes `lo <= x < hi`, `b > a
and c > b` becomes `a < b < c`, and `x < hi and x > lo` becomes `hi > x >
lo`. Neither conjunct is moved, and a chained comparison is not written
the other way round, since either would reorder the comparisons, and with
them the guards; at most one way of writing the conjuncts then chains
them, so the fix is written with `<` and `<=` where the conjuncts allow
it, and with `>` and `>=` otherwise. The lint does not fire where the
chain's first operand would be written the same as its last, as in `a <=
b and b <= a`, which [`double_comparison`](../Complexity/Comparisons.md#double-comparisons)
reports.

The run of `and` is the conjuncts of `p and q and ... and r`, through
each left operand that is an `and` not in parentheses, so `p and 0 <= i
and i < n and q` fires at `0 <= i and i < n`, and becomes `p and 0 <= i <
n and q`. Conjuncts that chain one after another are one message and one
chain: `a < b and b < c and c < d` becomes `a < b < c < d`, and `0 <= i <
n and n <= m` becomes `0 <= i < n <= m`. A conjunct in parentheses is not
joined. The message is reported from the first conjunct it joins to the
last.

The fix keeps the meaning and the guards. `a < b and b <= c` is `a < b <=
c` by definition, with `b` one expression, evaluated where its first copy
was; in the chain, as in the `and`, `b <= c` is guarded by `a < b`. A
comparison written the other way round, such as `b > a` for `a < b`, means
the same, and its operands are evaluated where they were. In a longer run,
`p and a < b <= c and q` is `p and a < b and b <= c and q`, in which each
conjunct has the same guards as before. The operands keep their text, in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes), and
there is no fix where a comment is within the conjuncts, which the chain
would lose; the message then suggests the chain.

Fren has no ranges, so a chained comparison is how it writes Clippy's
`(lo..hi).contains(&x)`: this is Clippy's `manual_range_contains`, in
`style`, which suggests `contains` for `x >= lo && x < hi`.
`lint::chainable_comparison` states when two conjuncts chain, and which of
them the fix writes the other way round:

```fren
pub comp chainable_comparison {
    in left_ascending?   -- the left conjunct orders with `<` and `<=`, rather than `>` and `>=`
    in right_ascending?
    in left_single?      -- it is one comparison, rather than a chain
    in right_single?
    in last_first?       -- the left's last operand is written the same as the right's first
    in first_last?       -- the left's first as the right's last
    in first_first?
    in last_last?
    pub det out fires?
    pub det out flip_left?   -- the fix writes the left conjunct the other way round
    pub det out flip_right?

    -- Each way to write the conjuncts: as written, the left the other way
    -- round, the right, or both.
    ensure rule: fires? iff (((left_ascending? iff right_ascending?) and last_first? and not first_last?)
        or (left_single? and not (left_ascending? iff right_ascending?) and first_first? and not last_last?)
        or (right_single? and not (left_ascending? iff right_ascending?) and last_last? and not first_first?)
        or (left_single? and right_single? and (left_ascending? iff right_ascending?) and first_last?
        and not last_first?))
    ensure left: flip_left? iff ((left_single? and not (left_ascending? iff right_ascending?) and first_first?
        and not last_last?)
        or (left_single? and right_single? and (left_ascending? iff right_ascending?) and first_last?
        and not last_first?))
    ensure right: flip_right? iff ((right_single? and not (left_ascending? iff right_ascending?) and last_last?
        and not first_first?)
        or (left_single? and right_single? and (left_ascending? iff right_ascending?) and first_last?
        and not last_first?))

    expect both_or_neither: when fires? and (left_ascending? iff right_ascending?), flip_left? iff flip_right?
}
```

The refinements check each way of writing the conjuncts, and the joining
of a chained comparison:

```fren
set_option fren.lint.chainable_comparison "allow" in
pub comp chainable_written {
    in lo: Int
    in x: Int
    in hi: Int
    in m: Int
    pub det out kept? := lo <= x and x < hi
    pub det out left? := x >= lo and x < hi
    pub det out right? := x < hi and x > lo
    pub det out both? := x >= lo and hi > x
    pub det out longer? := lo < x and x < hi and hi < m
    pub det out joined? := lo <= x < hi and hi <= m
}

pub comp chainable_fixed {
    in lo: Int
    in x: Int
    in hi: Int
    in m: Int
    pub det out kept? := lo <= x < hi
    pub det out left? := lo <= x < hi
    pub det out right? := hi > x > lo
    pub det out both? := lo <= x < hi
    pub det out longer? := lo < x < hi < m
    pub det out joined? := lo <= x < hi <= m
}

refine chainable_sound: chainable_fixed refines chainable_written
refine chainable_complete: chainable_written refines chainable_fixed
```
