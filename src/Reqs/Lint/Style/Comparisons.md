# Pattern tests and chained comparisons

The lints of the `style` group that write a [pattern
test](../../Lang/Expressions.md#pattern-tests) or a [chained
comparison](../../Lang/Expressions.md#chained-comparisons) more clearly.

## Pattern tests

A [pattern test](../../Lang/Expressions.md#pattern-tests), `e is P`, is how
Fren tests a value against several alternatives, as in `status is 429 |
503`. The same test can constrain a [subset
type](../../Lang/SubsetTypes.md), as in
`type Status = n: Nat where range: n is 100..=599`.
A range or a payload extends the test without rewriting, as in
`status is 429 | 500..=599`. Its meaning is a disjunction of equations
and comparisons, which the solver decides without the theory of sets that
a membership such as `status in {429, 503}` brings in. So a test of one
value is an equation, and a test of several is a pattern test:
[`manual_pattern_test`](#pattern-tests-written-out) writes a disjunction of
equations as one.

`is_equality` fires on `e is P` where `P` is one alternative, a variant
without a payload, `true`, `false`, a string literal or an integer literal,
and is fixable: `x is E::A` becomes `x = E::A`, and `n is -1` becomes `n =
-1`, with the alternative written as `P` writes it. A pattern of two or more
alternatives, as in `x is E::A | E::B` or `n is 0 | 1`, is left as it is,
and so is a range of one value, such as `3..=3`, a literal written otherwise
than its value, such as `0x10`, and a pattern with a payload, such as `x is
E::B(_)`. It does not fire where
[`irrefutable_is`](../Suspicious.md#pattern-tests) does, since the test is
then always `true`, however it is written. `e` keeps its text, in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes); an
equation binds as a pattern test does, as a comparison, so the fix needs no
parentheses that the test does not. `not x is E::A` becomes `not x =
E::A`, and `b? is true` becomes `b? = true`, which
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions) then fixes
to `x != E::A` and `b?`. A variant without a payload, or a literal, matches
its own value alone, so the equation holds exactly where the test does.
`e` is evaluated where it was, and the alternative guards nothing, so the
fix keeps the guards.
[`match_like_membership`](../Style.md#matches-that-are-memberships)
writes a pattern test only where this lint would not fire on it, and
`manual_pattern_test` writes one of two or more alternatives, so the lints
never undo each other.

Clippy's nearest lint, `equatable_if_let`, is in its `nursery` group, but
that group is about a lint's maturity rather than a judgment of style. It
too rewrites only a pattern of one alternative, `if let A = x` as `if x ==
A`: Clippy never suggests `[A, B].contains(&x)` for `matches!(x, A | B)`.
`style`, and so `warn`, fits here: there should be one way to write each
test, and Fren's other lints already write a test of one value with `=`.
`lint::is_equality` states when it fires:

```fren
pub mod lint

pub proc is_equality(
    n_alternatives: Nat,     -- the alternatives of the pattern
    equatable?,              -- each is a variant without a payload or a literal
    irrefutable?,            -- `irrefutable_is` fires on the test
): (det fires?) {
    ensure rule: fires? iff (n_alternatives = 1 and equatable? and not irrefutable?)

    expect several_stay: when n_alternatives >= 2, not fires?
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
pub proc membership_test_written(s: Shade, n: Int): (
    det tinted?,
    det shaded?,
    det light?,
    det untinted?,
    det small?,
    det digit?,
    det clear?,
    det positive?,
) {
    out tinted? := match s { Shade::Tinted(_) => true, _ => false }
    out shaded? := match s { Shade::Light => false, Shade::Dark | Shade::Tinted(_) => true }
    out light? := match s { Shade::Light => true, _ => false }
    out untinted? := match s { Shade::Tinted(_) => false, _ => true }
    out small? := match n { 0 | 1 => true, _ => false }
    out digit? := match n { 0..=9 => true, _ => false }
    out clear? := match s { Shade::Tinted(0) => true, _ => false }
    out positive? := match n { ..=0 => false, _ => true }
}

pub proc membership_test_fixed(s: Shade, n: Int): (
    det tinted?,
    det shaded?,
    det light?,
    det untinted?,
    det small?,
    det digit?,
    det clear?,
    det positive?,
) {
    out tinted? := s is Shade::Tinted(_)
    out shaded? := s != Shade::Light
    out light? := s = Shade::Light
    out untinted? := not s is Shade::Tinted(_)
    out small? := n is 0 | 1
    out digit? := n is 0..=9
    out clear? := s is Shade::Tinted(0)
    out positive? := not n is ..=0
}

expect membership_test_sound(s: lint::Shade, n: Int) {
    use lint
    call concrete := membership_test_fixed(s, n)
    refines concrete membership_test_written(s, n)
}
expect membership_test_complete(s: lint::Shade, n: Int) {
    use lint
    call concrete := membership_test_written(s, n)
    refines concrete membership_test_fixed(s, n)
}
```

The refinements check the fixes of `is_equality`:

```fren
set_option fren.lint.is_equality "allow" in
pub proc is_equality_written(s: Shade, n: Int, b?): (
    det light?,
    det dark?,
    det zero?,
    det negative?,
    det set?,
) {
    out light? := s is Shade::Light
    out dark? := not s is Shade::Dark
    out zero? := n is 0
    out negative? := n is -1
    out set? := b? is true
}

set_option fren.lint.nonminimal_bool "allow" in
pub proc is_equality_fixed(s: Shade, n: Int, b?): (
    det light?,
    det dark?,
    det zero?,
    det negative?,
    det set?,
) {
    out light? := s = Shade::Light
    out dark? := not s = Shade::Dark
    out zero? := n = 0
    out negative? := n = -1
    out set? := b? = true
}

expect is_equality_sound(s: lint::Shade, n: Int, b?) {
    use lint
    call concrete := is_equality_fixed(s, n, b?)
    refines concrete is_equality_written(s, n, b?)
}
expect is_equality_complete(s: lint::Shade, n: Int, b?) {
    use lint
    call concrete := is_equality_written(s, n, b?)
    refines concrete is_equality_fixed(s, n, b?)
}
```

## Pattern tests written out

`manual_pattern_test` fires on a run of two or more adjacent operands of
`or`, each an equation of one expression with a value that a pattern
writes, and is fixable: `x = a or x = b` becomes the [pattern
test](../../Lang/Expressions.md#pattern-tests) `x is a | b`. On its De
Morgan dual, a run of `and` of disequations, `x != a and x != b`, the fix
is `not x is a | b`. A value that a pattern writes is an integer literal in
decimal, possibly negated, a string literal without escape sequences, or a
variant without a payload: `status = 429 or status = 503` becomes `status is
429 | 503`, and `s = Shade::Light or s = Shade::Dark` becomes `s is
Shade::Light | Shade::Dark`. Either operand of an equation may be the value,
so `429 = status` is read as `status = 429`, and the other operand, the
expression tested, is [written the same](../../Lint.md#written-the-same) in
each equation of the run. A variable, a constant or a computed value is not
such a value, and neither are `true` and `false`, whose equations
[`bool_equality`](../Pedantic.md#boolean-equality) reports, nor a negative
literal where the operands are `Nat`s, as an alternative that never matches
is an error (`F0318`).

A pattern test of the same expression in the run, or for `and` its
negation, joins it, and its alternatives join the fix, in order: `status =
429 or status is 500..=599` becomes `status is 429 | 500..=599`, and `n !=
0 and not n is 10..` becomes `not n is 0 | 10..`. Such a test is read where
each of its alternatives is an integer literal, a range whose bounds are
integer literals, a string literal, or a variant, with a payload or
without, whatever its payload's patterns are, as in
`Shade::Tinted(1..=3)`; one with `_`, `true`, `false` or a constant as a
bound is not read. A run has at least one equation: one of pattern tests
alone is left as it is. Each alternative of a pattern must be reachable (`F0318`), so the lint
fires only where each two alternatives of the fix are *disjoint*, as far as
their text shows: two ranges of integers, a literal being a range of one,
that share no integer, two string literals written differently, or two
variants of different names, which a pattern of one type never names twice
otherwise. So `x = 1 or x = 1` and `x is 0..=9 or x = 5` are left as they
are.

The run of `or`, or of `and`, is read as
[`chainable_comparison`](#chained-comparisons) reads a run of `and`, through
each left operand that is an `or` not in parentheses, and an operand may be
in parentheses itself, as in `(x = 1) or (x = 2)`. Other operands may come
before and after it: `p? or x = 1 or x = 2 or q?` fires at `x = 1 or x = 2`,
and becomes `p? or x is 1 | 2 or q?`. Each longest run of adjacent operands
of one expression is one message, reported from its first operand to its
last, and there is no fix where a comment is within them, which the pattern
test would lose; the message then suggests the test. The expression is
written as its first operand writes it, in parentheses where [fixes need
them](../../Lint.md#parentheses-in-fixes), and each alternative as the
operands write it. Where the whole run is in parentheses as an operand of
an operator, and the test needs none there, they go with it: `q != [] and
(q[0] = 1 or q[0] = 2)` becomes `q != [] and q[0] is 1 | 2`. Elsewhere they
stay, since they may belong to what the run is in, or be needed by what
follows it: `match (x = 1 or x = 2) { ... }` becomes `match (x is 1 | 2) {
... }`, as a scrutinee's `{` would otherwise follow the pattern, and `f(x
= 1 or x = 2)` becomes `f(x is 1 | 2)`.

It does not fire within a chain that
[`membership_chain`](../Pedantic.md#membership-chains) reads: three or more
equations, or disequations, of one expression on their left, through
parentheses, with a value that a pattern does not write, such as `x = 1 or
x = 2 or x = q`, which that lint writes as `x in {1, 2, q}`. This holds
whatever that lint's level, and where a later value indexes a sequence, on
which that lint does not fire either. Where every value is one that a
pattern writes, this lint reports the chain and `membership_chain` does
not, so the two never fire on the same chain.

The fix keeps the meaning: a literal or a variant without a payload, as a
pattern, matches its own value alone, so `x = a` holds exactly where the
pattern `a` matches `x`, and an or-pattern matches where one of its
alternatives does, so `x is a | b` holds exactly where `x = a or x = b`
does, and where `x = a or x is P` does; the dual is the negation of the
same, by De Morgan's law. It keeps the guards (see
[Expressions](../../Lang/Expressions.md#sequences)): in the run, each
operand is guarded by those before it, so `x = b` is evaluated only where
`x = a` is `false`, and the fix evaluates `x` once, where the first operand
did, under the guards of the operands before the run, as the run's first
operand was. The values and the alternatives are literals and variants,
which are defined everywhere. The expression itself may index a sequence,
as in `q[0] = 1 or q[0] = 2`: it is written the same in each operand, so a
later copy is defined exactly where the first is, and gives no obligation
that the first does not, so evaluating it once changes neither where the
test is defined nor its meaning. So, unlike `membership_chain`, which
evaluates each value where the chain is, the lint fires whatever the
expression and its operands before the run index.

Clippy's nearest lint, `manual_pattern_char_comparison`, is in `style`: it
writes `c == 'a' || c == 'b'` as the pattern `['a', 'b']`. A Fren pattern
test is Rust's `matches!(x, A | B)`, and Clippy never pushes it toward a
membership such as `[A, B].contains(&x)`. This lint is in `style` too, and
`warn`: there should be one way to write each test, and a pattern test is
the one that ranges and payloads extend.

`lint::manual_pattern_test` models the run by its alternatives, in order,
each a range of integers between two bounds, a string literal by its text,
or a variant by its name, and states when it fires. `lint::alts_disjoint?`
is the test of two alternatives, and `lint::disjoint_alternatives` states
that two disjoint alternatives match no value in common, for every value:

```fren
-- A bound of a range of integers, `Open` where there is none.
pub enum Bound { Open, At(Int) }

-- An alternative: the integers between two bounds, as `Ints(At(k), At(k))`
-- for the literal `k`, a string literal, or a variant, by its name.
pub enum Alt { Ints(Bound, Bound), Text(String), Variant(String) }

-- A value an alternative may match: an integer, a string, or a variant.
pub enum Value { Number(Int), Word(String), Named(String) }

-- A position in the alternatives of a run.
pub type AltPosition = subset_value: Int where invariant: subset_value is 0..=7

-- No integer is at most `hi` and at least `lo`.
fn bound_below?(hi: Bound, lo: Bound) := match hi {
    Bound::At(h) => match lo { Bound::At(l) => h < l, Bound::Open => false },
    Bound::Open => false,
}

-- The alternatives match no value in common, as their text shows.
fn alts_disjoint?(a: Alt, b: Alt) := match a {
    Alt::Ints(l1, h1) => match b { Alt::Ints(l2, h2) => bound_below?(h1, l2) or bound_below?(h2, l1), _ => false },
    Alt::Text(s) => match b { Alt::Text(t) => s != t and not s.contains?("\\") and not t.contains?("\\"), _ => false },
    Alt::Variant(v) => match b { Alt::Variant(w) => v != w, _ => false },
}

-- `v` is at least `lo` and at most `hi`.
fn bound_within?(lo: Bound, hi: Bound, v: Int) :=
    (match lo { Bound::At(l) => l <= v, Bound::Open => true })
    and (match hi { Bound::At(h) => v <= h, Bound::Open => true })

-- The alternative matches the value, where a string literal's text is its
-- value, as it is without escape sequences.
fn alt_matches?(a: Alt, v: Value) := match a {
    Alt::Ints(lo, hi) => match v { Value::Number(k) => bound_within?(lo, hi, k), _ => false },
    Alt::Text(s) => match v { Value::Word(w) => s = w, _ => false },
    Alt::Variant(n) => match v { Value::Named(m) => n = m, _ => false },
}

pub proc disjoint_alternatives(a: Alt, b: Alt, v: Value) {
    expect apart: when alts_disjoint?(a, b), not (alt_matches?(a, v) and alt_matches?(b, v))
    expect symmetric: alts_disjoint?(a, b) iff alts_disjoint?(b, a)
}

pub proc manual_pattern_test(
    alts: Seq<Alt>,          -- the alternatives of the fix, in order: each equation's value, and each test's alternatives
    n_operands: Nat,         -- the operands of the run
    n_equations: Nat,        -- those that are equations, or disequations for `and`
    chain?,                  -- `membership_chain` reads the chain the run is in
): (det fires?) {
    -- The model's quantifiers range over the positions of eight alternatives.
    assume short: alts.len <= 8

    ensure rule: fires? iff (n_operands >= 2 and n_equations >= 1 and not chain?
        and (forall (i: AltPosition) (j: AltPosition), when i < j < alts.len, alts_disjoint?(alts[i], alts[j])))

    expect repeated: when alts = [Alt::Variant("A"), Alt::Variant("A")], not fires?
    expect overlapping: when alts = [Alt::Ints(Bound::At(0), Bound::At(9)), Alt::Ints(Bound::At(5), Bound::At(5))], not fires?
}
```

`lint::manual_pattern_test_keeps_meaning` states the fix as laws (see
[Fixing lints](../../Lint.md#fixing-lints)), of an integer, with the value
on either side, with a range, within a longer run, and of the dual:

```fren
set_option fren.lint.manual_pattern_test "expect" in
pub proc manual_pattern_test_keeps_meaning(x: Int, p?) {
    expect two: (x = 429 or x = 503) iff x is 429 | 503
    expect reversed: (429 = x or x = 503) iff x is 429 | 503
    expect range: (x = 429 or x is 500..=599) iff x is 429 | 500..=599
    expect within: (p? or x = 1 or x = 2) iff (p? or x is 1 | 2)
    expect dual: (x != 429 and x != 503) iff not x is 429 | 503
    expect dual_range: (x != 0 and not x is 10..) iff not x is 0 | 10..
}
```

The refinements check the fixes of a variant, a string, a negative literal,
and an expression that indexes a sequence:

```fren
set_option fren.lint.manual_pattern_test "allow" in
pub proc manual_pattern_test_written(s: Shade, n: Int, t: String, q: Seq<Int>): (
    det plain?,
    det tinted?,
    det dim?,
    det word?,
    det sign?,
    det first?,
) {
    out plain? := s = Shade::Light or s = Shade::Dark
    out tinted? := s = Shade::Light or s is Shade::Tinted(_)
    out dim? := s is Shade::Tinted(1..=3) or s = Shade::Dark
    out word? := t = "a" or "b" = t
    out sign? := n = -1 or n = 1
    out first? := q != [] and (q[0] = 1 or q[0] = 2)
}

pub proc manual_pattern_test_fixed(s: Shade, n: Int, t: String, q: Seq<Int>): (
    det plain?,
    det tinted?,
    det dim?,
    det word?,
    det sign?,
    det first?,
) {
    out plain? := s is Shade::Light | Shade::Dark
    out tinted? := s is Shade::Light | Shade::Tinted(_)
    out dim? := s is Shade::Tinted(1..=3) | Shade::Dark
    out word? := t is "a" | "b"
    out sign? := n is -1 | 1
    out first? := q != [] and q[0] is 1 | 2
}

expect manual_pattern_test_sound(s: lint::Shade, n: Int, t: String, q: Seq<Int>) {
    use lint
    call concrete := manual_pattern_test_fixed(s, n, t, q)
    refines concrete manual_pattern_test_written(s, n, t, q)
}
expect manual_pattern_test_complete(s: lint::Shade, n: Int, t: String, q: Seq<Int>) {
    use lint
    call concrete := manual_pattern_test_written(s, n, t, q)
    refines concrete manual_pattern_test_fixed(s, n, t, q)
}
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
pub proc chainable_comparison(
    left_ascending?,     -- the left conjunct orders with `<` and `<=`, rather than `>` and `>=`
    right_ascending?,
    left_single?,        -- it is one comparison, rather than a chain
    right_single?,
    last_first?,         -- the left's last operand is written the same as the right's first
    first_last?,         -- the left's first as the right's last
    first_first?,
    last_last?,
): (
    det fires?,
    det flip_left?,          -- the fix writes the left conjunct the other way round
    det flip_right?,
) {
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
pub proc chainable_written(lo: Int, x: Int, hi: Int, m: Int): (
    det kept?,
    det left?,
    det right?,
    det both?,
    det longer?,
    det joined?,
) {
    out kept? := lo <= x and x < hi
    out left? := x >= lo and x < hi
    out right? := x < hi and x > lo
    out both? := x >= lo and hi > x
    out longer? := lo < x and x < hi and hi < m
    out joined? := lo <= x < hi and hi <= m
}

pub proc chainable_fixed(lo: Int, x: Int, hi: Int, m: Int): (
    det kept?,
    det left?,
    det right?,
    det both?,
    det longer?,
    det joined?,
) {
    out kept? := lo <= x < hi
    out left? := lo <= x < hi
    out right? := hi > x > lo
    out both? := lo <= x < hi
    out longer? := lo < x < hi < m
    out joined? := lo <= x < hi <= m
}

expect chainable_sound(lo: Int, x: Int, hi: Int, m: Int) {
    call concrete := chainable_fixed(lo, x, hi, m)
    refines concrete chainable_written(lo, x, hi, m)
}
expect chainable_complete(lo: Int, x: Int, hi: Int, m: Int) {
    call concrete := chainable_written(lo, x, hi, m)
    refines concrete chainable_fixed(lo, x, hi, m)
}
```
