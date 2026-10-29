# Pattern tests written out


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
[`chainable_comparison`](Comparisons.md#chained-comparisons) reads a run of `and`, through
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

## Reading the operands

The lint reads each operand in two steps. The first reads its syntax and
text into a *shape*, `lint::Shape`: a comparison, with `=` or `!=`, whose
two sides are each read as a `lint::Literal`, a pattern test, possibly
negated, whose alternatives are read as `lint::Alt`s where each can be, or
anything else. A `Literal` is what a side's text says: a decimal integer
literal, possibly negated, by its value; a string literal with no `"`
within it, by its text; a variant without a payload, by the last segment
of its name; and otherwise `Other`, which a variable, a constant, a
computed value, `true` and `false` are. Only an atom or a negation is read
as anything but `Other`, so `1 + 1` is not a value. The second step,
`lint::reading`, decides from the shape alone whether the operand is in a
run, and with what: the expression it tests, as written, the alternatives
it gives the fix, in order, and whether it is an equation, of which a run
needs one. `lint::value_alt` is the alternative that writes a value:

```fren
pub mod lint

-- A value as written: a decimal integer literal, a string literal with no
-- `"` within it, a variant without a payload, by its name's last segment,
-- or anything else.
pub enum Literal { Decimal(Int), Quoted(String), Variant(String), Other }

-- A bound of a range of integers, `Open` where there is none.
pub enum Bound { Open, At(Int) }

-- An alternative: the integers between two bounds, as `Ints(At(k), At(k))`
-- for the literal `k`, a string literal, or a variant, by its name.
pub enum Alt { Ints(Bound, Bound), Text(String), Variant(String) }

-- A side of a comparison: its text, as written, and its value.
pub struct Side { text: String, value: Literal }

-- `left = right` if `equal?`, else `left != right`, where `nat?` says that
-- the operands are `Nat`s.
pub struct ComparisonShape { equal?, nat?, left: Side, right: Side }

-- `scrutinee is P`, or `not scrutinee is P` if `negated?`, with `P`'s
-- alternatives, in order, where each is one that the lint reads.
pub struct TestShape { negated?, scrutinee: String, alts: Option<Seq<Alt>> }

pub enum Shape { Comparison(ComparisonShape), Test(TestShape), Other }

-- An operand in a run: the expression it tests, as written, the
-- alternatives it gives the fix, and whether it is an equation.
pub struct Reading { scrutinee: String, alts: Seq<Alt>, equation? }

-- The alternative that writes the value, if there is one: a negative
-- literal is not one where the operands are `Nat`s.
pub fn value_alt(v: Literal, nat?): Option<Alt> := match v {
    Literal::Decimal(k) => if nat? and k < 0 then None else Some(Alt::Ints(Bound::At(k), Bound::At(k))),
    Literal::Quoted(t) => Some(Alt::Text(t)),
    Literal::Variant(n) => Some(Alt::Variant(n)),
    Literal::Other => None,
}

-- An equation, or a disequation, with exactly one side a value.
fn comparison_reading(c: ComparisonShape): Option<Reading> := match value_alt(c.left.value, c.nat?), value_alt(c.right.value, c.nat?) {
    None, Some(a) => Some(Reading { scrutinee := c.left.text, alts := [a], equation? := true }),
    Some(a), None => Some(Reading { scrutinee := c.right.text, alts := [a], equation? := true }),
    _, _ => None,
}

-- A pattern test, or its negation, whose alternatives are read.
fn test_reading(t: TestShape): Option<Reading> := match t.alts {
    Some(q) => Some(Reading { scrutinee := t.scrutinee, alts := q, equation? := false }),
    None => None,
}

-- An operand of a run of `or`, or of `and` if `conj?`: an equation for `or`
-- and a disequation for `and`, or a pattern test for `or` and its negation
-- for `and`.
pub fn reading(s: Shape, conj?): Option<Reading> := match s {
    Shape::Comparison(c) if c.equal? != conj? => comparison_reading(c),
    Shape::Test(t) if t.negated? = conj? => test_reading(t),
    _ => None,
}

pub proc read_operand(shape: Shape, conj?, read: Reading): (det reads?) {
    ensure rule: reads? iff reading(shape, conj?) = Some(read)

    expect no_value: when shape is Shape::Comparison(c) and c.left.value = Literal::Other
        and c.right.value = Literal::Other, not reads?
    expect two_values: when shape is Shape::Comparison(c) and c.left.value != Literal::Other
        and c.right.value != Literal::Other and not c.nat?, not reads?
}
```

`lint::read_operand` states that `read` is how the lint reads the
operand. It is bound to the lint's own decision, which both front ends
make, from the shape that they read from the syntax tree and the text.

## Disjoint alternatives

`lint::alts_disjoint?` is the test of two alternatives, and
`lint::disjoint_alternatives` states that two disjoint alternatives match
no value in common, for every value, and that a literal, as an
alternative, matches its own value alone:

```fren
-- A value an alternative may match: an integer, a string, or a variant.
pub enum Value { Number(Int), Word(String), Named(String) }

-- No integer is at most `hi` and at least `lo`.
fn bound_below?(hi: Bound, lo: Bound) := match hi, lo {
    Bound::At(h), Bound::At(l) => h < l,
    _, _ => false,
}

-- The alternatives match no value in common, as their text shows.
fn alts_disjoint?(a: Alt, b: Alt) := match a, b {
    Alt::Ints(l1, h1), Alt::Ints(l2, h2) => bound_below?(h1, l2) or bound_below?(h2, l1),
    Alt::Text(s), Alt::Text(t) => s != t and not s.contains?("\\") and not t.contains?("\\"),
    Alt::Variant(v), Alt::Variant(w) => v != w,
    _, _ => false,
}

-- `v` is at least `lo` and at most `hi`.
fn bound_within?(lo: Bound, hi: Bound, v: Int) :=
    (match lo { Bound::At(l) => l <= v, Bound::Open => true })
    and (match hi { Bound::At(h) => v <= h, Bound::Open => true })

-- The alternative matches the value, where a string literal's text is its
-- value, as it is without escape sequences.
fn alt_matches?(a: Alt, v: Value) := match a, v {
    Alt::Ints(lo, hi), Value::Number(k) => bound_within?(lo, hi, k),
    Alt::Text(s), Value::Word(w) => s = w,
    Alt::Variant(n), Value::Named(m) => n = m,
    _, _ => false,
}

pub proc disjoint_alternatives(a: Alt, b: Alt, v: Value) {
    expect apart: when alts_disjoint?(a, b), not (alt_matches?(a, v) and alt_matches?(b, v))
    expect symmetric: alts_disjoint?(a, b) iff alts_disjoint?(b, a)
    expect literal: when a is Alt::Ints(Bound::At(k), Bound::At(m)) and k = m,
        alt_matches?(a, v) iff v = Value::Number(k)
}
```

## Runs

`lint::manual_pattern_test_runs` states the lint over the operands of a
whole run of `or`, or of `and`, in order, each by its shape: it reports
`run` exactly when that is a longest run of adjacent operands that
`reading` reads as tests of one expression, written the same, on which
it fires. It fires on a run of two or more operands, of which one is an
equation, not in a chain that `membership_chain` reads, whose
alternatives, in order, are disjoint two by two. Each `forall` is over any
number of operands and alternatives, so the procedure is outside the
decidable core; its implementation is proved in Lean of the lint's code,
for every list of operands:

```fren
-- The positions of a run's first and last operands.
pub struct Span { first: Int, last: Int }

-- How the operand at position `i` is read, if there is one there.
fn reading_at(operands: Seq<Shape>, conj?, i: Int): Option<Reading> :=
    if 0 <= i < operands.len then reading(operands[i], conj?) else None

-- The operand at position `i` is read as a test of the expression written `x`.
fn tests_at?(operands: Seq<Shape>, conj?, i: Int, x: String) := match reading_at(operands, conj?, i) {
    Some(r) => r.scrutinee = x,
    None => false,
}

-- The alternatives that the operand at position `i` gives the fix.
fn alts_at(operands: Seq<Shape>, conj?, i: Int): Seq<Alt> := match reading_at(operands, conj?, i) {
    Some(r) => r.alts,
    None => [],
}

-- The operand at position `i` is an equation, or a disequation for `and`.
fn equation_at?(operands: Seq<Shape>, conj?, i: Int) := match reading_at(operands, conj?, i) {
    Some(r) => r.equation?,
    None => false,
}

-- `s` is a longest run of adjacent operands read as tests of one expression.
set_option fren.lint.undecidable "allow" in
fn longest_run?(operands: Seq<Shape>, conj?, s: Span) := exists (x: String),
    s.first <= s.last
    and (forall (i: Int), when s.first <= i <= s.last, tests_at?(operands, conj?, i, x))
    and not tests_at?(operands, conj?, s.first - 1, x)
    and not tests_at?(operands, conj?, s.last + 1, x)

-- The lint fires on the run `s`: the `k`th alternative of the operand at
-- `i` comes before the `l`th of the operand at `j`, and each two are
-- disjoint.
set_option fren.lint.undecidable "allow" in
fn run_fires?(operands: Seq<Shape>, conj?, chain?, s: Span) :=
    s.first < s.last and not chain?
    and (exists (i: Int), s.first <= i <= s.last and equation_at?(operands, conj?, i))
    and (forall (i j k l: Int), when s.first <= i <= j <= s.last and (i < j or k < l)
    and 0 <= k < alts_at(operands, conj?, i).len and 0 <= l < alts_at(operands, conj?, j).len,
    alts_disjoint?(alts_at(operands, conj?, i)[k], alts_at(operands, conj?, j)[l]))

set_option fren.lint.undecidable "allow" in
pub proc manual_pattern_test_runs(
    operands: Seq<Shape>,    -- the operands of the run of `or`, or of `and`, in order
    conj?,                   -- it is a run of `and`
    chain?,                  -- `membership_chain` reads the chain the run is in
    run: Span,               -- a run of the operands
): (det reported?) {
    ensure rule: reported? iff longest_run?(operands, conj?, run) and run_fires?(operands, conj?, chain?, run)
}
```

`lint::manual_pattern_test` is the decision on one run, from its
alternatives, in order, and its numbers of operands and of equations. Its
quantifiers range over the positions of eight alternatives, which keeps it
in the decidable core, so that `decide` checks its implementation over
every run of eight alternatives or fewer:

```fren
-- A position in the alternatives of a run.
pub type AltPosition = position: Int where invariant: position is 0..=7

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

## Keeping the meaning

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

