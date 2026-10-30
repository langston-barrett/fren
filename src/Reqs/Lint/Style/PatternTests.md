# Pattern tests written out

`manual_pattern_test` writes a run of equations of one expression with
values that patterns write, such as `x = 429 or x = 503`, as one [pattern
test](../../Lang/Expressions.md#pattern-tests), `x is 429 | 503`, which
means the same, and the dual, `x != 429 and x != 503`, as `not x is 429 |
503`.

## What it does

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

What the fix means is stated over the language's own [pattern
matching](../../Lang/Semantics.md#pattern-matching), `lang::matches_value?`
over the values and patterns of the dynamic semantics. An operand of the
run, as the language means it, is a `lint::RunTest`: `x = a` or `a = x`,
where `a` has the value `v`, which holds where `x`'s value is `v`; or `x
is A₁ | … | Aₖ`, by its alternatives, which holds where one of them
matches `x`'s value. The fix writes `x is` and then each operand's
alternatives, in order: for an equation, `a` as a pattern, which is the
literal pattern of its value, `Literal(v)`, which matches `v` alone, and
for a pattern test, its own. `lint::manual_pattern_test_fix` states that
the fix holds exactly where the run did, at every value `w` of `x`: some
alternative of the fix matches `w` exactly where some operand holds. The
dual is its negation, by De Morgan's law: `not x is …` holds exactly
where each disequation and negated test of the run does. Its quantifiers
range over any number of operands and alternatives, so it is checked by
random testing:

```fren
pub mod lint

-- An operand of a run of `or`, as the language means it: `x = a`, where
-- `a` has the value `v`, or `x is A₁ | … | Aₖ`, by its alternatives.
pub enum RunTest { Equals(lang::Value), Is(Seq<lang::Pattern>) }

-- The operand holds where `x` has the value `w`.
set_option fren.lint.undecidable "allow" in
pub fn test_holds?(t: RunTest, w: lang::Value) := match t {
    RunTest::Equals(v) => w = v,
    RunTest::Is(alts) => (exists (k: Int), 0 <= k < alts.len and lang::matches_value?(alts[k], w)),
}

-- The operand's alternatives in the fix: `a` as a pattern, or the test's own.
pub fn fix_alternatives(t: RunTest): Seq<lang::Pattern> := match t {
    RunTest::Equals(v) => [lang::Pattern::Literal(v)],
    RunTest::Is(alts) => alts,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc manual_pattern_test_fix(tests: Seq<RunTest>, w: lang::Value) {
    expect same_meaning: (exists (i k: Int), 0 <= i < tests.len and 0 <= k < fix_alternatives(tests[i]).len
        and lang::matches_value?(fix_alternatives(tests[i])[k], w))
        iff (exists (i: Int), 0 <= i < tests.len and test_holds?(tests[i], w))
}
```

## Reading the operands

The lint reads each operand in two steps. The first reads its syntax and
text into a *shape*, `lint::Shape`: a comparison, with `=` or `!=`, whose
two sides are each read as a `lint::Literal`, a pattern test, possibly
negated, whose alternatives are each read as a `lint::Alt`, where each
is one the lint reads, or anything else. An `Alt` is an integer literal
or a range whose bounds are integer literals, by its range, a literal
being the range of one integer, a string literal, by the text between
its quotes, or a variant, by its name, whatever its payload's patterns,
which the lint does not read. `lint::alt_pattern` is what an `Alt` means,
as a pattern of the [dynamic semantics](../../Lang/Semantics.md#patterns),
`lang::Pattern`: a variant's is `Variant(c, _)`, with `_` for its payload,
which may match more than the alternative does, so that each alternative
matches no value that its `alt_pattern` does not. An `Alt` is not a
second model of matching, as it has no matching of its own: the rules
below are stated over `lang::matches_value?` of its `alt_pattern`. It is
not recursive, unlike `lang::Pattern`, which keeps the checks over whole
runs of operands cheap. A `Literal`
is what a side's text says: a decimal integer literal, possibly negated,
by its value; a string literal with no `"` within it, by the text between
its quotes, which is its value where it has no escape sequences; a variant
without a payload, by its name, which the lint tells apart from the other
variants of its enumeration by its last segment; `true` or `false`; and
otherwise `Other`, which a
variable, a constant and a computed value are. Only an atom, a negation or
a Boolean literal is read as anything but `Other`, so `1 + 1` is not a
value. The second step, `lint::reading`, decides from the shape alone
whether the operand is in a run, and with what: the expression it tests,
by its [written form](../../Lint.md#written-the-same), the alternatives it
gives the fix, in order, and whether it is an equation, of which a run
needs one. `lint::value_alt` is the alternative that writes a value: none
for `true` and `false`, whose equations
[`bool_equality`](../Pedantic.md#boolean-equality) reports:

```fren
-- An alternative of a pattern as the lint reads it: the integers of a
-- range, a string literal, by the text between its quotes, or a variant,
-- by its name, whatever its payload.
pub enum Alt { Integers(lang::IntRange), Text(String), Variant(lang::Id) }

-- The alternative as a pattern: a range by its bounds, without them `_`,
-- and a variant with `_` for its payload.
pub fn alt_pattern(a: Alt): lang::Pattern := match a {
    Alt::Integers(r) => if r.bounded_below? and r.bounded_above? then lang::Pattern::Between(r.low, r.high)
        else if r.bounded_below? then lang::Pattern::AtLeast(r.low)
        else if r.bounded_above? then lang::Pattern::AtMost(r.high)
        else lang::Pattern::Wildcard,
    Alt::Text(t) => lang::Pattern::Literal(lang::Value::Text(t)),
    Alt::Variant(c) => lang::Pattern::Variant(c, lang::Pattern::Wildcard),
}

-- A value as written: a decimal integer literal, a string literal with no
-- `"` within it, by the text between its quotes, a variant without a
-- payload, by its name, `true` or `false`, or anything else.
pub enum Literal { Decimal(Int), Quoted(String), Variant(lang::Id), Truth(Bool), Other }

-- A side of a comparison: its written form, and its value.
pub struct Side { text: String, value: Literal }

-- `left = right` if `equal?`, else `left != right`, where `nat?` says that
-- the operands are `Nat`s.
pub struct ComparisonShape { equal?, nat?, left: Side, right: Side }

-- `scrutinee is P`, or `not scrutinee is P` if `negated?`, by the
-- scrutinee's written form, with `P`'s alternatives, in order, as the lint
-- reads them, where it reads each.
pub struct TestShape { negated?, scrutinee: String, alts: Option<Seq<Alt>> }

pub enum Shape { Comparison(ComparisonShape), Test(TestShape), Other }

-- An operand in a run: the expression it tests, by its written form, the
-- alternatives it gives the fix, and whether it is an equation.
pub struct Reading { scrutinee: String, alts: Seq<Alt>, equation? }

-- The integer `k` alone, as a range.
pub fn just(k: Int): lang::IntRange := lang::IntRange { bounded_below? := true, low := k, bounded_above? := true, high := k }

-- The alternative that writes the value, if there is one: a negative
-- literal is not one where the operands are `Nat`s.
pub fn value_alt(v: Literal, nat?): Option<Alt> := match v {
    Literal::Decimal(k) => if nat? and k < 0 then None else Some(Alt::Integers(just(k))),
    Literal::Quoted(t) => Some(Alt::Text(t)),
    Literal::Variant(c) => Some(Alt::Variant(c)),
    _ => None,
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

set_option fren.lint.undecidable "allow" in
pub proc read_operand(shape: Shape, conj?): (det reads?, det equation?) {
    ensure rule: reads? iff reading(shape, conj?) != None
    ensure equation: equation? iff (reading(shape, conj?) is Some(r) and r.equation?)

    expect no_value: when shape is Shape::Comparison(c) and c.left.value = Literal::Other
        and c.right.value = Literal::Other, not reads?
    -- Not where `nat?`: there a negative literal writes no alternative, so
    -- `0 = -1` is read as a test of `-1`.
    expect two_values: when shape is Shape::Comparison(c)
        and c.left.value is Literal::Decimal(_) | Literal::Quoted(_) | Literal::Variant(_)
        and c.right.value is Literal::Decimal(_) | Literal::Quoted(_) | Literal::Variant(_) and not c.nat?, not reads?
    expect tests_not_equations: when shape is Shape::Test(_), not equation?
}
```

`lint::read_operand` states whether the lint reads the operand into a
run, and as an equation. It is bound to the lint's own decision, which
both front ends make, from the shape that they read from the syntax tree
and the text; the expression and alternatives that the reading gives are
bound, with the runs, by `lint::manual_pattern_test_runs` below.

The fix writes each operand's alternatives as the operand writes them,
so they are those of the operands as the language means them
(`lint::RunTest`), and `manual_pattern_test_fix` applies to the fix. The
readings decide only whether the lint fires, by their disjointness below,
and each must match at least what its alternative does.
`lint::literal_value` is the value of a `Literal`, a variant without a
payload being `Constructed(c, Nil)`, and `lint::manual_pattern_test_reads`
states that the reading of an equation's value, by `value_alt`, matches
that value; a pattern test's alternatives are read by their text, which
the shape takes as read. That unfolds `matches_value?` twice, at a variant
and at its payload, more deeply than the solver does, so it is checked by
random testing:

```fren
-- The value that a literal writes, where it is one.
pub fn literal_value(v: Literal): Option<lang::Value> := match v {
    Literal::Decimal(k) => Some(lang::Value::Integer(k)),
    Literal::Quoted(t) => Some(lang::Value::Text(t)),
    Literal::Variant(c) => Some(lang::Value::Constructed(c, lang::Value::Nil)),
    Literal::Truth(b?) => Some(lang::truth(b?)),
    Literal::Other => None,
}

set_option fren.evidence "random" in
pub proc manual_pattern_test_reads(v: Literal, nat?) {
    expect value_matches: when value_alt(v, nat?) is Some(a) and literal_value(v) is Some(x),
        lang::matches_value?(alt_pattern(a), x)
}
```

## Disjoint alternatives

`lint::alts_disjoint?` is the test of two alternatives, from their text:
two ranges of integers that share no integer, two string literals written
differently without escape sequences, or two variants of different
names. A variant's payload is not read, so the test may find two
alternatives of one variant not disjoint where their payloads' patterns
are. `lint::disjoint_alternatives` states that the patterns of two
disjoint alternatives match no value in common, by the language's own
matching, for every value, and so do the alternatives, which match no
more than their patterns:

```fren
-- No integer is in both ranges, as their bounds show.
fn ranges_apart?(r: lang::IntRange, s: lang::IntRange) := (r.bounded_above? and s.bounded_below? and r.high < s.low)
    or (s.bounded_above? and r.bounded_below? and s.high < r.low)

-- The alternatives match no value in common, as their text shows.
pub fn alts_disjoint?(a: Alt, b: Alt) := match a, b {
    Alt::Integers(r), Alt::Integers(s) => ranges_apart?(r, s),
    Alt::Text(s), Alt::Text(t) => s != t and not s.contains?("\\") and not t.contains?("\\"),
    Alt::Variant(c), Alt::Variant(d) => c != d,
    _, _ => false,
}

pub proc disjoint_alternatives(a: Alt, b: Alt, v: lang::Value, c: lang::Id, k: Int) {
    expect apart: when alts_disjoint?(a, b),
        not (lang::matches_value?(alt_pattern(a), v) and lang::matches_value?(alt_pattern(b), v))
    expect symmetric: alts_disjoint?(a, b) iff alts_disjoint?(b, a)
    expect repeated: not alts_disjoint?(Alt::Variant(c), Alt::Variant(c))
    expect overlapping: when 0 <= k <= 9, not alts_disjoint?(Alt::Integers(lang::IntRange { bounded_below? := true,
        low := 0, bounded_above? := true, high := 9 }), Alt::Integers(just(k)))
}
```

## Runs

`lint::manual_pattern_test_runs` states the lint over the operands of a
whole run of `or`, or of `and`, in order, each by its shape: it reports
`run` exactly when that is a longest run of adjacent operands that
`reading` reads as tests of one expression, written the same, on which
it fires. It fires on a run of two or more operands, of which one is an
equation, whose alternatives, in order, are disjoint two by two, unless
`membership_chain` reads the chain it is in. That lint reads the chain's
operands through parentheses, which a run is not read through, so it is
read from their shapes too: `lint::membership_chain?` holds where there
are three or more of them, each an equation, or for `and` a disequation,
whose left operands are written the same, and one of whose right operands
is a value that no pattern writes, `Other`, whether or not a later one
indexes a sequence. Each `forall` is over any number of operands and
alternatives, so the procedure is outside the decidable core; its
implementation is proved in Lean of the lint's code, for every list of
operands and every number of alternatives, so no bounded version of the
decision is needed:

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

-- The operand is an equation, or for `and` a disequation, whose left
-- operand is written `x`.
fn chain_equation?(s: Shape, conj?, x: String) := match s {
    Shape::Comparison(c) => c.equal? != conj? and c.left.text = x,
    _ => false,
}

-- Its right operand is a value that no pattern writes.
fn unwritten?(s: Shape) := match s {
    Shape::Comparison(c) => c.right.value = Literal::Other,
    _ => false,
}

fn left_text(s: Shape): String := match s {
    Shape::Comparison(c) => c.left.text,
    _ => "",
}

-- `membership_chain` reads the chain whose operands, through parentheses,
-- are `chain`.
set_option fren.lint.undecidable "allow" in
pub fn membership_chain?(chain: Seq<Shape>, conj?) := chain.len >= 3
    and (forall (i: Int), when 0 <= i < chain.len, chain_equation?(chain[i], conj?, left_text(chain[0])))
    and (exists (i: Int), 0 <= i < chain.len and unwritten?(chain[i]))

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
fn run_fires?(operands: Seq<Shape>, conj?, chain: Seq<Shape>, s: Span) :=
    s.first < s.last and not membership_chain?(chain, conj?)
    and (exists (i: Int), s.first <= i <= s.last and equation_at?(operands, conj?, i))
    and (forall (i j k l: Int), when s.first <= i <= j <= s.last and (i < j or k < l)
    and 0 <= k < alts_at(operands, conj?, i).len and 0 <= l < alts_at(operands, conj?, j).len,
    alts_disjoint?(alts_at(operands, conj?, i)[k], alts_at(operands, conj?, j)[l]))

set_option fren.lint.undecidable "allow" in
pub proc manual_pattern_test_runs(
    operands: Seq<Shape>,    -- the operands of the run of `or`, or of `and`, in order
    chain: Seq<Shape>,       -- the operands of the chain the run is in, as `membership_chain` reads them
    conj?,                   -- it is a run of `and`
    run: Span,               -- a run of the operands
): (det reported?) {
    ensure rule: reported? iff longest_run?(operands, conj?, run) and run_fires?(operands, conj?, chain, run)
}
```

## Examples of the fix

`lint::manual_pattern_test_keeps_meaning` states examples of the fix as laws (see
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

