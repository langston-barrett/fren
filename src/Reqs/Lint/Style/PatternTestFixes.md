# Fixes of pattern tests written out


The fix of [`manual_pattern_test`](PatternTests.md), related to what the
lint reads and decides.

## The fix of a run

`lint::manual_pattern_test_fix_alts` states which alternatives the lint
writes in the fix of a run whose operands it reads: `n_operands` operands'
alternatives, one for each operand of the run, and those of the `q`th,
`alts`, are the alternatives of its reading, in order. The lint computes
that list, operand by operand, in one function, which `fren fix` writes
with `x is` before it and ` | ` between the alternatives, each as its
operand writes it; the implementation binds that function, so no
alternative is dropped or moved. The texts are outside the model.

`lint::manual_pattern_test_refines` relates the runs to the [high-level
spec](PatternTests.md#what-it-does), at a value `w` of the expression. Each operand of
the run is the test `lint::run_test`, computed from its shape: an
equation is `Equals` of its value side's `literal_value`, and a pattern
test is `Is` of its alternatives as the language means them,
`patterns`, which match no value that their readings' `alt_pattern`s do
not (`read`). The `tests` are those of the run's operands, in order.
Where the run's operands are read, the `q`th test's alternatives in the
fix are, position by position, those that the lint writes for the `q`th
operand, each matching no value that its reading does not (`covered`);
the fix means what the run did (`same_meaning`, which
`manual_pattern_test_fix` states of any tests); and where the run fires,
as where it is reported, by the rule of `lint::manual_pattern_test_runs`,
no value matches two alternatives of the fix (`reachable`).

```fren
pub mod lint

-- The value that an equation's value side writes.
fn equation_value(c: ComparisonShape): Option<lang::Value> := match value_alt(c.left.value, c.nat?), value_alt(c.right.value, c.nat?) {
    None, Some(_) => literal_value(c.right.value),
    Some(_), None => literal_value(c.left.value),
    _, _ => None,
}

-- The operand `s` as the language means it, where `patterns` are its pattern
-- test's alternatives, as the language means them.
pub fn run_test(s: Shape, patterns: Seq<lang::Pattern>): RunTest := match s {
    Shape::Comparison(c) => match equation_value(c) {
        Some(v) => RunTest::Equals(v),
        None => RunTest::Is([]),
    },
    _ => RunTest::Is(patterns),
}

-- The alternatives that the lint writes in the fix of the run, of the
-- operand at position `run.first + q`, and how many operands they are of.
set_option fren.lint.undecidable "allow" in
pub proc manual_pattern_test_fix_alts(operands: Seq<Shape>, conj?, run: Span, q: Int): (
    det n_operands: Int,
    det alts: Seq<Alt>,
) {
    -- The run's operands are read.
    assume read: 0 <= run.first <= run.last
        and (forall (i: Int), when run.first <= i <= run.last, reading_at(operands, conj?, i) != None)
    assume position: 0 <= q <= run.last - run.first

    out n_operands := run.last - run.first + 1
    out alts := alts_at(operands, conj?, run.first + q)
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc manual_pattern_test_refines(
    operands: Seq<Shape>,                -- the operands of the run of `or`, or of `and`, in order
    chain: Seq<Shape>,                   -- the operands of the chain the run is in
    conj?,                               -- it is a run of `and`
    run: Span,                           -- a run of the operands
    patterns: Seq<Seq<lang::Pattern>>,   -- each operand's pattern test's alternatives, as the language means them
    tests: Seq<RunTest>,                 -- the tests of the run's operands, in order
    w: lang::Value,                      -- a value of the expression
) {
    -- A pattern test's alternatives are its readings', each matching no value
    -- that its reading's pattern does not.
    assume read: forall (i: Int), when run.first <= i <= run.last and operands[i] is Shape::Test(_),
        patterns[i].len = alts_at(operands, conj?, i).len
        and (forall (k: Int), when 0 <= k < patterns[i].len and lang::matches_value?(patterns[i][k], w),
        lang::matches_value?(alt_pattern(alts_at(operands, conj?, i)[k]), w))
    assume operands_tests: tests.len = run.last - run.first + 1
        and (forall (i: Int), when 0 <= i < tests.len, tests[i] = run_test(operands[run.first + i], patterns[run.first + i]))

    -- The fix's alternatives are, position by position, those that the lint
    -- writes, each matching no value that its reading does not.
    ensure covered: when (forall (i: Int), when run.first <= i <= run.last, reading_at(operands, conj?, i) != None),
        forall (q: Int), when 0 <= q < tests.len,
        fix_alternatives(tests[q]).len = alts_at(operands, conj?, run.first + q).len
        and (forall (k: Int), when 0 <= k < fix_alternatives(tests[q]).len and lang::matches_value?(fix_alternatives(tests[q])[k], w),
        lang::matches_value?(alt_pattern(alts_at(operands, conj?, run.first + q)[k]), w))
    ensure same_meaning: fix_holds?(tests, w) iff run_holds?(tests, w)
    -- Where the run's operands are read and it fires, as where it is
    -- reported, no value matches two alternatives of the fix.
    ensure reachable: when (forall (i: Int), when run.first <= i <= run.last, reading_at(operands, conj?, i) != None)
        and run_fires?(operands, conj?, chain, run),
        forall (i j k l: Int), when 0 <= i < tests.len and i <= j < tests.len
        and 0 <= k < fix_alternatives(tests[i]).len and 0 <= l < fix_alternatives(tests[j]).len and (i < j or k < l),
        not (lang::matches_value?(fix_alternatives(tests[i])[k], w) and lang::matches_value?(fix_alternatives(tests[j])[l], w))
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

