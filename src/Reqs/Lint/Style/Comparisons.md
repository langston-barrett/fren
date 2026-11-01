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
[`manual_pattern_test`](PatternTests.md) writes a disjunction of
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
never undo each other. It does not fire on the test of a [pattern
shorthand](../../Lang/SubsetTypes.md#the-pattern-shorthand), `type T = U is
P`, whose `e` is not written and which has no form with `=`.

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
    out tinted? := match s {
        Shade::Tinted(_) => true,
        _ => false,
    }
    out shaded? := match s {
        Shade::Light => false,
        Shade::Dark | Shade::Tinted(_) => true,
    }
    out light? := match s {
        Shade::Light => true,
        _ => false,
    }
    out untinted? := match s {
        Shade::Tinted(_) => false,
        _ => true,
    }
    out small? := match n {
        0 | 1 => true,
        _ => false,
    }
    out digit? := match n {
        0..=9 => true,
        _ => false,
    }
    out clear? := match s {
        Shade::Tinted(0) => true,
        _ => false,
    }
    out positive? := match n {
        ..=0 => false,
        _ => true,
    }
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
them the fix writes the other way round, over the conjuncts as written: a
`lint::Chain` is a comparison or a chained comparison, which orders one
way, as a chain must (see [Chained
comparisons](../../Lang/Expressions.md#chained-comparisons)): its first
operand, whether it orders ascending, with `<` and `<=`, or descending,
with `>` and `>=`, and then each operator, strict or not, with the operand
after it, each operand as written. `lint::oriented` is a conjunct as the
fix writes it: as it is, or, for a single comparison, the other way
round, with its operands swapped and its operator mirrored, so that `x >=
lo` is `lo <= x`. Two conjuncts, so written, chain where they order the
same way, the left's last operand is the right's first, and the chain's
first operand is not its last. Either conjunct may be written the other
way round only where it is one comparison:

```fren
-- An operator, strict (`<` or `>`) or not (`<=` or `>=`), and the operand
-- after it, as written.
pub struct Step { strict?, operand: String }

-- `first op x op y ...`, with `<` and `<=` if `ascending?`, else with `>`
-- and `>=`: a comparison if it has one step, else a chained comparison.
pub struct Chain { first: String, ascending?, steps: Seq<Step> }

pub fn last_operand(c: Chain): String := if c.steps = [] then c.first else c.steps[c.steps.len - 1].operand

-- A comparison the other way round: `b > a` for `a < b`.
pub fn reversed(c: Chain): Chain := Chain {
    first := last_operand(c),
    ascending? := not c.ascending?,
    steps := [
        Step {
            strict? := c.steps[0].strict?,
            operand := c.first,
        },
    ],
}

-- The conjunct as the fix writes it: the other way round, if `flip?`.
pub fn oriented(c: Chain, flip?): Chain := if flip? and c.steps != [] then reversed(c) else c

-- The conjuncts, as written, chain.
pub fn chains?(l: Chain, r: Chain) :=
    (l.ascending? iff r.ascending?) and last_operand(l) = r.first and l.first != last_operand(r)

-- The conjuncts chain with the left written the other way round if
-- `flip_left?`, and the right if `flip_right?`, each only if it is one
-- comparison.
pub fn chains_flipped?(l: Chain, r: Chain, flip_left?, flip_right?) :=
    (not flip_left? or l.steps.len = 1) and (not flip_right? or r.steps.len = 1)
    and chains?(oriented(l, flip_left?), oriented(r, flip_right?))

pub proc chainable_comparison(left: Chain, right: Chain): (
    det fires?,
    det flip_left?,          -- the fix writes the left conjunct the other way round
    det flip_right?,
) {
    assume comparisons: left.steps != [] and right.steps != []

    out fires? := exists (a? b?: Bool), chains_flipped?(left, right, a?, b?)
    out flip_left? := exists (b?: Bool), chains_flipped?(left, right, true, b?)
    out flip_right? := exists (a?: Bool), chains_flipped?(left, right, a?, true)

    -- At most one way of writing the conjuncts chains them, so the fix is
    -- the way that does.
    expect flips: when fires?, chains_flipped?(left, right, flip_left?, flip_right?)
    expect one_way: forall (a? b? c? d?: Bool), when chains_flipped?(left, right, a?, b?)
        and chains_flipped?(left, right, c?, d?), a? = c? and b? = d?
    expect both_or_neither: when fires? and (left.ascending? iff right.ascending?), flip_left? iff flip_right?
    -- A chain that earlier conjuncts joined is never written the other way round.
    expect joined_kept: when left.steps.len >= 2, not flip_left?
}
```

In a run, the lint joins each conjunct, in turn, to the chain of the
conjuncts before it that chain, as `lint::chainable_comparison` joins two
conjuncts, or else starts a new chain at it. A chain that joins two
conjuncts has two operators or more, so `joined_kept` says it is never
written the other way round, and the conjuncts before it keep their order.

The chain that the fix writes for two conjuncts is
`lint::chainable_joined`: the left as the fix writes it, and then each of
the right's operators, with the operand after it. That it keeps the
meaning is stated over the comparisons that the
[semantics](../../Lang/Semantics.md#derived-forms) reads in a chain: a
chained comparison is the `and` of its comparisons, from left to right,
and `b > a` is `a < b`, so each comparison is a `lint::Inequality`, of a
lower operand that is less than, or at most, an upper one. The joined
chain's comparisons are the left's and then the right's, as written:
`joined_inequalities` states it for conjuncts that chain as the fix
writes them, `chainable_joined` that the two conjuncts are then such, and
`turned` that a comparison written the other way round is the same
inequality. The solver decides `chainable_joined`'s expectations and
`turned`, for chains of any length. `joined_inequalities`'s evidence is
testing, since the solver does not always decide it in time: its index
ranges over the joined chain, so testing evaluates it at every position.
The implementation of `chainable_joined` is proved in Lean of the code's
join:

```fren
-- A comparison as the semantics reads it: `lower < upper` if `strict?`,
-- else `lower <= upper`.
pub struct Inequality { lower: String, strict?, upper: String }

-- The operand of `c` at the position `k`, from `0`.
pub fn chain_operand(c: Chain, k: Int): String := if k = 0 then c.first else c.steps[k - 1].operand

-- The inequality of `c` at the position `k`, from `0`: of its operands at
-- `k` and `k + 1`, the other way round if `c` orders descending.
pub fn inequality(c: Chain, k: Int): Inequality := if c.ascending?
    then Inequality {
        lower := chain_operand(c, k),
        strict? := c.steps[k].strict?,
        upper := chain_operand(c, k + 1),
    }
    else Inequality {
        lower := chain_operand(c, k + 1),
        strict? := c.steps[k].strict?,
        upper := chain_operand(c, k),
    }

-- The chain of `l` and then `r`, whose first operand is `l`'s last: `l`'s
-- operands, then `r`'s after its first.
set_option fren.lint.undecidable "allow" in
pub fn joined(l: Chain, r: Chain): Chain := { l with
    steps := l.steps ++ r.steps,
}

-- A comparison written the other way round is the same inequality.
expect turned(c: Chain) {
    expect turned: when c.steps.len = 1, inequality(reversed(c), 0) = inequality(c, 0)
}

-- The joined chain's inequalities are the left's and then the right's, for
-- conjuncts that chain as the fix writes them: the right orders as the left
-- does, and its first operand is the left's last.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect joined_inequalities(left: Chain, steps: Seq<Step>) {
    assume nonempty: left.steps != [] and steps != []

    let right: Chain := Chain {
        first := last_operand(left),
        ascending? := left.ascending?,
        steps,
    }
    let chain: Chain := joined(left, right)

    expect inequalities: chain.steps.len = left.steps.len + right.steps.len
        and (forall (k: Int), when 0 <= k < chain.steps.len, inequality(chain, k)
        = (if k < left.steps.len then inequality(left, k) else inequality(right, k - left.steps.len)))
}

set_option fren.lint.undecidable "allow" in
pub proc chainable_joined(left: Chain, right: Chain, flip_left?, flip_right?): (chain: Chain) {
    assume nonempty: left.steps != [] and right.steps != []
    assume chains: chains_flipped?(left, right, flip_left?, flip_right?)

    out chain := joined(oriented(left, flip_left?), oriented(right, flip_right?))

    -- The conjuncts, as the fix writes them, are those of
    -- `joined_inequalities`: the right orders as the left does, and its first
    -- operand is the left's last; each has as many comparisons as it is
    -- written with.
    expect follows: (oriented(right, flip_right?).ascending? iff oriented(left, flip_left?).ascending?)
        and oriented(right, flip_right?).first = last_operand(oriented(left, flip_left?))
    expect kept: oriented(left, flip_left?).steps.len = left.steps.len
        and oriented(right, flip_right?).steps.len = right.steps.len
}
```

So the fix keeps the meaning of a run. The chain of a run is joined one
conjunct at a time, so its comparisons are those of its conjuncts, in
order. Operands written the same, in two adjacent conjuncts of one run,
are in the same scope, and so [elaborate
alike](../Meaning.md#expressions-as-written). The fix's chain then
elaborates to the `and` of the run's comparisons, which the run is too,
with the `and`s nested otherwise, and an `and` has the same outcome
however it nests, well-defined or not. That is `lint::and_associates`, of
the [evaluation function](../../Lang/Semantics.md#the-evaluation-function).
Its evidence is testing, which evaluates it, since the solver unfolds
`eval` only one step:

```fren
set_option fren.evidence "random" in
expect and_associates(
    i: lang::Interp,
    env: lang::Env,
    a: lang::Expr<lang::Id>,
    b: lang::Expr<lang::Id>,
    c: lang::Expr<lang::Id>,
) {
    use lang::{Expr, eval}
    expect associates: eval(i, env, Expr::And(Expr::And(a, b), c)) = eval(i, env, Expr::And(a, Expr::And(b, c)))
}
```

The refinements check each way of writing the conjuncts, and the joining
of a chained comparison, as examples:

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
