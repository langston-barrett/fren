# Comparisons

## Orderings written out

`manual_ordering`, `allow` by default, fires on a test that an operand is
one of the first two or more variants of an [ordered
enumeration](../../Lang/Items.md#enumerations), or one of the last two or
more, but not all of them, and is fixable: with `pub ordered enum Severity
{ Silent, Info, Warning, Error }`, `s in {Silent, Info}` becomes `s <=
Info`, and `s in {Error, Warning}` becomes `s >= Warning`. The test is a
membership in a set literal, `x in {...}`, a disjunction of equations of
one operand, `x = Silent or x = Info`, or the conjunction of
disequations that says the operand is none of them, `x != Error and x !=
Warning`, which becomes `x < Warning`. Each variant is written as a path,
and the members may come in any order, or more than once. The
disjunction or conjunction is the whole of a run of `or` or of `and`, read
as [`chainable_comparison`](../Style/Comparisons.md#chained-comparisons)
reads a run of `and`, with no other operand, and the operand is [written
the same](../../Lint.md#written-the-same) in each comparison. The fix
compares with a variant the test names: the last it names, where they are
the first variants, and the first it names otherwise.

It is `allow` by default because the two differ once a variant is added
among those named: `s <= Info` takes in a variant added between `Info`
and `Silent`, and `s in {Silent, Info}` does not, and only the spec's
author knows which is meant. Where the order means something, as a level
of severity does, the comparison says what the membership spells out, and
keeps holding as variants are added. Clippy has no counterpart. The fix
keeps the guards: it evaluates the operand once, where the test first did,
and every other operand of the test is a variant. `lint::manual_ordering` models the test by
the variants it names, by their [positions](../Complexity/Methods.md#bounds-of-orderings),
the last variant of the enumeration, and whether the test is that the
operand is none of them. The fix compares with the last variant named,
where they are the first, or the first named, where they are the last,
and it holds exactly where the test does, for every value of the
operand:

```fren
pub mod lint

pub enum OrderingFix { Unchanged, Compare(Comparison, Position) }

-- The variants a test names: whether it names each position.
pub struct NamedVariants { v0?, v1?, v2?, v3?, v4? }

fn names?(named: NamedVariants, v: Position) := match v {
    Position::V0 => named.v0?,
    Position::V1 => named.v1?,
    Position::V2 => named.v2?,
    Position::V3 => named.v3?,
    Position::V4 => named.v4?,
}

-- A function's body has no quantifier, so that `decide` evaluates it:
-- each is over the five positions in turn.

-- The number of variants named.
fn count_named(named: NamedVariants): Int := (if named.v0? then 1 else 0) + (if named.v1? then 1 else 0)
    + (if named.v2? then 1 else 0) + (if named.v3? then 1 else 0) + (if named.v4? then 1 else 0)

-- The test names two variants or more, but not all of them.
fn some_named?(named: NamedVariants, last: Position) :=
    count_named(named) >= 2 and (not named.v0?
    or (Position::V1 <= last and not named.v1?)
    or (Position::V2 <= last and not named.v2?)
    or (Position::V3 <= last and not named.v3?)
    or (Position::V4 <= last and not named.v4?))

-- Whether `v` is named exactly when it is up to `m`, if `up?`, or from `m`,
-- for `v` a variant of the enumeration.
fn bounded_at?(named: NamedVariants, last: Position, v: Position, m: Position, up?) :=
    when v <= last, names?(named, v) iff (if up? then v <= m else v >= m)

-- The variants named are those up to `m`, if `up?`, or from `m`.
fn bounded?(named: NamedVariants, last: Position, m: Position, up?) :=
    forall (v: Position), bounded_at?(named, last, v, m, up?)

-- `x OP m` holds exactly where the test does, at `x`.
fn agrees_at?(named: NamedVariants, last: Position, negated?, op: Comparison, m: Position, x: Position) :=
    when x <= last, (names?(named, x) != negated?) iff orders?(op, x, m)

pub comp manual_ordering {
    use self::Comparison::{Ge, Gt, Le, Lt}
    use self::OrderingFix::{Compare, Unchanged}
    in named: NamedVariants          -- the variants that the test names
    in last: Position        -- the last variant of the enumeration
    in negated?              -- the test is that the operand is none of them

    assume within: forall (v: Position), when names?(named, v), v <= last
    pub det out fix: OrderingFix

    ensure first: forall (m: Position), when some_named?(named, last) and bounded?(named, last, m, true),
        fix = Compare(if negated? then Gt else Le, m)
    ensure last_variants: forall (m: Position), when some_named?(named, last) and bounded?(named, last, m, false),
        fix = Compare(if negated? then Lt else Ge, m)
    ensure otherwise: unless some_named?(named, last)
        and (exists (m: Position), bounded?(named, last, m, true) or bounded?(named, last, m, false)),
        fix = Unchanged

    expect keeps_meaning: forall (op: Comparison) (m: Position), when fix = Compare(op, m),
        names?(named, m) and (forall (x: Position), agrees_at?(named, last, negated?, op, m, x))
}
```

The refinements check each test:

```fren
pub ordered enum Rank { Low, Mid, High, Top }

set_option fren.lint.manual_pattern_test "allow" in
set_option fren.evidence "enumerated" in
pub comp manual_ordering_written {
    in l: Rank
    pub det out low? := l in {Rank::Mid, Rank::Low}
    pub det out high? := l in {Rank::Top, Rank::High, Rank::Mid}
    pub det out equations? := l = Rank::Low or l = Rank::Mid
    pub det out none_high? := l != Rank::Top and l != Rank::High
    pub det out none_low? := l != Rank::Low and l != Rank::Mid
}

set_option fren.evidence "enumerated" in
pub comp manual_ordering_fixed {
    in l: Rank
    pub det out low? := l <= Rank::Mid
    pub det out high? := l >= Rank::Mid
    pub det out equations? := l <= Rank::Mid
    pub det out none_high? := l < Rank::High
    pub det out none_low? := l > Rank::Mid
}

refine manual_ordering_sound: manual_ordering_fixed refines manual_ordering_written
refine manual_ordering_complete: manual_ordering_written refines manual_ordering_fixed
```
