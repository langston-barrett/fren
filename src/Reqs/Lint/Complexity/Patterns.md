# Patterns

The lints of this chapter look at each or-pattern of two or more
alternatives in a [pattern](../../Lang/Patterns.md), of a `match` arm or of
a [pattern test](../../Lang/Expressions.md#pattern-tests), at any depth.
Each is reported at the or-pattern, from its first alternative to its
last, without a leading `|`, and its fix replaces that text. The
alternatives of an or-pattern bind no names, so a fix that rewrites them
drops no binder, and a pattern has no guard of its own: an arm's body is
guarded by what its pattern matches, which the fixes keep.

## Wildcards in or-patterns

`wildcard_in_or_patterns` fires on an or-pattern with `_` among its
alternatives, as `Shape::Empty | _`. `_` matches every value, so the
or-pattern matches what `_` does, and the other alternatives add nothing;
`_` is the last alternative, since one after it would never be reached, an
error (`F0318`). The fix writes `_`. It is Clippy's
`wildcard_in_or_patterns`, also in `complexity`.
The refinements below check the fix on one example:

```fren
pub mod lint

pub enum Signal { Stop, Slow, Go }

set_option fren.lint.wildcard_in_or_patterns "allow" in
set_option fren.evidence "enumerated" in
pub proc wildcard_in_or_written(s: Signal): (det v: Int) {
    out v := match s { Signal::Stop => 0, Signal::Slow | _ => 1 }
}

set_option fren.evidence "enumerated" in
pub proc wildcard_in_or_fixed(s: Signal): (det v: Int) {
    out v := match s { Signal::Stop => 0, _ => 1 }
}

expect wildcard_in_or_sound(s: lint::Signal) {
    use lint
    call concrete := wildcard_in_or_fixed(s)
    refines concrete wildcard_in_or_written(s)
}
expect wildcard_in_or_complete(s: lint::Signal) {
    use lint
    call concrete := wildcard_in_or_written(s)
    refines concrete wildcard_in_or_fixed(s)
}
```

`lint::wildcard_in_or_patterns` computes the fact from an or-pattern of the
[model](../Style/Matches.md#patterns-as-the-lints-see-them), and checks
that `_`, the fix, matches what the or-pattern does:

```fren
pub proc wildcard_in_or_patterns(alts: Seq<Pat>, x: Val): (det fires?) {
    assume size: 2 <= alts.len <= 4

    -- an alternative is `_`
    det let wildcard? := (exists (s: Slot), pos(s) < alts.len and alts[pos(s)] = Pat::Wild)

    ensure rule: fires? iff wildcard?

    expect keeps_meaning: when fires?, or_matches?(alts, x) iff pat_matches?(Pat::Wild, x)
}
```

## Ranges written as alternatives

`manual_range_patterns` fires on an or-pattern whose alternatives are
integer literals and ranges whose bounds are literals, three or more of
them, or two if one is a range, that together match the integers of one
range without a gap: `1 | 2 | 3` is `1..=3`, and `..=0 | 1 | 2..5` is
`..=4`. The fix writes that range, `a..=b`, `a..` or `..=b`, with its
bounds in decimal. Alternatives that match every integer together, as
`..=0 | 1..`, are left alone, since no range is written for them; and so is
an alternative whose bound is a constant, whose name the fix would drop.
Two literals, as `0 | 1`, read as well as a range of two. It is Clippy's
`manual_range_patterns`, also in `complexity`, which fires on as many
alternatives. The refinements below check the fix on one example:

```fren
set_option fren.lint.manual_range_patterns "allow" in
pub proc manual_range_written(n: Int): (det small: Int, det low: Int) {
    out small := match n { 1 | 2 | 3 => n, _ => 0 }
    out low := match n { ..=0 | 1 | 2..5 => 1, 5 => 2, _ => 3 }
}

pub proc manual_range_fixed(n: Int): (det small: Int, det low: Int) {
    out small := match n { 1..=3 => n, _ => 0 }
    out low := match n { ..=4 => 1, 5 => 2, _ => 3 }
}

expect manual_range_sound(n: Int) {
    call concrete := manual_range_fixed(n)
    refines concrete manual_range_written(n)
}
expect manual_range_complete(n: Int) {
    call concrete := manual_range_written(n)
    refines concrete manual_range_fixed(n)
}
```

`lint::manual_range_patterns` states when it fires, computing the facts from an or-pattern of the
[model](../Style/Matches.md#patterns-as-the-lints-see-them). Its
alternatives leave no gap when each upper bound that another alternative
reaches past is followed by an integer that one of them matches. The fix
is the range from the least lower bound to the greatest upper bound, and
the model checks that it matches exactly the integers that the or-pattern
does:

```fren
-- Whether some alternative of `alts` matches the integer `v`.
pub fn covers?(alts: Seq<Pat>, v: Int) := exists (s: Slot), pos(s) < alts.len and int_matches?(alts[pos(s)], v)

-- Whether some alternative of `alts` matches an integer above `h`.
pub fn past?(alts: Seq<Pat>, h: Int) :=
    exists (s: Slot), pos(s) < alts.len and not upper_le?(upper_of(alts[pos(s)]), Bound::At(h))

-- Whether the alternatives leave a gap after the one in slot `s`.
pub fn gap_after?(alts: Seq<Pat>, s: Slot) := pos(s) < alts.len and match upper_of(alts[pos(s)]) {
    Bound::At(h) => past?(alts, h) and not covers?(alts, h + 1),
    Bound::Open => false,
}

pub proc manual_range_patterns(alts: Seq<Pat>, v: Int): (det fires?) {
    assume size: 2 <= alts.len <= 4
    -- A range matches some integer (`F0349`).
    assume ranges: forall (s: Slot), when pos(s) < alts.len,
        reaches?(lower_of(alts[pos(s)]), upper_of(alts[pos(s)]))

    det let n_alternatives: Int := alts.len
    -- each alternative is an integer literal or a range whose bounds are literals
    det let integers? := (forall (s: Slot), when pos(s) < alts.len, alts[pos(s)] is Pat::Lit(_) | Pat::Range(_, _))
    -- one of them is a range
    det let range? := (exists (s: Slot), pos(s) < alts.len and alts[pos(s)] is Pat::Range(_, _))
    -- together they match the integers of one range, bounded on some side
    det let interval? := not (exists (s: Slot), gap_after?(alts, s))
        and not ((exists (s: Slot), pos(s) < alts.len and lower_of(alts[pos(s)]) = Bound::Open)
        and (exists (s: Slot), pos(s) < alts.len and upper_of(alts[pos(s)]) = Bound::Open))

    ensure rule: fires? iff (integers? and interval? and (n_alternatives >= 3 or (n_alternatives >= 2 and range?)))

    expect keeps_meaning: when fires?, covers?(alts, v) iff
        ((exists (s: Slot), pos(s) < alts.len and lower_holds?(lower_of(alts[pos(s)]), v))
        and (exists (s: Slot), pos(s) < alts.len and upper_holds?(upper_of(alts[pos(s)]), v)))
}
```

The alternatives make one range when, in the order of their lower bounds,
each starts no later than one past the highest integer that those before
it reach. `lint::range_union` states it for two intervals, the first
starting no later than the second, as `unionInterval?` decides it, step by
step:

```fren
pub proc range_union(
    lo1: Int,
    hi1: Int,
    lo2: Int,
    hi2: Int,
    n: Int,              -- an integer between the lowest and the highest bound
): (
    det joined?,         -- they leave no gap
) {
    assume sorted: lo1 <= lo2 <= hi2 and lo1 <= hi1
    assume between: lo1 <= n <= hi1.max(hi2)

    ensure rule: joined? iff lo2 <= hi1 + 1

    expect no_gap: when joined?, (lo1 <= n <= hi1 or lo2 <= n <= hi2)
}
```
