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
the members may come in any order, and each is named once. The
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
and every other operand of the test is a variant. `lint::manual_ordering`
states when it fires, and the comparison of the fix:

```fren
pub mod lint

pub comp manual_ordering {
    use self::Comparison::{Ge, Gt, Le, Lt}
    in count: Int        -- the variants of the enumeration
    in named: Int        -- the variants that the test names
    in first?            -- they are the first variants
    in last?             -- they are the last
    in negated?          -- the test is that the operand is none of them
    pub det out fires?
    pub det out op: Comparison

    ensure rule: fires? iff (2 <= named < count and (first? or last?))
    ensure fix: op = if negated? then (if first? then Gt else Lt) else (if first? then Le else Ge)
}
```

The refinements check each test:

```fren
pub ordered enum Rank { Low, Mid, High, Top }

pub comp manual_ordering_written {
    in l: Rank
    pub det out low? := l in {Rank::Mid, Rank::Low}
    pub det out high? := l in {Rank::Top, Rank::High, Rank::Mid}
    pub det out equations? := l = Rank::Low or l = Rank::Mid
    pub det out none_high? := l != Rank::Top and l != Rank::High
    pub det out none_low? := l != Rank::Low and l != Rank::Mid
}

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
