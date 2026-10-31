# Comparisons

These lints fire on comparisons whose value is fixed. The
[checks](../../Check.md) can see such a comparison only where it fixes a whole
constraint, which is then vacuous or never holds; the lints also find it as
an operand, such as in the condition of an `if`, where it fixes nothing that
a check reports. They have no fix: the likely mistake is the bound, the
operator, or `and` written for `or`, and writing the value instead would
keep the mistake and hide it.

`absurd_extreme_comparisons` fires on a comparison of a string's or
sequence's `len`, or a set's or relation's `card`, with an integer literal,
whose value is fixed because a length is never negative: `s.len < 0` is
always `false`, and `q.card >= 0` always `true`. So is every comparison
with a negative literal: `s.len > -1` is always `true`, and `s.len = -1`
always `false`. The length may be on either side, as in `0 > s.len`. The
message says what the comparison always is. It does not fire on an `Int`,
which may be negative, such as an input `n` in `n >= 0`, nor on the
comparisons with `0` that say whether the collection is empty, such as
`s.len > 0`, which are [`length_zero`'s](../Style.md#empty-collections).
`lint::absurd_extreme_comparisons` states when it fires:

```fren
pub mod lint

pub proc absurd_extreme_comparisons(
    op: Comparison,
    bound: Int,          -- the literal compared with
    left?,               -- the length is the left operand, rather than the right
): (
    det fires?,
    det value?,          -- what the comparison always is, where it fires
) {
    use self::Comparison::{Ge, Gt, Le, Lt, Ne}

    ensure rule: fires? iff (bound < 0 or (bound = 0 and (if left? then op in {Lt, Ge} else op in {
        Gt,
        Le,
    })))
    ensure fixed: value? iff (if left? then op in {Ne, Gt, Ge} else op in {Ne, Lt, Le})
}

proc absurd_extreme_comparisons_exact(
    op: Comparison,
    bound: Int,
    left?,
    n: Nat,              -- the length
) {
    call p := absurd_extreme_comparisons(op, bound, left?)
    call q := length_zero(op, bound, left?)

    expect exact: when p.fires?, compares?(op, if left? then n else bound, if left? then bound else n) iff p.value?
    expect not_length_zero: not (p.fires? and q.fires?)
}
```

`absurd_extreme_comparisons` also fires on a comparison that orders with
the first or the last variant of an [ordered
enumeration](../../Lang/Items.md#enumerations), written as a path, or an
ordered [newtype](../../Lang/Items.md#newtypes) built from one, as in `g >=
Grade(Level::Low)`. No value is below the first variant, so `x >= First`
is always `true` and `x < First` always `false`, and none is above the
last, so `x <= Last` is always `true` and `x > Last` always `false`. The
variant may be on either side, as in `Last >= x`. It does not fire on `=`
or `!=`, nor on the comparisons of a [chained
comparison](../../Lang/Expressions.md#chained-comparisons).
`lint::absurd_ordered` models the comparison by its operator, the
position of the variant ([`lint::Position`](../Complexity/Methods.md#bounds-of-orderings)),
the last variant of the enumeration, and the side the variant is on. It
fires exactly where the comparison orders and has the same value for
every value of the other operand:

```fren
pub enum AbsurdValue { NotFixed, AlwaysTrue, AlwaysFalse }

-- Whether the comparison holds where the other operand is `x`.
fn compared?(op: Comparison, variant: Position, right?, x: Position) :=
    if right? then orders?(op, x, variant) else orders?(op, variant, x)

pub proc absurd_ordered(
    op: Comparison,
    variant: Position,    -- the variant compared with, or that the newtype built from it holds
    last: Position,      -- the last variant of its enumeration
    right?,              -- the variant is the right operand, rather than the left
): (
    det value: AbsurdValue,         -- what the comparison always is, if it fires
) {
    use self::AbsurdValue::{AlwaysFalse, AlwaysTrue, NotFixed}
    use self::Comparison::{Ge, Gt, Le, Lt}

    assume within: variant <= last

    ensure rule: value = (if not op in {Lt, Le, Gt, Ge} then NotFixed
        else if (forall (x: Position), when x <= last, compared?(op, variant, right?, x)) then AlwaysTrue
        else if (forall (x: Position), when x <= last, not compared?(op, variant, right?, x)) then AlwaysFalse
        else NotFixed)

    expect extreme: when value != NotFixed, variant = Position::V0 or variant = last
}
```

`contradictory_comparisons` fires on two comparisons of one operand,
written the same, joined by `and` and never both true, or joined by `or`
and never both false:

| Written | Value |
|---|---|
| `x = a and x = b`, where `a` and `b` are distinct | `false` |
| `x != a or x != b`, where `a` and `b` are distinct | `true` |
| `x < 3 and x > 5`, `x <= 3 and x >= 4`, `x = 3 and x > 3` | `false` |
| `x > 3 or x < 5`, `x >= 4 or x <= 3`, `x != 3 or x <= 3` | `true` |

Two values are distinct if they are integer literals of different
values, string literals written differently, without escape sequences,
`true` and `false`, or two different variants without payloads, such as
`Mode::Heat` and `Mode::Cool`, by what their paths resolve to. The usual
mistake is `and` and `or` swapped: `m != Mode::Heat or m != Mode::Cool`
always holds. Each comparison may have its operand on either side, as in
`5 < x`. With integer literals, any two comparisons are looked at, with
the cases exactly those that
[`disjoint?`](../Complexity/Comparisons.md#redundant-comparisons) gives: under `and`, the two are
disjoint, and under `or`, their complements are, so that no integer
fails both. The message says which value the two always have. It fires
inside any expression, such as the condition of an `if`. A [pattern
test](../../Lang/Expressions.md#pattern-tests) is not a comparison, so
`s is A and s is B` is left as it is.
`lint::contradictory_comparisons` states when it fires on integers, and
`lint::contradictory_equalities` on other values:

```fren
pub proc contradictory_comparisons(
    conjunction?,        -- the comparisons are joined by `and`, rather than `or`
    first: Comparison,    -- `x OP k`, with `x` on the left
    first_bound: Int,
    second: Comparison,
    second_bound: Int,
): (det fires?) {
    ensure rule: fires? iff (if conjunction?
        then disjoint?(first, first_bound, second, second_bound)
        else disjoint?(
            complement_of(first),
            first_bound,
            complement_of(second),
            second_bound
        ))
}

proc contradictory_comparisons_exact(
    conjunction?,
    first: Comparison,
    first_bound: Int,
    second: Comparison,
    second_bound: Int,
    x: Int,
) {
    call p := contradictory_comparisons(conjunction?, first, first_bound, second, second_bound)

    expect exact: when p.fires?,
        (if conjunction? then both?(first, first_bound, second, second_bound, x)
        else compares?(first, x, first_bound) or compares?(second, x, second_bound))
        iff not conjunction?
}

pub proc contradictory_equalities(
    conjunction?,
    first: Comparison,
    second: Comparison,
    distinct?,           -- the values compared with are distinct
): (det fires?) {
    use self::Comparison::{Eq, Ne}

    ensure rule: fires? iff (distinct? and (if conjunction? then first = Eq and second = Eq else first = Ne and second = Ne))
}
```

In a [chained comparison](../../Lang/Expressions.md#chained-comparisons),
it fires on each operand between two integer literals, `a OP₁ x OP₂ b`,
which is `x OP₁' a and x OP₂ b`, with `OP₁'` the mirror of `OP₁`, where
those cannot both hold: `5 < x < 3` and `3 <= x <= 2` are always `false`.
The message is reported at the chain. `lint::contradictory_chain` states
this, and the refinements check the value:

```fren
fn mirror_of(op: Comparison): Comparison := match op {
    Eq => Eq,
    Ne => Ne,
    Lt => Gt,
    Gt => Lt,
    Le => Ge,
    Ge => Le,
}

pub proc contradictory_chain(
    first: Comparison,    -- `a OP₁ x`, with `x` on the right
    first_bound: Int,
    second: Comparison,    -- `x OP₂ b`
    second_bound: Int,
): (det fires?) {
    ensure rule: fires? iff disjoint?(mirror_of(first), first_bound, second, second_bound)
}

set_option fren.lint.contradictory_comparisons "allow" in
pub proc contradictory_chain_written(x: Int): (det strict?, det loose?, det descending?) {
    out strict? := 5 < x < 3
    out loose? := 3 <= x <= 2
    out descending? := 1 > x >= 1
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub proc contradictory_chain_value(x: Int): (det strict?, det loose?, det descending?) {
    out strict? := false
    out loose? := false
    out descending? := false
}

expect contradictory_chain_sound(x: Int) {
    call concrete := contradictory_chain_value(x)
    refines concrete contradictory_chain_written(x)
}
expect contradictory_chain_complete(x: Int) {
    call concrete := contradictory_chain_written(x)
    refines concrete contradictory_chain_value(x)
}
```

Where one of two comparisons of an operand with integer literals implies
the other, [`redundant_comparisons`](../Complexity/Comparisons.md#redundant-comparisons) fires
instead: that is never where this lint does, since a single comparison of
an integer always holds for some integer and fails for another.
