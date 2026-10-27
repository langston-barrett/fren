# Matches

## Patterns as the lints see them

The lints of `match` arms and patterns in this chapter and in
[Patterns](../Complexity/Patterns.md) and [Matches](../Pedantic/Matches.md)
are stated over a model of what they look at. A scrutinee's value is a
variant, by its tag, with up to two integers as its payload, or an integer.
A pattern is `_`, a binder (its name, and whether it is written with `!`),
an integer literal, a range, a variant without a payload, or a variant
with a pattern for each of two values of its payload; those inner patterns
are *leaves*, which do not nest further, since the spec's functions do not
recurse. A bound of a range is an integer, or absent, a `Bound` as
[pattern tests](Comparisons.md#pattern-tests) model it; a range's bounds
are inclusive, as `a..b` is `a..=b - 1`. An or-pattern is a sequence of up
to four alternatives, and its slots are quantified over. An arm's body is
its written form and the name it mentions, if any, two bodies being
written the same exactly when they are equal; its value is its form
plus that name's value, which is a binder's value where the arm's pattern
binds the name, and the value of the name outside the pattern otherwise,
so that a body means something else wherever the name means something
else.

```fren
pub mod lint

-- The slots of an or-pattern, or of the arms of a `match`.
pub enum Slot { S0, S1, S2, S3 }

pub fn pos(s: Slot): Int := match s { Slot::S0 => 0, Slot::S1 => 1, Slot::S2 => 2, Slot::S3 => 3 }

-- A pattern of a value of a payload.
pub enum Leaf { Wild, Binder(Int, Bool), Lit(Int), Range(Bound, Bound) }

-- A pattern of a scrutinee.
pub enum Pat { Wild, Binder(Int, Bool), Lit(Int), Range(Bound, Bound), Tag(Int), Variant(Int, Leaf, Leaf) }

-- A scrutinee's value: a variant's tag and payload, or an integer `n`.
pub struct Val { tag: Int, n: Int, a: Int, b: Int }

pub enum Use { Nothing, Name(Int) }

-- An arm's body: its written form, and the name it mentions.
pub struct Body { form: Int, uses: Use }

pub fn lower_holds?(lo: Bound, v: Int) := match lo { Bound::Open => true, Bound::At(l) => l <= v }

pub fn upper_holds?(hi: Bound, v: Int) := match hi { Bound::Open => true, Bound::At(h) => v <= h }

pub fn leaf_matches?(l: Leaf, v: Int) := match l {
    Leaf::Lit(k) => v = k,
    Leaf::Range(lo, hi) => lower_holds?(lo, v) and upper_holds?(hi, v),
    _ => true,
}

pub fn pat_matches?(p: Pat, x: Val) := match p {
    Pat::Lit(k) => x.n = k,
    Pat::Range(lo, hi) => lower_holds?(lo, x.n) and upper_holds?(hi, x.n),
    Pat::Tag(t) => x.tag = t,
    Pat::Variant(t, l, m) => x.tag = t and leaf_matches?(l, x.a) and leaf_matches?(m, x.b),
    _ => true,
}

-- Whether the alternative in slot `s` of `alts` is there and matches `x`.
pub fn slot_matches?(alts: Seq<Pat>, s: Slot, x: Val) := pos(s) < alts.len and pat_matches?(alts[pos(s)], x)

pub fn or_matches?(alts: Seq<Pat>, x: Val) := exists (s: Slot), slot_matches?(alts, s, x)

-- The name that a leaf binds, `-1` for none; names are not negative.
pub fn leaf_name(l: Leaf): Int := match l { Leaf::Binder(k, _) => k, _ => -1 }

-- The value of the body `b` where the names `n1`, `n2` and `n3` are bound
-- to `v1`, `v2` and `v3`, and a name outside the patterns has the value `o`.
pub fn body_value(b: Body, n1: Int, v1: Int, n2: Int, v2: Int, n3: Int, v3: Int, o: Int): Int := b.form + match b.uses {
    Use::Nothing => 0,
    Use::Name(k) => if k >= 0 and k = n1 then v1 else if k >= 0 and k = n2 then v2 else if k >= 0 and k = n3 then v3 else o,
}

-- Whether the body `b` mentions the name `k`.
pub fn body_names?(b: Body, k: Int) := k >= 0 and b.uses = Use::Name(k)
```

## Collapsible matches

`collapsible_match` fires on an arm of a
[`match`](../../Lang/Expressions.md#matches) whose body is a `match` on one
of the arm's binders, which the arm's pattern can match instead, with a
[nested pattern](../../Lang/Patterns.md#kinds-of-pattern):

```text
match r {
    Reply::Ok(s) => match s { Shape::Circle(_) => 1, Shape::Square(_) => 2, _ => 0 },
    _ => 0,
}
```

is

```text
match r { Reply::Ok(Shape::Circle(_)) => 1, Reply::Ok(Shape::Square(_)) => 2, _ => 0 }
```

It fires where all of these hold:

- The arm's pattern is one variant, not an or-pattern, whose payload's
  patterns are `_` or binders, so that it matches every value of the
  variant.
- Its body, without parentheses, is a `match` of two or more arms on one
  of those binders, written as its name alone, and the binder is not
  mentioned elsewhere in the inner `match`: the fix drops it.
- The inner `_` arm's body mentions no binder of the arm's pattern. After
  the fix that body is the outer `_` arm's, outside the pattern, where
  the same name means something else, or nothing: in `Pair::Two(s, n!)
  => match s { Shape::Empty => 1, _ => n }, _ => n`, the inner `n` is the
  payload's and the outer `n` the input it shadows.
- The inner `match`'s last arm is `_`, and the first later arm of the outer
  `match` that matches a value of the variant is `_`, whose body is
  [written the same](../../Lint.md#written-the-same) as the inner `_`
  arm's. An arm that names the variant after the arm would be unreachable,
  an error, so the later arms that match its values are those with `_` or a
  binder among their alternatives.
- Neither `match` has an arm with a guard, which may not be taken where
  its pattern matches.
- No pattern of the inner `match` binds a name that the arm's pattern
  binds, which would then be bound twice in one pattern.

The fix replaces the arm with one arm for each inner arm but `_`, in order:
the variant's pattern with the inner arm's pattern, or its alternatives
with ` | ` between them, in place of the binder, and the inner arm's body,
as written. Where the arm has a comment, the lint has no fix: it writes
the arms from their patterns and bodies, and would drop it. It is
reported at the inner `match`.

The fix keeps the meaning. A value of the variant whose payload's value
matches an inner pattern is matched by the new arm of that pattern, as it
was by the inner arm, since the earlier new arms are the earlier inner
arms. A value that no inner pattern matches had the body of the inner `_`
arm; after the fix it falls through to the later arms, of which the first
that matches it is the outer `_` arm, with the same body, which means the
same there since it mentions no binder of the arm's pattern. Each body keeps
its guard: an inner arm's body was guarded by the outer pattern's test and
its own, and its new arm's test is their conjunction. The outer `_` arm's
body is now also taken where the inner `_` arm's was, and the copy of that
body under each guard was already checked. Each new pattern stands for as
many or-free patterns as the inner pattern does, since the payload's other
patterns are `_` or binders. It is Clippy's `collapsible_match`, also in
`style`. The refinements below check the fix on one example:

```fren
-- An arm of a `match` on a value of a payload.
pub struct LeafArm { pat: Leaf, body: Body }

pub fn leaf_arm_pat(a: LeafArm): Leaf := a.pat

pub fn leaf_arm_body(a: LeafArm): Body := a.body

-- Whether `s` is the first arm of `arms` whose pattern matches `v`.
pub fn first_leaf?(arms: Seq<LeafArm>, s: Slot, v: Int) := pos(s) < arms.len
    and leaf_matches?(leaf_arm_pat(arms[pos(s)]), v)
    and (forall (r: Slot), when pos(r) < pos(s), not leaf_matches?(leaf_arm_pat(arms[pos(r)]), v))
```

`lint::collapsible_match` states when it fires, computing these facts from an arm whose
pattern is the variant `tag` with the leaves `first` and `second`, whose
body is a `match` on the first value of the payload, and the outer `_`
arm's body. It checks that the fix keeps the meaning for every value of
the scrutinee: a value of the variant whose first value an inner arm but
`_` matches first has that arm's body, with the binder of the inner
pattern bound as before, and any other has the outer `_` arm's body,
where a name means what it means outside the patterns. Without the
condition on what the inner `_` arm's body mentions, the case of the
review, `Pair::Two(x, y!) => match x { Shape::Empty => 1, _ => y }, _ =>
y`, is a counterexample:

```fren
pub proc collapsible_match(
    tag: Int,                -- the variant of the arm's pattern
    first: Leaf,             -- its pattern of the first value of the payload, which the inner `match` reads
    second: Leaf,            -- of the second
    inner: Seq<LeafArm>,     -- the arms of the inner `match`
    outer: Body,             -- the body of the outer `_` arm, the first later arm that matches the variant
    x: Val,                  -- a value of the scrutinee
    o: Int,                  -- the value of a name outside the patterns
): (det fires?) {
    assume size: 1 <= inner.len <= 4

    -- the arm's body is a `match` on a binder of the arm's pattern
    det let on_binder? := first is Leaf::Binder(_, _)
    -- the arm's pattern is one variant, whose payload's patterns are `_` or binders
    det let flat? := second is Leaf::Wild | Leaf::Binder(_, _)
    -- the inner `match`'s last arm is `_`
    det let inner_wildcard? := leaf_arm_pat(inner[inner.len - 1]) = Leaf::Wild
    -- the first later arm that matches the variant is `_`, with the body of the inner `_` arm
    det let same_wildcard? := leaf_arm_body(inner[inner.len - 1]) = outer
    -- the binder is mentioned elsewhere in the inner `match`, or the inner `_` arm's body mentions a binder of the arm's pattern
    det let mentioned? := (exists (s: Slot), pos(s) < inner.len and body_names?(leaf_arm_body(inner[pos(s)]), leaf_name(first)))
        or body_names?(leaf_arm_body(inner[inner.len - 1]), leaf_name(second))
    -- an inner pattern binds a name that the arm's pattern binds
    det let clash? := (exists (s: Slot), pos(s) < inner.len and leaf_name(leaf_arm_pat(inner[pos(s)])) >= 0
        and leaf_name(leaf_arm_pat(inner[pos(s)])) in {leaf_name(first), leaf_name(second)})
    -- arms of the inner `match`
    det let n_inner: Int := inner.len

    ensure rule: fires? iff (on_binder? and flat? and inner_wildcard? and same_wildcard? and not mentioned?
        and not clash? and n_inner >= 2)

    expect mentions_kept: when mentioned?, not fires?

    expect keeps_meaning: forall (s: Slot), when fires? and x.tag = tag and first_leaf?(inner, s, x.a),
        if pos(s) = inner.len - 1 then
        body_value(leaf_arm_body(inner[pos(s)]), leaf_name(first), x.a, leaf_name(second), x.b, -1, 0, o)
        = body_value(outer, -1, 0, -1, 0, -1, 0, o)
        else
        body_value(leaf_arm_body(inner[pos(s)]), leaf_name(first), x.a, leaf_name(leaf_arm_pat(inner[pos(s)])), x.a,
        leaf_name(second), x.b, o)
        = body_value(leaf_arm_body(inner[pos(s)]), leaf_name(leaf_arm_pat(inner[pos(s)])), x.a, leaf_name(second),
        x.b, -1, 0, o)
}

pub enum Grade { Low, High, Off }
pub enum Gauge { Read(Grade, Int), Missing }

set_option fren.lint.collapsible_match "allow" in
pub proc collapsible_match_written(g: Gauge): (det v: Int) {
    out v := match g {
        Gauge::Read(l, n) => match l { Grade::Low => n, Grade::High => n + 1, _ => 0 },
        _ => 0,
    }
}

pub proc collapsible_match_fixed(g: Gauge): (det v: Int) {
    out v := match g {
        Gauge::Read(Grade::Low, n) => n, Gauge::Read(Grade::High, n) => n + 1,
        _ => 0,
    }
}

refine collapsible_match_sound: collapsible_match_fixed refines collapsible_match_written
refine collapsible_match_complete: collapsible_match_written refines collapsible_match_fixed
```

Where the inner `_` arm's body mentions a binder of the arm's pattern, the
nested form keeps an arm for the rest of the variant, as the one below
does, which the refinements check means the same; the fix, which drops it,
would give the rest of the variant the outer `_` arm's body, where `n`
names the input:

```fren
set_option fren.lint.collapsible_match "allow" in
pub proc collapsible_shadow_written(g: Gauge, n: Int): (det v: Int) {
    out v := match g {
        Gauge::Read(t, n!) => match t { Grade::Low => 1, _ => n },
        _ => n,
    }
}

pub proc collapsible_shadow_fixed(g: Gauge, n: Int): (det v: Int) {
    out v := match g {
        Gauge::Read(Grade::Low, _) => 1, Gauge::Read(_, n!) => n,
        _ => n,
    }
}

refine collapsible_shadow_sound: collapsible_shadow_fixed refines collapsible_shadow_written
refine collapsible_shadow_complete: collapsible_shadow_written refines collapsible_shadow_fixed
```

## Overlapping arms

`match_overlapping_arm` fires on a range among the alternatives of an arm
of a `match` on an `Int` or a `Nat` that has an integer in common with an
integer pattern of an earlier arm, a range or a literal, where neither is
within the other: `5..=15` after `0..=10`. The later arm is taken only for
the part of its range that the earlier arm leaves, which reads as if the
arms split the integers differently. A range within an earlier one is
never reached, an error (`F0318`), and one that contains an earlier one,
as `0..=10` after `5`, is the usual way to write an exception first, so
neither is reported. It is reported at the later range, and the message
names the earlier pattern, the first that it overlaps. Only the
top-level alternatives of the arms are compared, not the patterns within
a payload. There is no fix: which arm should have the values in common is
not in the text. An arm with a guard is left out, earlier or later, as
in Clippy: it may not be taken where its pattern matches. It is Clippy's
`match_overlapping_arm`, also in `style`.
Its functions compare the bounds of the [model](#patterns-as-the-lints-see-them):

```fren
-- The bounds of an integer pattern; a pattern of another kind is
-- unbounded.
pub fn lower_of(p: Pat): Bound := match p { Pat::Lit(k) => Bound::At(k), Pat::Range(lo, _) => lo, _ => Bound::Open }

pub fn upper_of(p: Pat): Bound := match p { Pat::Lit(k) => Bound::At(k), Pat::Range(_, hi) => hi, _ => Bound::Open }

-- Whether the lower bound `a` is at most the upper bound `b`.
pub fn reaches?(a: Bound, b: Bound) := match a {
    Bound::At(l) => match b { Bound::At(h) => l <= h, Bound::Open => true },
    Bound::Open => true,
}

-- Whether the lower bound `a` is at most the lower bound `b`, and the upper
-- bound `c` at most the upper bound `d`.
pub fn lower_le?(a: Bound, b: Bound) := match a {
    Bound::Open => true,
    Bound::At(x) => match b { Bound::At(y) => x <= y, Bound::Open => false },
}

pub fn upper_le?(c: Bound, d: Bound) := match d {
    Bound::Open => true,
    Bound::At(y) => match c { Bound::At(x) => x <= y, Bound::Open => false },
}

-- Whether the integer pattern `p` matches `v`.
pub fn int_matches?(p: Pat, v: Int) := lower_holds?(lower_of(p), v) and upper_holds?(upper_of(p), v)
```

`lint::match_overlapping_arm` states when it fires, computing the facts from the earlier
pattern and the later range, by their bounds, and checks them against
the integers that each matches:

```fren
pub proc match_overlapping_arm(
    earlier: Pat,            -- an integer literal or range of an earlier arm
    later: Pat,              -- a range of a later arm
    v: Int,
): (det fires?) {
    assume kinds: earlier is Pat::Lit(_) | Pat::Range(_, _) and later is Pat::Range(_, _)

    -- they have an integer in common
    det let meet? := reaches?(lower_of(earlier), upper_of(later)) and reaches?(lower_of(later), upper_of(earlier))
    -- the range is within the earlier pattern
    det let within? := lower_le?(lower_of(earlier), lower_of(later)) and upper_le?(upper_of(later), upper_of(earlier))
    -- the range contains the earlier pattern
    det let contains? := lower_le?(lower_of(later), lower_of(earlier)) and upper_le?(upper_of(earlier), upper_of(later))

    ensure rule: fires? iff (meet? and not within? and not contains?)

    expect disjoint: when not meet?, not (int_matches?(earlier, v) and int_matches?(later, v))
    expect within: when within? and int_matches?(later, v), int_matches?(earlier, v)
    expect contains: when contains? and int_matches?(earlier, v), int_matches?(later, v)
    expect literal_inside: when earlier is Pat::Lit(_) and meet?, contains?
}
```
