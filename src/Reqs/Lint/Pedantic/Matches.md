# Matches

## Arms

`match_same_arms` and `wildcard_single_variant` look at the arms of a
[`match`](../../Lang/Expressions.md#matches) as written, as
[`match_like_membership`](../Style.md#matches-that-are-memberships) does.
Both are fixable. Both look only at a `match` whose patterns are all
*flat*: `_`, binders, `true`, `false`, variants whose payloads' patterns
are `_` or binders, and or-patterns of these. Two flat patterns either
match no value in common or one contains the other, so moving an arm
earlier, removing one, or naming what `_` matches keeps the meaning. With
a nested, literal or range pattern, an arm can match part of what a later
one does, as `S::A(0)` does of `S::A(_)`.

An arm with a [guard](../../Lang/Expressions.md#matches) is not taken
everywhere its pattern matches: where its guard fails, the arms after it
are tried. So `match_same_arms` does not fire on a `match` with a guard,
where merging or removing an arm would move the values it matches past a
guard or out from under one. `wildcard_single_variant` counts the variants
that `_` matches as those that no arm without a guard names, since `_` is
taken for the others where their guards fail, as `E::A` in `match e {
E::A if ok? => 1, _ => 2 }`, and it looks only at a `_` arm without a
guard.

A [table over a scrutinee](../../Lang/Expressions.md#tables-over-a-scrutinee)
means a `match`, and the match lints, these, those of
[Complexity](../Complexity/Matches.md), `match_like_membership` and
[`wildcard_enum_match_arm`](../Restriction.md#wildcard-arms), look at it as
at that `match`, and call it a table in their messages. Their fixes keep
its arms disjoint: an or-pattern of arms that have the same body matches
what they did, and removing an arm that has the body of the `_` arm, the
otherwise, leaves its values to `_`. But the `_` arm of a table is also
taken where the guards of the other arms fail, which no pattern can name
without overlapping the arms with guards, so `wildcard_single_variant` and
`wildcard_enum_match_arm` do not fire on a table that has an arm with a
guard.

`match_same_arms`, `allow` by default, fires on two arms whose bodies are
[written the same](../../Lint.md#written-the-same), and whose patterns bind no names.
It is reported once for each group of such arms, at the first arm that
the fix removes, and says which arm it repeats. The fix depends on the
group:

- If neither arm is `_`, the fix merges the group into one arm, with an
  or-pattern of their alternatives, `A | B => body`, where the first of
  them is.
- If one is `_`, the fix removes the others, and `_` then matches their
  variants.
- If the group is every arm of the `match`, the fix replaces the `match`
  with the body, in parentheses where [fixes need
  them](../../Lint.md#parentheses-in-fixes).

Neither changes what the `match` means. No variant is named twice, and
`_` is the last arm, so a variant is matched by the same body after the
fix as before, whatever the order of the arms. A body's guard is the test
of its arm's pattern, and after the fix it is the disjunction of the
guards of the arms it replaces, under each of which the body was already
evaluated. A pattern that binds a name is not merged, since its body
could mention the name. `lint::match_same_arms` states when it fires on
two arms, and the fix of their group:

```fren
pub mod lint

pub enum ArmsFix { Merge, Remove, Replace }

pub comp match_same_arms {
    in same_body?        -- the bodies are written the same
    in binds?            -- the pattern of either binds a name
    in wildcard?         -- one of the group is `_`
    in all?              -- the group is every arm of the `match`
    pub det out fires?
    pub det out fix: ArmsFix

    ensure rule: fires? iff (same_body? and not binds?)
    ensure group_fix: fix = if all? then ArmsFix::Replace else if wildcard? then ArmsFix::Remove else ArmsFix::Merge
}
```

`wildcard_single_variant`, `allow` by default, fires on a `_` arm that
matches exactly one variant. The fix names it: `E::V`, or `E::V(_, _)`
with one `_` per value of its payload, written as another pattern of the
`match` writes its variant's path, or as `V` or `E::V` if one of those
names it. If none does, the lint has no fix. A variant added to the
enumeration later then makes the `match` non-exhaustive, a static error,
rather than being matched by `_` without notice. The arm matches the same
variant as before, and its body's guard, that no earlier arm matches, is
then the test of that variant, which means the same. If `fren fix` also
removes an arm of the `match` that has the body of the `_` arm
(`match_same_arms`), `_` then matches more than one variant, so
`wildcard_single_variant` is not fixed. `lint::wildcard_single_variant`
states when it fires:

```fren
pub comp wildcard_single_variant {
    in n_matched: Int    -- variants that no other arm names

    assume reachable: n_matched >= 1
    pub det out fires?

    ensure rule: fires? iff n_matched = 1
}
```

## Variant tests

`if_chain_match`, `allow` by default, fires on a chain `if T1 then a else
if T2 then b ... else z` of two or more tests, each a *variant test*: a test
of which variant a scrutinee `x` is, `x = E::V`, `x in {E::V, E::W}`, a
[pattern test](../../Lang/Expressions.md#pattern-tests) `x is P` whose
alternatives are each a variant whose payload's patterns are all `_`,
such as `x is E::V(_) | E::W`, or an `or` of such tests. For now only
such flat patterns are variant tests: a literal, a range or a nested
pattern, as in `x is E::V(0)`, tests more than which variant `x` is. The scrutinee is [written the same](../../Lint.md#written-the-same) in
every test. A variant compared with `=` or `in` has no payload, since `x =
E::V(a)` compares the payload too; a pattern test may name a variant with
a payload, whose pattern the arm writes as the test does. The chain starts at an `if` that is not the `else` branch
of another. Its fix is a [`match`](../../Lang/Expressions.md#matches), `match x {
V => a, W | X => b, ..., _ => z }`, with an arm for each test, whose
pattern is an or-pattern if the test names several variants. A `match`
names no variant twice, so the lint does not fire if a variant is tested
twice. If the tests name every variant, the final `else` is never taken,
and the fix drops it, since a `_` arm that covers no variant is an error.

The fix keeps the meaning, and the guards. In the chain, a branch is
guarded by its test and the negations of the tests before it, which, since
no variant is tested twice, is its test alone: the test of its arm's
pattern. `z` and the `_` arm are both guarded by the negations of all the
tests. The scrutinee is evaluated once, where the first test was. A body
that is a top-level `when`, `unless` or quantifier, which an arm's body cannot be, is
put in parentheses, and so is a scrutinee with a `{`, which after `match`
would start the arms. `lint::if_chain_match` states when it fires and
whether the fix has a `_` arm:

```fren
pub comp if_chain_match {
    in n_tests: Int      -- tests in the chain
    in variant_tests?    -- each is a variant test of the same scrutinee
    in n_repeated: Nat   -- times a test names a variant that it, or an earlier test, names before
    in n_untested: Nat   -- variants of the enumeration that no test names

    assume counts: n_tests >= 1
    pub det out fires?
    pub det out wildcard?  -- the fix keeps the final `else`, as the `_` arm

    ensure rule: fires? iff (variant_tests? and n_tests >= 2 and n_repeated = 0)
    ensure fix: wildcard? iff n_untested > 0
}
```

`case_split_guarantees`, `allow` by default, fires on a component with two or
more guarantees `when T, y = e`, or `when T, y? iff e`, of one output
`y`, whose conditions `T` are variant tests of one scrutinee `x`, naming no
variant twice. Together they say what one guarantee `y = match x { ...
}` says, with an arm for each, and `_ => y` if some variant is not tested,
for which they leave `y` unconstrained. Its message is reported at the
second of them, names them all, and suggests that guarantee. A
guarantee `unless T, y = e` is not one of them: it constrains `y` for the
variants that `T` does not name. As in a `match` arm, `e` is guarded by
`T`. There is no fix: traces, claims and `impl`s refer to guarantees by
name, so merging them changes the structure of the spec, not only its text.
`lint::case_split_guarantees` states when it fires:

```fren
pub comp case_split_guarantees {
    in n_cases: Nat      -- guarantees `when T, y = e` of one output, whose `T` are variant tests of one scrutinee
    in n_repeated: Nat   -- times a test names a variant that it, or an earlier test, names before
    pub det out fires?

    ensure rule: fires? iff (n_cases >= 2 and n_repeated = 0)
}
```

## One pattern and `_`

`single_match_else`, `allow` by default, fires on a `match` of two arms,
of which the first has a pattern other than `_` that binds nothing, and
the second is `_`: `match x { E::V => a, _ => b }`, or `match n { 0..=9 =>
a, _ => b }`. A `match` on a `Bool` is [`match_bool`'s](#matches-on-a-bool).
Its fix is `if T then a else b`, where `T` tests whether `x` matches the
pattern: `x = E::V` for one variant without a payload or one literal, `x
in {E::V, E::W}` for several, and otherwise, as for an integer literal
not written in decimal, such as `0x10`, which `=` would write differently, the [pattern
test](../../Lang/Expressions.md#pattern-tests) `x is P`, with `P` written
as the arm writes it, as for
[`match_like_membership`](../Style.md#matches-that-are-memberships), so
that [`is_equality`](../Style/Comparisons.md#pattern-tests) does not
report the fix. The bodies and the scrutinee are as they are written. The
`if` is in parentheses where [fixes need
them](../../Lint.md#parentheses-in-fixes), since it ends in its `else`
branch, and so is the scrutinee, as the left operand of `=`, `in` or `is`.
A variant without a payload, or a literal, equals itself alone, so `T`
holds exactly where the pattern matches, and the `if` takes the branch
that the `match` takes. The fix keeps the guards: `a` is guarded by the
test of the pattern, which is `T`, and `b` by its negation, as the
branches of the `if` are. The scrutinee is evaluated where it was.

It does not fire where another lint reports the `match`:
[`match_like_membership`](../Style.md#matches-that-are-memberships), where
the bodies are `true` and `false`;
[`needless_match`](../Complexity/Matches.md#matches-that-give-back-the-scrutinee),
where both arms give back the scrutinee; `match_same_arms`, where the
bodies are written the same; and
[`trivial_match`](../Complexity/Matches.md#trivial-matches), which reports
a `match` of one arm. Nor does it fire where either arm has a
[guard](../../Lang/Expressions.md#matches), which the `if` has no place
for. Where the `match` has a comment, the lint has no
fix: the fix writes the `if` from the scrutinee, the pattern and the
bodies, and would drop it. Its Clippy counterpart, of the same name, is
`pedantic` too. The refinements below check the fix on one example:

```fren
pub enum Light { Red, Amber, Green }
pub enum Lamp { Lit(Light), Dark }

set_option fren.lint.single_match_else "allow" in
pub comp single_match_else_written {
    in light: Light
    in lamp: Lamp
    in n: Int
    in a: Int
    in b: Int
    pub det out v: Int := match light { Light::Red => a, _ => b }
    pub det out w: Int := match lamp { Lamp::Lit(Light::Red | Light::Amber) => a, _ => b }
    pub det out x: Int := match n { 0..=9 => a, _ => b }
    pub det out y: Int := match n { 1 | 3 => a, _ => b }
}

pub comp single_match_else_fixed {
    in light: Light
    in lamp: Lamp
    in n: Int
    in a: Int
    in b: Int
    pub det out v: Int := if light = Light::Red then a else b
    pub det out w: Int := if lamp is Lamp::Lit(Light::Red | Light::Amber) then a else b
    pub det out x: Int := if n is 0..=9 then a else b
    pub det out y: Int := if n in {1, 3} then a else b
}

refine single_match_else_sound: single_match_else_fixed refines single_match_else_written
refine single_match_else_complete: single_match_else_written refines single_match_else_fixed
```

`lint::single_match_else` states when it fires, computing the facts from the arms'
patterns in the [model](../Style/Matches.md#patterns-as-the-lints-see-them),
and checks that the `if` takes the branch that the `match` takes, testing
a literal or a variant without a payload with `=`, and another pattern
with `is`, which is the pattern's own test:

```fren
-- Whether the pattern `p` binds a name.
pub fn pat_binds?(p: Pat) := match p {
    Pat::Binder(_, _) => true,
    Pat::Variant(_, l, m) => l is Leaf::Binder(_, _) or m is Leaf::Binder(_, _),
    _ => false,
}

-- The test of the fix of `single_match_else` on the pattern `p`.
pub fn fix_test?(p: Pat, x: Val) := match p { Pat::Lit(k) => x.n = k, Pat::Tag(t) => x.tag = t, _ => pat_matches?(p, x) }

pub comp single_match_else {
    in first: Pat            -- the first arm's pattern
    in second: Pat           -- the second's
    in a: Body               -- the first arm's body
    in b: Body               -- the second's
    in bool?                 -- the scrutinee is a `Bool`
    in others?               -- `match_like_membership`, `needless_match` or `trivial_match` fires on the `match`
    in x: Val
    in o: Int

    pub det out fires?

    -- the first arm's pattern is not `_`, binds nothing, and the scrutinee is not a `Bool`
    det out test? := first != Pat::Wild and not pat_binds?(first) and not bool?
    -- the second arm is `_`
    det out wildcard? := second = Pat::Wild
    -- another match lint fires on it: those, or `match_same_arms`, where the bodies are written the same
    det out other? := others? or a = b

    ensure rule: fires? iff (test? and wildcard? and not other?)

    expect keeps_meaning: when fires?, body_value(if pat_matches?(first, x) then a else b, -1, 0, -1, 0, -1, 0, o)
        = body_value(if fix_test?(first, x) then a else b, -1, 0, -1, 0, -1, 0, o)
    expect binders_kept: when pat_binds?(first), not fires?
}
```

## Matches on a `Bool`

`match_bool`, `allow` by default, fires on a `match` on a `Bool` of two
arms, of which the first is `true` or `false`, and the second the other or
`_`: `match c? { true => a, false => b }`. Its fix is `if c? then a else
b`, whose `then` branch is the body of the arm that `true` takes, with the
scrutinee and the bodies as they are written, and the `if` in parentheses
where [fixes need them](../../Lint.md#parentheses-in-fixes). The `if`
takes the branch that the `match` takes, and each body is guarded by the
scrutinee or its negation, as the arm's test was. The scrutinee is
evaluated where it was. It does not fire where `match_like_membership`,
`match_same_arms` or `trivial_match` does, and, like `single_match_else`,
has no fix where the `match` has a comment. It does not fire on a
`match` with a guard. It is Clippy's `match_bool`,
also in `pedantic`. The refinements below check the fix on one example:

```fren
set_option fren.lint.match_bool "allow" in
pub comp match_bool_written {
    in c?
    in a: Int
    in b: Int
    pub det out v: Int := match c? { true => a, false => b }
    pub det out w: Int := match c? { false => a, _ => b }
}

pub comp match_bool_fixed {
    in c?
    in a: Int
    in b: Int
    pub det out v: Int := if c? then a else b
    pub det out w: Int := if c? then b else a
}

refine match_bool_sound: match_bool_fixed refines match_bool_written
refine match_bool_complete: match_bool_written refines match_bool_fixed
```

`lint::match_bool` states when it fires, computing the facts from the two arms' patterns,
and checks the fix for each value of the scrutinee:

```fren
pub enum BoolPat { True, False, Wild }

pub fn bool_matches?(p: BoolPat, c?) := match p { BoolPat::True => c?, BoolPat::False => not c?, BoolPat::Wild => true }

pub comp match_bool {
    in first: BoolPat
    in second: BoolPat
    in a: Body               -- the first arm's body
    in b: Body               -- the second's
    in others?               -- `match_like_membership` or `trivial_match` fires on the `match`
    in c?                    -- the scrutinee's value
    in o: Int

    -- The `match` is exhaustive, and its second arm is reachable.
    assume accepted: first = BoolPat::Wild or second = BoolPat::Wild or first != second

    pub det out fires?

    -- the first arm is `true` or `false`, and the second the other or `_`
    det out literals? := first != BoolPat::Wild and (second = BoolPat::Wild or second != first)
    -- another match lint fires on it: those, or `match_same_arms`, where the bodies are written the same
    det out other? := others? or a = b

    ensure rule: fires? iff (literals? and not other?)

    expect keeps_meaning: when fires?,
        body_value(if bool_matches?(first, c?) then a else b, -1, 0, -1, 0, -1, 0, o)
        = body_value(if c? iff first = BoolPat::True then a else b, -1, 0, -1, 0, -1, 0, o)
}
```

## Nested or-patterns

`unnested_or_patterns`, `allow` by default, fires on two or more
alternatives of an or-pattern, next to each other, that name one variant
and whose payloads' patterns are [written the same](../../Lint.md#written-the-same)
but at one value, the same for all of them: `Lamp::Lit(Light::Red) |
Lamp::Lit(Light::Amber)` is `Lamp::Lit(Light::Red | Light::Amber)`. It
looks at or-patterns as the [lints of patterns](../Complexity/Patterns.md)
do, and is reported at the alternatives, from the first to the last. The
fix writes them as one alternative, the variant with the or-pattern of
their patterns of that value nested, in order, and the first's patterns of
the others. The nested or-pattern matches what the alternatives matched
together, one alternative for each, in the same order, so each stays
reachable, and the pattern stands for as many or-free patterns as before.
Only alternatives next to each other are merged, so that none moves past
another. It is Clippy's `unnested_or_patterns`, also in `pedantic`.
The refinements below check the fix on one example:

```fren
set_option fren.lint.unnested_or_patterns "allow" in
pub comp unnested_or_written {
    in lamp: Lamp
    pub det out v: Int := match lamp { Lamp::Lit(Light::Red) | Lamp::Lit(Light::Amber) => 1, _ => 0 }
}

pub comp unnested_or_fixed {
    in lamp: Lamp
    pub det out v: Int := match lamp { Lamp::Lit(Light::Red | Light::Amber) => 1, _ => 0 }
}

refine unnested_or_sound: unnested_or_fixed refines unnested_or_written
refine unnested_or_complete: unnested_or_written refines unnested_or_fixed
```

`lint::unnested_or_patterns` states when it fires, computing the facts from two alternatives of the
model, a pattern being written the same as another exactly when it is
equal to it, and checks that the nested or-pattern matches what the two
did:

```fren
pub fn variant_tag(p: Pat): Int := match p { Pat::Variant(t, _, _) => t, _ => 0 }

pub fn first_leaf(p: Pat): Leaf := match p { Pat::Variant(_, l, _) => l, _ => Leaf::Wild }

pub fn second_leaf(p: Pat): Leaf := match p { Pat::Variant(_, _, m) => m, _ => Leaf::Wild }

pub comp unnested_or_patterns {
    in first: Pat
    in second: Pat
    in x: Val

    pub det out fires?

    -- they name the same variant
    det out same_variant? := first is Pat::Variant(_, _, _) and second is Pat::Variant(_, _, _)
        and variant_tag(first) = variant_tag(second)
    -- values of its payload whose patterns are not written the same
    det out n_differ: Int := (if first_leaf(first) = first_leaf(second) then 0 else 1)
        + (if second_leaf(first) = second_leaf(second) then 0 else 1)

    ensure rule: fires? iff (same_variant? and n_differ = 1)

    -- `V(p | q, r)` where they differ in the first value, and `V(p, q | r)`
    -- in the second.
    expect keeps_meaning: when fires?, (pat_matches?(first, x) or pat_matches?(second, x)) iff
        (x.tag = variant_tag(first)
        and (leaf_matches?(first_leaf(first), x.a) or leaf_matches?(first_leaf(second), x.a))
        and (leaf_matches?(second_leaf(first), x.b) or leaf_matches?(second_leaf(second), x.b)))
}
```

## Chains of conditions

`manual_table`, `allow` by default, fires on a chain `if T1 then a else if
T2 then b ... else z` of two or more tests, where it starts, as
[`if_chain_match`](#variant-tests) does, that are not variant tests of
one scrutinee, which `if_chain_match` reports instead. The chain picks a
value by the first test that holds, as a [table](../../Lang/Expressions.md#tables)
does, and the message suggests `table { T1 => a, T2 => b, ..., _ => z }`,
with a condition or value that is a top-level `when`, `unless`, `let` or
quantifier in parentheses, which a row's cannot be. The table means the
same, and guards each row as the chain guards its branch: by the
negations of the earlier tests, and its own. There is no fix: a table is
[checked](../../Check.md#disjointness) for two rows that may both hold,
and a chain whose tests overlap would fail that check after the fix,
though it means the same. It is `pedantic`, as Clippy's lints that
suggest another form of a chain of `if` are. The refinements
below check the table that the message suggests, on one example:

```fren
set_option fren.lint.manual_table "allow" in
pub comp manual_table_written {
    in n: Int
    pub det out v: Int := if n > 10 then 2 else if n < 0 then 1 else 0
}

pub comp manual_table_fixed {
    in n: Int
    pub det out v: Int := table { n > 10 => 2, n < 0 => 1, _ => 0 }
}

refine manual_table_sound: manual_table_fixed refines manual_table_written
refine manual_table_complete: manual_table_written refines manual_table_fixed
```

`lint::manual_table` states when it fires, computing whether the tests are variant tests of
one scrutinee from the tests, and checks that the table the message
suggests has the chain's value: that of the first row whose condition
holds, or of the `_` row where none does:

```fren
-- A test of a chain of `if`: of which variant the scrutinee `x` is, or
-- another condition.
pub enum Test { VariantOf(Int, Int), Other(Int) }

pub fn scrutinee_of(t: Test): Int := match t { Test::VariantOf(x, _) => x, Test::Other(_) => -1 }

pub fn chain_value(h: Seq(Bool), v: Seq(Int), z: Int): Int :=
    if h != [] and v != [] and h[0] then v[0]
    else if h.len > 1 and v.len > 1 and h[1] then v[1]
    else if h.len > 2 and v.len > 2 and h[2] then v[2]
    else if h.len > 3 and v.len > 3 and h[3] then v[3]
    else z

pub comp manual_table {
    in tests: Seq(Test)
    in holds: Seq(Bool)      -- whether each test holds
    in branches: Seq(Int)    -- the value of each branch
    in z: Int                -- the final `else`

    assume sizes: 1 <= tests.len <= 4 and holds.len = tests.len and branches.len = tests.len

    pub det out fires?

    -- tests in the chain
    det out n_tests: Int := tests.len
    -- each is a variant test of the same scrutinee
    det out variant_tests? := (forall (s: Slot), when pos(s) < tests.len, tests[pos(s)] is Test::VariantOf(_, _)
        and scrutinee_of(tests[pos(s)]) = scrutinee_of(tests[0]))

    ensure rule: fires? iff (n_tests >= 2 and not variant_tests?)

    expect never_both: not (fires? and variant_tests?)

    expect first_row: forall (s: Slot), when pos(s) < tests.len and holds[pos(s)]
        and (forall (r: Slot), when pos(r) < pos(s), not holds[pos(r)]),
        chain_value(holds, branches, z) = branches[pos(s)]
    expect wildcard_row: when (forall (s: Slot), when pos(s) < tests.len, not holds[pos(s)]),
        chain_value(holds, branches, z) = z
}
```
