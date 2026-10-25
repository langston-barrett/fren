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

    req rule: fires? iff (same_body? and not binds?)
    req group_fix: fix = if all? then ArmsFix::Replace else if wildcard? then ArmsFix::Remove else ArmsFix::Merge
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
    pub det out fires?

    assume reachable: n_matched >= 1

    req rule: fires? iff n_matched = 1
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
    pub det out fires?
    pub det out wildcard?  -- the fix keeps the final `else`, as the `_` arm

    assume counts: n_tests >= 1

    req rule: fires? iff (variant_tests? and n_tests >= 2 and n_repeated = 0)
    req fix: wildcard? iff n_untested > 0
}
```

`case_split_reqs`, `allow` by default, fires on a component with two or
more requirements `when T, y = e`, or `when T, y? iff e`, of one output
`y`, whose conditions `T` are variant tests of one scrutinee `x`, naming no
variant twice. Together they say what one requirement `y = match x { ...
}` says, with an arm for each, and `_ => y` if some variant is not tested,
for which they leave `y` unconstrained. Its message is reported at the
second of them, names them all, and suggests that requirement. A
requirement `unless T, y = e` is not one of them: it constrains `y` for the
variants that `T` does not name. As in a `match` arm, `e` is guarded by
`T`. There is no fix: traces, claims and `impl`s refer to requirements by
name, so merging them changes the structure of the spec, not only its text.
`lint::case_split_reqs` states when it fires:

```fren
pub comp case_split_reqs {
    in n_cases: Nat      -- requirements `when T, y = e` of one output, whose `T` are variant tests of one scrutinee
    in n_repeated: Nat   -- times a test names a variant that it, or an earlier test, names before
    pub det out fires?

    req rule: fires? iff (n_cases >= 2 and n_repeated = 0)
}
```

## One variant and `_`

`single_match_else`, `allow` by default, fires on a `match` of two arms,
of which the first names one variant without a payload, and so binds
nothing, and the second is `_`: `match x { E::V => a, _ => b }`. Its fix
is `if x is E::V then a else b`, with the [pattern
test](../../Lang/Expressions.md#pattern-tests) written as the pattern is,
and the bodies and the scrutinee as they are written. The `if` is in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes),
since it ends in its `else` branch, and so is the scrutinee, where `is`
requires it. `x is E::V` is `match x { E::V => true, _ => false }`, so it
holds exactly where the pattern matches, and the `if` takes the branch
that the `match` takes. The fix keeps the guards: `a` is guarded by the
test of the pattern, which is `x is E::V`, and `b` by its negation, as the
branches of the `if` are. The scrutinee is evaluated where it was.

It does not fire where another lint reports the `match`:
[`match_like_membership`](../Style.md#matches-that-are-memberships), where
the bodies are `true` and `false`;
[`needless_match`](../Complexity/Matches.md#matches-that-give-back-the-scrutinee),
where both arms give back the scrutinee; `match_same_arms`, where the
bodies are written the same; and
[`trivial_match`](../Complexity/Matches.md#trivial-matches), which reports
a `match` of one arm. Where the `match` has a comment, the lint has no
fix: the fix writes the `if` from the scrutinee, the pattern and the
bodies, and would drop it. Its Clippy counterpart, of the same name, is
`pedantic` too. `lint::single_match_else` states when it fires:

```fren
pub comp single_match_else {
    in n_arms: Int
    in one_variant?      -- the first arm's pattern is one variant without a payload
    in wildcard?         -- the second arm is `_`
    in other?            -- `match_like_membership`, `needless_match`, `trivial_match` or `match_same_arms` fires on the `match`
    pub det out fires?

    assume counts: n_arms >= 1

    req rule: fires? iff (n_arms = 2 and one_variant? and wildcard? and not other?)
}

pub enum Light { Red, Amber, Green }

set_option fren.lint.single_match_else "allow" in
pub comp single_match_else_written {
    in light: Light
    in a: Int
    in b: Int
    pub det out v: Int := match light { Light::Red => a, _ => b }
}

pub comp single_match_else_fixed {
    in light: Light
    in a: Int
    in b: Int
    pub det out v: Int := if light is Light::Red then a else b
}

refine single_match_else_sound: single_match_else_fixed refines single_match_else_written
refine single_match_else_complete: single_match_else_written refines single_match_else_fixed
```
