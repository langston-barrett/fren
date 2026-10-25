# Matches

## Trivial matches

`trivial_match` fires on a `match` of one arm, whose pattern binds no name:
`_`, the variant of an enumeration with one variant, without a payload or
with `_` for each of its values, or an or-pattern. A `match` is exhaustive
(see [Matches](../../Lang/Expressions.md#matches)), so that arm matches every
value of the scrutinee, and the `match` is the arm's body. Like Clippy's
`match_single_binding`, it is in `complexity`, and it is fixable. The fix
replaces the `match` with the body, which keeps the text it is written
with, and is put in parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes):
`x = 2 * match e { _ =>
x - 1 }` becomes `x = 2 * (x - 1)`. The body's guard is the guard of the
`match` and its pattern's test, which every value passes, so it is the
guard of the `match`, where the fix puts the body. The fix only drops the
scrutinee, which removes what was evaluated, so no guard is weaker.
`lint::trivial_match` states when it fires:

```fren
pub mod lint

pub comp trivial_match {
    in n_arms: Int
    in binds?            -- the first arm's pattern binds a name
    pub det out fires?

    assume counts: n_arms >= 1

    req rule: fires? iff (n_arms = 1 and not binds?)
}
```

## Matches that give back the scrutinee

`needless_match` fires on a `match` each of whose arms gives back the
value it matches: `E::V => E::V`, for a variant without a payload, or
`E::V(a, b) => E::V(a, b)`, whose body builds the variant that its
pattern names, with the pattern's binders, in order and none of them `_`,
written the same as its arguments. The variants are compared as they
resolve, so `V`, brought into scope by `use`, is `E::V`. An arm with an
or-pattern gives back nothing, and a `_` arm gives back its value only if
its body is written the same as the scrutinee. It does not fire where
[`trivial_match`](#trivial-matches) does, whose fix is the body. It is
fixable: the fix replaces the `match` with its scrutinee, which keeps the
text it is written with, but for parentheses around it, and is put in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes): `t = match (s) {
...}` becomes `t = s`.

The `match` has the value of the body of the first arm that matches.
`E::V(a, b)` matches only a scrutinee that is `V` with the payload `a` and
`b`, so the body `E::V(a, b)` is the scrutinee, as is the body of a `_`
arm written the same as it. The `match` and its scrutinee have the same
type, since each arm builds a value of the scrutinee's enumeration. The
fix evaluates the scrutinee where the `match` did, under its guard, and
only drops the bodies, which index nothing, so no guard is weaker.
`lint::needless_match` states when it fires:

```fren
pub comp needless_match {
    in given_back?       -- each arm but `_` gives back the variant it matches, with its binders in order
    in wildcard?         -- there is a `_` arm
    in scrutinee_back?   -- the `_` arm's body is written the same as the scrutinee
    in trivial?          -- `trivial_match` fires on the `match`
    pub det out fires?

    req rule: fires? iff (given_back? and (not wildcard? or scrutinee_back?) and not trivial?)
}
```
