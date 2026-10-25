# Pedantic

The lints of the `pedantic` group are matters of judgement, or would fire
on much that reads well as it is, so they are `allow` by default.

## Membership chains

`membership_chain`, `allow` by default, fires on a disjunction of
three or more equations of one expression with others, `x = a or x = b or x
= c`, whose fix is `x in {a, b, c}`, and on its De Morgan dual, a
conjunction of three or more disequations, `x != a and x != b and x != c`,
whose fix is `not x in {a, b, c}`.

In the chain, each operand is guarded by those before it (see
[Expressions](../Lang/Expressions.md#sequences)): `x = b` by `not x = a`, and
`x != b` by `x != a`. In the fix, each value is evaluated where the chain
is. A comparison of `x` with values, with `=`, `!=` or `in`, is defined
wherever `x` and the values are, and `x` and the first value are evaluated
where the chain is in either form, so the fix keeps their guards, but not
those of the later values. So the lint does not fire if a value after the
first indexes a sequence, which might be out of range: `x = 1 or x = q[0] or
x = 2` is left as it is. `lint::membership_chain` states when it fires,
from the number of operands of the chain, whether they all equate, or
disequate, the same expression, written the same way, on their left, and
whether a later value indexes a sequence:

```fren
pub mod lint

pub comp membership_chain {
    in n: Int            -- operands of the chain of `or`, or of `and`
    in same_left?        -- each is an equation, or for `and` a disequation, with the same left operand
    in later_indexes?    -- a value after the first indexes a sequence
    pub det out fires?

    assume counts: n >= 2

    req rule: fires? iff (same_left? and n >= 3 and not later_indexes?)
}
```

`lint::membership_chain_keeps_meaning` states both fixes as laws (see
[Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.membership_chain "expect" in
pub comp membership_chain_keeps_meaning {
    in x: Int
    in y: Int
    in z: Int
    in w: Int

    expect chain: (x = y or x = z or x = w) iff x in {y, z, w}
    expect dual: (x != y and x != z and x != w) iff not x in {y, z, w}
}
```

## Definable outputs

`definable_output`, `allow` by default, fires on an output, not defined,
that exactly one requirement constrains, unconditionally, as `x = e` or
`x? iff e`, where `e` does not mention `x`: the requirement could be its
definition. [`lint::output_lints`](Complexity.md#constant-outputs) states
when it fires, with `constant_output`.

## Negated conditions

`if_not_else`, `allow` by default, fires on `if C then A else B` where
`C` is a [negation](Style.md#conditionals): `if not C then A else B`
becomes `if C then B else A`, and `if a != b then A else B` becomes `if a
= b then B else A`. It does not fire when `B` is itself an `if`, since
swapping the branches would break a chain of `else if`. `A` is guarded by
`not C`, and `B` by `C`, before and after. It is `pedantic`, as its Clippy
counterpart is. It fires in the same places as the [lints on
conditionals](Style.md#conditionals) of the `style` group, and writes its
operands as they do. `lint::if_not_else` states when it fires, from the
[`lint::Head`](Style.md#conditionals) of the condition and of the `else`
branch:

```fren
pub comp if_not_else {
    in condition: Head
    in else_branch: Head
    pub det out fires?

    req rule: fires? iff (condition in {Head::Not, Head::Unequal} and else_branch != Head::If)

    expect chain: when else_branch = Head::If, not fires?
}
```

## Matches

`match_same_arms` and `wildcard_single_variant` look at the arms of a
[`match`](../Lang/Expressions.md#matches) as written, as
[`match_like_membership`](Style.md#matches-that-are-memberships) does.
Both are fixable.

`match_same_arms`, `allow` by default, fires on two arms whose bodies are
[written the same](../Lint.md#written-the-same), and whose patterns bind no names.
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
  them](../Lint.md#parentheses-in-fixes).

Neither changes what the `match` means. No variant is named twice, and
`_` is the last arm, so a variant is matched by the same body after the
fix as before, whatever the order of the arms. A body's guard is the test
of its arm's pattern, and after the fix it is the disjunction of the
guards of the arms it replaces, under each of which the body was already
evaluated. A pattern that binds a name is not merged, since its body
could mention the name. `lint::match_same_arms` states when it fires on
two arms, and the fix of their group:

```fren
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
of which variant a scrutinee `x` is, `x = E::V`, `x in {E::V, E::W}`, or an
`or` of such tests. The scrutinee is [written the
same](../Lint.md#written-the-same) in every test, and each variant has no payload: `x = E::V(a)` compares
the payload too. The chain starts at an `if` that is not the `else` branch
of another. Its fix is a [`match`](../Lang/Expressions.md#matches), `match x {
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
that is a top-level `when` or `unless`, which an arm's body cannot be, is
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

## Boolean equality

`bool_equality`, `allow` by default, follows the rules of the [lints on
operators](Complexity.md#comparisons) for its fix, and fires on `a = b`
where both operands
are `Bool`s, and its fix is `a iff b`, which means the same and says that
the two are equivalent. `iff` binds more loosely than `=`, so the fix may
need parentheses that the equation did not: `a? = b? and c?` becomes `(a?
iff b?) and c?`. The fix evaluates the same operands under the same guard.
It does not fire on `!=`, or where an operand is `true` or `false`, which
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions) simplifies:

```fren
pub comp bool_equality {
    use self::Comparison::Eq
    in op: Comparison
    in bools?            -- both operands are `Bool`s
    in literal?          -- an operand is `true` or `false`
    pub det out fires?

    req rule: fires? iff (op = Eq and bools? and not literal?)
}
```

## Relations to one value

`zero_sized_map_values`, `allow` by default, fires on a relation type
`Rel(A, B)`, wherever a type is written, whose `B` is an enumeration with
one variant and no payload, and so has exactly one value. Such a relation
pairs each `A` it relates with that one value, so it says only which `A`s it
relates, as `Set(A)` does, which the message suggests. It has no fix: the
expressions that build and read the relation would change too.
`lint::zero_sized_map_values` states when it fires:

```fren
pub comp zero_sized_map_values {
    in enum?             -- `B` is an enumeration
    in n_variants: Int   -- its variants
    in payload?          -- one of them has a payload
    pub det out fires?

    assume counts: n_variants >= 0

    req rule: fires? iff (enum? and n_variants = 1 and not payload?)
}
```

## Names

`many_single_char_names` and `similar_names` look at the names that an
item declares: the variables and instances of a component, the
parameters of a defined function, the binders of a global expectation, and
the binders of the `match` arms in each of them. Each name counts once,
however many times it is declared: `x` and a later `x!` that
[shadows](../Lang/Components.md#shadowing) it are one name. A final `?` is
not counted. Neither lint has a fix: only the writer knows what a name stands
for.

`many_single_char_names`, `allow` by default, fires on a component,
function or global expectation that declares more than four names of one
character, as Clippy's does by default. Its message is reported at the
item's name, and lists them. `lint::many_single_char_names` states when it
fires:

```fren
pub comp many_single_char_names {
    in n: Int            -- names of one character that the item declares
    pub det out fires?

    assume counts: n >= 0

    req rule: fires? iff n > 4
}
```

`similar_names`, `allow` by default, fires on two names that one item
declares, each of three or more characters, one of which is the other
with one character substituted, inserted or deleted, such as `level` and
`levels`, or `user` and `used`. Its message is reported at the later of
the two, once for each name, and names the earlier. Following Clippy, it
does not fire on names that differ only in a digit, such as `x1` and
`x2`, or in a substituted character that is a word of its own in both,
between `_`s or the name's ends, such as `a_mentions?` and `b_mentions?`:
both name a series on purpose. Nor does it fire on the pairs that Clippy
allows and that apply to Fren: `lhs` and `rhs`, `set` and `get`, `args` and
`arms`, and `lit` and `lint`. `lint::similar_names` states when it fires:

```fren
pub comp similar_names {
    in len_a: Int        -- characters of each name, without a final `?`
    in len_b: Int
    in one_edit?         -- one is the other with one character substituted, inserted or deleted
    in digits?           -- the characters that differ are digits
    in word?             -- a character is substituted for another, each a word of its name
    in allowed?          -- the pair is one that Clippy allows, such as `lhs` and `rhs`
    pub det out fires?

    assume counts: len_a >= 0 and len_b >= 0

    req rule: fires? iff (len_a >= 3 and len_b >= 3 and one_edit? and not digits? and not word? and not allowed?)

    expect series: when digits?, not fires?
}
```

## Long items

`too_many_lines`, `allow` by default, fires on a component or defined
function of more than 100 lines, as Clippy's does by default. Its lines
run from the line of its name to its end: a component's closing `}`, and
a function's last token, which is the `)` when its body is in parentheses.
A line counts if it has a character other than whitespace outside
[comments](../Lang/Lexical.md#comments):

- a blank line does not count, nor does one of only whitespace;
- a line comment, `--` to the end of the line, does not count, so a line
  of only a comment does not, but a line of code before one does;
- a block comment, `/-` to `-/`, may span lines and nests, `/- /- -/ -/`,
  and only what is outside it counts, so code after a `-/` does;
- a `--` or `/-` in a string literal starts no comment.

Its message is reported at the item's name. It has no fix: how to split an
item into smaller ones, as instances or functions, is the writer's choice.
`lint::too_many_lines` states when it fires:

```fren
pub comp too_many_lines {
    in n_lines: Int      -- lines of the item with code
    pub det out fires?

    assume counts: n_lines >= 0

    req rule: fires? iff n_lines > 100
}
```
