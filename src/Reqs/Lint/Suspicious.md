# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant. This chapter has the lints of names, of constraints, of
the spacing of negations and of the binders of global expectations, and
its subchapters the others: those of
[expressions](Suspicious/Expressions.md), of [methods and
indexes](Suspicious/Methods.md), of [literals](Suspicious/Literals.md) and of
[comparisons](Suspicious/Comparisons.md).

## Repeated constraints

`duplicate_constraint` fires on a constraint of a component that is
written the same as an earlier one of the component, whatever their
kinds, `assume`, `ensure` or `expect`, and on a global expectation written
the same as an earlier one of its module in the same file. It fires too
on a cover goal written the same as an earlier cover goal of the
component, but a cover goal is not compared with a constraint, since it
states a scenario rather than what holds in every behaviour. Two
constraints are written the same if their expressions are (see
[Written the same](../Lint.md#written-the-same)), and two global
expectations if all they say after their names is, binders included. It is
reported at the later one's name, and the message names the first one it
repeats.

Of two `ensure`s that say the same, the [redundancy
check](../Check.md#redundancy) reports each as following from the other,
which invites removing both; this lint says which to remove. Two
expectations that say the same are reported by no check. Where the two are
of one kind, the fix removes the later one, with a `--` comment after it
on its last line, and for a global expectation any `set_option ... in`
before it. This keeps the meaning: a constraint
that repeats one of its kind adds nothing to the component, and an
expectation that repeats one claims nothing more, and a cover goal that
repeats one is met exactly when that one is, so it checks nothing more. An `expect` that repeats
an `ensure` or an `assume` is not fixed: it tests nothing, since it follows
from what it repeats, and was probably meant to say something stronger,
which the message says. Nor is an `ensure` that repeats an `assume`, or the
reverse, since the two mean different things. `lint::duplicate_constraint`
states this:

```fren
pub mod lint

pub enum ConstraintKind { Assume, Ensure, Expect, Cover }

pub comp duplicate_constraint {
    in earlier: ConstraintKind
    in later: ConstraintKind
    in same?             -- the later is written the same as the earlier
    pub det out fires?
    pub det out fixed?   -- the fix removes the later

    -- A cover goal is compared only with cover goals.
    assume covers_apart: (earlier = ConstraintKind::Cover) iff (later = ConstraintKind::Cover)

    ensure rule: fires? iff same?
    ensure fix: fixed? iff (same? and earlier = later)

    expect weaker_kept: when later = ConstraintKind::Expect and earlier != later, not fixed?
}
```

## Negations after operators

`suspicious_unary_op_formatting` fires on a binary operator that is a
[punctuator](../Lang/Lexical.md#punctuators), directly followed by a
negation, `-`, that whitespace follows, as in `x >=- 1`, `a =- b` and `a
*- b`: the reader may take the operator and the `-` for one operator.
`-` itself is never directly followed by a `-`, which starts a comment,
and `<` never is, since `<-` is one punctuator, an
[error](../Lang/Lexical.md#punctuators). The lint looks only at the text,
in any constraint, binding, definition, constant or global expectation,
and is fixable. The fix moves the whitespace from after the `-` to before
it, so `x >=- 1` becomes `x >= -1`, and keeps the rest as it is written;
before an operand that starts with `-`, it keeps one space after the `-`
too, as in `x >= - -1`. Only whitespace moves, so the fix changes neither
the meaning nor the guards. [`fren fmt`](../Fmt.md) writes the negation so
too. `lint::suspicious_unary_op_formatting` states when it fires:

```fren
pub comp suspicious_unary_op_formatting {
    in punctuator?       -- the operator is a punctuator other than `-`
    in adjacent?         -- the `-` directly follows it
    in spaced?           -- whitespace directly follows the `-`
    pub det out fires?

    ensure rule: fires? iff (punctuator? and adjacent? and spaced?)
}
```

## Unrelated binders

`unrelated_binders` fires on a [global expectation](../Lang/Global.md)
whose binders fall into two or more groups that no single atom mentions
across. The *atoms* of an expression are its operands through `and`,
which are separate claims. Anything else is one atom, `or`, `not`, `when`,
`unless`, `iff`, `match` and `if` among them, since a connective relates
every binder it mentions: in `p.c? or q.c?`, two expectations would make
the disjunction a conjunction. Two binders are in one group when an atom
mentions both, or each is in one group with a third; a binder that no atom
mentions is left to [`unused_variables`](Unused.md#unused-variables). Such
an expectation is several independent claims run together: in `forall (a
b: c), a.y = a.x + 1 and b.y = b.x + 1`, nothing relates `a` to `b`, and a
counterexample to the claim about one names the other too. The message
names two of the groups. It has no fix: the binders may be meant to be
related, by an atom left out, or the claims may be meant to be separate
expectations. `lint::unrelated_binders` states when it fires:

```fren
pub comp unrelated_binders {
    in n_groups: Int     -- groups of the binders that atoms mention
    pub det out fires?

    assume counts: n_groups >= 0

    ensure rule: fires? iff n_groups >= 2
}
```

## Pattern tests

`irrefutable_is` fires on a [pattern
test](../Lang/Expressions.md#pattern-tests) `e is P` whose pattern matches
every value of `e`'s type: `P` is `_`, or its alternatives together cover
the type, as in `s is Shade::Light | Shade::Dark | Shade::Tinted(_)`, `b?
is true | false`, `n is ..=0 | 1..`, or `x is E::Only` where `E` has one
variant. It is decided as a `match`'s exhaustiveness is (see
[Patterns](../Lang/Patterns.md)): the pattern matches every value where
`_` after it would match none. The test is then always `true`, and the
message says so. There is no fix, as for
[`eq_op`](Suspicious/Expressions.md#operands-written-the-same): the
pattern is probably not the one meant, and writing `true` would keep the
mistake and hide it. Clippy has no exact analogue; rustc's
`irrefutable_let_patterns`, which warns by default, is the same lint for
`if let`. Fren has no `correctness` group, so it is in `suspicious`.
`lint::irrefutable_is` states when it fires:

```fren
pub comp irrefutable_is {
    in matches_every?    -- no value of the scrutinee's type is left for `_` after the pattern
    pub det out fires?

    ensure rule: fires? iff matches_every?
}
```

The refinements check the value that the message gives, for `_` and for
a pattern that names every variant of [`Shade`](Style/Comparisons.md#pattern-tests):

```fren
set_option fren.lint.irrefutable_is "allow" in
pub comp irrefutable_is_written {
    in s: Shade
    in n: Int
    pub det out wildcard? := s is _
    pub det out every? := s is Shade::Light | Shade::Dark | Shade::Tinted(_)
    pub det out ranges? := n is ..=0 | 1..
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp irrefutable_is_value {
    in s: Shade
    in n: Int
    pub det out wildcard? := true
    pub det out every? := true
    pub det out ranges? := true
}

refine irrefutable_is_sound: irrefutable_is_value refines irrefutable_is_written
refine irrefutable_is_complete: irrefutable_is_written refines irrefutable_is_value
```

## Cover goals

`trivial_cover` fires on a [cover goal](../Lang/Components.md#cover-goals)
that some behaviour meets whatever scenario it was meant to state. Lints
never ask the solver, so whether a goal can be met at all is the
[check's](../Check.md#cover-goals) to say: one that the guarantees rule
out, such as `not y?` beside `ensure r: y?`, is already an error there
(`F0615`), and a lint would only report it twice. It fires on two
mistakes that the check passes:

- a goal with a [trigger](../Lang/Components.md#triggers), `when c, d` or
  `unless c, d`: it holds wherever the trigger is false, so a behaviour in
  which the trigger is false meets it. The scenario is meant as a
  conjunction, such as `c and d`;
- a goal written the same as an assumption or a guarantee of its
  component, before it or after it, as [written](../Lint.md#written-the-same):
  every behaviour that meets the component satisfies it, so it is met
  unless the component allows no behaviour, which the [vacuity
  check](../Check.md#vacuity) reports.

A goal that mentions no variable is reported by
[`assertions_on_constants`](Style.md#constant-constraints), and one
written the same as an earlier goal by
[`duplicate_constraint`](#repeated-constraints). The lint has no fix:
which scenario was meant is not in the text. Clippy has no lint like it,
since Rust has no cover goals. `lint::trivial_cover` states when it
fires:

```fren
pub comp trivial_cover {
    in trigger?    -- the goal has a trigger
    in restates?   -- it is written the same as an assumption or a guarantee
    pub det out fires?

    ensure rule: fires? iff (trigger? or restates?)
}
```
