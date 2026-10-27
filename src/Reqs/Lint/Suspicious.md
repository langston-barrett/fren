# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant. This chapter has the lints of names, of constraints, of
the spacing of negations, of the binders of global expectations and of
definitions, and
its subchapters the others: those of
[expressions](Suspicious/Expressions.md), of [methods and
indexes](Suspicious/Methods.md), of [literals](Suspicious/Literals.md), of
[comparisons](Suspicious/Comparisons.md) and of [integers](Suspicious/Integers.md).

## Repeated constraints

`duplicate_constraint` fires on a constraint of a procedure that is
written the same as an earlier one of the procedure, whatever their
kinds, `assume`, `ensure` or `expect`, and on a global expectation written
the same as an earlier one of its module in the same file. It fires too
on a cover goal written the same as an earlier cover goal of the
procedure, but a cover goal is not compared with a constraint, since it
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
that repeats one of its kind adds nothing to the procedure, and an
expectation that repeats one claims nothing more, and a cover goal that
repeats one is met exactly when that one is, so it checks nothing more. An `expect` that repeats
an `ensure` or an `assume` is not fixed: it tests nothing, since it follows
from what it repeats, and was probably meant to say something stronger,
which the message says. Nor is an `ensure` that repeats an `assume`, or the
reverse, since the two mean different things. `lint::duplicate_constraint`
states this, from the two as [written](Meaning.md#expressions-as-written):

```fren
pub mod lint

pub enum ConstraintKind { Assume, Ensure, Expect, Cover }

pub proc duplicate_constraint(
    earlier: ConstraintKind,
    later: ConstraintKind,
    earlier_text: Scoped,    -- the earlier's expression, as written in its scope
    later_text: Scoped,      -- the later's
): (
    det same?,
    det fires?,
    det fixed?,          -- the fix removes the later
) {
    -- A cover goal is compared only with cover goals.
    assume covers_apart: (earlier = ConstraintKind::Cover) iff (later = ConstraintKind::Cover)
    out same? := earlier_text = later_text

    ensure rule: fires? iff same?
    ensure fix: fixed? iff (same? and earlier = later)

    expect weaker_kept: when later = ConstraintKind::Expect and earlier != later, not fixed?
}
```

A constraint that repeats one adds nothing because the two have the same
value in every behaviour: they are written the same, in one procedure, so
by [`written_same`](Meaning.md#expressions-as-written) they have the same
value in each environment. A global expectation is not one layer, since
it is a [quantifier](../Lang/Quantifiers.md), but the bodies of two written
the same, under the same binders, have the same value at each value of the
binders, and so the two do.
Here `p` and `q` are the constraints' root layers:

```fren
expect duplicate_constraint_value(
    d_earlier: ConstraintKind,
    d_later: ConstraintKind,
    d_earlier_text: Scoped,
    d_later_text: Scoped,
    p_program: lang::Program,
    p_head: lang::Head,
    p_env: lang::Env,
    p_values: Seq<lang::Value>,
    p_parts_mentioned: Set<lang::Mention>,
    p_undefined_parts: Set<Int>,
    q_program: lang::Program,
    q_head: lang::Head,
    q_env: lang::Env,
    q_values: Seq<lang::Value>,
    q_parts_mentioned: Set<lang::Mention>,
    q_undefined_parts: Set<Int>,
) {
    assume d_covers_apart: (d_earlier = ConstraintKind::Cover) iff (d_later = ConstraintKind::Cover)
    assume p_leaves: when p_head is lang::Head::Literal(_) | lang::Head::Bound(_) | lang::Head::Constant(_) | lang::Head::Variable(_),
        p_parts_mentioned = {}
    assume q_leaves: when q_head is lang::Head::Literal(_) | lang::Head::Bound(_) | lang::Head::Constant(_) | lang::Head::Variable(_),
        q_parts_mentioned = {}
    call d := duplicate_constraint(d_earlier, d_later, d_earlier_text, d_later_text)
    call p := lang::node(p_program, p_head, p_env, p_values, p_parts_mentioned, p_undefined_parts)
    call q := lang::node(q_program, q_head, q_env, q_values, q_parts_mentioned, q_undefined_parts)
    expect duplicate_constraint_value: when d.fires? and p.env = q.env and p.program = q.program and p.head = written_head(d.earlier_text)
        and p.values = written_values(p.env, d.earlier_text) and q.head = written_head(d.later_text)
        and q.values = written_values(q.env, d.later_text),
        p.value = q.value
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
in any constraint, argument, binding, definition, constant or global expectation,
and is fixable. The fix moves the whitespace from after the `-` to before
it, so `x >=- 1` becomes `x >= -1`, and keeps the rest as it is written;
before an operand that starts with `-`, it keeps one space after the `-`
too, as in `x >= - -1`. Only whitespace moves, so the fix changes neither
the meaning nor the guards. [`fren fmt`](../Fmt.md) writes the negation so
too. `lint::suspicious_unary_op_formatting` states when it fires:

```fren
set_option fren.evidence "enumerated" in
pub proc suspicious_unary_op_formatting(
    punctuator?,         -- the operator is a punctuator other than `-`
    adjacent?,           -- the `-` directly follows it
    spaced?,             -- whitespace directly follows the `-`
): (det fires?) {
    ensure rule: fires? iff (punctuator? and adjacent? and spaced?)
}
```

## Unrelated binders

`unrelated_binders` fires on a [global expectation](../Lang/Global.md)
whose calls fall into two or more groups that nothing relates. The *atoms*
of an expression are its operands through `and`, which are separate
claims. Anything else is one atom, `or`, `not`, `when`, `unless`, `iff`,
`match` and `if` among them, since a connective relates every call it
mentions: in `p.c? or q.c?`, two expectations would make the disjunction
a conjunction. Two calls are in one group when an atom of one of the
global expectation's constraints relates both, by mentioning each or a
parameter that its arguments mention; when one's arguments mention the
other, or a parameter that the other's arguments mention too; or when
each is in one group with a third. A call that nothing relates is in no
group. Such an expectation is several independent claims run together:
in `expect e(x: Int, z: Int) { call a := c(x) call b := c(z) expect e:
a.y = x + 1 and b.y = z + 1 }`, nothing relates `a` to `b`, and a
counterexample to the claim about one names the other too. The message
names two of the groups. It has no fix: the calls may be meant to be
related, by an atom or an argument left out, or the claims may be meant
to be separate global expectations. `lint::unrelated_binders` states when it fires:

```fren
pub proc unrelated_binders(
    n_groups: Nat,       -- groups of the calls that atoms, arguments and parameters relate
): (det fires?) {
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
set_option fren.evidence "enumerated" in
pub proc irrefutable_is(
    matches_every?,      -- no value of the scrutinee's type is left for `_` after the pattern
): (det fires?) {
    ensure rule: fires? iff matches_every?
}
```

The refinements check the value that the message gives, for `_` and for
a pattern that names every variant of [`Shade`](Style/Comparisons.md#pattern-tests):

```fren
set_option fren.lint.irrefutable_is "allow" in
pub proc irrefutable_is_written(s: Shade, n: Int): (det wildcard?, det every?, det ranges?) {
    out wildcard? := s is _
    out every? := s is Shade::Light | Shade::Dark | Shade::Tinted(_)
    out ranges? := n is ..=0 | 1..
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub proc irrefutable_is_value(s: Shade, n: Int): (det wildcard?, det every?, det ranges?) {
    out wildcard? := true
    out every? := true
    out ranges? := true
}

refine irrefutable_is_sound: irrefutable_is_value refines irrefutable_is_written
refine irrefutable_is_complete: irrefutable_is_written refines irrefutable_is_value
```

## Cover goals

`trivial_cover` fires on a [cover goal](../Lang/Procedures.md#cover-goals)
that some behaviour meets whatever scenario it was meant to state. Lints
never ask the solver, so whether a goal can be met at all is the
[check's](../Check.md#cover-goals) to say: one that the guarantees rule
out, such as `not y?` beside `ensure r: y?`, is already an error there
(`F0615`), and a lint would only report it twice. It fires on two
mistakes that the check passes:

- a goal with a [trigger](../Lang/Procedures.md#triggers), `when c, d` or
  `unless c, d`: it holds wherever the trigger is false, so a behaviour in
  which the trigger is false meets it. The scenario is meant as a
  conjunction, such as `c and d`;
- a goal written the same as an assumption or a guarantee of its
  procedure, before it or after it, as [written](../Lint.md#written-the-same):
  every behaviour that meets the procedure satisfies it, so it is met
  unless the procedure allows no behaviour, which the [vacuity
  check](../Check.md#vacuity) reports.

A goal that mentions no variable is reported by
[`assertions_on_constants`](Style.md#constant-constraints), and one
written the same as an earlier goal by
[`duplicate_constraint`](#repeated-constraints). The lint has no fix:
which scenario was meant is not in the text. Clippy has no lint like it,
since Rust has no cover goals. `lint::trivial_cover` states when it
fires:

```fren
set_option fren.evidence "enumerated" in
pub proc trivial_cover(
    trigger?,      -- the goal has a trigger
    restates?,     -- it is written the same as an assumption or a guarantee
): (det fires?) {
    ensure rule: fires? iff (trigger? or restates?)
}
```

## Redundant definitions

`redundant_locals` fires on a definition of a [`let` or
`where`](../Lang/Let.md) clause that names again what it
[hides](../Lang/Procedures.md#shadowing), `x! := x`, with no type written.
The `x` of the definition means what `x!` hides, so `x` means the same
with the definition and without it, and the definition was probably meant
to be another expression, such as `x! := x + 1`, perhaps left unfinished.
The message suggests writing that expression, or removing the definition,
with the `,` after it, or before it if it is the last, and the whole
clause, leaving its body, if it is its only one: `let x! := x in x > 0`
would become `x > 0`. `fren fix` does not apply that removal, as it would
hide the unfinished edit rather than finish it. The removal keeps the
meaning, since a name stands for its definition
([Meaning](../Lang/Let.md#meaning)), and the guards, since the definition
has no index of its own; a later `x!` of the clause hides the `x` it hid
instead, which is the same value, so it still hides something. A
definition with a written type, `x!: Int := x`, may say more than `x`
does, where `x` is a `Nat`, and is left as it is.

Clippy's `redundant_locals`, of `let x = x;`, is in `correctness`, which
is denied by default; here it is in `suspicious`, and `warn` (see
[Groups](../Lint.md#groups)). `x := x` in a binding or a record literal,
which `x` alone writes, is [`redundant_bindings`](Style.md#bindings)'s.
The refinements after the procedure check that the removal the message
suggests keeps the meaning. `lint::redundant_locals` states when it fires, on the definition in the
[model of scopes](Unused.md#scopes): its name, whether it is written with
`!` and with a type, and the tree of its expression, whose root is then a
path of that one name with no parts:

```fren
pub proc redundant_locals(name: Local, bang?, annotated?, value: Tree): (det fires?) {
    use lint::{Local, Tree}

    ensure rule: fires? iff (bang? and not annotated? and (value.root, name) in value.paths
        and value.children.image({value.root}) = {})

    expect more: when value.children != {} and value.root in value.children.domain, not fires?
}
```

The refinements check the suggested removal, of a `let` of one
definition, of the first of two, of the last of two, and of a `where`
clause:

```fren
set_option fren.lint.redundant_locals "allow" in
pub proc redundant_locals_written(x: Int, y: Int): (
    det only?,
    det first: Int,
    det last: Int,
    det clause: Int,
) {
    out only? := let x! := x in x > 0
    out first := let x! := x, k := 2 in x * k
    out last := let k := 2, y! := y in y * k
    out clause := x + y where y! := y
}

pub proc redundant_locals_fixed(x: Int, y: Int): (
    det only?,
    det first: Int,
    det last: Int,
    det clause: Int,
) {
    out only? := x > 0
    out first := let k := 2 in x * k
    out last := let k := 2 in y * k
    out clause := x + y
}

refine redundant_locals_sound: redundant_locals_fixed refines redundant_locals_written
refine redundant_locals_complete: redundant_locals_written refines redundant_locals_fixed
```
