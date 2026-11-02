# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant. This chapter has the lints of names, of constraints, of
the spacing of negations, of the calls of global expectations and of
definitions, and
its subchapters the others: those of
[expressions](Suspicious/Expressions.md), of [methods and
indexes](Suspicious/Methods.md), of [literals](Suspicious/Literals.md), of
[comparisons](Suspicious/Comparisons.md) and of [integers](Suspicious/Integers.md).

## Repeated constraints

`duplicate_constraint` fires on a constraint of a procedure that is
written the same as an earlier one of the procedure, whatever their
kinds, `assume`, `ensure` or `expect`, and on a global expectation in the
[short form](../Lang/Global.md#the-short-form) written the same as an
earlier one of its module in the same file. A global expectation with a
block is checked as a procedure is: its constraints are compared with each
other. It fires too
on a cover goal written the same as an earlier cover goal of the
procedure, but a cover goal is not compared with a constraint, since it
states a scenario rather than what holds in every behaviour. Two
constraints are written the same if their expressions are (see
[Written the same](../Lint.md#written-the-same)), and two global
expectations in the short form if all they say after their names is, a
leading `forall`'s binders included. It is
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

### Written identity of labelled clauses

Splitting `ensure when decision is RetryAfter(d), and { honor_server:
d >= retry_after, backoff: d >= Seconds(2 * attempt), latency_budget:
d <= MAX_DELAY }` creates three guarded constraints. Their shared outer
source range is not their written identity. Each identity retains its
own expression plus the ordered guard/lexical-binding wrappers, with the
names resolved in that scope. Labels and containing source ranges do not
make unequal expressions equal. Different guards or bindings also keep
otherwise equal bodies distinct. Predicate expansion likewise must not
replace distinct written calls or member expressions by a common definition
range or an empty synthetic source string.

The following model contains the actual scoped expression and ordered
wrappers; it deliberately keeps the label outside the identity.

```fren
pub enum ClauseWrapper { When(Scoped), Unless(Scoped), Let(Scoped) }
pub struct ClauseIdentity { wrappers: Seq<ClauseWrapper>, expression: Scoped }
pub struct LabelledClause { label: String, identity: ClauseIdentity }

pub proc labelled_clause_identity(earlier: LabelledClause, later: LabelledClause):
    (det same?) {
        out same? := earlier.identity = later.identity
        expect different_expression: when earlier.identity.expression != later.identity.expression,
            not same?
        expect different_wrapper: when earlier.identity.wrappers != later.identity.wrappers,
            not same?
        expect label_is_not_expression: when earlier.identity = later.identity, same?
    }
```

For an actual repeated member of one conjunction block, the fix removes
only that member's label, expression, separator and trailing line comment.
It retains the shared guard, bindings, block delimiters and all other
members. A generated clause without an independently removable written
member is diagnosed without a deletion fix; deleting its enclosing source
range could remove different constraints. Different expressions receive
neither this diagnostic nor its deletion fix.

A constraint that repeats one adds nothing because the two have the same
value in every behaviour: they are written the same, in one procedure, so
by [`written_same`](Meaning.md#expressions-as-written) they have the same
value in each environment. A global expectation is not one [expression of the semantics](../Lang/Semantics.md#expressions), since
it is a [quantifier](../Lang/Quantifiers.md), but the bodies of two written
the same, under the same binders, have the same value at each value of the
binders, and so the two do:

```fren
expect duplicate_constraint_value(
    d_earlier: ConstraintKind,
    d_later: ConstraintKind,
    d_earlier_text: Scoped,
    d_later_text: Scoped,
    i: lang::Interp,
    env: lang::Env,
) {
    assume d_covers_apart: (d_earlier = ConstraintKind::Cover) iff (d_later = ConstraintKind::Cover)
    call d := duplicate_constraint(d_earlier, d_later, d_earlier_text, d_later_text)
    expect duplicate_constraint_value: when d.fires?,
        lang::eval(i, env, written(d.earlier_text)) = lang::eval(i, env, written(d.later_text))
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
each is in one group with a third. A call that no atom mentions, and that
no argument or parameter relates to another, is in no group, and is left
to [`unused_variables`](Unused.md#unused-variables). Such an expectation is several independent claims run together:
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

expect irrefutable_is_sound(s: lint::Shade, n: Int) {
    use lint
    call concrete := irrefutable_is_value(s, n)
    refines concrete irrefutable_is_written(s, n)
}
expect irrefutable_is_complete(s: lint::Shade, n: Int) {
    use lint
    call concrete := irrefutable_is_written(s, n)
    refines concrete irrefutable_is_value(s, n)
}
```

### Pattern tests, over the syntax of the semantics

In the [syntax of the semantics](../Lang/Semantics.md#abstract-syntax), a
pattern test is `Is(s, p)`. Without types, the model knows only of `_`
as a pattern that matches every value. That alternatives cover
a type, or that an enumeration has one variant, is a fact about the
scrutinee's type, which the static rules decide and the model cannot
state. `irrefutable_is_fires?` fires on a test of `_`, and the message
says that it is `true`. As for
[`eq_op`](Suspicious/Expressions.md#operands-written-the-same-over-the-syntax-of-the-semantics),
there is no fix, and what the lint states is that its message is right:

```fren
pub fn irrefutable_is_fires?<V>(e: lang::Expr<V>) := e is lang::Expr::Is(_, lang::Pattern::Wildcard)
```

`lint::irrefutable_is` binds this to the linter: where the pattern is `_`,
the front ends read it as matching every value (`read`), and the linter
fires, as the function does. On the other patterns that it fires on, the
function does not. That the front ends read the
pattern so, and the `true` that the message gives, which is not an
output of `lint::irrefutable_is`, are trusted, and checked by the ui
tests in `test/ui/lints/pattern_tests_chains.fren`:

```fren
expect irrefutable_is_elaborated(
    matches_every?,
    s: lang::Expr<lang::Id>,
    p: lang::Pattern<lang::Id>,
) {
    assume read: when p = lang::Pattern::Wildcard, matches_every?

    call t := irrefutable_is(matches_every?)

    expect fires: when p = lang::Pattern::Wildcard, t.fires? and irrefutable_is_fires?(lang::Expr::Is(s, p))
}
```

Where it fires, the message agrees with the test, in every interpretation
and environment: the test is `true` wherever the scrutinee is
well-defined, and undefined elsewhere. `src/Impls/Rewrites.lean` proves
this in Lean, for every expression, interpretation and environment;
`fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc irrefutable_is_said_agrees(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure said: when irrefutable_is_fires?(e),
        agrees?(
            lang::eval(i, env, lang::Expr::Literal(lang::Value::True)),
            lang::eval(i, env, e)
        )
}
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

expect redundant_locals_sound(x: Int, y: Int) {
    call concrete := redundant_locals_fixed(x, y)
    refines concrete redundant_locals_written(x, y)
}
expect redundant_locals_complete(x: Int, y: Int) {
    call concrete := redundant_locals_written(x, y)
    refines concrete redundant_locals_fixed(x, y)
}
```
