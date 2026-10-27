# Local definitions

`let` and `where` name expressions within one expression, so that a long
condition is written once:

```text
ensure heat: when cold?, mode = Heat
    where cold? := temp < target - margin, margin := 2

expect bounded: let lo := base - 2, hi := base + 2 in lo <= x and x <= hi
```

```
expr       := ... | "let" definition ("," definition)* "in" expr
top        := expr ["where" definition ("," definition)*]
definition := DECL [":" type] ":=" iff
```

A `let` is an [expression](Expressions.md), at the level of `when`: its
body extends as far right as possible, and a `let` that is the operand of
an operator is written in parentheses. A `where` clause is not an
expression: it follows the whole expression of an assumption, guarantee,
expectation or [cover goal](Procedures.md#cover-goals), a [global expectation](Global.md) (after its `forall`), a
[definition](Procedures.md#definitions) of a result or `let` variable, a
[function's](Items.md#defined-functions) body or a
[constant's](Items.md#constants) value, and nothing else. It binds most
loosely, so in `when C, D where x := e`, `x` is in scope in both `C` and
`D`. The two forms share every other rule: `top where ds` means `let ds
in top`.

## Definitions

A definition `x := e` names the value of `e`. Its type is that of `e`,
and may be written, `x: T := e`, in which case `e` must have type `T`.
A written type may be a [`Nat`](Types.md#natural-numbers), and an `Int`
then accepts a `Nat`, as anywhere an `Int` is expected. It may be a
[pattern type](Types.md#pattern-types), as in `low: Byte := x - 1`, which
compares as its base type does, with the obligation that `e` matches its
pattern, which the [pattern-type check](../Check.md#pattern-types) asks
where the definition is written. A definition is substituted, so its
name brings no constraint of its own: its value is `e`, which the
obligation says matches.
The name follows the [Boolean names](Types.md#boolean-names) rule for its
type, as a binder of a pattern does: `cold? := temp < 40`, and `n := 3`.
`lang::definition_type` states this:

```fren
pub mod lang

pub proc definition_type(
    annotated?,          -- written `x: T := e`
    annotation: Ty,      -- `T`, if written
    value: Ty,           -- the type of `e`
): (
    det accepted?,
    det ty: Ty,          -- the type of the name
) {
    ensure rule: accepted? iff (not annotated? or annotation = value)
    ensure typed: ty = value

    expect inferred: unless annotated?, accepted?
    expect checked: when annotated? and accepted?, ty = annotation
    expect mismatch: when annotated? and annotation != value, not accepted?
}
```

The definitions of one clause are read in order. Each may mention the
ones before it, but neither itself nor a later one, so definitions are
never recursive, and a name is declared before it is used, as for
[functions](Items.md#defined-functions). The body of a `let`, or the
expression before a `where`, may mention all of them.
`lang::definition_order` states when a name means a definition of its
clause, from the definition's position and that of the definition the
name is written in, or the number of definitions for the body:

```fren
pub proc definition_order(
    n: Int,              -- the number of definitions of the clause
    k_def: Nat,          -- the position of the definition named
    k_use: Nat,          -- the position of the definition the name is in, or `n` in the body
): (
    det means?,          -- the name means the definition
) {
    assume positions: k_def < n and k_use <= n

    ensure rule: means? iff k_def < k_use

    expect body_sees_all: when k_use = n, means?
    expect not_itself: when k_use = k_def, not means?
    expect not_later: when k_use < k_def, not means?
}
```

Where a name does not mean a definition of its clause, it means what it
would without the clause: in `where x! := x + 1`, the `x` of the
definition is the variable that `x!` hides. A name that would otherwise
mean nothing, but is defined by this or a later definition, is reported as
used before its definition.

A definition's name may [shadow](Procedures.md#shadowing) another,
written with `!`: a variable, a parameter, a binder, a
[closure's](HigherOrder.md#arguments) parameter, a constant, a
function, a variant, a name of an enclosing `let` or `where`, or an
earlier name of the same clause, as in `let x := 1, x! := x + 1 in x`. A
mention of it in its scope is not a mention of what it shadows.

## Parentheses

A definition ends at the next top-level `,`, so its expression is not a
`when`, `unless`, `let` or [quantifier](Quantifiers.md), whose body would
run on into the next definition: those are written in parentheses, as in
`let all_off? := (forall (m: Mode), m = Mode::Off) in ...`. The body of a
`let`, like a quantifier's, may be any of them without parentheses, so a
quantifier's body may be a `let`, and a `let`'s body a quantifier. In a `let`, `in` ends the last
definition, so a membership at the top level of a definition is written
in parentheses too: `let b? := (x in s) in ...`, just as a
[`match`](Expressions.md#matches) scrutinee is not a record literal. The
top level is outside brackets, the condition and `then` branch of an
`if`, and a `match`'s scrutinee, which are all delimited, so `in` is a
membership there. A `let` nested in a definition, within those, ends its
own definitions with its own `in`, and its body keeps the restriction of
the definition it is in: in `let a := if p? then 1 else let b := 2 in b
in a > 0`, the second `in` ends `b`'s definitions and the third `a`'s.
`let b? := x in s in t` reads as `let b? := x in (s in t)`, and if its
last definition or its body, a membership right after the `in`, does not
type, the message says to write the membership in parentheses.
`lang::definition_form` states which forms a definition's expression may
take at its top level:

```fren
-- `OpenEnded` is `when`, `unless`, `let` or a quantifier, whose body extends
-- as far right as possible; `Membership` is `a in s` outside brackets; `Plain` is any other.
pub enum DefinitionForm { Plain, Membership, OpenEnded }

set_option fren.evidence "enumerated" in
pub proc definition_form(
    form: DefinitionForm,
    in_let?,             -- a definition of a `let`, rather than of a `where` clause
): (det accepted?) {
    use self::DefinitionForm::{Membership, OpenEnded, Plain}

    ensure rule: accepted? iff (form = Plain or (form = Membership and not in_let?))

    expect plain: when form = Plain, accepted?
    expect open_ended: when form = OpenEnded, not accepted?
    expect where_membership: when form = Membership and not in_let?, accepted?
    expect let_membership: when form = Membership and in_let?, not accepted?
}
```

For the same reason as a `when`, a `let` is not the top-level body of a
`match` arm, nor an argument of a call or the expression of a record
literal's field.

## Meaning

A name stands for its definition: `let x := e in b` means `b` with each
`x` that means the definition replaced by `e`, and so does `b where x :=
e`. So a definition that nothing mentions has no effect, and the index of
a [sequence](Expressions.md#sequences) in a definition is guarded by the
conditions where the name is mentioned, not where it is defined.

Mentioning a name counts as mentioning everything its definition
mentions, as for a [`match` binder](Expressions.md#matches), for the rules
of [Calls](Calls.md#call-variables), of [function
applications](Expressions.md#function-applications), of [linear
arithmetic](Expressions.md#linear-arithmetic) and of the [decidable
core](Decidability.md). A definition that nothing mentions, directly or
through the definitions that the body mentions, counts for nothing, so
those rules are not checked in it: `assume a: let v := o in x > 0` mentions
only `x`. Its names are still declared before use, and it is still typed,
and a divisor in it must still be a constant, since its value is needed
to translate the definition. A `++` in a definition is checked against
the decidable core in the definition, as if the definition were written
alone, not where the name is mentioned.
For the cycles of [definitions](Procedures.md#definitions), the
paths of every definition count, mentioned or not, as for unused
variables: whether definitions are acyclic is decided from what is
written. A
[trigger](Procedures.md#triggers) is read through a `let` or `where` at
the top of a constraint: the trigger of `when C, D where x := e` is `C`,
with `x` standing for `e`.

The `fren` command gives the solver each clause as SMT-LIB's `let`, so
that a name defined once is translated once. The Lean front end turns it
into Lean's `have`, around the expression for a `where` clause, in the
generated definitions, but substitutes the `have`s before it asks
lean-smt, which cannot read them, so its queries lose that sharing: a
chain of definitions that each mention the previous one twice grows
exponentially there, as it does in the evaluator and in the indexes that
each mention puts under its guards. When a solver's model is confirmed,
each index of a name mentioned more than once is paired with the
evaluator's by the order of the mentions; where the two orders differ, as
when `{}` makes the elaborator read a right operand first, the
confirmation gives up rather than report "may be out of range".
