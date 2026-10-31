# Local definitions and quantifiers

The lints of the `style` group that write a [`let` or
`where`](../../Lang/Let.md) clause, or a run of `and` or `or`, more
clearly.

## Returned definitions

`let_and_return` fires on a `let` or `where` clause whose body is the name
of its last definition, alone, as in `let d := x + 1 in d` or `ok? where
ok? := a? and b?`, and is fixable. A body in parentheses counts, but not
one that does more with the name, such as `d + 1`. The name says nothing
that its definition does not, since nothing else mentions it: the fix
writes the definition's expression in place of the body, and drops the
definition, or the whole clause if it has no other, so `let k := 1, d :=
x + k in d` becomes `let k := 1 in x + k`, and `ok? where ok? := a? and
b?` becomes `a? and b?`. The expression keeps its text, with its
parentheses. It needs no others: a clause binds as loosely as any
expression, so the expression can be written wherever the clause was, and
a definition's expression is never a `when`, `unless`, `let` or quantifier
that the body's place would not take. A `let`'s body may be a membership,
`in`, where its definitions may not, so a membership keeps the parentheses
that it had as a definition. It does not fire where the definition's type
is written, as in `let d: Int := n in d`, which may say more than the
expression: an `Int` that is a `Nat`.

The fix keeps the meaning, since a name stands for its definition
([Meaning](../../Lang/Let.md#meaning)), and the guards: a definition is
guarded where its name is mentioned, which is where the fix writes it.
It writes no new name, so it hides nothing. Clippy's `let_and_return` is
in `style`, and so `warn`, and so is this. `fren fix` leaves a clause with
a comment in it, which the fix could lose.

`lint::let_and_return` states when it fires, on the clause in the [model
of scopes](../Unused.md#scopes): the names of its definitions at their
positions, the last of them, those whose types are written, and the
body's tree, whose root is then a path of the last name with no parts:

```fren
pub mod lint

pub proc let_and_return(
    names: Rel<DefIndex, Local>,     -- the name each definition declares
    last: DefIndex,                  -- the position of the last definition
    annotated: Set<DefIndex>,        -- the definitions whose types are written
    body: Tree,
): (det fires?) {
    use lint::{DefIndex, Local, Tree}

    -- The positions up to `last`.
    let upto: Set<DefIndex> := match last {
        DefIndex::P0 => {DefIndex::P0},
        DefIndex::P1 => {DefIndex::P0, DefIndex::P1},
        DefIndex::P2 => {DefIndex::P0, DefIndex::P1, DefIndex::P2},
        DefIndex::P3 => {DefIndex::P0, DefIndex::P1, DefIndex::P2, DefIndex::P3},
    }

    ensure rule: fires? iff (last in names.domain and names.domain subset upto and not last in annotated
        and (body.paths.image({body.root}) inter names.image({last})) != {} and body.children.image({body.root}) = {})

    expect not_last: when names = {(DefIndex::P0, Local::A), (DefIndex::P1, Local::B)}
        and body.paths = {(body.root, Local::A)}, not fires?
}
```

The [refinements](../../Lang/Refinement.md) below check the fixes, of a
`let` of one definition and of two, and of a `where` clause, each of a
membership too. Here, as in the rest of these chapters, an operand of a
rewrite is a variable, which stands for any expression of its type: an
expression has no effects, so a rewrite that holds for every value of its
operands holds for every expression.

```fren
set_option fren.lint.let_and_return "allow" in
pub proc let_and_return_written(x: Int, s: Set<Int>, a?): (
    det one: Int,
    det two: Int,
    det member?,
    det clause?,
) {
    out one := let d := x + 1 in d
    out two := let k := 2, d := x * k in d
    out member? := let b? := (x in s) in b?
    out clause? := ok? where k := 3, ok? := a? and x > k
}

pub proc let_and_return_fixed(x: Int, s: Set<Int>, a?): (
    det one: Int,
    det two: Int,
    det member?,
    det clause?,
) {
    out one := x + 1
    out two := let k := 2 in x * k
    out member? := (x in s)
    out clause? := a? and x > k where k := 3
}

expect let_and_return_sound(x: Int, s: Set<Int>, a?) {
    call concrete := let_and_return_fixed(x, s, a?)
    refines concrete let_and_return_written(x, s, a?)
}
expect let_and_return_complete(x: Int, s: Set<Int>, a?) {
    call concrete := let_and_return_written(x, s, a?)
    refines concrete let_and_return_fixed(x, s, a?)
}
```

## Operands at each variant

`manual_forall` fires on three or more adjacent operands of a run of
`and` that are one expression at each variant of an enumeration none of
whose variants has a payload, as in `Mode::Heat in s and Mode::Cool in s
and Mode::Off in s`, and is fixable: they become `forall (mode: Mode),
mode in s`. On a run of `or`, the operands become an `exists`. The
operands are one expression at a variant where their
[lexemes](../../Lang/Lexical.md) are the same, with a path written in one
piece, such as `Mode::Heat`, as one lexeme, but for some places, and at
those places, each operand has a path to a variant without a payload,
written in an expression rather than a pattern, the same variant
throughout the operand, and each variant of the enumeration is one
operand's. The enumeration has a path written with `::` there, which is
the bound name's type. The run of `and` or `or` is the operands of `p and
q and ... and r`, through each left operand that is an `and` not in
parentheses, as for [chained
comparisons](Comparisons.md#chained-comparisons), and an operand in
parentheses is not one of the instances. Operands that equate, or
disequate, an expression with each variant, as in `m = Mode::Heat or m =
Mode::Cool or m = Mode::Off`, are not either: they test which variant `m`
is, and over every variant they are always `true`, or `false`, which a
quantifier would hide. As the other lints that rewrite an expression,
it does not look within the definitions of a `let` or `where`, and a
sequence literal's `[` counts as an index (see below), so it fires
neither there nor among a sequence's elements.

The fix writes one operand, the first, with the bound name in place of the
variant, as the body of the quantifier, whose expansion
([Meaning](../../Lang/Quantifiers.md#meaning)) is the operands, each once,
so it keeps the meaning. The bound name is the type's last segment in
snake case, `mode` for `Mode`, written with `!` where it would hide
something, such as the variable `mode`; the operands do not mention that
name, so the `!` hides nothing that they mean. The fix is in parentheses
unless it replaces the whole run, where it is placed as [fixes
are](../../Lint.md#parentheses-in-fixes): a quantifier binds as loosely
as `when` and is open-ended, so it is in parentheses as an operand, and
as an argument, a field of a record literal, an element of a collection
literal, an index, or a `match`'s scrutinee or arm's body. The parentheses
of an application, `f(e)`, are not the quantifier's own, so an argument
is written `h?((forall (m: Mode), g?(m)))`, for reading. There is no fix where that name is a reserved word, is
declared anywhere in the constraint, or is mentioned by the operands, or
where a comment would be lost; the message still suggests the quantifier.

The expansion conjoins the instances in the order of the variants, and
they do not guard each other, where an operand of `and` is guarded by the
ones before it (see [Sequences](../../Lang/Expressions.md#sequences)). The
lint fires only in a constraint, definition, function body or constant
with no index and no table, where guards make no difference, so the fix
keeps the guards too: a guard is of an index or of a table's rows, and a
name of a `let` or `where` is guarded where it is mentioned, so it could
carry one into the operands only from its definition in the same
constraint.

Clippy has no lint of a conjunction of every value of a type, as Rust has
no quantifiers over types; its nearest, `manual_all_any`'s fold over an
iterator, is not one either. It is in `style`, and so `warn`: a quantifier
says once what the operands say three or more times, and says it of a
variant added later, which a list of the variants does not.

`lint::manual_forall` states when it fires, from the variant each
operand is an instance at, here of an enumeration of three variants,
`Hue`, at up to four positions: the operands cover the enumeration, each
variant once. Whether they are instances, the same lexemes but at the
places of those variants, is a fact of their text, which `Reqs/Lint#written-the-same`
states and the procedure takes as given.
`lint::quantifier_parentheses` states where the fix is in parentheses,
from where the run is, `RunPlace`: a quantifier is open-ended, so it is in
parentheses wherever an open-ended form is not written bare, and where
something follows it:

```fren
pub enum Hue { Red, Green, Blue }

pub proc manual_forall(
    variant_of: Rel<DefIndex, Hue>,    -- the variant each operand is an instance at
    instances?,                      -- the operands are one expression at those variants, the same places in each
): (det fires?) {
    use lint::DefIndex

    -- Every variant, and no two operands at one.
    let covers? := variant_of.range = {Hue::Red, Hue::Green, Hue::Blue}
        and (variant_of join variant_of.inverse) subset {
            (DefIndex::P0, DefIndex::P0),
            (DefIndex::P1, DefIndex::P1),
            (DefIndex::P2, DefIndex::P2),
            (DefIndex::P3, DefIndex::P3),
        }

    ensure rule: fires? iff (instances? and covers?)

    expect each_once: when fires?, variant_of.range = {Hue::Red, Hue::Green, Hue::Blue}
}

-- Where a run of operands is: where any expression may be written, such as
-- a constraint or a branch of `if`; the body of a `when`, a `let` or a
-- quantifier; the condition of a `when`, or a part of an atom, such as an
-- argument, a field, an element, an index or a `match` arm's body, which
-- take an operand alike; an operand of an operator; or a receiver.
pub enum RunPlace { Free, Body, Condition, Operand, Receiver }

pub proc quantifier_parentheses(
    place: RunPlace,
    followed?,                       -- an operator or a `.` follows the run
    whole?,                          -- the fix replaces the whole run, not some of its operands
    enclosed?,                       -- the whole run is in parentheses of its own, not an application's
): (det parenthesized?) {
    ensure rule: parenthesized? iff (not enclosed? and (not whole? or followed?
        or place in {RunPlace::Condition, RunPlace::Operand, RunPlace::Receiver}))

    expect arms: when place = RunPlace::Condition and not enclosed?, parenthesized?
    expect bare_body: when place = RunPlace::Body and whole? and not followed?, not parenthesized?
}
```

The refinements below check the fixes, of a run of `and`, of a run of
`or`, of a run within a longer one, of one beside a variable of the bound
name's name, and of a run in a `match` arm's body, which takes the
quantifier only in parentheses:

```fren
set_option fren.lint.manual_forall "allow" in
pub proc manual_forall_written(s: Set<Hue>, t: Set<Hue>, hue: Hue, a?): (
    det every?,
    det some?,
    det within?,
    det beside?,
    det arm?,
) {
    out every? := Hue::Red in s and Hue::Green in s and Hue::Blue in s
    out some? := Hue::Red in s or Hue::Green in s or Hue::Blue in s
    out within? := a? and Hue::Blue in t and Hue::Red in t and Hue::Green in t
    out beside? := hue in s and Hue::Red in s and Hue::Green in s and Hue::Blue in s
    out arm? := match hue {
        Hue::Red => Hue::Red in s and Hue::Green in s and Hue::Blue in s,
        _ => a?,
    }
}

pub proc manual_forall_fixed(s: Set<Hue>, t: Set<Hue>, hue: Hue, a?): (
    det every?,
    det some?,
    det within?,
    det beside?,
    det arm?,
) {
    out every? := forall (hue!: Hue), hue in s
    out some? := exists (hue!: Hue), hue in s
    out within? := a? and (forall (hue!: Hue), hue in t)
    out beside? := hue in s and (forall (hue!: Hue), hue in s)
    out arm? := match hue {
        Hue::Red => (forall (hue!: Hue), hue in s),
        _ => a?,
    }
}

expect manual_forall_sound(s: Set<lint::Hue>, t: Set<lint::Hue>, hue: lint::Hue, a?) {
    use lint
    call concrete := manual_forall_fixed(s, t, hue, a?)
    refines concrete manual_forall_written(s, t, hue, a?)
}
expect manual_forall_complete(s: Set<lint::Hue>, t: Set<lint::Hue>, hue: lint::Hue, a?) {
    use lint
    call concrete := manual_forall_written(s, t, hue, a?)
    refines concrete manual_forall_fixed(s, t, hue, a?)
}
```
