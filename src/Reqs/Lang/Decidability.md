# Decidability

Every check of a spec is decidable unless the spec explicitly opts out.
Each theory beyond Booleans, integers, datatypes and uninterpreted
functions has a *decidable core*, which Fren recognizes from the syntax
alone: from the operators, the types of their operands, and which operands
are constants. A construct outside the core is reported by the
[lint](../Lint/Decidability.md#undecidable-constructs) `undecidable`, which is `deny`
by default. A spec opts out where it must, with `set_option
fren.lint.undecidable "allow" in` before an item.

## What is promised

Every query that Fren asks about a procedure or global expectation without
an opt-out is in a fragment with a known decision procedure. That the
fragment is decidable does not mean that the solver decides every query
in it quickly, or at all: see [In practice](#in-practice) for where it
does and where it does not. An `Inconclusive` verdict then means that the
solver ran out of time, and the [message](../View.md#check-results) says
to raise the time limit. With recursive functions, it may instead mean that evaluation refuted
a model allowed by their contracts (`F0450`); strengthen those contracts
rather than raising the time limit. In a procedure that opts out, it may also mean
that the solver gave up, and the message says that instead.

The rest of the language is decidable by three rules:

1. Every check but realizability asks a quantifier-free question.
2. Realizability quantifies only over outputs, and outputs have bounded
   types (see [Procedures](Procedures.md#members)), unless they are
   [defined](Procedures.md#definitions), in which case they are
   replaced by their definitions.
3. A function's arguments never mention an output (see
   [Calls](Calls.md#call-variables)), so the quantifier never
   reaches under a function.

A [quantifier](Quantifiers.md) over listed types adds no quantifier to a
query: it ranges over a finite type, and is expanded into a conjunction
or disjunction of at most 256 instances before anything is asked, so the
first rule still holds. Its bound names mention nothing, so each instance
is in the core exactly when the body would be with a constant in place of
each bound name: `forall (m: Method), s.starts_with?(prefix(m))`, with
`prefix` a defined function, is in the core, as each
`s.starts_with?(prefix(Method::Len))` is. An [unbounded
quantifier](Quantifiers.md#unbounded-quantifiers), over a type that is
not listed, is given to the solver as a quantifier, which breaks the first
rule, so it is outside the core, whatever its body and its guard, unless it
is a [quantifier over a sequence's elements](ElementQuantifiers.md), such
as `forall (x: T), when x in q, P`, with `x` used only as a value, which
each query instantiates at the finitely many positions of the array
property fragment's index set before anything is asked: a
quantifier over the integers alone is Presburger arithmetic, which is
decidable, but not with uninterpreted functions, strings, sets or
sequences beside it, and a guard that bounds it bounds it by a term, not
by a constant. The `undecidable` lint reports it at each binder whose
type is not listed (`Quantifier`).

A [table](Expressions.md#tables) is in the core when its rows' conditions
and values are: it is a chain of conditionals, and where no row of one
without a `_` row holds, its value is an index of the empty sequence,
`[][0]`, which is in the core (see [Sequences](#sequences)). Its
completeness, disjointness and reachability checks ask quantifier-free
questions of its conditions. So is a [`match`](Expressions.md#matches)
with guards, when its scrutinee, guards and bodies are, and its checks
likewise. A [pattern test](Expressions.md#binding-names) that binds names
is too, when its scrutinee and what sees its names are: as a `match`
arm's binders are, each name stands for a selector of the scrutinee's
payload, so no quantifier is added.

## Integers

Integer arithmetic is *linear*, which keeps it decidable, with or without
realizability's quantifier: it is Presburger arithmetic, which includes
division by a constant. `+` and `-`, `*` with a constant on one side (see
[Linear arithmetic](Expressions.md#linear-arithmetic)), `div` and `mod`
by a constant other than `0` (see [Division and
remainder](Expressions.md#division-and-remainder)), the methods `abs`,
`min` and `max`, which are conditionals, and the [cardinality
operators](Expressions.md#cardinality), which compare a sum of
conditionals with 1, are all linear. A cardinality operator counts its
`Bool` arguments, not the members of a set, so it is not `card` for the
rule on [relations](#relations). A product of two
variables, or a quotient by one, is not outside a core to opt out of: it is
an error, whatever the lint levels.

A [`Nat`](Types.md#natural-numbers) is an `Int` with the linear
constraint that it is at least 0, so it is in the core wherever an `Int`
is. The constraint on an output stays with the guarantees under
realizability's quantifier, and the one on an application of an
uninterpreted function is about that application, so no query quantifies
over a function's arguments.

## Subset types

A [subset type](SubsetTypes.md) at the top of a declared type,
or within a record's fields or the payloads of an enumeration that is not
recursive, brings one constraint for each of its invariants, at each
value that the variable or application has, which adds no quantifier: it
is in the core exactly when each invariant is. An invariant that is one
pattern test is: a pattern is a disjunction of comparisons with constants
and tests of variants. Its obligations add no quantifier either. Within a
set's, relation's or sequence's element type, its constraint and its
obligations hold of every element, which quantifies over the elements,
and within a recursive enumeration's payload, of every payload, which Fren
states for each one that a query reads. Both are outside the core, by
`lang::subset_place`: the
[`undecidable` lint](../Lint/Decidability.md#undecidable-constructs)
reports each such subset type where it is written, besides any invariant
that is itself outside the core, and the `Nat` that
would be the same is an error instead (see [Natural
numbers](Types.md#natural-numbers)).

## Orderings

An ordering of `Int`s or `Nat`s is linear arithmetic, and one of the
values of an ordered enumeration compares their variants' positions, which
are finitely many. An ordering of the values of an [ordered record or
newtype](Items.md#ordered-declarations), and its `min` and `max`, unfold,
field by field, into orderings and equations of its fields' values, joined
by `and` and `or`: no ordered declaration is recursive, so the unfolding
ends, and it is quantifier-free. Such an ordering is in the core exactly
when the orderings that it unfolds into are, so one whose type has a
`String` within it, at any depth, is an ordering of strings, in the core
when one side is a constant, as below. The others are always in the core.

## Strings

The core of the theory of strings is *regular constraints with length*:
each string operation constrains a term to a regular language, string
terms are compared only with constants or with each other as whole
variables, and lengths are used in linear arithmetic.

| Construct | In the core when |
|---|---|
| literals and constants | always |
| `s.len` | always: it is an `Int` |
| `s.starts_with?(c)`, `s.ends_with?(c)`, `s.contains?(c)` | the argument `c` is a [constant](Items.md#constants) |
| `s.matches?(p)` | always: the pattern is a literal |
| `s.at(i)`, `s.slice(i, n)` | `i` and `n` are constants: a substring at fixed positions is a regular condition on `s` |
| `s.index_of(t, i)`, `s.replace(a, b)`, `s.replace_all(a, b)` | never, unless every operand is a constant |
| `s = t`, `s != t`, on strings | one side is a constant, or both are variables |
| `s < t`, `s <= t`, `s > t`, `s >= t`, `s.min(t)`, `s.max(t)`, on strings, or on values of an ordered record or newtype with a `String` within | one side is a constant |
| `a ++ b` | it is the receiver of a method, a side of `=` or `!=` whose other side is a constant, a [definition](Procedures.md#definitions) or part of one, or itself a constant |

Here a *constant* is an expression that mentions no variable and no
uninterpreted function, as [Mentions](Expressions.md#mentions) defines,
such as `"F0" ++ "1"`, or `pad("F0")` with `pad` a defined function. A
binder mentions what its scrutinee mentions, so it is a constant if its
scrutinee is, a name of a [`let` or `where`](Let.md) is a constant if its
definition is, and a quantifier's bound name mentions nothing, so it is a
constant. A *variable* is a variable of the procedure, of one of its
calls, a field read from one, or a binder whose scrutinee is not a
constant. A [definition](Procedures.md#definitions) is an equation
between the defined variable and its expression, and a call's argument
an equation between the called procedure's parameter and its expression.

A definition assigns its variable once, and definitions are acyclic, so a
`++` in one is a *straight-line* equation, which is decidable with regular
constraints and length: substituting the definitions leaves only
constraints on the variables that they mention. A defined variable whose
definition has a `++` that is not a constant then stands for that `++` in
the rows above: it may be compared with a constant, or be the receiver of
a method, but not compared with another variable, which would be the word
equation that the definition spelled out.

Outside the core are equations with `++` on both sides, which are word
equations, comparisons of two non-constant strings other than by `=`
between variables, and searching: `index_of`, `replace` and
`replace_all`, which together are undecidable. A construct whose operands
are all constants, such as `"abc".index_of("c", 0)`, has a fixed value, so
it is always in the core.

## Sets

The core of the theory of sets is *Boolean algebra with Presburger
arithmetic*: membership, `union`, `inter`, `minus`, `subset`, `=`, `!=`,
literals, and `card` in linear arithmetic. It is decidable, and cvc5's
solver for sets with cardinality is a decision procedure for it.

| Construct | In the core when |
|---|---|
| set literals, `in`, `union`, `inter`, `minus`, `subset`, `card`, `=` and `!=` on sets | always |
| a function with a parameter or result of type `Set<T>` | `T` is infinite (see below) |

A function of sets combines with the theory of sets only if the set sort
has infinitely many values, which it has when `T` does: `Int`, `String`
and sets of those. An abstract type may have a single value, and an
enumeration finitely many, so `fn f(Set<Name>): Int` is outside the core.
A relation's sort is infinite when either of its element types is.

## Relations

A relation is a set of pairs, so the operations on sets are in the core
for relations too, as is `(x, y) in r`. The [relational
operators](Expressions.md#relations) quantify over a type: `(a, c) in r
join q` means that `(a, b) in r` and `(b, c) in q` for some `b`. Each is in
the core when the types it ranges over are [finite](Types.md#finite-types),
since a quantifier over a finite type is a finite formula of the theory of
sets, and outside it otherwise:

| Construct | Ranges over, for `r: Rel<A, B>` |
|---|---|
| `r join q` | `B` |
| `r.image(s)` | `A` |
| `r.domain` | `B` |
| `r.range` | `A` |
| `r.inverse` | `A` and `B` |
| `r.closure` | `A`, which is `B` |

Fren does not expand the quantifier into the formula: the operators go to
the solver as its relational operators, which decide them directly, with
one exception, found by the conformance corpus: the solver does not
reliably combine relational operators with counting. Given both, it gives
up, runs out of time, or even gives a wrong model, which Fren's model check
then refutes. So in a procedure or global expectation that applies a
relational operator, directly or through a call, a `card` of anything
but a constant is outside the core, and so is a call of a procedure
that counts.

## Sequences

Without concatenation, a sequence is an array with a length, and the
theory of arrays with extensionality and a length is decidable; the
solver's procedure for sequences targets it. With concatenation, equations
between sequences are word equations over an infinite alphabet, which are
not known to be decidable with length.

| Construct | In the core when |
|---|---|
| sequence literals, `q.len`, `q[i]`, `q.update(i, x)`, `=` and `!=` on sequences | always |
| `x in L`, `q.starts_with?(L)`, `q.ends_with?(L)` | `L` is a literal: each is then a formula of indexing and length, such as `q.len >= 2 and q[0] = a and q[1] = b`; or `x in q` is the membership of the guard of a [quantifier over elements](ElementQuantifiers.md) in the core, which its expansion replaces by a position's being in range |
| `++`, `q.at(i)`, `q.slice(i, n)`, `q.index_of(t, i)`, `q.contains?(t)`, `q.replace(a, b)`, `q.rev`, and the rest | never, unless every operand is a constant |


Under realizability's quantifier over outputs, a string operation on an
output would quantify over strings. So an operand of a string operation,
other than of `=` and `!=`, may not mention an output of an infinite type,
directly or through a definition: an `Int`, a `String`, an abstract type,
or an enumeration or record with such a payload or field. An output of a
finite type is a finite case split, and is always allowed.

A [higher-order function's](HigherOrder.md) applications are unfolded,
with their closures within them, so nothing of a function type reaches
the solver: a closure's body is in the core exactly when its expression
would be, written where the closure is unfolded, and a closure's parameter
counts as a value that varies, as an unbounded quantifier's bound name
does, for the rules above.

## Recursion

Applications of [structural recursions](Recursion.md) are opaque,
with ground postconditions and one step of defining equations at each
application. Applications introduced by that step receive postconditions
only. This is finite and adds no quantifiers, even for constant arguments,
so recursion never raises `undecidable`. Completeness is modulo this
opacity: facts requiring more of a recursive body than its one-step
equations and contract are not promised. Strengthen its contract to prove
such facts. Models refuted by evaluation are Inconclusive (`F0450`).

## In practice

Fren checks with cvc5 and does not add decision procedures of its own, so
what the core promises is what cvc5 does with it. Where cvc5 does not
decide a query in the core, the check is `Inconclusive`, and that is a
limit of the solver, not a fault in the spec.

The solver decides these reliably and quickly:

- Booleans, enumerations, records, linear integer arithmetic, abstract
  types and uninterpreted functions, including realizability's quantifier
  over outputs: the three rules above keep it to a form that the solver
  decides by trying finitely many values.
- A string compared with a constant, or constrained at its start or end:
  `=`, `!=`, `starts_with?` and `ends_with?`, alone or with a pattern.
- A pattern together with other constraints on the same string, when some
  string satisfies them all: the solver finds one.

The known weak spot is proving that no string satisfies a pattern with
repetition (`*`, `+` or `{m,}`) together with another constraint on the
middle of the same string: `contains?`, or a second pattern with
repetition. For example, `lang::identifier` in
[Lexical structure](Lexical.md#identifiers) would state that an
identifier, a pattern with repetition, never contains `..`. That is
true, but cvc5 does not prove it within any time limit tried, and neither
does Z3, so the chapter leaves it as a comment. Raising `--timeout`
does not help, and bounding the string's `len` only turns a query that
never ends into a slow one.
Such a check stays `Inconclusive`. A spec can say so where it applies,
with `set_option fren.evidence "random" in`, and have the check tested
instead (see [Checking by testing](../Check.md#checking-by-testing)), which
gives evidence for it, not proof.

Relational operators together with `card` are outside the core for the
same reason (see [Relations](#relations)).

## The rule

`lang::in_core` decides whether a construct is in the core. Each input is
decided from the syntax, without the solver:

```fren
pub mod lang

-- `StringCompare` is `=`, `!=` and the orderings on strings; `StringAtom`
-- is `starts_with?`, `ends_with?`, `contains?` and `matches?`; `StringIndex`
-- is `at` and `slice`; `StringSearch` is `index_of`, `replace`,
-- `replace_all`, and `++` outside the places the core allows; `SetAlgebra` is
-- the operations on sets and relations; `SetFunction` is a function of a set
-- or relation type; `Relational` is a relational operator; `RelationalCard` is
-- `card`, or a call of a procedure that counts, where there is one;
-- `SeqArray` is a sequence's literals, `len`, indexing and `update`; `SeqWord`
-- is the other operations on sequences; `Quantifier` is an unbounded
-- quantifier's binder of a type that is not listed, of a quantifier that
-- `element_quantifier` does not put in the core.
pub enum Construct {
    StringCompare, StringAtom, StringIndex, StringSearch, SetAlgebra, SetFunction, Relational, RelationalCard,
    SeqArray, SeqWord, Quantifier,
}

pub proc in_core(
    construct: Construct,
    constant_args?,          -- every operand but the receiver is a constant
    comparable?,             -- for `StringCompare`: as the table above says
    infinite_output?,        -- an operand other than of `=` or `!=` mentions an output of an infinite type
    ground?,                 -- every operand, the receiver too, is a constant
    infinite_elems?,         -- for `SetFunction`: the element types of its sets are infinite
    finite_range?,           -- for `Relational`: the types it ranges over are finite
    literal_operand?,        -- for `SeqWord`: `x in L`, `starts_with?(L)` or `ends_with?(L)`, with `L` a literal
): (det decidable?) {
    use self::Construct::{
        Quantifier,
        Relational,
        RelationalCard,
        SeqArray,
        SeqWord,
        SetAlgebra,
        SetFunction,
        StringAtom,
        StringCompare,
        StringIndex,
        StringSearch,
    }

    ensure rule: decidable? iff (construct != Quantifier and (ground? or (not infinite_output? and match construct {
        StringAtom | StringIndex => constant_args?,
        StringCompare => comparable?,
        SetAlgebra | SeqArray => true,
        SetFunction => infinite_elems?,
        Relational => finite_range?,
        SeqWord => literal_operand?,
        StringSearch | RelationalCard | Quantifier => false,
    })))

    expect outputs_block: when infinite_output? and not ground?, not decidable?
    expect search_never: when construct = StringSearch and not ground?, not decidable?
    expect ground_always: when ground? and construct != Quantifier, decidable?
    expect quantifier_never: when construct = Quantifier, not decidable?
    expect algebra_always: when construct = SetAlgebra and not infinite_output?, decidable?
    expect relational_finite: when construct = Relational and not ground? and decidable?, finite_range?
    expect relational_card_never: when construct = RelationalCard and not ground?, not decidable?
    expect arrays_always: when construct = SeqArray and not infinite_output?, decidable?
    expect words_literal: when construct = SeqWord and not ground? and decidable?, literal_operand?
}
```
