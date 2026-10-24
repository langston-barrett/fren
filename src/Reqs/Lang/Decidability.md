# Decidability

Every check of a spec is decidable unless the spec explicitly opts out.
Each theory beyond Booleans, integers, datatypes and uninterpreted
functions has a *decidable core*, which Fren recognizes from the syntax
alone: from the operators, the types of their operands, and which operands
are constants. A construct outside the core is reported by the
[lint](../Lint.md#undecidable-constructs) `undecidable`, which is `deny`
by default. A spec opts out where it must, with `set_option
fren.lint.undecidable "allow" in` before an item.

## What is promised

Every query that Fren asks about a component or global expectation without
an opt-out is in a fragment with a known decision procedure. That the
fragment is decidable does not mean that the solver decides every query
in it quickly, or at all: see [In practice](#in-practice) for where it
does and where it does not. An `Inconclusive` verdict then means that the
solver ran out of time, and the [message](../View.md#check-results) says
to raise the time limit. In a component that opts out, it may also mean
that the solver gave up, and the message says that instead.

The rest of the language is decidable by three rules:

1. Every check but realizability asks a quantifier-free question.
2. Realizability quantifies only over outputs, and outputs have bounded
   types (see [Components](Components.md#members)), unless they are
   [defined](Components.md#defined-outputs), in which case they are
   replaced by their definitions.
3. A function's arguments never mention an output (see
   [Instances](Instances.md#instance-variables)), so the quantifier never
   reaches under a function.

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
| `s < t`, `s <= t`, `s > t`, `s >= t`, on strings | one side is a constant |
| `a ++ b` | it is the receiver of a method, a side of `=` or `!=` whose other side is a constant, a [definition](Components.md#defined-outputs) or part of one, or itself a constant |

Here a *constant* is an expression that mentions no variable, binder or
function, such as `"F0" ++ "1"`, and a *variable* is a variable of the
component, of one of its instances, a field read from one, or a binder. A
[definition](Components.md#defined-outputs) is an equation between the
defined output and its definition, and an instance's binding an equation
between the instance's input and its expression.

A definition assigns its output once, and definitions are acyclic, so a
`++` in one is a *straight-line* equation, which is decidable with regular
constraints and length: substituting the definitions leaves only
constraints on the variables that they mention. A defined output whose
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
| a function with a parameter or result of type `Set(T)` | `T` is infinite (see below) |

A function of sets combines with the theory of sets only if the set sort
has infinitely many values, which it has when `T` does: `Int`, `String`
and sets of those. An abstract type may have a single value, and an
enumeration finitely many, so `fn f(Set(Name)): Int` is outside the core.
A relation's sort is infinite when either of its element types is.

## Relations

A relation is a set of pairs, so the operations on sets are in the core
for relations too, as is `(x, y) in r`. The [relational
operators](Expressions.md#relations) quantify over a type: `(a, c) in r
join q` means that `(a, b) in r` and `(b, c) in q` for some `b`. Each is in
the core when the types it ranges over are [finite](Types.md#finite-types),
since a quantifier over a finite type is a finite formula of the theory of
sets, and outside it otherwise:

| Construct | Ranges over, for `r: Rel(A, B)` |
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
then refutes. So in a component or global expectation that applies a
relational operator, directly or through an instance, a `card` of anything
but a constant is outside the core, and so is an instance of a component
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
| `x in L`, `q.starts_with?(L)`, `q.ends_with?(L)` | `L` is a literal: each is then a formula of indexing and length, such as `q.len >= 2 and q[0] = a and q[1] = b` |
| `++`, `q.at(i)`, `q.slice(i, n)`, `q.index_of(t, i)`, `q.contains?(t)`, `q.replace(a, b)`, `q.rev`, and the rest | never, unless every operand is a constant |


Under realizability's quantifier over outputs, a string operation on an
output would quantify over strings. So an operand of a string operation,
other than of `=` and `!=`, may not mention an output of an infinite type,
directly or through a definition: an `Int`, a `String`, an abstract type,
or an enumeration or record with such a payload or field. An output of a
finite type is a finite case split, and is always allowed.

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
repetition. For example, `lang::word::no_empty_segment` in
[Lexical structure](Lexical.md) states that a word, a pattern with
repetition, never contains `..`. That is true, but cvc5 does not prove it
within any time limit tried, and neither does Z3. Raising `--timeout`
does not help, and bounding the string's `len` only turns a query that
never ends into a slow one.
Such a check stays `Inconclusive`; `fren quickcheck` (see
[Evaluation](../Eval.md#fren-quickcheck)) gives evidence for it instead of proof.

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
-- `card`, or an instance of a component that counts, where there is one;
-- `SeqArray` is a sequence's literals, `len`, indexing and `update`; `SeqWord`
-- is the other operations on sequences.
pub enum Construct {
    StringCompare, StringAtom, StringIndex, StringSearch, SetAlgebra, SetFunction, Relational, RelationalCard,
    SeqArray, SeqWord,
}

pub comp in_core {
    use self::Construct::{
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
    in construct: Construct
    in constant_args?        -- every operand but the receiver is a constant
    in comparable?           -- for `StringCompare`: as the table above says
    in infinite_output?      -- an operand other than of `=` or `!=` mentions an output of an infinite type
    in ground?               -- every operand, the receiver too, is a constant
    in infinite_elems?       -- for `SetFunction`: the element types of its sets are infinite
    in finite_range?         -- for `Relational`: the types it ranges over are finite
    in literal_operand?      -- for `SeqWord`: `x in L`, `starts_with?(L)` or `ends_with?(L)`, with `L` a literal
    pub det out decidable?

    req rule: decidable? iff (ground? or (not infinite_output? and match construct {
        StringAtom | StringIndex => constant_args?,
        StringCompare => comparable?,
        SetAlgebra | SeqArray => true,
        SetFunction => infinite_elems?,
        Relational => finite_range?,
        SeqWord => literal_operand?,
        StringSearch | RelationalCard => false,
    }))

    expect outputs_block: when infinite_output? and not ground?, not decidable?
    expect search_never: when construct = StringSearch and not ground?, not decidable?
    expect ground_always: when ground?, decidable?
    expect algebra_always: when construct = SetAlgebra and not infinite_output?, decidable?
    expect relational_finite: when construct = Relational and not ground? and decidable?, finite_range?
    expect relational_card_never: when construct = RelationalCard and not ground?, not decidable?
    expect arrays_always: when construct = SeqArray and not infinite_output?, decidable?
    expect words_literal: when construct = SeqWord and not ground? and decidable?, literal_operand?
}
```
