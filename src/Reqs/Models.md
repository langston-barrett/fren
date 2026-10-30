# Reading models

When the solver answers `Sat`, it gives a *model*: a value for each
variable of the query, and an [interpretation](Check.md#interpretations).
Fren reads the model back into Fren values to report a counterexample, as
for a failed [expectation](Check.md#expectations), or a witness, as for a
met [cover goal](Check.md#cover-goals). The checks trust the solver's
answers (see [Verdicts](Check.md#verdicts)), but not Fren's own reading of
its models, nor Fren's translation of the spec for the solver. So before it
reports a model, each front end evaluates the query in Fren's [dynamic
semantics](Lang/Semantics.md), at the values it would show.

**Every counterexample that Fren shows is a behaviour in which the claim
is false, and every witness one in which the cover goal holds, in Fren's
semantics, at the values shown.** Where the semantics says otherwise, Fren
has a bug, and reports that as an internal error, never as a
counterexample.

```fren
pub mod model

use check::Verdict
use check::Verdict::Inconclusive
use lang::{Outcome, Value}
```

## Reading

Each front end has one *reader*, which turns each of the model's values
into the Fren value that it stands for: the `fren` command reads the
solver's SMT-LIB terms, and the Lean-hosted front end reads lean-smt's
Lean terms. A `Bool` is `true` or `false`, a `Nat` an integer, a sequence
the list of its elements, a set the list of its members, and a value of an
enumeration, a record or a newtype its constructor with the values of its
payload or fields, each read the same way, at every depth. A counterexample
or witness shows the values that the reader read (see [Check
results](View.md#check-results)), and the confirmation below evaluates the
query at those same values, not at the solver's. So a value that the reader
misreads is either still a counterexample, or is caught.

A value that a reader cannot read, such as a term of a shape that it does
not know, is shown as the solver writes it, and the parts of the query
that read it are undecided. Reading a value of every type back exactly as
the solver's encoding of it is a separate property, specified with the
readers (#425).

## Free values

A variable of the procedure's own, without a
[definition](Lang/Procedures.md#definitions), that no formula of the query
mentions has no value in the model: any value would do (see [Check
results](View.md#check-results)), and the counterexample does not show it.
A defined variable, or a call's, is not free even when the model leaves it
out, since its value follows from the others, by its definition or the
call's behaviour, which the solver may have substituted: it stays without a
value. The evaluator's formulas, which are
the spec's own, may still read it, as an argument that a function's body
never reads is read when the function is applied, since evaluation is
strict. The confirmation gives such a variable its type's *default value*,
the same in both front ends. `model::default_value` gives it, over a model
of the type, `TypeShape`, in which an enumeration or record is the list of its variants,
in the order declared, each with its constructor's full path and the list
of its payload's or fields' types, a record having one variant, and in
which `Itself` stands for the enumeration within its own payload:

- `false`, `0`, `""`, the empty sequence and the empty set (here the empty
  list, as [What the model leaves
  out](Lang/Semantics.md#what-the-model-leaves-out) leaves sets out);
- for a newtype, its underlying type's default value, constructed;
- for an enumeration or a record, its first variant whose payload's or
  fields' types all have a default value, with them;
- none for an abstract type, or for the enumeration within its own
  payload, whose default value is still being sought.

```fren
use lang::Id

pub enum TypeShape {
    Boolean,
    Integer,
    Natural,
    Text,
    Seq(TypeShape),
    Set,
    Abstract,
    Newtype(Id, TypeShape),
    -- An enumeration or a record: the list of its variants.
    Data(TypeShape),
    -- A variant: its constructor, the list of its payload's types, and the variants after it.
    Variant(Id, TypeShape, TypeShape),
    NoVariant,
    -- The enumeration within its own payload.
    Itself,
    -- A list of types.
    Nil,
    Cons(TypeShape, TypeShape),
}

pub fn default_value(t: TypeShape): Outcome := match t {
    TypeShape::Boolean => Outcome::Defined(Value::False),
    TypeShape::Integer | TypeShape::Natural => Outcome::Defined(Value::Integer(0)),
    TypeShape::Text => Outcome::Defined(Value::Text("")),
    TypeShape::Seq(_) | TypeShape::Set | TypeShape::Nil => Outcome::Defined(Value::Nil),
    TypeShape::Newtype(n, u) => match default_value(u) {
        Outcome::Defined(v) => Outcome::Defined(Value::Constructed(n, Value::Cons(v, Value::Nil))),
        Outcome::Undefined => Outcome::Undefined,
    },
    TypeShape::Data(variants) => default_value(variants),
    TypeShape::Variant(c, payload, rest) => match default_value(payload) {
        Outcome::Defined(l) => Outcome::Defined(Value::Constructed(c, l)),
        Outcome::Undefined => default_value(rest),
    },
    TypeShape::Cons(first, rest) => match default_value(first), default_value(rest) {
        Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
        _, _ => Outcome::Undefined,
    },
    TypeShape::Abstract | TypeShape::NoVariant | TypeShape::Itself => Outcome::Undefined,
}
```

So `pub enum F { L(Seq<Int>), N(F) }` has the default value `F::L([])`, and
`pub enum G { N(G), L }` has `G::L`, since `N`'s payload is the enumeration
itself:

```fren
-- The solver cannot unfold `default_value`, which has no contract; testing evaluates it.
set_option fren.evidence "random" in
expect default_examples(t: TypeShape) {
    expect boolean: when t = TypeShape::Boolean, default_value(t) = Outcome::Defined(Value::False)
    expect first_variant: when t = TypeShape::Data(TypeShape::Variant("F::L", TypeShape::Cons(TypeShape::Seq(TypeShape::Integer), TypeShape::Nil),
        TypeShape::Variant("F::N", TypeShape::Cons(TypeShape::Itself, TypeShape::Nil), TypeShape::NoVariant))),
        default_value(t) = Outcome::Defined(Value::Constructed("F::L", Value::Cons(Value::Nil, Value::Nil)))
    expect skips_itself: when t = TypeShape::Data(TypeShape::Variant("G::N", TypeShape::Cons(TypeShape::Itself, TypeShape::Nil),
        TypeShape::Variant("G::L", TypeShape::Nil, TypeShape::NoVariant))),
        default_value(t) = Outcome::Defined(Value::Constructed("G::L", Value::Nil))
    expect abstract_none: when t = TypeShape::Cons(TypeShape::Integer, TypeShape::Cons(TypeShape::Abstract, TypeShape::Nil)),
        default_value(t) = Outcome::Undefined
}
```

A variable whose type has no default value stays without one, and the
parts of the query that read it are undecided. A value that the model does
give is never replaced, even where no formula reads it.

## Confirmation

A model's *confirmation* evaluates each hypothesis of the query, and its
goal, at the values read, with the free ones filled: the outcome of each is
`Defined(true)`, `Defined(false)` or, where the semantics does not fix it
in the model, `Undefined`. A query asks that the hypotheses imply the goal,
so its model is right if every hypothesis is `true` and the goal `false`,
and *contradicted* if some hypothesis is `false` or the goal `true`. For a
witness, the goal is the negation of the cover goal, so a contradicted
witness is one in which the cover goal is `false`. A model that is neither,
such as one where a hypothesis applies a function that the model's
interpretation does not give, is *undecided*: it is reported on the
solver's word, as the checks report any answer.

```fren
set_option fren.lint.undecidable "allow" in
pub fn contradicted?(hypotheses: Seq<Outcome>, goal: Outcome) :=
    Outcome::Defined(Value::False) in hypotheses or goal = Outcome::Defined(Value::True)
```

Each front end evaluates with an evaluator of its own, each in Fren's
semantics: the `fren` command with the evaluator of [`fren
eval`](Eval.md#fren-eval), and the Lean-hosted front end by compiling the
Lean definitions that the spec generates (see [Generated Lean
declarations](Generated.md)) and running them. Lean's definitions give a
value where Fren's semantics gives none: an index out of range, a quotient
or remainder by 0, and the unspecified value of a table or `match` where
no row or arm is taken, which is an index of the empty sequence. So the
Lean-hosted front end evaluates only the formulas that have none of these,
directly or within the bodies of the functions and clauses that they
apply, and that apply no uninterpreted function and mention no value of an
abstract type: the others are `Undefined` to it. Neither front end ever
finds a correct model contradicted. Where one decides a formula that the
other leaves undefined, they may disagree about a model, but only about one
that Fren has misread or mistranslated.

## Reporting

`model::report` states what Fren does with a model that a check would
report: the counterexample of an expectation, a call's assumption,
definedness, completeness, disjointness, a precondition, a postcondition or
determinism, or the witness of a cover goal. A contradicted model is not
shown. The check is then inconclusive, as `eval::confirmed_verdict` makes a
refuted model's check, and Fren reports an internal error, an error at the
place where the check would have reported its result. It names the first
hypothesis that is `false`, in the query's order, or else the goal, and
shows the values as Fren read them:

```text
error: internal error: the solver's model for the expectation check of `m::p::e` makes its hypothesis `pinned` false in Fren's semantics
note: Fren reads the model as a = 0
note: so it is not shown as a counterexample or a witness, and the check is inconclusive
note: this is a bug in Fren: in reading the solver's model, or in translating the spec
```

The last line of `report`, `real`, is the statement at the top of this
chapter: where the semantics decides the query, a model shown is a
counterexample or a witness.

```fren
set_option fren.lint.undecidable "allow" in
pub proc report(
    hypotheses: Seq<Outcome>,      -- each hypothesis of the query, in its order, at the values read
    goal: Outcome,                 -- the goal, likewise
    solver: Verdict,               -- the verdict that the solver's answer gives
): (
    det shown?,                    -- the values are shown, as a counterexample or a witness
    det internal?,                 -- an internal error is reported instead
    det verdict: Verdict,
) {
    assume booleans: forall (k: Int), when 0 <= k < hypotheses.len, hypotheses[k] is Outcome::Defined(Value::True | Value::False) | Outcome::Undefined
    assume boolean_goal: goal is Outcome::Defined(Value::True | Value::False) | Outcome::Undefined

    ensure shows: shown? iff not contradicted?(hypotheses, goal)
    ensure errs: internal? iff not shown?
    ensure kept: when shown?, verdict = solver
    ensure inconclusive: unless shown?, verdict = Inconclusive

    expect real: when shown? and not (Outcome::Undefined in hypotheses) and goal != Outcome::Undefined,
        goal = Outcome::Defined(Value::False) and not (Outcome::Defined(Value::False) in hypotheses)
}
```

The `fren` command also confirms every other model that the solver gives
it, as [Confirming models](Eval.md#confirming-models) states.

## Testing

A reader's bug that changes no hypothesis or goal leaves the values a
counterexample, so the ui tests check the confirmation by injecting one:
with the environment variable `FREN_MISREAD_MODELS` set, both readers read
each integer of a model that a check would report as one more than it is.
The `fren` command's confirmation of its other models reads them right, so
that both front ends report the same. The ui tests in
`test/ui/misread/` run with it set (see [Testing](dev/Testing.md)), and
expect the internal errors above where the misread values contradict the
query, and the misread values as the counterexample where they do not.

#fren_check
