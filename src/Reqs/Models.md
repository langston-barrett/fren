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

**Wherever Fren's semantics decides the claim, every counterexample that
Fren shows is a behaviour in which the claim is false, and every witness
one in which the cover goal holds, at the values shown.** Where the
semantics says otherwise, Fren has a bug, and reports that as an internal
error, never as a counterexample. Where the semantics decides nothing, the
values are shown on the solver's word, as [Confirmation](#confirmation)
states.

```fren
pub mod model

use check::Verdict
use check::Verdict::Inconclusive
use lang::{Env, Expr, Id, Interp, Outcome, Value, eval}
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
value. A free variable may still be read by the evaluator's formulas,
which are the spec's own, as an argument that a function's body never
reads is read when the function is applied, since evaluation is strict.
The confirmation gives each free variable its type's *default value*, the
same in both front ends. `model::default_value` gives it, over a model of
the type, `TypeShape`, in which an enumeration or record is the list of
its variants, in the order declared, each with its constructor's full path
and the list of its payload's or fields' types, a record having one
variant, and in which `Itself` stands for the enumeration within its own
payload:

- `false`, `0`, `""`, the empty sequence and the empty set (here the empty
  list, as [What the model leaves
  out](Lang/Semantics.md#what-the-model-leaves-out) leaves sets out);
- for a newtype, its underlying type's default value, constructed;
- for an enumeration or a record, its first variant whose payload's or
  fields' types all have a default value, with them;
- none for an abstract type, or for the type within its own payload, whose
  default value is still being sought, which `Itself` stands for.

`TypeShape` is `model::default_value`'s own model of a type, not the type
itself, and it covers only what the rule needs: `Set` stands for a set and
for a relation, since the default value of both is empty, and the elements'
type is not read; and a record is a `Data` of one `Variant`, its fields.
It is complete for Fren's types, as the variables of a query have them.
A type's payload or fields can recur only into the type itself, never
through another type: a type is declared before it is used, so two types
cannot each contain the other, and a recursive payload must be the type
itself, not an instance that contains it (F0387). So `Itself`, the
immediately enclosing type, is the only type whose default value can be
sought within its own. An instance of a generic type has its arguments substituted
before the rule is applied. A [generic
function](Lang/GenericFunctions.md#type-parameters)'s checks, though, hold
for every type, so their variables may have its type parameter as their
type, as an abstract type: the rule treats it as one, `Abstract`, and
gives no value, as both front ends do. A free variable of a type
parameter is then left without a value, and the parts of the query that
read it are undecided, as for an abstract type.

```fren
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
    expect first_variant: when t = TypeShape::Data(
        TypeShape::Variant(
            "F::L",
            TypeShape::Cons(TypeShape::Seq(TypeShape::Integer), TypeShape::Nil),
            TypeShape::Variant(
                "F::N",
                TypeShape::Cons(TypeShape::Itself, TypeShape::Nil),
                TypeShape::NoVariant
            )
        )
    ),
        default_value(t) = Outcome::Defined(
            Value::Constructed("F::L", Value::Cons(Value::Nil, Value::Nil))
        )
    expect skips_itself: when t = TypeShape::Data(
        TypeShape::Variant(
            "G::N",
            TypeShape::Cons(TypeShape::Itself, TypeShape::Nil),
            TypeShape::Variant("G::L", TypeShape::Nil, TypeShape::NoVariant)
        )
    ),
        default_value(t) = Outcome::Defined(Value::Constructed("G::L", Value::Nil))
    expect abstract_none: when t = TypeShape::Cons(
        TypeShape::Integer,
        TypeShape::Cons(TypeShape::Abstract, TypeShape::Nil)
    ),
        default_value(t) = Outcome::Undefined
    -- A newtype's value is its underlying type's, constructed: `Ms(0)`.
    expect newtype: when t = TypeShape::Newtype("Ms", TypeShape::Integer),
        default_value(t) = Outcome::Defined(
            Value::Constructed("Ms", Value::Cons(Value::Integer(0), Value::Nil))
        )
    expect text: when t = TypeShape::Text, default_value(t) = Outcome::Defined(Value::Text(""))
    expect set: when t = TypeShape::Set, default_value(t) = Outcome::Defined(Value::Nil)
    -- A record: its fields, in the order declared.
    expect record: when t = TypeShape::Data(
        TypeShape::Variant(
            "P",
            TypeShape::Cons(
                TypeShape::Boolean,
                TypeShape::Cons(TypeShape::Newtype("Ms", TypeShape::Integer), TypeShape::Nil)
            ),
            TypeShape::NoVariant
        )
    ),
        default_value(t) = Outcome::Defined(
            Value::Constructed(
                "P",
                Value::Cons(
                    Value::False,
                    Value::Cons(
                        Value::Constructed("Ms", Value::Cons(Value::Integer(0), Value::Nil)),
                        Value::Nil
                    )
                )
            )
        )
}
```

A variable whose type has no default value stays without one, and the
parts of the query that read it are undecided. A value that the model does
give is never replaced, even where no formula reads it. `model::fill`
binds the free variables, each with its type, in an environment of the
values read:

```fren
-- A free variable of the type `t` is filled with `value`.
pub proc fill_rule(t: TypeShape): (det value: Outcome) { out value := default_value(t) }

-- The variables that a model leaves free, each with its type.
pub enum Free { Nil, Bind(Id, TypeShape, Free) }

pub fn fill(env: Env, free: Free): Env := match free {
    Free::Bind(x, t, rest) => Env::Bind(x, default_value(t), fill(env, rest)),
    Free::Nil => env,
}
```

The `fren` command's `Spec.defaultVal` and the Lean-hosted front end's
`defaultValue` implement `default_value`, as `fill_rule` states.
`src/FrenTest/ModelDefaults.lean` tests each against `default_value`
itself, which Lean generates from this chapter: it builds the `TypeShape`
of each of an enumeration whose first variant has a default value, one
whose first variant's payload is the enumeration itself, a newtype, a
record of a newtype and a set, and an enumeration whose payload is that
record, evaluates `default_value` on it, and compares the result with each
front end's value, read as a `lang::Value`. Neither front end's value
records a newtype's constructor, which its renderer restores, so the test
restores it too: that is the one place where the representations differ.

## Confirmation

A model's *confirmation* evaluates each hypothesis of the query, and its
goal, by `lang::eval`, in the model's interpretation, as read, and in the
environment of the values read, with the free ones filled. The outcome of
each is `Defined(true)`, `Defined(false)` or, where the semantics does not
fix it in the model, `Undefined`. A query asks that the hypotheses imply
the goal, so its model is right if every hypothesis is `true` and the goal
`false`, and *contradicted* if some hypothesis is `false` or the goal
`true`. For a witness, the goal is the negation of the cover goal, so a
contradicted witness is one in which the cover goal is `false`. A model
that is neither, such as one where a hypothesis applies a function that
the model's interpretation does not give, is *undecided*: it is reported
on the solver's word, as the checks report any answer. The hypotheses are
a list of expressions, `Nil` or `Cons(h, rest)`, as the operands of a
form are in [the abstract syntax](Lang/Semantics.md#expressions):

```fren
pub fn some_false?(i: Interp, env: Env, hypotheses: Expr<Id>) := match hypotheses {
    Expr::Cons(h, rest) => eval(i, env, h) = Outcome::Defined(Value::False) or some_false?(i, env, rest),
    _ => false,
}

pub fn contradicted?(i: Interp, env: Env, hypotheses: Expr<Id>, goal: Expr<Id>) :=
    some_false?(i, env, hypotheses) or eval(i, env, goal) = Outcome::Defined(Value::True)
```

### How the front ends evaluate

Neither front end evaluates by `lang::eval` itself, which models only a
fragment of the language (see [What the model leaves
out](Lang/Semantics.md#what-the-model-leaves-out)). Each has an evaluator of
its own, so that each agrees with `lang::eval` where `lang::eval` is
defined is a separate claim:

- The `fren` command evaluates with the evaluator of [`fren
  eval`](Eval.md#fren-eval), the one that [confirms its other
  models](Eval.md#confirming-models). Like `lang::eval`, it gives no value
  to an index out of range, a quotient or remainder by 0, or a table or
  `match` where no row or arm is taken. It is checked against `lang::eval`
  on random expressions, in random behaviours, by
  `src/FrenTest/Semantics.lean`, which is the evidence for
  [`lang::coincidence`](Lang/EvaluationRules.md#free-variables): the
  agreement is **tested**, over the forms that that test generates, which
  leave out `*`, `div`, `mod` and the concatenation of strings.
- The Lean-hosted front end compiles the Lean definitions that the spec
  generates (see [Generated Lean declarations](Generated.md)) and runs
  them. Lean's definitions give a value where Fren's semantics gives none:
  `default` for an index out of range, 0 for a quotient or remainder by 0,
  and so for a table or `match` where no row or arm is taken, which is an
  index of the empty sequence. So the Lean-hosted front end evaluates only
  the formulas that have none of these, directly or within the bodies of
  the functions and clauses that they apply, and that apply no
  uninterpreted function and mention no value of an abstract type, nor
  of a generic function's type parameter, which is one: the others are
  `Undefined` to it. It confirms nothing that indexes a
  sequence, so a misread model whose contradiction is only in such a
  formula is shown by it, and caught by the `fren` command (#462), as is
  one whose contradiction is only in a formula that mentions a value of a
  type parameter (`test/ui/misread/misread_type_parameter.fren`). That it
  agrees with `lang::eval` on the formulas it does decide is **trusted**:
  nothing checks the generated definitions against `lang::eval`.

  A generated [selector](Generated.md) of a payload is total in the same
  way, by a `| _ => default` arm for the other variants, and is not
  excluded. A read of a payload is evaluated only where the model's value
  has the variant that a `match` arm or a pattern test matched, since every
  such read is under the `ite` of that test, which Lean's definitions do
  not evaluate on the branch not taken; and a `match` that may take no arm
  reads the empty sequence, so it is excluded already.

Where one front end decides a formula that the other leaves undefined,
they may disagree about a model, but only about one that the semantics
contradicts. That neither finds a correct model contradicted rests on the
evidence above: tested for the `fren` command, trusted for the Lean-hosted
front end. Beyond that, the ui tests and Fren's own requirements, which
`fren check` checks in `lake test` and Lean on `main` ([Own
requirements](dev/Testing.md#own-requirements)), run both front ends over
every model that they report, so a confirmation that refuted a correct
model would fail them.

## Reporting

`model::report` states what Fren does with a model that a check would
report: the counterexample of an expectation, a call's assumption,
definedness, completeness, disjointness, a precondition, a postcondition or
determinism, or the witness of a cover goal. A contradicted model is not
shown. The check is then inconclusive, as `eval::confirmed_verdict` makes a
refuted model's check, and Fren reports an internal error, an error at the
place where the check would have reported its result, in place of the
inconclusive result's warning: the summary counts the check as
inconclusive, but the run has an error, so a Lean build fails and `fren
check` exits with 1 (see [Check results](View.md#check-results)). It
names the first hypothesis that is `false`, in the query's order, or else
the goal, and shows the values as Fren read them:

```text
error: internal error: the solver's model for the expectation check of `m::p::e` makes its hypothesis `pinned` false in Fren's semantics
note: Fren reads the model as a = 0
note: so it is not shown as a counterexample or a witness, and the check is inconclusive
note: this is a bug in Fren: in reading the solver's model, or in translating the spec
```

`model::report` states it over the semantics: given the model's
interpretation and values as read, the free variables, and the query's
hypotheses and goal as expressions, the values are shown exactly where
`contradicted?` does not hold of them, with the free variables filled:

```fren
pub proc report(
    i: Interp,              -- the model's interpretation, as read
    env: Env,               -- the model's values of the query's variables, as read
    free: Free,             -- the variables that the model leaves free
    hypotheses: Expr<Id>,   -- the query's hypotheses, in order, as a list
    goal: Expr<Id>,         -- the query's goal
    solver: Verdict,        -- the verdict that the solver's answer gives
): (
    det shown?,             -- the values are shown, as a counterexample or a witness
    det internal?,          -- an internal error is reported instead
    det verdict: Verdict,
) {
    out shown? := not contradicted?(i, fill(env, free), hypotheses, goal)
    out internal? := not shown?
    out verdict := if shown? then solver else Inconclusive
}
```

`model::reported_real` is the statement at the top of this chapter: a
model shown is one in which, in Fren's semantics, no hypothesis is false
and the goal is not true, so a counterexample or a witness wherever the
semantics decides them. `report` refines it:

```fren
pub proc reported_real(
    no_false_hypothesis?,   -- in Fren's semantics, at the values shown, no hypothesis is false
    goal_not_true?,         -- nor is the goal true
    solver: Verdict,
): (shown?, internal?, verdict: Verdict) {
    ensure real: when shown?, no_false_hypothesis? and goal_not_true?
    ensure reported: shown? or internal?
    ensure kept: when shown?, verdict = solver
}

expect report_real(
    i: Interp,
    env: Env,
    free: Free,
    hypotheses: Expr<Id>,
    goal: Expr<Id>,
    solver: Verdict,
) {
    call r := report(i, env, free, hypotheses, goal, solver)
    refines r reported_real(
        not some_false?(i, fill(env, free), hypotheses),
        eval(i, fill(env, free), goal) != Outcome::Defined(Value::True),
        solver,
    )
}
```

Both front ends decide from the outcomes that their evaluators give, by
one function of the shared core, `Fren.Core.contradiction?`, which
implements `model::decision`: `report`'s rule over the list of the
hypotheses' outcomes and the goal's, which is what `report` reads of
`lang::eval`. That `decision` is `report`'s rule is by inspection: nothing
checks that the two agree at the outcomes that `lang::eval` gives, whose
lists they encode differently, a list of expressions for `report` and a
sequence of outcomes for `decision`. That `report` holds of the front ends
then rests on the agreement of their evaluators with `lang::eval` above:
tested for the `fren` command, over the forms that its test generates, and
trusted for the Lean-hosted front end.

```fren
set_option fren.lint.undecidable "allow" in
pub fn outcomes_contradicted?(hypotheses: Seq<Outcome>, goal: Outcome) :=
    Outcome::Defined(Value::False) in hypotheses or goal = Outcome::Defined(Value::True)

set_option fren.lint.undecidable "allow" in
pub proc decision(
    hypotheses: Seq<Outcome>,      -- each hypothesis of the query, in its order, at the values read
    goal: Outcome,                 -- the goal, likewise
    solver: Verdict,
): (det shown?, det internal?, det verdict: Verdict) {
    ensure shows: shown? iff not outcomes_contradicted?(hypotheses, goal)
    ensure errs: internal? iff not shown?
    ensure kept: when shown?, verdict = solver
    ensure inconclusive: unless shown?, verdict = Inconclusive
}
```

### What is not confirmed

The other values that checks report from models are not confirmed, since
none is a counterexample or a witness of the query whose model it is:

- the input of a [realizability](Check.md#realizability) conflict: its
  query's goal is that some outputs satisfy the guarantees, `∃ o. R`, which
  evaluation decides only by searching for outputs, and a search that finds
  none decides nothing. The `fren` command's [confirmation of every
  model](Eval.md#confirming-models) refutes one for which its search finds
  outputs, of their declared types, subset types included, as the query's
  `∃ o` ranges over them: an output that the guarantees allow but its type
  does not refutes nothing (`test/ui/checks/realizable_subset_outputs.fren`);
- the [forced outputs](Check.md#forced-outputs) of a conflict's clash
  notes, which come from models of parts of the guarantees, not of the
  query reported;
- the values of the members of a [Boolean block](Lang/BooleanBlocks.md),
  which are read from the model of the reported query, but are shown only
  where the model also gives their guards, as values, not as a behaviour.
  They are part of what a model shows, so a model that is not shown shows
  none of them: they would say, of the same model, what the internal error
  says is not a behaviour.

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

```fren
#fren_check
```
