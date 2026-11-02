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

The front ends' confirmation is *sound*: each value that it gives a
formula is the formula's value in every *completion* of what is unknown
to it, that is, whatever values the unknown parts take, as the language's
unspecified values do in a behaviour (see [Outcomes and
well-definedness](Lang/Semantics.md#outcomes-and-well-definedness)), and
so in the solver's interpretation too. That is all that it promises.

It may know less than `lang::eval`: a formula that a front end does not
evaluate, such as one that applies an uninterpreted function in the
Lean-hosted front end (see [Known values](#known-values)), is undecided to
it, and if every hypothesis and the goal are, its model is shown on the
solver's word, though `contradicted?` might refute it. And it may know
more, by the rules of [Known values](#known-values) that extend
`lang::eval`'s, which `model::known_eval` states, and no other: the strong
Kleene connectives for `and`, `or`, `not` and `when`; an `if` whose
condition is unknown and whose branches are known and equal; a table or a
`match` as the chain of `if`s that it is, its rows' conditions or its
arms' tests and guards, so that one whose condition or scrutinee is
unknown is known where the rows or arms that may be taken are known and
equal; and a count, `exactly_one?`, `at_most_one?` or one spelled out as a
sum of `if c then 1 else 0` compared with 1, that its unknown conditions
cannot change. So it may refute a model that `contradicted?` finds
undecided, where every completion contradicts it: a hypothesis
`q[5] = 0 and a = 1` is `false` to the front ends at `q = []` and `a = 2`,
though `lang::eval`, which evaluates `and` left to right, leaves it
undefined. Such a model is no behaviour of the spec in any interpretation.
So a model that a front end shows is one in which no hypothesis that it
decides is `false` and the goal is not `true` if it decides it, which is
`model::reported_real` wherever it decides them all
(`model::confirmed_report`, under [Reporting](#reporting)).

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
  them, with the defined functions and clauses that a formula applies
  unfolded, as a query's are. That it agrees with `lang::eval` on the
  formulas it decides is **trusted**: nothing checks the generated
  definitions against `lang::eval`.

Where one front end decides a formula that the other leaves undefined,
they may disagree about a model, but only about one that every completion
contradicts. That neither finds a correct model contradicted rests on the
evidence above: tested for the `fren` command, trusted for the Lean-hosted
front end. Beyond that, the ui tests and Fren's own requirements, which
`fren check` checks in `lake test` and Lean on `main` ([Own
requirements](dev/Testing.md#own-requirements)), run both front ends over
every model that they report, so a confirmation that refuted a correct
model would fail them.

#### Known values

Lean's definitions give a value where Fren's semantics gives none:
`default` for an index out of range, and so for a table or `match` where
no row or arm is taken, which is an index of the empty sequence. So the
Lean-hosted front end reads each index as unknown out of range, as the
`fren` command's evaluator does, and as enumeration does in both (see
[Searching](Check.md#searching)), by the same code.

A formula's value is then known only where no index out of range can
change it. Both front ends' evaluators decide it by the same functions of
the shared core, from the outcomes of each form's operands:

- `and`, `or`, `not` and `when` by the strong Kleene connectives
  (`check::partial_and` and `check::partial_not`), which know more than
  `lang::and_value` and `lang::or_value`: `q[5] = 0 and false` is `false`,
  where `lang::eval`, which evaluates `and` left to right, leaves it
  undefined;
- an `if` where its condition is known and so is the branch it takes, as
  `lang::if_value` has it, and also where its condition is unknown and
  both branches are known and equal (`model::known_if`, which
  `Fren.Core.iteKnown` implements);
- a table as the chain of `if`s that `lang` writes it as, a row's
  condition each `if`'s, and a `match` likewise, an arm's test and guard,
  by the strong Kleene conjunction, each `if`'s condition, and its body in
  an environment with its binders bound, or unknown where the scrutinee is
  (`model::unknown_binders`), the test being known only of an irrefutable
  pattern there. So `match q[5] { 0 => a = 1, _ => a = 1 }` is `a = 1`,
  where `lang::eval`, whose `match` is strict in its scrutinee, leaves it
  undefined. Both front ends write them so: the Lean-hosted front end's
  Lean definitions are those `if`s, and the `fren` command's evaluator
  decides a table or a `match` as them where a condition, a guard or the
  scrutinee is unknown (`chainKnown`). An irrefutable pattern is `_`, a
  binder, or alternatives of which one is; a pattern that covers the
  scrutinee's type only by its type, as `E::P(_) | E::Q` does, or the last
  arm of a complete `match`, is not, since `lang::Expr` has no types:
  where the scrutinee is unknown, such an arm's test is unknown too. The
  Lean-hosted front end writes the last arm of a complete `match`, which
  has no test there, as `Fren.lastArm` of the scrutinees, which it knows
  only where it knows them; and a `Prop` that a table or a `match` reads
  where no row or arm is taken as `Bool`'s unspecified value, which has a
  decision, so that a table whose last row is `true` is decided as its
  `if`s are;
- `exactly_one?` and `at_most_one?` where their unknown arguments cannot
  change the count's comparison with 1 (`check::cardinality_truth`, which
  `Fren.Core.Cardinality.holds?` implements), which knows more than
  `lang::count_value`: `at_most_one?(true, true, q[5] = 0)` is `false`,
  where `lang::eval` leaves it undefined. A count spelled out, a sum of
  `if c then 1 else 0` and of literals that are not negative compared with
  1 by `=`, `<=` or `>=`, as `(if q[5] = 0 then 1 else 0) + 2 <= 1`, each
  integer a literal, negated or not, or a constant (`model::integer_of`),
  as both front ends read a constant by its value and `-0` as 0, is
  decided as the count of its conditions, an integer `k` as `k` of them
  that are `true`, as `exactly_one?` and `at_most_one?` are defined
  (`Reqs/Lang/Expressions#cardinality`): the Lean-hosted front end sees
  the same term for both;
- any other operation, and an application of a function, exactly as
  `lang::eval` has it: where every operand is known, and so is the result
  at them (`model::known_application`, which `Fren.Core.appliedKnown`
  implements).

The extensions are sound, as [Confirmation](#confirmation) says: each
value that they give is the formula's in every completion of the unknown
operands. `and_sound`, `or_sound` and `if_sound` below state it of each
rule, at each completion of an unknown operand by a value, and
`check::cardinality_truth`'s rules state it of a count, at each number of
its unknown arguments that may be `true`. A table or a `match` is sound as
its `if`s are. A formula's soundness follows from its parts', by induction
on the formula: a part whose value is known has it in every completion,
and one whose value is unknown has some value in each, which the rule
above it was shown to be sound at.

Each rule reads only its operands' outcomes. Which forms each rule is
applied to is `model::known_eval`'s, below: `lang::eval` with the rules
above, and every other form strict, exactly as `lang::eval` has it, so
that an extension that it does not list is a difference from it. The
`fren` command's evaluator is tested against it, and the Lean-hosted
front end against the `fren` command, by the fuzzer's `--confirm` mode.

An application does not extend in the same way. Its value can also be the
same in every completion of an unknown argument, as `ign?(q[5])` is when
`ign?`'s body never reads its parameter. But seeing that needs the body
evaluated with the argument
unknown, which neither front end can do for every function: a structural
recursion's body is not unfolded, nor is an uninterpreted function's, and
a defined function's is unfolded only where the formula is. So an
application is strict, as `lang::eval`'s is: unknown where an argument is,
even one that the body never reads. Both front ends unfold a defined
function's body, which drops such an argument, so each keeps the
arguments to decide this. The Lean-hosted front end reads the formula as
written as well as unfolded, and the `fren` command keeps the arguments
beside the body that it substitutes them into (`Ex.strict`). This holds
only in a model's confirmation. Enumeration asks whether a check's answer
could change with the unspecified values, and an argument that a body
never reads cannot change it.

`model::known_application` and `model::known_if` state two of the rules
over whether the operands' values are known, which is what each front end
computes of its own representation. `application_known`, `if_known`,
`and_known`, `or_known` and `count_known` relate the rules to
`lang::eval`, with each input computed by `lang::eval` from the
expressions themselves: an application's rule is exactly `lang::eval`'s,
an `if`'s is wherever its condition is known, and the connectives' and
counts' rules give every truth that `lang::eval` gives, and the same one.
`and_sound`, `or_sound` and `if_sound` state the extensions' soundness
over outcomes, at every completion of the unknown ones. `known_eval`
states every rule at once, over the forms of `lang::Expr`, and
`known_agrees` that it gives every value that `lang::eval` gives, and the
same one, and `known_sound` that completing a variable that it does not
know never changes a value that it knows, which checks every rule at once.
The solver cannot unfold `eval`, a structural recursion without a
contract, so random testing checks them, as it does `lang::coincidence`.

```fren
use check::{CountOp, Truth, cardinality_truth, partial_and, partial_not}
use lang::{
    BinaryOp,
    Cardinality,
    Params,
    Pattern,
    UnaryOp,
    and_value,
    binary_value,
    bind,
    bind_params,
    call_value,
    cons_value,
    construct_value,
    count_value,
    if_value,
    index_value,
    is_value,
    lookup,
    matches_value?,
    method_value,
    or_value,
    project_value,
    truth,
    unary_value,
}

set_option fren.lint.undecidable "allow" in
pub proc known_application(
    arguments: Seq<Bool>,   -- whether each argument's value is known
    body_known?,            -- whether the body's value is known at them
): (det known?) {
    ensure strict: known? iff body_known? and not false in arguments
}

pub proc known_if(
    condition: Truth,   -- the condition's truth
    then_known?,        -- whether the value of the branch taken where it is true is known
    else_known?,        -- likewise, where it is false
    same?,              -- whether the two branches' values are equal
): (det known?) {
    use check::Truth::{False, True, Unknown}
    ensure rule: known? iff match condition {
        True => then_known?,
        False => else_known?,
        Unknown => then_known? and else_known? and same?,
    }
}

-- Whether an outcome is a value.
pub fn defined?(o: Outcome) := o != Outcome::Undefined

-- The truth that an outcome is, `Unknown` for one that is not a `Bool`.
pub fn truth_of(o: Outcome): Truth := match o {
    Outcome::Defined(Value::True) => Truth::True,
    Outcome::Defined(Value::False) => Truth::False,
    _ => Truth::Unknown,
}

-- Whether the value of each expression of the list `args` is known, in order.
set_option fren.lint.undecidable "allow" in
pub fn args_known(i: Interp, env: Env, args: Expr<Id>): Seq<Bool> := match args {
    Expr::Cons(a, rest) => [defined?(eval(i, env, a))] ++ args_known(i, env, rest),
    _ => [],
}

-- Whether the body's value is known at the arguments' values, where they have them.
pub fn body_defined?(i: Interp, env: Env, args: Expr<Id>, ps: Params<Id>, body: Expr<Id>) :=
    match eval(i, env, args) {
        Outcome::Defined(l) => defined?(eval(i, bind_params(ps, l), body)),
        Outcome::Undefined => false,
    }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect application_known(
    i: Interp,
    env: Env,
    f: Id,
    args: Expr<Id>,
    ps: Params<Id>,
    body: Expr<Id>,
) {
    call k := known_application(
        args_known(i, env, args),
        body_defined?(i, env, args, ps, body),
    )
    expect exact: k.known? iff defined?(eval(i, env, Expr::Apply(f, args, ps, body)))
}

set_option fren.evidence "random" in
expect if_known(i: Interp, env: Env, c: Expr<Id>, t: Expr<Id>, f: Expr<Id>) {
    call k := known_if(
        truth_of(eval(i, env, c)),
        defined?(eval(i, env, t)),
        defined?(eval(i, env, f)),
        eval(i, env, t) = eval(i, env, f),
    )
    -- Where the condition is known, exactly the values that evaluation gives.
    expect exact_where_known: unless truth_of(eval(i, env, c)) = Truth::Unknown,
        k.known? iff defined?(eval(i, env, Expr::If(c, t, f)))
}

set_option fren.evidence "random" in
expect and_known(i: Interp, env: Env, a: Expr<Id>, b: Expr<Id>) {
    call k := partial_and(truth_of(eval(i, env, a)), truth_of(eval(i, env, b)))
    -- Where evaluation gives `a and b` a truth, the Kleene conjunction gives the same.
    expect agrees: unless truth_of(eval(i, env, Expr::And(a, b))) = Truth::Unknown,
        k.truth = truth_of(eval(i, env, Expr::And(a, b)))
}

set_option fren.evidence "random" in
expect or_known(i: Interp, env: Env, a: Expr<Id>, b: Expr<Id>) {
    -- The Kleene disjunction, as the conjunction's dual.
    call na := partial_not(truth_of(eval(i, env, a)))
    call nb := partial_not(truth_of(eval(i, env, b)))
    call both := partial_and(na.truth, nb.truth)
    call k := partial_not(both.truth)
    expect agrees: unless truth_of(eval(i, env, Expr::Or(a, b))) = Truth::Unknown,
        k.truth = truth_of(eval(i, env, Expr::Or(a, b)))
}

-- How many of the list `args`'s values are `true`, and how many are unknown.
pub fn trues_of(i: Interp, env: Env, args: Expr<Id>): Nat := match args {
    Expr::Cons(a, rest) => (if eval(i, env, a) = Outcome::Defined(Value::True) then 1 else 0)
        + trues_of(i, env, rest),
    _ => 0,
}

pub fn unknowns_of(i: Interp, env: Env, args: Expr<Id>): Nat := match args {
    Expr::Cons(a, rest) => (if defined?(eval(i, env, a)) then 0 else 1) + unknowns_of(i, env, rest),
    _ => 0,
}

pub fn count_op(c: Cardinality): CountOp := match c {
    Cardinality::Exactly => CountOp::Exactly,
    Cardinality::AtMost => CountOp::AtMost,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect count_known(i: Interp, env: Env, c: Cardinality, args: Expr<Id>) {
    call k := cardinality_truth(
        count_op(c),
        trues_of(i, env, args),
        unknowns_of(i, env, args),
    )
    -- Where evaluation gives a count a truth, the count's rule gives the same.
    expect agrees: unless truth_of(eval(i, env, Expr::Count(c, args))) = Truth::Unknown,
        k.truth = truth_of(eval(i, env, Expr::Count(c, args)))
}

-- `o`, or, where it is not a value, the truth `x?`: a completion of it.
pub fn complete(o: Outcome, x?): Outcome := match o {
    Outcome::Undefined => Outcome::Defined(truth(x?)),
    _ => o,
}

-- An outcome that is a truth or unknown, as a formula's is.
pub fn boolean?(o: Outcome) := o = Outcome::Undefined or truth_of(o) != Truth::Unknown

-- The Kleene conjunction's truth is `and`'s in every completion of its unknown operands.
set_option fren.evidence "random" in
expect and_sound(a: Outcome, b: Outcome, x?, y?) {
    assume typed: boolean?(a) and boolean?(b)
    call k := partial_and(truth_of(a), truth_of(b))
    expect sound: unless k.truth = Truth::Unknown,
        truth_of(and_value(complete(a, x?), complete(b, y?))) = k.truth
}

set_option fren.evidence "random" in
expect or_sound(a: Outcome, b: Outcome, x?, y?) {
    assume typed: boolean?(a) and boolean?(b)
    call na := partial_not(truth_of(a))
    call nb := partial_not(truth_of(b))
    call both := partial_and(na.truth, nb.truth)
    call k := partial_not(both.truth)
    expect sound: unless k.truth = Truth::Unknown,
        truth_of(or_value(complete(a, x?), complete(b, y?))) = k.truth
}

-- Where `known_if` knows an `if`'s value, it is the same in every completion
-- of the condition: the branch taken's, or both branches' where they are equal.
set_option fren.evidence "random" in
expect if_sound(c: Outcome, t: Outcome, f: Outcome, x?) {
    assume typed: boolean?(c)
    call k := known_if(truth_of(c), defined?(t), defined?(f), t = f)
    expect sound: when k.known?,
        if_value(complete(c, x?), t, f) = (if truth_of(c) = Truth::False then f else t)
}

-- A pattern's binders bound to unknown values, for an arm whose scrutinee is unknown, as `bind` binds them.
pub fn unknown_binders(p: Pattern<Id>, env: Env): Env := match p {
    Pattern::Binder(x) => Env::Bind(x, Outcome::Undefined, env),
    Pattern::Variant(_, ps) => unknown_binders(ps, env),
    Pattern::Cons(first, rest) => unknown_binders(rest, unknown_binders(first, env)),
    _ => env,
}

-- Whether a pattern matches every value.
pub fn irrefutable?(p: Pattern<Id>) := match p {
    Pattern::Wildcard | Pattern::Binder(_) => true,
    Pattern::Or(a, b) => irrefutable?(a) or irrefutable?(b),
    _ => false,
}

-- The rules of the connectives and of `if`, over the operands' outcomes:
-- `lang::eval`'s where it gives a value, and the extensions' elsewhere.
pub fn known_and(a: Outcome, b: Outcome): Outcome := match a {
    Outcome::Defined(Value::True) => b,
    Outcome::Defined(Value::False) => Outcome::Defined(Value::False),
    _ => if b = Outcome::Defined(Value::False) then b else Outcome::Undefined,
}

pub fn known_or(a: Outcome, b: Outcome): Outcome := match a {
    Outcome::Defined(Value::True) => Outcome::Defined(Value::True),
    Outcome::Defined(Value::False) => b,
    _ => if b = Outcome::Defined(Value::True) then b else Outcome::Undefined,
}

pub fn known_if_value(c: Outcome, t: Outcome, f: Outcome): Outcome := match c {
    Outcome::Defined(Value::True) => t,
    Outcome::Defined(Value::False) => f,
    _ => if t = f then t else Outcome::Undefined,
}

-- A count's truth, of `trues` arguments `true` and `unknowns` unknown, as
-- `cardinality_truth` gives it: the same at every number of the unknown
-- ones that may be `true`, or unknown.
pub fn count_truth(c: Cardinality, trues: Int, unknowns: Int): Outcome := match c {
    Cardinality::AtMost => if trues >= 2 then Outcome::Defined(Value::False)
        else if trues + unknowns <= 1 then Outcome::Defined(Value::True) else Outcome::Undefined,
    Cardinality::Exactly => if trues >= 2 or trues + unknowns = 0 then Outcome::Defined(Value::False)
        else if trues = 1 and unknowns = 0 then Outcome::Defined(Value::True) else Outcome::Undefined,
}

-- Whether a value is an integer that is not negative.
pub fn natural?(v: Value) := match v {
    Value::Integer(k) => k >= 0,
    _ => false,
}

-- The value of `e` where it is a literal, negated or not, or a constant,
-- which `lang` writes as an application of no arguments to its definition:
-- as both front ends read an integer in a count spelled out, a constant by
-- its value.
pub fn integer_of(i: Interp, e: Expr<Id>): Outcome := match e {
    Expr::Literal(v) => Outcome::Defined(v),
    Expr::Unary(UnaryOp::Neg, Expr::Literal(v)) => unary_value(UnaryOp::Neg, Outcome::Defined(v)),
    Expr::Apply(_, args, _, body) => if args = Expr::Nil then eval(i, Env::Empty, body) else Outcome::Undefined,
    _ => Outcome::Undefined,
}

pub fn natural_outcome?(o: Outcome) := match o {
    Outcome::Defined(v) => natural?(v),
    Outcome::Undefined => false,
}

-- Whether `e` is a sum of `if c then 1 else 0` and of integers that are not
-- negative, each a literal, negated or not, or a constant (`integer_of`).
pub fn spelled?(i: Interp, e: Expr<Id>) := match e {
    Expr::Binary(op, a, b) => op = BinaryOp::Add and spelled?(i, a) and spelled?(i, b),
    Expr::If(_, t, f) => integer_of(i, t) = Outcome::Defined(Value::Integer(1))
        and integer_of(i, f) = Outcome::Defined(Value::Integer(0)),
    Expr::Literal(v) => natural?(v),
    Expr::Unary(_, _) | Expr::Apply(_, _, _, _) => natural_outcome?(integer_of(i, e)),
    _ => false,
}

-- Whether `e` is a list of expressions, `Nil` or `Cons(a, rest)`.
pub fn list_expr?(e: Expr<Id>) := match e {
    Expr::Cons(_, rest) => list_expr?(rest),
    Expr::Nil => true,
    _ => false,
}

-- The count that `a op 1` spells out: `exactly_one?` for `=`, `at_most_one?` for `<=`.
pub fn spelled_count(op: BinaryOp): Cardinality := match op {
    BinaryOp::Eq => Cardinality::Exactly,
    _ => Cardinality::AtMost,
}

pub fn counts?(i: Interp, op: BinaryOp, a: Expr<Id>, b: Expr<Id>) :=
    op is BinaryOp::Eq | BinaryOp::Le and integer_of(i, b) = Outcome::Defined(Value::Integer(1))
    and spelled?(i, a)

pub fn number(o: Outcome): Int := match o {
    Outcome::Defined(Value::Integer(n)) => n,
    _ => 0,
}

pub fn one_if(b?): Outcome := Outcome::Defined(Value::Integer(if b? then 1 else 0))

pub fn plus(a: Outcome, b: Outcome): Outcome := Outcome::Defined(
    Value::Integer(number(a) + number(b))
)

-- What `known` gives of an expression: its outcome, or, of a list or a sum
-- spelled out, how many of its conditions are `true`, or how many unknown.
pub enum Want { Value, Trues, Unknowns }

-- An arm's test where its scrutinee is unknown: `true` of an irrefutable
-- pattern, else unknown.
pub fn test_of(p: Pattern<Id>): Outcome :=
    if irrefutable?(p) then Outcome::Defined(Value::True) else Outcome::Undefined

-- An expression's outcome as confirmation knows it: `lang::eval`'s rules,
-- with the extensions of `Reqs/Models#known-values` and no others.
pub fn known(i: Interp, env: Env, e: Expr<Id>, w: Want): (r: Outcome) {
    -- Only a list, a sum spelled out and their parts are asked for a count
    -- (`list_expr?`, `spelled?`): every other form gives its outcome.
    out r := match e {
        Expr::Literal(v) => match w {
            Want::Value => Outcome::Defined(v),
            Want::Trues => Outcome::Defined(Value::Integer(number(Outcome::Defined(v)).min(2))),
            Want::Unknowns => Outcome::Defined(Value::Integer(0)),
        },
        Expr::Var(x) => lookup(env, x),
        Expr::Let(x, d, b) => known(
            i,
            Env::Bind(x, known(i, env, d, Want::Value), env),
            b,
            Want::Value
        ),
        Expr::Unary(op, a) => match w {
            Want::Value => unary_value(op, known(i, env, a, Want::Value)),
            -- A negated literal in a count spelled out, by its value.
            Want::Trues => Outcome::Defined(Value::Integer(number(integer_of(i, e)).min(2))),
            Want::Unknowns => Outcome::Defined(Value::Integer(0)),
        },
        Expr::Binary(op, a, b) => match w {
            Want::Value => if counts?(i, op, a, b) then count_truth(
                spelled_count(op),
                number(known(i, env, a, Want::Trues)),
                number(known(i, env, a, Want::Unknowns))
            ) else binary_value(i, op, known(i, env, a, w), known(i, env, b, w)),
            _ => plus(known(i, env, a, w), known(i, env, b, w)),
        },
        Expr::And(a, b) => known_and(known(i, env, a, Want::Value), known(i, env, b, Want::Value)),
        Expr::Or(a, b) => known_or(known(i, env, a, Want::Value), known(i, env, b, Want::Value)),
        Expr::If(c, t, f) => match w {
            Want::Value => known_if_value(
                known(i, env, c, w),
                known(i, env, t, w),
                known(i, env, f, w)
            ),
            Want::Trues => one_if(
                known(i, env, c, Want::Value) = Outcome::Defined(Value::True)
            ),
            Want::Unknowns => one_if(truth_of(known(i, env, c, Want::Value)) = Truth::Unknown),
        },
        Expr::Is(s, p) => is_value(p, known(i, env, s, Want::Value)),
        Expr::Match(s, p, g, b, rest) => match known(i, env, s, Want::Value) {
            Outcome::Defined(v) => if matches_value?(p, v) then known_if_value(
                known(i, bind(p, v, env), g, Want::Value),
                known(i, bind(p, v, env), b, Want::Value),
                known(i, env, rest, Want::Value)
            ) else known(i, env, rest, Want::Value),
            Outcome::Undefined => known_if_value(
                known_and(
                    test_of(p),
                    known(i, unknown_binders(p, env), g, Want::Value)
                ),
                known(i, unknown_binders(p, env), b, Want::Value),
                known(i, env, rest, Want::Value)
            ),
        },
        Expr::NoMatch => Outcome::Undefined,
        Expr::Nil => Outcome::Defined(Value::Nil),
        Expr::Cons(a, rest) => match w {
            Want::Value => cons_value(known(i, env, a, w), known(i, env, rest, w)),
            Want::Trues => plus(
                one_if(
                    known(i, env, a, Want::Value) = Outcome::Defined(Value::True)
                ),
                known(i, env, rest, w)
            ),
            Want::Unknowns => plus(
                one_if(truth_of(known(i, env, a, Want::Value)) = Truth::Unknown),
                known(i, env, rest, w)
            ),
        },
        Expr::Construct(c, args) => construct_value(c, known(i, env, args, Want::Value)),
        Expr::Project(a, c, k) => project_value(known(i, env, a, Want::Value), c, k),
        Expr::Index(q, k) => index_value(
            known(i, env, q, Want::Value),
            known(i, env, k, Want::Value)
        ),
        Expr::Method(m, receiver, args) => method_value(
            m,
            known(i, env, receiver, Want::Value),
            known(i, env, args, Want::Value)
        ),
        Expr::Count(c, args) => if list_expr?(args) then count_truth(
            c,
            number(known(i, env, args, Want::Trues)),
            number(known(i, env, args, Want::Unknowns))
        ) else count_value(c, known(i, env, args, Want::Value)),
        Expr::Apply(_, args, ps, body) => match w {
            Want::Value => match known(i, env, args, Want::Value) {
                Outcome::Defined(l) => known(i, bind_params(ps, l), body, Want::Value),
                Outcome::Undefined => Outcome::Undefined,
            },
            -- A constant in a count spelled out, likewise.
            Want::Trues => Outcome::Defined(Value::Integer(number(integer_of(i, e)).min(2))),
            Want::Unknowns => Outcome::Defined(Value::Integer(0)),
        },
        Expr::Call(f, args) => call_value(i.functions, f, known(i, env, args, Want::Value)),
        Expr::Recur(f, args) => call_value(i.recursions, f, known(i, env, args, Want::Value)),
    }
}

pub fn known_eval(i: Interp, env: Env, e: Expr<Id>): Outcome := known(i, env, e, Want::Value)

-- Completing a variable that it does not know, by any value, never changes
-- a value that it knows: soundness over the whole evaluator, at every rule.
set_option fren.evidence "random" in
expect known_sound(i: Interp, env: Env, x: Id, v: Value, e: Expr<Id>) {
    expect same: when defined?(known_eval(i, Env::Bind(x, Outcome::Undefined, env), e)),
        known_eval(i, Env::Bind(x, Outcome::Defined(v), env), e)
        = known_eval(i, Env::Bind(x, Outcome::Undefined, env), e)
}

-- It gives every value that `lang::eval` gives, and the same one.
set_option fren.evidence "random" in
expect known_agrees(i: Interp, env: Env, e: Expr<Id>) {
    expect agrees: when defined?(eval(i, env, e)), known_eval(i, env, e) = eval(i, env, e)
}

-- Its count's rule is `cardinality_truth`'s.
set_option fren.lint.undecidable "allow" in
expect count_rule(c: Cardinality, trues: Nat, unknowns: Nat) {
    call k := cardinality_truth(count_op(c), trues, unknowns)
    expect same: truth_of(count_truth(c, trues, unknowns)) = k.truth
}
```

A quotient or remainder is by a constant that is not 0 (see [Division and
remainder](Lang/Expressions.md#division-and-remainder)), where Lean's value
is Fren's, so the Lean-hosted front end evaluates it as Lean does.

A value of an abstract type, or of a generic function's type parameter,
which is one, is the `k`th value of its type, as `T#k` shows it, and is
compared only with `=`, as the `fren` command compares it.

The formulas that the Lean-hosted front end does not evaluate are
`Undefined` to it:

- those that apply an uninterpreted function, or read a free variable
  without a default value;
- those whose value an index under a binder, such as a quantifier's or a
  `match` arm's, may change;
- those that read an index within a definition that is not unfolded, a
  structural recursion's.

A generated [selector](Generated.md) of a payload is total in the same way
as an index, by a `| _ => default` arm for the other variants, but it is
not read as unknown. A read of a payload is evaluated only where the
model's value has the variant that a `match` arm or a pattern test
matched, since every such read is under the `ite` of that test, which
Lean's definitions do not evaluate on the branch not taken; and a `match`
that may take no arm reads the empty sequence, an index.

`test/ui/misread/misread_index.fren` checks that both front ends catch a
misread in an index, a quotient and a remainder; that neither refutes a
model by an index out of range; and that both leave unknown an application
whose argument is. `test/ui/misread/misread_type_parameter.fren` checks
that both catch one in a formula that compares values of an abstract type
or of a type parameter.

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
sequence of outcomes for `decision`.

The front ends do not implement `report` itself, since their evaluators
are not `lang::eval` (see [Confirmation](#confirmation)). They may refute
a model that `report` shows, where every completion contradicts it, and
they show a model whose hypotheses and goal they leave undecided on the
solver's word. What holds of them is one direction, which
`model::confirmed_report` states: they decide by `decision` over the
outcomes that `model::known_eval` gives, so a model that they show is one
that `known_eval` does not contradict, and so one in which no hypothesis
is `false` and the goal is not `true` in `lang::eval`, which is
`reported_real` (`confirmed_real`). A front end whose evaluator knows less
than `known_eval`, as the Lean-hosted one does of the formulas that it
does not evaluate, shows a model that `known_eval` would refute where the
formulas that decide it are those, on the solver's word. That `known_eval`
gives every value that `lang::eval` gives is `known_agrees`, by random
testing. That the front ends' evaluators are `known_eval` is tested for
the `fren` command, over the forms that `src/FrenTest/Semantics.lean`
generates, and checked against it for the Lean-hosted front end by the
fuzzer's `--confirm` mode.

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

-- Whether `known_eval` finds a hypothesis `false` or the goal `true`.
pub fn some_known_false?(i: Interp, env: Env, hypotheses: Expr<Id>) := match hypotheses {
    Expr::Cons(h, rest) => known_eval(i, env, h) = Outcome::Defined(Value::False)
        or some_known_false?(i, env, rest),
    _ => false,
}

pub fn known_contradicted?(i: Interp, env: Env, hypotheses: Expr<Id>, goal: Expr<Id>) :=
    some_known_false?(i, env, hypotheses) or known_eval(i, env, goal) = Outcome::Defined(Value::True)

-- What the front ends do with a model: decide by `decision` over the
-- outcomes that `known_eval` gives.
pub proc confirmed_report(
    i: Interp,              -- the model's interpretation, as read
    env: Env,               -- the model's values of the query's variables, as read, the free ones filled
    hypotheses: Expr<Id>,   -- the query's hypotheses, in order, as a list
    goal: Expr<Id>,         -- the query's goal
    solver: Verdict,
): (det shown?, det internal?, det verdict: Verdict) {
    out shown? := not known_contradicted?(i, env, hypotheses, goal)
    out internal? := not shown?
    out verdict := if shown? then solver else Inconclusive
}

-- A model that is shown is one in which, in `lang::eval`, no hypothesis is
-- `false` and the goal is not `true`: `reported_real`'s `real`, since
-- `known_eval` gives every value that `lang::eval` gives.
set_option fren.evidence "random" in
expect confirmed_real(i: Interp, env: Env, hypotheses: Expr<Id>, goal: Expr<Id>, solver: Verdict) {
    call r := confirmed_report(i, env, hypotheses, goal, solver)
    expect real: when r.shown?,
        not some_false?(i, env, hypotheses) and eval(i, env, goal) != Outcome::Defined(Value::True)
    expect kept: when r.shown?, r.verdict = solver
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
