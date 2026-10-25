# Glossary

**Abstract type.** A type whose values the spec does not describe,
declared with `type`. See [Types](Lang/Types.md#abstract-types).

**Admissible input.** An input that satisfies the component's assumptions.

**Assumption.** A constraint on a component's inputs, declared with
`assume`: what the environment promises. See [Components](Lang/Components.md).

**Behaviour.** An interpretation, with a value for each of a component's
variables, including its instances'. See [Evaluation and
testing](Eval.md#behaviours).

**Cardinality operator.** One of the built-in functions `exactly_one?`
and `at_most_one?`, which hold when exactly one, or at most one, of their
`Bool` arguments is `true`. See [Expressions](Lang/Expressions.md#cardinality).

**Chained comparison.** Orderings written one after another, as in
`0 <= i < n`, which means `0 <= i and i < n`. See
[Expressions](Lang/Expressions.md#chained-comparisons).

**Component.** A part of a system, described by its inputs, outputs and
constraints, declared with `comp`. See [Components](Lang/Components.md).

**Constant.** A name for a fixed value, declared with `const`. See
[Items](Lang/Items.md#constants).

**Constraint.** An assumption, requirement, expectation or cover goal.

**Counterexample.** Values of a component's variables that satisfy the
hypotheses of a check but not its goal. See [Checks](Check.md).

**Cover goal.** A scenario that a component must allow, declared with
`cover`: some behaviour that meets the component's assumptions and
requirements must satisfy it. See [Components](Lang/Components.md#cover-goals).

**Defined output.** An output declared with a definition, `out x: T :=
e`, which stands for `e`. See [Components](Lang/Components.md#defined-outputs).

**Determined.** Of an output: taking the same value in every behaviour
that meets the component, for each admissible input. An output declared
with `det out` must be determined. See [Checks](Check.md#determinism).

**Enumeration.** A type whose values are each one of a fixed set of named
variants, with the variant's payload, declared with `enum`. See
[Items](Lang/Items.md#enumerations).

**Divisor.** The right operand of `div` or `mod`: an integer literal or a
constant, possibly negated or in parentheses, whose value is not `0`. See
[Expressions](Lang/Expressions.md#division-and-remainder).

**Environment.** Whatever chooses a component's inputs.

**Exhaustive.** Of a `match`: every value of its scrutinee's type matches
the pattern of some arm. See [Expressions](Lang/Expressions.md#matches).

**Expectation.** A claim, declared with `expect`, that follows from a
component's assumptions and requirements, and that the checks confirm.

**Function.** Declared with `fn`. A defined function, written with `:=
e`, has the value of its body `e`. Of an uninterpreted function, the spec
says only its type. The cardinality operators are built-in functions. See
[Items](Lang/Items.md#functions).

**Global expectation.** A claim about one or more components as a whole,
declared with `expect` outside any component, that the checks confirm. See
[Global expectations](Lang/Global.md).

**Implementation.** A Lean proof that Lean code meets a component, declared
with `impl`. See [Implementations](Impl.md).

**Inconclusive.** The verdict of a check that the solver could not decide.

**Integer constant expression.** An expression whose value Fren computes
when it reads a spec: integer literals and constants whose values are
integer constant expressions, combined by `+`, `-`, `*`, `div`, `mod`,
`abs`, `min` and `max`. A constant divisor's value is one. See
[Expressions](Lang/Expressions.md#division-and-remainder).

**Interpretation.** A meaning for each abstract type and function. The
checks consider every interpretation, and in Lean, `interp` fixes one. See
[Components](Lang/Components.md#interpretations).

**Input.** A variable of a component chosen by its environment, declared
with `in`.

**Instance.** A use of one component inside another, declared with `inst`.
See [Instances](Lang/Instances.md).

**Item.** A top-level declaration: a module, `use` declaration,
enumeration, record, abstract type, function, constant, component, global
expectation, check or claim. See [Items](Lang/Items.md).

**Lint.** A diagnostic about something allowed but probably not intended,
such as an unused import, whose level (`allow`, `warn`, `deny` or
`forbid`) can be set. See [Lints](Lint.md).

**Match.** An expression that has the value of the body of the first of its
arms whose pattern matches its scrutinee. See
[Expressions](Lang/Expressions.md#matches).

**Member.** A declaration inside a component: an input, output, constraint
or instance.

**Output.** A variable of a component chosen by the system, declared with
`out`. A *public output* is declared with `pub out`; other outputs are
private.

**Pattern.** What a `match` arm or a pattern test matches values against:
`_`, a binder, a literal, a range, a variant with patterns for its
payload, or an or-pattern. See [Patterns](Lang/Patterns.md).

**Pattern test.** An expression `e is P`, which is `true` exactly when the
pattern `P`, as of a `match` arm but binding no names, matches `e`. See
[Expressions](Lang/Expressions.md#pattern-tests).

**Payload.** The values that a variant carries, as in `Circle(Int)`. See
[Items](Lang/Items.md#enumerations).

**Range pattern.** A pattern that matches the integers between its
bounds, such as `0..=9`, `0..10`, `1..` and `..=-1`. See
[Patterns](Lang/Patterns.md#kinds-of-pattern).

**Reachable.** Of an arm of a `match`, or an alternative of an
or-pattern: matching some value that no arm or alternative before it
matches. See [Expressions](Lang/Expressions.md#matches).

**Realizable.** Of a component: some system can meet its requirements for
every admissible input. See [Checks](Check.md#realizability).

**Record.** A type whose values each have a value for each of its named
fields, declared with `struct`. See [Items](Lang/Items.md#records).

**Record update.** An expression `{ r with x := e }`: the value of `r`'s
record with `e` for `x` and `r`'s values for its other fields. See
[Expressions](Lang/Expressions.md#record-updates).

**Redundant.** Of an assumption or requirement: following from the
component's other constraints. See [Checks](Check.md#redundancy).

**Requirement.** A constraint on what the system must do, declared with
`req`.

**Shadowing.** A declaration hiding a name in scope, so that within the
declaration's scope the name means the declaration. It is written with
`!` after the declared name, as in `x!`. See
[Shadowing](Lang/Components.md#shadowing).

**Spec.** A sequence of items, in a Lean file, a `.fren` file or a
[Markdown spec](Markdown.md).

**System.** Whatever chooses a component's outputs.

**Trigger.** The condition under which a `when` or `unless` constraint
applies. See [Components](Lang/Components.md#triggers).

**Vacuous.** Of a constraint: holding only because its trigger can never
hold. See [Checks](Check.md#vacuity).

**Unbounded type.** A type with arbitrarily large values: a recursive
enumeration, or one with a field or payload of an unbounded type. See
[Types](Lang/Types.md#recursive-and-unbounded-types).

**Useful.** Of a vector of patterns, with respect to a matrix of them:
some values match the vector and no row of the matrix. See
[Patterns](Lang/Patterns.md#usefulness).

**Variant.** One of the alternatives of an enumeration, carrying a payload
or not.

**Widening.** Accepting a `Nat` where an `Int` is expected, the only
conversion between types. See [Types](Lang/Types.md#natural-numbers).

**Witness.** Values of a component's variables that satisfy the
hypotheses of a check that asks whether something can hold, and its goal,
such as a behaviour in which a cover goal holds. See [Checks](Check.md).
