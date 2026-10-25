# Glossary

**Abstract type.** A type whose values the spec does not describe,
declared with `type`. See [Types](Lang/Types.md#abstract-types).

**Admissible input.** An input that satisfies the component's assumptions.

**Assumption.** A constraint on a component's inputs, declared with
`assume`: what the environment promises. See [Components](Lang/Components.md).

**Behaviour.** An interpretation, with a value for each of a component's
variables, including its instances'. See [Evaluation and
testing](Eval.md#behaviours).

**Component.** A part of a system, described by its inputs, outputs and
constraints, declared with `comp`. See [Components](Lang/Components.md).

**Constant.** A name for a fixed value, declared with `const`. See
[Items](Lang/Items.md#constants).

**Constraint.** An assumption, requirement or expectation.

**Counterexample.** Values of a component's variables that satisfy the
hypotheses of a check but not its goal. See [Checks](Check.md).

**Defined output.** An output declared with a definition, `out x: T :=
e`, which stands for `e`. See [Components](Lang/Components.md#defined-outputs).

**Determined.** Of an output: taking the same value in every behaviour
that meets the component, for each admissible input. An output declared
with `det out` must be determined. See [Checks](Check.md#determinism).

**Enumeration.** A type whose values are each one of a fixed set of named
variants, with the variant's payload, declared with `enum`. See
[Items](Lang/Items.md#enumerations).

**Divisor.** The right operand of `div` or `mod`: an integer literal or a
constant other than `0`. See
[Expressions](Lang/Expressions.md#division-and-remainder).

**Environment.** Whatever chooses a component's inputs.

**Expectation.** A claim, declared with `expect`, that follows from a
component's assumptions and requirements, and that the checks confirm.

**Function.** Declared with `fn`. A defined function, written with `:=
e`, has the value of its body `e`. Of an uninterpreted function, the spec
says only its type. See [Items](Lang/Items.md#functions).

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

**Match.** An expression that reads which variant a value is, and its
payload. See [Expressions](Lang/Expressions.md#matches).

**Member.** A declaration inside a component: an input, output, constraint
or instance.

**Output.** A variable of a component chosen by the system, declared with
`out`. A *public output* is declared with `pub out`; other outputs are
private.

**Pattern test.** An expression `e is P`, which is `true` exactly when the
pattern `P`, as of a `match` arm but binding no names, matches `e`. See
[Expressions](Lang/Expressions.md#pattern-tests).

**Payload.** The values that a variant carries, as in `Circle(Int)`. See
[Items](Lang/Items.md#enumerations).

**Realizable.** Of a component: some system can meet its requirements for
every admissible input. See [Checks](Check.md#realizability).

**Record.** A type whose values each have a value for each of its named
fields, declared with `struct`. See [Items](Lang/Items.md#records).

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

**Variant.** One of the alternatives of an enumeration, carrying a payload
or not.
