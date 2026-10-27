# Glossary

**Abstract type.** A type whose values the spec does not describe,
declared with `type`. See [Types](Lang/Types.md#abstract-types).

**Admissible input.** An input that satisfies the procedure's assumptions.

**Assumption.** A constraint on a procedure's inputs, declared with
`assume`: what the environment promises. See [Procedures](Lang/Procedures.md).

**Behaviour.** An interpretation, with a value for each of a procedure's
variables, including its calls'. See [Evaluation and
testing](Eval.md#behaviours).

**Bound name.** A name that a quantifier's binder declares, standing for
one value of its type in each instance, or, in an unbounded quantifier,
for every value of a type that is not listed. See
[Quantifiers](Lang/Quantifiers.md).

**Call.** A use of one procedure inside another, declared with `call`,
whose arguments give the called procedure's parameters. See
[Calls](Lang/Calls.md).

**Cardinality operator.** One of the built-in functions `exactly_one?`
and `at_most_one?`, which hold when exactly one, or at most one, of their
`Bool` arguments is `true`. See [Expressions](Lang/Expressions.md#cardinality).

**Chained comparison.** Orderings written one after another, as in
`0 <= i < n`, which means `0 <= i and i < n`. See
[Expressions](Lang/Expressions.md#chained-comparisons).

**Complete.** Of a table: some row's condition holds wherever the table is
evaluated; of a `match` with guards, some arm is taken wherever it is
evaluated. See [Checks](Check.md#completeness).

**Constant.** A name for a fixed value, declared with `const`. See
[Items](Lang/Items.md#constants).

**Constraint.** An assumption, guarantee, expectation or cover goal.

**Contract.** The preconditions and postconditions of a function, written
after its signature with `assume` and `ensure`. See
[Items](Lang/Items.md#contracts).

**Counterexample.** Values of a procedure's variables that satisfy the
hypotheses of a check but not its goal. See [Checks](Check.md).

**Cover goal.** A scenario that a procedure must allow, declared with
`cover`: some behaviour that meets the procedure's assumptions and
guarantees must satisfy it. See [Procedures](Lang/Procedures.md#cover-goals).

**Definition.** Of a result, `out r := e`, or of a `let` variable, `let x:
T := e`: the expression `e`, which the variable stands for. See
[Procedures](Lang/Procedures.md#definitions).

**Determined.** Of an output: taking the same value in every behaviour
that meets the procedure, for each admissible input. A result or variable
declared with `det` must be determined. See [Checks](Check.md#determinism).

**Enumeration.** A type whose values are each one of a fixed set of named
variants, with the variant's payload, declared with `enum`. See
[Items](Lang/Items.md#enumerations).

**Disjoint.** Of the rows of a table: no two of them, other than `_`, hold
at once wherever the table is evaluated; of the arms of a table over a
scrutinee, no two of them are taken at once. See
[Checks](Check.md#disjointness).

**Domain.** Of a bound name of an unbounded quantifier: the values that
its guard bounds it to, which the evaluator enumerates: the members of a
set or sequence, or a range of integers. See
[Quantifiers](Lang/Quantifiers.md#guards).

**Divisor.** The right operand of `div` or `mod`: an integer literal or a
constant, possibly negated or in parentheses, whose value is not `0`. See
[Expressions](Lang/Expressions.md#division-and-remainder).

**Environment.** Whatever chooses a procedure's inputs.

**Exhaustive.** Of a `match`: every value of its scrutinee's type matches
the pattern of some arm, guards ignored. See [Expressions](Lang/Expressions.md#matches).

**Expectation.** A claim, declared with `expect`, that follows from a
procedure's assumptions and guarantees, and that the checks confirm.

**Function.** Declared with `fn`. A defined function, written with `:=
e`, has the value of its body `e`. Of an uninterpreted function, the spec
says only its type. The cardinality operators are built-in functions. See
[Items](Lang/Items.md#functions).

**Generic function.** A function with type parameters, as `fn id<T>(x:
T): T := x`, whose type arguments are inferred at each application: a
defined one is unfolded at that instance, and each instance of one without
a body is an unknown function of its own. See [Generic
functions](Lang/GenericFunctions.md).

**Generic type.** An enumeration or record with type parameters, as
`enum Option<T> { None, Some(T) }`, which is a type once given a type
argument for each parameter, as in `Option<Int>`. See [Generic
types](Lang/Generics.md).

**Global expectation.** A claim about one or more procedures as a whole,
declared with `expect` outside any procedure, that the checks confirm. See
[Global expectations](Lang/Global.md).

**Guarantee.** A constraint on what the system must do, declared with
`ensure`.

**Guard.** A condition, `if C`, after the pattern of a `match` arm: the
arm is taken only where it holds. See
[Expressions](Lang/Expressions.md#matches). Also, of an operand, the
conditions under which it is evaluated. See
[Expressions](Lang/Expressions.md#sequences). Also, of a quantifier, the
conditions of the `when`s at the top of a `forall`'s body, or the
conjuncts of an `exists`'s body, which may bound its bound names. See
[Quantifiers](Lang/Quantifiers.md#guards).

**Implementation.** A Lean proof that Lean code meets a procedure, declared
with `impl`. See [Implementations](Impl.md).

**Inconclusive.** The verdict of a check that the solver could not decide.

**Integer constant expression.** An expression whose value Fren computes
when it reads a spec: integer literals and constants whose values are
integer constant expressions, combined by `+`, `-`, `*`, `div`, `mod`,
`abs`, `min` and `max`. A constant divisor's value is one. See
[Expressions](Lang/Expressions.md#division-and-remainder).

**Interpretation.** A meaning for each abstract type and function. The
checks consider every interpretation, and in Lean, `interp` fixes one. See
[Procedures](Lang/Procedures.md#interpretations).

**Input.** A variable of a procedure chosen by its environment: one of its
parameters.

**Instance of a generic type.** A generic type with its type arguments,
such as `Option<Int>`. See [Generic types](Lang/Generics.md).

**Instance of a quantifier.** The body of a quantifier over listed types
with each bound name standing for one value; such a quantifier means the
conjunction or disjunction of its instances. See [Quantifiers](Lang/Quantifiers.md#meaning).

**Item.** A top-level declaration: a module, `use` declaration,
enumeration, record, abstract type, function, constant, procedure, global
expectation, check or claim. See [Items](Lang/Items.md).

**Let.** An expression, `let x := e in b`, that names the value of `e` as
`x` within `b`. See [Local definitions](Lang/Let.md).

**Lint.** A diagnostic about something allowed but probably not intended,
such as an unused import, whose level (`allow`, `warn`, `deny` or
`forbid`) can be set. See [Lints](Lint.md).

**Listed type.** A type whose values a quantifier can list: `Bool`, or an
enumeration or record whose payloads and fields have listed types. A
quantifier over listed types is expanded into its instances. See
[Quantifiers](Lang/Quantifiers.md#types).

**Match.** An expression that has the value of the body of the first of its
arms whose pattern matches its scrutinee and whose guard, if it has one,
holds. See
[Expressions](Lang/Expressions.md#matches).

**Member.** A declaration inside a procedure's body: an `exists` or `let`
variable, a result's definition, a constraint or a call.

**Newtype.** A record with exactly one field, which has no name, declared
as `struct Ms(Int)`: a type distinct from every other, with the values of
its underlying type. See [Items](Lang/Items.md#newtypes).

**Obligation.** That a value given where a pattern type is declared
matches its pattern, which a check asks the solver. See
[Types](Lang/Types.md#typing).

**Ordered declaration.** An enumeration, record or newtype declared with
`ordered`, as `ordered enum` or `ordered struct`, whose values are ordered:
an enumeration's variants as they are declared, and a record's values by
their fields, lexicographically. See [Items](Lang/Items.md#ordered-declarations).

**Ordered enumeration.** An enumeration without payloads, declared with
`ordered enum`, whose variants are ordered as they are declared, so that
`<`, `<=`, `>`, `>=`, `min` and `max` apply to its values. See
[Items](Lang/Items.md#enumerations).

**Ordered type.** A type whose values `<`, `<=`, `>`, `>=`, `min` and `max`
compare: `Int`, `Nat`, `String`, and the ordered declarations, with
pattern types and type aliases of these. See [Types](Lang/Types.md#ordered-types).

**Otherwise.** The last arm `_ => e`, without a guard, of a table over a
scrutinee, taken wherever no other arm is, as a table's `_` row is. See
[Expressions](Lang/Expressions.md#tables-over-a-scrutinee).

**Output.** A variable of a procedure chosen by the system: one of its
results, or a variable declared with `exists` or `let`.

**Overlap.** Of two patterns: some value matches both. See
[Patterns](Lang/Patterns.md#overlap).

**Parameter.** An input of a procedure, declared in its signature, as
`temp: Int` in `proc thermostat(temp: Int): (alarm?)`.

**Pattern.** What a `match` arm or a pattern test matches values against:
`_`, a binder, a literal, a range, a variant with patterns for its
payload, or an or-pattern. See [Patterns](Lang/Patterns.md).

**Pattern test.** An expression `e is P`, which is `true` exactly when the
pattern `P`, as of a `match` arm, matches `e`. Its binders name parts of
`e` in the later operands of its chain of `and`, and in the body of a
`when` or the `then` branch of an `if` whose condition it is. See
[Expressions](Lang/Expressions.md#pattern-tests).

**Pattern type.** A type `T is P`, whose values are those of its base
type `T` that match the pattern `P`, such as `Int is 0..=255`. See
[Types](Lang/Types.md#pattern-types).

**Payload.** The values that a variant carries, as in `Circle(Int)`. See
[Items](Lang/Items.md#enumerations).

**Postcondition.** A clause of a function's contract, declared with
`ensure`: what the function gives, wherever its arguments meet its
preconditions. See [Items](Lang/Items.md#contracts).

**Precondition.** A clause of a function's contract, declared with
`assume`: what each application's arguments must meet. See
[Items](Lang/Items.md#contracts).

**Prelude.** The items that every spec can use without declaring or
importing them, `Option<T>` and `Result<T, E>` and their variants, which
both front ends load before every spec. See [The prelude](Lang/Prelude.md).

**Procedure.** A part of a system, described by its parameters, results
and constraints, declared with `proc`. See [Procedures](Lang/Procedures.md).

**Quantifier.** An expression, `forall (x: T), e` or `exists (x: T), e`,
that says that `e` holds for every value, or for some value, of the type
`T`. See [Quantifiers](Lang/Quantifiers.md).

**Range pattern.** A pattern that matches the integers between its
bounds, such as `0..=9`, `0..10`, `1..` and `..=-1`. See
[Patterns](Lang/Patterns.md#kinds-of-pattern).

**Reachable.** Of an arm of a `match`, or an alternative of an
or-pattern: matching some value that no arm without a guard, or
alternative, before it matches. See [Expressions](Lang/Expressions.md#matches).
Of an arm with a guard, or after one, or of a row of a table: taken
somewhere it is evaluated. See [Checks](Check.md#reachability).

**Realizable.** Of a procedure: some system can meet its guarantees for
every admissible input. See [Checks](Check.md#realizability).

**Record.** A type whose values each have a value for each of its named
fields, declared with `struct`. See [Items](Lang/Items.md#records).

**Record update.** An expression `{ r with x := e }`: the value of `r`'s
record with `e` for `x` and `r`'s values for its other fields. See
[Expressions](Lang/Expressions.md#record-updates).

**Redundant.** Of an assumption or guarantee: following from the
procedure's other constraints. See [Checks](Check.md#redundancy).

**Requirement.** Anything a spec states about a system. What a procedure
says the system must do is its *guarantees*.

**Result.** An output of a procedure named in its signature, as `alarm?`
in `proc thermostat(temp: Int): (alarm?)`, which, unlike its `exists` and
`let` variables, a calling procedure can refer to. Its definition is
written `out r := e`.

**Shadowing.** A declaration hiding a name in scope, so that within the
declaration's scope the name means the declaration. It is written with
`!` after the declared name, as in `x!`. See
[Shadowing](Lang/Procedures.md#shadowing).

**Spec.** A sequence of items, in a Lean file, a `.fren` file or a
[Markdown spec](Markdown.md).

**System.** Whatever chooses a procedure's outputs.

**Table.** An expression `table { C => e, ... }` that has the value of its
first row whose condition holds: a `match` with guards and nothing to match
on. Over a scrutinee, `table s { P if C => e, ... }`, a `match` whose arms
are disjoint, so that its value does not depend on their order. See
[Expressions](Lang/Expressions.md#tables).

**Type argument.** A type that stands for a type parameter in an
instance of a generic type, as `Int` in `Option<Int>`. Expressions never
write them: they are inferred. See [Generic
types](Lang/Generics.md#type-arguments).

**Type parameter.** A name that stands for a type within the declaration
of a generic type, as `T` in `enum Option<T> { None, Some(T) }`. See
[Generic types](Lang/Generics.md#type-parameters).

**Trigger.** The condition under which a `when` or `unless` constraint
applies. See [Procedures](Lang/Procedures.md#triggers).

**Vacuous.** Of a constraint: holding only because its trigger can never
hold. See [Checks](Check.md#vacuity).

**Type alias.** A name for a type, declared with `type Name := T`, which
is not a new type. See [Items](Lang/Items.md#type-aliases).

**Underlying type.** The type of a newtype's field, whose values the
newtype has. See [Items](Lang/Items.md#newtypes).

**Unbounded quantifier.** A quantifier with a bound name of a type that is
not listed, such as `Int`: Lean's `∀` or `∃`, and a quantifier for the
solver, outside the decidable core. See
[Quantifiers](Lang/Quantifiers.md#unbounded-quantifiers).

**Unbounded type.** A type with arbitrarily large values: a recursive
enumeration, or one with a field or payload of an unbounded type. See
[Types](Lang/Types.md#recursive-and-unbounded-types).

**Useful.** Of a vector of patterns, with respect to a matrix of them:
some values match the vector and no row of the matrix. See
[Patterns](Lang/Patterns.md#usefulness).

**Variant.** One of the alternatives of an enumeration, carrying a payload
or not.

**Where clause.** Definitions, `where x := e`, after the whole expression
of a constraint or cover goal, a definition, a function's body or a constant's value,
that name expressions within it. See [Local definitions](Lang/Let.md).

**Widening.** Accepting a `Nat` where an `Int` is expected, or a pattern
type where its base type is, the only conversion between types. See [Types](Lang/Types.md#natural-numbers).

**Witness.** Values of a procedure's variables that satisfy the
hypotheses of a check that asks whether something can hold, and its goal,
such as a behaviour in which a cover goal holds. See [Checks](Check.md).
