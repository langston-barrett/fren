# Components

A component describes part of a system by the relation it must maintain
between its inputs and its outputs.

```
component  := ["pub"] "comp" IDENT "{" member* "}"
member     := "in" variable
            | ["pub"] ["det"] "out" variable [":=" top]
            | "assume" IDENT ":" top
            | "ensure" IDENT ":" top
            | "expect" IDENT ":" top
            | "cover" IDENT ":" top
            | instance
            | use
variable   := DECL [":" type]
```

A `DECL` is an identifier that declares a name, and ends in `!` if it
[shadows](#shadowing) another. A `top` is an expression, optionally
followed by a `where` clause (see [Local definitions](Let.md)).

## Members

- **Inputs** (`in x: T`) are chosen by the component's environment. Inputs
  are always part of the component's interface, and cannot be marked `pub`.
- **Outputs** (`out x: T`) are chosen by the system. An output may not
  have an [unbounded type](Types.md#recursive-and-unbounded-types). An output is private
  unless it is marked `pub`. A private output is an auxiliary variable: it
  can be constrained like any other, but it is not shown in counterexamples
  and cannot be mentioned through an [instance](Instances.md). An output
  marked `det` must be determined by the inputs: the [determinism
  check](../Check.md#determinism) confirms that all behaviours that meet the
  component agree on it for each admissible input.
- **Defined outputs** (`out x: T := e`) stand for their definition `e`:
  they name an expression rather than a value the system chooses. See
  [Defined outputs](#defined-outputs).
- **Assumptions** (`assume n: e`) constrain the environment. An assumption
  must mention only inputs.
- **Guarantees** (`ensure n: e`) constrain the system: every behaviour of the
  system must satisfy them.
- **Expectations** (`expect n: e`) are claims that follow from the
  assumptions and guarantees. They constrain nothing; the checks confirm
  them. An expectation about several behaviours, or several components, is
  a [global expectation](Global.md) instead.
- **Cover goals** (`cover n: e`) are scenarios that the component must
  allow: some behaviour that meets the assumptions and guarantees must
  satisfy `e`. Like expectations, they constrain nothing; the [cover
  check](../Check.md#cover-goals) confirms them. See [Cover
  goals](#cover-goals).
- **Instances** (`inst w: c { ... }`) make another component part of this
  one. See [Instances](Instances.md).
- **Imports** (`use a::E::*`) bring names into scope for the component's
  other members only. See [`use` in a
  component](Modules.md#use-in-a-component).

Only outputs take modifiers or definitions: an input is always public and
chosen by the environment, and `det` says nothing of a constraint or an
instance. `lang::modifiers` states this:

```fren
pub mod lang

pub enum Member { Input, Output, Constraint, Instance }

pub comp modifiers {
    in member: Member
    in pub?              -- written with `pub`
    in det?              -- written with `det`
    in defined?          -- written with `:= e`
    pub out accepted?

    ensure rule: accepted? iff (member = Member::Output or not (pub? or det? or defined?))

    expect plain_members: unless pub? or det? or defined?, accepted?
    expect outputs_take_all: when member = Member::Output, accepted?
    expect pub_only_outputs: when member != Member::Output and pub?, not accepted?
    expect det_only_outputs: when member != Member::Output and det?, not accepted?
    expect defined_only_outputs: when member != Member::Output and defined?, not accepted?

    cover every_modifier: member = Member::Output and pub? and det? and defined? and accepted?
}
```

An input may have any type, but an output's type is bounded unless the
output is defined, so that the solver never has to find an unbounded
value (see [Recursive and unbounded
types](Types.md#recursive-and-unbounded-types)). A defined output is never
searched for. `lang::variable_type` states this, with the variable's type
unbounded by the closure of the constituent relation (`lang::type_facts`);
`only_outputs` is an assumption because `lang::modifiers` rejects a
defined input first:

```fren
set_option fren.lint.undecidable "allow" in
pub comp variable_type {
    in output?                                       -- the variable is an output, public or private
    in ty: DeclaredTy                                -- its type
    in constituents: Rel<DeclaredTy, DeclaredTy>     -- (t, u): t has a field, payload or element of type u
    in defined?                                      -- it is declared with `:= e`

    assume only_outputs: when defined?, output?
    pub det out accepted?
    inst facts: type_facts { ty, constituents }

    ensure rule: accepted? iff not (output? and facts.unbounded? and not defined?)

    expect inputs_any_type: unless output?, accepted?
    expect defined_any_type: when defined?, accepted?
    expect strings_defined: when output? and declared_kind(ty) = ValueType::StringTy, accepted? iff defined?
    expect bool_outputs: when declared_kind(ty) = ValueType::BoolTy and constituents = {}, accepted?

    cover unbounded_defined: output? and facts.unbounded? and defined? and accepted?
}
```

Assumptions, guarantees, expectations and cover goals are together
called *constraints*. Each constraint is an [expression](Expressions.md) of type
`Bool`.

The variables, constraints (cover goals among them) and instances of a
component share one namespace, so their names must be distinct. A component's variables and
instances may [shadow](#shadowing) the constants, functions and variants of
its module, explicitly. Members may appear in any order; a variable may be
mentioned before its declaration. A component may have no members at all.

## Shadowing

A declaration *shadows* a name in scope when, within the declaration's
scope, a path of that one name means the declaration rather than what it
otherwise would. Shadowing is allowed, but explicit: a declaration that
shadows is written with `!` directly after its name, as in `x!`, or
`ready?!` for a `Bool`, whose `!` follows its `?`. The `!` is not part of
the name, and its uses are written without it.

```text
comp c {
    in x: Int
    in s: Shape
    pub out p?
    -- `x!` declares a binder that shadows the input `x`; in the arm, `x` is the payload.
    ensure r: p? iff match s {
        Shape::Circle(x!) => x > 0,
        _ => x > 0,   -- the input
    }
}
```

These declarations may shadow:

- a component's [variable](#members) or [instance](Instances.md), the
  constants, functions and variants in the component's scope (see
  [Modules and visibility](Modules.md#use-in-a-component));
- a [defined function's](Items.md#defined-functions) parameter, those of
  the function's module;
- a [global expectation's](Global.md) binder, those of its module;
- a [`match` arm's](Expressions.md#matches) binder or a
  [quantifier's](Quantifiers.md#names) bound name, those and also the
  variables (or, in a function's body, the parameters), instances, global
  expectation binders, binders of enclosing arms, bound names of
  enclosing quantifiers and names of enclosing `let`s and `where` clauses
  in scope;
- a [`let` or `where`](Let.md) definition's name, those and also the
  names of enclosing `let`s and `where` clauses and the earlier names of
  its own clause.

The built-in functions, the [cardinality
operators](Expressions.md#cardinality), are in every scope, so each of
these may shadow them.

Other items, such as components, enumerations and modules, are never named
where a variable can be, so nothing shadows them. Nor do items,
constraints, fields and variants shadow, so their names never take `!`.
The precedence of a component's imports over its module's scope (see
[Modules and visibility](Modules.md#use-in-a-component)) is a rule of
resolution, not a declaration, and takes no `!`.

An import that brings in a name that a `!` declaration hides counts as
used (see [Unused imports](../Lint/Unused.md#unused-imports)). A name that two
glob imports make ambiguous is not hidden, since a use of it would be an
error: a variable named like it takes no `!`.

A function is not in scope in its own body (see [Defined
functions](Items.md#defined-functions)), so a parameter named like its
function, as in `fn f(f: Int): Int := f + 1`, hides nothing, and is
written without `!`: `fn f(f!: Int)` is an error, since nothing is
shadowed.

Some names followed by `!` are tokens of Lean's, with `Fren` imported:
`assert!`, `debug_assert!`, `f!`, `m!`, `panic!`, `println!`,
`reportDbgIssue!`, `reportEMatchIssue!`, `reportIssue!`, `s!`,
`unreachable!` and `using!`. Lean reads each as one token, not as a name
and `!`, so neither front end accepts a declaration written so, such as
`in s!: Int`: it is an error that says to rename the declaration. The
Lean front end reads these tokens as identifiers where Fren expects one,
so that it reports the same error as the `fren` command, and, at a use,
the same unknown name.

`lang::shadowing` states when a declaration is accepted, from whether its
name hides a name in scope and whether it is written with `!`. Shadowing
without `!` is an error, and so is `!` where nothing is shadowed. This
replaces the lint `shadowed_constants`, which warned of a variable named
like a constant, and whose code `F0713` is not reused.

```fren
pub mod lang

set_option fren.evidence "enumerated" in
pub comp shadowing {
    in hides?            -- the declared name hides a name in scope
    in bang?             -- the declaration is written with `!`
    in own_function?     -- it is a parameter named like its own function

    assume not_in_own_body: when own_function?, not hides?
    pub det out accepted?

    ensure rule: accepted? iff (hides? iff bang?)

    expect explicit: when hides? and bang?, accepted?
    expect implicit: when hides? and not bang?, not accepted?
    expect needless: when bang? and not hides?, not accepted?
    expect own_function: when own_function?, accepted? iff not bang?

    cover explicit_accepted: hides? and bang? and accepted?
}
```

## Meaning

A component is a relation between its inputs `i` and its outputs `o`. Let
`A(i)` be the conjunction of its assumptions and `R(i, o)` the conjunction
of its guarantees. The system meets the component if, whenever `A(i)`
holds, its outputs satisfy `R(i, o)`. [Defined outputs](#defined-outputs)
are first replaced by their definitions.

A component with instances is an assume-guarantee composition. Each
instance `w` contributes a constraint `I_w`: its bindings, and the
assumptions, guarantees and (recursively) instances of the component it
instantiates, over the instance's variables `y`. The instance is part of
the system, but its variables are not the component's to choose: whatever
the instantiated component does within its guarantees, the component must
cope. So instance variables are treated like inputs, constrained by `I(i, y)
= ⋀ I_w`, and the guarantees become `R(i, y, o)`. The instantiated
component's assumptions become obligations on the bindings, which the
[instance check](../Check.md#instance-assumptions) confirms.

## Cover goals

Every other constraint says what must hold in *every* behaviour. A cover
goal says what must hold in *some*: `cover n: e` claims that some
behaviour that meets the component satisfies `e`. It catches a component
that is over-constrained in a way that the [vacuity
check](../Check.md#vacuity) does not see: one that allows some
behaviours, and whose triggers can each hold, but that rules out a
particular scenario that should be possible. Like a constraint, a goal
may end with a [`where` clause](Let.md).

```text
comp heater {
    in temp: Int
    pub out alarm?

    ensure r: alarm? iff temp > 100

    cover overheat: temp > 100 and alarm?
}
```

A cover goal may mention what an expectation may (see [Instance
variables](Instances.md#instance-variables)). It constrains nothing: it
is not part of the component's [meaning](#meaning), of an instance's
constraint `I_w`, or of an implementation's obligation. It is checked
only in its own component, not where the component is instantiated: a
goal is about the component alone. A cover goal with a
[trigger](#triggers) holds wherever the trigger is false, so it is met by
any behaviour in which the trigger is false; write the scenario as a
conjunction, such as `temp > 100 and alarm?`, instead.

## Defined outputs

An output declared with a definition, `out x: T := e`, stands for `e`.
`e` is an expression of type `T`, over the component's variables, and it
ends where the next member starts. Its type is written, or, as for any
variable, omitted for a name ending in `?`, which is a `Bool`. `pub` and
`det` work as for any output, and `det` is still checked rather than
implied.

```
mod accounts

pub comp handle {
    in length: Int
    in taken?
    out long? := length > 40     -- a name for a condition
    pub det out accepted?

    ensure rule: accepted? iff not (long? or taken?)
}
```

Let `D` be the definitions `d_k := e_k` of a component. The component means
what it would with each `d_k` replaced by `e_k` in its constraints and
bindings, repeatedly, until no defined output remains. Equivalently, `D`
adds the equations `d_k = e_k`. The [checks](../Check.md#definitions) use
whichever form keeps their queries decidable.

- **Acyclic.** A definition may not mention its own output, directly or
  through other definitions, so the substitution ends.
- **Mentions.** A defined output mentions what its definition mentions,
  transitively, as a [`match` binder](Expressions.md#matches) mentions
  what its scrutinee does. Every rule about where a variable may occur
  applies through it: one whose definition mentions only inputs may occur
  in an assumption or a binding, and one whose definition mentions an
  output may not occur in a function's argument.
- **Not bound.** An instance cannot bind a defined output, since it is an
  output.

A private defined output names a subexpression for the whole component,
as a [`where` clause](Let.md) does for one constraint. Define an
output when the spec computes it, and require it when the spec constrains
it: a definition is not a constraint, so the vacuity, redundancy and
realizability checks no longer see it.

## Natural numbers

A variable of type [`Nat`](Types.md#natural-numbers) brings the
constraint that it is at least 0, as though it were written in the spec:

- an input, an assumption;
- an output, public or private, a guarantee;
- an instance's variable, a constraint of the instance, as its
  component's own variable does, even one that is a defined output there,
  where its definition already makes it at least 0;
- a defined output, none: its definition is a `Nat`, so it is at least 0
  already.

These constraints have no names. They are never reported in a [minimal
set](../Check.md#minimal-sets), never checked for redundancy, and need no
check of their own: a binding or a definition of type `Nat` is at least 0
by its type. `lang::nat_variable` states what a `Nat` variable brings:

```fren
pub enum Brought { Nothing, Assumption, Guarantee }

pub comp nat_variable {
    in own_output?       -- an output of the component itself, rather than an input or an instance's variable
    in defined?          -- a defined output

    assume only_outputs: when defined?, own_output?
    pub det out brought: Brought

    ensure rule: brought = (if defined? then Brought::Nothing
        else if own_output? then Brought::Guarantee
        else Brought::Assumption)

    expect inputs_assumed: unless own_output?, brought = Brought::Assumption
    expect definitions_typed: when defined?, brought = Brought::Nothing
}
```

## Pattern types

A variable whose type is a [pattern type](Types.md#pattern-types), or a
record or an enumeration with a pattern type or a `Nat` within its fields
and payloads, brings the constraint that its value matches, just as a
`Nat` variable brings that it is at least 0, and in the same way, which
`lang::nat_variable` states: an assumption for an input, a guarantee for
an output, a constraint of the instance for an instance's variable, and
nothing for a defined output, whose definition is checked to match instead
(see [Checks](../Check.md#pattern-types)). An instance's input is the one
exception: what its type brings is the instantiated component's
assumption, which the instance check asks of its binding, so it is not
also a constraint of the instance. With `in hops: Int is 1..`, the
component assumes `hops is 1..`; with `pub out level: Loud`, it guarantees
that `level` is one of `Loud`'s variants. Like a `Nat`'s, these constraints
have no names, are never reported in a minimal set, and are never checked
for redundancy. An instance's binding of an input of a pattern type is
checked like any other assumption of the instantiated component, by the
[instance check](../Check.md#instance-assumptions). A [global
expectation's](Global.md) binders have no bindings, so their inputs bring
their constraints, as their assumptions do.

## Interpretations

The [abstract types](Types.md#abstract-types) and
[uninterpreted functions](Items.md#uninterpreted-functions) of a spec are
fixed, but unknown. An *interpretation* gives each abstract type a
nonempty set of values, and each uninterpreted function a total function
between the sets of its parameter and result types. A [generic
one](GenericFunctions.md#uninterpreted-generic-functions) is given a
function of its own for each instance, between the sets of its parameter
and result types at that instance: `pick<Int>` and `pick<Bool>` need not
be related. A [defined
function](Items.md#defined-functions) needs no interpretation: its body
gives its values, from those of its arguments. A component's meaning above is relative to an
interpretation: `A`, `I` and `R` may apply functions, and the variables
of abstract types range over the values the interpretation gives them.

An interpretation is chosen neither by the environment nor by the system:
it is the same for every input, every behaviour, and every component. The
[checks](../Check.md#interpretations) confirm their claims under every
interpretation, so a spec can rely only on what it states about a
function, such as an assumption `when f(x) = f(y), x = y` over the inputs
`x` and `y`. A system runs under one interpretation, and meets the
component if it does so under that one. In Lean, an
[interpretation](../Impl.md#interpretations) states which.

## Triggers

A constraint of the form `when C, D` applies only when `C` holds. `C` is its
*trigger*. Likewise, the trigger of `unless C, D` is `not C`. Triggers of
nested constraints are conjoined: the trigger of `when C1, unless C2, D` is
`C1 and not C2`. A constraint with no top-level `when` or `unless` has no
trigger, and neither does one whose top level is a
[quantifier](Quantifiers.md#names), even around a `when`. A `let` or
`where` at the top of a constraint is read through: the trigger of `when
C, D where x := e` is `C`, with `x` standing for `e` (see [Local
definitions](Let.md#meaning)). A name that a [pattern
test](Expressions.md#binding-names) of `C1` binds stands for the value it
matches in a nested trigger: the trigger of `when x is P(d), when d > 0,
D` is that `x` matches `P(_)` and its payload's value is positive. The [vacuity check](../Check.md#vacuity)
confirms that the trigger of every guarantee and expectation can hold.
A cover goal's trigger is not checked: the [cover
check](../Check.md#cover-goals) confirms the goal itself.
