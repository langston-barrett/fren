# Components

A component describes part of a system by the relation it must maintain
between its inputs and its outputs.

```
component  := ["pub"] "comp" IDENT "{" member* "}"
member     := "in" variable
            | ["pub"] ["det"] "out" variable [":=" expr]
            | "assume" IDENT ":" expr
            | "req" IDENT ":" expr
            | "expect" IDENT ":" expr
            | instance
            | use
variable   := DECL [":" type]
```

A `DECL` is an identifier that declares a name, and ends in `!` if it
[shadows](#shadowing) another.

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
- **Requirements** (`req n: e`) constrain the system: every behaviour of the
  system must satisfy them.
- **Expectations** (`expect n: e`) are claims that follow from the
  assumptions and requirements. They constrain nothing; the checks confirm
  them. An expectation about several behaviours, or several components, is
  a [global expectation](Global.md) instead.
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

    req rule: accepted? iff (member = Member::Output or not (pub? or det? or defined?))

    expect plain_members: unless pub? or det? or defined?, accepted?
    expect outputs_take_all: when member = Member::Output, accepted?
    expect pub_only_outputs: when member != Member::Output and pub?, not accepted?
    expect det_only_outputs: when member != Member::Output and det?, not accepted?
    expect defined_only_outputs: when member != Member::Output and defined?, not accepted?
}
```

An input may have any type, but an output's type is bounded unless the
output is defined, so that the solver never has to find an unbounded
value (see [Recursive and unbounded
types](Types.md#recursive-and-unbounded-types)). A defined output is never
searched for. `lang::variable_type` states this; `only_outputs` is an
assumption because `lang::modifiers` rejects a defined input first:

```fren
pub comp variable_type {
    in output?           -- the variable is an output, public or private
    in unbounded?        -- its type is unbounded
    in defined?          -- it is declared with `:= e`
    pub det out accepted?

    assume only_outputs: when defined?, output?

    req rule: accepted? iff not (output? and unbounded? and not defined?)

    expect inputs_any_type: unless output?, accepted?
    expect defined_any_type: when defined?, accepted?
}
```

Assumptions, requirements and expectations are together called
*constraints*. Each constraint is an [expression](Expressions.md) of type
`Bool`.

The variables, constraints and instances of a component share one
namespace, so their names must be distinct. A component's variables and
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
    req r: p? iff match s {
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
- a [`match` arm's](Expressions.md#matches) binder, those and also the
  variables (or, in a function's body, the parameters), instances, global
  expectation binders and binders of enclosing arms in scope.

Other items, such as components, enumerations and modules, are never named
where a variable can be, so nothing shadows them. Nor do items,
constraints, fields and variants shadow, so their names never take `!`.
The precedence of a component's imports over its module's scope (see
[Modules and visibility](Modules.md#use-in-a-component)) is a rule of
resolution, not a declaration, and takes no `!`.

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

pub comp shadowing {
    in hides?            -- the declared name hides a name in scope
    in bang?             -- the declaration is written with `!`
    in own_function?     -- it is a parameter named like its own function
    pub det out accepted?

    assume not_in_own_body: when own_function?, not hides?

    req rule: accepted? iff (hides? iff bang?)

    expect explicit: when hides? and bang?, accepted?
    expect implicit: when hides? and not bang?, not accepted?
    expect needless: when bang? and not hides?, not accepted?
    expect own_function: when own_function?, accepted? iff not bang?
}
```

## Meaning

A component is a relation between its inputs `i` and its outputs `o`. Let
`A(i)` be the conjunction of its assumptions and `R(i, o)` the conjunction
of its requirements. The system meets the component if, whenever `A(i)`
holds, its outputs satisfy `R(i, o)`. [Defined outputs](#defined-outputs)
are first replaced by their definitions.

A component with instances is an assume-guarantee composition. Each
instance `w` contributes a constraint `I_w`: its bindings, and the
assumptions, requirements and (recursively) instances of the component it
instantiates, over the instance's variables `y`. The instance is part of
the system, but its variables are not the component's to choose: whatever
the instantiated component does within its requirements, the component must
cope. So instance variables are treated like inputs, constrained by `I(i, y)
= ⋀ I_w`, and the requirements become `R(i, y, o)`. The instantiated
component's assumptions become obligations on the bindings, which the
[instance check](../Check.md#instance-assumptions) confirms.

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

    req rule: accepted? iff not (long? or taken?)
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

A private defined output names a subexpression, like a `let`. Define an
output when the spec computes it, and require it when the spec constrains
it: a definition is not a constraint, so the vacuity, redundancy and
realizability checks no longer see it.

## Interpretations

The [abstract types](Types.md#abstract-types) and
[uninterpreted functions](Items.md#uninterpreted-functions) of a spec are
fixed, but unknown. An *interpretation* gives each abstract type a
nonempty set of values, and each uninterpreted function a total function
between the sets of its parameter and result types. A [defined
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
trigger. The [vacuity check](../Check.md#vacuity) confirms that the trigger
of every requirement and expectation can hold.
