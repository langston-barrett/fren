# Procedures

A procedure describes part of a system by the relation it must maintain
between its inputs and its outputs. It is written like a function: its
inputs are its parameters, and its outputs that callers see are its named
results, in its signature; its other members, in its block, constrain
them.

```
procedure  := ["pub"] "proc" IDENT "(" [param ("," param)* [","]] ")"
              [":" "(" result ("," result)* [","] ")"] "{" member* "}"
param      := variable
result     := [evidence-setting "in"] ["det"] variable
member     := ["det"] "exists" variable
            | ["det"] "let" variable ":=" top
            | "out" IDENT ":=" top
            | "assume" IDENT ":" top
            | "ensure" IDENT ":" top
            | "expect" IDENT ":" top
            | "cover" IDENT ":" top
            | call
            | use
variable   := DECL [":" type]
```

A `DECL` is an identifier that declares a name, and ends in `!` if it
[shadows](#shadowing) another. A `top` is an expression, optionally
followed by a `where` clause (see [Local definitions](Let.md)). An
evidence setting is `set_option fren.evidence "..."` (see [Checking by
testing](../Check.md#checking-by-testing)). A procedure with no results
has no `:` and no result list; one with no parameters is written `proc
p() { ... }`. A list of parameters or results may be written one to a
line, with a comment after each, and a comma after the last (see
[Trailing commas](../Fmt.md#trailing-commas)):

```text
pub proc thermostat(
    temp: Int,               -- the temperature
    target: Int is 50..=90,  -- the target, which the environment keeps sane
): (det mode: Mode) {
    ensure heat: when temp < target - 2, mode = Mode::Heat
}
```

`proc` is a reserved word. `call` and `out` are contextual keywords, which
start a member and are names anywhere else, and so is `det` before a
result or a member. `exists` and `let` are reserved, and what they start
depends on where they are: at the start of a member, an `exists` or a
`let` member; within an expression, a [quantifier](Quantifiers.md) or a
[local definition](Let.md) (see [Grammar](../Grammar.md)).

## Members

- **Parameters** (`x: T` in the signature) are the procedure's inputs,
  chosen by its environment. They take no modifier (`F0110`) and no
  definition (`F0114`).
- **Results** (`r: T` in the result list) are outputs, chosen by the
  system, that the procedure's callers see: a call `w` reads them as
  `w.r` (see [Call variables](Calls.md#call-variables)). A result marked
  `det` must be determined by the inputs: the [determinism
  check](../Check.md#determinism) confirms that all behaviours that meet
  the procedure agree on it for each admissible input.
- **`exists x: T`** declares a private output: an auxiliary variable that
  the system chooses. It can be constrained like any other, but it is not
  shown in counterexamples and cannot be mentioned through a call. It may
  be marked `det`, as a result may.
- **`let x: T := e`** declares a private variable that stands for its
  definition `e` (see [Definitions](#definitions)); `det` too.
- **`out r := e`** defines the result `r`, which then stands for `e`, as
  a `let` stands for its definition. It declares nothing, and has no type
  annotation: `r` is declared in the signature. `out` of any other name,
  such as a parameter, is an error (`F0444`): a value of the block's own
  is a `let`. A result is defined by one `out` member at most (`F0421`);
  without one, the system chooses it.
- **Assumptions** (`assume n: e`) constrain the environment. An assumption
  must mention only parameters.
- **Guarantees** (`ensure n: e`) constrain the system: every behaviour of the
  system must satisfy them.
- **Expectations** (`expect n: e`) are claims that follow from the
  assumptions and guarantees. They constrain nothing; the checks confirm
  them. An expectation about several behaviours, or several procedures, is
  a [global expectation](Global.md) instead.
- **Cover goals** (`cover n: e`) are scenarios that the procedure must
  allow: some behaviour that meets the assumptions and guarantees must
  satisfy `e`. Like expectations, they constrain nothing; the [cover
  check](../Check.md#cover-goals) confirms them. See [Cover
  goals](#cover-goals).
- **Calls** (`call w := p(...)`) make another procedure part of this
  one. See [Calls](Calls.md).
- **Imports** (`use a::E::*`) bring names into scope for the procedure's
  other members only. See [`use` in a
  procedure](Modules.md#use-in-a-procedure).

The *outputs* of a procedure are its results and its `exists` and `let`
variables. Its *variables*, in order, are its parameters, then its
results, then its `exists` and `let` variables in the order they are
written; the [generated definitions](../Generated.md) take them in that
order.

`pub` marks an item public, and is no modifier of a member, a parameter
or a result: a procedure's results are what callers see. `det` applies
only to a result, an `exists` or a `let`: a parameter is chosen by the
environment, and `det` says nothing of a constraint or a call
(`F0110`, `F0113`). A definition, `:= e`, is written on a `let` and on an
`out` member, which defines a result, and on nothing else: a parameter
cannot have one (`F0114`), a result is defined by an `out` member rather
than in the signature, and an `exists` is chosen by the system.
`lang::modifiers` states this:

```fren
pub mod lang

pub enum Member { Param, Result, Exists, Let, Define, Constraint, Call }

pub proc modifiers(
    member: Member,
    pub?,                -- written with `pub`
    det?,                -- written with `det`
    defined?,            -- written with `:= e`
): (accepted?) {
    ensure rule: accepted? iff (not pub? and (not det? or member is Member::Result | Member::Exists | Member::Let)
        and (defined? iff member is Member::Let | Member::Define))

    expect plain_members: when member is Member::Param | Member::Constraint | Member::Call,
        accepted? iff not (pub? or det? or defined?)
    expect no_pub: when pub?, not accepted?
    expect det_variables: when member is Member::Result | Member::Exists | Member::Let, accepted? iff not pub?
        and (defined? iff member = Member::Let)
    expect det_nothing_else: when det? and member is Member::Param | Member::Define | Member::Constraint | Member::Call,
        not accepted?
    expect definitions: when member is Member::Param | Member::Result | Member::Exists and defined?, not accepted?

    cover det_result: member = Member::Result and det? and accepted?
    cover det_let: member = Member::Let and det? and defined? and accepted?
}
```

A parameter may have any type, but an output's type is bounded unless the
output is defined, so that the solver never has to find an unbounded
value (see [Recursive and unbounded
types](Types.md#recursive-and-unbounded-types)). A defined output is never
searched for. `lang::variable_type` states this, with the variable's type
unbounded by the closure of the constituent relation (`lang::type_facts`);
`only_outputs` is an assumption because a parameter cannot be defined:

```fren
set_option fren.lint.undecidable "allow" in
pub proc variable_type(
    output?,                                         -- the variable is an output: a result, an `exists` or a `let`
    ty: DeclaredTy,                                  -- its type
    constituents: Rel<DeclaredTy, DeclaredTy>,       -- (t, u): t has a field, payload or element of type u
    defined?,                                        -- it is a `let`, or a result that an `out` member defines
): (det accepted?) {
    assume only_outputs: when defined?, output?

    call facts := type_facts(ty, constituents)

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

The parameters, results, variables, constraints (cover goals among them)
and calls of a procedure share one namespace, so their names must be
distinct. A procedure's parameters, results, variables and calls may
[shadow](#shadowing) the constants, functions and variants of its module,
explicitly. Members may appear in any order, though the lint
[`arbitrary_source_item_ordering`](../Lint/Restriction.md) asks for one;
a variable may be mentioned before its declaration. A procedure may have
no parameters, no results and no members at all.

## Shadowing

A declaration *shadows* a name in scope when, within the declaration's
scope, a path of that one name means the declaration rather than what it
otherwise would. Shadowing is allowed, but explicit: a declaration that
shadows is written with `!` directly after its name, as in `x!`, or
`ready?!` for a `Bool`, whose `!` follows its `?`. The `!` is not part of
the name, and its uses are written without it.

```text
proc c(x: Int, s: Shape): (p?) {
    -- `x!` declares a binder that shadows the input `x`; in the arm, `x` is the payload.
    ensure r: p? iff match s {
        Shape::Circle(x!) => x > 0,
        _ => x > 0,   -- the input
    }
}
```

These declarations may shadow:

- a procedure's [parameter, result or variable](#members) or
  [call](Calls.md), the constants, functions and variants in the
  procedure's scope (see [Modules and
  visibility](Modules.md#use-in-a-procedure));
- a [defined function's](Items.md#defined-functions) parameter, those of
  the function's module;
- a [global expectation's](Global.md) parameter, `let` variable or call,
  those of its module, as a procedure's do;
- a [`match` arm's](Expressions.md#matches) binder or a
  [quantifier's](Quantifiers.md#names) bound name, those and also the
  variables (or, in a function's body, the parameters), calls, binders
  of enclosing arms, bound names of
  enclosing quantifiers and names of enclosing `let`s and `where` clauses
  in scope;
- a [`let` or `where`](Let.md) definition's name, those and also the
  names of enclosing `let`s and `where` clauses and the earlier names of
  its own clause.

The built-in functions, the [cardinality
operators](Expressions.md#cardinality), are in every scope, so each of
these may shadow them.

Other items, such as procedures, enumerations and modules, are never named
where a variable can be, so nothing shadows them. Nor do items,
constraints, fields and variants shadow, so their names never take `!`.
The precedence of a procedure's imports over its module's scope (see
[Modules and visibility](Modules.md#use-in-a-procedure)) is a rule of
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
`proc p(s!: Int)`: it is an error that says to rename the declaration. The
Lean front end reads these tokens as identifiers where Fren expects one,
so that it reports the same error as the `fren` command, and, at a use,
the same unknown name.

`lang::shadowing` states when a declaration is accepted, from the
[scope](Scope.md#scopes) where it is declared and whether it is written
with `!`. Its scope is the one where it is declared, without itself: a
later declaration, of the same construct or one within it, is not in it,
and nor is a later item. It *hides* a name in scope when, in that scope, its name
resolves to a value: anything but a module, an enumeration or another
item that is not a value, and not an ambiguous name. Shadowing without
`!` is an error, and so is `!` where nothing is shadowed. This replaces
the lint `shadowed_constants`, which warned of a variable named like a
constant, and whose code `F0713` is not reused.

```fren
pub mod lang

-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub proc shadowing(
    bindings: Set<Binding>,      -- its scope, where it is declared, without it (`context_scope`)
    name: Id,                    -- the name it declares
    bang?,                       -- it is written with `!`
): (det hides?, det accepted?) {
    use self::BindingKind::{Enumeration, Input, Item, Module, Output}

    out hides? := hidden.value?

    call hidden := scope(bindings, name)

    ensure rule: accepted? iff (hides? iff bang?)

    expect explicit: when hides? and bang?, accepted?
    expect implicit: when hides? and not bang?, not accepted?
    expect needless: when bang? and not hides?, not accepted?
    -- An item that is not a value, and a name that glob imports make ambiguous, are not hidden.
    expect items_not_hidden: when hidden.result is Lookup::Found(Module | Enumeration | Item) | Lookup::Ambiguous,
        accepted? iff not bang?
    expect unbound: when bindings = {}, accepted? iff not bang?
    -- A declaration named like the procedure's variable, in its innermost scope, hides it.
    expect variable_hidden: forall (b: Binding), when b in bindings and b.name = name and b.depth = 0
        and b.kind in {Input, Output}
        and (forall (c: Binding), when c in bindings and c.name = name and c.depth = 0, c = b),
        accepted? iff bang?

    cover explicit_accepted: hides? and bang? and accepted?
}
```

## Meaning

A procedure is a relation between its inputs `i` and its outputs `o`. Let
`A(i)` be the conjunction of its assumptions and `R(i, o)` the conjunction
of its guarantees. The system meets the procedure if, whenever `A(i)`
holds, its outputs satisfy `R(i, o)`. [Definitions](#definitions) are
first replaced by what they define.

A procedure with calls is an assume-guarantee composition. Each call `w`
contributes a constraint `I_w`: its arguments, bound to the called
procedure's parameters, and the assumptions, guarantees and
(recursively) calls of the procedure it calls, over the call's variables
`y`. The call is part of the system, but its variables are not the
procedure's to choose: whatever the called procedure does within its
guarantees, the procedure must cope. So a call's variables are treated
like inputs, constrained by `I(i, y) = ⋀ I_w`, and the guarantees become
`R(i, y, o)`. The called procedure's assumptions become obligations on
the arguments, which the [call assumption
check](../Check.md#call-assumptions) confirms.

## Cover goals

Every other constraint says what must hold in *every* behaviour. A cover
goal says what must hold in *some*: `cover n: e` claims that some
behaviour that meets the procedure satisfies `e`. It catches a procedure
that is over-constrained in a way that the [vacuity
check](../Check.md#vacuity) does not see: one that allows some
behaviours, and whose triggers can each hold, but that rules out a
particular scenario that should be possible. Like a constraint, a goal
may end with a [`where` clause](Let.md).

```text
proc heater(temp: Int): (alarm?) {
    ensure r: alarm? iff temp > 100

    cover overheat: temp > 100 and alarm?
}
```

A cover goal may mention what an expectation may (see [Call
variables](Calls.md#call-variables)). It constrains nothing: it is not
part of the procedure's [meaning](#meaning), of a call's constraint
`I_w`, or of an implementation's obligation. It is checked only in its
own procedure, not where the procedure is called: a goal is about the
procedure alone. A cover goal with a [trigger](#triggers) holds wherever
the trigger is false, so it is met by any behaviour in which the trigger
is false; write the scenario as a conjunction, such as `temp > 100 and
alarm?`, instead.

## Definitions

A `let x: T := e`, and a result `r` with the member `out r := e`, stand
for `e`. `e` is an expression of the variable's type, over the
procedure's variables, and it ends where the next member starts. A
`let`'s type is written, or, as for any variable, omitted for a name
ending in `?`, which is a `Bool`; a result's is written in the signature.
`det` works as for any output, and is still checked rather than implied.

```
mod accounts

pub proc handle(length: Int, taken?): (det accepted?) {
    let long? := length > 40     -- a name for a condition

    ensure rule: accepted? iff not (long? or taken?)
}
```

Let `D` be the definitions `d_k := e_k` of a procedure. The procedure
means what it would with each `d_k` replaced by `e_k` in its constraints
and its calls' arguments, repeatedly, until no defined variable remains.
Equivalently, `D` adds the equations `d_k = e_k`. The
[checks](../Check.md#definitions) use whichever form keeps their queries
decidable.

- **Acyclic.** A definition may not mention its own variable, directly
  or through other definitions, so the substitution ends (`F0411`).
- **Mentions.** A defined variable mentions what its definition mentions,
  transitively, as a [`match` binder](Expressions.md#matches) mentions
  what its scrutinee does. Every rule about where a variable may occur
  applies through it: one whose definition mentions only parameters may
  occur in an assumption or a call's argument, and one whose definition
  mentions an output may not occur in a function's argument.

A `let` names a subexpression for the whole procedure, as a [`where`
clause](Let.md) does for one constraint. Define a variable when the spec
computes it, and require it when the spec constrains it: a definition is
not a constraint, so the vacuity, redundancy and realizability checks no
longer see it.

## Natural numbers

A variable of type [`Nat`](Types.md#natural-numbers) brings the
constraint that it is at least 0, as though it were written in the spec:

- a parameter, an assumption;
- a result or an `exists`, a guarantee;
- a call's variable, a constraint of the call, as the called procedure's
  own variable does, even one that is defined there, where its
  definition already makes it at least 0;
- a defined variable, none: its definition is a `Nat`, so it is at least
  0 already.

These constraints have no names. They are never reported in a [minimal
set](../Check.md#minimal-sets), never checked for redundancy, and need no
check of their own: an argument or a definition of type `Nat` is at least
0 by its type. `lang::nat_variable` states what a `Nat` variable brings:

```fren
pub enum Brought { Nothing, Assumption, Guarantee }

pub proc nat_variable(
    own_output?,         -- an output of the procedure itself, rather than a parameter or a call's variable
    defined?,            -- a defined variable
): (det brought: Brought) {
    assume only_outputs: when defined?, own_output?

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
`lang::nat_variable` states: an assumption for a parameter, a guarantee
for an output, a constraint of the call for a call's variable, and
nothing for a defined variable, whose definition is checked to match
instead (see [Checks](../Check.md#pattern-types)). A call's parameter is
the one exception: what its type brings is the called procedure's
assumption, which the call assumption check asks of its argument, so it
is not also a constraint of the call. With the parameter `hops: Int is
1..`, the procedure assumes `hops is 1..`; with the result `level: Loud`,
it guarantees that `level` is one of `Loud`'s variants. Like a `Nat`'s,
these constraints have no names, are never reported in a minimal set, and
are never checked for redundancy. A call's argument for a parameter of a
pattern type is checked like any other assumption of the called
procedure, by the [call assumption check](../Check.md#call-assumptions).

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
gives its values, from those of its arguments. A procedure's meaning above is relative to an
interpretation: `A`, `I` and `R` may apply functions, and the variables
of abstract types range over the values the interpretation gives them.

An interpretation is chosen neither by the environment nor by the system:
it is the same for every input, every behaviour, and every procedure. The
[checks](../Check.md#interpretations) confirm their claims under every
interpretation, so a spec can rely only on what it states about a
function, such as an assumption `when f(x) = f(y), x = y` over the inputs
`x` and `y`. A system runs under one interpretation, and meets the
procedure if it does so under that one. In Lean, an
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
