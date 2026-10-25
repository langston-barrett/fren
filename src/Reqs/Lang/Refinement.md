# Refinement

```
refinement := "refine" IDENT ":" path "refines" path ["{" [binding ("," binding)* [","]] "}"] ["by" TACTICS]
binding    := IDENT [":=" expr]
```

`refine r: c refines a` states that the component `c` *refines* the
component `a`: `c` accepts every input that `a` accepts, and on those
inputs every behaviour of `c` meets `a`'s requirements. So whatever `a`
guarantees, `c` guarantees too, and every expectation that follows from
`a`'s assumptions and requirements holds of `c`'s behaviours as well.

Refinement is a way to gain confidence in a spec where parts of it are hard
for the solver (see [Decidability](Decidability.md#in-practice)): `a` can
be a simpler component that the solver decides, whose expectations are
checked, and `c` the precise one. Whether `c` refines `a` is itself
checked, by the solver, by [testing](../Check.md#checking-by-testing), or,
in Lean, by a proof.

```fren
pub mod refinement
```

## The interface

`a` and `c` are related through `a`'s variables. By default, each is
read as the variable of `c` of the same name: each input of `a` must be
an input of `c`, and each output of `a` a public output of `c`, of the same
type, or one that [widens](Types.md#natural-numbers) in the direction its
values flow. An output of `c` is read where `a`'s type is expected, so
`c`'s type must widen to `a`'s: a `Nat` output of `c` serves for an `Int`
of `a`. An input of `a` is given to `c`, so `a`'s type must widen to
`c`'s: an `Int` input of `c` serves for a `Nat` of `a`, but a `Nat` input
of `c` does not serve for an `Int` of `a`, since `c` need not accept the
inputs below 0 that `a` does. The input then has `a`'s type, and the
output `c`'s, for what a `Nat` brings. A private output of `a` must be a public output of `c` too: `a`'s
requirements may mention it, and the refinement can read it only from
`c`'s public outputs, since a private output says nothing about how `c`
computes it. `c` may have more inputs and outputs than `a`. An input of
`c` that no variable of `a` reads, by name or through a binding (see
[Bindings](#bindings)), is unconstrained by `a`'s assumptions, so an
assumption of `c` about such an input makes the refinement fail unless it
holds, given `a`'s assumptions, whatever that input is (see [The
obligation](#the-obligation)). An input that a binding reads is
constrained through it: with `x := y - 1`, `a`'s assumption `x > 0` says
`y - 1 > 0`, so `c` may assume `y > 1`. `a`'s instances are `a`'s own,
and stay hidden. A variable of `a` that `c` does not have
with the right role and type is an error (`F0412`). `refinement::interface`
states the rule for one variable of `a` that the refinement does not bind
(see [Bindings](#bindings)):

```fren
pub comp interface {
    in input?            -- the variable is an input of `a`, rather than an output
    in in_concrete?      -- `c` has a variable of the same name
    in concrete_input?   -- that variable is an input of `c`
    in concrete_pub?     -- that variable is public in `c`
    in a_widens?         -- its type in `a` widens to its type in `c` (`lang::widening`)
    in c_widens?         -- its type in `c` widens to its type in `a`
    pub det out accepted?

    req rule: accepted? iff (in_concrete? and (if input? then a_widens? else c_widens?)
        and (if input? then concrete_input? else not concrete_input? and concrete_pub?))

    expect hidden_outputs: when not input? and not concrete_pub?, not accepted?
    -- An input flows from `a` to `c`, and an output from `c` to `a`.
    expect inputs_from_abstract: when input? and accepted?, a_widens?
    expect outputs_from_concrete: when not input? and accepted?, c_widens?
}
```

## Bindings

Where the names differ, or `a` is more abstract than `c`, a refinement
can bind variables of `a`. The bindings are written as an
[instance](Instances.md#bindings)'s are, in braces after `a`:

```
refine fmt_exit_status: fmt::exit refines cli::exit_status { ran? := all_parsed? }
```

Each binding `x := e` gives the variable `x` of `a` as the expression `e`
over `c`'s variables, in place of `c`'s variable named `x`. `x` alone means
`x := x`. Since `e` is an expression, not just a name, a binding can be an
abstraction function, as in `{ forbidden? := level = Forbid }`. `e` must
have the type of `x` in `a`, as an instance's binding must have the type of
its input. It is written at the refinement, so other names in it resolve
as they do there.

A refinement may bind any variable of `a`, input or output, each at most
once, and nothing else: a name that is not a variable of `a` (`F0413`), or
one bound twice (`F0414`), is an error. Unlike an instance, it need not
bind every variable: the others are read by name, as in [The
interface](#the-interface). `refinement::binding` states the rule for one
name, given whether it is a variable of `a` and how many times the
refinement binds it:

```fren
pub comp binding {
    in variable?         -- the name is a variable of `a`
    in n: Nat            -- bindings of this name in the refinement
    pub det out accepted?

    req rule: accepted? iff (n = 0 or (variable? and n = 1))

    expect bound_once: when accepted?, n <= 1
}
```

A binding sees `c` from outside, as `a`'s variable would. Only `c`'s own
variables are in scope in it: the variables of `c`'s instances, such as
`inner.y`, are not, and neither are its instances' names, so `inner.y`
is a dotted name whose root is not in scope (`F0111`), as anywhere else.
Of `c`'s own variables, a binding may mention the inputs and public
outputs, and no private output. A binding of an input of `a` may mention
`c`'s inputs only, since `a`'s inputs are chosen by the environment, before `c` chooses
its outputs, and `a`'s assumptions, which mention them, constrain the
environment. A defined output of `c` is an output here, whatever its
definition mentions. A mention that breaks this rule is an error
(`F0415`). `refinement::mention` states it, for one variable of `c`
mentioned in a binding:

```fren
pub comp mention {
    in input?            -- the binding binds an input of `a`
    in concrete_input?   -- the variable mentioned is an input of `c`, rather than an output
    in concrete_pub?     -- it is public in `c`
    pub det out allowed?

    req rule: allowed? iff (concrete_input? or (not input? and concrete_pub?))

    expect inputs_see_inputs: when input? and allowed?, concrete_input?
    expect private_hidden: when not concrete_input? and not concrete_pub?, not allowed?
}
```

A binding is part of the refinement, which is checked as a component (see
[The obligation](#the-obligation)), so the [decidable
core](Decidability.md#relations) is a component's: if the refinement
applies a relational operator, in a binding or through `c` or `a`, then a
`card` of anything but a constant in a binding is outside the core, and
so are `c` and `a` if they count.

The indexes of a binding are checked for
[definedness](../Check.md#definedness) where it is read. An input's
binding is checked under all of `a`'s assumptions, with the bindings
substituted into them, and nothing else: not `c`'s instance, nor any
other hypothesis. An assumption on another binding can guard an index:
with `n := q.len` and `assume pos: n > 0` in `a`, `x := q[0]` is defined.
Without one, an input's binding is guarded within its own expression, as
in `if q != [] then q[0] else 0`. An output's binding is
checked under the hypotheses of the obligation's second part below: `a`'s
assumptions, the instance of `c`, and `a`'s instances.

## The obligation

In the notation of [Components](Components.md#meaning), with `i` the
inputs of `c`, `y` the variables of `c`'s instances, `o` its outputs, `w`
the variables of `a`'s instances, and each variable of `a` read as its
binding, over `i` and `o`, or else as `c`'s variable of the same name,
`c` refines `a` when, for all `i`:

  A_a(i) → A_c(i)

and for all `i`, `y`, `o`, `w`:

  A_a(i) ∧ I_c(i, y) ∧ R_c(i, y, o) ∧ D_c(i, y, o) ∧ I_a(i, w) → R_a(i, w, o) ∧ D_a(i, w, o)

Fren checks this as it checks a component: the refinement is a component
whose inputs are `c`'s, whose assumptions are `a`'s, with an instance of
`c` named as `c` is, and `a`'s instances, and whose expectations are `a`'s
requirements and the definitions of `a`'s defined outputs. Throughout,
`a`'s variables are replaced by their bindings, or their names, with
`c`'s outputs read from the instance of `c`. `a`'s instances are hypotheses there, as
`I_a` is above: their assumptions are `a`'s own obligations, checked in
`a`. The first part of the obligation is then
the [instance assumption](../Check.md#instance-assumptions) check of the
instance of `c`, and the second part its [expectation
checks](../Check.md#expectations). A failure is reported as for those
checks, with a counterexample, at the refinement. `refinement::checks` gives
which checks run on a refinement: those that check the obligation, and the
[definedness](../Check.md#definedness) of what it reads:

```fren
use check::Kind

pub comp checks {
    use check::Kind::{Definedness, Expectation, InstanceAssumption}
    in kind: Kind
    pub det out runs?

    req rule: runs? iff kind in {InstanceAssumption, Expectation, Definedness}
}
```

A refinement has no requirements of its own, so the other checks would
only repeat those of `a` and `c`.

## Evidence

By default the solver decides the obligation. `set_option fren.evidence
"tested" in` before the refinement has it tested instead (see [Checking by
testing](../Check.md#checking-by-testing)).

In Lean, `by` and tactics prove it instead: Fren generates the obligation
as a proposition, `r`, in the module's namespace, and the tactics must
prove it. Then no check of the refinement is asked of the solver, and a
proof that does not succeed is an error. The `fren` command does not run
Lean, so `by` is a static error there, like any construct that needs Lean
(see [The `fren` command](../Cli.md#agreement-with-lean)).

A refinement is not a component: it has no evidence in the sense of
[Traceability](../Trace.md), and does not change the evidence of `a` or `c`.

#fren_check
