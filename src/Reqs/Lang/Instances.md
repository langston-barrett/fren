# Instances

An instance makes one component part of another.

```
instance := "inst" DECL ":" path "{" [binding ("," binding)* [","]] "}"
binding  := IDENT [":=" expr]
```

`inst w: c { x := e, ... }` makes `w` an instance of the component `c`,
binding each input `x` of `c` to the expression `e`. A binding `x` alone
means `x := x`. `c` must be declared, and visible, before the component that
instantiates it; in particular, a component cannot instantiate itself.
The name `w` may [shadow](Components.md#shadowing) a constant, a function
or a variant in scope, written `inst w!: c { ... }`.

```fren
pub mod inst
```

## Example

`band` classifies a temperature, and `thermostat` uses it:

```
pub comp band {
  in temp: Int
  in target: Int
  pub out too_cold?
  pub out too_hot?

  ensure cold: too_cold? iff temp < target - 2
  ensure hot: too_hot? iff temp > target + 2
}

pub comp thermostat {
  in temp: Int
  in target: Int
  pub out mode: Mode

  inst range: band { temp, target }

  ensure heat: when range.too_cold?, mode = Heat
  ensure cool: when range.too_hot?, mode = Cool
  ensure idle: unless range.too_cold? or range.too_hot?, mode = Off
}
```

`thermostat` can meet `heat` and `cool` together only because `band`'s
guarantees rule out a temperature that is both too cold and too hot. That
is how instances work in general: the instance's outputs are not the
component's to choose, but they are known to satisfy the instantiated
component's guarantees (see [Components](Components.md#meaning)).

## Bindings

An instance must bind each input of the instantiated component exactly once,
and must bind nothing else. A binding's expression cannot be a top-level
`when`, `unless`, `let` or [quantifier](Quantifiers.md), whose body would
run on into the following bindings; it must be parenthesized. Nor does a
binding take a `where` clause (see [Local definitions](Let.md)).

`inst::binding` states this rule, given what a bound name is in the
instantiated component and how many times the instance binds it:

```fren
pub enum Target { CompInput, CompOutput, Absent }

use self::Target::{CompInput, CompOutput}

pub comp binding {
    in target: Target
    in n: Nat            -- bindings of this name in the instance
    pub out accepted?

    ensure rule: accepted? iff ((target = CompInput and n = 1) or (target != CompInput and n = 0))

    expect inputs_bound_once: when target = CompInput and accepted?, n = 1
    expect outputs_not_bound: when target = CompOutput and n > 0, not accepted?
}
```

`inst::bindings` states the rule for the whole instance, which the rule
for each name cannot: that every input is bound. A set cannot see a name
bound twice, so repeats are counted:

```fren
pub type VarName

pub comp bindings {
    in inputs: Set(VarName)          -- the instantiated component's inputs
    in outputs: Set(VarName)         -- its other variables: its outputs
    in bound: Set(VarName)           -- the names the instance binds
    in n_repeated: Nat               -- bindings of a name bound earlier in the instance
    pub det out accepted?

    assume disjoint: (inputs inter outputs) = {}

    ensure rule: accepted? iff (bound = inputs and n_repeated = 0)

    expect outputs_not_bound: when (bound inter outputs) != {}, not accepted?
    expect all_inputs: when accepted?, inputs subset bound
}
```

## Instance variables

Within the component, `w.x` refers to the variable `x` of the instance `w`.
Only the inputs and public outputs of the instantiated component can be
referred to this way. Its private outputs, and the variables of its own
instances, are hidden.

Which variables an expression may mention depends on where it is:

| | own input | own output | `w.x` |
|---|---|---|---|
| assumption | yes | no | no |
| binding of an instance | yes | no | only if `w` is declared earlier |
| guarantee, expectation, [cover goal](Components.md#cover-goals) | yes | yes | yes |
| argument of a [function application](Expressions.md#function-applications) in a guarantee, expectation or cover goal | yes | no | yes |

A field read `p.x` mentions `p`, a binder of a [`match`
arm](Expressions.md#matches) mentions what its scrutinee mentions, a name
of a [`let` or `where`](Let.md) what its definition mentions, and a
[defined output](Components.md#defined-outputs) mentions what its
definition mentions. So a defined output whose definition mentions only
inputs may occur in an assumption, and an instance cannot bind a defined
output, which is an output.

Assumptions constrain the environment, so they see only inputs. Bindings
see inputs and earlier instances only, so instances never depend on each
other in a cycle. A function's arguments see no output of the component,
public or private, so that a function is only ever applied to values the
system does not choose: the [realizability
check](../Check.md#realizability) asks for outputs `∃ o. R`, and outputs
in arguments would make that query quantify over the function's
arguments, which the solver cannot decide in general. An application
within an assumption or a binding follows the rule of its place, which is
already as strict.

Whether an instance is declared earlier is a matter of positions in the
component's instances, in order, which `inst::earlier` states:

```fren
pub type InstName

pub comp earlier {
    in order: Seq(InstName)      -- the component's instances, in declaration order
    in owner: InstName           -- the instance whose variable is mentioned
    in binder: InstName          -- the instance whose binding mentions it
    in k_owner: Nat              -- the position of `owner` in `order`
    in k_binder: Nat             -- the position of `binder`
    pub det out earlier?

    assume positions: k_owner < order.len and order[k_owner] = owner
        and k_binder < order.len and order[k_binder] = binder
    -- Instance names are distinct.
    assume distinct: when owner = binder, k_owner = k_binder

    ensure rule: earlier? iff k_owner < k_binder

    expect not_itself: when owner = binder, not earlier?
    -- The first instance's variables can be bound in the second's, and not
    -- the other way.
    expect first_earlier: when owner != binder and k_owner = 0 and k_binder = 1, earlier?
    expect second_later: when owner != binder and k_owner = 1 and k_binder = 0, not earlier?
}
```

The positions are inputs, rather than found with `index_of`, which is
outside the [decidable core](Decidability.md#sequences); they are what the
elaborator computes anyway. `distinct` states that the names are distinct
only for the two at hand, which is all the rule needs.

`inst::mention` states this rule. `Place` is where a variable is mentioned
(`Constraint` covers guarantees, expectations and cover goals, and `Argument` an
argument within one of them), and `Role` is what the variable is: one of
the component's own, or one of an instance's.
`InstHidden` covers an instance's private outputs and the variables of the
instance's own instances.

```fren
pub enum Place { Assume, Binding, Constraint, Argument }

pub enum Role { Input, Output, InstInput, InstOutput, InstHidden }

use self::Place::{Argument, Assume, Binding, Constraint}
use self::Role::{Input, InstHidden, InstInput, InstOutput, Output}

pub comp mention {
    in place: Place
    in role: Role
    in earlier?          -- the variable's instance is declared before this binding
    pub out allowed?

    ensure inputs: when role = Input, allowed?
    ensure outputs: when role = Output, allowed? iff place = Constraint
    ensure instances: when role = InstInput or role = InstOutput,
        allowed? iff (place = Constraint or place = Argument or (place = Binding and earlier?))
    ensure hidden: when role = InstHidden, not allowed?

    expect assume_sees_inputs_only: when place = Assume and allowed?, role = Input
    expect no_cycles: when place = Binding and role != Input and allowed?, earlier?
    expect arguments_not_chosen: when place = Argument and allowed?, role != Output
}

#fren_check
```

## Checking

Each assumption of the instantiated component becomes an obligation on the
instance's bindings, confirmed by the [instance
check](../Check.md#instance-assumptions).
