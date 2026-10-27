# Calls

A call makes one procedure part of another.

```
call := "call" DECL ":=" path "(" [expr ("," expr)* [","]] ")"
```

`call w := p(e1, ..., en)` makes `w` a call of the procedure `p`, binding
the `k`th parameter of `p` to the `k`th argument `ek`. `p` must be
declared, and visible, before the procedure that calls it; in particular,
a procedure cannot call itself. The name `w` may
[shadow](Procedures.md#shadowing) a constant, a function or a variant in
scope, written `call w! := p(...)`. `call` is a contextual keyword: it
starts a member, and is a name anywhere else.

```fren
pub mod call
```

## Example

`band` classifies a temperature, and `thermostat` calls it:

```
pub proc band(temp: Int, target: Int): (too_cold?, too_hot?) {
  ensure cold: too_cold? iff temp < target - 2
  ensure hot: too_hot? iff temp > target + 2
}

pub proc thermostat(temp: Int, target: Int): (mode: Mode) {
  call range := band(temp, target)

  ensure heat: when range.too_cold?, mode = Heat
  ensure cool: when range.too_hot?, mode = Cool
  ensure idle: unless range.too_cold? or range.too_hot?, mode = Off
}
```

`thermostat` can meet `heat` and `cool` together only because `band`'s
guarantees rule out a temperature that is both too cold and too hot. That
is how calls work in general: the call's results are not the procedure's
to choose, but they are known to satisfy the called procedure's guarantees
(see [Procedures](Procedures.md#meaning)).

## Arguments

A call gives one argument for each parameter of the called procedure, in
the order that it declares them, and nothing else: too many arguments
are an error (`F0408`), and so are too few (`F0409`). Each argument is
an expression of its parameter's type, parsed as a [function
application's](Expressions.md#function-applications) argument is, so it
takes no [`where` clause](Let.md). The arguments may be written one to a
line, with a comma after the last (see [Trailing
commas](../Fmt.md#trailing-commas)).

`call::arguments` states what a call binds, given the called procedure's
parameters and the call's arguments, in order: each parameter at a
position `k` is bound to the argument at `k`, if the numbers agree. Both
front ends and the evaluator bind a call's arguments with the same
function, `Fren.Core.callBindings`, which its implementation runs. A
parameter's name is its name as declared, without the `!` of
[shadowing](Procedures.md#shadowing).

```fren
pub type VarName

pub type Arg

pub enum Arity { Fits, TooMany, TooFew }

pub proc arguments(
    params: Seq<VarName>,        -- the called procedure's parameters, in order
    args: Seq<Arg>,              -- the call's arguments, in order
    k: Int,                      -- any position
): (
    det arity: Arity,            -- whether there is an argument for each parameter
    det binds?,                  -- the call binds the parameter at `k`
    param: VarName,              -- if so, that parameter
    arg: Arg,                    -- and the argument it is bound to
) {
    ensure fits: arity = (if args.len = params.len then Arity::Fits
        else if args.len > params.len then Arity::TooMany else Arity::TooFew)
    ensure bound: binds? iff (arity = Arity::Fits and 0 <= k < params.len)
    ensure positional: when binds?, param = params[k] and arg = args[k]

    expect nothing_called: when params = [] and args = [], arity = Arity::Fits and not binds?
    expect first: when arity = Arity::Fits and params != [] and k = 0, param = params[0] and arg = args[0]
    expect each_once: when binds?, k < args.len
}
```

## Call variables

Within the procedure, `w.x` refers to the variable `x` of the call `w`.
Only the parameters and results of the called procedure can be referred
to this way. Its `exists` and `let` variables, and the variables of its
own calls, are hidden.

Which variables an expression may mention depends on where it is:

| | own parameter | own result, `exists` or `let` | `w.x` |
|---|---|---|---|
| assumption | yes | no | no |
| argument of a call | yes | no | only if `w` is declared earlier |
| guarantee, expectation, [cover goal](Procedures.md#cover-goals) | yes | yes | yes |
| argument of a [function application](Expressions.md#function-applications) in a guarantee, expectation or cover goal | yes | no | yes |

A field read `p.x` mentions `p`, a binder of a [`match`
arm](Expressions.md#matches) mentions what its scrutinee mentions, a name
of a [`let` or `where`](Let.md) what its definition mentions, and a
variable with a [definition](Procedures.md#definitions) mentions what its
definition mentions. So a `let` whose definition mentions only parameters
may occur in an assumption, and in a call's argument.

Assumptions constrain the environment, so they see only parameters. A
call's arguments see parameters and earlier calls only, so calls never
depend on each other in a cycle. A function's arguments see no output of
the procedure, so that a function is only ever applied to values the
system does not choose: the [realizability
check](../Check.md#realizability) asks for outputs `∃ o. R`, and outputs
in arguments would make that query quantify over the function's
arguments, which the solver cannot decide in general. An application
within an assumption or a call's argument follows the rule of its place,
which is already as strict.

Whether a call is declared earlier is a matter of positions in the
procedure's calls, in order, which `call::earlier` states:

```fren
pub type CallName

pub proc earlier(
    order: Seq<CallName>,        -- the procedure's calls, in declaration order
    owner: CallName,             -- the call whose variable is mentioned
    caller: CallName,            -- the call whose argument mentions it
    k_owner: Nat,                -- the position of `owner` in `order`
    k_caller: Nat,               -- the position of `caller`
): (det earlier?) {
    assume positions: k_owner < order.len and order[k_owner] = owner
        and k_caller < order.len and order[k_caller] = caller
    -- Call names are distinct.
    assume distinct: when owner = caller, k_owner = k_caller

    ensure rule: earlier? iff k_owner < k_caller

    expect not_itself: when owner = caller, not earlier?
    -- The first call's variables can be passed to the second, and not the
    -- other way.
    expect first_earlier: when owner != caller and k_owner = 0 and k_caller = 1, earlier?
    expect second_later: when owner != caller and k_owner = 1 and k_caller = 0, not earlier?
}
```

The positions are inputs, rather than found with `index_of`, which is
outside the [decidable core](Decidability.md#sequences); they are what the
elaborator computes anyway. `distinct` states that the names are distinct
only for the two at hand, which is all the rule needs.

`call::mention` states this rule. `Place` is where a variable is mentioned
(`Constraint` covers guarantees, expectations and cover goals, `CallArg`
an argument of a call, and `FnArg` an argument of a function application
within a constraint), and `Role` is what the variable is: one of the
procedure's own, or one of a call's. `CallHidden` covers a call's
`exists` and `let` variables and the variables of its own calls.

```fren
pub enum Place { Assume, CallArg, Constraint, FnArg }

pub enum Role { Input, Output, CallInput, CallOutput, CallHidden }

use self::Place::{Assume, CallArg, Constraint, FnArg}
use self::Role::{CallHidden, CallInput, CallOutput, Input, Output}

pub proc mention(
    place: Place,
    role: Role,
    earlier?,            -- the variable's call is declared before this argument's
): (allowed?) {
    ensure inputs: when role = Input, allowed?
    ensure outputs: when role = Output, allowed? iff place = Constraint
    ensure calls: when role is CallInput | CallOutput,
        allowed? iff (place is Constraint | FnArg or (place = CallArg and earlier?))
    ensure hidden: when role = CallHidden, not allowed?

    expect assume_sees_inputs_only: when place = Assume and allowed?, role = Input
    expect no_cycles: when place = CallArg and role != Input and allowed?, earlier?
    expect arguments_not_chosen: when place = FnArg and allowed?, role != Output
}

#fren_check
```

## Checking

Each assumption of the called procedure becomes an obligation on the
call's arguments, confirmed by the [call assumption
check](../Check.md#call-assumptions).
