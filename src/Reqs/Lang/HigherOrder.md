# Higher-order functions

A [defined function](Items.md#defined-functions)'s parameter may be a
function, whose type is a *function type*, and an application gives it a
*closure* or the name of a function. Such a function is *higher-order*:

```text
pub enum Option<T> { None, Some(T) }

fn map<T, U>(o: Option<T>, f: fn(T) -> U): Option<U> := match o {
    Option::Some(x) => Option::Some(f(x)),
    Option::None => Option::None,
}

fn twice(f: fn(Int) -> Int, x: Int): Int := f(f(x))

comp c {
    in o: Option<Int>
    in step: Int
    pub det out p: Option<Int> := map(o, |x| x + step)
    pub det out q: Int := twice(|n: Int| 2 * n, step)
}
```

Functions are *second-class*: a function is applied, or given to a
higher-order function, and never held in a variable, a field, a
collection or a constant, nor compared. So an application of a
higher-order function is [unfolded](#meaning), and its closures with it,
and nothing of a function type is left for the solver, which sees the
first-order formulas that it sees without them.

```
type          := base ["is" pattern] | "fn" "(" type ("," type)* ")" "->" type
closure       := "|" closure-param ("," closure-param)* "|" expr
closure-param := DECL [":" base]
```

## Function types

`fn(T) -> U` is the type of the functions from a `T` to a `U`, and
`fn(T1, T2) -> U` of those of two parameters, and so on: a function type
has at least one parameter, as a function does. A function type is
written only as the whole type of a defined function's parameter: not as
a field's or payload's type (`F0432`), a component's variable's (`F0433`),
nor a constant's, a function's result's, an uninterpreted function's
parameter's, a definition's of a `let` or `where`, a bound name's, a type
alias's or a closure's parameter's (`F0434`), and never within another
type, as an element type, a type argument, or a function type's parameter
or result (`F0435`). `lang::function_type_place` states where it may be
written, from where the type is written and the steps from that type down
to the function type within it, which both front ends read from the type
as written (`Core.fnTypeWithin`):

```fren
pub mod lang

-- Where a type is written.
pub enum TypeSite {
    DefinedParameter,
    UninterpretedParameter,
    Result,
    Constant,
    Variable,
    Field,
    Payload,
    Definition,
    BoundName,
    Alias,
    ClosureParameter,
}

-- A step from a type into one that it is built from: an element type of a
-- set, relation or sequence, a type argument of an instance, or a function
-- type's parameter or result.
pub enum Within { Element, Argument, FnParameter, FnResult }

-- Comparing sequences is outside the decidable core.
set_option fren.lint.undecidable "allow" in
pub comp function_type_place {
    use self::TypeSite::{DefinedParameter, Field, Payload, Variable}
    in site: TypeSite
    in within: Seq<Within>   -- the steps from the written type down to the function type, outermost first
    pub det out accepted?
    -- The error's code, `""` where it is accepted.
    pub det out code: Id := if accepted? then "" else if within != [] then "F0435"
        else if site in {Field, Payload} then "F0432" else if site = Variable then "F0433" else "F0434"

    ensure rule: accepted? iff (site = DefinedParameter and within = [])

    expect parameter: when site = DefinedParameter and within = [], accepted?
    expect nested: when within != [], not accepted?
    expect not_in_data: when site in {Field, Payload}, code = "F0432"
}
```

A function type's parameters and result are types of values, which may
mention the function's [type parameters](GenericFunctions.md), as
`fn(T) -> U` does above, but are not `Nat`s nor [pattern
types](Types.md#pattern-types) (`F0435`): those bring a fact or an
obligation of their values, which would be a [contract](Items.md#contracts)
of the function given, and the parameter has none, for now. Nor is one a
function type, as above. `lang::function_type_parts` states this, from
what each of its parameters' types and its result's is:

```fren
-- What a function type's parameter's or result's type is.
pub enum FnPart { Plain, Natural, Patterned, Function }

set_option fren.lint.undecidable "allow" in
pub comp function_type_parts {
    in kinds: Seq<FnPart>    -- what its parameters' types are, then its result's
    pub det out accepted?

    ensure rule: accepted? iff not (FnPart::Natural in kinds or FnPart::Patterned in kinds or FnPart::Function in kinds)

    expect plain: when kinds = [FnPart::Plain, FnPart::Plain], accepted?
    expect no_nat: when FnPart::Natural in kinds, not accepted?
}
```

## Function parameters

Within a higher-order function's body, a parameter `f` of type `fn(T) ->
U` is applied as a function is, `f(e)`, which gives as many arguments as
the function type has parameters (`F0308`), each of its parameter's type,
or a `Nat` where it is an `Int`, and has the function type's result type.
It may also be given, by its name, to another higher-order function's
parameter of its type. Mentioned in any other way it is a function that
is not applied (`F0210`). Its contract's clauses may apply it too, as its
body may: a precondition that applies `f` is one about the function
given.

For the function's own checks (see [Defined
functions](Items.md#defined-functions)), each function parameter is an
[uninterpreted function](Items.md#uninterpreted-functions) of its type, of
which nothing is known: the body's tables, the preconditions of the
functions it applies, its pattern types' obligations and its
postconditions are checked once, for every function that an application
could give, as they are for every value of the other parameters. So a
higher-order function's body is checked once, not at each application.
Since a function type has no `Nat` and no pattern type, an application of
`f` brings no fact. A counterexample of such a check shows the other
parameters' values, never a function's, as a counterexample shows no
uninterpreted function's.

## Arguments

An application of a higher-order function gives each function parameter a
closure or the name of a function of its type: a defined function,
generic or not, or, within another higher-order function, a function
parameter of the enclosing one. Anything else there is an error
(`F0436`), as is a closure anywhere else, and so is the name of an
uninterpreted function there: its applications would be within the
higher-order function's body, where its arguments may mention an output
of the enclosing component (see [Function
applications](Expressions.md#function-applications)). A function's name
anywhere else is a function that is not applied (`F0210`), as before.
`lang::function_argument` states this, from what the parameter takes and
the argument as written:

```fren
-- What a parameter takes: a value, or a function of `n` parameters.
pub enum ParamKind { Value, Function(Nat) }

-- An argument, as written: a closure of `n` parameters, the name of a
-- defined function, of an uninterpreted function or of the enclosing
-- function's function parameter, or any other expression.
pub enum ArgShape { Closure(Nat), DefinedName, UninterpretedName, FnParameterName, Other }

pub comp function_argument {
    use self::ArgShape::{Closure, DefinedName, FnParameterName, Other, UninterpretedName}
    in param: ParamKind
    in arg: ArgShape
    pub det out accepted?
    -- The error's code, `""` where it is accepted.
    pub det out code: Id := if accepted? then ""
        else if param = ParamKind::Value and arg is DefinedName | UninterpretedName | FnParameterName then "F0210"
        else "F0436"

    ensure rule: accepted? iff match param {
        ParamKind::Value => arg = Other,
        ParamKind::Function(n) => arg = Closure(n) or arg = DefinedName or arg = FnParameterName,
    }

    expect values: when param = ParamKind::Value, accepted? iff arg = Other
    expect closures: when param = ParamKind::Function(1), accepted? iff arg in {Closure(1), DefinedName, FnParameterName}
    expect no_uninterpreted: when arg = UninterpretedName, not accepted?
}
```

A closure's parameters are declared as a quantifier's bound names are:
their names are distinct (`F0213`), follow the [Boolean
names](Types.md#boolean-names) rule for their types, and are written with
`!` exactly when they [shadow](Components.md#shadowing) a name in scope.
A closure has as many parameters as the function type (`F0436`); a
parameter's type is the function type's, and if it is written, `|x: T|`,
it must be that type (`F0304`), which a [generic
function's](GenericFunctions.md) closure may need. Its body is an
expression of the function type's result type, or a `Nat` where that is an
`Int`. Like a defined function's body, it applies no uninterpreted
function (`F0331`).

The name of a function `g` given to a parameter of type `fn(T1, ..., Tn)
-> U` means the closure `|x1, ..., xn| g(x1, ..., xn)`, so it is checked
as that application is: `g` takes `n` arguments, of the types `T1` to
`Tn`, and its result is a `U`.

A closure's body may mention anything in scope where it is written, not
only its parameters: the component's variables, the enclosing function's
parameters, the binders of `match` arms and quantifiers, and the names of
`let`s and `where`s. It *captures* them, and they keep their meaning
where its body is unfolded (see [Meaning](#meaning)). Mentioning a
closure's parameter counts as mentioning a value that varies, as an
unbounded quantifier's bound name does, for the rules of [linear
arithmetic](Expressions.md#linear-arithmetic) and of constant divisors:
`|x| x * 2` is linear, and `|x| x * y` is not where `y` is a variable.

A closure's body's *obligations*, its tables' questions, the
preconditions of the functions it applies, its indexes and its pattern
types' obligations, are checked where it is unfolded: at each application
`f(e1, ..., en)` of its function parameter within the higher-order
function's body, unfolded as at the application, under the guards around
it there (`lang::guard`), and with the closure's parameters standing for
`e1` to `en`; under the conditions where the closure is written too. Since
closures are always unfolded and nothing is recursive, this is exact: a
closure applied only where its argument is in range, as in `if q.len > 0
then f(0) else 0` with `|i| q[i]`, has no index out of range, and one that
is never applied has nothing to check. An obligation is reported at the
closure, and its counterexample shows the values that reach it. The
higher-order function's own checks still treat its function parameters as
uninterpreted functions.

`lang::closure_obligation` states this of one application, from the
guarded operands around it, outermost first, with their conditions'
values, and whether the obligation holds at its arguments: it is checked
there exactly where the application is evaluated, which is where each
guard holds, as `lang::guard` states for each. The obligation of the
closure is the conjunction of this over the applications. Here an
application has three guards around it at most, and the rule is the same
for more:

```fren
-- Whether the operand `o`, whose condition has the value `c?`, is evaluated
-- (`lang::guard`).
pub fn guard_holds?(o: GuardedOperand, c?) := match o {
    GuardedOperand::WhenBody | GuardedOperand::ThenBranch | GuardedOperand::AndRight
    | GuardedOperand::ArmGuard | GuardedOperand::ArmBody => c?,
    _ => not c?,
}

set_option fren.lint.length_zero "allow" in
pub comp closure_obligation {
    in frames: Seq<GuardedOperand>   -- the guarded operands around the application, outermost first
    in conditions: Seq<Bool>         -- their conditions' values, in the same order
    in at_args?                      -- the obligation holds at the application's arguments

    assume same: frames.len = conditions.len and frames.len <= 3
    pub det out evaluated? := (frames.len <= 0 or guard_holds?(frames[0], conditions[0]))
        and (frames.len <= 1 or guard_holds?(frames[1], conditions[1]))
        and (frames.len <= 2 or guard_holds?(frames[2], conditions[2]))
    pub det out holds?               -- the obligation, as it is checked there

    ensure rule: holds? iff (not evaluated? or at_args?)

    expect unguarded: when frames.len = 0, holds? iff at_args?
    expect unevaluated: when frames = [GuardedOperand::ThenBranch] and conditions = [false], holds?
}
```

Function parameters and closures are not values, so neither is compared:
`=` and `!=` with an operand that is a closure, a function's name or a
function parameter is an error (`F0437`), whatever the other operand.
Two functions would be compared by their values at every argument, which
the solver cannot decide; written as closures they would be compared by
how they are written, which is not what `=` means. `lang::function_comparison`
states this, over the operands of a comparison, or of a chain of them:

```fren
-- An operand of `=` or `!=`, as written: a closure, the name of a
-- function or of a function parameter, or any other expression.
pub enum Comparand { Value, Closure, FunctionName }

set_option fren.lint.undecidable "allow" in
pub comp function_comparison {
    in operands: Seq<Comparand>
    pub det out accepted?

    ensure rule: accepted? iff not (Comparand::Closure in operands or Comparand::FunctionName in operands)

    expect values: when operands = [Comparand::Value, Comparand::Value], accepted?
    expect functions: when operands = [Comparand::FunctionName, Comparand::FunctionName], not accepted?
}
```

## Applications

An application of a higher-order function is typed as any other is (see
[Function applications](Expressions.md#function-applications)), and those
of a generic one have their type arguments inferred as in [Generic
functions](GenericFunctions.md#applications), where a function parameter's
type mentions the type parameters as any parameter's does, and its
argument is elaborated between the others: first the arguments that do
not wait, in order, then the functions, in order, each once the types of
its parameters are known, and last those that wait. A closure gives a
type parameter the argument that its body's type gives, if the result
type of the function type mentions it, or that its parameter's written
type gives; a function's name, those that its parameters' and its
result's types give. So in `map(o, |x| x + 1)` with `o: Option<Int>`,
`o` gives `T` the argument `Int`, which is the type of `x`, and the body,
an `Int`, gives `U` the argument `Int`. A closure whose parameter's type
mentions a type parameter that has no argument yet, and is not written,
cannot be elaborated (`F0400`).

## Meaning

An application of a higher-order function has the value of its body, as
any defined function's does, with each parameter standing for its
argument: a function parameter stands for its closure, so that each
application `f(e1, ..., en)` within the body has the value of the
closure's body, with each of its parameters standing for the value of
`ei`. The body is *unfolded* at the application, with each closure
unfolded within it. Fren has no recursion, so unfolding ends, and nothing
of a function type is left: the solver's queries are first-order, a
closure's body is in the [decidable core](Decidability.md) exactly when
its expression would be, and neither front end gives the solver a
function value.

The names that a closure captures keep the meaning that they have where
the closure is written, wherever its body is unfolded: a name that the
higher-order function's body binds around the application of `f`, such as
a `let` of the same name, or one of its own parameters, never captures a
name of the closure's body. Unfolding is *capture-avoiding*:

- The Lean-hosted front end gives a function type as a Lean arrow, `T → U`
  and `T1 → T2 → U`, and a closure as a Lean `fun`; it unfolds defined
  functions and reduces their applications to closures, as it gives any
  query to the solver, and Lean's bound variables cannot be captured.
- The `fren` command gives the higher-order function's body to the solver
  as a `let` of its other parameters, at their arguments, around its body,
  in which each application of a function parameter is a `let` of the
  closure's parameters, at the application's arguments, around the
  closure's body. First the names that the closure's body mentions free,
  other than its parameters, are renamed to *capture symbols*, `|#0|`,
  `|#1|` and so on, which no other symbol of the query is, and bound to
  those names by the outer `let`, beside the parameters. A closure's
  parameters' symbols are their names with a number of their own, so that
  neither is ever a symbol of another binder.

The names that the `fren` command gives the solver are of two kinds:
quoted symbols, `|x|`, and the symbols `let@N` of the definitions of `let`s
and `where`s. Each `let@N` is numbered as its definition is elaborated, by
one count that only grows, so each is bound by exactly one definition of the
spec, which a body's text binds wherever it is copied. A higher-order
function's body is elaborated before any application of it, since a
function is declared before it is used and is never recursive, so its text
binds no `let@N` that a closure at an application mentions. The `fren`
command does not rely on this: a closure's free `let@N`s are captured as
its quoted local symbols are. Each free symbol of the renamed closure's body
is then one of its parameters, one of its capture symbols, or a symbol of
the prelude, which nothing binds (`Core.captureFree`, proved in Lean of the
functions that run).

`lang::closure_capture` states this of a mention of a name `x` in the
closure's body, from the binders around it once the body is unfolded,
outermost first: the outer `let`'s capture symbols and the other
parameters, the higher-order body's binders around the application, the
inner `let`'s closure parameters, and the closure body's own binders
around the mention. A mention means the innermost binder of its name
(`lang::means?`). Where `x` is captured, the mention means the capture
symbol bound to `x`, and so the value that `x` has where the closure is
written; where it is a parameter of the closure, the closure's parameter;
and where the closure's body binds it, that binder:

```fren
-- A mention of `x` means the binder at position `i` among those around
-- it, outermost first: the innermost of its name.
set_option fren.lint.undecidable "allow" in
pub fn means?(around: Seq<Id>, x: Id, i: Int) := 0 <= i < around.len and around[i] = x
    and not x in around.slice(i + 1, around.len)

-- The capture symbols of the names `captured`, numbered from `next`, in order.
pub fn capture_symbols(Nat, Seq<Id>): Seq<Id>

-- The capture symbol numbered `k`, which is at least 0.
pub fn capture_symbol(Int): Id

-- What a mention of `x` in the closure's body is renamed to, where the
-- closure's parameters are `params` and the names it captures `captured`,
-- whose capture symbols are numbered from `next`.
pub fn renamed(Nat, Seq<Id>, Seq<Id>, Id): Id

set_option fren.lint.undecidable "allow" in
pub comp closure_capture {
    in next: Nat             -- the first capture symbol that the query does not yet have
    in captured: Seq<Id>     -- the names that the closure's body mentions free, other than its parameters
    in params: Seq<Id>       -- the closure's parameters' symbols
    in values: Seq<Id>       -- the higher-order function's other parameters
    in around: Seq<Id>       -- the higher-order body's binders around the application, outermost first
    in inner: Seq<Id>        -- the closure body's binders around the mention, outermost first
    in x: Id                 -- the name mentioned
    in k: Int                -- where `x` is first among `captured`, if it is captured
    in j: Int                -- where `x` is last among `params`, if it is a parameter

    -- The capture symbols from `next` on are new: no other binder has one.
    assume fresh: forall (n: Nat), when n >= next,
        not capture_symbol(n) in values and not capture_symbol(n) in around
        and not capture_symbol(n) in params and not capture_symbol(n) in inner
    -- A free name is captured, a parameter or bound within the body.
    assume free: x in captured or x in params or x in inner
    assume first: when x in captured, 0 <= k < captured.len and captured[k] = x and not x in captured.slice(0, k)
    assume last: when x in params, 0 <= j < params.len and params[j] = x and not x in params.slice(j + 1, params.len)
    -- The parameters and the names captured are told apart.
    assume apart: not (x in captured and x in params)

    pub det out symbols: Seq<Id> := capture_symbols(next, captured)
    pub det out mention: Id := if x in inner then x else renamed(next, captured, params, x)
    pub det out binders: Seq<Id> := symbols ++ values ++ around ++ params ++ inner

    ensure symbols_named: symbols.len = captured.len
        and (forall (i: Int), when 0 <= i < captured.len, symbols[i] = capture_symbol(next + i))
    ensure own_binders: when x in inner, mention = x
    ensure captures: when not x in inner and x in captured, means?(binders, mention, k)
    ensure parameters: when not x in inner and x in params,
        means?(binders, mention, symbols.len + values.len + around.len + j)
}
```

The front ends unfold alike, so they ask the same queries of the same
formulas, and report the same counterexamples, which never show a
function: a closure's parameters are bound within the queries, and a
function parameter is never a variable of a component.
