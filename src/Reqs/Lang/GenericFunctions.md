# Generic functions

A [function](Items.md#functions), [defined](Items.md#defined-functions)
or [uninterpreted](Items.md#uninterpreted-functions), may have *type
parameters*, written in angle brackets right after its name, before its
parameters, as a [generic type's](Generics.md) are after its name:

```text
pub enum Option<T> { None, Some(T) }

fn unwrap_or<T>(o: Option<T>, d: T): T := match o { Option::Some(x) => x, Option::None => d }
fn swap<A, B>(p: Pair<A, B>): Pair<B, A> := Pair { fst := p.snd, snd := p.fst }
fn pick<T>(T, T): T
```

Such a function is *generic*. Its parameters' and result's types, and the
types written in its body and its contract, may mention its type
parameters, which stand for types there, so that `unwrap_or` is a function
from an `Option<T>` and a `T` to a `T`, for every type `T`. A function with
no type parameters is written as before, and `fn f(T)` declares the
uninterpreted function `f` of one parameter of type `T`, not a type
parameter: type parameters are written only in angle brackets. `fn f(T)(x:
T)`, a group of names right before a second `(`, is how they were written
before, and is an error (`F0156`), whose fix is `fn f<T>(x: T)` (see
[Angle brackets](Generics.md#angle-brackets)).

```
function      := ["pub"] "fn" declared-type"(" type ("," type)* ")" [":" type]
               | ["pub"] "fn" declared-type"(" variable ("," variable)* ")" [":" type] [":=" top] clause+
               | ["pub"] "fn" declared-type"(" variable ("," variable)* ")" [":" type] ":=" top
declared-type := IDENT | IDENT"<" IDENT ("," IDENT)* ">"
```

## Type parameters

A function's type parameters follow the [rules of a generic
type's](Generics.md#type-parameters): their names are distinct (`F0213`),
none has the name of a built-in type or of an item that a path of one
segment names where the function is declared (`F0388`), and none is an
element type, as in `Set<T>`, for now (`F0387`). A type parameter may be
an argument of an instance, as in `Option<T>`, and the whole type of a
parameter or the result, as `d` and the result of `unwrap_or` are.

Within the function, a type parameter is a type of its own, of which
nothing is known but that it has values, and that two of them are equal or
not: it is like an [abstract type](Types.md#abstract-types), declared for
the function alone. So the body may compare two values of `T`, pass them to
functions and constructions, and match the payloads that hold them, but it
may not add them or order them, which an instance's arguments may not
allow. Its checks, and its contract's, hold for every type `T`, since they
hold for a type of which nothing is known.

The rules that a type gives a name are of the type as declared: a
parameter or result of type `T` is not named with `?`, though an
application at `Bool` has a `Bool` (see [Boolean
names](Types.md#boolean-names)), as `id(b?)` does with `fn id<T>(x: T): T`.

Since nothing is known of a type parameter's values, a quantifier over a
type parameter, or over a type that mentions one, is outside the
[decidable core](Decidability.md) (`F0714`), and testing cannot evaluate it
(`F0639` for `quickcheck`), even where every instance that the spec applies
the function at is finite: the body is checked once, for every type, which
is conservative.

A generic function may be defined or not, with a contract or without: a
defined one's applications are [unfolded](#meaning), and each instance of
one without a body is an [unknown function of its
own](#uninterpreted-generic-functions), so the solver never needs a
polymorphic function. Its type parameters are inferred at each
application from its parameters' and result's types, so each must be
mentioned by one of them (`F0400`): `fn f<T, U>(x: T): T` has no place
where a `U` could be inferred from. A generic function without a body was
an error before (`F0399`), which nothing reports now.

`lang::generic_function` states which functions may have type parameters,
from how many it has, and whether one of them is mentioned by no
parameter's type nor the result's, whether the function is defined or not:

```fren
pub mod lang

pub comp generic_function {
    in params: Nat        -- how many type parameters it has
    in unmentioned?       -- one of them is mentioned by no parameter's type nor the result's
    pub det out accepted?

    ensure rule: accepted? iff (params = 0 or not unmentioned?)

    expect plain: when params = 0, accepted?
    expect inferable: when params > 0 and unmentioned?, not accepted?
}
```

`lang::generic_signature` states it over the function's signature: the
declared types of its parameters, in order, and of its result, in which a
type parameter `k` is mentioned exactly when `lang::ty_mentions?` says so
(`Ty.mentions`). Here a function has three parameters at most and three
type parameters at most, and the rule is the same for more: here the
parameters after the third, and the type parameters after the third, are
not looked at. It refines `lang::generic_function`:

```fren
pub fn ty_mentions?(Ty, Nat)   -- a type mentions the type parameter at that position

-- `declared.len > 0` rather than `declared != []`, which compares sequences
-- of an abstract type, whose equality Lean does not decide.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.length_zero "allow" in
pub comp generic_signature {
    in params: Nat               -- how many type parameters it has
    in declared: Seq<Ty>         -- its parameters' declared types, in order
    in result: Ty                -- its result's declared type

    -- Whether the type parameters `0`, `1` and `2` are in the signature: the
    -- result's type mentions them, or one of the parameters' types does.
    pub det out in0? := ty_mentions?(result, 0) or (declared.len > 0 and ty_mentions?(declared[0], 0))
        or (declared.len > 1 and ty_mentions?(declared[1], 0)) or (declared.len > 2 and ty_mentions?(declared[2], 0))
    pub det out in1? := ty_mentions?(result, 1) or (declared.len > 0 and ty_mentions?(declared[0], 1))
        or (declared.len > 1 and ty_mentions?(declared[1], 1)) or (declared.len > 2 and ty_mentions?(declared[2], 1))
    pub det out in2? := ty_mentions?(result, 2) or (declared.len > 0 and ty_mentions?(declared[0], 2))
        or (declared.len > 1 and ty_mentions?(declared[1], 2)) or (declared.len > 2 and ty_mentions?(declared[2], 2))
    pub det out unmentioned? := (params > 0 and not in0?) or (params > 1 and not in1?) or (params > 2 and not in2?)
    pub det out accepted?

    ensure rule: accepted? iff (params = 0 or not unmentioned?)

    expect plain: when params = 0, accepted?
    expect in_result: when params = 1 and ty_mentions?(result, 0), accepted?
}

set_option fren.lint.undecidable "allow" in
set_option fren.lint.length_zero "allow" in
refine signature_detail: generic_signature refines generic_function {
    unmentioned? := (params > 0 and not (ty_mentions?(result, 0) or (declared.len > 0 and ty_mentions?(declared[0], 0))
        or (declared.len > 1 and ty_mentions?(declared[1], 0)) or (declared.len > 2 and ty_mentions?(declared[2], 0))))
        or (params > 1 and not (ty_mentions?(result, 1) or (declared.len > 0 and ty_mentions?(declared[0], 1))
        or (declared.len > 1 and ty_mentions?(declared[1], 1)) or (declared.len > 2 and ty_mentions?(declared[2], 1))))
        or (params > 2 and not (ty_mentions?(result, 2) or (declared.len > 0 and ty_mentions?(declared[0], 2))
        or (declared.len > 1 and ty_mentions?(declared[1], 2)) or (declared.len > 2 and ty_mentions?(declared[2], 2)))),
}
```

## Applications

A generic function is applied as any other, `unwrap_or(x, 0)`: an
expression never writes type arguments, and an application's are
*inferred*, as a [construction's](Generics.md#type-arguments) are, with
the function's parameters for the construction's values and its result
for the construction's type:

- **From what is expected.** If a type is
  [expected](Types.md#checking-and-synthesis) of the application, each type
  parameter that matching the expected type against the declared result
  type gives an argument (`lang::parameter_matching`) has that argument,
  with a `Nat` widened to an `Int`. So with `n: Int`, `n = unwrap_or(x, 0)`
  gives `T` the argument `Int` from `n`.
- **From its arguments.** Otherwise, each type parameter takes its argument
  from the first argument whose parameter's declared type mentions it, and
  which synthesizes its type, as a construction's parameter does from its
  values: so `unwrap_or(x, 0)` with `x: Option<Bool>` gives `T` the
  argument `Bool`, and then `0` is a type mismatch.

An application some of whose type parameters neither gives an argument has
a type that cannot be known, as `unwrap_or(Option::None, {})` alone
(`F0400`). Once its arguments are known, each argument is checked against
its parameter's declared type, and the application has the declared result
type, each with the type arguments for the type parameters
(`lang::instantiation`). The arguments are elaborated in the order in which
a construction's values are (`lang::construction_order`), the expected
type standing for an expected instance for the type parameters it gives
arguments: one that waits, because it does not synthesize its type and its
parameter's declared type mentions a type parameter that has no argument
yet, is elaborated after the others.

`lang::call_type_argument` states this for one type parameter `k` of a
generic function, from the declared types of its parameters, which of its
arguments synthesize their types, its declared result type, and whether a
type is expected of the application. It is `lang::type_argument_inference`,
with matching the expected type against the result in place of an expected
instance:

```fren
set_option fren.lint.undecidable "allow" in
pub comp call_type_argument {
    in declared: Seq<Ty>           -- the declared types of the function's parameters, in order
    in synthesizes: Seq<Bool>      -- which arguments synthesize their types
    in k: Nat                      -- the type parameter
    in result_matched?             -- a type is expected of the application, and matching it against the result gives `k` an argument
    in result_arg: Ty              -- that argument
    in matched?                    -- matching the first giver's type against its declared type gives `k` an argument
    in matched: Ty                 -- that argument

    assume as_many: synthesizes.len = declared.len

    pub det out giver: Int := first_giver(declared, synthesizes, k)
    pub det out known? := result_matched? or (giver >= 0 and matched?)
    pub det out argument: Ty := if result_matched? then widened(result_arg) else widened(matched)

    expect from_result: when result_matched?, known? and argument = widened(result_arg)
    expect no_giver: when not result_matched? and giver < 0, not known?
}
```

`lang::call_order` states in which order the arguments are elaborated,
which type parameters end with an argument, and whether the application's
type arguments are reported unknown, over its arguments, `lang::ArgMode`s as
for `lang::construction_order`, and which type parameters the expected
type gives an argument. Here an application has two arguments at most,
of a function with three type parameters at most, and the rule is the same
for more. It is
`lang::construction_order` where no instance is expected and the expected
type gives no argument:

```fren
-- Value `j`'s position, if it is among the values and waits, or does not, as
-- `waiting?` says, where `from_result` gives the type parameters that the
-- expected type gives an argument.
set_option fren.lint.undecidable "allow" in
pub fn call_waits?(values: Seq<ArgMode>, from_result: Seq<Bool>, j: Int) := 0 <= j < values.len
    and match values[j] {
    ArgMode::Waits(Arg::P0) => not ArgMode::Gives(Arg::P0) in values.slice(0, j) and not (from_result != [] and from_result[0]),
    ArgMode::Waits(Arg::P1) => not ArgMode::Gives(Arg::P1) in values.slice(0, j) and not (from_result.len > 1 and from_result[1]),
    ArgMode::Waits(Arg::P2) => not ArgMode::Gives(Arg::P2) in values.slice(0, j) and not (from_result.len > 2 and from_result[2]),
    ArgMode::Waits(Arg::Other) => false,
    ArgMode::Gives(_) => false,
}

set_option fren.lint.undecidable "allow" in
pub fn call_position_if(values: Seq<ArgMode>, from_result: Seq<Bool>, waiting?, j: Int): Seq<Int> :=
    if 0 <= j < values.len and call_waits?(values, from_result, j) = waiting? then [j] else []

set_option fren.lint.undecidable "allow" in
pub comp call_order {
    use self::Arg::{P0, P1, P2}
    use self::ArgMode::{Gives, Waits}
    in params: Nat                 -- how many type parameters the function has: `P0`, `P1`, ...
    in values: Seq<ArgMode>          -- the application's arguments, in order
    in from_result: Seq<Bool>      -- for each type parameter, whether the expected type gives it an argument

    assume few: values.len <= 2 and params <= 3 and from_result.len = params
    assume own_parameters: forall (a: Arg), when Gives(a) in values or Waits(a) in values, within?(a, params)

    -- The arguments' positions, in the order in which they are elaborated:
    -- those that do not wait, in order, then those that do.
    pub det out order: Seq<Int> :=
        call_position_if(values, from_result, false, 0) ++ call_position_if(values, from_result, false, 1)
        ++ call_position_if(values, from_result, false, 2) ++ call_position_if(values, from_result, true, 0)
        ++ call_position_if(values, from_result, true, 1) ++ call_position_if(values, from_result, true, 2)
    -- For each type parameter, whether it ends with an argument.
    pub det out given: Seq<Bool> := (if params >= 1 then [from_result[0] or Gives(P0) in values] else [])
        ++ (if params >= 2 then [from_result[1] or Gives(P1) in values] else [])
        ++ (if params >= 3 then [from_result[2] or Gives(P2) in values] else [])
    pub det out unknown? := false in given

    expect each_once: order.len = values.len
    expect from_the_result: when params = 1 and from_result = [true] and values = [Waits(P0), Gives(P0)],
        order = [0, 1] and not unknown?
    expect waiting: when params = 1 and from_result = [false] and values = [Waits(P0), Gives(P0)],
        order = [1, 0] and not unknown?
    expect nothing_gives: when params = 1 and from_result = [false] and values = [Waits(P0)], unknown?
}
```

`lang::call_instance` states the type that an application of a generic
function has once its type arguments are inferred: its declared result
type, instantiated (`lang::instantiation`) with the type arguments.
`lang::instantiated` is what `lang::instantiation` gives. Each argument is
checked against its parameter's declared type instantiated so too, as
`lang::call_order`'s elaboration has it:

```fren
pub fn instantiated(Ty, Seq<Ty>): Ty   -- `lang::instantiation`'s result

pub comp call_instance {
    in result: Ty                  -- the function's declared result type
    in arguments: Seq<Ty>          -- the application's type arguments
    pub det out result_type: Ty := instantiated(result, arguments)   -- the application's type
}
```

Whether an application of a generic function synthesizes its type is
stated by [`lang::synthesizes`](Types.md#checking-and-synthesis), with the
shape `Construction` whose parts are the type parameters that its result
type mentions: it synthesizes exactly when an argument that synthesizes
its type gives each of them an argument.

## Uninterpreted generic functions

A generic function without a body is
[uninterpreted](Items.md#uninterpreted-functions) at each instance, and
each instance is an unknown function of its own: `pick<Int>` and
`pick<Bool>` are two functions, which nothing relates. That is sound, since
all that is known of an uninterpreted function is that it is a function,
applied to equal arguments it gives equal results, and equal arguments
have the same type, so that this never relates two instances. Nothing in
Fren relies on two instances being related, as parametricity would relate
them. So with

```text
fn pick<T>(T, T): T
fn choose<T>(a: T, b: T): T
    ensure either: choose(a, b) = a or choose(a, b) = b
```

`pick(x, y) = pick(x, y)` holds at any instance, and `choose(1, 2)` is `1`
or `2`, but nothing says whether `pick(1, 2) = 1` when `pick(true, false)`
is `true`.

An application of an instance is an application of an uninterpreted
function, and brings what one does: at least 0, if its result is a `Nat`,
that it matches its result type, if that type brings a constraint, and
each postcondition wherever its arguments meet the preconditions, all at
its instance, with its type arguments for the type parameters. At each
application, its arguments must meet its preconditions, at its instance,
which the [precondition check](../Check.md#preconditions) confirms, as for
a defined generic function.

`lang::uninterpreted_instance` states the instance that an application of a
generic function without a body applies: its parameters' and result's
declared types, instantiated with the application's type arguments
(`lang::instantiation`), which are the sorts of its unknown function, the
type whose constraint each of its applications brings, which is the
instance's result type, with its patterns, not the declared one, so that
`pick(r)` of an `r: R` brings what `R`'s fields' pattern types do, and
whether each of its applications is at least 0. A type argument is never a
`Nat`, since an inferred one is widened (see [Applications](#applications)),
so it is at least 0 exactly when the declared result type is `Nat`. Here a
function has three parameters at most, and an application three type
arguments, and the rule is the same for more:

```fren
-- `arguments.len < 1` rather than `arguments = []`, which compares
-- sequences of an abstract type, whose equality Lean does not decide.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.length_zero "allow" in
pub comp uninterpreted_instance {
    in declared: Seq<Ty>         -- its parameters' declared types, in order
    in result: Ty                -- its result's declared type
    in arguments: Seq<Ty>        -- the application's type arguments

    assume few: declared.len <= 3 and arguments.len <= 3
    -- Each inferred type argument is widened.
    assume widened: (arguments.len < 1 or kind(arguments[0]) != ValueType::NatTy)
        and (arguments.len < 2 or kind(arguments[1]) != ValueType::NatTy)
        and (arguments.len < 3 or kind(arguments[2]) != ValueType::NatTy)

    -- The sorts of the instance's unknown function.
    pub det out params: Seq<Ty> := (if declared.len > 0 then [instantiated(declared[0], arguments)] else [])
        ++ (if declared.len > 1 then [instantiated(declared[1], arguments)] else [])
        ++ (if declared.len > 2 then [instantiated(declared[2], arguments)] else [])
    pub det out result_type: Ty := instantiated(result, arguments)
    pub det out fact_type: Ty    -- the type whose constraint each of its applications brings
    pub det out nat?             -- each of its applications is at least 0

    ensure facts_at_instance: fact_type = result_type
    ensure nat_rule: nat? iff kind(result_type) = ValueType::NatTy

    expect each_param: params.len = declared.len
}
```

Its contract is checked first at its type parameters, each a sort of
which nothing is known, as a defined generic function's body and contract
are: the [contract
realizability](../Check.md#contracts-of-uninterpreted-functions) check,
whose two queries ask whether its preconditions can hold and whether, for
all arguments that meet them, some value meets every postcondition. A
formula that holds over a sort of which nothing is known holds at every
instance, since it cannot use any type's structure. So a contract that
passes there holds at every instance, and is assumed at each. The solver
looks there for a small domain on which it fails (`finite-model-find`),
since one may fail only where a type has a single value, or where
arguments are equal, which every type allows: `fn other<T>(x: T): T` with
`ensure diff: other(x) != x` fails at a type with one value, but holds at
`Bool` and at `Int`.

Where that check does not pass, whether it fails or is not decided, the
contract is checked at each instance that the spec applies instead, with
the instance's types. Each is then the check of a function without type
parameters, named after the instance, as `other<One>`: a failure is the
error `F0631`, an undecided check is `F0608`, and its postconditions are
assumed at that instance, as a function without type parameters' are
whatever its check finds. So a contract that fails only at types that the
spec does not apply it at is accepted.

An item's checks use the instances that its applications apply: those it
writes, and, for each instance of a generic function among them, those
that the function's body and contract apply, at that instance, and so on
(transitively). A generic function's own items are its body and contract,
whose applications at its own type parameters are its own. An instance at
another generic function's type parameters, as `other<g::0::T>` in a
contract of `g` that applies `other`, is checked with finite-model finding,
as the check at type parameters' sorts is.

Each instance is checked once, by the first run of checks whose items use
it: the `fren` command checks every item in one run, and the Lean-hosted
front end checks those that each `#fren_check` names, or those of its file,
and records in its environment, which the modules that import it see,
which instances each run has checked. In a run, an instance that no
earlier run has checked is checked with the first item, in the order of
the files and of the items in each, that the run checks and whose checks
use it: with the function's own check, if the run checks it and that item
is in the function's file, and otherwise with that item's, and reported at
that item. A file's runs know only of it and the files before it, which the
Lean-hosted front end's imports are, so a function's own check cannot know
of an instance that only a later file applies, as `other<client::One>` in a
module that imports `other`'s and applies it at its own `One`: that file's
first checked item that uses it checks it. Where every item of every file
is checked, by one run or by a run for each file in order, the item is the
same in both front ends: the first item whose checks use the instance, or
the function, if that item is in its file. `lang::instance_site` states
where a run checks an instance's contract, from the function's file,
whether the run checks the function, whether an earlier run has checked
the instance, and the items that the run checks and whose checks use it,
in order (`Core.instanceSites` finds them, through `Core.instancesThrough`,
and both front ends call it):

```fren
pub struct ItemAt { file: Int, item: Int }   -- an item, by its file and its position in it
pub enum CheckSite { Unchecked, AtFunction, AtItem(ItemAt) }

-- `users.len < 1` rather than `users = []`, which compares sequences.
set_option fren.lint.length_zero "allow" in
pub comp instance_site {
    in function_file: Int     -- the file that declares the function
    in function_checked?      -- the run checks the function's own contract
    in done?                  -- an earlier run checked the instance
    in users: Seq<ItemAt>     -- the items that the run checks and whose checks use the instance, in order
    pub det out site: CheckSite := if done? or users.len < 1 then CheckSite::Unchecked
        else if function_checked? and users[0].file = function_file then CheckSite::AtFunction
        else CheckSite::AtItem(users[0])

    expect once: when done?, site = CheckSite::Unchecked
    expect later_file: when not done? and users.len > 0 and users[0].file != function_file,
        site = CheckSite::AtItem(users[0])
    -- Where the run checks everything, as the `fren` command's does.
    expect everything: when function_checked? and not done? and users.len > 0 and users[0].file = function_file,
        site = CheckSite::AtFunction
}
```

The instances checked with the function's own check are those at
`AtFunction`.

```fren
pub enum Decided { Holds, Fails, Undecided }

-- `in` on a sequence is outside the decidable core.
set_option fren.lint.undecidable "allow" in
pub comp generic_contract {
    in at_sorts: Decided           -- the check at the type parameters' sorts
    in instances: Seq<Decided>     -- the check at each instance that the spec applies, in order
    -- The checks reported, in order.
    pub det out reported: Seq<Decided> := if at_sorts = Decided::Holds or instances = [] then [at_sorts] else instances

    expect fast: when at_sorts = Decided::Holds, reported = [Decided::Holds]
    expect accepted: when instances = [Decided::Holds, Decided::Holds], not Decided::Fails in reported
    expect unapplied: when instances = [], reported = [at_sorts]
}
```

A generic defined function's body applies no uninterpreted function,
generic or not (`F0331`), so that its values are fully known (see
[Defined functions](Items.md#defined-functions)), but its contract may
apply one: there, at its own type parameters, the generic function is the
instance at their sorts, for the checks of the contract, and at each of
its instances, at that instance. A component that applies a generic
function without a body is not [enumerated](../Check.md#enumerable-types)
(`F0645`).

## Meaning

An application of a generic function has the value of its body, with each
parameter standing for the value of its argument, as an application of any
defined function has (see [Function
applications](Expressions.md#function-applications)), and each type
parameter for its type argument. So it is *unfolded* at its instance, and
the solver never sees a polymorphic function:

- The `fren` command gives the solver one `define-fun` for each instance
  that an application uses, named after the function and its type
  arguments as they print, as `|::unwrap_or<Int>|`, whose sorts are the
  arguments', and one for the function itself, `|::unwrap_or|`, over a sort
  of its own for each type parameter, `|::unwrap_or::0::T|`, for the checks
  of its body and its contract.
- The Lean-hosted front end gives a generic function a Lean definition with
  an explicit parameter of type `Type` for each type parameter, followed by
  an `Inhabited` instance for it (see [Generated
  Lean](../Generated.md#generic-functions)), and the solver sees its body
  at each application, unfolded with the type arguments given explicitly.

Each type parameter is, for the checks of the function's body and
contract, a sort of its own, of which the solver knows nothing: both front
ends check the body and the contract once, for every type.

An application of a generic function without a body is of its instance's
unknown function:

- The `fren` command gives the solver one `declare-fun` for each instance
  that an application uses, named as a defined function's instance is, as
  `|::pick<Int>|`, whose sorts are `lang::uninterpreted_instance`'s, and
  one for the function itself, `|::pick|`, over its type parameters'
  sorts, for the checks of its contract and of the bodies and contracts
  that apply it at their own type parameters. Each clause of its contract
  is a `define-fun` at each instance too, as `|::choose<Int>#either|`.
- The Lean-hosted front end gives it an opaque constant, whose type takes
  a `Type` and its `Inhabited` instance for each type parameter first (see
  [Generated Lean](../Generated.md#generic-functions)), applied to the type
  arguments. Each check gives each instance that its formulas apply, once
  the definitions and clauses that they apply are unfolded, a local of its
  own, declared before the variables, as the `fren` command declares it,
  so that the solver sees the same unknown functions.

A counterexample shows the values of the variables, as it does for any
uninterpreted function.
