# Generic functions

A [defined function](Items.md#defined-functions) may have *type
parameters*, written in angle brackets right after its name, before its
parameters, as a [generic type's](Generics.md) are after its name:

```text
fn unwrap_or<T>(o: Option<T>, d: T): T := match o { Option::Some(x) => x, Option::None => d }
fn swap<A, B>(p: Pair<A, B>): Pair<B, A> := Pair { fst := p.snd, snd := p.fst }
```

`Option` is the [prelude's](Prelude.md). Such a function is *generic*. Its parameters' and result's types, and the
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

A generic function is defined: SMT-LIB has no polymorphic `declare-fun`,
so an uninterpreted function cannot be generic, for now (`F0399`), with a
contract or without. A defined generic function needs no polymorphic
function in SMT-LIB, since its applications are
[unfolded](#meaning). Its type parameters are inferred at each
application from its parameters' and result's types, so each must be
mentioned by one of them (`F0400`): `fn f<T, U>(x: T): T` has no place
where a `U` could be inferred from.

`lang::generic_function` states which functions may have type parameters,
from whether the function is defined, how many type parameters it has, and
whether one of them is mentioned by no parameter's type nor the result's:

```fren
pub mod lang

pub comp generic_function {
    in defined?           -- written with `:= e`
    in params: Nat        -- how many type parameters it has
    in unmentioned?       -- one of them is mentioned by no parameter's type nor the result's
    pub det out accepted?

    ensure rule: accepted? iff (params = 0 or (defined? and not unmentioned?))

    expect plain: when params = 0, accepted?
    expect uninterpreted: when params > 0 and not defined?, not accepted?
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
    in defined?
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

    ensure rule: accepted? iff (params = 0 or (defined? and not unmentioned?))

    expect plain: when params = 0, accepted?
    expect in_result: when params = 1 and defined? and ty_mentions?(result, 0), accepted?
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
