# Generic types

An enumeration or a record may have *type parameters*, written in angle
brackets after its name, which stand for types within its
declaration:

```text
pub enum Option<T> { None, Some(T) }
pub struct Pair<A, B> { fst: A, snd: B }
pub enum List<T> { Nil, Cons(T, List<T>) }
```

`Option` is the [prelude's](Prelude.md), declared as above, so a spec uses
it without declaring it, and one that declares its own writes
`Option!` (see [Shadowing the prelude](Modules.md#shadowing-the-prelude)).

Such a type is *generic*. It is used with a *type argument* for each of
its parameters, in the same `<...>` style as `Set<T>`: `Option<Int>` is
an *instance* of `Option`, whose values are those of the enumeration with
`Int` for `T`, that is `Option::None` and `Option::Some(n)` for every
`Int` `n`. Two instances are the same type exactly when their arguments
are, so `Option<Int>` and `Option<Bool>` are different types, and neither
is `Option` itself, which is not a type until it has its arguments.

```
enumeration   := ["pub"] ["ordered"] "enum" declared-type "{" variant ("," variant)* [","] "}"
record        := ["pub"] ["ordered"] "struct" declared-type "{" field ("," field)* [","] "}"
               | ...
declared-type := IDENT | IDENT"<" IDENT ("," IDENT)* ">"
type          := ... | path ["<" type ("," type)* ">"]
```

The `<` follows the name directly, and so does its `<` in an instance
(see [Angle brackets](#angle-brackets)).

A record with type parameters always has named fields: `struct P(A, B)`
without braces is a [newtype](Items.md#newtypes) of two types, which is an
error, and Fren does not yet have a newtype with type parameters.

## Angle brackets

Type parameters and type arguments are written in angle brackets, `<`
and `>`, as in Rust: `enum Option<T>`, `fn unwrap_or<T>(...)`,
`Option<Int>`, `Set<Int>`, `Seq<Int>` and `Rel<A, B>`. A newtype's
parentheses, `struct Ms(Int)`, and a variant's, `Some(T)`, hold a
payload's types, not type arguments, and stay parentheses.

**Where a type is written.** A type is written only after the `:` of an
input, an output, a field, a parameter, a function's result, a constant,
a quantifier's binder, as in `forall (x: Set<Int>), e`, or a definition
of a `let` or a `where` clause, as in `let s: Set<Int> := {} in e`; after
the `:=` of a type alias; as a type argument; and in a variant's or a
newtype's parentheses. An expression never writes a type, nor type
arguments, which are [inferred](#type-arguments), even those of a
[generic function](GenericFunctions.md#applications). So a `<` within an
expression is always a comparison, and a `<` within a type always opens
type arguments: `forall (x: Set<Int>), x.card < 3` has both.

**The bracket after a name.** The `<` that opens type arguments or type
parameters follows the name directly, with no space, line break or
comment between them, as a call's `(` does
([Lexical structure](Lexical.md#punctuators)): `Set <Int>` is an error
(`F0144`). Within the brackets, spaces are allowed, and `fren fmt` removes
them. A `(` after a type's name is not the type's: the type ends before
it, so `Option(Int)` is a parse error, and after a declaration's name, it
opens a newtype's types or a function's parameters, not type parameters.
`lang::type_bracket` states what the bracket after the name does:

```fren
-- The punctuator right after a type's name, or after a generic
-- declaration's name.
pub enum Bracket { Angle, Paren, Other }

-- What it does.
pub enum AfterName {
    Opens,          -- opens the type arguments or type parameters
    Spaced,         -- a `<` after a space: `F0144`
    Ends,           -- not the type's: the type or the name ends before it
}

pub proc type_bracket(
    bracket: Bracket,
    adjacent?,                   -- it follows the name directly
): (det reading: AfterName) {
    out reading := if bracket = Bracket::Angle then (if adjacent? then AfterName::Opens else AfterName::Spaced)
        else AfterName::Ends

    -- After a type's name, a `<` is never a comparison.
    expect never_compared: when bracket = Bracket::Angle, reading != AfterName::Ends
    -- A `(` is not the type's, as in a function's parameter list after a
    -- variant's type.
    expect paren_ends: when bracket = Bracket::Paren, reading = AfterName::Ends
}
```

**The closing `>`.** Fren's lexer has no `>>`, so `Option<Set<Int>>`
ends with two `>`s. Lean lexes `>>` as one token, so the hosted front end
reads the `>` that closes type arguments or type parameters one character
at a time, and `>>` closes two. No type is followed by `=`, so a `>=`
after a type, as in `x: Set<Int>= e` for `x: Set<Int> := e`, is an error
in both front ends; `x: Set<Int>:= e` is `>` and `:=`, as it is in Lean.

## Ordered records

A record with type parameters cannot be declared [`ordered`](Items.md#ordered-declarations)
for now (`F0390`): an ordered record's fields must be of ordered types, and
a type parameter's type is not known until an instance gives it, so
whether `Pair<A, B>` is ordered would depend on its instance. An ordered
enumeration may have type parameters, since it has no payloads, and is
ordered by its variants whatever its arguments.

`lang::ordered_generic` states which records may be declared `ordered`,
from whether one is and how many type parameters it has:

```fren
pub proc ordered_generic(
    ordered?,          -- the record is declared `ordered`
    params: Nat,       -- how many type parameters it has
): (det accepted?) {
    ensure rule: accepted? iff not ordered? or params = 0

    expect plain: when params = 0, accepted?
    expect unordered: when not ordered?, accepted?
    expect generic: when ordered? and params > 0, not accepted?
}
```

## Type parameters

A type parameter is a type only within its declaration, as the type of a
payload or field, or as an argument of an instance there, as in
`Cons(T, List<T>)` or `Some(Pair<A, B>)`. The names of the type
parameters of a declaration are [distinct](Items.md#distinct-names). A type parameter cannot have the name of a built-in type, such
as `Int` or `Set`, or of an item that a path of one segment names where
the declaration is, so that within the declaration, a name always means
one thing (`F0388`). It also keeps the meaning that the solver is given
right: a generic type's parametric datatype declares its parameters with
`par` (see [Meaning](#meaning)), within which a parameter named `Int`
would capture the sort `Int`, so that a payload of type `Int` would mean
the parameter instead.

For now, a type parameter is not an element type, as in `Set<T>`,
`Seq<T>` or `Rel<T, Int>`, and a generic enumeration's payload of its own
type gives it its own parameters, in order, as `List<T>` does within
`List<T>`, rather than other arguments, as in
`enum Nested<T> { Leaf(T), Node(Nested<Pair<T, T>>) }` (`F0387`). Each of
these needs more of the solver or of Lean than an enumeration's parameters
being types. `lang::type_parameter_place` states where a type parameter
is accepted, from where it is written:

```fren
pub mod lang

-- Where a type parameter is written within its declaration: the whole type
-- of a payload or a field; an argument of an instance, other than a
-- recursive one; an argument of the declaration's own type, as it is
-- declared, for a recursive payload; the same, but not as declared; or an
-- element type of a set, relation or sequence.
pub enum ParamPlace { Whole, Argument, OwnParameter, OwnOther, Element }

pub proc type_parameter_place(place: ParamPlace): (det accepted?) {
    use self::ParamPlace::{Argument, Element, OwnOther, OwnParameter, Whole}

    ensure rule: accepted? iff place is Whole | Argument | OwnParameter

    expect not_elements: when place = Element, not accepted?
    expect recursion_uniform: when place = OwnOther, not accepted?
}
```

`lang::recursive_payload` states where a recursive payload writes the
enumeration's own type over what is written: the arguments it is written
with, each one of the enumeration's type parameters or another type, and
whether it is within an argument of an instance, as in `Option<List<T>>`
within `List<T>`. Both front ends read a payload's type alike into these
(`Core.ownArgs`), as `lang::own_type` below states. The type parameters are
three at most here, and the rule is the same for more. It refines `lang::type_parameter_place`, whose place
is `OwnParameter` exactly when the payload is the type with its own type
parameters, in order. Comparing sequences is outside the [decidable
core](Decidability.md), so both opt out:

```fren
pub enum Arg { P0, P1, P2, Other }   -- a type argument, as written: one of the type parameters, or another type

set_option fren.lint.undecidable "allow" in
pub proc recursive_payload(
    params: Seq<Arg>,      -- the enumeration's type parameters, in order: `P0`, `P1`, ..., never `Other`
    args: Seq<Arg>,        -- the arguments that its own type is written with
    nested?,               -- it is within an argument of an instance
): (det accepted?) {
    ensure rule: accepted? iff (not nested? and args = params and not Arg::Other in params)

    expect nested: when nested?, not accepted?
    expect arity: when args.len != params.len, not accepted?
    expect other: when Arg::Other in args, not accepted?
}

set_option fren.lint.undecidable "allow" in
expect recursive_place(params: Seq<lang::Arg>, args: Seq<lang::Arg>, nested?) {
    use lang
    call concrete := recursive_payload(params, args, nested?)
    refines concrete type_parameter_place(
        if not (nested?) and (args) = (params) and not lang::Arg::Other in (params) then lang::ParamPlace::OwnParameter
            else lang::ParamPlace::OwnOther,
    )
}
```

`lang::own_type` states how both front ends classify a payload's or
field's type as it is written, which `lang::recursive_payload` takes as
given. Each front end reads the type into its *segments*
(`Core.ownArgs`, `Core.ownIn`): each segment of a path, in turn, with
markers for the rest, which no segment of a path can be. An instance
`G<A, B>` is `G`'s segments, a marker that opens its type arguments,
`A`'s, a marker that separates them, `B`'s and a marker that closes them;
`Set<T>` and `Seq<T>` are a marker of their own and `T`'s, and
`Rel<A, B>` its marker, `A`'s, a separator of its own and `B`'s.
Subset aliases are resolved to their base types; their invariant
expressions are not type segments. Here a segment that is not a marker is the declaration's own
name, `Own`, or another identifier, `Ident(a)`, which is one of the
declaration's type parameters, `P0`, `P1` or `P2`, or another name,
`Other`. From the segments it states:

- whether the type is the declaration's own type, with type arguments or
  without: its first segment is the own name, and it is that alone or
  followed by the opening of its arguments (`lang::own_whole?`);
- whether it is that type with the declaration's own type parameters, in
  order, as it is declared (`lang::own_written`), which is how a recursive
  payload must write it;
- whether the own name is *nested*: within the type's arguments, if it is
  the own type, or anywhere in it, if it is not, but not within a set's,
  sequence's or relation's element type, that is unless the type is one
  of those (`lang::own_nested?`);
- whether the type is the own name alone, as a newtype's check needs, and
  whether the own name is within an element type, as the check of a
  recursive set needs (`lang::field_type`);
- and, from these, whether a recursive payload is accepted: one that is
  nested never is, and one that is the own type is exactly when it is
  written as declared.

A type whose own name is within an element type, as `Set<List<T>>` in
`List<T>`, is accepted here, and rejected by the check of a recursive set.
The segments may be as many as a type has, and the declaration has at most
three type parameters here: the rule is the same for more. It refines
`lang::type_parameter_place`, whose place is `OwnParameter` for the own
type written as declared, `OwnOther` for any other own type or nested own
name, and `Whole` for a type with neither, which this check accepts
whatever its parameters' places are, since the other places are checked
apart from it:

```fren
-- A segment of a written type, as both front ends read it (`Core.ownArgs`):
-- the declaration's own name; another identifier; the opening, separator and
-- closing of an instance's type arguments; and the markers of a set's,
-- sequence's and relation's element types, with a relation's separator.
pub enum Segment { Own, Ident(Arg), ArgsOpen, ArgsSep, ArgsClose, SetOf, SeqOf, RelOf, RelSep }

-- The declaration's own type, with its type parameters, in order: `G`,
-- `G<P0>`, `G<P0, P1>` or `G<P0, P1, P2>`.
set_option fren.lint.undecidable "allow" in
pub fn own_written(params: Nat): Seq<Segment> :=
    if params = 0 then [Segment::Own]
    else if params = 1 then [
        Segment::Own,
        Segment::ArgsOpen,
        Segment::Ident(Arg::P0),
        Segment::ArgsClose,
    ]
    else if params = 2 then [
        Segment::Own,
        Segment::ArgsOpen,
        Segment::Ident(Arg::P0),
        Segment::ArgsSep,
        Segment::Ident(Arg::P1),
        Segment::ArgsClose,
    ]
    else [
        Segment::Own,
        Segment::ArgsOpen,
        Segment::Ident(Arg::P0),
        Segment::ArgsSep,
        Segment::Ident(Arg::P1),
        Segment::ArgsSep,
        Segment::Ident(Arg::P2),
        Segment::ArgsClose,
    ]

-- The type is the declaration's own type, with type arguments or without.
pub fn own_whole?(segs: Seq<Segment>) := segs != [] and segs[0] = Segment::Own
    and (segs.len = 1 or segs[1] = Segment::ArgsOpen)

-- The own name is within the type's arguments, if it is the own type, or
-- anywhere in it, if not, and the type is not a set, sequence or relation.
set_option fren.lint.undecidable "allow" in
pub fn own_nested?(segs: Seq<Segment>) :=
    not (segs != [] and segs[0] in {Segment::SetOf, Segment::SeqOf, Segment::RelOf})
    and Segment::Own in segs.slice(if own_whole?(segs) then 1 else 0, segs.len)

set_option fren.lint.undecidable "allow" in
pub proc own_type(
    params: Nat,                 -- how many type parameters the declaration has: `P0`, `P1`, ...
    segs: Seq<Segment>,          -- a payload's or field's type, as written
): (det own?, det as_declared?, det nested?, det bare?, det in_element?, det accepted?) {
    use self::Arg::{Other, P0, P1}
    use self::Segment::{ArgsClose, ArgsOpen, ArgsSep, Ident, Own, RelOf, RelSep, SeqOf, SetOf}
    out own? := own_whole?(segs)
    out as_declared? := own? and params <= 3 and segs = own_written(params)
    out nested? := own_nested?(segs)
    out bare? := segs = [Own]
    out in_element? := (SetOf in segs or SeqOf in segs or RelOf in segs or RelSep in segs) and Own in segs

    ensure rule: accepted? iff (not nested? and (not own? or as_declared?))

    expect declared: when params = 1 and segs = [Own, ArgsOpen, Ident(P0), ArgsClose], accepted?
    expect plain: when params = 0 and segs = [Own], bare? and accepted?
    expect swapped: when params = 2 and segs = [Own, ArgsOpen, Ident(P1), ArgsSep, Ident(P0), ArgsClose], not accepted?
    expect other_argument: when params = 1 and segs = [Own, ArgsOpen, Ident(Other), ArgsClose], not accepted?
    expect missing_arguments: when params = 1 and segs = [Own], own? and not accepted?
    expect within_instance: when segs = [
        Ident(Other),
        ArgsOpen,
        Own,
        ArgsOpen,
        Ident(P0),
        ArgsClose,
        ArgsClose,
    ],
        nested? and not accepted?
    expect within_set: when segs = [SetOf, Own, ArgsOpen, Ident(P0), ArgsClose], in_element? and accepted?
    expect unrelated: when not Own in segs, accepted?
}

set_option fren.lint.undecidable "allow" in
expect own_place(params: Nat, segs: Seq<lang::Segment>) {
    use lang
    call concrete := own_type(params, segs)
    expect rule: (concrete.accepted?) iff (if lang::own_nested?((segs)) or (lang::own_whole?((segs)) and not ((params) <= 3 and (segs) = lang::own_written((params))))
        then lang::ParamPlace::OwnOther
        else if lang::own_whole?((segs)) then lang::ParamPlace::OwnParameter
        else lang::ParamPlace::Whole) is lang::ParamPlace::Whole | lang::ParamPlace::Argument | lang::ParamPlace::OwnParameter
}
```

A type argument is the type of a payload or a field once it stands for
its parameter, so it follows their [rules](Items.md#fields-and-payloads):
no abstract type is within it. Nor is it `Nat` (`F0338`, see
`lang::nat_place`).

## Instantiation

Within its declaration, a type parameter is a type of its own, known by its
position among the declaration's parameters, counted from 0. An instance's
payloads and fields have the types declared with its arguments
*instantiated* for the parameters: the `k`th argument for each mention of
parameter `k`, however deeply within an instance or a set, relation or
sequence type it is, and anything else left as it is. So `Some(T)` of an
`Option<Int>` has an `Int`, and `Cons(T, List<T>)` of a `List<Bool>` a
`Bool` and a `List<Bool>`. Instantiating the payloads' types is how each
front end finds the types of a construction's values, a pattern's binders,
a field read and a record update's values, and how both find an
instance's values (see [below](#recursive-unbounded-and-finite-instances)).

`lang::param?` says whether a type is a type parameter, and
`lang::param_index` gives its position. A type's *parts* are the types it
is built from directly: an instance's type arguments, in order, a set's or
sequence's element type, and a relation's two; other types have none.
`lang::parts` gives them, and `lang::with_parts` the type of the same kind
and generic type with other parts in their place:

```fren
pub mod lang

pub fn param?(Ty)                     -- a type parameter, within its declaration
pub fn param_index(Ty): Nat           -- a type parameter's position among its declaration's
pub fn parts(Ty): Seq<Ty>
pub fn with_parts(Ty, Seq<Ty>): Ty
```

`lang::instantiation` states what instantiating a type `ty` with the
arguments `arguments` gives, from what instantiating each of its parts
gives: a parameter is replaced by its argument, if there is one, and any
other type is the same type with its parts instantiated, so that a type
without parts is left as it is:

```fren
pub proc instantiation(
    ty: Ty,
    arguments: Seq<Ty>,
    instantiated: Seq<Ty>,         -- each of the parts of `ty`, instantiated in turn
): (det result: Ty) {
    out result := if param?(ty) then
        (if param_index(ty) < arguments.len then arguments[param_index(ty)] else ty)
        else with_parts(ty, instantiated)

    assume each_part: instantiated.len = parts(ty).len
}
```

## Type arguments

Wherever a type is written, a generic type has exactly as many type
arguments as it has parameters, and any other type has none, so `Option`,
`Option<Int, Int>` and `Int(Bool)` are errors (`F0385`).
`lang::type_arguments` states this, from how many parameters the type has
and how many arguments it is written with:

```fren
pub proc type_arguments(
    params: Int,       -- how many type parameters the type has: none if it is not generic
    args: Int,         -- how many arguments it is written with
): (det accepted?) {
    ensure rule: accepted? iff args = params

    expect plain: when params = 0 and args = 0, accepted?
    expect missing: when params > 0 and args = 0, not accepted?
}
```

`lang::written_type_arguments` states this over what the type's path
names, and the type parameters and arguments as they are written: only an
enumeration or record has type parameters, so a built-in type, a type
parameter, a newtype, an abstract type or a type alias has none. It
refines `lang::type_arguments`:

```fren
-- What the path of a type names: a built-in type, a type parameter, an
-- enumeration or record, or another item.
pub enum Named { Builtin, Parameter, Data, OtherItem }

set_option fren.lint.undecidable "allow" in
pub proc written_type_arguments(
    named: Named,
    params: Seq<Arg>,      -- an enumeration's or record's type parameters, in order
    args: Seq<Arg>,        -- the type arguments, as written
): (det accepted?) {
    ensure rule: accepted? iff args.len = (if named = Named::Data then params.len else 0)

    expect builtin: when named = Named::Builtin and args != [], not accepted?
    expect parameter: when named = Named::Parameter and args != [], not accepted?
}

set_option fren.lint.undecidable "allow" in
expect written_arguments(named: lang::Named, params: Seq<lang::Arg>, args: Seq<lang::Arg>) {
    use lang
    call concrete := written_type_arguments(named, params, args)
    refines concrete type_arguments(
        if (named) = lang::Named::Data then (params).len else 0,
        (args).len,
    )
}
```

An expression never writes type arguments. A variant or record of a
generic type is built as any other, as in `Option::Some(3)`,
`Option::None` or `Pair { fst := 1, snd := true }`, and matched as any
other, and its type arguments are *inferred*:

- **From what is expected.** If a type is [expected](Types.md#checking-and-synthesis)
  of the construction, and that type is an instance of the construction's
  generic type, its arguments are that instance's. So with `x:
  Option<Int>`, `x = Option::None` is accepted.
- **From its payload or fields.** Otherwise, each type parameter takes
  its argument from the first value of the payload, or the first field in
  the order of the declaration, whose declared type mentions the
  parameter, and which [synthesizes](Types.md#checking-and-synthesis) its
  type: the parameter's argument is what stands for it when that value's
  type is matched against the declared type. A `Nat` is widened to an
  `Int` first, since an argument is never `Nat`. So `Option::Some(3)` is
  an `Option<Int>`, and `Pair { fst := 1, snd := "a" }` a `Pair<Int,
  String>`.

A construction with no expected instance, some of whose parameters no
such value gives an argument, has a type that cannot be known, as
`Option::None` alone, `Option::Some({})` and `Option::Some(Option::None)`
(`F0386`). Once its arguments are known, each value of its payload, or
each field, is checked against its declared type, with the arguments for
the parameters, as for any other variant or record. So
`Pair { fst := 1, snd := 2 }` where a `Pair<Int, Bool>` is expected
reports the `2`.

`lang::type_argument_inference` states this for one type parameter of a
construction. `lang::first_giver` gives the position of the first of the
construction's values that synthesizes its type and whose declared type
mentions the parameter, or `-1` if none does, and `lang::widened` a type
with a `Nat` widened to an `Int`:

```fren
pub fn first_giver(Seq<Ty>, Seq<Bool>, Nat): Int
pub fn widened(Ty): Ty

pub proc type_argument_inference(
    declared: Seq<Ty>,             -- the declared types of the construction's values, in order
    synthesizes: Seq<Bool>,        -- which values synthesize their types
    k: Nat,                        -- the type parameter
    expected?,                     -- an instance of the construction's type is expected of it
    expected_arg: Ty,              -- that instance's argument for `k`
    matched?,                      -- matching the first giver's type against its declared type gives `k` an argument
    matched: Ty,                   -- that argument
): (det giver: Int, det known?, det argument: Ty) {
    out giver := first_giver(declared, synthesizes, k)
    out known? := expected? or (giver >= 0 and matched?)
    out argument := if expected? then expected_arg else widened(matched)

    assume as_many: synthesizes.len = declared.len

    expect from_expected: when expected?, known? and argument = expected_arg
    expect no_giver: when not expected? and giver < 0, not known?
}
```

`lang::parameter_matching` states what matching a value's type, `found`,
against its declared type gives a type parameter `k`: the found type itself
where the declared type is `k`, and nothing where it is another parameter.
Otherwise, if the two have the same shape, that is the same kind, the same
generic type and as many parts, it is what matching the first of the
declared type's parts that mentions `k` against the part of the found type
in its place gives, and if they do not, nothing. So matching `Option<Int>`
against `Option<T>` gives `T` the argument `Int`, and matching `Int`
against it gives `T` none, which leaves the construction's type unknown,
and its value a type mismatch. `lang::same_shape?` says whether two types
have the same shape:

```fren
pub fn same_shape?(Ty, Ty)

pub proc parameter_matching(
    declared: Ty,
    found: Ty,
    k: Nat,
    first: Int,                    -- the position of the first of the declared type's parts that mentions `k`, or -1
    part_matched?,                 -- matching the part of `found` there against that part gives `k` an argument
    part_argument: Ty,             -- that argument
): (det matched?, det argument: Ty) {
    out matched? := if param?(declared) then param_index(declared) = k
        else same_shape?(declared, found) and first >= 0 and part_matched?
    out argument := if param?(declared) then found else part_argument

    expect itself: when param?(declared) and param_index(declared) = k, matched? and argument = found
    expect other_shape: when not param?(declared) and not same_shape?(declared, found), not matched?
}
```

Whether a construction synthesizes its type is stated by
[`lang::synthesizes`](Types.md#checking-and-synthesis), whose shape
`Construction` counts the parameters as its parts, and those that a value
that synthesizes its type gives an argument as those that synthesize:
it synthesizes exactly when every parameter is given one.

`lang::construction_synthesis` states this over a construction's values:
for each, the one type parameter that its declared type mentions, or none,
and whether it synthesizes its type. A value's declared type may mention
several parameters, and then gives each of them an argument; the rule is
the same. Here a value's declared type mentions one of the first three
type parameters at most, so a construction of a type with more never
synthesizes its type. It refines
`lang::synthesizes` for the shape `Construction`, whose parts are the
parameters and whose synthesizing parts are those given an argument:

```fren
-- A construction's value: `Gives(p)` if its declared type mentions `p` and it
-- synthesizes its type, `Waits(p)` if it mentions `p` and does not.
pub enum ArgMode { Gives(Arg), Waits(Arg) }

set_option fren.lint.undecidable "allow" in
pub proc construction_synthesis(
    params: Nat,             -- how many type parameters the generic type has: `P0`, `P1`, ...
    values: Seq<ArgMode>,      -- the construction's values, in order
): (det synthesizes?) {
    use self::Arg::{P0, P1, P2}

    ensure rule: synthesizes? iff (params <= 3 and (params < 1 or ArgMode::Gives(P0) in values)
        and (params < 2 or ArgMode::Gives(P1) in values)
        and (params < 3 or ArgMode::Gives(P2) in values))

    expect waiting: when params = 1 and not ArgMode::Gives(P0) in values, not synthesizes?
    expect plain: when params = 0, synthesizes?
}

set_option fren.lint.undecidable "allow" in
expect construction_shape(params: Nat, values: Seq<lang::ArgMode>) {
    use lang
    assume spec_counted: ((if (params) >= 1 and lang::ArgMode::Gives(lang::Arg::P0) in (values) then 1 else 0)
        + (if (params) >= 2 and lang::ArgMode::Gives(lang::Arg::P1) in (values) then 1 else 0)
        + (if (params) >= 3 and lang::ArgMode::Gives(lang::Arg::P2) in (values) then 1 else 0)) <= (params)
    assume spec_pair: when (lang::Shape::Construction) = lang::Shape::Pair, (params) = 2
    call concrete := construction_synthesis(params, values)
    refines concrete synthesizes(
        lang::Shape::Construction,
        (params),
        (if (params) >= 1 and lang::ArgMode::Gives(lang::Arg::P0) in (values) then 1 else 0)
            + (if (params) >= 2 and lang::ArgMode::Gives(lang::Arg::P1) in (values) then 1 else 0)
            + (if (params) >= 3 and lang::ArgMode::Gives(lang::Arg::P2) in (values) then 1 else 0),
    )
}
```

Each front end elaborates a construction's values in the same order
(`Core.inferConstruction`), so that both infer the same arguments, check
the same values against the same types and report the same first error.
The values are elaborated in order, except that one that *waits* is
elaborated after all the others, in order: a value waits if it does not
synthesize its type, and its declared type mentions a type parameter that
has no argument yet, that is no instance is expected of the construction,
and no value before it that synthesizes its type mentions the parameter.
A value that waits is then checked against its declared type with the
arguments that the others gave. A type parameter ends with an argument if
an instance is expected, or if a value that synthesizes its type mentions
it, and otherwise the construction's type arguments are reported unknown
(`F0386`).

`lang::construction_order` states this over a construction's values,
`lang::ArgMode`s as for `lang::construction_synthesis`, each of whose
declared type mentions one of the generic type's parameters or none, with
the order in which they are elaborated, by their positions, which type
parameters end with an argument, and whether the arguments are reported
unknown. Here a construction has three values at most, of a type with at
most three type parameters, and every value has a type once elaborated, as
an error in one is reported in it. `lang::waits?` says whether the value
at a position waits:

```fren
-- Whether a value's declared type mentions only the first `params` type
-- parameters, or none.
pub fn within?(a: Arg, params: Nat) := match a {
    Arg::P0 => params >= 1,
    Arg::P1 => params >= 2,
    Arg::P2 => params >= 3,
    Arg::Other => true,
}

set_option fren.lint.undecidable "allow" in
pub fn waits?(values: Seq<ArgMode>, expected?, j: Int) := not expected? and 0 <= j < values.len
    and match values[j] {
        ArgMode::Waits(a) => a != Arg::Other and not ArgMode::Gives(a) in values.slice(0, j),
        ArgMode::Gives(_) => false,
    }

-- Value `j`'s position, if it is among the values and waits, or does not,
-- as `waiting?` says.
set_option fren.lint.undecidable "allow" in
pub fn position_if(values: Seq<ArgMode>, expected?, waiting?, j: Int): Seq<Int> :=
    if 0 <= j < values.len and waits?(values, expected?, j) = waiting? then [j] else []

set_option fren.lint.undecidable "allow" in
pub proc construction_order(
    params: Nat,                   -- how many type parameters the generic type has: `P0`, `P1`, ...
    values: Seq<ArgMode>,            -- the construction's values, in order
    expected?,                     -- an instance of the construction's type is expected of it
): (det order: Seq<Int>, det given: Seq<Bool>, det unknown?) {
    use self::Arg::{P0, P1, P2}
    use self::ArgMode::{Gives, Waits}
    -- The values' positions, in the order in which they are elaborated:
    -- those that do not wait, in order, then those that do.
    out order :=
        position_if(values, expected?, false, 0) ++ position_if(values, expected?, false, 1)
        ++ position_if(values, expected?, false, 2) ++ position_if(values, expected?, true, 0)
        ++ position_if(values, expected?, true, 1) ++ position_if(values, expected?, true, 2)
    -- For each type parameter, whether it ends with an argument.
    out given := (if params >= 1 then [expected? or Gives(P0) in values] else [])
        ++ (if params >= 2 then [expected? or Gives(P1) in values] else [])
        ++ (if params >= 3 then [expected? or Gives(P2) in values] else [])
    out unknown? := false in given

    assume few: values.len <= 3 and params <= 3
    assume own_parameters: forall (a: Arg), when Gives(a) in values or Waits(a) in values, within?(a, params)

    expect each_once: order.len = values.len
    expect expected_in_order: when expected? and values.len = 3, order = [0, 1, 2] and not unknown?
    expect waiting: when params = 1 and not expected? and values = [Waits(P0), Gives(P0)],
        order = [1, 0] and not unknown?
    expect given_before: when params = 1 and not expected? and values = [Gives(P0), Waits(P0)], order = [0, 1]
    expect waiting_in_order: when params = 2 and not expected? and values = [Waits(P0), Waits(P1), Gives(P0)],
        order = [2, 0, 1] and given = [true, false] and unknown?
    expect nothing_gives: when params = 1 and not expected? and values = [Waits(P0)], unknown?
}
```

A pattern of a variant of a generic type matches values of every instance
of it, and its payload's patterns, binders included, have the payload's
types with the scrutinee's arguments for the parameters, so in `match x {
Option::Some(n) => n > 0, Option::None => false }` with `x: Option<Int>`,
`n` is an `Int`. So does a field read, as `p.fst` of a `Pair<Int, Bool>`
is an `Int`, and a record update, whose values are checked against the
fields' types with the record's arguments.

## Printing

A type prints as it is written, with its arguments, as in `Option<Int>`
and `Set<Pair<Int, Bool>>`, in every message, note and witness, the same
in both front ends. A value of a generic type prints as any other value of
an enumeration or record, without type arguments, as in `Option::Some(3)`.

## Subset types as type arguments

A type argument may be a [subset type](SubsetTypes.md), as in
`Option<Byte>` with `type Byte = n: Int where range: n is 0..=255`,
or a type whose
values bring a constraint, as `Option<Byte>` is in `Pair<Option<Byte>,
Int>`. A type argument stands for its parameter with its invariants, so a
payload or field whose declared type is the parameter has the argument's
type as declared:

- A value of the instance brings the constraints of its payloads and
  fields with the arguments' types, as a value of any enumeration or record
  brings those of its own (see [Subset types](SubsetTypes.md#static-types-assumptions-and-obligations)): a value `x` of
  `Option<Byte>` brings that when `x` is `Option::Some(b)`, `b` is in
  `0..=255`. A constraint of an element type within an argument, as in
  `Option<Set<Digit>>` with `type Digit = n: Int where range: n is 0..=9`, quantifies over the elements, as it does
  anywhere (`lang::subset_place`).
- A value given where an instance is declared has the obligation
  (`lang::obligation`) of each payload or field whose declared type
  mentions a type parameter, with the arguments, guarded by its variant:
  the value was built from values of the parameters' types, which have no
  invariants, so nothing else ensures them. `Option::Some(300)` given where an
  `Option<Byte>` is declared is an error (`F0661`), as `300` is where a
  `Byte` is. A payload or field whose declared type mentions no parameter
  has its own obligation where its value is given, as in any enumeration or
  record.
- A quantifier ranges over the values of the instance that meet its
  constraint (`lang::pattern_finite`): with `type Small = n: Int where range: n is 0..=2`, `forall (o: Option<Small>)`
  ranges over `Option::None` and three `Option::Some`s.

A type argument of a recursive enumeration whose values bring a
constraint is an error (`F0389`), for now: the constraint would hold of
every payload, at every depth, which the constraints of a recursive
enumeration's payloads, brought where each is read, do not say for a type
parameter. So `List<Digit>` and `List<Option<Byte>>` are errors,
and `List<Option<Int>>` is not. This is stricter than for a recursive
enumeration that is not generic, whose payload of a subset type is
allowed, under the [`undecidable` lint](../Lint/Decidability.md#undecidable-constructs)
(see [Subset types](SubsetTypes.md#static-types-assumptions-and-obligations)). It reaches records too: with
`struct R { b: Byte }`, `List<R>` is an error, since a value of `R` brings
that its field is in range, though `R` itself is not a subset type. It
reaches through instances too, once their arguments stand for their
parameters: with `enum Wrap<T> { W(List<T>) }`, `Wrap<Byte>` is an error,
and so is `S<Byte>`, with `struct S<T> { s: Set<List<T>> }`, through a
set's, sequence's or relation's element types. A
recursive generic enumeration's payload of a declared subset type that
mentions no parameter, as `Digit` in
`enum Tree<T> { Leaf, Node(Digit, T, Tree<T>) }`, brings its
constraint where it is read, as for any recursive enumeration.

A subset type's base type may be an instance, as in
`type Present = o: Option<Int> where present: o is Option::Some(_)`, whose
invariant's pattern is a pattern of the instance (see [Patterns](Patterns.md)).

## Recursive, unbounded and finite instances

An instance's payloads and fields have the types declared, with the
instance's arguments for the parameters, and it is
[recursive, unbounded](Types.md#recursive-and-unbounded-types) or
[finite](Types.md#finite-types) by those types, as any enumeration or
record is by its own. So `Option<Int>` is bounded and `Option<String>`
unbounded, every instance of `List` is recursive and so unbounded, and
`Option<Bool>` is finite, so that a [quantifier](Quantifiers.md) over it
is expanded into its instances, while one over `Option<Int>`, which is
not, is outside the [decidable core](Decidability.md) and given to the
solver. Since every parameter of `Option` and
`Pair` is a payload's or field's type, an instance of either is finite
exactly when its arguments are. Whether an enumeration is
[well founded](Items.md#fields-and-payloads) does not depend on its
arguments, since a payload of its own type is one whatever they are.

`lang::instance_values` states this for the three generic types of this
chapter's examples, declared as above, `Option` as the prelude declares it:

```text
enum Option<T> { None, Some(T) }
struct Pair<A, B> { fst: A, snd: B }
enum List<T> { Nil, Cons(T, List<T>) }
```

`lang::instance_values` states how many values a quantifier ranges over
in their instances, from how many it ranges over in the arguments, where
`-1` means it ranges over none. An `Option` has one more value than its
argument, a `Pair` is finite exactly when both its arguments are, and a
`List` never is:

```fren
-- A `List`'s count is the same whatever its argument's, as it should be.
set_option fren.lint.constant_output "allow" in
pub proc instance_values(
    a: Int,                        -- the values of the first argument, or -1
    b: Int,                        -- of the second, for `Pair`
): (det option: Int, det pair_finite?, det list: Int) {
    out option := if a >= 0 then a + 1 else -1
    out pair_finite? := a >= 0 and b >= 0
    out list := -1

    assume counts: a >= -1 and b >= -1

    expect option_finite: option >= 0 iff a >= 0
    expect option_bool: when a = 2, option = 3
}
```

## Meaning

A generic type means one type for each of its instances, without a copy of
its declaration for each: each front end gives the solver one SMT-LIB 2.6
*parametric datatype* for it, as in
`(declare-datatypes ((|List| 1)) ((par (|T|) ((List~Nil) (List~Cons (|List::Cons::0| |T|) (|List::Cons::1| (|List| |T|)))))))`,
and each instance is a sort application, as `(|List| Int)`. Both front
ends give the same declarations, up to the names of their symbols, which
each front end writes its own way: one parametric datatype for each
generic type, with the same constructors and selectors, and the same sort
applications, so that they cannot differ in what the solver decides. The Lean-hosted front end declares a generic type as a
Lean inductive type with a parameter of type `Type` for each type
parameter (see [Generated Lean](../Generated.md#generic-types)), which
lean-smt gives the solver as a parametric datatype.

`lang::smt_encoding` states what the `fren` command gives the solver for
the examples above, from the sorts of the arguments `a` and `b`, with
`Option` a user's, declared `Option!` at the root module, rather than the
[prelude's](Prelude.md#meaning), whose symbols are lean-smt's. A type's
symbol is its path between `|`s, or after `::` if its path is the name of
one of the Lean types that the prelude's types are, as `Option` is, and a payload's selector's or a field's
is named after the variant or field, as for any enumeration or record. A
constructor's symbol is its path with `~` for `::`, and a record's ends in
`~`: a constructor of a parametric datatype is qualified by its sort,
`(as List~Nil (|List| Int))`, and cvc5 finds a qualified constructor
only by a symbol without `|`s, which `~` keeps apart from every
variable's. An instance is its generic type's symbol applied to its
arguments' sorts, and every instance of a generic type has the one
declaration, whatever its arguments:

```fren
-- The declarations are the same whatever the arguments are, as they should
-- be: one for every instance.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.constant_output "allow" in
pub proc smt_encoding(
    a: String,                     -- the sort of the first argument
    b: String,                     -- of the second, for `Pair`
): (
    det option_sort: String,
    det pair_sort: String,
    det option_declaration: String,
    det pair_declaration: String,
    det list_declaration: String,
) {
    out option_sort := "(|::Option| " ++ a ++ ")"
    out pair_sort := "(|Pair| " ++ a ++ " " ++ b ++ ")"
    out option_declaration :=
        "(declare-datatypes ((|::Option| 1)) ((par (|T|) ((Option~None) (Option~Some (|Option::Some::0| |T|))))))\n"
    out pair_declaration :=
        "(declare-datatypes ((|Pair| 2)) ((par (|A| |B|) ((Pair~ (|Pair::fst| |A|) (|Pair::snd| |B|))))))\n"
    out list_declaration :=
        "(declare-datatypes ((|List| 1)) ((par (|T|) ((List~Nil) (List~Cons (|List::Cons::0| |T|) (|List::Cons::1| (|List| |T|)))))))\n"
}
```
