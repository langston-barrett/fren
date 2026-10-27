# Items

A spec is a sequence of items. Each item is a Lean command, so in a Lean file
items can be mixed with Lean code.

```
item := module | use | enumeration | record | abstract-type | type-alias | function | constant
      | component | expectation | check | claim | lint-setting | lean-item
```

Items are processed in order: an item must be declared before it is used,
including by a `use` declaration. Within a module, the names of items and
of `use`-imported names must be unique. `lang::declared_before` states the
order, over the items of a file and its imports, in order, and the
positions of the item that a path names and of the item it is written in:

```fren
pub mod lang

pub type ItemName

pub comp declared_before {
    in items: Seq<ItemName>      -- the items of the file and its imports, in order
    in used: ItemName            -- the item a path names
    in user: ItemName            -- the item the path is written in
    in k_used: Nat               -- the position of `used` in `items`
    in k_user: Nat               -- the position of `user`

    assume positions: k_used < items.len and items[k_used] = used
        and k_user < items.len and items[k_user] = user
    assume distinct: when used = user, k_used = k_user
    pub det out accepted?

    ensure rule: accepted? iff (used = user or k_used < k_user)

    expect self_reference: when used = user, accepted?
    -- The first item can be used by the second, and not the other way.
    expect first_used: when used != user and k_used = 0 and k_user = 1, accepted?
    expect second_unused: when used != user and k_used = 1 and k_user = 0, not accepted?
}
```

`used = user` is a recursive enumeration naming itself. Self-reference by
any other item is rejected elsewhere: a component instantiating itself
([Instances](Instances.md)), or a constant mentioning itself
([constants](#constants)).

## Modules

```
module := ["pub"] "mod" path
```

`mod a::b` makes `a::b` the current module for the items that follow. See
[Modules and visibility](Modules.md).

## `use` declarations

```
use := "use" path ["::*" | "::{" path ("," path)* [","] "}"]
```

`use` brings an item, several items, or all variants of an enumeration,
into scope in the current module. See [Modules and visibility](Modules.md#use-declarations).

## Enumerations

```
enumeration   := ["pub"] ["ordered"] "enum" declared-type "{" variant ("," variant)* [","] "}"
variant       := IDENT ["(" type ("," type)* ")"]
declared-type := IDENT | IDENT"(" IDENT ("," IDENT)* ")"
```

`enum E { A, B }` declares the enumeration `E` with the variants `A` and
`B`. An enumeration has at least one variant, and its variants must have
distinct names. Variants live in their enumeration: they are written `E::A`,
or `A` once brought into scope by `use` (see [Modules and
visibility](Modules.md#use-declarations)), so a variant may share its name
with an item.

A variant may carry a *payload*: values of the types in parentheses, as
in `enum Shape { Circle(Int), Rect(Int, Int), Empty }`. A variant with a
payload is [constructed](Expressions.md#variants-with-payloads) by
applying it to values, as in `Shape::Circle(2)`, and its payload is read
by a [`match`](Expressions.md#matches). The payload's values have types
but no names. A payload may have the type of its own enumeration, which
makes the enumeration [recursive](Types.md#recursive-and-unbounded-types),
as in `enum List { Nil, Cons(Int, List) }`; this is the one exception to
an item being declared before it is used. An enumeration with type
parameters, as `enum Option<T> { None, Some(T) }`, is
[generic](Generics.md).

An enumeration declared with the modifier `ordered`, after `pub` if it
has both, is *ordered*: its variants are ordered as they are declared, so
that with `pub ordered enum Severity { Silent, Info, Warning, Error }`,
`Silent < Info < Warning < Error`. The
[orderings](Expressions.md#operators) `<`, `<=`, `>` and `>=`, their
[chains](Expressions.md#chained-comparisons), and the
[methods](Expressions.md#methods) `min` and `max` apply to its values, as
they do to `Int`s. Comparing values of an enumeration that is not ordered
is an error, whose message says to declare it `ordered`: the order in
which a plain enumeration's variants are listed is not part of its
meaning. For now, only an enumeration without payloads may be ordered (see
[Ordered declarations](#ordered-declarations)).

`lang::enumeration_order` states the laws of the order, on an example: it
is the order of declaration, and it is total:

```fren
pub ordered enum Level { Low, Middle, High }

set_option fren.lint.unnecessary_min_or_max "allow" in
set_option fren.evidence "enumerated" in
pub comp enumeration_order {
    use self::Level::{High, Low, Middle}
    in a: Level
    in b: Level
    in c: Level

    expect declared: when a = Middle, Low < a < High
    expect bounded: Low <= a <= High
    expect total: a <= b or b <= a
    expect asymmetric: not (a < b and b < a)
    expect transitive: when a < b < c, a < c
    expect antisymmetric: when a <= b <= a, a = b
    expect min_below: a.min(b) <= a and a.min(b) <= b and (a.min(b) = a or a.min(b) = b)
    expect max_above: a.max(b) >= a and a.max(b) >= b and (a.max(b) = a or a.max(b) = b)
    expect clamped: a.min(Middle) = (if a = High then Middle else a) and a.max(High) = High
}
```

## Records

```
record := ["pub"] ["ordered"] "struct" declared-type "{" field ("," field)* [","] "}"
        | ["pub"] ["ordered"] "struct" IDENT "(" [type ("," type)*] ")"
field  := IDENT [":" type]
```

`struct Point { x: Int, y: Int }` declares the record `Point`, whose
values each have an `Int` for `x` and one for `y`. A record has at least
one field, and its fields must have distinct names. A field follows the
[Boolean names](Types.md#boolean-names) rule: `ready?` is a `Bool` field,
and any other field has its type written. A record is
[built](Expressions.md#records) as `Point { x := 1, y := 2 }`, its
fields are read as `p.x`, and `{ p with x := 1 }` is `p` with `1` for
`x` (see [Record updates](Expressions.md#record-updates)). Its fields are
visible wherever the record is.

A record's field cannot have the record's own type: a record has only one
way to build a value, so each value would contain another without end, and
the record would have no values. So records are never recursive
themselves, though a field may have an [unbounded
type](Types.md#recursive-and-unbounded-types).

A record with type parameters, as `struct Pair<A, B> { fst: A, snd: B }`,
is [generic](Generics.md); it cannot be declared `ordered` (`F0390`). A
record declared `ordered`, as `ordered struct Version { major: Nat,
minor: Nat }`, orders its values by their fields (see [Ordered
declarations](#ordered-declarations)).

A record whose one field has no name, written `struct Ms(Int)`, is a
[newtype](#newtypes).

## Newtypes

```
record := ... | ["pub"] ["ordered"] "struct" IDENT "(" [type ("," type)*] ")"
```

`struct Ms(Int)` declares the *newtype* `Ms`: a record with exactly one
field, which has no name, of the type in parentheses, its *underlying
type*. A newtype has the values of its underlying type, but is a type
distinct from every other, its underlying type included, so that values
that mean different things, such as times and sizes, are not mixed by
mistake:

```text
pub struct Ms(Int)
pub struct Bytes(Int)

comp timer {
    in elapsed: Ms
    in size: Bytes
    expect bad: elapsed < size   -- error: cannot compare `Ms` with `Bytes`
}
```

A newtype's name is both a type and its constructor: `Ms(5)` builds a
value, and `x.0` reads its field (see
[Newtypes](Expressions.md#newtypes), which also says which operators a
newtype has). A newtype is a record, so its field follows the rules of
a record's [fields](#fields-and-payloads): its type has no abstract type
within it and it does not have the newtype as an element type, and is not
the newtype itself. It may be a `Nat`, or a [pattern
type](Types.md#pattern-types), as in `struct Byte(Int is 0..=255)`: a value
of it is then in range wherever it is read, and `Byte(e)` has the
obligation that `e` is. Like any type, a newtype is
[unbounded](Types.md#recursive-and-unbounded-types) exactly when its
underlying type is. A newtype declared `ordered`, as `ordered struct
Seconds(Nat)`, is ordered as its underlying type is (see [Ordered
declarations](#ordered-declarations)); one declared without it is not
ordered, even when its underlying type is.

`lang::newtype` states which newtypes are accepted, from how many types
its parentheses hold and whether its one field's type is accepted as a
record's field's, and when it is unbounded, by the closure of the
constituent relation (`lang::type_facts`). Its one constituent is its
underlying type, which is not built from it:

```fren
pub mod lang

set_option fren.lint.undecidable "allow" in
pub comp newtype {
    in n_fields: Nat                                 -- the types in its parentheses
    in field_accepted?                               -- the first's type is accepted as a record's field's (`field_type`)
    in ty: DeclaredTy                                -- the newtype
    in underlying: DeclaredTy                        -- its underlying type
    in constituents: Rel<DeclaredTy, DeclaredTy>     -- (t, u): t has a field, payload or element of type u

    assume record: declared_kind(ty) = ValueType::RecordTy
    assume one_constituent: constituents.image({ty}) = {underlying}
    assume not_recursive: not (ty, ty) in constituents.closure
    pub det out accepted?
    pub det out unbounded?
    inst facts: type_facts { ty, constituents }

    ensure rule: accepted? iff (n_fields = 1 and field_accepted?)
    ensure bounds: unbounded? iff facts.unbounded?

    expect one_field: when n_fields != 1, not accepted?
    expect as_records: when not field_accepted?, not accepted?
    expect growing_underlying: when former(declared_kind(underlying)).growing?, unbounded?
    expect bounded_underlying: when constituents.image({underlying}) = {} and not former(declared_kind(underlying)).growing?,
        not unbounded?
}
```

Fren does not yet have a newtype over a type parameter, as in `struct
Id<T>(T)`.

## Ordered declarations

The modifier `ordered`, written after `pub` if the item has both, makes an
enumeration, a record or a newtype an [ordered
type](Types.md#ordered-types), whose values the
[orderings](Expressions.md#operators) `<`, `<=`, `>` and `>=`, their
[chains](Expressions.md#chained-comparisons), and the
[methods](Expressions.md#methods) `min` and `max` compare, as Rust's
`#[derive(PartialOrd, Ord)]` does. It is opt-in: an enumeration, record or
newtype declared without it has no orderings, whatever its fields' types,
and comparing its values is an error that says to declare it `ordered`
(`F0352`). `ordered` on any other item is an error (`F0130`).

An ordered enumeration orders its variants as they are declared. An
ordered record orders its values *lexicographically*, by its fields in the
order declared: `a < b` exactly when, at the first field where `a` and `b`
differ, `a`'s is less than `b`'s, each compared as its own type is. So with
`ordered struct Version { major: Nat, minor: Nat }`, `Version { major := 1,
minor := 9 } < Version { major := 2, minor := 0 }`. A newtype is the
record of one field, so an ordered newtype orders its values as their
fields are ordered: with `ordered struct Seconds(Nat)`, `Seconds(1) <
Seconds(2)`. Each comparison unfolds, field by field, into comparisons of
`Int`s, `String`s and variants' positions, joined by `and` and `or`, so it
is quantifier-free, and is in the [decidable
core](Decidability.md#strings) exactly when the comparisons that it
unfolds into are: one whose type has a `String` within it is a comparison
of strings.

So that the order is defined, every field of an ordered record, and the
underlying type of an ordered newtype, has an ordered type, and a
declaration whose field does not is an error that names the field
(`F0371`). For now, only an enumeration without payloads may be ordered
(`F0353`): ordering values with payloads, by their variants and then by
their payloads, is left for later. So no ordered declaration is recursive,
records never being so, and the unfolding of a comparison ends. The error
names the first field whose type is not ordered. `lang::ordered_declaration`
states which declarations are accepted, from how many of an enumeration's
variants have a payload, and from the types of a record's fields, or a
newtype's underlying type, each ordered or not by `lang::ordered_in?` (see
[Ordered types](Types.md#ordered-types)). `k` stands for any position, so
`reported` and `earliest` hold of every field:

```fren
pub mod lang

pub enum Declaration { Enumeration, Record, Newtype }

set_option fren.lint.undecidable "allow" in
pub comp ordered_declaration {
    use self::Declaration::Enumeration
    in declaration: Declaration
    in ordered?                       -- declared with `ordered`
    in n_payloads: Nat                -- for an enumeration: its variants with a payload
    in fields: Seq<Ty>                -- a record's fields' types, in order, or a newtype's underlying type, without patterns
    in ordered_items: Set<TypeName>   -- the enumerations, records and newtypes declared `ordered`
    in k: Int                         -- any position among the fields

    assume enumerations_without_fields: when declaration = Enumeration, fields = []
    assume structs_without_payloads: when declaration != Enumeration, n_payloads = 0
    pub out first_unordered: Int      -- the field reported: the first whose type is not ordered, `-1` if none is
    pub out accepted?

    ensure in_range: -1 <= first_unordered < fields.len
    ensure reported: when k = first_unordered and k != -1,
        not ordered_in?(kind(fields[k]), type_name(fields[k]), ordered_items)
    ensure earliest: when 0 <= k < fields.len and not ordered_in?(kind(fields[k]), type_name(fields[k]), ordered_items), 0 <= first_unordered <= k
    ensure rule: accepted? iff (not ordered? or (n_payloads = 0 and first_unordered = -1))

    expect plain: when not ordered?, accepted?
    expect no_payloads: when ordered? and n_payloads > 0, not accepted?
    expect ordered_fields: when ordered? and 0 <= k < fields.len and not ordered_in?(kind(fields[k]), type_name(fields[k]), ordered_items),
        not accepted?
}
```

How two values of an ordered type compare is planned from the type, and
a record's plan compares its fields lexicographically: see [Orderings of
ordered types](Expressions.md#orderings-of-ordered-types).

## Distinct names

The names of a list of declarations are distinct: the variants of an
enumeration, the fields of a record, the [type
parameters](Generics.md#type-parameters) of either, the parameters and contract clauses
of a function, which share one namespace,
the variables, instances and constraints of a component, which share one
namespace, and the binders of a global expectation, of a pattern or of a
[quantifier](Quantifiers.md#names), across all of its binders. A
pattern's `_` declares no name. A name declared again is an error,
reported where it is declared again, in the order the declarations are
written, whatever their kinds. In every list, only the first such name is
reported, and the rest of its item is not checked, so a component with two
repeated names and an unknown type reports the first repeat alone. The
names of a component's members, of a function's parameters and of binders
are compared without their `!` of [shadowing](Components.md#shadowing), so
`in x: Int` and `in x!: Int` declare the same name, and so do `in x: Int`
and `ensure x!: true`, even though a constraint never shadows. The names of
variants and fields are compared as written: neither ever shadows, and a
`!` on one is an error of its own, and so is one on a type parameter.
`lang::distinct_names` states this, from how many names a list declares
and the set of them:

```fren
pub mod lang

pub type DeclaredName

pub comp distinct_names {
    in count: Int                  -- how many names the list declares
    in names: Set<DeclaredName>    -- the names it declares

    assume counted: names.card <= count
    pub det out accepted?

    ensure rule: accepted? iff names.card = count

    expect repeated: when names.card < count, not accepted?
    expect empty: when count = 0, accepted?
}
```

Each name in an item must be a single segment, except where an expression
reads an instance's variable, a value's field or a method with `.`. This
is checked as the item is parsed, and a name is reported with its `!` if
it has one.

An item's problems are reported in this order, and only the first is
reported:

1. Its [lexical](Lexical.md) problems, wherever they are in the item: an
   identifier or integer literal that is not Fren's, such as `xα`, or a
   prefix `!`.
2. Its problems found as it is parsed, in source order: a name that is not
   a single segment, an input's definition (`in x: Int := 3`), a member's
   `set_option` of an option other than `fren.evidence`, and an operator
   of another language, `==`, `&&`, `||` or `|`.
3. Everything else about it.

So `A(x.y)` reports `x.y`, even in a pattern with the wrong number of
binders or in an or-pattern, but `in s.t: S`, `in a: Int := 3` or
`ensure q: x == 1` before it is reported instead, and so is `!x?` anywhere in
the item.

## Fields and payloads

A field or a payload may have any type in which no abstract type occurs,
including a [pattern type](Types.md#pattern-types) and a `Nat`, but not a
`Nat` within an element type, nor as a payload of a recursive enumeration
(see [Natural numbers](Types.md#natural-numbers)): the values of a record or
enumeration are fully described by the spec, and `Set<Name>` is as
abstract as `Name`. Nor may the item being declared
occur within a set's element type, as in `enum Tree { Node(Set<Tree>) }`:
a set is a value up to its members' order, and a type cannot be built from
sets of itself. `lang::field_type` states which types are accepted, from
the kind of the type, whether an abstract type or the item being declared
occurs within it, and whether it is a variant's payload rather than a
record's field:

```fren
pub mod lang

set_option fren.evidence "enumerated" in
pub comp field_type {
    in kind!: ValueType   -- the kind of the field's or payload's type
    in abstract_within?  -- an abstract type is the type, or a set's element type within it
    in own?              -- the type is the item being declared
    in own_in_set?       -- the item being declared is a set's element type within the type
    in payload?          -- a variant's payload, rather than a record's field

    assume own_enum: when own? and payload?, kind = ValueType::EnumTy
    assume own_record: when own? and not payload?, kind = ValueType::RecordTy
    assume abstract_kind: when kind = ValueType::AbstractTy, abstract_within?
    assume in_set: when own_in_set?, kind = ValueType::SetTy and not own?
    pub det out accepted?

    ensure rule: accepted? iff (not abstract_within? and not own_in_set? and (payload? or not own?))

    expect no_abstract_fields: when kind = ValueType::AbstractTy, not accepted?
    expect records_not_recursive: when own? and not payload?, not accepted?
    expect not_through_sets: when own_in_set?, not accepted?
}
```

A [newtype](#newtypes)'s field is a record's field, so no abstract type is
within it either. Its type may be a [pattern type](Types.md#pattern-types),
as any field's may:

```fren
set_option fren.lint.undecidable "allow" in
expect newtype_not_abstract: forall (n: newtype) (f: field_type),
    when n.n_fields = 1 and (n.field_accepted? iff f.accepted?) and f.abstract_within? and not f.payload?,
    not n.accepted?
```

Every value of a recursive enumeration is built from finitely many
variants, so the enumeration needs at least one variant none of whose
payloads has a type built from the enumeration: `enum Stream { More(Int,
Stream) }` has no values, and is an error. A type is built from the
enumeration when it is the enumeration, or when the closure of the
constituent relation reaches the enumeration from it (see
`lang::built_from`). `lang::well_founded` states this, from the variants and the
types of their payloads:

```fren
pub type VariantName

set_option fren.lint.undecidable "allow" in
pub comp well_founded {
    in ty: DeclaredTy                                -- the enumeration
    in constituents: Rel<DeclaredTy, DeclaredTy>     -- (t, u): t has a field, payload or element of type u
    in variants: Set<VariantName>
    in payloads: Rel<VariantName, DeclaredTy>        -- (v, u): a payload of the variant `v` has the type `u`

    assume some_variant: variants != {}
    assume among: payloads.domain subset variants
    pub det out accepted?

    ensure rule: accepted? iff (exists (v: VariantName), v in variants
        and (forall (u: DeclaredTy), when u in payloads.image({v}), not ty in built_from(u, constituents)))

    expect no_payloads: when payloads = {}, accepted?
    expect plain_enumerations: when constituents = {} and not ty in payloads.range, accepted?
}
```

## Abstract types

```
abstract-type := ["pub"] "type" IDENT
```

`type Name` declares the [abstract type](Types.md#abstract-types) `Name`.
Its values are not described: all that is known of them is that there is
at least one, and whether two of them are equal.

## Type aliases

```
type-alias := ["pub"] "type" IDENT ":=" type
```

`type Byte := Int is 0..=255` declares the *type alias* `Byte`, which
names the type after `:=`, as a constant names a value: wherever `Byte` is
written as a type, it means `Int is 0..=255`. An alias is not a new type:
`Byte` and `Int is 0..=255` are the same type, both widen to `Int`, and a
`Byte` is accepted wherever an `Int is 0..=255` is (see [Pattern
types](Types.md#pattern-types)). A type that is distinct from the one it is
made from is a [newtype](#newtypes). Without `:=`, `type Name` still
declares an abstract type.

An alias names any type, most often a pattern type, so that it is written
once and used everywhere: `type Port := Int is 1..=65535`, `type Loud :=
Severity is Severity::Warning | Severity::Error`. Like any item, it is
declared before it is used, so an alias is never recursive: its type
mentions only types declared before it. It is a type and nothing else: a
path that names an alias is not a record for a record literal, nor an
enumeration for its variants. Its name follows the rules of a type's, and
like any other item, it is visible according to `pub`, and can be brought
into scope with `use`. A pattern on an alias of a pattern type is an error,
since pattern types are not nested (`F0369`).

## Functions

```
function := ["pub"] "fn" declared-type "(" type ("," type)* ")" [":" type]
          | ["pub"] "fn" declared-type "(" variable ("," variable)* ")" [":" type] [":=" top] clause+
          | ["pub"] "fn" declared-type "(" variable ("," variable)* ")" [":" type] ":=" top
clause   := ("assume" | "ensure") IDENT ":" top
```

`fn arity(Name): Int` declares the function `arity`, from values of type
`Name` to values of type `Int`. A function has at least one parameter, and
its parameters and result may have any type, including records and
enumerations with payloads. As for a variable, the result
type of a function whose name ends in `?` is `Bool`, and need not be
written, and any other function must have its result type written (see
[Boolean names](Types.md#boolean-names)). The types are checked in the
order they are written, so the parameters come before the result:
`fn f(Nope): Gone` reports `Nope`.

A function may have type parameters, as in `fn unwrap_or<T>(o: Option<T>,
d: T): T := ...`, which makes it [generic](GenericFunctions.md), and a
defined function's parameter may be a function, as in `fn twice(f: fn(Int)
-> Int, x: Int): Int := f(f(x))`, which makes it
[higher-order](HigherOrder.md); the rest of this section is about
functions without them.

A function written with `:= e` is *defined*, and any other is
*uninterpreted*. Either may have a [contract](#contracts): the clauses
after its signature, and after its body if it has one.

`exactly_one?` and `at_most_one?` are built-in functions, the
[cardinality operators](Expressions.md#cardinality), and no function may
be declared with either name, just as no type may be declared with the
name of a built-in type: `fn exactly_one?(n: Int) := n = 1` is an error.

### Defined functions

`fn double(n: Int): Int := 2 * n` declares the function `double`, whose
value at any `Int` `n` is `2 * n`. A defined function's parameters are
declared like a component's variables, `n: Int` or `ready?` for a `Bool`,
and its *body* `e` is an [expression](Expressions.md) of its result type,
optionally followed by a [`where` clause](Let.md).
An uninterpreted function's parameters have types but no names, unless
it has a contract, and a defined function's all have names, so that the
body and the contract can mention them. `lang::function_params` states
this, from the number of parameters and of those written with a name:

```fren
pub comp function_params {
    in defined?          -- written with `:= e`
    in contract?         -- it has a contract: an `assume` or an `ensure` clause
    in n_params: Nat is 1..
    in n_named: Nat      -- parameters written with a name

    assume counts: n_named <= n_params
    pub det out accepted?

    ensure rule: accepted? iff n_named = (if defined? or contract? then n_params else 0)

    expect all_or_nothing: when accepted? and n_named > 0, n_named = n_params
    expect contracts_name: when contract? and accepted?, n_named = n_params
}
```

The parameters' names must be distinct, and may
[shadow](Components.md#shadowing) the constants, functions and variants
of the function's module, written with `!`. The body mentions no
component's variables: only the parameters, binders of its own [`match`
arms](Expressions.md#matches), names of its own [`let`s and `where`
clauses](Let.md), constants, variants, and defined functions
declared before the function.
So a function is not in scope in its own body, and defined functions are
never recursive, directly or through each other. Nor does the body apply
an uninterpreted function, so a defined function's values are fully
known. `lang::function_body` states when a body is accepted:

```fren
set_option fren.evidence "enumerated" in
pub comp function_body {
    in typed?                -- the body has the function's result type
    in applies_self?         -- the body applies the function being declared
    in applies_uninterpreted?  -- the body applies an uninterpreted function
    pub det out accepted?

    ensure rule: accepted? iff (typed? and not applies_self? and not applies_uninterpreted?)

    expect not_recursive: when applies_self?, not accepted?
    expect well_typed: when not typed?, not accepted?
    expect interpreted_only: when applies_uninterpreted?, not accepted?
}
```

An application of a defined function has the value of its body, with each
parameter standing for the value of its argument (see [Function
applications](Expressions.md#function-applications)). The body has a value
for every argument, so there is nothing about the function itself to
check but its [contract](#contracts): a defined function is like a
component with an input for each parameter, and one `det out` that a
single guarantee makes equal to the body, which always meets its checks.
Unlike a component, it is applied in expressions rather than
instantiated. Otherwise only how the body is written is checked: the
[completeness](../Check.md#completeness),
[disjointness](../Check.md#disjointness) and
[reachability](../Check.md#reachability) of its
[tables](Expressions.md#tables) and its [`match`es](Expressions.md#matches)
with guards, the
[preconditions](../Check.md#preconditions) of the functions it applies,
and its [pattern types' obligations](../Check.md#pattern-types), such as
that the body is in range where the result is a pattern type, for every
value of the parameters that meets its preconditions and their types, as
for the value of a [constant](#constants).

### Uninterpreted functions

The spec does not say what an uninterpreted function's value is for any
argument. All that is known of it is that it is a function: applied
to equal arguments, it gives equal results, of its result type, and
that it meets its [postconditions](#contracts). So an
application of a function whose result is a `Nat` is at least 0, as a
`Nat` variable is (see [Components](Components.md#natural-numbers)), one
whose result is a [pattern type](Types.md#pattern-types) matches its
pattern, and an application of a function with postconditions meets each
of them wherever it meets the preconditions: each application brings these
constraints where it is written, and no constraint quantifies over the
function's arguments. So it relates values
consistently wherever it is applied, across the constraints of a
component, its instances, and the behaviours of a [global
expectation](Global.md). What its values are is given by an
[interpretation](Components.md#interpretations). A [generic
one](GenericFunctions.md#uninterpreted-generic-functions) is an unknown
function of its own at each instance.

### Contracts

A function's *contract* is the clauses written after its signature, and
after its body for a defined function, one per line: `assume n: e`
declares the *precondition* `n`, and `ensure n: e` the *postcondition*
`n`, each a `Bool` expression `e`, optionally followed by a [`where`
clause](Let.md):

```text
fn at(q: Seq<Int>, i: Int): Int := q[i]
    assume in_range: 0 <= i < q.len

pub type Name
pub fn arity(n: Name): Nat
    ensure positive: arity(n) > 0
```

A contract states what a function needs of its arguments and what it
gives, as a component's [assumptions and
guarantees](Components.md#meaning) do of its inputs and outputs: a
function is like a component with an input for each parameter and one
`det out`, its value. The names of the clauses share one namespace with
the parameters (see [Distinct names](#distinct-names)). A clause mentions
what a component's constraint may, but for variables: the parameters,
binders and names of its own, constants, variants, and functions declared
before the function, so that a precondition of `elem` can say what `kind`
its argument has. A postcondition may also mention the function's value, by
applying the function to its parameters, each written as its name, in
order, as `arity(n)` above. A precondition does not apply the function
itself: it says where the function may be applied, so it cannot depend on
the function's value. `lang::contract_application` states which
applications of the function itself a clause may have:

```fren
pub enum ClauseKind { Precondition, Postcondition }

set_option fren.evidence "enumerated" in
pub comp contract_application {
    in clause: ClauseKind
    in own?                  -- it applies the function whose contract the clause is in
    in to_params?            -- its arguments are the parameters, each written as its name, in order
    pub det out accepted?

    ensure rule: accepted? iff (not own? or (clause = ClauseKind::Postcondition and to_params?))

    expect others: when not own?, accepted?
    expect value_only: when own? and not to_params?, not accepted?
    expect not_in_preconditions: when clause = ClauseKind::Precondition and own?, not accepted?
}
```

`lang::contract_arguments` states the rule over the arguments as they
are written, which both front ends read alike: each is one of the
parameters' names, not hidden by a name of the clause's own, or another
expression. The parameters are three at most here, and the rule is the
same for more. It refines `lang::contract_application`, whose
`to_params?` is that the arguments are the parameters. Comparing
sequences is outside the [decidable core](Decidability.md), so both opt
out:

```fren
pub enum Param { P0, P1, P2 }
pub enum Written { Name(Param), Other }   -- an argument, as written

set_option fren.lint.undecidable "allow" in
pub comp contract_arguments {
    in clause: ClauseKind
    in own?                  -- it applies the function whose contract the clause is in
    in params: Seq<Written>  -- the function's parameters, each as its name, never `Other`
    in args: Seq<Written>    -- the application's arguments, as written
    pub det out accepted?

    ensure rule: accepted? iff (not own? or (clause = ClauseKind::Postcondition and args = params
        and not Written::Other in params))

    expect expressions: when own? and Written::Other in args, not accepted?
    expect arity: when own? and args.len != params.len, not accepted?
}

set_option fren.lint.undecidable "allow" in
refine arguments_detail: contract_arguments refines contract_application {
    to_params? := args = params and not Written::Other in params,
}
```

At each application of a function, its arguments must meet its
preconditions: the [precondition check](../Check.md#preconditions)
confirms that each holds where the application is evaluated, as the
[instance check](../Check.md#instance-assumptions) confirms an instance's
bindings meet its component's assumptions. Where one fails, the
application's value is still what the body gives, for a defined function,
or unknown, for an uninterpreted one: the failure is reported, never
assumed away. A defined function's body, and its postconditions, are
checked under its preconditions.

A defined function's postconditions are claims about its body, which the
[postcondition check](../Check.md#postconditions) confirms for every
value of the parameters that meets the preconditions, as the expectation
check confirms an expectation. An uninterpreted function's postconditions
are what is known of it: each application brings, where it is written,
that if its arguments meet the preconditions, its value meets each
postcondition, one constraint for each, so that no constraint quantifies
over the function's arguments (see [Uninterpreted
functions](#uninterpreted-functions)). So they must be able to hold: for
all arguments that meet the preconditions, some value must meet every
postcondition, whatever the other functions are, which the
[realizability check](../Check.md#contracts-of-uninterpreted-functions)
confirms. Postconditions that contradict each other, as `bad(n) > 0` and
`bad(n) < 0`, or one that says nothing of the function's value and can be
false, as `n > 0`, fail it. In Lean, an
[interpretation](../Impl.md#interpretations) of the function proves them.
Contracts on constants, and contracts on components beyond what
components already state, are not part of Fren.

Every function is used by [applying it](Expressions.md#function-applications),
as in `arity(n) > 0`. Like any other item, a function or abstract type is
visible according to `pub`, and can be brought into scope with `use` (see
[Modules and visibility](Modules.md)).

## Constants

```
constant := ["pub"] "const" IDENT ":" type ":=" top
```

`const MAX_TEMP: Int := 100` declares the constant `MAX_TEMP`, of type
`Int`, with the value `100`. A constant's name never ends in `?`, even
when the constant is a `Bool`, and by convention is in `UPPER_CASE` (see
[Naming conventions](../Lint/NonstandardStyle.md#naming-conventions)). Its type is always
written.

The value is an [expression](Expressions.md) of the constant's type,
optionally followed by a [`where` clause](Let.md). It
mentions no variables: only literals, variants, names of its own `let`s
and `where` clauses, and constants declared before it, so constants cannot depend on each other in a cycle. It may
apply [defined functions](#defined-functions) declared before it, but no
uninterpreted function, since its value is unknown. And the constant's
type is not an abstract type, which has no literals. Its type may be a
[pattern type](Types.md#pattern-types), and its value is then checked to
match it, as a defined function's body is. `lang::constant`
states this:

```fren
set_option fren.evidence "enumerated" in
pub comp constant {
    in ty: ValueType     -- the constant's type
    in applies?          -- its value applies an uninterpreted function
    pub det out accepted?

    ensure rule: accepted? iff (ty != ValueType::AbstractTy and not applies?)

    expect no_abstract_constants: when ty = ValueType::AbstractTy, not accepted?
}
```

A constant stands for its value wherever it is mentioned: in assumptions,
guarantees, expectations, bindings, and the values of other constants,
and as a record whose field is read or the receiver of a
[method](Expressions.md#methods), as in `LOBBY.floor` or `GREETING.len`.
There it is named by one identifier, since `a.b` is never a path (see
[Lexical structure](Lexical.md#identifiers)): a constant of another
module is first brought into scope with `use`, and `places::LOBBY.floor`
is an error.
It is not a variable, so the rules for which variables an expression may
mention (see [Instances](Instances.md#instance-variables)) do not apply to
it. Like any other item, a constant is visible according to `pub`, and can
be brought into scope with `use` (see [Modules and
visibility](Modules.md)).

## Components

```
component := ["pub"] "comp" IDENT "{" member* "}"
```

See [Components](Components.md).

## Global expectations

```
expectation := "expect" IDENT ":" ["forall" binder+ ","] expr
binder      := "(" DECL+ ":" path ")"
```

A global expectation is an expectation about components as a whole rather
than about one of their behaviours, such as two components agreeing, or one
component being monotone. See [Global expectations](Global.md).

## Refinements

```
refinement := "refine" IDENT ":" path "refines" path ["{" [binding ("," binding)* [","]] "}"] ["by" TACTICS]
```

`refine r: c refines a` states that component `c` refines component `a`,
and has Fren check it. Its bindings, written as an instance's, give
variables of `a` as expressions over `c`'s. See [Refinement](Refinement.md).

## Checks

```
check := "#fren_check" [path] | "#fren_trace"
```

`#fren_check` runs the [checks](../Check.md) in Lean, and `#fren_trace`
reports the [evidence](../Trace.md) for every component. The `fren` command
accepts and ignores both: `fren check` checks every component and global
expectation, and `fren trace` reports the evidence. See [Lean embedding](../Lean.md#commands).

## Claims

```
claim := "tested" path ":" STRING ("," STRING)* [","] | "trusted" path ":" STRING
```

A claim records evidence for a component that is not an implementation: a
`tested` claim names test files that exercise it, and a `trusted` claim
gives a justification. Both Lean and the `fren` command accept claims. See
[Traceability](../Trace.md).

## Lint settings

```
lint-setting := "set_option" lint-option STRING ["in" item]
lint-option  := "fren.lint." IDENT
```

`set_option fren.lint.unused_imports "deny"` sets the level of a
[lint](../Lint.md) for the rest of the file, or, followed by `in` and an
item, for that item only. See [Setting levels](../Lint.md#setting-levels).

## Lean-only items

```
lean-item := implementation | interpretation | "#fren_md" STRING
```

These items exist only in Lean, and the `fren` command rejects them. See
[Implementations](../Impl.md), [Interpretations](../Impl.md#interpretations),
[Markdown specs](../Markdown.md) and [Lean embedding](../Lean.md#commands).
