# Items

A spec is a sequence of items. Each item is a Lean command, so in a Lean file
items can be mixed with Lean code.

```
item := module | use | enumeration | record | abstract-type | function | constant
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
    in items: Seq(ItemName)      -- the items of the file and its imports, in order
    in used: ItemName            -- the item a path names
    in user: ItemName            -- the item the path is written in
    in k_used: Int               -- the position of `used` in `items`
    in k_user: Int               -- the position of `user`
    pub det out accepted?

    assume positions: 0 <= k_used < items.len and items[k_used] = used
        and 0 <= k_user < items.len and items[k_user] = user
    assume distinct: when used = user, k_used = k_user

    req rule: accepted? iff (used = user or k_used < k_user)

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
enumeration := ["pub"] "enum" IDENT "{" variant ("," variant)* [","] "}"
variant     := IDENT ["(" type ("," type)* ")"]
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
an item being declared before it is used.

## Records

```
record := ["pub"] "struct" IDENT "{" field ("," field)* [","] "}"
field  := IDENT [":" type]
```

`struct Point { x: Int, y: Int }` declares the record `Point`, whose
values each have an `Int` for `x` and one for `y`. A record has at least
one field, and its fields must have distinct names. A field follows the
[Boolean names](Types.md#boolean-names) rule: `ready?` is a `Bool` field,
and any other field has its type written. A record is
[built](Expressions.md#records) as `Point { x := 1, y := 2 }`, and its
fields are read as `p.x`. Its fields are visible wherever the record is.

A record's field cannot have the record's own type: a record has only one
way to build a value, so each value would contain another without end, and
the record would have no values. So records are never recursive
themselves, though a field may have an [unbounded
type](Types.md#recursive-and-unbounded-types).

## Distinct names

The names of a list of declarations are distinct: the variants of an
enumeration, the fields of a record, the parameters of a defined function,
the variables, instances and constraints of a component, which share one
namespace, and the binders of a global expectation or of a pattern. A
pattern's `_` declares no name. A name declared again is an error,
reported where it is declared again, in the order the declarations are
written, whatever their kinds. In every list, only the first such name is
reported, and the rest of its item is not checked, so a component with two
repeated names and an unknown type reports the first repeat alone. The
names of a component's members, of a function's parameters and of binders
are compared without their `!` of [shadowing](Components.md#shadowing), so
`in x: Int` and `in x!: Int` declare the same name, and so do `in x: Int`
and `req x!: true`, even though a constraint never shadows. The names of
variants and fields are compared as written: neither ever shadows, and a
`!` on one is an error of its own.
`lang::distinct_names` states this, from how many names a list declares
and the set of them:

```fren
pub mod lang

pub type DeclaredName

pub comp distinct_names {
    in count: Int                  -- how many names the list declares
    in names: Set(DeclaredName)    -- the names it declares
    pub det out accepted?

    assume counted: names.card <= count

    req rule: accepted? iff names.card = count

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
`req q: x == 1` before it is reported instead, and so is `!x?` anywhere in
the item.

## Fields and payloads

A field or a payload may have any type in which no abstract type occurs:
the values of a record or enumeration are fully described by the spec,
and `Set(Name)` is as abstract as `Name`. Nor may the item being declared
occur within a set's element type, as in `enum Tree { Node(Set(Tree)) }`:
a set is a value up to its members' order, and a type cannot be built from
sets of itself. `lang::field_type` states which types are accepted, from
the kind of the type, whether an abstract type or the item being declared
occurs within it, and whether it is a variant's payload rather than a
record's field:

```fren
pub mod lang

pub comp field_type {
    in kind!: ValueType   -- the kind of the field's or payload's type
    in abstract_within?  -- an abstract type is the type, or a set's element type within it
    in own?              -- the type is the item being declared
    in own_in_set?       -- the item being declared is a set's element type within the type
    in payload?          -- a variant's payload, rather than a record's field
    pub det out accepted?

    assume own_enum: when own? and payload?, kind = ValueType::EnumTy
    assume own_record: when own? and not payload?, kind = ValueType::RecordTy
    assume abstract_kind: when kind = ValueType::AbstractTy, abstract_within?
    assume in_set: when own_in_set?, kind = ValueType::SetTy and not own?

    req rule: accepted? iff (not abstract_within? and not own_in_set? and (payload? or not own?))

    expect no_abstract_fields: when kind = ValueType::AbstractTy, not accepted?
    expect records_not_recursive: when own? and not payload?, not accepted?
    expect not_through_sets: when own_in_set?, not accepted?
}
```

Every value of a recursive enumeration is built from finitely many
variants, so the enumeration needs at least one variant whose payload
does not have its own type: `enum Stream { More(Int, Stream) }` has no
values, and is an error. `lang::well_founded` states this, from the
variants and those with a payload of the enumeration's own type:

```fren
pub type VariantName

pub comp well_founded {
    in variants: Set(VariantName)
    in recursive: Set(VariantName)   -- variants with a payload of the enumeration's own type
    pub det out accepted?

    assume some_variant: variants != {}
    assume among: recursive subset variants

    req rule: accepted? iff recursive != variants

    expect plain_enumerations: when recursive = {}, accepted?
    expect one_base_case: when (variants minus recursive).card = 1, accepted?
}
```

## Abstract types

```
abstract-type := ["pub"] "type" IDENT
```

`type Name` declares the [abstract type](Types.md#abstract-types) `Name`.
Its values are not described: all that is known of them is that there is
at least one, and whether two of them are equal.

## Functions

```
function := ["pub"] "fn" IDENT "(" type ("," type)* ")" [":" type]
          | ["pub"] "fn" IDENT "(" variable ("," variable)* ")" [":" type] ":=" expr
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

A function written with `:= e` is *defined*, and any other is
*uninterpreted*.

### Defined functions

`fn double(n: Int): Int := 2 * n` declares the function `double`, whose
value at any `Int` `n` is `2 * n`. A defined function's parameters are
declared like a component's variables, `n: Int` or `ready?` for a `Bool`,
and its *body* `e` is an [expression](Expressions.md) of its result type.
An uninterpreted function's parameters have types but no names, and a
defined function's all have names, so that the body can mention them.
`lang::function_params` states this, from the number of parameters and of
those written with a name:

```fren
pub comp function_params {
    in defined?          -- written with `:= e`
    in n_params: Int
    in n_named: Int      -- parameters written with a name
    pub det out accepted?

    assume counts: n_params >= 1 and 0 <= n_named <= n_params

    req rule: accepted? iff n_named = (if defined? then n_params else 0)

    expect all_or_nothing: when accepted? and n_named > 0, n_named = n_params
}
```

The parameters' names must be distinct, and may
[shadow](Components.md#shadowing) the constants, functions and variants
of the function's module, written with `!`. The body mentions no
component's variables: only the parameters, binders of its own [`match`
arms](Expressions.md#matches), constants, variants, and defined functions
declared before the function.
So a function is not in scope in its own body, and defined functions are
never recursive, directly or through each other. Nor does the body apply
an uninterpreted function, so a defined function's values are fully
known. `lang::function_body` states when a body is accepted:

```fren
pub comp function_body {
    in typed?                -- the body has the function's result type
    in applies_self?         -- the body applies the function being declared
    in applies_uninterpreted?  -- the body applies an uninterpreted function
    pub det out accepted?

    req rule: accepted? iff (typed? and not applies_self? and not applies_uninterpreted?)

    expect not_recursive: when applies_self?, not accepted?
    expect well_typed: when not typed?, not accepted?
    expect interpreted_only: when applies_uninterpreted?, not accepted?
}
```

An application of a defined function has the value of its body, with each
parameter standing for the value of its argument (see [Function
applications](Expressions.md#function-applications)). The body has a value
for every argument, so there is nothing about the function itself to
check: a defined function is like a component with an input for each
parameter, and one `det out` that a single requirement makes equal to the
body, which always meets its checks. Unlike a component, it is applied in
expressions rather than instantiated.

### Uninterpreted functions

The spec does not say what an uninterpreted function's value is for any
argument. All that is known of it is that it is a function: applied
to equal arguments, it gives equal results. So it relates values
consistently wherever it is applied, across the constraints of a
component, its instances, and the behaviours of a [global
expectation](Global.md). What its values are is given by an
[interpretation](Components.md#interpretations).

Every function is used by [applying it](Expressions.md#function-applications),
as in `arity(n) > 0`. Like any other item, a function or abstract type is
visible according to `pub`, and can be brought into scope with `use` (see
[Modules and visibility](Modules.md)).

## Constants

```
constant := ["pub"] "const" IDENT ":" type ":=" expr
```

`const MAX_TEMP: Int := 100` declares the constant `MAX_TEMP`, of type
`Int`, with the value `100`. A constant's name never ends in `?`, even
when the constant is a `Bool`, and by convention is in `UPPER_CASE` (see
[Naming conventions](../Lint/NonstandardStyle.md#naming-conventions)). Its type is always
written.

The value is an [expression](Expressions.md) of the constant's type. It
mentions no variables: only literals, variants, and constants declared
before it, so constants cannot depend on each other in a cycle. It may
apply [defined functions](#defined-functions) declared before it, but no
uninterpreted function, since its value is unknown. And the constant's
type is not an abstract type, which has no literals. `lang::constant`
states this:

```fren
pub comp constant {
    in ty: ValueType     -- the constant's type
    in applies?          -- its value applies an uninterpreted function
    pub det out accepted?

    req rule: accepted? iff (ty != ValueType::AbstractTy and not applies?)

    expect no_abstract_constants: when ty = ValueType::AbstractTy, not accepted?
}
```

A constant stands for its value wherever it is mentioned: in assumptions,
requirements, expectations, bindings, and the values of other constants,
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
