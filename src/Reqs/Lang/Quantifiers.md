# Quantifiers

A quantifier says that an expression holds for every value of a finite
type, or for some value of one:

```text
ensure all_quiet: forall (m: Method), not loud?(m)
expect some_mode: exists (m: Mode), heats?(m)
```

```
expr   := ... | ("forall" | "exists") binder+ "," expr
binder := "(" DECL+ ":" type ")"
```

`forall (x y: T) (z: U), e` holds if `e`, its *body*, holds for every
value of `x` and `y` of type `T` and every value of `z` of type `U`, and
`exists (x: T), e` if `e` holds for some value of `x`. Each name that a
binder declares is a *bound name*. The body must be a `Bool`, and so is
the quantifier. Binders are written as a [global
expectation's](Global.md) are, with a type in place of a component.

A quantifier is an [expression](Expressions.md), at the level of `when`:
the binders end at the first `,` after them, and the body extends as far
right as possible. So `forall (m: Method), p(m) and q(m)` is `forall (m:
Method), (p(m) and q(m))`, and a quantifier that is the operand of an
operator is written in parentheses, as in `(forall (m: Method), p(m)) or
r?` (`F0109`). The body may itself be a quantifier, or a `when`, without
parentheses: `forall (a: Mode), forall (b: Mode), when a != b, differ?(a,
b)`. For the same reason as a `when`, a quantifier is not the top-level
body of a [`match` arm](Expressions.md#matches), nor the expression of an
instance's binding or of a record literal's field: those are written in
parentheses. `forall` and `exists` are [reserved
words](Lexical.md#keywords).

## Types

A quantifier ranges over a type whose values can be listed: `Bool`, or an
enumeration or record whose payloads and fields have such types. These
are the types that are both [finite and not unbounded](Types.md#finite-types):
`Int`, `Nat`, `String` and abstract types have infinitely many values, a
recursive enumeration has values of every size, and a set, relation or
sequence type is unbounded, even where its element type is finite, as in
`Set(Bool)`. Quantifying over any other type is an error (`F0355`): to say
something of every member of a set `s` of a finite type `T`, write
`forall (x: T), when x in s, ...`. A binder's type is written and resolved
as a variable's is, so a path that names no type is an error, and so is
one that names a component, except in a global expectation's leading
`forall` (see [Global expectations](#global-expectations)).
`lang::quantified_type` states which types a quantifier ranges over, from
the kind of the type, whether it is a recursive enumeration, and whether
the types of its payloads or fields are all ones it ranges over:

```fren
pub mod lang

pub comp quantified_type {
    use self::ValueType::{
        AbstractTy,
        BoolTy,
        EnumTy,
        IntTy,
        NatTy,
        RecordTy,
        RelTy,
        SeqTy,
        SetTy,
        StringTy,
    }
    in type_kind: ValueType      -- the kind of the type
    in recursive?                -- it is a recursive enumeration
    in parts?                    -- a quantifier ranges over the type of each of its payloads or fields
    pub det out accepted?

    assume enumerations_only: when type_kind != EnumTy, not recursive?

    ensure rule: accepted? iff match type_kind {
        BoolTy => true,
        EnumTy => parts? and not recursive?,
        RecordTy => parts?,
        _ => false,
    }

    expect bool: when type_kind = BoolTy, accepted?
    expect infinite: when type_kind in {IntTy, NatTy, StringTy, AbstractTy}, not accepted?
    expect collections: when type_kind in {SetTy, RelTy, SeqTy}, not accepted?
    expect parts_ranged: when accepted? and type_kind != BoolTy, parts?
}
```

## Meaning

A quantifier means its *expansion*. Its *instances* are its body with each
bound name standing for one value of its type, one instance for each
combination of the bound names' values; a `forall` is the conjunction of
its instances, and an `exists` their disjunction. With `enum Method {
Len, Card }`, `forall (m: Method), not loud?(m)` means `not
loud?(Method::Len) and not loud?(Method::Card)`, and `exists (a? b?:
Bool), a? and not b?` is the disjunction of four instances. Every type
has a value, so every quantifier has an instance: a `forall` implies the
`exists` of the same body. `lang::quantifier` states this, from the
values of the instances:

```fren
pub comp quantifier {
    in all?                  -- `forall`, rather than `exists`
    in values: Set(Bool)     -- the values of its instances
    pub det out holds?

    assume some_instance: values != {}

    ensure rule: holds? iff (if all? then not false in values else true in values)

    expect conjunction: when all?, holds? iff values = {true}
    expect disjunction: unless all?, holds? iff true in values
}

expect forall_implies_exists: forall (a e: quantifier),
    when a.all? and not e.all? and a.values = e.values and a.holds?, e.holds?
```

The values of a type are listed in order: `true` then `false`; the
variants of an enumeration in their declaration's order, each with every
combination of the values of its payload; and every combination of a
record's fields. The bound names vary in the order that they are written,
the last fastest. The order changes no meaning: it is the order in which
the instances are conjoined, which the [generated Lean
declarations](../Generated.md#components) show.

Both front ends expand a quantifier while elaborating it, so the solver's
queries stay quantifier-free (see [Decidability](Decidability.md)), and
Lean sees the expansion, with no `Fintype`. The body is elaborated once:
its errors and lints are reported once, where it is written, not for each
instance.

A quantifier has at most 256 instances: one with more is an error that
says how many it would have (`F0356`). The number of instances is the
product of the numbers of values of the bound names' types, so `(a b:
T)` counts `T`'s values twice. A `Bool` has two values, an enumeration
the sum, over its variants, of the product of the numbers of values of a
variant's payload (one for a variant without one), and a record the
product of the numbers of values of its fields. They are counted without
expanding anything. A quantifier in the body of another counts the
instances of those around it too, multiplied by its own: nested
quantifiers expand to at most 256 copies of the innermost body, so
`forall (a b: Byte), e` and `forall (a: Byte), forall (b: Byte), e` are
both rejected for a `Byte` of 256 values. `lang::quantifier_size` states
the limit:

```fren
pub const MAX_INSTANCES: Int := 256

pub comp quantifier_size {
    in n_instances: Int      -- the combinations of the values of its bound names and those around it
    pub det out accepted?

    assume some: n_instances >= 1

    ensure rule: accepted? iff n_instances <= MAX_INSTANCES

    expect at_limit: when n_instances = MAX_INSTANCES, accepted?
    expect beyond_limit: when n_instances > MAX_INSTANCES, not accepted?
}
```

## Names

A bound name is in scope in the body, and nowhere else. The names of one
quantifier, across all of its binders, are [distinct](Items.md#distinct-names)
(`F0213`), and follow the [Boolean names](Types.md#boolean-names) rule for
their type: `forall (b?: Bool)`, and `forall (m: Method)`. A bound name
may [shadow](Components.md#shadowing) another, written with `!`: a
variable, a parameter, an instance, a binder of a global expectation or a
pattern, a bound name of an enclosing quantifier, a constant, a function
or a variant, as in `forall (m!: Method), ...` within a component with a
variable `m`. A mention of it in the body is not a mention of what it
shadows.

A bound name stands for one value in each instance, so it
[mentions](Expressions.md#mentions) nothing: `forall (m: Method), f(m)`
is allowed wherever `f` of a constant is, and so is `2 * cost(m)`. The
quantifier mentions what its body mentions.

An index in the body is [guarded](Expressions.md#sequences) in each
instance by the conditions before it within the body, and by those around
the quantifier. The instances do not guard each other: the definedness
check reports an index that may be out of range in some instance where
its guard holds. A quantifier at the top of a constraint is not a `when`,
so the constraint has no [trigger](Components.md#triggers).

## Global expectations

In a [global expectation's](Global.md) leading `forall`, a binder whose
path names a component ranges over its behaviours, and one whose type is a
type ranges over its values, and one `forall` may have both: in `expect
n: forall (a: c) (m: Method), E`, `E` holds for every behaviour `a` of
`c` and every value `m` of `Method`. The binders over values are a
quantifier around `E`, as if written `expect n: forall (a: c), forall (m:
Method), E`, with the rules of this chapter: they are counted, expanded,
named and scoped as a quantifier's. Everywhere else, a quantifier ranges
over values only. `lang::quantifier_binder` states this, from what a
binder's type names and whether it is in a global expectation's leading
`forall`:

```fren
-- `ListedType` is a type that a quantifier ranges over (`quantified_type`),
-- `OtherType` any other type, and `Component` a component.
pub enum BinderTarget { ListedType, OtherType, Component }

pub comp quantifier_binder {
    use self::BinderTarget::{Component, ListedType, OtherType}
    in target: BinderTarget
    in global?               -- it is in a global expectation's leading `forall`
    pub det out accepted?
    pub det out behaviours?  -- it ranges over a component's behaviours, not a type's values

    ensure rule: accepted? iff (target = ListedType or (global? and target = Component))
    ensure ranges: behaviours? iff target = Component

    expect values_anywhere: when target = ListedType, accepted? and not behaviours?
    expect behaviours_globally: when target = Component and accepted?, global?
    expect other_types: when target = OtherType, not accepted?
}

-- One leading `forall` may range over values and over behaviours.
expect mixed_binders: forall (v b: quantifier_binder),
    when v.global? and b.global? and v.target = BinderTarget::ListedType and b.target = BinderTarget::Component,
    v.accepted? and b.accepted? and not v.behaviours? and b.behaviours?
```
