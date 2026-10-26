# Quantifiers

A quantifier says that an expression holds for every value of a type, or
for some value of one:

```text
ensure all_quiet: forall (m: Method), not loud?(m)
expect some_mode: exists (m: Mode), heats?(m)
ensure sorted: forall (i: Int), when 0 <= i < q.len - 1, q[i] <= q[i + 1]
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

A quantifier ranges over any type. A type whose values can be listed is
*listed*: `Bool`, or an enumeration or record whose payloads and fields
have listed types. These are the types that are both [finite and not
unbounded](Types.md#finite-types). A quantifier over listed types is
expanded into its instances (see [Meaning](#meaning)), and stays within
the [decidable core](Decidability.md). Any other type is not listed:
`Int`, `Nat`, `String` and abstract types have infinitely many values, a
recursive enumeration has values of every size, and a set, relation or
sequence type is unbounded, even where its element type is finite, as in
`Set(Bool)`. A bound name of such a type makes the quantifier *unbounded*
(see [Unbounded quantifiers](#unbounded-quantifiers)), which is outside
the decidable core. A binder's type is written and resolved as a
variable's is, so a path that names no type is an error, and so is one
that names a component, except in a global expectation's leading
`forall` (see [Global expectations](#global-expectations)).
A [pattern type](Types.md#pattern-types) is listed when it is finite and
not unbounded, as `lang::pattern_finite` says: `forall (x: Int is
0..=7), e` has eight instances, for 0 to 7 in increasing order, and
`forall (s: Severity is Severity::Warning | Severity::Error), e` two, the
variants that match in their declaration's order. Its values are those of
its base type that match its pattern, and are counted so. Within a binder's
type, as anywhere, a pattern type's alias stands for it.
`lang::quantified_type` states which types are listed, from the kind of
the type, whether it is a recursive enumeration, and whether the types of
its payloads or fields are all listed:

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
    in parts?                    -- the type of each of its payloads or fields is listed
    pub det out listed?

    assume enumerations_only: when type_kind != EnumTy, not recursive?

    ensure rule: listed? iff match type_kind {
        BoolTy => true,
        EnumTy => parts? and not recursive?,
        RecordTy => parts?,
        _ => false,
    }

    expect bool: when type_kind = BoolTy, listed?
    expect infinite: when type_kind in {IntTy, NatTy, StringTy, AbstractTy}, not listed?
    expect collections: when type_kind in {SetTy, RelTy, SeqTy}, not listed?
    expect parts_listed: when listed? and type_kind != BoolTy, parts?
}
```

## Meaning

A quantifier over listed types means its *expansion*. Its *instances* are
its body with each bound name standing for one value of its type, one
instance for each combination of the bound names' values; a `forall` is the conjunction of
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

Both front ends expand a quantifier over listed types while elaborating
it, so the solver's queries stay quantifier-free (see
[Decidability](Decidability.md)), and Lean sees the expansion, with no
`Fintype`. The body is elaborated once: its errors and lints are reported
once, where it is written, not for each instance. In an unbounded
quantifier, the bound names of listed types are expanded in the same way,
within the quantifier over the others (see [Unbounded
quantifiers](#unbounded-quantifiers)).

A quantifier has at most 256 instances: one with more is an error that
says how many it would have (`F0356`). The number of instances is the
product of the numbers of values of the types of the bound names of listed
types, so `(a b:
T)` counts `T`'s values twice. A `Bool` has two values, an enumeration
the sum, over its variants, of the product of the numbers of values of a
variant's payload (one for a variant without one), and a record the
product of the numbers of values of its fields. They are counted without
expanding anything. A quantifier in the body of another counts the
instances of those around it too, multiplied by its own: nested
quantifiers expand to at most 256 copies of the innermost body, so
`forall (a b: Byte), e` and `forall (a: Byte), forall (b: Byte), e` are
both rejected for a `Byte` of 256 values. A bound name of a type that is
not listed is not expanded, so it counts once: `forall (i: Int) (m:
Method), e` has as many instances as `forall (m: Method), e`.
`lang::quantifier_size` states the limit:

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

## Unbounded quantifiers

An unbounded quantifier means what it says, as in Lean: `forall (x: T),
e` is the proposition that `e` holds for every value of `x` of type `T`,
and `exists (x: T), e` that it holds for some. A bound name of a [pattern
type](Types.md#pattern-types) ranges over the values that match its
pattern, as a variable's does, and one of type `Nat` over the integers at
least 0: `forall (n: Nat), e` is `forall (n: Int), when n >= 0, e`, and
`exists (n: Nat), e` is `exists (n: Int), n >= 0 and e`. Its bound names
of listed types are expanded within it, as in a quantifier over listed
types: `forall (i: Int) (m: Method), e` is `forall (i: Int), e1 and e2`,
with `e1` and `e2` its body's instances at the two methods, which means
the same, since quantifiers of one kind may be taken in any order.

There is no other form of quantifier: one that ranges over the members of
a set or the positions of a sequence is written with a guard, which
bounds it (see [Guards](#guards)):

```text
forall (x: T), when x in s, p(x)
exists (i: Int), 0 <= i < q.len and q[i] = x
forall (x: T), law(x)
```

Neither front end expands an unbounded quantifier: in Lean it is `∀` or
`∃`, a `Prop`, and both front ends give the solver a quantifier, `(forall
((x T)) e)` or `(exists ((x T)) e)`, which declares the bound name at its
type's sort and nothing else, as [Solver queries](../Cli.md#solver-queries)
says. The solver decides it when it can. A quantifier is outside the
[decidable core](Decidability.md), so the `undecidable` lint reports each
binder of a type that is not listed, at the binder, and a spec that
quantifies so opts out of the core where it does. Its checks are then
asked of the solver, which may not decide them, and are
`Inconclusive` where it does not; they may be [tested](../Check.md#checking-by-testing)
instead, where the evaluator can evaluate the quantifier (see
[Evaluation](../Eval.md#quantifiers)), or a component's evidence may be a
`trusted` claim.

This is how a precise spec is written beside a decidable one. A
component that states a rule over any number of things, with unbounded
quantifiers, and a bounded model of it over a listed type, which `decide`
or the solver proves of the code, are related by a
[refinement](Refinement.md#evidence) whose evidence is testing: `fren
check` and `fren quickcheck` then test the precise statement on the
bounded one's behaviours, and its expectations on behaviours of any size.
`lint::manual_at_most_one_any` is one (see
[Cardinality](../Lint/Complexity/Operators.md#cardinality)).

Within an unbounded quantifier's body, an application of a function whose
arguments mention one of its bound names brings none of the facts that an
application brings elsewhere: that a `Nat` result is at least 0, that the
result is of its pattern type, and the function's postconditions (see
[Contracts](../Check.md#contracts-of-uninterpreted-functions)). Each is
about one application, at fixed arguments, and here the arguments range
over the values of the bound names. The solver then knows less of the
application, so a check may not be proved that would be with the facts,
and a counterexample that needs a fact to be false is refuted when Fren
confirms the model (see [Confirming models](../Eval.md#confirming-models)):
the check is then `Inconclusive`, never wrongly passed.

## Guards

The *guard* of a quantifier is what its body says first about its bound
names. The guard of a `forall` is the conditions of the `when`s at the top
of its body: `forall (x: T), when c, when d, e` has the guard `c` and
`d`. The guard of an `exists` is its body: `exists (x: T), a and b` has
the guard `a and b`. A guard's *conjuncts* are the operands of the `and`s
at its top, in order, with their parentheses removed, and a [chained
comparison](Expressions.md#chained-comparisons) is a conjunct of each of
its comparisons: `when 0 <= i < q.len and i != k, e` has the conjuncts
`0 <= i`, `i < q.len` and `i != k`. An `unless`, a `let` or anything else
ends a `forall`'s guard, as `exists (x: T), not (a and b)` has the one
conjunct `not (a and b)`.

Each conjunct gives a *bound* for each bound name `x` of a type that is
not listed: `x in e` gives its members, `x >= e`, `x > e`, `e <= x` and
`e < x` a lower bound, and `x <= e`, `x < e`, `e >= x` and `e > x` an
upper bound, where `x` is the bound name alone, not a field read from it,
and `e` mentions neither `x` nor a bound name declared after `x` in the
same quantifier. A bound by `<` or `>` is *strict*: the bound itself is
not in range. Any other conjunct gives no bound. `lang::guard_bound`
states the bound from the conjunct's operands, seen from `x`, and its
relation:

```fren
-- An operand of a conjunct, seen from a bound name `x`: `x` itself, written
-- alone; an expression that mentions neither `x` nor a bound name declared
-- after it (`Free`); or any other (`Later`).
pub enum GuardOperand { Name, Free, Later }

-- The relation of a conjunct: a comparison, `in`, or anything else
-- (`Other`), whose operands are then irrelevant.
pub enum GuardRelation { Lt, Le, Gt, Ge, In, Other }

pub enum Bound { Members, Lower, Upper, NoBound }

pub comp guard_bound {
    use self::Bound::{Lower, Members, NoBound, Upper}
    use self::GuardOperand::{Free, Name}
    use self::GuardRelation::{Ge, Gt, In, Le, Lt}
    in left: GuardOperand
    in relation: GuardRelation
    in right: GuardOperand
    pub det out bound: Bound
    pub det out strict?      -- the bound itself is not in range

    ensure rule: bound = table {
        | left = Name and relation = In and right = Free => Members,
        | (left = Name and relation in {Gt, Ge} and right = Free)
            or (left = Free and relation in {Lt, Le} and right = Name) => Lower,
        | (left = Name and relation in {Lt, Le} and right = Free)
            or (left = Free and relation in {Gt, Ge} and right = Name) => Upper,
        | _ => NoBound,
    }
    ensure strictness: strict? iff relation in {Lt, Gt}

    expect members_by_in: when bound = Members, relation = In
    expect name_alone: when bound != NoBound, (left = Name) != (right = Name)
}
```

The bound name's *domain* comes from its conjuncts' bounds, in order: its
members, from the first conjunct that gives them; otherwise a range, from
the first conjunct that gives a lower bound and the first that gives an
upper bound, where a `Nat` with no lower bound starts from 0; otherwise
none. `lang::guard_domain` states it, from each conjunct's bound, naming
the conjuncts by their positions, from 0:

```fren
-- No bound of `bounds` before position `k` is `b`.
set_option fren.lint.undecidable "allow" in
fn none_before?(bounds: Seq(Bound), b: Bound, k: Int) := forall (j: Int), when 0 <= j < k, bounds[j] != b

-- `b` is the bound at position `k` of `bounds`, and at none before it.
set_option fren.lint.undecidable "allow" in
fn first_at?(bounds: Seq(Bound), b: Bound, k: Int) := bounds[k] = b and none_before?(bounds, b, k)

-- `Members(k)`: the members of the conjunct at `k`. `Range(lo, hi)`: from
-- the lower bound at `lo` to the upper bound at `hi`. `FromZero(hi)`: from 0
-- to the upper bound at `hi`. `Unbounded`: no domain.
pub enum Domain { Members(Int), Range(Int, Int), FromZero(Int), Unbounded }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp guard_domain {
    use self::Bound::{Lower, Members, Upper}
    in bounds: Seq(Bound)    -- the bound of each conjunct, in order
    in nat?                  -- the bound name is a `Nat`
    pub det out domain: Domain

    ensure members: forall (k: Int), when 0 <= k < bounds.len and first_at?(bounds, Members, k),
        domain = Domain::Members(k)
    ensure range: forall (lo hi: Int), when 0 <= lo < bounds.len and 0 <= hi < bounds.len
        and none_before?(bounds, Members, bounds.len) and first_at?(bounds, Lower, lo) and first_at?(bounds, Upper, hi),
        domain = Domain::Range(lo, hi)
    ensure from_zero: forall (hi: Int), when 0 <= hi < bounds.len and nat? and none_before?(bounds, Members, bounds.len)
        and none_before?(bounds, Lower, bounds.len) and first_at?(bounds, Upper, hi),
        domain = Domain::FromZero(hi)
    ensure unbounded: when none_before?(bounds, Members, bounds.len) and (none_before?(bounds, Upper, bounds.len)
        or (not nat? and none_before?(bounds, Lower, bounds.len))), domain = Domain::Unbounded

    expect members_first: when Members in bounds, domain is Domain::Members(_)
    expect bounded_above: when domain is Domain::Range(_, _) | Domain::FromZero(_), Upper in bounds
}
```

A quantifier's guard says nothing about its meaning, which is the same
however it is written: a domain only lets the evaluator enumerate the
values at which the guard can hold (see
[Evaluation](../Eval.md#quantifiers)), and lets the solver know that the
quantifier is bounded: a component, global expectation or refinement
whose queries have an unbounded quantifier with a bound name that has a
domain sets cvc5's `fmf-bound` (see [Solver
queries](../Cli.md#solver-queries)), with which it finds models of
quantifiers bounded by membership and by integer ranges.

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

A bound name of a listed type stands for one value in each instance, so
it [mentions](Expressions.md#mentions) nothing: `forall (m: Method),
f(m)` is allowed wherever `f` of a constant is, and so is `2 *
cost(m)`. A bound name of any other type stands for all of its values at
once, as a variable does, so within the body it mentions itself: `2 * i`
is linear, but `n * i`, with `n` a variable, is a product of two
variables, an error, as `n * m` is (see [Linear
arithmetic](Expressions.md#linear-arithmetic)). The quantifier mentions
what its body mentions, but not its own bound names.

An index in the body is [guarded](Expressions.md#sequences) in each
instance by the conditions before it within the body, and by those around
the quantifier. The instances do not guard each other: the definedness
check reports an index that may be out of range in some instance where
its guard holds. In an unbounded quantifier, the index must be in range
for every value of the bound names where its guard holds, so its
definedness is quantified as the body is, whether the quantifier is a
`forall` or an `exists`: in `exists (i: Int), 0 <= i < q.len and q[i] =
x`, the goal is that `q[i]` is in range for every `i` with `0 <= i <
q.len`, which holds. A quantifier at the top of a constraint is not a `when`,
so the constraint has no [trigger](Components.md#triggers).

## Global expectations

In a [global expectation's](Global.md) leading `forall`, a binder whose
path names a component ranges over its behaviours, and one whose type is a
type ranges over its values, listed or not, and one `forall` may have both: in `expect
n: forall (a: c) (m: Method), E`, `E` holds for every behaviour `a` of
`c` and every value `m` of `Method`. The binders over values are a
quantifier around `E`, as if written `expect n: forall (a: c), forall (m:
Method), E`, with the rules of this chapter: they are counted, expanded,
named and scoped as a quantifier's. Everywhere else, a quantifier ranges
over values only. `lang::quantifier_binder` states this, from what a
binder's type names and whether it is in a global expectation's leading
`forall`:

```fren
-- `TypeName` is a type, listed or not, and `Component` a component.
pub enum BinderTarget { TypeName, Component }

pub comp quantifier_binder {
    use self::BinderTarget::{Component, TypeName}
    in target: BinderTarget
    in global?               -- it is in a global expectation's leading `forall`
    pub det out accepted?
    pub det out behaviours?  -- it ranges over a component's behaviours, not a type's values

    ensure rule: accepted? iff (target = TypeName or (global? and target = Component))
    ensure ranges: behaviours? iff target = Component

    expect values_anywhere: when target = TypeName, accepted? and not behaviours?
    expect behaviours_globally: when target = Component and accepted?, global?
}

-- One leading `forall` may range over values and over behaviours.
expect mixed_binders: forall (v b: quantifier_binder),
    when v.global? and b.global? and v.target = BinderTarget::TypeName and b.target = BinderTarget::Component,
    v.accepted? and b.accepted? and not v.behaviours? and b.behaviours?
```
