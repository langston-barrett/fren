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

set_option fren.evidence "enumerated" in
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

    assume enumerations_only: when type_kind != EnumTy, not recursive?
    pub det out listed?

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

    assume some_instance: values != {}
    pub det out holds?

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

    assume some: n_instances >= 1
    pub det out accepted?

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
quantifiers, is bound by an [implementation](../Impl.md) to the code and
proved in Lean, where each `forall` is a `∀` of the theorem, for every
input. A bounded model of it, over a listed type, stays in the decidable
core, where `decide` checks its implementation. `lint::manual_at_most_one_any`
and `lint::manual_at_most_one` are such a pair (see
[Cardinality](../Lint/Complexity/Operators.md#cardinality)). Where a proof
is out of reach, a [refinement](Refinement.md#evidence) whose evidence is
testing relates the two instead, and testing evaluates the quantifiers
where they have [domains](#guards).

Within an unbounded quantifier's body, an application of a function whose
arguments mention one of its bound names brings the facts that an
application brings elsewhere: that a `Nat` result is at least 0, that the
result is of its pattern type, and that the function's postconditions
hold where its preconditions do (see
[Contracts](../Check.md#contracts-of-uninterpreted-functions)). Each holds
whatever the arguments, so it is stated for every value of the bound names
that the application mentions, under the solver's quantifier over them,
without the guard: for `forall (i: Int), when 0 <= i < n, h(i) >= 0`, with
`fn h(Int): Nat`, the queries assume `(forall ((|i'0| Int)) (>= (h |i'0|)
0))`, and in Lean, `∀ i'0, 0 ≤ ↑(h i'0)`. Both front ends state the same
facts, so the checks agree.

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
and `e` names neither `x` nor a bound name declared after `x` in the same
quantifier: no name of one segment within it, nor the root of a dotted
name, nor a field of a record literal written without `:=`, is one of
theirs, whatever shadows it. A bound by `<` or `>` is *strict*: the bound
itself is not in range. Any other conjunct gives no bound. Seen from `x`,
an operand is `x` itself (`Name`), an expression that names neither `x`
nor a later bound name (`Free`), or any other (`Later`), and
`lang::guard_bound` states the bound from a conjunct's operands, `lhs`
and `rhs`, and its relation:

```fren
-- An operand of a conjunct, seen from a bound name `x`.
pub enum GuardOperand { Name, Free, Later }

-- The relation of a conjunct: a comparison, `in`, or anything else
-- (`Other`), whose operands are then irrelevant.
pub enum GuardRelation { Lt, Le, Gt, Ge, In, Other }

pub enum GuardBound { Members, Lower, Upper, NoBound }

-- The bound that `lhs relation rhs` gives.
fn guard_bound_of(lhs: GuardOperand, relation: GuardRelation, rhs: GuardOperand): GuardBound := table {
    | lhs = GuardOperand::Name and relation = GuardRelation::In and rhs = GuardOperand::Free => GuardBound::Members,
    | (lhs = GuardOperand::Name and relation in {GuardRelation::Gt, GuardRelation::Ge} and rhs = GuardOperand::Free)
        or (lhs = GuardOperand::Free and relation in {GuardRelation::Lt, GuardRelation::Le} and rhs = GuardOperand::Name)
        => GuardBound::Lower,
    | (lhs = GuardOperand::Name and relation in {GuardRelation::Lt, GuardRelation::Le} and rhs = GuardOperand::Free)
        or (lhs = GuardOperand::Free and relation in {GuardRelation::Gt, GuardRelation::Ge} and rhs = GuardOperand::Name)
        => GuardBound::Upper,
    | _ => GuardBound::NoBound,
}

pub comp guard_bound {
    use self::GuardBound::{Members, NoBound}
    use self::GuardOperand::Name
    use self::GuardRelation::{Gt, In, Lt}
    in lhs: GuardOperand
    in relation: GuardRelation
    in rhs: GuardOperand
    pub det out bound: GuardBound
    pub det out strict?      -- the bound itself is not in range

    ensure rule: bound = guard_bound_of(lhs, relation, rhs)
    ensure strictness: strict? iff relation in {Lt, Gt}

    expect members_by_in: when bound = Members, relation = In
    expect name_alone: when bound != NoBound, (lhs = Name) != (rhs = Name)
}
```

The bound name's *domain* comes from its conjuncts' bounds, in order: its
members, from the first conjunct that gives them; otherwise a range, from
the first conjunct that gives a lower bound and the first that gives an
upper bound, where a `Nat` with no lower bound starts from 0; otherwise
none. `lang::guard_domain` states it, from the conjuncts as written: each
side of each with the position of the bound name that it is, written
alone, and those of the bound names that it names, which is all that each
front end reads of a conjunct's syntax. The bound names and the conjuncts
are named by their positions, from 0:

```fren
-- A side of a conjunct: the position of the bound name that it is, written
-- alone, or -1 if it is none; and the positions of the bound names that it
-- names.
pub struct GuardSide { alone: Int, names: Seq(Int) }

-- A conjunct of a guard: a comparison or membership, or `Other`.
pub struct GuardConjunct { lhs: GuardSide, relation: GuardRelation, rhs: GuardSide }

-- What the side `s` is, seen from the bound name at position `k`.
set_option fren.lint.undecidable "allow" in
fn guard_operand(s: GuardSide, k: Int): GuardOperand :=
    if s.alone = k then GuardOperand::Name
    else if (exists (j: Int), j in s.names and j >= k) then GuardOperand::Later
    else GuardOperand::Free

-- The bound that the conjunct `c` gives the bound name at position `k`.
set_option fren.lint.undecidable "allow" in
fn conjunct_bound(c: GuardConjunct, k: Int): GuardBound :=
    guard_bound_of(guard_operand(c.lhs, k), c.relation, guard_operand(c.rhs, k))

-- No conjunct of `cs` before position `n` gives the bound name at `k` the
-- bound `b`.
set_option fren.lint.undecidable "allow" in
fn none_before?(cs: Seq(GuardConjunct), k: Int, b: GuardBound, n: Int) :=
    forall (j: Int), when 0 <= j < n, conjunct_bound(cs[j], k) != b

-- The conjunct at position `j` gives the bound name at `k` the bound `b`,
-- and none before it does.
set_option fren.lint.undecidable "allow" in
fn first_at?(cs: Seq(GuardConjunct), k: Int, b: GuardBound, j: Int) :=
    conjunct_bound(cs[j], k) = b and none_before?(cs, k, b, j)

-- `Members`: the members of the conjunct at `lo`. `Range`: from the lower
-- bound at `lo` to the upper bound at `hi`. `FromZero`: from 0 to the upper
-- bound at `hi`. `Unbounded`: no domain.
pub enum DomainShape { Members, Range, FromZero, Unbounded }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp guard_domain {
    use self::GuardBound::{Lower, Members, Upper}
    in conjuncts: Seq(GuardConjunct)  -- the conjuncts of the guard, in order
    in k: Nat                         -- the position of the bound name
    in nat?                           -- the bound name is a `Nat`
    pub det out shape: DomainShape
    pub det out lo: Int               -- the position of the conjunct that gives the members or the lower bound, or -1
    pub det out hi: Int               -- the position of the conjunct that gives the upper bound, or -1

    ensure members: forall (j: Int), when 0 <= j < conjuncts.len and first_at?(conjuncts, k, Members, j),
        shape = DomainShape::Members and lo = j and hi = -1
    ensure range: forall (l h: Int), when 0 <= l < conjuncts.len and 0 <= h < conjuncts.len
        and none_before?(conjuncts, k, Members, conjuncts.len) and first_at?(conjuncts, k, Lower, l)
        and first_at?(conjuncts, k, Upper, h),
        shape = DomainShape::Range and lo = l and hi = h
    ensure from_zero: forall (h: Int), when 0 <= h < conjuncts.len and nat?
        and none_before?(conjuncts, k, Members, conjuncts.len) and none_before?(conjuncts, k, Lower, conjuncts.len)
        and first_at?(conjuncts, k, Upper, h),
        shape = DomainShape::FromZero and lo = -1 and hi = h
    ensure unbounded: when none_before?(conjuncts, k, Members, conjuncts.len)
        and (none_before?(conjuncts, k, Upper, conjuncts.len)
        or (not nat? and none_before?(conjuncts, k, Lower, conjuncts.len))),
        shape = DomainShape::Unbounded and lo = -1 and hi = -1

    expect positions: (lo = -1 or 0 <= lo < conjuncts.len) and (hi = -1 or 0 <= hi < conjuncts.len)
    expect bounded_above: shape in {DomainShape::Members, DomainShape::Unbounded} or hi >= 0
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

set_option fren.evidence "enumerated" in
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
