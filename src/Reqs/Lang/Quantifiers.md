# Quantifiers

A quantifier states that a `Bool` expression holds for every value of a
type (`forall`), or for some value of one (`exists`).

```text
ensure all_quiet: forall (m: Method), not loud?(m)
expect some_mode: exists (m: Mode), heats?(m)
ensure sorted: forall (i: Int), when 0 <= i < q.len - 1, q[i] <= q[i + 1]
```

## Syntax

r[quantifier.syntax]
```
expr   := ... | ("forall" | "exists") binder+ "," expr
binder := "(" DECL+ ":" type ")"
```

r[quantifier.syntax.terms]
The expression after the `,` is the quantifier's *body*. Each name that a
binder declares is a *bound name*.

r[quantifier.syntax.keywords]
`forall` and `exists` are [reserved words](Lexical.md#keywords).

r[quantifier.syntax.extent]
A quantifier is an [expression](Expressions.md) at the precedence of
`when`. Its binders end at the first `,` after them, and its body extends
as far to the right as possible.

r[quantifier.syntax.operand]
A quantifier that is an operand of an operator is written in parentheses
(`F0109`).

r[quantifier.syntax.nested]
The body may be a quantifier or a `when` without parentheses.

r[quantifier.syntax.positions]
A quantifier is written in parentheses where it is the top-level body of a
[`match` arm](Expressions.md#matches), an argument of a call, or the
expression of a field of a record literal, as a `when` is.

**Examples**

```text
forall (m: Method), p(m) and q(m)          -- forall (m: Method), (p(m) and q(m))
(forall (m: Method), p(m)) or r?
forall (a: Mode), forall (b: Mode), when a != b, differ?(a, b)
```

## Types

A quantifier ranges over any type. Over a type whose values can be listed,
it is expanded into finitely many instances; over any other, it is
unbounded.

**Legality rules**

r[quantifier.type.body]
The body is a `Bool`, and so is the quantifier.

r[quantifier.type.binder]
A binder's type is written and resolved as a variable's type is. A binder
whose type is a path that names no type is an error. One whose type names a
procedure is an error too (`quantifier.binder.procedure`).

r[quantifier.type.listed]
A type is *listed* when it is [finite and not
unbounded](Types.md#finite-types): every type that it is built from is
finite by itself, has a former that is not growing, and is not recursive.
A type of a former that has no constituents, such as `Bool`, has none
(`lang::quantified_type`, over the constituent relation of
`lang::type_facts`).

r[quantifier.type.not-listed]
`Int`, `Nat`, `String`, abstract types, recursive enumerations, and set,
relation and sequence types are not listed, whatever their element types.

r[quantifier.type.subset]
A [subset type](SubsetTypes.md) is listed when it is finite and not
unbounded (`lang::pattern_finite`). A subset type whose invariant is a
pattern test that matches finitely many integers is listed, and so is a
type built from it. Its values are those of its base type that satisfy its
invariants.

r[quantifier.type.alias]
An alias of a subset type stands for the subset type in a binder's type, as
anywhere.

r[quantifier.type.unbounded]
A quantifier with a bound name of a type that is not listed is
*unbounded* (see [Unbounded quantifiers](#unbounded-quantifiers)), and is
outside the [decidable core](Decidability.md). A quantifier whose bound
names all have listed types is within it.

```fren
pub mod lang

set_option fren.lint.undecidable "allow" in
pub proc quantified_type(
    ty: DeclaredTy,
    constituents: Rel<DeclaredTy, DeclaredTy>,      -- (t, u): t has a field, payload or element of type u
): (det listed?) {
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

    -- A type of a former that has no constituents has none.
    assume leaf: unless former(declared_kind(ty)).composite?, constituents.image({ty}) = {}
    call facts := type_facts(ty, constituents)

    ensure rule: listed? iff (facts.finite? and not facts.unbounded?)

    expect bool: when declared_kind(ty) = BoolTy, listed?
    expect infinite: when declared_kind(ty) in {StringTy, AbstractTy}, not listed?
    expect integers: when declared_kind(ty) in {IntTy, NatTy}, listed? iff pattern_bounded?(ty)
    expect collections: when declared_kind(ty) in {SetTy, RelTy, SeqTy}, not listed?
    expect not_recursive: when facts.recursive?, not listed?
    expect constituents_listed: when listed?, (forall (u: DeclaredTy), when u in constituents.image({ty}),
        own_finite?(declared_kind(u), pattern_bounded?(u)) and not former(declared_kind(u)).growing?
        and not (u, u) in constituents.closure)
    -- `struct P { x: Four }`, `enum Small { S(Three), T }` and `Option<Three>`.
    expect bounded_field: forall (x: DeclaredTy),
        when declared_kind(ty) in {RecordTy, EnumTy} and constituents = {(ty, x)}
        and declared_kind(x) = IntTy and pattern_bounded?(x),
        listed?
    -- `Pair<Bool, Two>`.
    expect bounded_pair: forall (b: DeclaredTy) (x: DeclaredTy),
        when declared_kind(ty) = RecordTy and constituents = {(ty, b), (ty, x)}
        and declared_kind(b) = BoolTy and declared_kind(x) = IntTy and pattern_bounded?(x),
        listed?
    expect unbounded_field: forall (x: DeclaredTy),
        when declared_kind(ty) = RecordTy and constituents = {(ty, x)} and declared_kind(x) = IntTy and not pattern_bounded?(x),
        not listed?
}
```

**Examples**

- Listed: `Bool`; `enum Method { Len, Card }`; with subset aliases
  `Four`, `Three` and `Two` of the integers `0..=3`, `0..=2` and `1..=2`,
  `struct P { x: Four }`, `enum Small { S(Three), T }`, `Option<Three>` and
  `Pair<Bool, Two>`.
- Not listed: `Int`, `Set<Bool>`, `enum Tree { Leaf, Node(Tree) }`.

A quantifier over `Int` is unbounded, and the `undecidable` lint reports
its binder:

```fren example
proc positive(n: Int): (some?) {
    ensure rule: some? iff (exists (k: Int), k > n)
    --~^ error: this is outside the decidable core: a quantifier over a type whose values cannot be listed
}
```

## Meaning

A quantifier over listed types means the conjunction (`forall`) or
disjunction (`exists`) of its body at every value of its bound names.

**Dynamic semantics**

r[quantifier.meaning.instances]
The *instances* of a quantifier over listed types are its body with each
bound name standing for one value of its type, one instance for each
combination of the bound names' values.

r[quantifier.meaning.expansion]
A `forall` over listed types means the conjunction of its instances, and an
`exists` their disjunction: its *expansion* (`lang::quantifier`).

r[quantifier.meaning.some-instance]
Every quantifier has at least one instance. A `forall` implies the
`exists` of the same body (`lang::forall_implies_exists`).

r[quantifier.meaning.order]
The values of a type are listed in this order: `true`, then `false`; the
variants of an enumeration in their declaration's order, each with every
combination of the values of its payload; every combination of a record's
fields; and the values of a subset type in its base type's order, the
integers increasing.

r[quantifier.meaning.binder-order]
The bound names vary in the order in which they are written, the last
fastest.

r[quantifier.meaning.order-free]
The order changes no meaning. It is the order in which the instances are
conjoined, which the [generated Lean
declarations](../Generated.md#procedures) show.

r[quantifier.meaning.elaboration]
Both front ends expand a quantifier over listed types while elaborating it.
The solver's queries have no quantifier over listed types (see
[Decidability](Decidability.md)), and Lean sees the expansion, with no
`Fintype`.

r[quantifier.meaning.reported-once]
The body is elaborated once. Its errors and lints are reported once, where
it is written, not for each instance.

r[quantifier.meaning.mixed]
In an unbounded quantifier, the bound names of listed types are expanded as
in a quantifier over listed types, within the quantifier over the others.

```fren
pub proc quantifier(
    all?,                    -- `forall`, rather than `exists`
    values: Set<Bool>,       -- the values of its instances
): (det holds?) {
    assume some_instance: values != {}

    ensure rule: holds? iff (if all? then not false in values else true in values)

    expect conjunction: when all?, holds? iff values = {true}
    expect disjunction: unless all?, holds? iff true in values
}

expect forall_implies_exists(a_all?, a_values: Set<Bool>, e_all?, e_values: Set<Bool>) {
    assume a_some_instance: a_values != {}
    assume e_some_instance: e_values != {}
    call a := quantifier(a_all?, a_values)
    call e := quantifier(e_all?, e_values)
    expect forall_implies_exists: when a.all? and not e.all? and a.values = e.values and a.holds?, e.holds?
}
```

**Examples**

- With `enum Method { Len, Card }`, `forall (m: Method), not loud?(m)`
  means `not loud?(Method::Len) and not loud?(Method::Card)`.
- `exists (a? b?: Bool), a? and not b?` is the disjunction of four
  instances, at `(true, true)`, `(true, false)`, `(false, true)` and
  `(false, false)`.
- With `type Octal = n: Int where range: n is 0..=7`, `forall (x: Octal),
  e` has eight instances, for 0 to 7 in increasing order.
- With `type Loud = s: Severity where invariant: s is Severity::Warning |
  Severity::Error`, `forall (s: Loud), e` has two instances, at the
  variants that match, in their declaration's order.

The checker proves that a quantifier over an enumeration means its
expansion:

```fren example
pub enum Method { Len, Card }

proc quiet(len_loud?, card_loud?): (all_quiet?) {
    ensure rule: all_quiet? iff (forall (m: Method), not (if m = Method::Len then len_loud? else card_loud?))

    expect expansion: all_quiet? iff (not len_loud? and not card_loud?)
}
--@ summary: 3 passed, 0 failed, 0 inconclusive, 0 redundant
```

> **Note:** Every type has a value, which is why every quantifier has an
> instance.

### Number of instances

A quantifier is expanded only where it has few enough instances.

r[quantifier.limit]
A quantifier has at most 256 instances. One with more is an error that says
how many it would have (`F0356`, `lang::quantifier_size`).

r[quantifier.limit.count]
The number of instances is the product, over the bound names of listed
types, of the number of values of each one's type.

r[quantifier.limit.values]
`Bool` has two values. An enumeration has the sum, over its variants, of
the product of the numbers of values of a variant's payload, one for a
variant without one. A record has the product of the numbers of values of
its fields. A subset type has as many values as its base type has values
that satisfy its invariants.

r[quantifier.limit.unexpanded]
The numbers are computed without expanding anything.

r[quantifier.limit.nested]
A quantifier in the body of another has as many instances as its own
number multiplied by those of the quantifiers around it.

r[quantifier.limit.not-listed]
A bound name of a type that is not listed is not expanded, and counts once.

```fren
pub const MAX_INSTANCES: Int := 256

pub proc quantifier_size(
    n_instances: Int,        -- the combinations of the values of its bound names and those around it
): (det accepted?) {
    assume some: n_instances >= 1

    ensure rule: accepted? iff n_instances <= MAX_INSTANCES

    expect at_limit: when n_instances = MAX_INSTANCES, accepted?
    expect beyond_limit: when n_instances > MAX_INSTANCES, not accepted?
}
```

**Examples**

- `(a b: T)` counts `T`'s values twice.
- For a `Byte` of 256 values, `forall (a b: Byte), e` and `forall (a:
  Byte), forall (b: Byte), e` are both errors: each would have 65536
  instances of the innermost body.
- `forall (i: Int) (m: Method), e` has as many instances as `forall (m:
  Method), e`.

Nine `Bool`s have 512 combinations of values:

```fren example
proc parity(): (even?) {
    ensure rule: even? iff (forall (a? b? c? d? e? f? g? h? i?: Bool), a? or not a?)
    --~^ error: this quantifier has 512 instances, more than 256
}
```

## Unbounded quantifiers

An unbounded quantifier ranges over infinitely many values. It means what
it says, as in Lean, and the solver decides it when it can.

**Dynamic semantics**

r[quantifier.unbounded.meaning]
`forall (x: T), e` is the proposition that `e` holds for every value of `x`
of type `T`, and `exists (x: T), e` that it holds for some.

r[quantifier.unbounded.subset]
A bound name of a [subset type](SubsetTypes.md) ranges over the values of
the subset type, as a variable's does.

r[quantifier.unbounded.nat]
A bound name of type `Nat` ranges over the integers at least 0. `forall (n:
Nat), e` is `forall (n: Int), when n >= 0, e`, and `exists (n: Nat), e` is
`exists (n: Int), n >= 0 and e`.

r[quantifier.unbounded.listed-names]
The bound names of listed types are expanded within an unbounded quantifier
(`quantifier.meaning.mixed`): `forall (i: Int) (m: Method), e` is `forall
(i: Int), e1 and e2`, where `e1` and `e2` are the body's instances at the
two methods.

r[quantifier.unbounded.only-form]
There is no other form of quantifier. A quantifier over the members of a
set or the positions of a sequence is written with a guard, which bounds it
(see [Guards](#guards)).

r[quantifier.unbounded.elements]
A quantifier over a sequence's elements whose bound name is used only as a
value is in the decidable core, and each query expands it (see
[Quantifiers over elements](ElementQuantifiers.md)).

```text
forall (x: T), when x in q, p(x)                 -- over the elements of a sequence
forall (x: T), when x in s, p(x)                 -- over the members of a set
exists (i: Int), 0 <= i < q.len and q[i] = x     -- over the positions of a sequence
forall (x: T), law(x)                            -- over a type
```

**In Lean and the solver**

r[quantifier.unbounded.lean]
Neither front end expands an unbounded quantifier. In Lean it is a `∀` or
`∃`, a `Prop`.

r[quantifier.unbounded.solver]
Both front ends give the solver a quantifier, `(forall ((x T)) e)` or
`(exists ((x T)) e)`, which declares the bound name at its type's sort and
nothing else (see [Solver queries](../Cli.md#solver-queries)).

r[quantifier.unbounded.lint]
The `undecidable` lint reports each binder of a type that is not listed, at
the binder. A spec that allows the lint there opts out of the decidable core
at that quantifier.

r[quantifier.unbounded.verdicts]
The checks of an unbounded quantifier are asked of the solver, and are
`Inconclusive` where it does not decide them. They may be
[tested](../Check.md#checking-by-testing) instead, where the evaluator can
evaluate the quantifier (see [Evaluation](../Eval.md#quantifiers)), or a
procedure's evidence may be a `trusted` claim.

r[quantifier.unbounded.contracts]
Within an unbounded quantifier's body, an application of a function whose
arguments mention one of its bound names brings the facts that an
application brings elsewhere (see
[Contracts](../Check.md#contracts-of-uninterpreted-functions)): a `Nat`
result is at least 0, the result satisfies the invariants of its subset
type, and the function's postconditions hold where its preconditions do.

r[quantifier.unbounded.contracts.quantified]
Each such fact is stated for every value of the bound names that the
application mentions, under the solver's quantifier over them, without the
guard. Both front ends state the same facts.

**Examples**

For `forall (i: Int), when 0 <= i < n, h(i) >= 0`, with `fn h(Int): Nat`,
the queries assume `(forall ((|i'0| Int)) (>= (h |i'0|) 0))`, and Lean
assumes `∀ i'0, 0 ≤ ↑(h i'0)`.

> **Note:** A precise spec is written beside a decidable one. A procedure
> that states a rule over any number of things, with unbounded quantifiers,
> is bound by an [implementation](../Impl.md) to the code and proved in
> Lean, where each `forall` is a `∀` of the theorem. A bounded model of it,
> over a listed type, stays in the decidable core, where `decide` checks
> its implementation. `lint::manual_at_most_one_any` and
> `lint::manual_at_most_one` are such a pair (see
> [Cardinality](../Lint/Complexity/Operators.md#cardinality)). Where a proof
> is out of reach, a [refinement](Refinement.md#evidence) whose evidence is
> testing relates the two, and testing evaluates the quantifiers where they
> have [domains](#guards).

> **Note:** A contract's fact holds whatever the arguments, which is why
> it is stated without the guard.

## Guards

The guard of a quantifier is what its body first says about its bound
names. It gives a bound name a domain, which the evaluator enumerates and
which tells the solver that the quantifier is bounded. It does not change
what the quantifier means.

### Conjuncts and bounds

r[quantifier.guard.forall]
The *guard* of a `forall` is the conditions of the `when`s at the top of its
body. An `unless`, a `let` or any other expression ends it.

r[quantifier.guard.exists]
The guard of an `exists` is its body.

r[quantifier.guard.conjuncts]
A guard's *conjuncts* are the operands of the `and`s at its top, in order,
with their parentheses removed. A [chained
comparison](Expressions.md#chained-comparisons) is a conjunct of each of its
comparisons.

r[quantifier.guard.bound]
A conjunct gives a *bound* to each bound name `x` of a type that is not
listed: `x in e` gives its members; `x >= e`, `x > e`, `e <= x` and `e < x`
a lower bound; and `x <= e`, `x < e`, `e >= x` and `e > x` an upper bound.
Here `x` is the bound name alone (`quantifier.guard.name`), and `e` is free
of `x` (`quantifier.guard.free`). Any other conjunct gives no bound.

r[quantifier.guard.free]
An operand is *free* of `x` when it names neither `x` nor a bound name
declared after `x` in the same quantifier. A name of one segment, the root
of a dotted name, and a field of a record literal written without `:=` each
name the bound name that they spell, whatever shadows it.

r[quantifier.guard.operand]
Seen from `x`, an operand is `x` itself (`Name`), free of `x` (`Free`), or
any other (`Later`). `lang::guard_bound` states the bound from a conjunct's
operands, `lhs` and `rhs`, and its relation.

r[quantifier.guard.strict]
A bound by `<` or `>` is *strict*: the bound itself is not in range.

```fren
-- An operand of a conjunct, seen from a bound name `x`.
pub enum GuardOperand { Name, Free, Later }

-- The relation of a conjunct: a comparison, `in`, or anything else
-- (`Other`), whose operands are then irrelevant.
pub enum GuardRelation { Lt, Le, Gt, Ge, In, Other }

pub enum GuardBound { Members, Lower, Upper, NoBound }

-- The bound that `lhs relation rhs` gives.
fn guard_bound_of(lhs: GuardOperand, relation: GuardRelation, rhs: GuardOperand): GuardBound := table {
    lhs = GuardOperand::Name and relation = GuardRelation::In and rhs = GuardOperand::Free => GuardBound::Members,
    (lhs = GuardOperand::Name and relation in {GuardRelation::Gt, GuardRelation::Ge} and rhs = GuardOperand::Free)
        or (lhs = GuardOperand::Free and relation in {GuardRelation::Lt, GuardRelation::Le} and rhs = GuardOperand::Name)
        => GuardBound::Lower,
    (lhs = GuardOperand::Name and relation in {GuardRelation::Lt, GuardRelation::Le} and rhs = GuardOperand::Free)
        or (lhs = GuardOperand::Free and relation in {GuardRelation::Gt, GuardRelation::Ge} and rhs = GuardOperand::Name)
        => GuardBound::Upper,
    _ => GuardBound::NoBound,
}

pub proc guard_bound(lhs: GuardOperand, relation: GuardRelation, rhs: GuardOperand): (
    det bound: GuardBound,
    det strict?,             -- the bound itself is not in range
) {
    use self::GuardBound::{Members, NoBound}
    use self::GuardOperand::Name
    use self::GuardRelation::{Gt, In, Lt}

    ensure rule: bound = guard_bound_of(lhs, relation, rhs)
    ensure strictness: strict? iff relation in {Lt, Gt}

    expect members_by_in: when bound = Members, relation = In
    expect name_alone: when bound != NoBound, (lhs = Name) != (rhs = Name)
}
```

**Examples**

- `forall (x: T), when c, when d, e` has the guard `c` and `d`.
- `exists (x: T), a and b` has the guard `a and b`.
- `when 0 <= i < q.len and i != k, e` has the conjuncts `0 <= i`, `i <
  q.len` and `i != k`. The first gives `i` a lower bound, the second a
  strict upper bound, and the third no bound.
- `exists (x: T), not (a and b)` has the one conjunct `not (a and b)`.

### Newtypes

r[quantifier.guard.name]
A bound name's field `0`, where its type is a [newtype](Items.md#newtypes),
is the bound name itself, and so on through nested newtypes. Any other
field read from a bound name, and a field `0` read from a type that is not
a newtype, is not the name (`lang::name_alone`).

r[quantifier.guard.name.members]
A membership read through such fields gives the members as the name's
values.

r[quantifier.guard.name.shared]
Both front ends ask `lang::name_alone` of the bound name's type
(`nameAlone` in `FrenCore.Quantifier`). Each computes only which bound name
an operand reads and its fields' names: the `fren` command from a path such
as `m.0`, and the hosted front end from the field projections that
elaboration writes, which are the same for `m.0` as for an ordering of a
newtype.

r[quantifier.guard.name.elaborators]
The elaborators read no field as the name: they set `fmf-bound` from the
guard's shape alone (`quantifier.guard.fmf-bound`).

`lang::name_alone` is stated over the type model of [Types](Types.md#types):
from the position of the bound name that an operand reads, or -1, its type
and the underlying type of each newtype it is, and the fields read from
it, outermost last. It gives the position that `GuardSide`'s `alone` holds.

```fren
set_option fren.lint.undecidable "allow" in
pub proc name_alone(
    base: Int,             -- the position of the bound name read, or -1
    types: Seq<Ty>,        -- its type, then each newtype's underlying type
    fields: Seq<String>,   -- the fields read from it, outermost last
): (det alone: Int) {
    assume position: base >= -1
    assume typed: types != []
    assume wrapped: forall (i: Int), when 0 <= i < types.len - 1,
        newtype?(types[i]) and under(types[i]) = types[i + 1]
    assume erased: not newtype?(types[types.len - 1])

    ensure rule: alone = (if fields.len < types.len
        and (forall (i: Int), when 0 <= i < fields.len, fields[i] = "0") then base else -1)

    expect itself: when fields = [], alone = base
    expect through_a_newtype: when types.len = 2 and fields = ["0"], alone = base
    expect not_a_newtype: when types.len = 1 and fields = ["0"], alone = -1
    expect other_field: when fields = ["x"], alone = -1
}
```

**Examples**

- For a newtype `Ms` over `Int`, `0 <= m.0 < 2` bounds `m` as `Ms(0) <= m <
  Ms(2)` does.
- `m.0.0` is `m` where `m`'s type is a newtype over a newtype.
- `p.x` is not the name `p`.
- In `m.0 in {0, 1}`, `m` ranges over `Ms(0)` and `Ms(1)`.

### Domains

r[quantifier.guard.nat-floor]
Where the guard gives a bound name only an upper bound, its range starts
from 0 if its values are naturals: a `Nat`, or a newtype over one
(`lang::nat_floor`, which gives `lang::guard_domain`'s `nat?`).

r[quantifier.guard.nat-floor.shared]
Both front ends' evaluators ask `lang::nat_floor` (`startsAtZero` in
`FrenCore.Quantifier`). The elaborators take `nat?` only of a name declared
`Nat`.

r[quantifier.guard.domain]
A bound name's *domain* comes from its conjuncts' bounds, in order: its
members, from the first conjunct that gives them; otherwise a range, from
the first conjunct that gives a lower bound and the first that gives an
upper bound, starting from 0 for a name whose values are naturals and that
has no lower bound; otherwise none (`lang::guard_domain`).

r[quantifier.guard.domain.inputs]
`lang::guard_domain` is computed from the conjuncts as written: each side
of each, with the position of the bound name that it is, written alone, and
those of the bound names that it names. Each front end reads only these of
a conjunct's syntax. The bound names and the conjuncts are named by their
positions, from 0.

```fren
set_option fren.lint.undecidable "allow" in
pub proc nat_floor(
    types: Seq<Ty>,    -- the bound name's type, then each newtype's underlying type
): (nat?) {
    use self::ValueType::{IntTy, NatTy}

    assume typed: types != []
    assume wrapped: forall (i: Int), when 0 <= i < types.len - 1,
        newtype?(types[i]) and under(types[i]) = types[i + 1]
    assume erased: not newtype?(types[types.len - 1])

    out nat? := kind(types[types.len - 1]) = NatTy

    expect nats: when types.len = 1 and kind(types[0]) = NatTy, nat?
    expect newtype_over_nat: when types.len = 2 and kind(types[1]) = NatTy, nat?
    expect ints: when kind(types[types.len - 1]) = IntTy, not nat?
}
```

```fren
-- A side of a conjunct: the position of the bound name that it is, written
-- alone, or -1 if it is none; and the positions of the bound names that it
-- names.
pub struct GuardSide { alone: Int, names: Seq<Int> }

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
fn none_before?(cs: Seq<GuardConjunct>, k: Int, b: GuardBound, n: Int) :=
    forall (j: Int), when 0 <= j < n, conjunct_bound(cs[j], k) != b

-- The conjunct at position `j` gives the bound name at `k` the bound `b`,
-- and none before it does.
set_option fren.lint.undecidable "allow" in
fn first_at?(cs: Seq<GuardConjunct>, k: Int, b: GuardBound, j: Int) :=
    conjunct_bound(cs[j], k) = b and none_before?(cs, k, b, j)

-- `Members`: the members of the conjunct at `lo`. `Range`: from the lower
-- bound at `lo` to the upper bound at `hi`. `FromZero`: from 0 to the upper
-- bound at `hi`. `Unbounded`: no domain.
pub enum DomainShape { Members, Range, FromZero, Unbounded }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc guard_domain(
    conjuncts: Seq<GuardConjunct>,    -- the conjuncts of the guard, in order
    k: Nat,                           -- the position of the bound name
    nat?,                             -- its values are naturals (`lang::nat_floor`)
): (
    det shape: DomainShape,
    det lo: Int,                      -- the position of the conjunct that gives the members or the lower bound, or -1
    det hi: Int,                      -- the position of the conjunct that gives the upper bound, or -1
) {
    use self::GuardBound::{Lower, Members, Upper}

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

**Examples**

`n < Ns(10)` and `n.0 < 10` both give a bound name `n` of a newtype `Ns`
over `Nat` the values from `Ns(0)` to `Ns(9)`.

### Ranges

r[quantifier.guard.range]
A membership bounds a bound name of any type. A comparison bounds one only
where its type is `Int`, `Nat`, or a [newtype](Items.md#newtypes) over
them, a [pattern type](Types.md#subset-types) counting as its base type
(`lang::range_domain`).

r[quantifier.guard.range.other]
For evaluation and enumeration, a comparison of a bound name of any other
type gives it no bound. Without a membership, it then has no domain, and
both [evaluation](../Eval.md#quantifiers) and
[enumeration](../Check.md#quantifiers-up-to-the-bound) read it as any other
bound name without a domain.

r[quantifier.guard.range.shared]
Both front ends ask `lang::range_domain` (`countedBetween` in
`FrenCore.Quantifier`). It is stated over the type model of
[Types](Types.md#types), from the bound name's type and the underlying type
of each newtype it is, from the outermost in: each but the last is a
newtype whose `under` is the next, and the last, not a newtype, is the type
of the values that the comparison compares.

```fren
set_option fren.lint.undecidable "allow" in
pub proc range_domain(
    types: Seq<Ty>,    -- the bound name's type, then each newtype's underlying type
): (ranged?) {
    use self::ValueType::{IntTy, NatTy, RecordTy, StringTy}

    assume typed: types != []
    assume wrapped: forall (i: Int), when 0 <= i < types.len - 1,
        newtype?(types[i]) and under(types[i]) = types[i + 1]
    assume erased: not newtype?(types[types.len - 1])

    out ranged? := kind(types[types.len - 1]) in {IntTy, NatTy}

    expect ints: when types.len = 1 and kind(types[0]) = IntTy, ranged?
    expect nats: when types.len = 1 and kind(types[0]) = NatTy, ranged?
    expect strings: when types.len = 1 and kind(types[0]) = StringTy, not ranged?
    expect records: when types.len = 1 and kind(types[0]) = RecordTy, not ranged?
    expect newtype_over_int: when types.len = 2 and kind(types[1]) = IntTy, ranged?
    expect newtype_over_string: when types.len = 2 and kind(types[1]) = StringTy, not ranged?
}
```

> **Rationale:** Only the integers have finitely many values between any
> two bounds, whatever they are, so that the type alone says that a range
> can be enumerated. Between `"a"` and `"b"` lie `"aa"`, `"aaa"` and every
> other string that starts with `"a"`. An [ordered
> record](Items.md#ordered-declarations)'s values are compared
> lexicographically, so between `P(0, 0)` and `P(1, 0)` lies `P(0, n)` for
> every `n`. An ordered enumeration's are compared by their variants'
> positions, which say nothing of their payloads (#368).

### Meaning and the solver

r[quantifier.guard.meaning]
A quantifier's guard does not change its meaning, which is the same however
it is written.

r[quantifier.guard.evaluation]
A domain lets the evaluator enumerate the values at which the guard can hold
(see [Evaluation](../Eval.md#quantifiers)).

r[quantifier.guard.fmf-bound]
A procedure, global expectation or refinement whose queries have an
unbounded quantifier with a bound name that has a domain sets cvc5's
`fmf-bound` (see [Solver queries](../Cli.md#solver-queries)). `fmf-bound`
is set from the shape of the guard alone (`lang::guard_domain`), whatever
the bound name's type. `lang::range_domain` says only which ranges the
evaluators enumerate.

> **Note:** With `fmf-bound`, cvc5 finds models of quantifiers bounded by
> membership and by integer ranges.

## Names

A bound name is a local name of the body, which may shadow another name.

**Legality rules**

r[quantifier.name.scope]
A bound name is in scope in the body, and nowhere else.

r[quantifier.name.distinct]
The names of one quantifier, across all of its binders, are
[distinct](Items.md#distinct-names) (`F0213`).

r[quantifier.name.boolean]
A bound name follows the [Boolean names](Types.md#boolean-names) rule for
its type: `forall (b?: Bool)`, and `forall (m: Method)`.

r[quantifier.name.shadowing]
A bound name may [shadow](Procedures.md#shadowing) another, written with
`!`: a variable, a parameter, a call, a binder of a pattern, a bound name
of an enclosing quantifier, a constant, a function or a variant. A mention
of it in the body is not a mention of what it shadows.

r[quantifier.name.mentions.listed]
A bound name of a listed type [mentions](Expressions.md#mentions) nothing.

r[quantifier.name.mentions.unbounded]
Within the body, a bound name of a type that is not listed mentions itself,
as a variable does.

r[quantifier.name.mentions.quantifier]
A quantifier mentions what its body mentions, but not its own bound names.

**Examples**

- `forall (m!: Method), ...` within a procedure with a variable `m`.
- `forall (m: Method), f(m)` is allowed wherever `f` of a constant is, and
  so is `2 * cost(m)`.
- With `i` an `Int` bound name, `2 * i` is linear, but `n * i`, with `n` a
  variable, is a product of two variables, an error, as `n * m` is (see
  [Linear arithmetic](Expressions.md#linear-arithmetic)).

```fren example
pub enum Mode { Off, On }

proc pairs(): (distinct?) {
    ensure rule: distinct? iff (forall (m: Mode) (m: Mode), m = m)
    --~^ error: `m` is bound multiple times in this quantifier
}
```

### Indices

r[quantifier.index.instances]
An index in the body is [guarded](Expressions.md#sequences) in each
instance by the conditions before it within the body, and by those around
the quantifier. The instances do not guard each other: the definedness
check reports an index that may be out of range in some instance where its
guard holds.

r[quantifier.index.unbounded]
In an unbounded quantifier, an index must be in range for every value of
the bound names where its guard holds, whether the quantifier is a `forall`
or an `exists`. Its definedness is quantified as the body is.

r[quantifier.index.trigger]
A quantifier at the top of a constraint is not a `when`. The constraint has
no [trigger](Procedures.md#triggers).

**Examples**

In `exists (i: Int), 0 <= i < q.len and q[i] = x`, the goal is that `q[i]`
is in range for every `i` with `0 <= i < q.len`, which holds.

## Global expectations

A quantifier ranges over values, never over the behaviours of a
procedure, which a global expectation relates.

r[quantifier.global.short-form]
A [global expectation's](Global.md) short form, `expect n: forall (m:
Method), E`, is a quantifier like any other, around `E` with any `where`
clause.

r[quantifier.binder.procedure]
A binder whose type names a procedure is an error (`F0210`), whose help
says to call the procedure in a global expectation instead
(`lang::quantifier_binder`).

```fren
-- `TypeName` is a type, listed or not, and `Component` a procedure.
pub enum BinderTarget { TypeName, Component }

set_option fren.evidence "enumerated" in
pub proc quantifier_binder(target: BinderTarget): (det accepted?) {
    use self::BinderTarget::{Component, TypeName}

    ensure rule: accepted? iff target = TypeName

    expect values_only: when target = Component, not accepted?
}
```

```fren example
proc heats(): (on?) {
    ensure rule: on?
}

proc cools(): (any?) {
    ensure rule: any? iff (exists (h: heats), true)
    --~^ error: expected a type, but `heats` is a procedure
}
```
