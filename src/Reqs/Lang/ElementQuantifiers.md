# Quantifiers over elements

A quantifier over a sequence's elements, written with a guard that bounds
it (see [Guards](Quantifiers.md#guards)), is in the decidable core:

```text
ensure all_positive: forall (x: Int), when x in q, positive?(x)
ensure some_late: exists (t: Event), t in log and t.time > deadline
```

Its meaning is that of any [unbounded
quantifier](Quantifiers.md#unbounded-quantifiers): `forall (x: T), when x in
q, P` holds if `P` holds of every element of `q`, and in Lean it is `∀ x, x ∈
q → P`. What sets it apart is that both front ends expand it, at each
query, into instances at finitely many positions of `q`, so that the
query stays quantifier-free, as [rule 1](Decidability.md#what-is-promised)
promises. There is no syntax of its own: the user's decision on #234 is
that Fren has no quantifier constructs for collections, so this is the
guarded `forall` of #259, recognized.

## Why it is decidable

For sequences, the decidable fragment is the *array property fragment* of
Bradley, Manna and Sipma ("What's decidable about arrays?", VMCAI 2006):
formulas `forall i, G(i) => V(a[i])`, where the bound index `i` is used
only as an index, the guard `G` is linear, and quantifiers do not
alternate. Its decidability proof gives, for each query, a finite *index
set* at which instantiating the quantifier is enough.

`forall (x: T), when x in q, P(x)` means `forall i, 0 <= i < q.len =>
P(q[i])`, and `exists (x: T), x in q and P(x)` its dual. Its guard is linear,
and where `x` is used in `P` only as a value, never as an index, the
quantified position `i` is used only as the index of `q`: the quantifier is
in the fragment by its form. `lang::element_meaning` states the two meanings
the same, over a sequence of integers and the set `good` of the elements at
which `P` holds:

```fren
pub mod lang

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp element_meaning {
    in q: Seq(Int)
    in good: Set(Int)
    pub det out holds?

    ensure by_elements: holds? iff (forall (x: Int), when x in q, x in good)
    ensure by_positions: holds? iff (forall (i: Int), when 0 <= i < q.len, q[i] in good)
}
```

This component, and the others of this chapter, state rules over any
number of things, with quantifiers that are outside the core, as a precise
spec does (see [Unbounded quantifiers](Quantifiers.md#unbounded-quantifiers)):
each is bound by an [implementation](../Impl.md) proved in Lean for every
input, and its own checks are [tested](../Check.md#checking-by-testing),
since beside a quantifier that is not expanded, the solver's model of an
expansion may not be confirmed (see [Expansion](#expansion)).

## The shape

A quantifier is a *quantifier over elements* when each of its bound names
of a type that is not [listed](Quantifiers.md#types) has, as its
[domain](Quantifiers.md#guards), the members of a conjunct `x in e` of its
guard, and no earlier conjunct names it: its guard starts, for that name,
with its membership. Other conjuncts may come before it, if they do not
name it, and after it. It is in the decidable core when, besides:

- `e` is a sequence, not a set or a relation (see [Sets](#sets));
- `e` mentions no bound name of the same quantifier, nor one of an
  enclosing quantifier of a type that is not listed: a sequence within the
  element is a nested array, outside the fragment;
- `e` mentions no output that is not [defined](Components.md#defined-outputs),
  directly or through a definition: the realizability check quantifies over
  such outputs, and the quantifier would be within that quantifier;
- the body uses `x` only as a value. A *use* of `x` is a place where the
  body mentions it, or a name that the body declares, which may stand for
  it: as the index `r[i]`, or the position of `r.update(i, v)`, `r.at(i)` or
  `r.slice(i, n)`, of a sequence `r` that is not a
  [constant](Decidability.md#strings) (`Index`); in an argument of a defined
  function with a parameter whose type has a sequence within it, which may
  use the argument as an index (`SeqArgument`); in the members of the guard
  of a quantifier within the body (`Receiver`); or in an argument of an
  uninterpreted function whose applications bring
  [facts](Quantifiers.md#unbounded-quantifiers), which would be stated for
  every element (`FactArgument`). Any other mention is a `Value`;
- it is within no quantifier over elements, or is directly the body of one
  of the same kind: the body of a `forall` under its `when`s, or the last
  conjunct of an `exists`'s body. Elsewhere within one, the two may
  alternate, as `forall` and `exists` do in `forall (x: T), when x in q,
  exists (y: T), y in r and x = y`, which is outside the fragment.

Two bound names, `forall (x y: Int), when x in q and y in r, x < y`, and
two quantifiers one directly within the other, `forall (x: Int), when x in
q, forall (y: Int), when y in r, x < y`, are both in the core. The body
itself is held to the core as any expression is, with `x` a variable, and a
sequence outside the core, as `a ++ b` in `when x in a ++ b`, is reported
where it is written.

`lang::element_quantifier` states the verdict, from what both front ends
read of each bound name of a type that is not listed, in order, and from
where the quantifier is. It is in the core if every bound name is, and it
is not nested otherwise; else the verdict is the first bound name's reason,
in this order, or `Nested`:

```fren
-- How the body uses a bound name, at one place.
pub enum ElementUse { Value, Index, SeqArgument, Receiver, FactArgument }

-- What a bound name's domain is: a sequence's elements, a set's members, or neither.
pub enum ElementMembers { Sequence, SetOrRelation, Neither }

pub struct ElementBinder {
    members: ElementMembers,
    receiver_bound?,             -- its sequence mentions a bound name
    receiver_output?,            -- its sequence mentions an output that is not defined
    uses: Set(ElementUse),       -- how the body uses it
}

-- Within no quantifier over elements, directly the body of one of the same kind, or elsewhere within one.
pub enum ElementNesting { Top, Direct, Other }

pub enum ElementVerdict { InCore, NotMembers, SetMembers, ReceiverBound, ReceiverOutput, Used(ElementUse), Nested }

-- The verdict of one bound name.
fn binder_verdict(b: ElementBinder): ElementVerdict := match b.members {
    ElementMembers::Neither => ElementVerdict::NotMembers,
    ElementMembers::SetOrRelation => ElementVerdict::SetMembers,
    ElementMembers::Sequence =>
        if b.receiver_bound? then ElementVerdict::ReceiverBound
        else if b.receiver_output? then ElementVerdict::ReceiverOutput
        else if ElementUse::Index in b.uses then ElementVerdict::Used(ElementUse::Index)
        else if ElementUse::SeqArgument in b.uses then ElementVerdict::Used(ElementUse::SeqArgument)
        else if ElementUse::Receiver in b.uses then ElementVerdict::Used(ElementUse::Receiver)
        else if ElementUse::FactArgument in b.uses then ElementVerdict::Used(ElementUse::FactArgument)
        else ElementVerdict::InCore,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp element_quantifier {
    use self::ElementVerdict::{InCore, Nested}
    in binders: Seq(ElementBinder)  -- its bound names of types that are not listed, in order
    in nesting: ElementNesting
    pub det out verdict: ElementVerdict

    ensure first: forall (j: Int), when 0 <= j < binders.len and binder_verdict(binders[j]) != InCore
        and (forall (i: Int), when 0 <= i < j, binder_verdict(binders[i]) = InCore),
        verdict = binder_verdict(binders[j])
    ensure nested: when (forall (b: ElementBinder), when b in binders, binder_verdict(b) = InCore),
        verdict = (if nesting = ElementNesting::Other then Nested else InCore)
}
```

A quantifier that is not in the core is reported by the [`undecidable`
lint](../Lint/Decidability.md#undecidable-constructs) at each binder of a
type that is not listed, with the reason (`F0714`), and so is its guard's
`x in e`, which is outside the core as a membership of a sequence that is
not a literal ([Sequences](Decidability.md#sequences)). One whose verdict is
`NotMembers` is #259's unbounded quantifier, reported as it was. One in the
core is reported for neither.

## Sets

`forall (x: T), when x in s, P(x)` over a set `s` stays outside the core,
with the verdict `SetMembers`. The theory of sets with cardinality is
decided by cvc5's procedure for *quantifier-free* formulas of Boolean
algebra with Presburger arithmetic (Bansal, Reynolds, Barrett and
Tinelli, "A new decision procedure for finite sets and cardinality
constraints in SMT", IJCAR 2016), and no decision procedure for those
formulas together with quantifiers over the members and `card` is cited
here. Expanding over finitely many members, as for a sequence, would need a
bound on the members that are not named, which `card` breaks: `card(s) >
n` asks for members that no term names.

## Expansion

Each query expands its quantifiers over elements before anything is
asked, after the definitions of defined functions are unfolded, so that a
quantifier in a function's body is expanded where the function is applied.
The *index set* of a query is, after Bradley, Manna and Sipma, the terms:

- `0`;
- `e.len - 1`, for the sequence `e` of each quantifier, its last position;
- each index `r[i]` in the query, of any sequence, whose position `i`
  mentions no bound name;
- for each `r.update(i, v)` whose position mentions no bound name, `i - 1`,
  `i` and `i + 1`, the terms that an update's elimination into reads gives;
- a fresh *witness* for each bound name of each quantifier, and for each
  equation `a = b` between sequences of which one is a quantifier's: an
  `Int` that nothing constrains.

each once, in that order. `lang::index_set` states it, over the terms as
an abstract type, with `index_set?` saying whether `terms` is the index set of
the others:

```fren
pub type IndexTerm

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp index_set {
    in zero: IndexTerm
    in lasts: Seq(IndexTerm)       -- each quantifier's sequence's last position
    in reads: Seq(IndexTerm)       -- each index's position
    in positions: Seq(IndexTerm)   -- each update's position
    in before: Seq(IndexTerm)      -- each update's position less one
    in after: Seq(IndexTerm)       -- each update's position plus one
    in witnesses: Seq(IndexTerm)
    in terms: Seq(IndexTerm)       -- the index set
    assume neighbours: before.len = positions.len and after.len = positions.len
    pub det out index_set?         -- `terms` is the index set of the others

    ensure rule: index_set? iff (terms != [] and terms[0] = zero
        and (forall (t: IndexTerm), when t in lasts, t in terms)
        and (forall (t: IndexTerm), when t in reads, t in terms)
        and (forall (i: Int), when 0 <= i < positions.len, before[i] in terms and positions[i] in terms and after[i] in terms)
        and (forall (t: IndexTerm), when t in witnesses, t in terms)
        and (forall (t: IndexTerm), when t in terms, t = zero or t in lasts or t in reads or t in positions or t in before
            or t in after or t in witnesses)
        and (forall (i j: Int), when 0 <= i < j < terms.len, terms[i] != terms[j]))
}
```

A quantifier with `n` bound names is replaced by one instance for each
`n`-tuple of the index set, the last name varying fastest, as a quantifier
over listed types is: the body with each bound name `x` replaced by `e[t]`,
where `e` is its sequence and `t` its term in the tuple, and its membership
`x in e` in the guard replaced by `0 <= t < e.len`. A `forall` is the
conjunction of its instances, and an `exists` their disjunction. A bound
name that the body does not mention takes no term. A quantifier in the body
of another is expanded within each of its instances, over the same index
set, with the same witnesses.

Each instance is implied by the quantifier, so a `forall` is replaced by
something weaker, and an `exists` by something stronger only by naming its
witness. Since a witness is in the index set, the replacement holds in a
model exactly where the quantifier does, whatever the position of the
quantifier in the query: under `not`, in either side of `iff`, or in a
hypothesis or the goal. So an unsatisfiable expansion means an
unsatisfiable query. The converse is the fragment's completeness: a model
of the expansion becomes a model of the query when each element of each
sequence is replaced by the element at the last value of the index set at
or before its position. Reads at the index set and lengths do not change;
an update at a position whose successor is in the index set commutes with
the replacement; two sequences that differ differ at the witness of their
equation, which survives it; and every element is then one at which an
instance holds. `lang::element_projection` states it, for one sequence of
integers, the values `ix` of the index set's terms in a model, and the set
`good` at which the body holds, with `projection?` saying whether `projected`
and `updated` are made so:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp element_projection {
    in q: Seq(Int)
    in ix: Seq(Int)             -- the values of the index set's terms
    in good: Set(Int)           -- the elements at which the body holds
    in i: Int                   -- the position of an update
    in v: Int                   -- its value
    in projected: Seq(Int)      -- each element replaced by the element at the last value of `ix` at or before its position
    in updated: Seq(Int)        -- the same of `q.update(i, v)`
    assume zero: 0 in ix
    pub det out projection?     -- `projected` and `updated` are made so

    ensure rule: projection? iff (projected.len = q.len
        and (forall (t: Int), when t in ix and 0 <= t < q.len, projected[t] = q[t])
        and (when (forall (t: Int), when t in ix and 0 <= t < q.len, q[t] in good),
            forall (x: Int), when x in projected, x in good)
        and (when i in ix and i + 1 in ix and 0 <= i < q.len, updated = projected.update(i, v)))
}
```

A model of the expansion is not a model of the query, and its
counterexample may show elements outside the index set that the quantifier
rules out. So when the expanded query is satisfiable, it is asked again,
with each quantifier's sequence's length pinned to its length in the model
and each quantifier instantiated at every position below it, rather than
at the index set: at those lengths, that query means exactly the
quantified one, so its model, which the check reports, is a real one. By
completeness, it is satisfiable whenever the first is. If it is not, the
check is inconclusive (`F0648`): an equation between sequences of which
neither is a quantifier's can make it so.

A sequence of a quantifier that mentions a name bound around it, as an
output in the realizability check's `∃` may be, is not expanded: the
quantifier is given to the solver as written. Such a quantifier is outside
the core, by `ReceiverOutput`.

Both front ends expand the same quantifiers over the same index set: the
binary on the SMT-LIB of each query, and the Lean-hosted front end on the
Lean terms that it gives lean-smt, where the quantifier is marked. The
generated Lean declarations are unchanged: they state the quantifier.

## Size

A query's expansion has at most 256 instances in all, counting each
instance of a quantifier within another's instance: a query with more is
not asked, and its check is inconclusive with a message that says so
(`F0647`). The index set grows with the indexes in the query,
and an instance's count is the index set's size to the power of the
quantifier's bound names, so the limit is reached by many indexes, not by
long sequences. The second query counts its positions instead.
`lang::element_size` states the limit:

```fren
pub const MAX_ELEMENT_INSTANCES: Int := 256

pub comp element_size {
    in n_instances: Int      -- the instances of a query's quantifiers over elements
    pub det out accepted?

    ensure rule: accepted? iff n_instances <= MAX_ELEMENT_INSTANCES

    expect at_limit: when n_instances = MAX_ELEMENT_INSTANCES, accepted?
    expect beyond_limit: when n_instances > MAX_ELEMENT_INSTANCES, not accepted?
}
```
