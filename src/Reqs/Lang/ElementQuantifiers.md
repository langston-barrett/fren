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
set_option fren.evidence "random" in
pub proc element_meaning(q: Seq<Int>, good: Set<Int>): (det holds?) {
    ensure by_elements: holds? iff (forall (x: Int), when x in q, x in good)
    ensure by_positions: holds? iff (forall (i: Int), when 0 <= i < q.len, q[i] in good)
}
```

This procedure, and the others of this chapter, state rules over any
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
  every element (`FactArgument`); or in an argument of a defined function
  whose body has a quantifier over a type that is not listed, directly or
  through another, which once the body is unfolded is within this one
  (`QuantifiedArgument`). Any other mention is a `Value`;
- neither `e` nor the body mentions an output that is not
  [defined](Procedures.md#definitions), directly or through a
  definition: the realizability check quantifies over such outputs, and
  this quantifier would alternate with that one;
- it is within no quantifier over elements, or is directly the body of one
  of the same kind: the body of a `forall` under its `when`s, or the last
  conjunct of an `exists`'s body. Elsewhere within one, the two may
  alternate, as `forall` and `exists` do in `forall (x: T), when x in q,
  exists (y: T), y in r and x = y`, which is outside the fragment;
- its body mentions no bound name of a quantifier around it, other than
  of the quantifiers of the same kind that it is directly the body of: a
  witness of the quantifier is one name for the whole query, which must not
  depend on such a name.

Two bound names, `forall (x y: Int), when x in q and y in r, x < y`, and
two quantifiers one directly within the other, `forall (x: Int), when x in
q, forall (y: Int), when y in r, x < y`, are both in the core. The body
itself is held to the core as any expression is, with `x` a variable, and a
sequence outside the core, as `a ++ b` in `when x in a ++ b`, is reported
where it is written.

`lang::element_quantifier` states the verdict, from what both front ends
read of each bound name of a type that is not listed, in order, and from
where the quantifier is and what it mentions. It is in the core if every
bound name is and none of the rest holds; else the verdict is the first
bound name's reason, in this order, or else `MentionsOutput`, `Nested` or
`MentionsBound`, in that order:

```fren
-- How the body uses a bound name, at one place.
pub enum ElementUse { Value, Index, SeqArgument, Receiver, FactArgument, QuantifiedArgument }

-- What a bound name's domain is: a sequence's elements, a set's members, or neither.
pub enum ElementMembers { Sequence, SetOrRelation, Neither }

pub struct ElementBinder {
    members: ElementMembers,
    receiver_bound?,             -- its sequence mentions a bound name
    uses: Set<ElementUse>,       -- how the body uses it
}

-- Within no quantifier over elements, directly the body of one of the same kind, or elsewhere within one.
pub enum ElementNesting { Top, Direct, Other }

pub enum ElementVerdict {
    InCore, NotMembers, SetMembers, ReceiverBound, MentionsOutput, MentionsBound, Used(ElementUse), Nested,
}

-- The verdict of one bound name.
fn binder_verdict(b: ElementBinder): ElementVerdict := match b.members {
    ElementMembers::Neither => ElementVerdict::NotMembers,
    ElementMembers::SetOrRelation => ElementVerdict::SetMembers,
    ElementMembers::Sequence =>
        if b.receiver_bound? then ElementVerdict::ReceiverBound
        else if ElementUse::Index in b.uses then ElementVerdict::Used(ElementUse::Index)
        else if ElementUse::SeqArgument in b.uses then ElementVerdict::Used(ElementUse::SeqArgument)
        else if ElementUse::Receiver in b.uses then ElementVerdict::Used(ElementUse::Receiver)
        else if ElementUse::FactArgument in b.uses then ElementVerdict::Used(ElementUse::FactArgument)
        else if ElementUse::QuantifiedArgument in b.uses then ElementVerdict::Used(ElementUse::QuantifiedArgument)
        else ElementVerdict::InCore,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc element_quantifier(
    binders: Seq<ElementBinder>,    -- its bound names of types that are not listed, in order
    nesting: ElementNesting,
    output?,                        -- its sequences or its body mention an output that is not defined
    bound?,                         -- its body mentions a bound name around it, but of the quantifiers it is directly the body of
): (det verdict: ElementVerdict) {
    use self::ElementVerdict::{InCore, MentionsBound, MentionsOutput, Nested}

    ensure first: forall (j: Int), when 0 <= j < binders.len and binder_verdict(binders[j]) != InCore
        and (forall (i: Int), when 0 <= i < j, binder_verdict(binders[i]) = InCore),
        verdict = binder_verdict(binders[j])
    ensure rest: when (forall (b: ElementBinder), when b in binders, binder_verdict(b) = InCore),
        verdict = (if output? then MentionsOutput else if nesting = ElementNesting::Other then Nested
        else if bound? then MentionsBound else InCore)
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
set_option fren.evidence "random" in
pub proc index_set(
    zero: IndexTerm,
    lasts: Seq<IndexTerm>,         -- each quantifier's sequence's last position
    reads: Seq<IndexTerm>,         -- each index's position
    positions: Seq<IndexTerm>,     -- each update's position
    before: Seq<IndexTerm>,        -- each update's position less one
    after: Seq<IndexTerm>,         -- each update's position plus one
    witnesses: Seq<IndexTerm>,
    terms: Seq<IndexTerm>,         -- the index set
): (
    det index_set?,                -- `terms` is the index set of the others
) {
    assume neighbours: before.len = positions.len and after.len = positions.len

    ensure rule: index_set? iff (terms != [] and terms[0] = zero
        and (forall (t: IndexTerm), when t in lasts, t in terms)
        and (forall (t: IndexTerm), when t in reads, t in terms)
        and (forall (i: Int), when 0 <= i < positions.len, before[i] in terms and positions[i] in terms and after[i] in terms)
        and (forall (t: IndexTerm), when t in witnesses, t in terms)
        and (forall (t: IndexTerm), when t in terms, t = zero or t in lasts or t in reads or t in positions or t in before
        or t in after or t in witnesses)
        and (forall (i j: Int), when 0 <= i < terms.len and 0 <= j < terms.len and i != j, terms[i] != terms[j]))
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
set_option fren.evidence "random" in
pub proc element_projection(
    q: Seq<Int>,
    ix: Seq<Int>,               -- the values of the index set's terms
    good: Set<Int>,             -- the elements at which the body holds
    i: Int,                     -- the position of an update
    v: Int,                     -- its value
    projected: Seq<Int>,        -- each element replaced by the element at the last value of `ix` at or before its position
    updated: Seq<Int>,          -- the same of `q.update(i, v)`
): (
    det projection?,            -- `projected` and `updated` are made so
) {
    assume zero: 0 in ix

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

A quantifier is expanded only where its witnesses may be names of the
whole query: where nothing bound around it is mentioned by its sequences,
nor by its body, other than the bound names of the expanded quantifiers of
its kind that it is directly within, on their *spine*: the consequent of an
implication, or a conjunct, where it has their polarity. One that is not
expanded, as a quantifier within the realizability check's `∃` whose body
mentions an output may be, or one within an unbounded quantifier whose
body mentions its bound name, or one unfolded from a defined function
within another quantifier, is given to the solver as written. Each such
quantifier is outside the core, by the rules of [the shape](#the-shape),
once defined functions are unfolded. `lang::site_expanded` states which
are expanded, from the binders around one, outermost first, and which of
them its body mentions:

```fren
-- A binder around a quantifier in a query: an expanded quantifier over
-- elements, whether it is a `forall` and whether what is within it is on its
-- spine; or any other.
pub enum Frame { Element(Bool, Bool), Other }

-- The binders from position `j` to the innermost are expanded quantifiers of
-- the kind `all?`, each with what is within it on its spine.
set_option fren.lint.undecidable "allow" in
fn in_chain?(frames: Seq<Frame>, all?, j: Int) :=
    forall (k: Int), when j <= k < frames.len, frames[k] = Frame::Element(all?, true)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc site_expanded(
    frames: Seq<Frame>,          -- the binders around it, outermost first
    all?,                        -- it is a `forall`
    receivers_closed?,           -- its sequences mention no name bound around it
    mentioned: Seq<Int>,         -- the positions of the binders whose names its body mentions
): (det expanded?) {
    ensure rule: expanded? iff (receivers_closed?
        and (forall (j: Int), when j in mentioned, 0 <= j < frames.len and in_chain?(frames, all?, j)))
}
```

Each expanded quantifier is replaced by its instances at the index set
with its witnesses, and `lang::element_witness` states the law that makes
that right: a quantifier over a sequence's positions holds exactly where
its instances hold at the terms `ix` together with a witness `w`, for every
value of `w`. A witness is a fresh name of the query, so the solver may
take it to be a position where the quantifier fails, if there is one: the
instances then fail exactly where the quantifier does. The names that the
quantifier's value depends on are the free names of the query and, by the
rule above, those of the quantifiers of its kind that it is directly within,
for whose instances one value of the witness, a failing position in the
instance that fails, serves:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc element_witness(
    q: Seq<Int>,
    good: Set<Int>,              -- the elements at which the body holds
    ix: Seq<Int>,                -- the values of the other terms of the index set
    w: Int,                      -- a value of the witness
): (
    det all?,                    -- the quantifier holds
    det instances?,              -- its instances at `w` and `ix` hold
    det failing: Int,            -- the first position where the body fails, and 0 where there is none
) {
    ensure meaning: all? iff (forall (x: Int), when x in q, x in good)
    ensure instances_rule: instances? iff ((when 0 <= w < q.len, q[w] in good)
        and (forall (t: Int), when t in ix and 0 <= t < q.len, q[t] in good))
    ensure sound: when all?, instances?
    ensure witness: when not all?, 0 <= failing < q.len and not (q[failing] in good)
    ensure first: forall (i: Int), when 0 <= i < failing, q[i] in good
    ensure none_fails: when all?, failing = 0
}
```

What is proved is this law, the rule of which quantifiers are expanded,
the index set and the projection, each of the code that both front ends
call. That the whole expanded query is unsatisfiable exactly where the
quantified one is follows from them by an induction over the query's
terms, which is argued here and not proved in Lean.

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

pub proc element_size(
    n_instances: Int,        -- the instances of a query's quantifiers over elements
): (det accepted?) {
    ensure rule: accepted? iff n_instances <= MAX_ELEMENT_INSTANCES

    expect at_limit: when n_instances = MAX_ELEMENT_INSTANCES, accepted?
    expect beyond_limit: when n_instances > MAX_ELEMENT_INSTANCES, not accepted?
}
```
