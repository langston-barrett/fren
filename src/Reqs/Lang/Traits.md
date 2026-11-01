# Traits

A *trait* declares an interface: a type, its *carrier*, written `Self`
within the trait, with *methods* over it, the *laws* that the methods
obey, and *expectations*, consequences of the laws that the trait claims.
A key-value store is one:

```text
type Key

trait KV {
    fn put(Self, Key, Int): Self
    fn get(Self, Key): Option<Int>

    law get_put(s: Self, k: Key, v: Int, j: Key): get(put(s, k, v), j) = (if j = k then Option::Some(v) else get(s, j))

    expect overwritten(s: Self, k: Key, v: Int, w: Int) {
        expect last_wins: get(put(put(s, k, v), k, w), k) = Option::Some(w)
    }
}
```

```
trait        := ["pub"] "trait" IDENT "{" trait-member* "}"
trait-member := method | law | expectation | lint-setting "in" trait-member
method       := "fn" IDENT"(" type ("," type)* ")" [":" type]
              | "fn" IDENT"(" variable ("," variable)* ")" ":" "(" variable [","] ")" "{" member* "}"
law          := "law" IDENT"(" [variable ("," variable)* [","]] ")" ":" top
```

A trait is an item of its module, named like a type, and `trait` is a
reserved word. `law` is a contextual keyword: it starts a law only where a
member of a trait starts (see [Keywords](Lexical.md#keywords)).

What follows is the first part of traits that Fren has (#594): a trait,
its laws and its expectations. Its instances, which give the carrier and
the methods, the code that is generic over a trait, and the trigger rule
that brings laws into the [decidable core](Decidability.md) come next.

```fren
pub mod lang
```

## Members

A trait's members are its methods, its laws and its expectations, in any
order. A method is an [uninterpreted function](Items.md#uninterpreted-functions),
written as one is, with its types alone or with its parameters' names and
a [contract](Items.md#contracts) in its block. An expectation is a [global
expectation](Global.md), in either of its forms. A member is not written
`pub`: it is visible where the trait is. Nor does a member's block have a
`use`, for now, and a method has no type parameters and no body, for now:
a method with a body would be a *default method*, which Fren does not have
yet. Any other item is not a member of a trait. Each of these is the error
`F0222`.

`lang::trait_member` states which members a trait accepts, from what the
member is, as it is written, and whether it is written `pub`, has type
parameters or has a `use` in its block (`Core.traitMemberAccepted`, which
both front ends call):

```fren
-- A member of a trait, as written: a function without a body, a law, a
-- global expectation, a function with a body, or any other item.
pub enum TraitMemberKind { Method, Law, Expectation, DefinedFunction, OtherItem }

pub proc trait_member(
    kind: TraitMemberKind,
    pub?,                  -- written `pub`
    generic?,              -- it has type parameters
    uses?,                 -- its block has a `use`
): (det accepted?) {
    use self::TraitMemberKind::{Expectation, Law, Method}

    ensure rule: accepted? iff (kind in {Method, Law, Expectation} and not pub? and not generic? and not uses?)

    expect methods: when kind = Method and not pub? and not generic? and not uses?, accepted?
    expect no_default_methods: when kind = TraitMemberKind::DefinedFunction, not accepted?
    expect items_outside: when kind = TraitMemberKind::OtherItem, not accepted?
}
```

## The carrier

Within a trait, `Self` is its carrier: an [abstract
type](Types.md#abstract-types) of the trait's own, of which nothing is
known but that it has values, and whether two of them are equal. So a
method's parameter or result may be a `Self`, and a law or expectation may
quantify over `Self`s, but a record's field or a variant's payload may not
be one, as for any abstract type (`F0310`). Outside the trait, `Self`
means nothing.

## Scope

A trait's members are in its scope: there, `Self`, and the trait's
methods, each by its name alone, shadow the names of the trait's module,
as a [procedure's imports](Modules.md#use-in-a-procedure) do, without a
`!`, and every other name is the module's. A method's signature and
contract see the methods declared before it, as a function's do; the laws
and the expectations see every method. `Self` and the names of the
members are distinct (`F0213`). The members are not items of the module,
so nothing outside the trait names them, for now: an instance and the code
generic over the trait will.

## Laws

`law n(x: T, y?): e` states that `e`, a `Bool`, holds for all values of
its variables, which are a quantifier around it: it means `forall (x: T)
(y?: Bool), e`. Like a global expectation in the [short
form](Global.md#the-short-form), it mentions no variable but its own, and
may mention constants, functions and the trait's methods. A variable has
its type written, as a defined function's parameter does, or is a `Bool`
written `x?` alone. Its variables are distinct (`F0213`), and their names,
and the law's, are in `snake_case` (`non_snake_case`).

A law is what is known of the methods, beyond their contracts: an
[interpretation](Procedures.md#interpretations) of the trait is one of its
carrier and methods that meets the methods' contracts and every law. A
law's quantifier is over types that are not listed, so for now each law is
outside the decidable core, and the
[`undecidable`](../Lint/Decidability.md#undecidable-constructs) lint
reports it at its variables, as it reports any [unbounded
quantifier](Quantifiers.md#unbounded-quantifiers). The trigger rule that
#594 sets out, by which a law whose every variable is in one application
of a method is instantiated at the ground terms of each query, will bring
such laws into the core.

## Expectations

An expectation of a trait is a global expectation that claims its
expectations for every interpretation of the trait: for every carrier, and
all methods that meet their contracts and the laws, as Larch's `implies`
does. So it checks, from the laws alone, that the laws say what the author
means. It is checked once, in the trait, and nothing that later gives the
trait an instance checks it again. Its checks are the solver's:
`fren.evidence` cannot be set to testing or enumeration for it (`F0215`),
since an interpretation that testing or enumeration picks need not meet
the laws.

`lang::trait_expectation` states this, over the interpretations of the
spec's abstract types and functions, the trait's carrier and methods among
them: those that meet the contracts, those that meet the laws, and those
in which the expectation's claims hold for all its parameters that meet its
assumptions:

```fren
pub type Interpretation

pub proc trait_expectation(
    models: Set<Interpretation>,       -- the interpretations that meet the contracts
    lawful: Set<Interpretation>,       -- those that meet every law of the trait
    claims: Set<Interpretation>,       -- those in which the expectation's claims hold
    witness: Interpretation,
): (det holds?) {
    ensure meaning: holds? iff models inter lawful subset claims

    -- An interpretation that meets the laws and not the claims refutes it.
    expect lawful_counts: when witness in models and witness in lawful and not witness in claims, not holds?
    -- One that does not meet the laws never does.
    expect unlawful_ignored: when claims = models inter lawful, holds?
    expect no_laws: when lawful = models, holds? iff models subset claims
    -- Laws that no interpretation meets make every expectation hold.
    expect vacuous: when models inter lawful = {}, holds?
}
```

## Meaning

Both front ends check a trait as what they already check: its carrier is an
abstract type, `T::Self` for the trait `T`; each method is an
uninterpreted function, `T::m`, with its contract; and each expectation is
a global expectation, `T::e`, whose queries have the trait's laws, each a
quantified formula, among their hypotheses, before its assumptions and
calls (`Core.Comp.laws`). The laws are among the hypotheses of every check
of the expectation but its [realizability](../Check.md#global-expectations),
which asks of its own assumptions alone: whether the laws can hold together
is a check of its own, which comes with the instances. In Lean, the
carrier and the methods are what an abstract type and uninterpreted
functions are (see [Generated Lean](../Generated.md#abstract-types-and-uninterpreted-functions)); the trait becomes
a Lean class with its instances.

#fren_check
