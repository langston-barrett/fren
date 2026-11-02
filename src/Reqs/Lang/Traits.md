# Traits

A *trait* declares an interface: a type, written `Self` within it, the
functions over that type that the interface offers, the laws that those
functions obey, and expectations that follow from the laws.

```text
trait KV {
    fn put(Self, Key, Int): Self
    fn get(Self, Key): Option<Int>
    law get_put(s: Self, k: Key, v: Int, j: Key): get(put(s, k, v), j) = (if j = k then Option::Some(v) else get(s, j))
    expect overwritten(s: Self, k: Key, v: Int, w: Int) {
        expect last_wins: get(put(put(s, k, v), k, w), k) = Option::Some(w)
    }
}
```

> **Note:** This chapter is the first part of traits (#594). Instances,
> which give a trait its type and functions, code generic over a trait, and
> the rule that brings laws into the decidable core come later.

```fren
pub mod lang
```

## Syntax

r[trait.syntax]
```
trait        := ["pub"] "trait" IDENT "{" trait-member* "}"
trait-member := method | law | expectation | lint-setting "in" trait-member
method       := "fn" IDENT"(" type ("," type)* ")" [":" type]
              | "fn" IDENT"(" variable ("," variable)* ")" ":" "(" variable [","] ")" "{" member* "}"
law          := "law" IDENT"(" [variable ("," variable)* [","]] ")" ":" top
```

r[trait.syntax.item]
A trait is an [item](Items.md) of its module.

r[trait.syntax.keywords]
`trait` is a [reserved word](Lexical.md#keywords). `law` is a contextual
keyword: it starts a law only where a member of a trait starts.

## Members

A trait's members are its methods, its laws and its expectations, in any
order.

**Legality rules**

r[trait.member.kinds]
A *method* is an [uninterpreted function](Items.md#uninterpreted-functions),
written with its types alone or with its parameters' names and a
[contract](Items.md#contracts). An *expectation* of a trait is a [global
expectation](Global.md), in either of its forms. A *law* is written `law`.

r[trait.member.other]
A member of any other kind is an error (`F0222`).

r[trait.member.pub]
A member written `pub` is an error (`F0222`).

r[trait.member.default]
A method with a body is an error (`F0222`).

r[trait.member.generic]
A method with type parameters is an error (`F0222`).

r[trait.member.use]
A `use` in the block of a member is an error (`F0222`).

r[trait.member.rule]
`lang::trait_member` states which members a trait accepts, from what the
member is as written, and whether it is written `pub`, has type
parameters, or has a `use` in its block.

```fren
-- A member of a trait, as written: a function without a body, a law, a
-- global expectation, a function with a body, or any other item.
pub enum TraitMemberKind { Method, Law, Expectation, DefinedFunction, OtherItem }

pub proc trait_member(
    member: TraitMemberKind,
    pub?,                  -- written `pub`
    generic?,              -- it has type parameters
    uses?,                 -- its block has a `use`
): (det accepted?) {
    use self::TraitMemberKind::{Expectation, Law, Method}

    ensure rule: accepted? iff (member in {Method, Law, Expectation} and not pub? and not generic? and not uses?)

    expect methods: when member = Method and not pub? and not generic? and not uses?, accepted?
    expect no_default_methods: when member = TraitMemberKind::DefinedFunction, not accepted?
    expect items_outside: when member = TraitMemberKind::OtherItem, not accepted?
}
```

r[trait.member.order]
The messages about a trait's members come by their phase, and in the
order written within a phase: those of the methods first, then those of
the laws, then those of the expectations (`lang::trait_member_phase`). A
member of another kind is reported, and no other member is. Each member
reports its own errors, and its errors stop only what follows them within
it.

```fren
pub proc trait_member_phase(member: TraitMemberKind): (det phase: Int) {
    use self::TraitMemberKind::{Expectation, Law, Method}

    ensure rule: phase = match member {
        Method => 0,
        Law => 1,
        Expectation => 2,
        _ => 3,
    }

    expect methods_first: when member = Method, phase < 1
    expect laws_before_expectations: when member = Law, phase = 1
}
```

> **Rationale:** A method with a body would be a *default method*, which
> comes with supertraits and associated types (#594). A member's own `use`
> would hide the trait's names in its block.

## The carrier

**Legality rules**

r[trait.carrier]
Within a trait, `Self` names the trait's *carrier*, an [abstract
type](Types.md#abstract-types) of the trait's own.

r[trait.carrier.payload]
A field or payload whose type is the carrier is an error (`F0310`), as for
any abstract type.

r[trait.carrier.outside]
Outside its trait, `Self` names nothing.

## Scope

**Legality rules**

r[trait.scope.shadowing]
Within a trait, `Self` and the trait's methods, each by its name alone,
shadow the names of the trait's module, without a `!`, as a [procedure's
imports](Modules.md#use-in-a-procedure) do. Every other name is the
module's.

r[trait.scope.order]
A method's signature and contract see the methods declared before it, and
its contract sees the method itself, as a function's contract does. The
laws and the expectations see every method.

r[trait.scope.distinct]
`Self` and the names of a trait's members are distinct (`F0213`).

r[trait.scope.outside]
The members of a trait are not items of its module.

## Laws

A law states what holds of the methods for all values of its variables.

**Legality rules**

r[trait.law.type]
A law's equation is a `Bool`.

r[trait.law.variables]
A law's variables are distinct (`F0213`). A variable's type is written,
but for a `Bool`, which may be written `x?` alone.

r[trait.law.mentions]
A law mentions no variable but its own. It may mention constants,
functions and the trait's methods.

r[trait.law.names]
A law's name is not written with `?` or `!`.

**Dynamic semantics**

r[trait.law.meaning]
`law n(x: T, y?): e` means `forall (x: T) (y?: Bool), e`.

r[trait.law.interpretation]
An [interpretation](Procedures.md#interpretations) of a trait gives its
carrier and its methods. An interpretation *meets* the trait when its
methods meet their contracts and every law holds.

**Proof obligations**

r[trait.law.undecidable]
A law with a variable of a type that is not listed is outside the
[decidable core](Decidability.md): its variables are an [unbounded
quantifier](Quantifiers.md#unbounded-quantifiers), which
[`undecidable`](../Lint/Decidability.md#undecidable-constructs) reports.
A law with no variables, or only variables of listed types, is within it
where its equation is.

## Expectations

An expectation of a trait checks, from the laws alone, that the laws say
what the author means, as Larch's `implies` does.

**Dynamic semantics**

r[trait.expect.meaning]
An expectation of a trait holds when its claims hold in every
interpretation that meets the trait (`lang::trait_expectation`).

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
    expect unlawful_ignored: when witness in models and not witness in lawful and claims = models minus {witness}, holds?
    expect no_laws: when lawful = models, holds? iff models subset claims
    -- Laws that no interpretation meets make every expectation hold.
    expect vacuous: when models inter lawful = {}, holds?
}
```

**Proof obligations**

r[trait.expect.checks]
An expectation of a trait has the checks of a [global
expectation](../Check.md#global-expectations), each with the trait's laws
among its hypotheses, but for its realizability, whose queries ask of its
own assumptions and calls alone.

r[trait.expect.core]
An expectation of a trait is in the decidable core where it is and every
law of its trait is, and `undecidable` is an error in it where it is in
the expectation or in a law (`lang::law_flags`, one law at a time).

```fren
-- What is known of an expectation, or of a law, before it is checked.
pub struct CheckFlags {
    in_core?,                -- every construct is in the decidable core
    denied?,                 -- `undecidable` is an error in it
}

pub proc law_flags(expectation: CheckFlags, law: CheckFlags): (det combined: CheckFlags) {
    ensure rule: combined = CheckFlags {
        in_core? := expectation.in_core? and law.in_core?,
        denied? := expectation.denied? or law.denied?,
    }

    expect outside: when not law.in_core?, not combined.in_core?
}
```

r[trait.expect.lawful]
An expectation of a trait with laws, and with assumptions or calls, has a
vacuity check of its own: whether its assumptions and calls can hold
together with the laws. Where they cannot, it is an error (`F0602`). Its
other checks rest on this check as they rest on its realizability: a pass
of a proof check is then inconclusive (`F0664`), and the verdict of a
check that a model decides, such as a cover goal's, stands
([Evidence](../Evidence.md#the-laws-of-a-trait)). Laws that contradict
each other fail it too.

r[trait.expect.laws-unchecked]
A verdict of an expectation of a trait with laws that comes from an
`unsat` query, such as a pass of an expectation or a failure of a cover
goal, rests on the laws. Where the expectation has a vacuity check under
the laws that is not decided, the verdict rests on the laws holding
together with its assumptions and calls, and where it has none, on the
laws' consistency, which Fren does not check yet (#594). Either way, its
constraint says so once, whatever its other checks give, and that check
reports nothing more (`F0665`, `check::law_premise`). A verdict that comes
from a model, such as a counterexample, rests on nothing more, since the
model meets the laws. Realizability's queries have no laws
(`check::query_hypotheses`).

r[trait.expect.once]
An expectation of a trait is checked once, in the trait.

r[trait.law.setting]
`fren.evidence` or `fren.enumeration.size` set before a law is an error
(`F0215`): a law has no checks of its own.

r[trait.expect.evidence]
`fren.evidence` set to testing or enumeration for an expectation of a
trait is an error (`F0215`, `lang::trait_expectation_evidence`).

```fren
pub proc trait_expectation_evidence(tested?, enumerated?): (det accepted?) {
    ensure rule: accepted? iff not tested? and not enumerated?
}
```

> **Rationale:** An interpretation that testing or enumeration picks need
> not meet the laws. Whether the laws can hold together is a check of its
> own, which comes with the instances (#594).

**Examples**

```fren example
mod store

type Key

set_option fren.lint.undecidable "allow" in
trait Store {
    fn put(Self, Key, Int): Self
    fn get(Self, Key): Option<Int>

    law get_put(s: Self, k: Key, v: Int, j: Key): get(put(s, k, v), j) = (if j = k then Option::Some(v) else get(s, j))

    expect overwritten(s: Self, k: Key, v: Int, w: Int) {
        expect last_wins: get(put(put(s, k, v), k, w), k) = Option::Some(w)  --~ warning: rests on the laws of `store::Store`
    }
}
--@ summary: 2 passed, 0 failed, 0 inconclusive, 0 redundant
```

#fren_check
