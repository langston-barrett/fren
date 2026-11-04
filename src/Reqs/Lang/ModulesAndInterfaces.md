# Modules

A module declares items: types, functions, procedures, and the items that
state claims about them, `lemma`, `assume`, `expect` and `law`. Some of its
items may be abstract. A function or procedure item states its own
precondition and claims in its `require` and `ensure` clauses. A lemma or
`assume` item can relate several items, mentioning functions as terms and
procedures through calls, in any mix. An *interface* is a module that other
modules implement. An *implementation* gives the abstract items of an
interface, or of a module, their definitions. A generic function is
checked once and used at each of its instances, as an interface's lemmas
are used at each of its implementations.

Internally, all of these are one notion. A module is a *theory*: a
signature, its parameters and items, with *sentences*, its lemma, `assume`,
`expect` and `law` items and its items' `require` and `ensure` clauses. An
implementation is a *theory morphism*. A generic function is a theory with
one item. The rules that define the meaning use these three terms, and say
which construct each case is. [Modules and visibility](Modules.md) states
how modules name and hide their items.

This chapter specifies modules, their signatures and imports, the items and
clauses that state claims, and which of them a check may use. It changes
nothing of how a spec of today is checked. How a
check instantiates a sentence, implementations, their obligations, the
translation of sentences along them, views, dispatch, and what each check
reports are specified apart, over one model of what each check rests on
(#669).

```text
type Path
type Fs

fn mkdir(Fs, Path): Fs
fn exists?(Fs, Path): Bool

assume made(fs: Fs, p: Path): exists?(mkdir(fs, p), p)

lemma still_made(fs: Fs, p: Path, q: Path): exists?(mkdir(mkdir(fs, p), q), q)
```

> **Note:** This chapter is the design of #669, which is not implemented
> yet. It comes in stages: `require` (stage 2); lemma and `assume` items,
> items with calls, and the rules of instantiation (stage 3); induction by
> unfolding (stage 4); the realizability tiers of `assume` items about
> several items (stage 5); and nested and mutual types (stage 6). Until a
> stage lands, the chapters that it changes say what Fren does. The codes of
> the errors that this chapter adds are assigned when they are implemented.
> Interfaces and implementations written as modules, `mod I<Self>` and
> `mod x: I<T>`, are decided in #669 and come with stage 3. Until then, an
> interface is written as today's [`trait`](Traits.md), and an
> implementation as the `inst` to come.

> **Note:** #669 also decides the following, which later stages specify:
>
> - Two lints, each an exact rewrite: one moves a lemma or `assume` item
>   whose only application is one function at exactly its parameters into
>   that function as an `ensure` clause, and one moves out an `ensure`
>   clause that mentions other abstract items (stage 3).
> - Traits stage 1's `trait` and `inst` move to `mod I<Self>` and `mod x:
>   I<T>` by a migration script, once stage 3 builds the shared machinery.
> - An implementation in scope is canonical for dispatch, two are an
>   error, and an explicit choice is always available (stage 3).
> - A module whose parts stay abstract, with `assume` items, is code over
>   an assumed implementation, as Lean's `section` and `variable` are, and
>   can later be ascribed to a named interface (stage 3).
> - A generic implementation, `mod list_eq<T: Eq>: Eq<List<T>>`, is a
>   functor, the only kind of functor for now. A bound on a type parameter
>   is an interface parameter of its theory (#617).
> - An interface generates a Lean `class` whose laws are `Prop` fields,
>   and an implementation an `instance` whose law fields Fren fills from
>   its own checks. An existing Lean instance can be named as an
>   implementation's witness. An interface's procedures are `Prop`-valued
>   relations there.
> - An unspecified value is a constant of its theory, instantiated at each
>   instance (the lesson of #635).
> - Dictionary passing is the reference semantics of generic items, and
>   monomorphization an optimization proved to agree with it (#594).
> - Theories stay second-class, unlike 1ML's, so that instances
>   resolve statically and queries stay free of the sentences' quantifiers.
> - Stage 1 removes the copies of instances across guard paths, and scopes
>   the closure of facts to the queries that mention a sentence's items.
>   The solver's time limit and the limit of 256 instances (`F0356`) are
>   settings to remove later.

```fren
pub mod lang
```

## Syntax

r[module.syntax]
```
lemma          := "lemma" IDENT "(" [variable ("," variable)* [","]] ")" claim-body
assume         := "assume" IDENT "(" [variable ("," variable)* [","]] ")" claim-body
claim-body     := ":" top | "{" claim-member* "}"
claim-member   := require | ensure | "expect" IDENT ":" top | "cover" IDENT ":" top
                | call | "let" variable ":=" top | use
require        := "require" IDENT ":" top
ensure         := "ensure" IDENT ":" top
```

r[module.syntax.forms]
An `expect` is accepted everywhere but in an `assume` item's block: as an
item of a module or of an interface, which is a [global
expectation](Global.md) in either of its forms, and as a member of a
function, a procedure, a global expectation or a lemma. A `law` item is a
member of a [trait](Traits.md#laws).

r[module.syntax.keywords]
`lemma` and `require` are contextual keywords. `lemma` starts an item where
an item starts, and a member of a trait where one starts. `require` starts
a member where a member starts.

r[module.syntax.short]
`lemma n(x: T): e` means `lemma n(x: T) { ensure n: e }`, and `assume n(x:
T): e` means `assume n(x: T) { ensure n: e }`. Each is reported by its own
name, `n`.

r[module.syntax.item]
A lemma item and an `assume` item are [items](Items.md) of their module. A
lemma item of an interface, today a trait, is a member of it.

## Modules as theories

Modules, interfaces, implementations and generic items differ only in
their numbers of parameters and items. This chapter specifies all but
implementations, which are specified apart:

| Construct | Parameters | Items |
|---|---|---|
| a module, `mod m` | none | many, some perhaps abstract |
| an interface, `mod I<Self>` (today `trait I`) | `Self` | many, partly abstract |
| a generic module, `mod m<T: B>` | types, with an implementation of each bound | many |
| an implementation, `mod x: I<T>` (replacing `inst`) | those of a generic implementation | many, matching `I` |
| a generic function, `fn f<T: B>` | types, with an implementation of each bound | one |
| a generic type, `enum Option<T>` | types, with an implementation of each bound | one datatype declaration, with its functions |

**Legality rules**

r[module.theory]
A module is a *theory*: a list of *parameters*, a list of items, and the
theory's *sentences*, which are the module's lemma, `assume`, `expect` and
`law` items and its items' `require` and `ensure` clauses. Each of its
parameters and items is *abstract* or *defined*.

r[module.theory.plain]
A module without parameters is a theory without parameters, whose items
are its declarations.

r[module.interface]
An interface is a module whose parameter is `Self`. Today's
[trait](Traits.md) is an interface: its carrier is `Self`, its methods are
its abstract items, and its laws are axioms among its sentences.

r[module.generic-function]
A generic function `fn f<T: B>` is a theory with one item, `f`. Its
parameters are its type parameters and an implementation of each bound at
them, and its sentences are `f`'s `require` and `ensure` clauses.

r[module.procedures]
The items of a module or interface may be procedures, abstract or not, and
its lemma and `assume` items may relate them through calls
(`module.meaning.procedures`).

## Imports and generic types

A `use` brings another module's items and sentences into a module. A
generic type is a theory with a datatype in its signature.

**Legality rules**

r[module.use.inclusion]
A `use` includes the module it imports, its items and its sentences, in
the importing one, and owes nothing: no sentence of the imported module is
an obligation of the importing one.

r[module.generic-type]
A generic type, such as `enum Option<T>` or `struct Pair<A, B>`, is a
theory whose parameters are its type parameters. Its signature has a
*datatype declaration*, a member whose meaning is *free*: its constructors
are distinct and injective, and every value is built by one of them.

r[module.generic-type.sentences]
A generic type's sentences are those that the spec writes: its invariants,
its functions' clauses, and the lemma items about them. Freeness is the
meaning of the datatype declaration, and no sentence states it.

> **Note:** A module may have a type constructor as a member, as `mod Monad
> { type M<A>; fn pure<A>(a: A): M<A>; ... }`, and a parameter may be such a
> module, as OCaml's functors take structures that have `'a t`. That gives
> generics over type constructors without type variables of higher kind.
> It comes later: type sharing, and whether a functor's abstract types are
> generative or applicative (Leroy; MixML; Rossberg's "F-ing modules"),
> are to be settled first (#669).

> **Note:** Nothing changes below the surface or on it. Obligations stay
> monomorphic (#705), and whether the solver's queries keep parametric
> datatypes or instantiate them is a choice of performance. `Option<T>` is
> still a type that a spec applies.

## Items and clauses that state claims

Each keyword says what is done with its item or clause: whether it is
checked, and whether later checks use it.

| Keyword | Where | Meaning |
|---|---|---|
| `require` | a clause of a function, a procedure, a global expectation, a lemma or an `assume` item | a precondition: the domain of its item |
| `ensure` | a clause of a function, a procedure, a lemma or an `assume` item | a claim of its item, which later checks use |
| `expect` | an item, or a member of anything but an `assume` item | a goal: checked, never used by another check |
| `lemma` | an item of a module or of an interface | a theorem: checked, and later checks use it |
| `assume` | an item of a module; within a function, a procedure or a global expectation, `require` | an axiom of the module's abstract items; within an item, a precondition |
| `law` | an item of an interface | an axiom of the interface, which each implementation discharges |

**Legality rules**

r[module.place] lang::sentence_place
An item or clause with one of these keywords is accepted where
`lang::sentence_place` accepts its keyword. Within a function, a procedure
or a global expectation, `assume` is accepted where `require` is.

r[module.place.error]
One where its keyword is not accepted is an error. In the block of a global
expectation, it is the error of a member that the block does not accept
(`F0417`). In a trait, it is the error of a member of another kind
(`F0222`).

r[module.place.expect] lang::sentence_place::expectations_anywhere
An `expect` in a function's block is accepted, and is a claim about the
function's value at its parameters, as a procedure's expectation is about
its outputs.

r[module.assume.block] lang::sentence_role::within_items
`assume n: e` inside a function, a procedure or a global expectation means
`require n: e`.

r[module.block] lang::sentence_member
The block of a lemma or `assume` item accepts the members that
`lang::sentence_member` accepts. Another member is an error. A lemma's
`ensure` members are its claims, and its `expect` and `cover` members are
checked as a global expectation's are.

```fren
-- A sentence's keyword. `Assume` is an `assume` item, or one within a
-- block, which means `require` there.
pub enum SentenceKind { Require, Ensure, Expect, Lemma, Assume, Law }

-- Where a sentence is written: in the block of a defined function, an
-- uninterpreted function, a procedure, a global expectation, a lemma or a
-- `assume` item; at the top level of a module; or in an interface,
-- today a trait.
pub enum SentencePlace {
    DefinedFunction,
    UninterpretedFunction,
    Procedure,
    GlobalBlock,
    LemmaBlock,
    AssumeBlock,
    Module,
    Interface,
}

set_option fren.evidence "enumerated" in
pub proc sentence_place(keyword: SentenceKind, place: SentencePlace): (det accepted?) {
    use self::SentencePlace::{
        AssumeBlock,
        DefinedFunction,
        GlobalBlock,
        Interface,
        LemmaBlock,
        Module,
        Procedure,
        UninterpretedFunction,
    }

    ensure rule: accepted? iff match keyword {
        SentenceKind::Require =>
            place in {
                DefinedFunction,
                UninterpretedFunction,
                Procedure,
                GlobalBlock,
                LemmaBlock,
                AssumeBlock,
            },
        SentenceKind::Ensure =>
            place in {
                DefinedFunction,
                UninterpretedFunction,
                Procedure,
                LemmaBlock,
                AssumeBlock,
            },
        SentenceKind::Expect => place != AssumeBlock,
        SentenceKind::Lemma => place in {Module, Interface},
        SentenceKind::Assume =>
            place in {
                DefinedFunction,
                UninterpretedFunction,
                Procedure,
                GlobalBlock,
                Module,
            },
        SentenceKind::Law => place = Interface,
    }

    expect expectations_anywhere: when keyword = SentenceKind::Expect and place != AssumeBlock, accepted?
    expect laws_in_traits: when keyword = SentenceKind::Law and accepted?, place = Interface
    expect lemmas_are_items: when keyword = SentenceKind::Lemma and place in {DefinedFunction, Procedure, GlobalBlock}, not accepted?
    expect no_assume_in_new_blocks: when keyword = SentenceKind::Assume and place in {LemmaBlock, AssumeBlock}, not accepted?
}

-- A member of a lemma's or an `assume` item's block.
pub enum SentenceMember { Require, Ensure, Expect, Cover, Call, Let, Use, Assume, Exists, Define, Refines }

set_option fren.evidence "enumerated" in
pub proc sentence_member(
    block: SentenceKind,       -- `Lemma`, or `Assume` for an `assume` item
    member: SentenceMember,
    det?,                      -- written with `det`, which no member of these blocks may be
): (det accepted?) {
    use self::SentenceMember::{Call, Cover, Ensure, Expect, Let, Require, Use}
    assume blocks: block in {SentenceKind::Lemma, SentenceKind::Assume}

    ensure rule: accepted? iff (not det? and (member in {Require, Ensure, Call, Let, Use}
        or (block = SentenceKind::Lemma and member in {Expect, Cover})))

    expect claims: when not det? and member = Ensure, accepted?
    expect axioms_have_no_goals: when block = SentenceKind::Assume and member in {Expect, Cover}, not accepted?
    expect require_only: when member = SentenceMember::Assume, not accepted?
}
```

> **Rationale:** `require` takes the place of `assume` within an item, so
> that `assume` means only an axiom. Within a global expectation the
> change is to be confirmed when it is implemented (#669). Within a
> function, a procedure or a global expectation, `assume` stays accepted
> where `require` is, so that every spec of today stays valid
> (`module.expansion`).

> **Note:** `lang::sentence_place` decides again part of what
> [`lang::fn_member`](Items.md#function-blocks) and
> [`lang::block_accepts?`](Global.md) decide today, and differs from
> `lang::fn_member` where `module.place.expect` accepts an `expect` in a
> function's block. Stage 3 makes them one decision in `Fren.Core`: the
> blocks' requirements take their rows for these keywords from
> `lang::sentence_place`, so that both front ends call one function.

## Theorems and axioms

Each lemma, `assume`, `expect` and `law` item, and each `require` and
`ensure` clause, is one of its module's sentences. A sentence is a
theorem, which Fren proves, or an axiom, which Fren takes as given and
never proves. Of its consistency, Fren checks only what `module.axiom.check`
says.

**Legality rules**

r[module.abstract]
The *abstract items* of a module are its abstract parameters and items:
its [abstract types](Types.md#abstract-types), [uninterpreted
functions](Items.md#uninterpreted-functions) and
[procedures](Procedures.md), an interface's `Self` and methods, and a
generic function's type parameters and the members of their bounds. A
defined function and a constant are not.

r[module.assume.abstract] lang::sentence_role
An `assume` item that mentions no abstract item, as an item it applies or
calls, as the type of one of its variables, or through the definition of a
defined item it applies, in turn, is an error.

**Dynamic semantics**

r[module.role] lang::sentence_role
Each sentence has the *role* that `lang::sentence_role` gives it, from its
keyword, its place, and the items it mentions.

r[module.role.domain] lang::sentence_role
A `require` clause is a *domain*: it restricts the values of its item's
parameters at which the item's other sentences are claimed.

r[module.role.theorem] lang::sentence_role
A *theorem* is a lemma item, or an `ensure` clause of a defined function
or of a lemma.
It holds in every interpretation that meets the axioms that it may rest on
(`module.use`).

r[module.role.axiom] lang::sentence_role
An *axiom* is an `assume` item, a `law` item, or an `ensure` clause of an
uninterpreted function, of a procedure, or of an `assume` item. The
spec's interpretations are those that meet every axiom.

r[module.role.goal] lang::sentence_role
An `expect` item or member is a *goal*. Fren proves it as it proves a
theorem, and no other check uses it.

r[module.ensure.sugar] lang::sentence_role
An `ensure` clause of a function `f` with the parameters `x` is the sentence that
`f`'s contract states of `f(x)`: a lemma about `f(x)` where `f` is defined, and an
`assume` item about it where `f` is uninterpreted.

r[module.meaning] lang::global_checks
A sentence with the quantified variables `x`, the domain `R(x)`, the calls
`y` and the claims `E(x, y)` means `∀ x y. R(x) ∧ I(x, y) ⇒ E(x, y)`, where
`I(x, y)` says that each `y` is a behaviour of its call, as a [global
expectation](Global.md#meaning) means. Its quantified variables are its
parameters, or its item's.

r[module.meaning.procedures] lang::global_checks
A call in a sentence ranges over the behaviours of its procedure at its
arguments. An `assume` item with calls constrains the procedures it
calls, as an environment that is never implemented does.

```fren
-- What is done with a sentence.
pub enum SentenceRole {
    Domain,      -- it restricts its item's parameters
    Theorem,     -- Fren proves it, and later checks use it
    Axiom,       -- Fren takes it as given, and never proves it
    Goal,        -- Fren proves it, and no other check uses it
}

-- The role of a sentence of the keyword `keyword`, written at `place`.
pub fn role_of(keyword: SentenceKind, place: SentencePlace): SentenceRole := match keyword {
    SentenceKind::Require => SentenceRole::Domain,
    SentenceKind::Expect => SentenceRole::Goal,
    SentenceKind::Lemma => SentenceRole::Theorem,
    SentenceKind::Law => SentenceRole::Axiom,
    SentenceKind::Ensure =>
        if place in {SentencePlace::DefinedFunction, SentencePlace::LemmaBlock} then SentenceRole::Theorem
        else SentenceRole::Axiom,
    SentenceKind::Assume =>
        if place = SentencePlace::Module then SentenceRole::Axiom else SentenceRole::Domain,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc sentence_role(
    keyword: SentenceKind,
    place: SentencePlace,
    mentioned: Set<Int>,     -- the items it applies or calls, and its variables' types
    defines: Rel<Int, Int>,  -- `(d, i)`: the definition of the defined item `d` mentions `i`
    abstract: Set<Int>,      -- the abstract items of the spec
): (det role: SentenceRole, det accepted?) {
    use self::SentencePlace::Module
    use self::SentenceRole::{Axiom, Domain}

    out role := role_of(keyword, place)
    let reached: Set<Int> := mentioned union defines.closure.image(mentioned)
    out accepted? :=
        not (keyword = SentenceKind::Assume and place = Module and reached inter abstract = {})

    expect axioms_mention_abstract_items: when keyword = SentenceKind::Assume and place = Module and accepted?,
        reached inter abstract != {}
    expect within_items: when keyword = SentenceKind::Assume and place != Module, role = Domain
    expect uninterpreted_contracts: when keyword = SentenceKind::Ensure and place = SentencePlace::UninterpretedFunction,
        role = Axiom
}
```

An `assume` item that applies only a defined function, whose definition
applies an abstract one, is accepted (`lang::assume_through_definition`):

```fren
-- `assume a(x: Int): h(x) > 0`, where `h`, at 2, is defined as `g(x)` of
-- the abstract `g`, at 1.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect assume_through_definition() {
    call r := sentence_role(
        SentenceKind::Assume,
        SentencePlace::Module,
        {2},
        {(2, 1)},
        {1},
    )
    expect accepted: r.accepted?
    expect an_axiom: r.role = SentenceRole::Axiom
}
```

> **Rationale:** An `assume` about defined items alone could contradict
> their definitions, and needs no trust: it is a lemma, and defined items
> are a conservative extension (`module.meta.conservative`).

## Order and use

Which items a sentence may mention depends on its keyword, and which
sentences a check may use on where each is declared. How a check uses a
sentence, by instantiating it at the terms of its query, and what it then
reports, are specified with implementations, over one model of what each
check rests on (#669).

**Legality rules**

r[module.signature] lang::lemma_order::axioms_unordered, lang::law_before_method
A module's *signature* is its items other than its lemma, `assume`,
`expect` and `law` items: its types, functions and procedures. A module
declares its signature as a whole. An `assume`, `expect` or `law` item
may mention any item of its own module's signature, wherever it is
declared, and the items of the modules that its module imports. This changes, for those items, the order of
declarations that [`lang::declared_before`](Items.md#items) states, and
which [Global expectations](Global.md) states for a global expectation's
procedures. A spec that is accepted today stays accepted, and stage 3
changes `lang::declared_before` to match. A `require` or `ensure` clause mentions only
the items declared before its function or procedure, and the item itself,
as [Contracts](Items.md#contracts) states.

r[module.order.lemma] lang::lemma_order
A lemma item applies and calls only the items declared before it, and the
items of the modules that its module imports. A lemma that applies or
calls an item declared after it is an error that names the application.

> **Note:** The Lean-hosted front end elaborates each item as a Lean
> command, in order. How it resolves the name of an item declared later in
> its module, as an `assume`, `expect` or `law` item may mention, is left
> to stage 3, which brings these items.

r[module.order.items]
The items of a spec are ordered: an imported module's items come before
those of the module that imports it, and a module's own items come in the
order in which they are declared.

**Dynamic semantics**

r[module.use]
A check of an item may use every axiom of its module and of the modules
it imports, wherever it is declared, and each theorem declared before the
item. No check uses a goal. A check of a sentence of today's forms uses
today's laws and contracts as it does today: a trait's laws as the
quantified hypotheses of the trait's checks that `traits.expect.checks`
gives them to, wherever each is written, and contracts as
[Contracts](Items.md#contracts) states.

`lang::lemma_order` states which applications a lemma may have:

```fren
-- The items that a sentence applies or calls, by their places in the
-- order of items, in the order in which it writes them.
pub enum AppliedItems { Nil, Cons(Int, AppliedItems) }

-- The first of `items` that is not declared before `position`, the first
-- at `k`, and -1 where there is none.
pub fn first_later(items: AppliedItems, position: Int, k: Int): Int := match items {
    AppliedItems::Nil => -1,
    AppliedItems::Cons(item, rest) =>
        if item >= position then k else first_later(rest, position, k + 1),
}

set_option fren.evidence "random" in
pub proc lemma_order(
    keyword: SentenceKind,
    position: Int,               -- the sentence's position in the order of items
    applied: AppliedItems,
): (det reported: Int) {
    out reported := if keyword = SentenceKind::Lemma then first_later(applied, position, 0) else -1

    expect axioms_unordered: when keyword in {
        SentenceKind::Assume,
        SentenceKind::Law,
        SentenceKind::Expect,
    },
        reported = -1
}

-- `lemma l(n: N): h(n) >= 1` at 2, before a function `h` at 3: an error at
-- `h(n)`, so that `h`'s contract and `l` cannot rest on each other.
set_option fren.evidence "random" in
expect lemma_before_function() {
    call r := lemma_order(
        SentenceKind::Lemma,
        2,
        AppliedItems::Cons(3, AppliedItems::Nil),
    )
    expect reported: r.reported = 0
}

-- `law l(s: Self): f(s) >= 0` at 1, before `fn f(Self): Int` at 2: a law
-- may apply an item declared after it, as a lemma may not.
set_option fren.evidence "random" in
expect law_before_method() {
    call r := lemma_order(
        SentenceKind::Law,
        1,
        AppliedItems::Cons(2, AppliedItems::Nil),
    )
    expect reported: r.reported = -1
}
```

> **Rationale:** Axioms are used wherever they are declared, since no
> axiom is proved and so none can rest on a check that rests on it.
> Theorems are ranked, so that no proof rests on itself. Lemmas keep the
> order of declarations because a theorem that mentioned a later item
> could rest on it: with `lemma l(n: N): h(n) >= 1` before a structural
> recursion `h` whose contract claims `h(n) >= 1`, the check of `l` would
> use `h`'s contract, and the check of `h`'s contract would use `l`, so
> each would pass from the other, whatever `h` is. No check rests on an
> axiom's or a goal's proof, so they may come anywhere.

## Checks

**Proof obligations**

r[module.theorem.check]
A lemma has the checks of a [global
expectation](../Check.md#global-expectations) with its parameters, its
domain, its calls and its claims, each using the sentences that
`module.use` gives. Induction by unfolding, which proves some theorems
that these checks do not, is to be specified in Structural recursion by
#750.

r[module.axiom.check]
An axiom is never proved. Until the realizability of axioms that relate
several items is specified (#669, stage 5), Fren checks of a module's
axioms only what it checks today: the realizability of each uninterpreted
function's `ensure` clauses ([Realizability](../Check.md#contracts-of-uninterpreted-functions),
`F0631`, `F0632`).

> **Note:** Today's realizability check is kept, so
> `module.expansion` holds of it: a spec of today's forms has the same
> realizability verdicts and messages. Stage 5 adds the tiers that check
> `assume` items and laws that relate several items.

## Metatheory

The rules above rest on properties of the logic and of the language. Each
is stated here, with the rule that relies on it, and whether it is argued
or open (#669). Those that implementations rest on are stated with them.

**Dynamic semantics**

r[module.meta.conservative]
A module's defined items are a *conservative extension* of its other
items: adding a defined function, a constant or a structural recursion
proves no new sentence that does not mention it (Shoenfield; CASL's
definitional extensions). `module.abstract`, which leaves defined items out
of the abstract ones, and `module.assume.abstract`, which needs no trust in
an `assume` about defined items alone, rely on it. It is argued from the
totality of [structural recursion](Recursion.md#meaning), and from an
unspecified value being a constant of the theory, one for each instance.

r[module.meta.free]
A datatype declaration's free meaning is that of the solver's datatypes
and of a Lean `inductive`, which give its constructors' distinctness,
injectivity and exhaustiveness (CASL's free types; the initial algebra of
its constructors). `module.generic-type.sentences` relies on it, so that
no query states freeness. It is argued.

## Strict expansion

**Dynamic semantics**

r[module.expansion]
A spec that Fren accepts today, whose items and clauses are all of
today's forms, has the same verdicts and messages as before this chapter.
Today's forms are an `ensure` clause and an `assume` clause of a function
or procedure, an `assume` member of a global expectation's block, an
`expect` of a procedure, a global expectation or a trait, a global
expectation, and a trait's `law`, with the other members of today's
blocks, such as a `cover` of a procedure or a global expectation, `let`,
`call`, `use`, `exists` and `refines`. A `require`, a lemma item, an `assume`
item, an `expect` in a function, and any member of a lemma's or an
`assume` item's block are new. This chapter adds the new forms and changes
nothing of how a sentence of today's forms is checked or reported. The
second half of this design computes what each check is reported as, from
a model of the module and through `check::reported_pass`, and checks this
guarantee over it, with the exceptions that its instantiation and
induction by unfolding, which is to be specified in Structural recursion
by #750, bring (#669).

> **Rationale:** The prior art: ACL2's `encapsulate` and functional
> instantiation; Why3's theories and `clone`; the loose and initial
> semantics of CASL, Larch, OBJ and Maude; Isabelle's locales; Event-B's
> feasibility obligations; and TLA+'s `ASSUME` and `THEOREM` (#669).

The Lean-hosted front end checks this chapter's items by name, since no
`#fren_check` of its Lean file comes after it, and one without a path would
check every earlier chapter again:

```fren
#fren_check sentence_place
#fren_check sentence_member
#fren_check sentence_role
#fren_check assume_through_definition
#fren_check law_before_method
#fren_check lemma_order
#fren_check lemma_before_function
```
