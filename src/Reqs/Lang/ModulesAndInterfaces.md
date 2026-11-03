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
>   error, and an explicit choice is always available
>   (`module.meta.coherence`, stage 3).
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

## Interfaces and implementations

Modules, interfaces, implementations and generic functions differ only in
their numbers of parameters and items:

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

r[module.implementation]
An implementation of a module or interface is a *theory morphism* from it
into the module that implements it. It maps each parameter, and some of the
abstract items, to types and items there, and *translates* each sentence by
that map. An implementation `mod x: I<T>`, an `inst`, a spec's
[`impl` and `interp`](../Impl.md) bindings, and an instance `f<Int>` of a
generic function are morphisms.

r[module.implementation.instantiate]
Translating a module along an implementation is one operation, the same
for every construct of the table above.

r[module.implementation.partial]
An implementation is *total* where it maps every abstract item, and
*partial* otherwise.

r[module.implementation.obligations]
An implementation makes each translated axiom an *obligation* where the
axiom mentions only implemented items, leaves it *trusted* where it
mentions only items left abstract, and makes it an obligation that
*relies* on the rest otherwise (`lang::morphism_status`). The report of
the evidence lists the items that a partial implementation leaves
abstract.

r[module.implementation.theorems]
A theorem of a module, once checked, holds translated, without another
check, of every implementation of it whose obligations hold, and of a
partial one, given the axioms that it leaves trusted (*functional
instantiation*, `lang::translated_theorem`).

r[module.parametricity]
No check or item of a module or generic function inspects a type
parameter but through the members of its bounds.

r[module.implementation.liskov]
Each item that implements an abstract item refines it: its `require`
clauses are weaker than the abstract item's or the same, its `ensure`
clauses are stronger or the same, and it preserves the invariants of the
types that it implements, as [Refinement](Refinement.md) checks of each
member.

```fren
-- What an implementation makes of a translated axiom.
pub enum MorphismStatus {
    Obligation,      -- it mentions only implemented items: the implementation must prove it
    Trusted,         -- it mentions only items left abstract: it stays an axiom
    Relying,         -- it mentions both: an obligation that relies on the rest
}

set_option fren.evidence "random" in
pub proc morphism_status(
    mentioned: Set<Int>,     -- the abstract items that the axiom mentions
    mapped: Set<Int>,        -- the abstract items that the implementation implements
): (det status: MorphismStatus) {
    out status :=
        if mentioned subset mapped then MorphismStatus::Obligation
        else if mentioned inter mapped = {} then MorphismStatus::Trusted
        else MorphismStatus::Relying

    expect total: when mentioned subset mapped, status = MorphismStatus::Obligation
    expect nothing_mapped: when mapped = {} and mentioned != {}, status = MorphismStatus::Trusted
    expect no_abstract_mentions: when mentioned = {}, status = MorphismStatus::Obligation
}
```

> **Note:** A sentence that mentions no abstract item is an obligation of
> every implementation, which its own check as a theorem has already
> discharged (`module.implementation.theorems`).

> **Rationale:** One notion of module, and one translation, means that a
> generic function's instances, an interface's implementations and a
> module's implementations cannot differ in how they translate a claim.
> #635 needed seven rounds of review because generic functions were
> instantiated piecemeal (#669). The design follows Dreyer, Harper,
> Chakravarty and Keller's modular type classes (POPL 2007), in which a
> class is a signature and an instance a structure; Burstall and Goguen's
> Clear, OBJ and CASL's views; Specware's morphisms with proof
> obligations; mixin modules (MixML); and Agda's parameterized modules,
> Isabelle's locales and Coq's sections. Whether two partly abstract
> modules that share an interface combine as their colimit, and whether
> `refines` is module ascription, are open (#669).

## Views, inclusions and generic types

Every way of relating modules is a theory morphism, and the kinds of
morphism differ only in what they owe. A *view* is one that a spec
declares by name, between modules that exist already.

| Construct | As a morphism | It owes |
|---|---|---|
| `mod Ord<Self> extends Eq<Self>` | an inclusion of `Eq` into `Ord` | nothing itself; an implementation of `Ord` owes `Eq`'s laws too |
| `mod x: I<T>`, an implementation | from `I` into a module that implements it | `I`'s laws |
| `f<Int>`, `Option<Int>`, an instance | a substitution | its parameters' requirements |
| `use`, an import | an inclusion into the importing module | nothing |
| a refinement (#685) | a morphism with refinement obligations | as #685 states |
| a view | between two existing modules | the target's laws, proved from the source's |

**Legality rules**

r[module.morphism.kinds]
Each of the constructs of the table above is a morphism, and owes what
`lang::morphism_obligations` gives. There is one translation along a
morphism, whatever its kind (`module.implementation.instantiate`) (`lang::morphism_obligations`).

r[module.morphism.transport]
A theorem of a morphism's source is a theorem of its target, translated,
once the morphism's obligations hold (`lang::translated_theorem`), whatever
the morphism's kind.

r[module.extends]
`mod Ord<Self> extends Eq<Self>` makes `Ord` include `Eq`: `Eq`'s items and
sentences are `Ord`'s too. The inclusion owes nothing. An implementation of
an interface owes the laws of every interface that it includes, directly
or through others, with its own (`lang::owed_laws`).

r[module.use.inclusion]
A `use` is an inclusion of the module it imports into the importing one,
and owes nothing (`inclusions_owe_nothing` of `lang::morphism_obligations`).

r[module.view]
A *view* is a named morphism from one module into another, declared
apart from both, so that neither changes. Its keyword is not decided yet.

r[module.view.derived]
A view may define the target's operations from the source's, as
`le(x, y) := meet(x, y) = x` makes a lattice a partial order. The target's
laws, translated, are its obligations, proved once from the source's
sentences. Where they hold, every lemma of the target holds of the source
(`module.morphism.transport`).

r[module.view.choice]
A use that a view could serve takes the view that it names. A use that
names none takes the one view that applies, and where no view or several
apply, it is an error (`lang::view_choice`), as `Int` is a monoid under `+`
and under `*`.

r[module.generic-type]
A generic type, such as `enum Option<T>` or `struct Pair<A, B>`, is a
theory whose parameters are its type parameters. Its signature has a
*datatype declaration*, a member whose meaning is *free*: its constructors
are distinct and injective, and every value is built by one of them.

r[module.generic-type.sentences]
A generic type's sentences are those that the spec writes: its invariants,
its functions' clauses, and the lemma items about them. Freeness is the
meaning of the datatype declaration, and no sentence states it.

r[module.generic-type.instance]
An instance of a generic type, such as `Option<Int>`, is a morphism by
substitution, as an instance `f<Int>` of a generic function is. A bound on
a parameter, as in `type SortedList<T: Ord>`, an invariant that mentions a
parameter, and the lemmas about the type's functions are translated along
it by the one translation.

```fren
-- A kind of morphism between modules.
pub enum MorphismKind { Inclusion, Implementation, Instance, Import, Refinement, View }

set_option fren.evidence "enumerated" in
pub proc morphism_obligations(morphism: MorphismKind): (
    det laws?,               -- the target owes the source's laws
    det requirements?,       -- it owes the requirements of the source's parameters
    det refinement?,         -- it owes refinement obligations (#685)
) {
    out laws? := morphism in {MorphismKind::Implementation, MorphismKind::View}
    out requirements? := morphism = MorphismKind::Instance
    out refinement? := morphism = MorphismKind::Refinement

    expect inclusions_owe_nothing: when morphism in {MorphismKind::Inclusion, MorphismKind::Import},
        not laws? and not requirements? and not refinement?
}

-- The laws that an implementation of `interface` owes: its own, and those
-- of every interface it includes, directly or through others.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc owed_laws(
    interface: Int,
    laws: Rel<Int, Int>,         -- `(i, l)`: the interface `i` states the law `l`
    includes: Rel<Int, Int>,     -- `(i, j)`: the interface `i` extends `j`
): (det owed: Set<Int>) {
    out owed := laws.image({interface} union includes.closure.image({interface}))

    expect own_laws: laws.image({interface}) subset owed
    expect no_extends: when includes = {}, owed = laws.image({interface})
}

-- The view that a use takes: the one it names, or else the one view that
-- applies, and -1 where it is an error.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc view_choice(
    applicable: Seq<Int>,        -- the views that could serve the use, each once
    named: Int,                  -- the view that the use names, and -1 where it names none
): (det view: Int, det error?) {
    out error? := (named != -1 and not named in applicable) or (named = -1 and applicable.len != 1)
    out view := if error? then -1 else if named != -1 then named else applicable[0]

    expect implicit_only_alone: when named = -1 and applicable.len >= 2, error?
    expect named_wins: when named in applicable, view = named
}
```

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
| `lemma` | an item of a module or of an interface | a goal that, once checked, later checks use, at every implementation |
| `assume` | an item of a module | an axiom of the module's abstract items |
| `law` | an item of an interface | an axiom of the interface, which each implementation discharges |

**Legality rules**

r[module.place]
An item or clause with one of these keywords is accepted where
`lang::sentence_place` accepts its keyword. Within a function, a procedure
or a global expectation, `assume` is accepted where `require` is (`lang::sentence_place`).

r[module.place.error]
One where its keyword is not accepted is an error. In the block of a global
expectation, it is the error of a member that the block does not accept
(`F0417`). In a trait, it is the error of a member of another kind
(`F0222`).

r[module.place.expect]
An `expect` in a function's block is accepted, and is a claim about the
function's value at its parameters, as a procedure's expectation is about
its outputs (`expectations_anywhere` of `lang::sentence_place`).

r[module.assume.block]
`assume n: e` inside a function, a procedure or a global expectation means
`require n: e` (`within_items` of `lang::sentence_role`).

r[module.block]
The block of a lemma or `assume` item accepts the members that
`lang::sentence_member` accepts. Another member is an error. A lemma's
`ensure` members are its claims, and its `expect` and `cover` members are
checked as a global expectation's are (`lang::sentence_member`).

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
> change is to be confirmed when it is implemented (#669). `assume` stays
> accepted where `require` is, so that every spec of today stays valid
> (`module.expansion`).

## Theorems and axioms

Each lemma, `assume`, `expect` and `law` item, and each `require` and
`ensure` clause, is one of its module's sentences. A sentence is a
theorem, which Fren proves, or an axiom, which Fren takes as given and
checks only for consistency.

**Legality rules**

r[module.abstract]
The *abstract items* of a module are its abstract parameters and items:
its [abstract types](Types.md#abstract-types), [uninterpreted
functions](Items.md#uninterpreted-functions) and
[procedures](Procedures.md), an interface's `Self` and methods, and a
generic function's type parameters and the members of their bounds. A
defined function and a constant are not.

r[module.assume.abstract]
An `assume` item that depends on no abstract item (`module.depends`) is an
error
(`lang::sentence_role`).

**Dynamic semantics**

r[module.role]
Each sentence has the *role* that `lang::sentence_role` gives it, from its
keyword, its place, and the items it mentions (`lang::sentence_role`).

r[module.role.domain]
A `require` clause is a *domain*: it restricts the values of its item's
parameters at which the item's other sentences are claimed (`lang::sentence_role`).

r[module.role.theorem]
A *theorem* is a lemma item, or an `ensure` clause of a defined function
or of a lemma.
It holds in every interpretation that meets the axioms that it may rest on
(`module.use`) (`lang::sentence_role`).

r[module.role.axiom]
An *axiom* is an `assume` item, a `law` item, or an `ensure` clause of an
uninterpreted function, of a procedure, or of an `assume` item. The
spec's interpretations are those that meet every axiom (`lang::sentence_role`).

r[module.role.goal]
An `expect` item or member is a *goal*. Fren proves it as it proves a
theorem, and no other check uses it (`lang::sentence_role`).

r[module.ensure.sugar]
An `ensure` clause of a function `f` with the parameters `x` is the sentence that
`f`'s contract states of `f(x)`: a lemma about `f(x)` where `f` is defined, and an
`assume` item about it where `f` is uninterpreted (`lang::sentence_role`).

r[module.meaning]
A sentence with the quantified variables `x`, the domain `R(x)`, the calls
`y` and the claims `E(x, y)` means `∀ x y. R(x) ∧ I(x, y) ⇒ E(x, y)`, where
`I(x, y)` says that each `y` is a behaviour of its call, as a [global
expectation](Global.md#meaning) means. Its quantified variables are its
parameters, or its item's (`lang::global_checks`).

r[module.meaning.procedures]
A call in a sentence ranges over the behaviours of its procedure at its
arguments. An `assume` item with calls constrains the procedures it
calls, as an environment that is never implemented does (`lang::global_checks`).

r[module.trait.lemma]
A lemma of an interface holds in every interpretation that meets the
interface, and of every implementation of it, by
`module.implementation.theorems` (`lang::translated_theorem`).

```fren
-- What is done with a sentence.
pub enum SentenceRole {
    Domain,      -- it restricts its item's parameters
    Theorem,     -- Fren proves it, and later checks use it
    Axiom,       -- Fren takes it as given, and checks its consistency
    Goal,        -- Fren proves it, and no other check uses it
}

set_option fren.evidence "random" in
pub proc sentence_role(
    keyword: SentenceKind,
    place: SentencePlace,
    mentioned: Set<Int>,     -- the items that the sentence depends on, directly or through definitions (`module.depends`)
    abstract: Set<Int>,      -- the abstract items of the spec
): (det role: SentenceRole, det accepted?) {
    use self::SentencePlace::{DefinedFunction, LemmaBlock, Module}
    use self::SentenceRole::{Axiom, Domain, Goal, Theorem}

    out role := match keyword {
        SentenceKind::Require => Domain,
        SentenceKind::Expect => Goal,
        SentenceKind::Lemma => Theorem,
        SentenceKind::Law => Axiom,
        SentenceKind::Ensure => if place in {DefinedFunction, LemmaBlock} then Theorem else Axiom,
        SentenceKind::Assume => if place = Module then Axiom else Domain,
    }
    out accepted? :=
        not (keyword = SentenceKind::Assume and place = Module and mentioned inter abstract = {})

    expect axioms_mention_abstract_items: when keyword = SentenceKind::Assume and place = Module and accepted?,
        mentioned inter abstract != {}
    expect within_items: when keyword = SentenceKind::Assume and place != Module, role = Domain
    expect uninterpreted_contracts: when keyword = SentenceKind::Ensure and place = SentencePlace::UninterpretedFunction,
        role = Axiom
}
```

> **Rationale:** An `assume` about defined items alone could contradict
> their definitions, and needs no trust: it is a lemma, and defined items
> are a conservative extension (`module.meta.conservative`).

## Instantiation

Fren uses a theorem or an axiom in a check by *instantiating* it: it puts
ground terms of the check's query for the sentence's quantified variables,
and adds each instance as a hypothesis. It chooses the instances itself,
from the applications and calls of the query, and no spec writes or sees
how a sentence is instantiated.

**Legality rules**

r[module.signature]
A module's *signature* is its items other than its lemma, `assume`,
`expect` and `law` items: its types, functions and procedures. A module
declares its signature as a whole. A sentence may mention any item of its
own module's signature, wherever it is declared, and the items of the
modules that its module imports (`lang::law_before_method`).

r[module.order.items]
The items of a spec are ordered: an imported module's items come before
those of the module that imports it, and a module's own items come in the
order in which they are declared.

r[module.subject]
A sentence's *subject* is the item, of those it applies or calls, that
comes last in that order (`lang::sentence_instantiation`).

r[module.anchor]
An *anchor* of a sentence is an application of its subject, as a function,
that mentions no name that a quantifier within the sentence binds, and
that has an argument that is neither a quantified variable nor a closed
term. Where the sentence has no such application, each application of its
subject, as a function, that mentions no such name is an anchor (`lang::sentence_instantiation`).

r[module.matched]
The *matched* applications of a sentence are its anchors and each of its
calls that mentions no name that a quantifier within the sentence binds (`lang::sentence_instantiation`).

r[module.binding]
Each quantified variable of a sentence that occurs in an application of
it, and whose type is not [listed](Quantifiers.md#types), occurs in a
matched application. A variable that does not is an error that names it
(the *binding rule*) (`lang::sentence_instantiation`).

r[module.binding.outside]
A quantified variable that the sentence mentions only outside its
applications, as `n` in `law bounded(s: Self, n: Int): when n > 0, h(s) >=
0`, needs no term: it stays quantified within each instance (`lang::outside_variable`).

r[module.rules.kinds]
The binding rule applies to a lemma item and an `assume` item. An `expect`
that does not meet it is checked, as every goal is. An `ensure` meets it,
since a contract applies its function only to its parameters
([Contracts](Items.md#contracts)).

r[module.rules.laws]
A `law` that meets the binding rule is instantiated as a lemma is. A `law`
that does not is not an error, and is used only as today, as a quantified
hypothesis of every check of its trait ([Traits](Traits.md#laws),
`lang::unbound_law_quantified`).

r[module.rules.report]
A sentence that breaks the binding rule reports its first unbound variable
(`lang::sentence_instantiation`).

**Dynamic semantics**

r[module.instance]
An *instance* of a sentence is the sentence with a ground term in place of
each of its quantified variables that has one. It holds wherever the
sentence does.

r[module.instance.matching]
Fren takes the instances at which all the matched applications of the
sentence are terms of the query at once: each anchor an application of the
query, and each call a call of the query, with the same arguments once the
instance's terms are put in. Two terms are the same where they are written
alike, once each name with a definition is replaced by it.

r[module.instance.ground]
An application of the query that mentions a name that a quantifier of the
query binds is not a term at which a sentence is instantiated.

r[module.instance.listed]
A quantified variable of a listed type that no matched application binds
takes each value of its type, as a [quantifier over listed
types](Quantifiers.md#meaning) does (`lang::listed_variable`).

r[module.instance.unused]
A quantified variable that the sentence does not mention takes no term (`lang::sentence_instantiation`).

r[module.instance.hypothesis]
Each instance adds its claims, under its domain, as one hypothesis of the
query. The applications and calls that the instance has are terms of the
query too, but for those that mention a name that stays quantified.

r[module.instance.quantifiers]
A quantifier within a sentence, and a variable that stays quantified
(`module.binding.outside`), are quantifiers of each instance. Where their
types are not listed, the instance is outside the [decidable
core](Decidability.md), and `undecidable` reports it at the sentence, as
it reports an [unbounded quantifier](Quantifiers.md#unbounded-quantifiers).

r[module.closure]
Fren instantiates each sentence that the check uses at the terms of the
query and of the instances, until no new instance arises. The *closure* is
the set of all those instances.

r[module.closure.finite]
The closure of every query is finite. Take the items in reverse order
(`module.order.items`). An instance applies its subject only to quantified
variables, which matching binds to proper subterms of the query's terms,
to values of listed types, and to closed terms of the sentence. It applies
every other item only where that item comes before the subject. So the
arguments of each item's applications are among finitely many terms, once
the applications of the items after it are finitely many. No bound on the
number of rounds is part of the language.

r[module.instance.models]
A model of a query whose hypotheses include instances of axioms is a
model of those instances, not always of the axioms. Fren reports it as a
counterexample, or as a witness of consistency, only where it confirms
that the model meets the axioms themselves. Where it does not, a check
that uses only today's laws asks today's query, with the laws quantified
([Traits](Traits.md#expectations)), and any other check is Inconclusive.

r[module.use]
A check instantiates the sentences that are visible to it and meet the
binding rule, whose subject the closure applies (`lang::sentence_use`): every
axiom of its module and of the modules it imports, wherever it is
declared, and each theorem declared before the check's item. An `ensure`
is used as a [contract](Items.md#contracts) is.

r[module.use.subject]
A sentence is used where its subject is applied by the query, or by an
instance of a used sentence (`lang::sentence_use`).

r[module.use.verdict]
A check uses a lemma whatever the lemma's own verdict. Where the check
passes, the pass rests on the lemma's check ([Evidence](../Evidence.md#resting-on-checks)).

r[module.use.laws]
The laws of a trait are visible to the checks of the trait's lemmas and
expectations, wherever each is written, as [Traits](Traits.md#expectations)
states (`lang::axioms_anywhere`).

r[module.use.morphism]
The sentences visible to a check are those of its module, of the modules
that it imports, and their theorems and axioms translated along the
implementations that the check's terms use: an interface's at each of its
implementations, and a generic function's at each of its instances. Each
is used as `module.use` states, at its translation's subject.

r[module.no-patterns]
No sentence states how it is instantiated, and no setting changes it.

```fren
-- An argument of an application in a sentence, as written: one of the
-- sentence's quantified variables, a closed term, which mentions none of
-- them, or another term.
pub enum SentenceArg { Variable, Closed, Compound }

-- An application of a function, or a call of a procedure, in a sentence.
pub struct SentenceApplication {
    item: Int,                  -- the item applied or called, by its place in the order of items
    call?,                      -- it is a call
    args: Seq<SentenceArg>,     -- its arguments
    point: Int,                 -- its arguments as written: applications with the same arguments have the same point
    mentions: Set<Int>,         -- the quantified variables that occur in it, by position
    inner?,                     -- it mentions a name that a quantifier within the sentence binds
}

-- A sentence's applications and calls, in the order written.
pub enum Applications { Nil, Cons(SentenceApplication, Applications) }

-- A quantified variable of a sentence.
pub struct SentenceVariable {
    mentioned?,                 -- the sentence mentions it
    listed?,                    -- its type is listed
}

-- A sentence's quantified variables, in order.
pub enum SentenceVariables { Nil, Cons(SentenceVariable, SentenceVariables) }

-- Whether a sentence meets the binding rule; or the first variable that
-- breaks it, by position.
pub enum SentenceInstantiation { Instantiable, Unbound(Int) }

-- The item, of those that `apps` applies or calls, that comes last, and -1 where there is none.
pub fn last_item(apps: Applications): Int := match apps {
    Applications::Nil => -1,
    Applications::Cons(a, rest) => a.item.max(last_item(rest)),
}

-- Whether `a` applies the function `s`, outside every quantifier of the sentence.
pub fn outer_application?(a: SentenceApplication, s: Int) :=
    a.item = s and not a.call? and not a.inner?

-- Membership in a sequence is outside the decidable core.
set_option fren.lint.undecidable "allow" in
pub fn compound_application?(a: SentenceApplication, s: Int) :=
    outer_application?(a, s) and SentenceArg::Compound in a.args

pub fn has_compound?(apps: Applications, s: Int) := match apps {
    Applications::Nil => false,
    Applications::Cons(a, rest) => compound_application?(a, s) or has_compound?(rest, s),
}

-- Whether `a` is an anchor of a sentence whose subject is `s`, where
-- `compound?` says whether one of its applications of `s` has a compound
-- argument.
pub fn anchor?(a: SentenceApplication, s: Int, compound?) :=
    outer_application?(a, s) and (compound_application?(a, s) or not compound?)

pub fn matched?(a: SentenceApplication, s: Int, compound?) :=
    anchor?(a, s, compound?) or (a.call? and not a.inner?)

-- The positions of the anchors of `apps`, the first at position `k`.
pub fn anchor_positions(apps: Applications, s: Int, compound?, k: Int): Set<Int> := match apps {
    Applications::Nil => {},
    Applications::Cons(a, rest) =>
        (if anchor?(a, s, compound?) then {k} else {}) union anchor_positions(rest, s, compound?, k + 1),
}

-- Whether a matched application of `apps` mentions the variable `v`.
pub fn bound?(apps: Applications, v: Int, s: Int, compound?) := match apps {
    Applications::Nil => false,
    Applications::Cons(a, rest) =>
        (matched?(a, s, compound?) and v in a.mentions) or bound?(rest, v, s, compound?),
}

-- Whether an application of `apps` mentions the variable `v`.
pub fn in_application?(apps: Applications, v: Int) := match apps {
    Applications::Nil => false,
    Applications::Cons(a, rest) => v in a.mentions or in_application?(rest, v),
}

-- The first variable that the binding rule needs bound and is not, the
-- first at position `v`, and -1 where there is none.
pub fn first_unbound(vars: SentenceVariables, apps: Applications, v: Int, s: Int, compound?): Int :=
    match vars {
        SentenceVariables::Nil => -1,
        SentenceVariables::Cons(x, rest) =>
            if not x.listed? and in_application?(apps, v) and not bound?(apps, v, s, compound?)
            then v else first_unbound(rest, apps, v + 1, s, compound?),
    }

-- Whether a sentence with these variables and applications meets the binding rule.
pub fn instantiation_verdict(vars: SentenceVariables, apps: Applications): SentenceInstantiation :=
    if first_unbound(
        vars,
        apps,
        0,
        last_item(apps),
        has_compound?(apps, last_item(apps))
    ) = -1
    then SentenceInstantiation::Instantiable
    else SentenceInstantiation::Unbound(
        first_unbound(
            vars,
            apps,
            0,
            last_item(apps),
            has_compound?(apps, last_item(apps))
        )
    )

set_option fren.evidence "random" in
pub proc sentence_instantiation(
    variables: SentenceVariables,    -- its quantified variables, in order
    applications: Applications,      -- its applications and calls, in the order written
): (det subject: Int, det anchors: Set<Int>, det verdict: SentenceInstantiation) {
    out subject := last_item(applications)
    out anchors := anchor_positions(
        applications,
        subject,
        has_compound?(applications, subject),
        0
    )
    out verdict := instantiation_verdict(variables, applications)

    expect no_variables: when variables = SentenceVariables::Nil, verdict = SentenceInstantiation::Instantiable
    expect no_applications: when applications = Applications::Nil, verdict = SentenceInstantiation::Instantiable
}
```

r[module.instantiation.examples]
The law `get_put` of [Traits](Traits.md) has one anchor,
`get(put(s, k, v), j)`, which binds all four variables. It is
instantiated at each application of `get` to an application of `put`
(`lang::get_put_instantiation`). Of `f(x) = f(f(x))`, `f(f(x))` is the only
anchor (`lang::nested_anchor`). Of `f(g(x)) = f(g(g(x)))`, both
applications of `f` are anchors, matched at once, so an instance arises
only where both are terms of the query, and adds no application of `f`.
Of `f(a, b) = f(b, a)`, both applications are anchors, so it relates
`f(c, d)` and `f(d, c)` only where both are terms of the query.
`f(x) <= g(x, y)`, where `g` comes before `f`, leaves `y` unbound
(`lang::unbound_variable`). A law may come before the methods it mentions
(`lang::law_before_method`). A law whose variable is a `Bool` that no
application has, such as `law flagged(s: Self, b?): when b?, obs(s) >= 0`,
takes both values of it (`lang::listed_variable`), and `law bounded(s:
Self, n: Int): when n > 0, h(s) >= 0` keeps `n` quantified
(`lang::outside_variable`).

```fren
-- An application, outside every quantifier, of `item` at `point` to `args`, which mention `mentions`.
pub fn app(
    item: Int,
    point: Int,
    args: Seq<SentenceArg>,
    mentions: Set<Int>
): SentenceApplication := SentenceApplication {
    item,
    call? := false,
    args,
    point,
    mentions,
    inner? := false,
}

pub fn quantified(listed?): SentenceVariable := SentenceVariable { mentioned? := true, listed? }

-- `law get_put(s: Self, k: Key, v: Int, j: Key): get(put(s, k, v), j) = (if j = k then Option::Some(v) else get(s, j))`,
-- with `put` at 1 and `get` at 2.
pub const GET_PUT_VARIABLES: SentenceVariables := SentenceVariables::Cons(
    quantified(false),
    SentenceVariables::Cons(
        quantified(false),
        SentenceVariables::Cons(
            quantified(false),
            SentenceVariables::Cons(quantified(false), SentenceVariables::Nil)
        )
    )
)

pub const GET_PUT_APPLICATIONS: Applications := Applications::Cons(
    app(
        2,
        0,
        [SentenceArg::Compound, SentenceArg::Variable],
        {0, 1, 2, 3}
    ),
    Applications::Cons(
        app(
            1,
            1,
            [
                SentenceArg::Variable,
                SentenceArg::Variable,
                SentenceArg::Variable,
            ],
            {0, 1, 2}
        ),
        Applications::Cons(
            app(2, 2, [SentenceArg::Variable, SentenceArg::Variable], {0, 3}),
            Applications::Nil
        )
    )
)

set_option fren.evidence "random" in
expect get_put_instantiation() {
    call r := sentence_instantiation(GET_PUT_VARIABLES, GET_PUT_APPLICATIONS)
    expect subject: r.subject = 2
    expect one_anchor: r.anchors = {0}
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- One variable, which the sentence mentions and whose type is not listed.
pub const ONE_VARIABLE: SentenceVariables :=
    SentenceVariables::Cons(quantified(false), SentenceVariables::Nil)

-- `f(x) = f(f(x))`, with `f` at 1: the applications `f(x)`, `f(f(x))` and the inner `f(x)`.
pub const NESTED_APPLICATIONS: Applications := Applications::Cons(
    app(1, 0, [SentenceArg::Variable], {0}),
    Applications::Cons(
        app(1, 1, [SentenceArg::Compound], {0}),
        Applications::Cons(app(1, 0, [SentenceArg::Variable], {0}), Applications::Nil)
    )
)

set_option fren.evidence "random" in
expect nested_anchor() {
    call r := sentence_instantiation(ONE_VARIABLE, NESTED_APPLICATIONS)
    expect outer_only: r.anchors = {1}
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- `f(x) <= g(x, y)`, with `g` at 1 and `f` at 2.
pub const TWO_VARIABLES: SentenceVariables := SentenceVariables::Cons(
    quantified(false),
    SentenceVariables::Cons(quantified(false), SentenceVariables::Nil)
)

set_option fren.evidence "random" in
expect unbound_variable() {
    call r := sentence_instantiation(
        TWO_VARIABLES,
        Applications::Cons(
            app(2, 0, [SentenceArg::Variable], {0}),
            Applications::Cons(
                app(1, 1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
                Applications::Nil
            )
        ),
    )
    expect y_unbound: r.verdict = SentenceInstantiation::Unbound(1)
}

-- `law l(s: Self): f(s) >= 0`, written before `fn f(Self): Int`: the law
-- applies `f`, at 1, wherever it is declared.
set_option fren.evidence "random" in
expect law_before_method() {
    call r := sentence_instantiation(
        ONE_VARIABLE,
        Applications::Cons(app(1, 0, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
    expect anchored: r.anchors = {0}
}

-- `law flagged(s: Self, b?): when b?, obs(s) >= 0`, with `obs` at 1.
set_option fren.evidence "random" in
expect listed_variable() {
    call r := sentence_instantiation(
        SentenceVariables::Cons(
            quantified(false),
            SentenceVariables::Cons(quantified(true), SentenceVariables::Nil)
        ),
        Applications::Cons(app(1, 0, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- `law bounded(s: Self, n: Int): when n > 0, h(s) >= 0`, with `h` at 1:
-- `n` is in no application.
set_option fren.evidence "random" in
expect outside_variable() {
    call r := sentence_instantiation(
        TWO_VARIABLES,
        Applications::Cons(app(1, 0, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}
```

`lang::sentence_use` states which sentences a check uses, from the
sentences visible to it and the items that its query applies:

```fren
-- A lemma, `assume` item or law, or a goal, visible to a check. `Ensure`
-- is an `ensure` clause of an abstract item.
pub struct Sentence {
    kind: SentenceKind,
    position: Int,                   -- its position in declaration order
    variables: SentenceVariables,
    applications: Applications,
}

pub enum Sentences { Nil, Cons(Sentence, Sentences) }

-- The items that `apps` applies or calls.
pub fn applied_items(apps: Applications): Set<Int> := match apps {
    Applications::Nil => {},
    Applications::Cons(a, rest) => {a.item} union applied_items(rest),
}

-- Whether `p` is an axiom: an `assume` item, a law, or an `ensure` clause of an abstract item.
pub fn axiom?(p: Sentence) :=
    p.kind in {
        SentenceKind::Assume,
        SentenceKind::Law,
        SentenceKind::Ensure,
    }

-- Whether `p` may be used by a check of the item at `check`, where its
-- subject is applied: an axiom, wherever it is declared, or a lemma
-- declared before the item, that meets the binding rule.
pub fn fact?(p: Sentence, check: Int) :=
    (axiom?(p) or (p.kind = SentenceKind::Lemma and p.position < check))
    and instantiation_verdict(p.variables, p.applications) = SentenceInstantiation::Instantiable

-- Whether `p` is used where the query and the instances apply `items`.
pub fn used?(p: Sentence, check: Int, items: Set<Int>) :=
    fact?(p, check) and last_item(p.applications) in items

-- The items that the instances of the sentences of `ps` that `items` brings apply.
pub fn brought(ps: Sentences, check: Int, items: Set<Int>): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) =>
        (if used?(p, check, items) then applied_items(p.applications) else {}) union brought(rest, check, items),
}

-- `items`, with what the sentences `all` bring, once for each sentence of `rounds`.
pub fn reach(rounds: Sentences, all: Sentences, check: Int, items: Set<Int>): Set<Int> :=
    match rounds {
        Sentences::Nil => items,
        Sentences::Cons(_, rest) => reach(rest, all, check, items union brought(all, check, items)),
    }

-- The laws of `ps` that break the binding rule, which every check of
-- their trait uses as today, quantified (`module.rules.laws`).
pub fn quantified_laws(ps: Sentences): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) =>
        (if p.kind = SentenceKind::Law
            and instantiation_verdict(p.variables, p.applications) != SentenceInstantiation::Instantiable
            then {p.position} else {}) union quantified_laws(rest),
}

pub fn used_positions(ps: Sentences, check: Int, items: Set<Int>): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) =>
        (if used?(p, check, items) then {p.position} else {}) union used_positions(rest, check, items),
}

set_option fren.evidence "random" in
pub proc sentence_use(
    check: Int,                  -- the position of the item whose check it is
    sentences: Sentences,        -- the sentences visible to the check
    applied: Set<Int>,           -- the items that the query applies or calls
): (
    det reached: Set<Int>,       -- the items that the query and the instances apply
    det used: Set<Int>,          -- the sentences that the check instantiates
    det kept_quantified: Set<Int>,   -- the laws that it uses as today, quantified
) {
    out reached := reach(sentences, sentences, check, applied)
    out used := used_positions(sentences, check, reached)
    out kept_quantified := quantified_laws(sentences)

    expect query_items_reached: applied subset reached
    expect nothing_visible: when sentences = Sentences::Nil, used = {} and kept_quantified = {}
}

-- `assume made(fs: Fs, p: Path): exists?(mkdir(fs, p), p)`, with `mkdir`
-- at 1, `exists?` at 2 and the axiom at 3.
pub fn made(keyword: SentenceKind): Sentences := Sentences::Cons(
    Sentence {
        kind := keyword,
        position := 3,
        variables := TWO_VARIABLES,
        applications := Applications::Cons(
            app(2, 0, [SentenceArg::Compound, SentenceArg::Variable], {0, 1}),
            Applications::Cons(
                app(1, 1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
                Applications::Nil
            )
        ),
    },
    Sentences::Nil
)

-- A check that applies `exists?` uses it, and reaches `mkdir`.
set_option fren.evidence "random" in
expect made_used() {
    call r := sentence_use(4, made(SentenceKind::Assume), {2})
    expect used: r.used = {3}
    expect reaches_mkdir: 1 in r.reached
}

-- One that applies only `mkdir` does not.
set_option fren.evidence "random" in
expect made_unused() {
    call r := sentence_use(4, made(SentenceKind::Assume), {1})
    expect unused: r.used = {}
}

-- An axiom is used by the check of an item declared before it, as a law
-- is by an expectation written before it; a lemma is not.
set_option fren.evidence "random" in
expect axioms_anywhere() {
    call assumed := sentence_use(2, made(SentenceKind::Assume), {2})
    expect used_before: assumed.used = {3}
}

-- `law l(s: Self, t: Self): f(s) <= g(s, t)`, with `g` at 1, `f` at 2
-- and the law at 3, breaks the binding rule, so every check of its trait
-- uses it quantified, whatever its query applies.
pub const UNBOUND_LAW: Sentence := Sentence {
    kind := SentenceKind::Law,
    position := 3,
    variables := TWO_VARIABLES,
    applications := Applications::Cons(
        app(2, 0, [SentenceArg::Variable], {0}),
        Applications::Cons(
            app(1, 1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
            Applications::Nil
        )
    ),
}

set_option fren.evidence "random" in
expect unbound_law_quantified() {
    call r := sentence_use(4, Sentences::Cons(UNBOUND_LAW, Sentences::Nil), {})
    expect quantified: r.kept_quantified = {3}
    expect not_instantiated: r.used = {}
}

set_option fren.evidence "random" in
expect lemmas_ranked() {
    call lemma := sentence_use(2, made(SentenceKind::Lemma), {2})
    expect not_before: lemma.used = {}
}
```

> **Rationale:** Instantiating at the query's own terms keeps each query
> free of the sentences' own quantifiers, and its verdict the same in both
> front ends. In the experiment of #669, ground instances always sufficed:
> every theorem that was not proved needed a generalization or a lemma
> that nobody wrote. The binding rule takes variables only from the
> subject's applications because the closure would not end otherwise: with
> `forall z, f(z) = g(z)` taking `z` from `f`'s arguments, and `forall x,
> f(g(x)) = 0`, each application `g(a)` brings `f(g(a))`, which brings
> `g(g(a))`, and so on. Matching the anchors at once is needed too: matched
> one at a time, `f(g(x)) = f(g(g(x)))` brings `f(g(g(g(c))))` from
> `f(g(g(c)))`, and so on. Axioms are used wherever they are declared,
> since no axiom is proved and so none can rest on a check that rests on
> it. Theorems are ranked, so that no proof rests on itself. A model of the
> instances alone need not be one of the axioms: `forall (n: Nat), f(n) >
> f(n + 1)`, with `f` to `Nat`, has no model, but each finite set of its
> instances does. Fren chooses the instances that F\*'s `SMTPat` and
> Dafny's triggers have the author choose.

## Checks

**Proof obligations**

r[module.theorem.check]
A lemma has the checks of a [global
expectation](../Check.md#global-expectations) with its parameters, its
domain, its calls and its claims, each using the sentences that
`module.use` gives. A theorem that these checks do not prove is checked by
induction, where `module.induction` applies.

r[module.axiom.check]
An axiom is never proved. Fren checks that the axioms of each module can
hold together (its *consistency*), item by abstract item, in the tier that
`lang::axiom_tier` gives.

r[module.depends]
A sentence *depends on* each abstract item that it applies or calls, and on
each abstract item that the definition of a defined item it applies
depends on, through definitions in turn. A definition mentions only items
declared before its own ([Functions](Items.md#functions)).

r[module.axiom.owner]
Each axiom that depends on an abstract item has one *owner*: the last, in
the order of items, of the abstract items that it depends on
(`lang::axiom_owner`). The axioms of an abstract item are those it owns.

r[module.contract.earlier]
A contract mentions only the items declared before its function, and the
function itself ([Contracts](Items.md#contracts)). The owner of an
`ensure` clause is its own item.

r[module.tier.modular]
An abstract item that owns only `ensure` clauses, and axioms that depend on
no other abstract item, is checked as today: it is *realizable* where, for
each argument that meets its domain, some value meets its axioms, whatever
the other items are (tier 1,
[Realizability](../Check.md#contracts-of-uninterpreted-functions)).

r[module.tier.pointwise]
An axiom is *pointwise* where all its applications and calls of its owner
have the same arguments, as `f(x)` in each of `f`'s contracts, and none of
the definitions of the defined items it applies depends on its owner.

r[module.tier.relative]
An abstract item that owns only pointwise axioms, some of them depending
on other abstract items, is *relatively realizable* where, for every
interpretation of the items before it that meets the axioms they own, each
argument that meets its domain has a value that meets the axioms it owns
(tier 2), as in the rely-guarantee method. Fren asks it with the instances
of those items' axioms at the query's terms as the rely, which considers
more interpretations, not fewer.

r[module.tier.joint]
An abstract item that owns an axiom that is not pointwise, or that is not
shown relatively realizable, is checked with the module's other axioms:
they are *jointly consistent* where some interpretation of the module's
abstract items meets all of them (tier 3).

r[module.tier.order]
Where every abstract item of a module is realizable in tier 1 or tier 2,
its axioms are jointly consistent (`lang::relative_tiers`). The proof is by
induction on the order of items: an interpretation of the items before an
item that meets the axioms they own extends, by a value at each argument
that its tier gives, to one of the item as well. It rests on
`module.contract.earlier` for tier 1, and on `module.axiom.owner` for tier
2: an item's axioms depend only on it and on abstract items before it. A
defined item that an axiom applies may come after its owner, but its
definition depends only on abstract items that the owner's choice covers
(`module.depends`), so its meaning is fixed once they are interpreted, and
the axiom constrains only the owner and the items before it.

r[module.tier.theories]
The tiers are the same for every theory, whichever construct it is: a
module's abstract items, an interface's `Self` and methods, and a generic
function's type parameters and their bounds' members.

r[module.consistency.evidence]
The evidence of consistency is, from strongest to weakest: a total
implementation whose obligations hold (a *witness*), a tier's proof, an
interpretation that bounded model finding finds up to its bound, or none,
which is Inconclusive (`lang::consistency`). A model of the axioms'
instances alone is no evidence (`module.instance.models`).

r[module.consistency.vacuity]
Where the axioms cannot hold together, every check that uses them holds
vacuously, and the report names a minimal set of axioms that cannot hold
together. Where an item's tier fails, the report names the axioms it owns.

r[module.assume.trusted]
An axiom that no implementation makes an obligation is reported as
trusted: a pass that rests on it says that it does, as one that rests on a
trait's laws does (`F0665`).

r[module.inst]
An implementation of an interface, `mod x: I<T>` or an `inst`, is a total
morphism from the interface (`module.implementation`). Each law is an
obligation of it, over its `Self` and its members. Where every law holds,
each lemma of the interface holds of the implementation without another
check, and the implementation is a witness of the laws' consistency.

r[module.inst.group]
A group of abstract functions that is meant to be implemented together is
an interface, and a refinement of the group is an implementation of it.

r[module.impl]
The [`impl`](../Impl.md) and [`interp`](../Impl.md#interpretations)
bindings of a spec are an implementation of its module, partial where
some abstract item has neither. An axiom that becomes an obligation of it
is proved in Lean, and where the implementation is total, it is a witness
of the module's consistency.

r[module.generic.check]
A generic function's contract is checked once, at its type parameters, as
the theorems of its one-item theory, and each instance `f<Int>` uses it
translated, by `module.implementation.theorems`.

```fren
-- Which tier checks an abstract item's axioms.
pub enum Tier { Modular, Relative, Joint }

-- The first point at which `apps` applies or calls `s`, and -1 where none is.
pub fn first_point(apps: Applications, s: Int): Int := match apps {
    Applications::Nil => -1,
    Applications::Cons(a, rest) => if a.item = s then a.point else first_point(rest, s),
}

-- Whether every application and call of `s` in `apps` is at the point `p`.
pub fn all_at?(apps: Applications, s: Int, p: Int) := match apps {
    Applications::Nil => true,
    Applications::Cons(a, rest) => (a.item != s or a.point = p) and all_at?(rest, s, p),
}

-- A module's abstract items, in the order of items.
pub enum AbstractItems { Nil, Cons(Int, AbstractItems) }

pub fn item_set(items: AbstractItems): Set<Int> := match items {
    AbstractItems::Nil => {},
    AbstractItems::Cons(a, rest) => {a} union item_set(rest),
}

-- The last of `items` that is in `among`, and -1 where none is.
pub fn last_among(items: AbstractItems, among: Set<Int>): Int := match items {
    AbstractItems::Nil => -1,
    AbstractItems::Cons(a, rest) =>
        if last_among(rest, among) != -1 then last_among(rest, among)
        else if a in among then a else -1,
}

-- The items that the definitions of the defined items that `p` applies
-- apply, through definitions in turn, where `defines` relates each defined
-- item to the items that its definition applies.
set_option fren.lint.undecidable "allow" in
pub fn through_definitions(p: Sentence, defines: Rel<Int, Int>): Set<Int> :=
    defines.closure.image(applied_items(p.applications))

-- The abstract items that `p` depends on (`module.depends`).
pub fn depends(p: Sentence, abstract: AbstractItems, defines: Rel<Int, Int>): Set<Int> :=
    (applied_items(p.applications) union through_definitions(p, defines)) inter item_set(abstract)

-- The owner of `p`: the last abstract item it depends on, and -1 where it depends on none.
pub fn owner(p: Sentence, abstract: AbstractItems, defines: Rel<Int, Int>): Int :=
    last_among(abstract, depends(p, abstract, defines))

pub fn pointwise?(p: Sentence, item: Int, defines: Rel<Int, Int>) :=
    not item in through_definitions(p, defines)
    and all_at?(p.applications, item, first_point(p.applications, item))

-- Whether `p` is an axiom that `item` owns.
pub fn owns?(p: Sentence, item: Int, abstract: AbstractItems, defines: Rel<Int, Int>) :=
    axiom?(p) and owner(p, abstract, defines) = item

-- Whether an axiom of `item` keeps it in tier 1: an `ensure` clause, or one that depends on no other abstract item.
pub fn modular_axiom?(p: Sentence, item: Int, abstract: AbstractItems, defines: Rel<Int, Int>) :=
    p.kind = SentenceKind::Ensure or depends(p, abstract, defines) subset {item}

pub fn owned(ps: Sentences, item: Int, abstract: AbstractItems, defines: Rel<Int, Int>): Set<Int> :=
    match ps {
        Sentences::Nil => {},
        Sentences::Cons(p, rest) =>
            (if owns?(p, item, abstract, defines) then {p.position} else {}) union owned(rest, item, abstract, defines),
    }

pub fn all_modular?(ps: Sentences, item: Int, abstract: AbstractItems, defines: Rel<Int, Int>) :=
    match ps {
        Sentences::Nil => true,
        Sentences::Cons(p, rest) =>
            (not owns?(p, item, abstract, defines) or modular_axiom?(p, item, abstract, defines))
            and all_modular?(rest, item, abstract, defines),
    }

pub fn all_pointwise?(ps: Sentences, item: Int, abstract: AbstractItems, defines: Rel<Int, Int>) :=
    match ps {
        Sentences::Nil => true,
        Sentences::Cons(p, rest) =>
            (not owns?(p, item, abstract, defines) or pointwise?(p, item, defines))
            and all_pointwise?(rest, item, abstract, defines),
    }

set_option fren.evidence "random" in
pub proc axiom_owner(
    sentence: Sentence,
    abstract: AbstractItems,     -- the module's abstract items, in order
    defines: Rel<Int, Int>,      -- `(d, a)`: the definition of the defined item `d` applies `a`
): (det owned_by: Int) {
    out owned_by := owner(sentence, abstract, defines)

    -- Every axiom that depends on an abstract item has an abstract owner, which it depends on.
    expect abstract_owner: owned_by in depends(sentence, abstract, defines)
        or (owned_by = -1 and depends(sentence, abstract, defines) = {})
}

set_option fren.evidence "random" in
pub proc axiom_tier(
    item: Int,                   -- the abstract item, by its place in the order of items
    abstract: AbstractItems,     -- the module's abstract items, in order
    defines: Rel<Int, Int>,      -- `(d, a)`: the definition of the defined item `d` applies `a`
    sentences: Sentences,        -- the module's axioms
): (det owns: Set<Int>, det tier: Tier) {
    out owns := owned(sentences, item, abstract, defines)
    out tier :=
        if all_modular?(sentences, item, abstract, defines) then Tier::Modular
        else if all_pointwise?(sentences, item, abstract, defines) then Tier::Relative else Tier::Joint

    expect nothing_owned: when sentences = Sentences::Nil, tier = Tier::Modular
}

-- `assume ax(x: Int): f(x) >= g(x) + 1 and g(x) >= f(x) + 1`, with `f` at
-- 1, `g` at 2 and the axiom at 3: `g` owns it, and it is pointwise, so `g`
-- is checked in tier 2, which it fails, naming `ax`. `f` owns nothing.
pub const SHARED_AXIOM: Sentences := Sentences::Cons(
    Sentence {
        kind := SentenceKind::Assume,
        position := 3,
        variables := ONE_VARIABLE,
        applications := Applications::Cons(
            app(1, 0, [SentenceArg::Variable], {0}),
            Applications::Cons(app(2, 0, [SentenceArg::Variable], {0}), Applications::Nil)
        ),
    },
    Sentences::Nil
)

pub const F_AND_G: AbstractItems :=
    AbstractItems::Cons(1, AbstractItems::Cons(2, AbstractItems::Nil))

set_option fren.evidence "random" in
expect shared_axiom_owned() {
    call g := axiom_tier(2, F_AND_G, {}, SHARED_AXIOM)
    expect g_owns_it: g.owns = {3}
    expect g_relative: g.tier = Tier::Relative
}

set_option fren.evidence "random" in
expect shared_axiom_not_earlier() {
    call f := axiom_tier(1, F_AND_G, {}, SHARED_AXIOM)
    expect f_owns_nothing: f.owns = {}
}

-- `assume ax(x: Int): h(g(x)) > g(x)`, with `g` abstract at 1, `fn h(y:
-- Int): Int := y` defined at 2, and the axiom at 3: its last item is `h`,
-- but its owner is `g`, which is checked in tier 1 and fails, since no
-- value `v` meets `h(v) > v`.
pub const DEFINED_LAST: Sentence := Sentence {
    kind := SentenceKind::Assume,
    position := 3,
    variables := ONE_VARIABLE,
    applications := Applications::Cons(
        app(2, 0, [SentenceArg::Compound], {0}),
        Applications::Cons(
            app(1, 1, [SentenceArg::Variable], {0}),
            Applications::Cons(app(1, 1, [SentenceArg::Variable], {0}), Applications::Nil)
        )
    ),
}

pub const ONLY_G: AbstractItems := AbstractItems::Cons(1, AbstractItems::Nil)

set_option fren.evidence "random" in
expect defined_last_owned() {
    call g := axiom_tier(1, ONLY_G, {}, Sentences::Cons(DEFINED_LAST, Sentences::Nil))
    expect g_owns_it: g.owns = {3}
    expect g_modular: g.tier = Tier::Modular
}

-- The same axiom, where `h(y) := t(y)` applies an abstract `t` at 2, so
-- that `h` comes at 3 and the axiom at 4: its owner is `t`, which it
-- depends on through `h`'s definition, and it is not pointwise for `t`.
pub const THROUGH_DEFINITION: Sentence := Sentence {
    kind := SentenceKind::Assume,
    position := 4,
    variables := ONE_VARIABLE,
    applications := Applications::Cons(
        app(3, 0, [SentenceArg::Compound], {0}),
        Applications::Cons(
            app(1, 1, [SentenceArg::Variable], {0}),
            Applications::Cons(app(1, 1, [SentenceArg::Variable], {0}), Applications::Nil)
        )
    ),
}

set_option fren.evidence "random" in
expect owner_through_definition() {
    call o := axiom_owner(THROUGH_DEFINITION, F_AND_G, {(3, 2)})
    expect owned_by_t: o.owned_by = 2
}

set_option fren.evidence "random" in
expect tier_through_definition() {
    call t := axiom_tier(
        2,
        F_AND_G,
        {(3, 2)},
        Sentences::Cons(THROUGH_DEFINITION, Sentences::Nil),
    )
    expect t_owns_it: t.owns = {4}
    expect t_joint: t.tier = Tier::Joint
}

-- An interpretation of a function from `Bool` to `Bool`: its values at
-- `false` and at `true`.
pub struct Table { at_false?, at_true? }

-- An interpretation of two such functions, `f`, which comes first, and `g`.
pub struct Tables { f: Table, g: Table }

-- Tier 2 over two abstract functions, with their interpretations as the
-- values: `f`'s axioms constrain `f` alone, and `g`'s both.
pub proc relative_tiers(
    f_meets: Set<Table>,         -- the interpretations of `f` that meet the axioms that `f` owns
    g_meets: Set<Tables>,        -- the interpretations of both that meet the axioms that `g` owns
): (det f_realizable?, det g_realizable?, det consistent?) {
    out f_realizable? := f_meets != {}
    out g_realizable? :=
        forall (t: Table), when t in f_meets, exists (u: Table), Tables { f := t, g := u } in g_meets
    out consistent? :=
        exists (t: Table) (u: Table), t in f_meets and Tables { f := t, g := u } in g_meets

    expect tiers_give_consistency: when f_realizable? and g_realizable?, consistent?
    -- The axiom that no interpretation meets is caught at its owner.
    expect contradiction_caught: when g_meets = {} and f_realizable?, not g_realizable?
}
```

> **Rationale:** The file system of #631 has abstract functions, such as
> `at`, `mkdir` and `rm`, whose sentences relate them, and so fail tier 1,
> which asks each to be realizable whatever the others are. Tier 2 is the
> rely-guarantee reading of such a group, ordered by the items' order so
> that an axiom that relates `f` and `g` is checked once, at the later of
> them, against the earlier one's own axioms. Asking each item of `assume
> ax(x: Int): f(x) >= g(x) + 1 and g(x) >= f(x) + 1` against the others'
> axioms, `ax` included, would find both realizable, since no
> interpretation meets `ax`. Tier 3 is the consistency of ACL2's
> `encapsulate`, Why3's realizations and Alloy's `run`. A group that
> cannot hold together makes every check that uses it vacuous, so the
> report must say which axioms to blame.

```fren
-- The outcome of a query about consistency: shown to hold, shown not to,
-- or not decided.
pub enum Answer { Holds, Fails, Unknown }

-- The evidence that an abstract item's axioms can hold.
pub enum ConsistencyEvidence {
    Witness,          -- a total implementation meets them
    Modular,          -- tier 1
    Relative,         -- tier 2
    Joint,            -- tier 3
    Bounded,          -- bounded model finding found an interpretation up to its bound
    Unrealizable,     -- tier 1 fails: some argument has no value
    Inconsistent,     -- tier 3 fails: no interpretation meets them
    Inconclusive,
}

set_option fren.evidence "random" in
pub proc consistency(
    tier: Tier,            -- the item's tier (`lang::axiom_tier`)
    witness?,              -- a total implementation of the module meets its axioms
    modular: Answer,       -- the tier 1 query: realizable whatever the others are
    relative: Answer,      -- the tier 2 query: realizable for every interpretation of the items before it that meets their axioms
    joint: Answer,         -- the tier 3 query: some interpretation meets all the axioms
    found?,                -- bounded model finding found an interpretation up to its bound
): (det evidence: ConsistencyEvidence) {
    use self::ConsistencyEvidence::{
        Bounded,
        Inconclusive,
        Inconsistent,
        Joint,
        Modular,
        Relative,
        Unrealizable,
        Witness,
    }

    out evidence :=
        if witness? then Witness
        else if tier = Tier::Modular then (match modular {
            Answer::Holds => Modular,
            Answer::Fails => Unrealizable,
            Answer::Unknown => Inconclusive,
        })
        else if tier = Tier::Relative and relative = Answer::Holds then Relative
        else match joint {
            Answer::Holds => Joint,
            Answer::Fails => Inconsistent,
            Answer::Unknown => if found? then Bounded else Inconclusive,
        }

    -- Tier 1 is today's check, and an item in it is never judged by the later tiers.
    expect as_today: when not witness? and tier = Tier::Modular, evidence in {Modular, Unrealizable, Inconclusive}
    expect witness_suffices: when witness?, evidence = Witness
    expect relative_only_pointwise: when evidence = Relative, tier = Tier::Relative
    expect inconsistency_needs_proof: when evidence = Inconsistent, joint = Answer::Fails
}
```

The `joint` query is the solver's, over the axioms themselves, and a model
of their instances alone does not answer it `Holds`
(`module.instance.models`).

## Metatheory

The rules above rest on properties of the logic and of the language. Each
is stated here, over morphisms of every kind, with the rule that relies on
it, and whether it is argued or open (#669).

**Dynamic semantics**

r[module.meta.satisfaction]
The *satisfaction condition* holds: a model of an implementing module,
reduced along the implementation, is a model of the implemented module,
and it meets a sentence's translation exactly where its reduction meets
the sentence (Goguen and Burstall's institutions, 1992).
`module.implementation.obligations` and `module.implementation.theorems`
rely on it. It is argued for Fren's many-sorted first-order logic, and its
proof in Lean is open.

r[module.meta.theorems]
A morphism preserves theorems: where its obligations hold, the translation
of each theorem of its source holds in its target. It follows from `module.meta.satisfaction`, as in CASL's
views and ACL2's functional instantiation (Kaufmann and Moore).
`module.implementation.theorems`, `module.morphism.transport`,
`module.trait.lemma` and `module.generic.check` rely on it. It is argued.

r[module.meta.composition]
Morphisms compose, and each module has the identity morphism: the
translation along the composite of two morphisms is the translation along
one, then along the other. A generic function applied within another
generic function, an implementation of a generic module, and an
implementation of an interface that extends another, rely on it
(`module.implementation.instantiate`, `module.extends`). It is argued, as
substitutions compose, and its proof is open.

r[module.meta.conservative]
A module's defined items are a *conservative extension* of its other
items: adding a defined function, a constant or a structural recursion
proves no new sentence that does not mention it (Shoenfield; CASL's
definitional extensions). `module.abstract`, which leaves defined items out
of the abstract ones, and `module.assume.abstract`, which needs no trust in
an `assume` about defined items alone, rely on it. It is argued from the
totality of [structural recursion](Recursion.md#meaning), and from an
unspecified value being a constant of the theory, one for each instance.

r[module.meta.coherence]
Instances are *coherent* and *canonical*: an implementation in scope is
canonical for dispatch, two in scope for the same interface and types are
an error, and every way of elaborating a use gives the same meaning
(Dreyer, Harper, Chakravarty and Keller, POPL 2007). Dispatch and
`module.use.morphism` rely on it. It is open, and comes with stage 3.

r[module.meta.views]
Views are coherent through their names: two paths of views and
inclusions from one module to another, as `Ord` and `Num` each reaching
`Eq`, translate each sentence alike. `module.view.choice` relies on it
where a use takes a view implicitly, and `module.extends` where an
interface is included twice. It is open.

r[module.meta.free]
A datatype declaration's free meaning is that of the solver's datatypes
and of a Lean `inductive`, which give its constructors' distinctness,
injectivity and exhaustiveness (CASL's free types; the initial algebra of
its constructors). `module.generic-type.sentences` relies on it, so that
no query states freeness. It is argued.

r[module.meta.parametricity]
`module.parametricity` is Reynolds's abstraction theorem for Fren's
generic items (Reynolds 1983; Wadler, "Theorems for free!", 1989).
`module.generic.check`, which checks a generic function once, at its type
parameters, for every instance, relies on it. A construct that inspected a
type parameter, such as a type case, would break it. It is open.

```fren
-- What a translated theorem rests on: nothing more, the axioms that the
-- implementation leaves trusted, or what is not yet established.
pub enum Translation { Holds, GivenTrusted, Unestablished }

-- The statuses of a module's axioms under an implementation, in order.
pub enum Statuses { Nil, Cons(MorphismStatus, Statuses) }

-- Whether each axiom that is an obligation, or relies on the rest, is
-- discharged, the first at position `k`.
pub fn discharged?(axioms: Statuses, done: Set<Int>, k: Int) := match axioms {
    Statuses::Nil => true,
    Statuses::Cons(s, rest) =>
        (s = MorphismStatus::Trusted or k in done) and discharged?(rest, done, k + 1),
}

pub fn any_trusted?(axioms: Statuses) := match axioms {
    Statuses::Nil => false,
    Statuses::Cons(s, rest) => s = MorphismStatus::Trusted or any_trusted?(rest),
}

set_option fren.evidence "random" in
pub proc translated_theorem(
    axioms: Statuses,            -- what the implementation makes of each axiom (`lang::morphism_status`)
    done: Set<Int>,              -- the positions of the obligations that hold
): (det translation: Translation) {
    out translation :=
        if not discharged?(axioms, done, 0) then Translation::Unestablished
        else if any_trusted?(axioms) then Translation::GivenTrusted else Translation::Holds

    expect total_and_discharged: when not any_trusted?(axioms) and discharged?(axioms, done, 0),
        translation = Translation::Holds
    expect obligation_open: when axioms is Statuses::Cons(MorphismStatus::Obligation, _) and not 0 in done,
        translation = Translation::Unestablished
}
```

## Induction by unfolding

A theorem about a recursive enumeration is often true by induction but not
by one step of each function's definition. Fren proves it by induction on
one of its variables, unfolding the definitions where each case decides
them, as Liquid Haskell's proof by logical evaluation (PLE) does (Vazou et
al., POPL 2018).

```text
lemma more_fuel(f: Fuel, e: Expr): when eval(f, e) is Some(v), eval(Fuel::More(f), e) = Some(v)
```

**Proof obligations**

r[module.induction]
A lemma or an `expect` with a quantified variable whose type is a
recursive enumeration, which its check does not prove and its
counterexample, if any, is not confirmed by evaluation, is checked by
induction on such a variable.

r[module.induction.variable]
The *candidates* are the quantified variables, of a recursive enumeration,
that are the argument at the decreasing parameter of some application of a
[structural recursion](Recursion.md) in the sentence
(`lang::induction_variables`). Fren tries each, in the order of the
variables, until one proves the sentence.

r[module.induction.cases]
Induction on `x` has one case for each variant of `x`'s type, in which `x`
is that variant with fresh variables for its payload. The *children* are
those of its payload's fresh variables whose type is `x`'s.

r[module.induction.hypotheses]
Each case has, as hypotheses, the sentence at each child, with each other
quantified variable at each ground term of its type that the case has.

r[module.induction.unfolding]
In each case, an application of a structural recursion unfolds into the arm
of its body that the case decides: the arm that the case's hypotheses
imply is taken, where they rule out every earlier arm
(`lang::arm_decided`). An application whose arm the case does not decide
stays opaque, with its contract.

r[module.induction.fixpoint]
Unfolding repeats at the applications that the unfolded arms bring, until
no application unfolds. Each application unfolds once.

r[module.induction.lemmas]
Each case uses the sentences that `module.use` gives, at the terms of
the case and of its unfoldings.

r[module.induction.verdict]
The induction passes where every case passes. A sentence whose check does
not pass is Inconclusive where no candidate's induction passes, and the
induction does not fail a check (`lang::induction_verdict`).

r[module.induction.evidence]
A pass by induction is a proof of a [structural recursion's
contract](Recursion.md#contracts) by Hoare induction, with the sentence as
the contract of a function generated from the cases. It adds nothing to
what the checks trust.

```fren
-- Whether each parameter's type is a recursive enumeration, in order.
pub enum ParamTypes { Nil, Cons(Bool, ParamTypes) }

-- The applications of structural recursions in a sentence: each by the
-- quantified variable that is its argument at the function's decreasing
-- parameter, by position, or -1 where that argument is not one.
pub enum Recursions { Nil, Cons(Int, Recursions) }

pub fn decreasing_variables(apps: Recursions): Set<Int> := match apps {
    Recursions::Nil => {},
    Recursions::Cons(v, rest) => (if v >= 0 then {v} else {}) union decreasing_variables(rest),
}

-- The candidates, the first variable at position `k`.
pub fn candidate_positions(types: ParamTypes, decreasing: Set<Int>, k: Int): Set<Int> :=
    match types {
        ParamTypes::Nil => {},
        ParamTypes::Cons(recursive?, rest) =>
            (if recursive? and k in decreasing then {k} else {}) union candidate_positions(rest, decreasing, k + 1),
    }

set_option fren.evidence "random" in
pub proc induction_variables(types: ParamTypes, apps: Recursions): (det candidates: Set<Int>) {
    out candidates := candidate_positions(types, decreasing_variables(apps), 0)

    expect decreasing_only: when apps = Recursions::Nil, candidates = {}
}

-- What a case's hypotheses say of an arm of a structural recursion's body:
-- that it is taken, that it is not, or neither.
pub enum ArmStatus { Taken, Excluded, Open }

-- The arms of the body, in order.
pub enum Arms { Nil, Cons(ArmStatus, Arms) }

pub fn decided?(arms: Arms) := match arms {
    Arms::Nil => false,
    Arms::Cons(status, rest) => match status {
        ArmStatus::Taken => true,
        ArmStatus::Excluded => decided?(rest),
        ArmStatus::Open => false,
    },
}

set_option fren.evidence "random" in
pub proc arm_decided(arms: Arms): (det unfolds?) {
    out unfolds? := decided?(arms)

    expect first_taken: when arms is Arms::Cons(ArmStatus::Taken, _), unfolds?
    expect open_first: when arms is Arms::Cons(ArmStatus::Open, _), not unfolds?
}

-- A check's verdict.
pub enum CheckVerdict { Pass, Fail, Inconclusive }

-- The verdicts of the inductions on the candidates, in the order tried.
pub enum Inductions { Nil, Cons(CheckVerdict, Inductions) }

pub fn some_pass?(attempts: Inductions) := match attempts {
    Inductions::Nil => false,
    Inductions::Cons(v, rest) => v = CheckVerdict::Pass or some_pass?(rest),
}

set_option fren.evidence "random" in
pub proc induction_verdict(direct: CheckVerdict, attempts: Inductions): (
    det verdict: CheckVerdict,
) {
    out verdict :=
        if direct != CheckVerdict::Inconclusive then direct
        else if some_pass?(attempts) then CheckVerdict::Pass else CheckVerdict::Inconclusive

    expect never_fails: when direct != CheckVerdict::Fail, verdict != CheckVerdict::Fail
    expect direct_kept: when direct = CheckVerdict::Pass, verdict = CheckVerdict::Pass
}
```

> **Note:** A child within a sequence, as of `Seq<Self>`, and mutually
> recursive types need recursive types beyond those that `F0387` allows
> (#602, #604). Then a case has the hypothesis `forall c, when c in cs,
> P(c)`, instantiated at the positions that the case mentions, and the
> unfolding of a mutual type goes on until the original type returns.

> **Rationale:** In the experiment of #669, of about 25 theorems of
> `examples/stlc.fren`, induction by unfolding proved 6, and the 3 laws of
> the lints, each in 5 to 309 ms, with 1 or 2 unfoldings in each case, and
> its unfolding ended on every function. With earlier lemmas as
> hypotheses, it proved about 11. cvc5's `--quant-ind` proved the same easy
> cases, and ran out of time on the rest. Hoare induction alone proved one.
> The instances are many, as each hypothesis is copied for each path of
> guards, so stage 1 removes the copies first.

## Strict expansion

**Dynamic semantics**

r[module.expansion]
A spec whose items and clauses are all of today's forms has the same
verdicts and messages as before this chapter, but for the exceptions
below (`lang::strict_expansion`). Today's forms are an `ensure` clause and
an `assume` clause of a function or procedure, an `expect` of a procedure,
a global expectation or a trait, a global expectation, and a trait's
`law`. A `require`, a lemma item, an `assume` item, an `expect` in a
function, and any member of a lemma's or an `assume` item's block are new.

r[module.expansion.laws]
Today's laws keep their meaning. They may come before the methods they
mention (`module.signature`). Every check of their trait uses them,
wherever each is written (`module.use.laws`). One that breaks the binding
rule is used as today (`module.rules.laws`). A query that their instances
do not decide is asked as today (`module.instance.models`), so the
warning of `traits::Pos::undecided`, that it could not decide whether its
assumptions hold with the laws, stays (`lang::strict_expansion`).

r[module.expansion.induction]
A check that was Inconclusive may pass by induction (`module.induction`) (`lang::strict_expansion`).

r[module.expansion.instances]
A check that was not decided may be decided by the instances of today's
laws, where their closure gives `unsat`: an expectation may pass, and
assumptions that contradict the laws may be an error (`F0602`) where today
they are a warning that the check is not decided (`F0608`) (`lang::strict_expansion`).

r[module.expansion.consistency]
Once the laws' consistency is checked (`module.axiom.check`), the warning
that a verdict rests on laws whose consistency is not checked (`F0665`)
gives way to that check's messages (`F0602`, `F0608`) (`lang::strict_expansion`).

r[module.expansion.corpus]
Each stage that lands compares the messages of Fren's own specs and of the
ui tests, before and after, and every difference is one that
`module.expansion` allows.

```fren
-- An item or clause of a spec, by its keyword and its place.
pub struct WrittenSentence { kind: SentenceKind, place: SentencePlace }

-- Whether an item or clause is of today's language.
pub fn today_form?(w: WrittenSentence) := match w.kind {
    SentenceKind::Ensure =>
        w.place in {
            SentencePlace::DefinedFunction,
            SentencePlace::UninterpretedFunction,
            SentencePlace::Procedure,
        },
    SentenceKind::Assume =>
        w.place in {
            SentencePlace::DefinedFunction,
            SentencePlace::UninterpretedFunction,
            SentencePlace::Procedure,
            SentencePlace::GlobalBlock,
        },
    SentenceKind::Expect =>
        w.place in {
            SentencePlace::Procedure,
            SentencePlace::GlobalBlock,
            SentencePlace::Module,
            SentencePlace::Interface,
        },
    SentenceKind::Law => w.place = SentencePlace::Interface,
    _ => false,
}

-- What a check reports: its verdict, and the codes of its messages.
pub struct Report { verdict: CheckVerdict, messages: Set<String> }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc strict_expansion(
    written: Seq<WrittenSentence>,       -- the spec's items and clauses that state claims
    before: Report,              -- what the check reports before this chapter
    after: Report,               -- and after it
    by_induction?,               -- the check passes by induction: an outcome of the check, given as such
    by_instances?,               -- the closure of today's laws' instances gives `unsat`: an outcome of the check, given as such
): (det new_forms?, det allowed?) {
    out new_forms? := exists (k: Int), 0 <= k < written.len and not today_form?(written[k])
    out allowed? := new_forms? or after = before
        or (before.verdict = CheckVerdict::Inconclusive and after.verdict = CheckVerdict::Pass and by_induction?)
        or (before.verdict = CheckVerdict::Inconclusive and by_instances? and (after.verdict = CheckVerdict::Pass
        or (after.verdict = CheckVerdict::Fail and "F0602" in after.messages
        and after.messages minus {"F0602"} = before.messages minus {"F0608"})))
        or (after.verdict = before.verdict and after.messages minus {"F0602", "F0608"} = before.messages minus {"F0665"})

    expect laws_are_today: when written = [
        WrittenSentence {
            kind := SentenceKind::Law,
            place := SentencePlace::Interface,
        },
    ],
        not new_forms?
    expect lemmas_are_new: when written = [
        WrittenSentence {
            kind := SentenceKind::Lemma,
            place := SentencePlace::Module,
        },
    ],
        new_forms?
    expect passes_stay: when not new_forms? and before.verdict = CheckVerdict::Pass and allowed?, after.verdict = CheckVerdict::Pass
    expect failures_stay: when not new_forms? and before.verdict = CheckVerdict::Fail and allowed?, after.verdict = CheckVerdict::Fail
    expect messages_kept: when not new_forms? and before.verdict != CheckVerdict::Inconclusive and allowed?
        and not "F0665" in before.messages and not "F0602" in after.messages and not "F0608" in after.messages,
        after.messages = before.messages
}
```

> **Rationale:** The prior art: ACL2's `encapsulate` and functional
> instantiation; Why3's theories and `clone`; the loose and initial
> semantics of CASL, Larch, OBJ and Maude; Isabelle's locales; Event-B's
> feasibility obligations; and TLA+'s `ASSUME` and `THEOREM` (#669).

The Lean-hosted front end checks this chapter's items by name, since no
`#fren_check` of its Lean file comes after it, and one without a path would
check every earlier chapter again:

```fren
#fren_check morphism_status
#fren_check morphism_obligations
#fren_check owed_laws
#fren_check view_choice
#fren_check sentence_place
#fren_check sentence_member
#fren_check sentence_role
#fren_check sentence_instantiation
#fren_check get_put_instantiation
#fren_check nested_anchor
#fren_check unbound_variable
#fren_check law_before_method
#fren_check listed_variable
#fren_check outside_variable
#fren_check sentence_use
#fren_check made_used
#fren_check made_unused
#fren_check axioms_anywhere
#fren_check unbound_law_quantified
#fren_check lemmas_ranked
#fren_check axiom_owner
#fren_check axiom_tier
#fren_check shared_axiom_owned
#fren_check shared_axiom_not_earlier
#fren_check defined_last_owned
#fren_check owner_through_definition
#fren_check tier_through_definition
#fren_check relative_tiers
#fren_check consistency
#fren_check translated_theorem
#fren_check induction_variables
#fren_check arm_decided
#fren_check induction_verdict
#fren_check strict_expansion
```
