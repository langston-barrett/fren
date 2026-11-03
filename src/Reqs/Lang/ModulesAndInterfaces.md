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
clauses that state claims, how a check uses them, and induction by
unfolding. Implementations, their obligations, the translation of
sentences along them, views and dispatch are specified apart, over one
model of what each check rests on (#669).

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
| `assume` | an item of a module | an axiom of the module's abstract items |
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
    Axiom,       -- Fren takes it as given, and checks its consistency
    Goal,        -- Fren proves it, and no other check uses it
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

## Instantiation

Fren uses a theorem or an axiom in a check by *instantiating* it: it puts
ground terms of the check's query for the sentence's quantified variables,
and adds each instance as a hypothesis. It chooses the instances itself,
from the applications and calls of the query, and no spec writes or sees
how a sentence is instantiated.

**Legality rules**

r[module.signature] lang::lemma_order::axioms_unordered, lang::law_before_method, lang::axioms_anywhere, lang::laws_anywhere
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

r[module.subject] lang::sentence_instantiation
A sentence's *subject* is the item, of those it applies or calls, that
comes last in that order.

r[module.anchor] lang::sentence_instantiation
An *anchor* of a sentence is an application of its subject, as a function,
that mentions no name that a quantifier within the sentence binds, and
that has an argument that is neither a quantified variable nor a closed
term. Where the sentence has no such application, each application of its
subject, as a function, that mentions no such name is an anchor.

r[module.matched] lang::sentence_instantiation
The *matched* applications of a sentence are its anchors and each of its
calls that mentions no name that a quantifier within the sentence binds.

r[module.binding] lang::sentence_instantiation
Each quantified variable of a sentence that occurs in an application of
it, and whose type is not [listed](Quantifiers.md#types), occurs in a
matched application. A variable that does not is an error that names it
(the *binding rule*).

r[module.binding.outside] lang::outside_variable
A quantified variable that the sentence mentions only outside its
applications, as `n` in `law bounded(s: Self, n: Int): when n > 0, h(s) >=
0`, needs no term: it stays quantified within each instance.

r[module.rules.kinds] lang::ensure_clause, lang::contract_without_result_used
The binding rule applies to a lemma item and an `assume` item. An `expect`
that does not meet it is checked, as every goal is. An `ensure` meets it.
Its sentence is what the clause states of its function at its parameters
(`module.ensure.sugar`), so it has that application among its
applications, whether or not the clause writes the result's name or the
application. Its clause mentions only items
declared before its function and the function itself
(`module.signature`), so its subject is its function, and that
application, whose arguments are its quantified variables, binds them
all. It is used at each application of its function, as a contract is
([Uninterpreted functions](Items.md#uninterpreted-functions)). An `ensure` clause of a procedure is
what it states of a call of the procedure at its inputs, which is its
matched application, and it is used at each call, as a call's constraint
is today ([Procedures](Procedures.md#meaning)).

r[module.rules.laws] lang::unbound_law_quantified
A `law` that meets the binding rule is instantiated as a lemma is. A `law`
that does not is not an error, and is used only as today, as a quantified
hypothesis of every check of its trait ([Traits](Traits.md#laws)).

r[module.rules.report] lang::sentence_instantiation
A sentence that breaks the binding rule reports its first unbound variable.

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
alike, once each name that a `let`, a `where` clause or an `out :=`
defines, and each constant, is replaced by its definition. An application
of a function is not replaced by the function's body.

r[module.instance.ground]
An application of the query that mentions a name that a quantifier of the
query binds is not a term at which a sentence is instantiated.

r[module.instance.listed] lang::listed_variable
A quantified variable of a listed type that no matched application binds
takes each value of its type, as a [quantifier over listed
types](Quantifiers.md#meaning) does.

r[module.instance.unused] lang::sentence_instantiation
A quantified variable that the sentence does not mention takes no term.

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
variables, which matching binds to proper subterms of the query's
applications, or to the arguments and outputs of its calls, which no
instance adds, to values of listed types, and to closed terms of the
sentence. It applies
every other item only where that item comes before the subject. So the
arguments of each item's applications are among finitely many terms, once
the applications of the items after it are finitely many. No bound on the
number of rounds is part of the language.

r[module.instance.models]
A model of a query whose hypotheses include instances of axioms is a
model of those instances, not always of the axioms. A check whose
sentences are all of today's forms (`module.expansion`), where the
instances do not give `unsat`, asks today's query, with today's laws
quantified ([Traits](Traits.md#expectations)) and its contracts as today,
and never takes a model of the instances as a counterexample or as a
witness of consistency. Any other check reports such a model as a counterexample,
or as a witness, only where Fren confirms that the model meets the axioms
themselves, and is Inconclusive where it does not.

r[module.use] lang::sentence_use
A check instantiates the sentences that are visible to it and meet the
binding rule, whose subject the closure applies: every
axiom of its module and of the modules it imports, wherever it is
declared, and each theorem declared before the check's item. An `ensure`
is used as a [contract](Items.md#contracts) is.

r[module.use.subject] lang::sentence_use, lang::no_subject_used
A sentence is used where its subject is applied by the query, or by an
instance of a used sentence. A sentence that applies and calls nothing,
such as an `assume` item about an abstract type alone, has no subject, and
every check that may use it does, as its one instance.

r[module.use.verdict]
A check uses a lemma whatever the lemma's own verdict. Where the check
passes, the pass rests on the lemma's check ([Evidence](../Evidence.md#resting-on-checks)).

r[module.use.laws] lang::laws_anywhere
The laws of a trait are visible to the checks of the trait's lemmas and
expectations, wherever each is written, as [Traits](Traits.md#expectations)
states.

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
    mentions: Set<Int>,         -- the quantified variables that occur in it, by position
    inner?,                     -- it mentions a name that a quantifier within the sentence binds
}

-- A sentence's applications and calls, in the order written.
pub enum Applications { Nil, Cons(SentenceApplication, Applications) }

-- A quantified variable of a sentence: whether its type is listed. A
-- variable that no application mentions needs no term, whether or not the
-- rest of the sentence mentions it (`module.binding.outside`,
-- `module.instance.unused`).
pub struct SentenceVariable { listed? }

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

r[module.instantiation.examples] lang::get_put_instantiation, lang::nested_anchor, lang::unbound_variable, lang::listed_variable, lang::outside_variable
The law `get_put` of [Traits](Traits.md) has one anchor,
`get(put(s, k, v), j)`, which binds all four variables. It is
instantiated at each application of `get` to an application of `put`. Of `f(x) = f(f(x))`, `f(f(x))` is the only
anchor. Of `f(g(x)) = f(g(g(x)))`, both
applications of `f` are anchors, matched at once, so an instance arises
only where both are terms of the query, and adds no application of `f`.
Of `f(a, b) = f(b, a)`, both applications are anchors, so it relates
`f(c, d)` and `f(d, c)` only where both are terms of the query.
`f(x) <= g(x, y)`, where `g` comes before `f`, leaves `y` unbound. A law whose variable is a `Bool` that no
application has, such as `law flagged(s: Self, b?): when b?, obs(s) >= 0`,
takes both values of it, and `law bounded(s:
Self, n: Int): when n > 0, h(s) >= 0` keeps `n` quantified.

```fren
-- An application, outside every quantifier, of `item` to `args`, which mention `mentions`.
pub fn app(item: Int, args: Seq<SentenceArg>, mentions: Set<Int>): SentenceApplication :=
    SentenceApplication {
        item,
        call? := false,
        args,
        mentions,
        inner? := false,
    }

pub fn quantified(listed?): SentenceVariable := SentenceVariable { listed? }

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
        [SentenceArg::Compound, SentenceArg::Variable],
        {0, 1, 2, 3}
    ),
    Applications::Cons(
        app(
            1,
            [
                SentenceArg::Variable,
                SentenceArg::Variable,
                SentenceArg::Variable,
            ],
            {0, 1, 2}
        ),
        Applications::Cons(
            app(2, [SentenceArg::Variable, SentenceArg::Variable], {0, 3}),
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
    app(1, [SentenceArg::Variable], {0}),
    Applications::Cons(
        app(1, [SentenceArg::Compound], {0}),
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil)
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
            app(2, [SentenceArg::Variable], {0}),
            Applications::Cons(
                app(1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
                Applications::Nil
            )
        ),
    )
    expect y_unbound: r.verdict = SentenceInstantiation::Unbound(1)
}

-- `law flagged(s: Self, b?): when b?, obs(s) >= 0`, with `obs` at 1.
set_option fren.evidence "random" in
expect listed_variable() {
    call r := sentence_instantiation(
        SentenceVariables::Cons(
            quantified(false),
            SentenceVariables::Cons(quantified(true), SentenceVariables::Nil)
        ),
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- `law bounded(s: Self, n: Int): when n > 0, h(s) >= 0`, with `h` at 1:
-- `n` is in no application.
set_option fren.evidence "random" in
expect outside_variable() {
    call r := sentence_instantiation(
        TWO_VARIABLES,
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}
```

`lang::lemma_order` states which applications a lemma may have:

```fren
-- The first application of `apps` of an item that is not declared before
-- `position`, the first at position `k`, and -1 where there is none.
pub fn first_later(apps: Applications, position: Int, k: Int): Int := match apps {
    Applications::Nil => -1,
    Applications::Cons(a, rest) =>
        if a.item >= position then k else first_later(rest, position, k + 1),
}

set_option fren.evidence "random" in
pub proc lemma_order(
    keyword: SentenceKind,
    position: Int,               -- the sentence's position in the order of items
    applications: Applications,
): (det reported: Int) {
    out reported :=
        if keyword = SentenceKind::Lemma then first_later(applications, position, 0) else -1

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
        Applications::Cons(app(3, [SentenceArg::Variable], {0}), Applications::Nil),
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
        Applications::Cons(app(2, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect reported: r.reported = -1
}
```

```fren
-- `[Variable, ...]`, one for each of `vars`. Concatenating sequences is
-- outside the decidable core.
set_option fren.lint.undecidable "allow" in
pub fn variable_args(vars: SentenceVariables): Seq<SentenceArg> := match vars {
    SentenceVariables::Nil => [],
    SentenceVariables::Cons(_, rest) => [SentenceArg::Variable] ++ variable_args(rest),
}

-- The positions of `vars`, the first at position `k`.
pub fn variable_positions(vars: SentenceVariables, k: Int): Set<Int> := match vars {
    SentenceVariables::Nil => {},
    SentenceVariables::Cons(_, rest) => {k} union variable_positions(rest, k + 1),
}

-- The applications of the sentence of an `ensure` clause of the function
-- at `function`, with the parameters `variables`, that writes `written`:
-- the function at its parameters, then what the clause writes.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc ensure_clause(function: Int, variables: SentenceVariables, written: Applications): (
    det applications: Applications,
) {
    out applications := Applications::Cons(
        SentenceApplication {
            item := function,
            call? := false,
            args := variable_args(variables),
            mentions := variable_positions(variables, 0),
            inner? := false,
        },
        written
    )

    -- A clause applies only items declared before its function, and the
    -- function itself only at its parameters (`module.signature`,
    -- `lang::contract_application`).
    assume earlier_items: last_item(written) <= function
    assume own_at_parameters: not has_compound?(written, function)

    expect subject_is_function: last_item(applications) = function
    expect instantiable: instantiation_verdict(variables, applications) = SentenceInstantiation::Instantiable
}

-- `fn g(x: Int, y: Int): Int { ensure e: k(x) <= h(x, y) }`, with `h` at
-- 1, `k` at 2 and `g` at 3, all uninterpreted: the clause writes neither
-- the result nor `g(x, y)`.
pub const NO_RESULT_WRITTEN: Applications := Applications::Cons(
    app(2, [SentenceArg::Variable], {0}),
    Applications::Cons(
        app(1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
        Applications::Nil
    )
)

-- Its sentence has `g(x, y)`, its subject is `g`, and it meets the binding rule.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect contract_without_result() {
    call clause := ensure_clause(3, TWO_VARIABLES, NO_RESULT_WRITTEN)
    call r := sentence_instantiation(TWO_VARIABLES, clause.applications)
    expect subject: r.subject = 3
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

-- Whether a sentence of the keyword `k` is an axiom (`module.role.axiom`):
-- an `assume` item, a law, or an `ensure` clause, which stands for one of
-- an abstract item here.
pub fn axiom_kind?(k: SentenceKind) :=
    k in {
        SentenceKind::Assume,
        SentenceKind::Law,
        SentenceKind::Ensure,
    }

-- Whether `p` is an axiom: an `assume` item, a law, or an `ensure` clause of an abstract item.
pub fn axiom?(p: Sentence) := axiom_kind?(p.kind)

-- Whether `p` may be used by a check of the item at `check`, where its
-- subject is applied: an axiom, wherever it is declared, or a lemma
-- declared before the item, that meets the binding rule.
pub fn fact?(p: Sentence, check: Int) :=
    (axiom?(p) or (p.kind = SentenceKind::Lemma and p.position < check))
    and instantiation_verdict(p.variables, p.applications) = SentenceInstantiation::Instantiable

-- Whether `p` is used where the query and the instances apply `items`.
pub fn used?(p: Sentence, check: Int, items: Set<Int>) :=
    fact?(p, check) and (last_item(p.applications) in items or p.applications = Applications::Nil)

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
            app(2, [SentenceArg::Compound, SentenceArg::Variable], {0, 1}),
            Applications::Cons(
                app(1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
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

-- An axiom is used by the check of an item declared before it: an
-- `assume` item, and a law, as by an expectation written before it.
set_option fren.evidence "random" in
expect axioms_anywhere() {
    call assumed := sentence_use(2, made(SentenceKind::Assume), {2})
    expect used_before: assumed.used = {3}
}

set_option fren.evidence "random" in
expect laws_anywhere() {
    call law_used := sentence_use(2, made(SentenceKind::Law), {2})
    expect used_before: law_used.used = {3}
}

-- `law l(s: Self, t: Self): f(s) <= g(s, t)`, with `g` at 1, `f` at 2
-- and the law at 3, breaks the binding rule, so every check of its trait
-- uses it quantified, whatever its query applies.
pub const UNBOUND_LAW: Sentence := Sentence {
    kind := SentenceKind::Law,
    position := 3,
    variables := TWO_VARIABLES,
    applications := Applications::Cons(
        app(2, [SentenceArg::Variable], {0}),
        Applications::Cons(
            app(1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
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

-- `assume one(x: T, y: T): x = y`, about the abstract type `T` at 1 alone,
-- at 2: every later check uses it.
set_option fren.evidence "random" in
expect no_subject_used() {
    call r := sentence_use(
        3,
        Sentences::Cons(
            Sentence {
                kind := SentenceKind::Assume,
                position := 2,
                variables := TWO_VARIABLES,
                applications := Applications::Nil,
            },
            Sentences::Nil
        ),
        {},
    )
    expect used: r.used = {2}
}

set_option fren.evidence "random" in
expect lemmas_ranked() {
    call lemma := sentence_use(2, made(SentenceKind::Lemma), {2})
    expect not_before: lemma.used = {}
}
```

```fren
-- The clause `e` of the uninterpreted `g` is used by a later check that
-- applies `g`, as a contract is today, whatever else the query applies.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect contract_without_result_used() {
    call clause := ensure_clause(3, TWO_VARIABLES, NO_RESULT_WRITTEN)
    call r := sentence_use(
        4,
        Sentences::Cons(
            Sentence {
                kind := SentenceKind::Ensure,
                position := 3,
                variables := TWO_VARIABLES,
                applications := clause.applications,
            },
            Sentences::Nil
        ),
        {3},
    )
    expect used: r.used = {3}
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
> instances does. Lemmas keep the order of declarations because a theorem
> that mentioned a later item could rest on it: with
> `lemma l(n: N): h(n) >= 1` before a structural recursion `h` whose
> contract claims `h(n) >= 1`, the check of `l` would use `h`'s contract,
> and the check of `h`'s contract would use `l`, so each would pass from
> the other, whatever `h` is. Axioms and goals rest on no proof, so they may come anywhere. Fren
> chooses the instances that F\*'s `SMTPat` and Dafny's triggers have the
> author choose.

## Checks

**Proof obligations**

r[module.theorem.check]
A lemma has the checks of a [global
expectation](../Check.md#global-expectations) with its parameters, its
domain, its calls and its claims, each using the sentences that
`module.use` gives. A theorem that these checks do not prove is checked by
induction, where `module.induction` applies.

r[module.axiom.check]
An axiom is never proved. Until the realizability of axioms that relate
several items is specified (#669, stage 5), Fren checks of a module's
axioms only what it checks today: the realizability of each uninterpreted
function's `ensure` clauses ([Realizability](../Check.md#contracts-of-uninterpreted-functions),
`F0631`, `F0632`).

r[module.axiom.unchecked]
The consistency of an `assume` item, and of a trait's laws, is not checked
yet. A verdict that rests on one says so, as one that rests on a trait's
laws does today (`F0665`).

r[module.consistency.vacuity]
Where the axioms cannot hold together, every check that uses them holds
vacuously.

r[module.assume.trusted]
An axiom is reported as trusted: a pass that rests on it says that it
does, as one that rests on a trait's laws does (`F0665`).

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
recursive enumeration is checked by induction on such a variable at each
check of a claim of it, `ensure` or `expect`, that is Inconclusive. Its
other checks, such as its vacuity and its `cover` members, which ask
whether something can hold, never are. A check whose counterexample evaluation does
not confirm is Inconclusive ([Recursion](Recursion.md#counterexamples-and-completeness)),
so a check that fails has a confirmed counterexample.

r[module.induction.variable] lang::induction_variables
The *candidates* are the quantified variables, of a recursive enumeration,
that are the argument at the decreasing parameter of some application of a
[structural recursion](Recursion.md) in the sentence. Fren tries each, in the order of the
variables, until one proves the sentence.

r[module.induction.cases]
Induction on `x` has one case for each variant of `x`'s type, in which `x`
is that variant with fresh variables for its payload. The *children* are
those of its payload's fresh variables whose type is `x`'s.

r[module.induction.hypotheses]
Each case has, as hypotheses, the sentence at each child, with each other
quantified variable at each ground term of its type that the case has.

r[module.induction.unfolding] lang::arm_decided
In each case, an application of a structural recursion unfolds into the arm
of its body that the case decides: the arm that the case's hypotheses
imply is taken, where they rule out every earlier arm. An application whose arm the case does not decide
stays opaque, with its contract.

r[module.induction.fixpoint]
Unfolding repeats at the applications that the unfolded arms bring, until
no application unfolds. Each application unfolds once.

r[module.induction.lemmas]
Each case uses the sentences that `module.use` gives, at the terms of
the case and of its unfoldings.

r[module.induction.verdict] lang::induction_verdict
The induction passes where every case passes. A sentence whose check is
Inconclusive stays Inconclusive where no candidate's induction passes. The
induction never fails a check, and never changes a pass or a failure.

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

r[module.expansion] lang::strict_expansion
A spec that Fren accepts today, whose items and clauses are all of
today's forms, has the same
verdicts and messages as before this chapter, but for the exceptions
below. Today's forms are an `ensure` clause and
an `assume` clause of a function or procedure, an `expect` of a procedure,
a global expectation or a trait, a global expectation, and a trait's
`law`. A `require`, a lemma item, an `assume` item, an `expect` in a
function, and any member of a lemma's or an `assume` item's block are new.

r[module.expansion.laws] lang::strict_expansion
Today's laws keep their meaning. They may come before the methods they
mention (`module.signature`). Every check of their trait uses them,
wherever each is written (`module.use.laws`). One that breaks the binding
rule is used as today (`module.rules.laws`). A query to which their
instances do not give `unsat` is asked as today, whatever model the
instances have (`module.instance.models`), so the warning of
`traits::Pos::undecided` in the ui test `test/ui/lang/traits.fren`, that
it could not decide whether its assumptions hold with the laws, stays.

r[module.expansion.induction] lang::strict_expansion
A check that was Inconclusive may pass by induction (`module.induction`).

r[module.expansion.instances] lang::strict_expansion
A check that was not decided may be decided by the instances of today's
laws, where their closure gives `unsat`: an expectation may pass, and
assumptions that contradict the laws may be an error (`F0602`) where today
they are a warning that the check is not decided (`F0608`).

r[module.expansion.consistency] lang::strict_expansion
Once stage 5 checks the laws' consistency (`module.axiom.unchecked`), the warning
that a verdict rests on laws whose consistency is not checked (`F0665`)
gives way to that check's messages (`F0602`, `F0608`).
A check that passes today keeps its verdict, and where stage 5 finds the
laws inconsistent, it reports that at the laws, as stage 5 states, not at
the check.

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
    attempts: Inductions,        -- the verdicts of the inductions on the candidates (`lang::induction_verdict`)
    by_instances?,               -- the closure of today's laws' instances gives `unsat`: an outcome of the check, given as such
    consistency_checked?,        -- stage 5 checks the laws' consistency (`module.expansion.consistency`)
): (det new_forms?, det allowed?) {
    out new_forms? := exists (k: Int), 0 <= k < written.len and not today_form?(written[k])
    out allowed? := new_forms? or after = before
        or (before.verdict = CheckVerdict::Inconclusive and after.verdict = CheckVerdict::Pass and some_pass?(attempts)
        and after.messages subset before.messages)
        or (before.verdict = CheckVerdict::Inconclusive and by_instances?
        and (after.verdict = CheckVerdict::Pass and after.messages subset before.messages
        or (after.verdict = CheckVerdict::Fail and "F0602" in after.messages
        and after.messages minus {"F0602"} = before.messages minus {"F0608"})))
        -- Stage 5's exception (`module.expansion.consistency`).
        or (consistency_checked? and after.verdict = before.verdict and "F0665" in before.messages
        and after.messages minus {"F0602", "F0608"} = before.messages minus {"F0665"}
        and (not "F0602" in after.messages or after.verdict = CheckVerdict::Fail))

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

-- A check of today's forms whose verdict stays, and which gains `F0608`
-- without having had `F0665`, breaks strict expansion.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect consistency_messages_need_f0665() {
    call r := strict_expansion(
        [],
        Report {
            verdict := CheckVerdict::Pass,
            messages := {},
        },
        Report {
            verdict := CheckVerdict::Pass,
            messages := {"F0608"},
        },
        Inductions::Nil,
        false,
        true,
    )
    expect not_allowed: not r.allowed?
}

-- Each exception allows what its rule allows. Where stage 5 finds the
-- laws consistent, `F0665` goes, and nothing takes its place.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect consistent_laws_drop_f0665() {
    call r := strict_expansion(
        [],
        Report {
            verdict := CheckVerdict::Pass,
            messages := {"F0665"},
        },
        Report {
            verdict := CheckVerdict::Pass,
            messages := {},
        },
        Inductions::Nil,
        false,
        true,
    )
    expect allowed: r.allowed?
}

-- An Inconclusive check that passes by induction loses its warning.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect induction_pass_allowed() {
    call r := strict_expansion(
        [],
        Report {
            verdict := CheckVerdict::Inconclusive,
            messages := {"F0450"},
        },
        Report {
            verdict := CheckVerdict::Pass,
            messages := {},
        },
        Inductions::Cons(CheckVerdict::Pass, Inductions::Nil),
        false,
        false,
    )
    expect allowed: r.allowed?
}

-- Assumptions that today's laws' instances contradict are an error where
-- today they are not decided.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect instances_contradiction_allowed() {
    call r := strict_expansion(
        [],
        Report {
            verdict := CheckVerdict::Inconclusive,
            messages := {"F0608"},
        },
        Report {
            verdict := CheckVerdict::Fail,
            messages := {"F0602"},
        },
        Inductions::Nil,
        true,
        false,
    )
    expect allowed: r.allowed?
}

-- A spec whose one claim is an `ensure` clause of an uninterpreted function
-- that writes neither its result nor its function, as `e` of `g` in
-- `lang::contract_without_result`, is of today's forms, so a check that
-- passes today because of it must not become Inconclusive.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect contract_without_result_kept() {
    call r := strict_expansion(
        [
            WrittenSentence {
                kind := SentenceKind::Ensure,
                place := SentencePlace::UninterpretedFunction,
            },
        ],
        Report {
            verdict := CheckVerdict::Pass,
            messages := {},
        },
        Report {
            verdict := CheckVerdict::Inconclusive,
            messages := {"F0450"},
        },
        Inductions::Nil,
        false,
        false,
    )
    expect today: not r.new_forms?
    expect not_allowed: not r.allowed?
}

-- Before stage 5 checks the laws' consistency, `F0608` does not take the
-- place of `F0665` either.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect consistency_messages_need_stage_5() {
    call r := strict_expansion(
        [],
        Report {
            verdict := CheckVerdict::Pass,
            messages := {"F0665"},
        },
        Report {
            verdict := CheckVerdict::Pass,
            messages := {"F0608"},
        },
        Inductions::Nil,
        false,
        false,
    )
    expect not_allowed: not r.allowed?
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
#fren_check sentence_place
#fren_check sentence_member
#fren_check sentence_role
#fren_check assume_through_definition
#fren_check sentence_instantiation
#fren_check get_put_instantiation
#fren_check nested_anchor
#fren_check unbound_variable
#fren_check law_before_method
#fren_check listed_variable
#fren_check outside_variable
#fren_check lemma_order
#fren_check lemma_before_function
#fren_check sentence_use
#fren_check made_used
#fren_check made_unused
#fren_check axioms_anywhere
#fren_check laws_anywhere
#fren_check unbound_law_quantified
#fren_check contract_without_result_used
#fren_check ensure_clause
#fren_check contract_without_result
#fren_check no_subject_used
#fren_check lemmas_ranked
#fren_check induction_variables
#fren_check arm_decided
#fren_check induction_verdict
#fren_check strict_expansion
#fren_check contract_without_result_kept
#fren_check consistency_messages_need_f0665
#fren_check consistency_messages_need_stage_5
#fren_check consistent_laws_drop_f0665
#fren_check induction_pass_allowed
#fren_check instances_contradiction_allowed
```
