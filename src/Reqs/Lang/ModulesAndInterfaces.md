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
An `expect` item is a [global expectation](Global.md) in either of its
forms. An `expect` member is a member of a procedure, a function, a global
expectation or a lemma. A `law` item is a member of a
[trait](Traits.md#laws).

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
A theorem of a module, once checked, holds of every implementation of it,
translated, without another check (*functional instantiation*).

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
    out status := if mentioned subset mapped then MorphismStatus::Obligation
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
or a global expectation, `assume` is accepted where `require` is.

r[module.place.error]
One where its keyword is not accepted is an error. In the block of a global
expectation, it is the error of a member that the block does not accept
(`F0417`). In a trait, it is the error of a member of another kind
(`F0222`).

r[module.place.expect]
An `expect` in a function's block is accepted, and is a claim about the
function's value at its parameters, as a procedure's expectation is about
its outputs.

r[module.assume.block]
`assume n: e` inside a function, a procedure or a global expectation means
`require n: e`.

r[module.block]
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
        SentenceKind::Require => place in {
            DefinedFunction,
            UninterpretedFunction,
            Procedure,
            GlobalBlock,
            LemmaBlock,
            AssumeBlock,
        },
        SentenceKind::Ensure => place in {
            DefinedFunction,
            UninterpretedFunction,
            Procedure,
            LemmaBlock,
            AssumeBlock,
        },
        SentenceKind::Expect => place != AssumeBlock,
        SentenceKind::Lemma => place in {Module, Interface},
        SentenceKind::Assume => place in {
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
    det?,                      -- written with `det`
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
An `assume` item that mentions no abstract item is an error
(`lang::sentence_role`).

**Dynamic semantics**

r[module.role]
Each sentence has the *role* that `lang::sentence_role` gives it, from its
keyword, its place, and the items it mentions.

r[module.role.domain]
A `require` clause is a *domain*: it restricts the values of its item's
parameters at which the item's other sentences are claimed.

r[module.role.theorem]
A *theorem* is a lemma item, or an `ensure` clause of a defined function
or of a lemma.
It holds in every interpretation that meets the axioms that it may rest on
(`module.use`).

r[module.role.axiom]
An *axiom* is an `assume` item, a `law` item, or an `ensure` clause of an
uninterpreted function, of a procedure, or of an `assume` item. The
spec's interpretations are those that meet every axiom.

r[module.role.goal]
An `expect` item or member is a *goal*. It holds as a theorem does, and no other check
uses it.

r[module.ensure.sugar]
An `ensure` clause of a function `f` with the parameters `x` is the sentence that
`f`'s contract states of `f(x)`: a lemma about `f(x)` where `f` is defined, and an
`assume` item about it where `f` is uninterpreted.

r[module.meaning]
A sentence with the quantified variables `x`, the domain `R(x)`, the calls
`y` and the claims `E(x, y)` means `∀ x y. R(x) ∧ I(x, y) ⇒ E(x, y)`, where
`I(x, y)` says that each `y` is a behaviour of its call, as a [global
expectation](Global.md#meaning) means. Its quantified variables are its
parameters, or its item's.

r[module.meaning.procedures]
A call in a sentence ranges over the behaviours of its procedure at its
arguments. An `assume` item with calls constrains the procedures it
calls, as an environment that is never implemented does.

r[module.trait.lemma]
A lemma of an interface holds in every interpretation that meets the
interface, and of every implementation of it, by
`module.implementation.theorems`.

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
    mentioned: Set<Int>,     -- the items that the sentence mentions
    abstract: Set<Int>,      -- the abstract items of the spec
): (det role: SentenceRole, det accepted?) {
    use self::SentencePlace::{AssumeBlock, DefinedFunction, LemmaBlock, Module}
    use self::SentenceRole::{Axiom, Domain, Goal, Theorem}

    out role := match keyword {
        SentenceKind::Require => Domain,
        SentenceKind::Expect => Goal,
        SentenceKind::Lemma => Theorem,
        SentenceKind::Law => Axiom,
        SentenceKind::Ensure => if place in {DefinedFunction, LemmaBlock} then Theorem else Axiom,
        SentenceKind::Assume => if place in {Module, AssumeBlock} then Axiom else Domain,
    }
    out accepted? := not (keyword = SentenceKind::Assume and place = Module and mentioned inter abstract = {})

    expect axioms_mention_abstract_items: when keyword = SentenceKind::Assume and place = Module and accepted?,
        mentioned inter abstract != {}
    expect within_items: when keyword = SentenceKind::Assume and not place is Module | AssumeBlock, role = Domain
    expect uninterpreted_contracts: when keyword = SentenceKind::Ensure and place = SentencePlace::UninterpretedFunction,
        role = Axiom
}
```

> **Rationale:** An `assume` about defined items alone could contradict
> their definitions, and needs no trust: it is a lemma.

## Instantiation

Fren uses a theorem or an axiom in a check by *instantiating* it: it puts
ground terms of the check's query for the sentence's quantified variables,
and adds each instance as a hypothesis. It chooses the instances itself,
from the applications and calls of the query, so that every query stays
free of quantifiers, and no spec writes or sees how a sentence is
instantiated.

**Legality rules**

r[module.subject]
A sentence's *subject* is the item, of those it applies or calls, that is
declared last.

r[module.order]
A sentence applies and calls only items declared before it. Another
application is an error that names it (the *order rule*).

r[module.anchor]
An *anchor* of a sentence is an application of its subject, as a function,
that mentions no name that a quantifier within the sentence binds, and
that has an argument that is neither a quantified variable nor a closed
term. Where the sentence has no such application, each application of its
subject, as a function, that mentions no such name is an anchor.

r[module.matched]
The *matched* applications of a sentence are its anchors and each of its
calls that mentions no name that a quantifier within the sentence binds.

r[module.binding]
Each quantified variable that a sentence mentions, and whose type is not
[listed](Quantifiers.md#types), occurs in a matched application. A variable
that does not is an error that names it (the *binding rule*).

r[module.rules.kinds]
The order rule and the binding rule apply to a lemma, an `assume` item
and a law. An `expect` that does not meet them is checked, as every goal
is. An `ensure` meets them, since a contract applies its function only to
its parameters ([Contracts](Items.md#contracts)).

r[module.rules.report]
A sentence that breaks both rules reports its first application that
breaks the order rule, and no variable. One that breaks only the binding
rule reports its first unbound variable (`lang::sentence_instantiation`).

**Dynamic semantics**

r[module.instance]
An *instance* of a sentence is the sentence with a ground term in place of
each of its quantified variables. It holds wherever the sentence does.

r[module.instance.matching]
Fren takes the instances at which each matched application of the sentence
is a term of the query: each anchor an application of the query, and each
call a call of the query, with the same arguments once the instance's terms
are put in. Two terms are the same where they are written alike, once each
name with a definition is replaced by it.

r[module.instance.ground]
An application of the query that mentions a name that a quantifier of the
query binds is not a term at which a sentence is instantiated.

r[module.instance.listed]
A quantified variable of a listed type that no matched application binds
takes each value of its type, as a [quantifier over listed
types](Quantifiers.md#meaning) does.

r[module.instance.unused]
A quantified variable that the sentence does not mention takes no term.

r[module.instance.hypothesis]
Each instance adds its claims, under its domain, as one hypothesis of the
query. The applications and calls that the instance has are terms of the
query too.

r[module.closure]
Fren instantiates each sentence that the check uses at the terms of the
query and of the instances, until no new instance arises. The *closure* is
the set of all those instances.

r[module.closure.finite]
The closure of every query is finite. No bound on the number of rounds is
part of the language.

r[module.use]
A check uses the lemmas, `assume` items and laws that are visible to it,
declared before its item, and meet the two rules, whose subject the
closure applies (`lang::sentence_use`). An `ensure` is used as a
[contract](Items.md#contracts) is.

r[module.use.subject]
A sentence is used where its subject is applied by the query, or by an
instance of a used sentence whose subject is declared after it.

r[module.use.verdict]
A check uses a lemma whatever the lemma's own verdict. Where the check
passes, the pass rests on the lemma's check ([Evidence](../Evidence.md#resting-on-checks)).

r[module.use.laws]
The laws of a trait are visible to the checks of the trait's lemmas and
expectations, as [Traits](Traits.md#expectations) states.

r[module.use.morphism]
The sentences visible to a check are those of its module, of the modules
that it imports, and their theorems and axioms translated along the
implementations that the check's terms use: an interface's at each of its
implementations, and a generic function's at each of its instances.
Each is used as `module.use` states, at its translation's subject.

r[module.no-patterns]
No sentence states how it is instantiated, and no setting changes it.

```fren
-- An argument of an application in a sentence, as written: one of the
-- sentence's quantified variables, a closed term, which mentions none of
-- them, or another term.
pub enum SentenceArg { Variable, Closed, Compound }

-- An application of a function, or a call of a procedure, in a sentence.
pub struct SentenceApplication {
    item: Int,                  -- the item applied or called, by its position in declaration order
    call?,                      -- it is a call
    args: Seq<SentenceArg>,     -- its arguments
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

-- Whether a sentence meets the two rules; or the first application that
-- breaks the order rule, or the first variable that breaks the binding
-- rule, each by position.
pub enum SentenceInstantiation { Instantiable, Unordered(Int), Unbound(Int) }

-- The item, of those that `apps` applies or calls, declared last, and -1 where there is none.
pub fn last_item(apps: Applications): Int := match apps {
    Applications::Nil => -1,
    Applications::Cons(a, rest) => a.item.max(last_item(rest)),
}

-- Whether `a` applies the function `s`, outside every quantifier of the sentence.
pub fn outer_application?(a: SentenceApplication, s: Int) := a.item = s and not a.call? and not a.inner?

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

pub fn matched?(a: SentenceApplication, s: Int, compound?) := anchor?(a, s, compound?) or (a.call? and not a.inner?)

-- The positions of the anchors of `apps`, the first at position `k`.
pub fn anchor_positions(apps: Applications, s: Int, compound?, k: Int): Set<Int> := match apps {
    Applications::Nil => {},
    Applications::Cons(a, rest) => (if anchor?(a, s, compound?) then {k} else {}) union anchor_positions(rest, s, compound?, k + 1),
}

-- Whether a matched application of `apps` mentions the variable `v`.
pub fn bound?(apps: Applications, v: Int, s: Int, compound?) := match apps {
    Applications::Nil => false,
    Applications::Cons(a, rest) => (matched?(a, s, compound?) and v in a.mentions) or bound?(rest, v, s, compound?),
}

-- The first application of an item that is not declared before `position`,
-- the first at position `k`, and -1 where there is none.
pub fn first_unordered(apps: Applications, position: Int, k: Int): Int := match apps {
    Applications::Nil => -1,
    Applications::Cons(a, rest) => if a.item >= position then k else first_unordered(rest, position, k + 1),
}

-- The first variable that the binding rule needs bound and is not, the
-- first at position `v`, and -1 where there is none.
pub fn first_unbound(vars: SentenceVariables, apps: Applications, v: Int, s: Int, compound?): Int := match vars {
    SentenceVariables::Nil => -1,
    SentenceVariables::Cons(x, rest) => if x.mentioned? and not x.listed? and not bound?(apps, v, s, compound?)
        then v else first_unbound(rest, apps, v + 1, s, compound?),
}

-- Whether the sentence at `position`, with these variables and applications, meets the two rules.
pub fn instantiation_verdict(
    position: Int,
    vars: SentenceVariables,
    apps: Applications
): SentenceInstantiation :=
    if first_unordered(apps, position, 0) != -1 then SentenceInstantiation::Unordered(first_unordered(apps, position, 0))
    else if first_unbound(
        vars,
        apps,
        0,
        last_item(apps),
        has_compound?(apps, last_item(apps))
    ) != -1
    then SentenceInstantiation::Unbound(
        first_unbound(
            vars,
            apps,
            0,
            last_item(apps),
            has_compound?(apps, last_item(apps))
        )
    )
    else SentenceInstantiation::Instantiable

set_option fren.evidence "random" in
pub proc sentence_instantiation(
    position: Int,                   -- the sentence's position in declaration order
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
    out verdict := instantiation_verdict(position, variables, applications)

    expect order_first: when first_unordered(applications, position, 0) != -1,
        verdict = SentenceInstantiation::Unordered(first_unordered(applications, position, 0))
    expect no_variables: when variables = SentenceVariables::Nil and first_unordered(applications, position, 0) = -1,
        verdict = SentenceInstantiation::Instantiable
}
```

r[module.instantiation.examples]
The law `get_put` of [Traits](Traits.md) has one anchor,
`get(put(s, k, v), j)`, which binds all four variables. It is
instantiated at each application of `get` to an application of `put`
(`lang::get_put_instantiation`). Of `f(x) = f(f(x))`, `f(f(x))` is the only
anchor (`lang::nested_anchor`). `f(x) <= g(x, y)`, where `g` is declared
before `f`, leaves `y` unbound (`lang::unbound_variable`). A law whose
variable is a `Bool` that no application has, such as `law flagged(s:
Self, b?): when b?, obs(s) >= 0`, takes both values of it
(`lang::listed_variable`).

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

pub fn quantified(listed?): SentenceVariable := SentenceVariable {
    mentioned? := true,
    listed?,
}

-- `law get_put(s: Self, k: Key, v: Int, j: Key): get(put(s, k, v), j) = (if j = k then Option::Some(v) else get(s, j))`,
-- with `put` declared at 1, `get` at 2, and the law at 3.
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
    call r := sentence_instantiation(3, GET_PUT_VARIABLES, GET_PUT_APPLICATIONS)
    expect subject: r.subject = 2
    expect one_anchor: r.anchors = {0}
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- One variable, which the sentence mentions and whose type is not listed.
pub const ONE_VARIABLE: SentenceVariables := SentenceVariables::Cons(
    quantified(false),
    SentenceVariables::Nil
)

-- `f(x) = f(f(x))`, with `f` declared at 1 and the sentence at 2: the
-- applications `f(x)`, `f(f(x))` and the inner `f(x)`.
pub const NESTED_APPLICATIONS: Applications := Applications::Cons(
    app(1, [SentenceArg::Variable], {0}),
    Applications::Cons(
        app(1, [SentenceArg::Compound], {0}),
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil)
    )
)

set_option fren.evidence "random" in
expect nested_anchor() {
    call r := sentence_instantiation(2, ONE_VARIABLE, NESTED_APPLICATIONS)
    expect outer_only: r.anchors = {1}
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}

-- `f(x) <= g(x, y)`, with `g` declared at 1 and `f` at 2.
pub const TWO_VARIABLES: SentenceVariables := SentenceVariables::Cons(
    quantified(false),
    SentenceVariables::Cons(quantified(false), SentenceVariables::Nil)
)

pub const UNBOUND_APPLICATIONS: Applications := Applications::Cons(
    app(2, [SentenceArg::Variable], {0}),
    Applications::Cons(
        app(1, [SentenceArg::Variable, SentenceArg::Variable], {0, 1}),
        Applications::Nil
    )
)

-- Declared at 3, the sentence leaves `y` unbound.
set_option fren.evidence "random" in
expect unbound_variable() {
    call r := sentence_instantiation(3, TWO_VARIABLES, UNBOUND_APPLICATIONS)
    expect y_unbound: r.verdict = SentenceInstantiation::Unbound(1)
}

-- Declared at 2, the sentence applies `f`, which is not declared before it.
set_option fren.evidence "random" in
expect unordered_application() {
    call r := sentence_instantiation(2, TWO_VARIABLES, UNBOUND_APPLICATIONS)
    expect f_not_earlier: r.verdict = SentenceInstantiation::Unordered(0)
}

-- `law flagged(s: Self, b?): when b?, obs(s) >= 0`, with `obs` declared at 1 and the law at 2.
pub const FLAGGED_VARIABLES: SentenceVariables := SentenceVariables::Cons(
    quantified(false),
    SentenceVariables::Cons(quantified(true), SentenceVariables::Nil)
)

set_option fren.evidence "random" in
expect listed_variable() {
    call r := sentence_instantiation(
        2,
        FLAGGED_VARIABLES,
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
}
```

`lang::sentence_use` states which sentences a check uses, from the
sentences visible to it and the items that its query applies:

```fren
-- A lemma, `assume` item or law, or a goal, visible to a check.
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

-- Whether `p` may be used by a check of the item at `check`, where its subject is applied.
pub fn fact?(p: Sentence, check: Int) := p.kind in {SentenceKind::Lemma, SentenceKind::Assume, SentenceKind::Law}
    and p.position < check and instantiation_verdict(p.position, p.variables, p.applications) = SentenceInstantiation::Instantiable

-- Whether `p` is used where the query and the instances apply `items`.
pub fn used?(p: Sentence, check: Int, items: Set<Int>) := fact?(p, check) and last_item(p.applications) in items

-- The items that the instances of the sentences of `ps` that `items` brings apply.
pub fn brought(ps: Sentences, check: Int, items: Set<Int>): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) => (if used?(p, check, items) then applied_items(p.applications) else {}) union brought(rest, check, items),
}

-- `items`, with what the sentences `all` bring, once for each sentence of `rounds`.
pub fn reach(rounds: Sentences, all: Sentences, check: Int, items: Set<Int>): Set<Int> := match rounds {
    Sentences::Nil => items,
    Sentences::Cons(_, rest) => reach(rest, all, check, items union brought(all, check, items)),
}

pub fn used_positions(ps: Sentences, check: Int, items: Set<Int>): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) => (if used?(p, check, items) then {p.position} else {}) union used_positions(rest, check, items),
}

set_option fren.evidence "random" in
pub proc sentence_use(
    check: Int,                  -- the position of the item whose check it is
    sentences: Sentences,      -- the sentences visible to the check
    applied: Set<Int>,           -- the items that the query applies or calls
): (det reached: Set<Int>, det used: Set<Int>) {
    out reached := reach(sentences, sentences, check, applied)
    out used := used_positions(sentences, check, reached)

    expect query_items_reached: applied subset reached
    expect only_earlier: when sentences = Sentences::Nil, used = {}
}

-- `assume made(fs: Fs, p: Path): exists?(mkdir(fs, p), p)`, with `mkdir`
-- declared at 1, `exists?` at 2 and the axiom at 3.
pub const MADE: Sentences := Sentences::Cons(
    Sentence {
        kind := SentenceKind::Assume,
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

-- A later check that applies `exists?` uses it, and reaches `mkdir`.
set_option fren.evidence "random" in
expect made_used() {
    call r := sentence_use(4, MADE, {2})
    expect used: r.used = {3}
    expect reaches_mkdir: 1 in r.reached
}

-- One that applies only `mkdir` does not.
set_option fren.evidence "random" in
expect made_unused() {
    call r := sentence_use(4, MADE, {1})
    expect unused: r.used = {}
}

-- Nor does the check of an item declared before it.
set_option fren.evidence "random" in
expect made_later() {
    call r := sentence_use(3, MADE, {2})
    expect not_before: r.used = {}
}
```

> **Rationale:** Instantiating at the query's own terms keeps each query
> quantifier-free and its verdict the same in both front ends. In the
> experiment of #669, ground instances always sufficed: every theorem that
> was not proved needed a generalization or a lemma that nobody wrote. The
> binding rule takes variables only from the subject's applications because
> the closure would not end otherwise: with `forall z, f(z) = g(z)` taking
> `z` from `f`'s arguments, and `forall x, f(g(x)) = 0`, each application
> `g(a)` brings `f(g(a))`, which brings `g(g(a))`, and so on. Under the two
> rules each instance applies the subject only to terms that the query
> already has within the subject's applications, or to closed terms, and
> applies every other item only where that item is declared before the
> subject. So the applications of the item declared last are finitely many
> once those of the items after it are, and the closure ends. Fren
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
An axiom is never proved. Fren checks that the axioms of each module can
hold together (its *consistency*), item by abstract item, in the tier that
`lang::consistency` gives. The axioms of an abstract item are those of its
module's axioms that mention it.

r[module.tier.modular]
An abstract item whose axioms mention no other abstract item of its module
is checked as today: it is *realizable* where, for each argument that
meets its domain, some value meets its axioms, whatever the other items
are (tier 1, [Realizability](../Check.md#contracts-of-uninterpreted-functions)).
An `ensure`'s axiom is its item's alone, whatever else it mentions.

r[module.tier.relative]
An abstract item whose `assume` items or laws mention other abstract
items of its module is *relatively realizable* where its axioms are
realizable for every interpretation of the others that meets the others'
own axioms (tier 2), as in the rely-guarantee method.

r[module.tier.joint]
Where an item is not shown relatively realizable, its module's axioms are
*jointly consistent* where some interpretation of the module's abstract
items meets all of them (tier 3).

r[module.tier.theories]
The tiers are the same for every theory, whichever construct it is: a
module's abstract items, an
interface's `Self` and methods, and a generic function's type parameters
and their bounds' members.

r[module.consistency.evidence]
The evidence of consistency is, from strongest to weakest: a total
implementation whose obligations hold (a *witness*), a
tier's proof, an interpretation that bounded model finding finds up to its
bound, or none, which is Inconclusive.

r[module.consistency.vacuity]
Where the axioms cannot hold together, every check that uses them holds
vacuously, and the report names a minimal set of axioms that cannot hold
together.

r[module.assume.trusted]
An axiom that no implementation makes an obligation is reported as trusted: a
pass that rests on it says that it does, as one that rests on a trait's
laws does (`F0665`).

r[module.inst]
An implementation of an interface, `mod x: I<T>` or an `inst`, is a total
morphism from the interface (`module.implementation`). Each law is an obligation of it, over its
`Self` and its members. Where every law holds, each lemma of the interface
holds of the implementation without another check, and the implementation
is a witness of the laws' consistency.

r[module.inst.group]
A group of abstract functions that is meant to be implemented together is
an interface, and a refinement of the group is an implementation of it.

r[module.impl]
The [`impl`](../Impl.md) and [`interp`](../Impl.md#interpretations)
bindings of a spec are an implementation of its module, partial where
some abstract item has neither. An axiom that becomes an obligation of it is
proved in Lean, and where the implementation is total, it is a witness of the
module's consistency.

r[module.generic.check]
A generic function's contract is checked once, at its type parameters, as
the theorems of its one-item theory, and each instance `f<Int>` uses it
translated, by `module.implementation.theorems`.

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
    others: Seq<Int>,      -- the other abstract items of the module that the item's `assume` items and laws mention
    witness?,              -- a total implementation of the module meets its axioms
    modular: Answer,       -- tier 1: realizable whatever the others are
    relative: Answer,      -- tier 2: realizable for every interpretation of the others that meets their axioms
    joint: Answer,         -- tier 3: some interpretation meets all of them
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

    out evidence := if witness? then Witness
        else if others = [] then (match modular {
            Answer::Holds => Modular,
            Answer::Fails => Unrealizable,
            Answer::Unknown => Inconclusive,
        })
        else if relative = Answer::Holds then Relative
        else match joint {
            Answer::Holds => Joint,
            Answer::Fails => Inconsistent,
            Answer::Unknown => if found? then Bounded else Inconclusive,
        }

    -- Tier 1 is today's check, and a sentence of one item is never judged by the later tiers.
    expect as_today: when not witness? and others = [], evidence in {Modular, Unrealizable, Inconclusive}
    expect witness_suffices: when witness?, evidence = Witness
    expect relative_before_joint: when not witness? and others != [] and relative = Answer::Holds, evidence = Relative
    expect inconsistency_needs_proof: when evidence = Inconsistent, joint = Answer::Fails
}
```

> **Rationale:** The file system of #631 has abstract functions, such as
> `at`, `mkdir` and `rm`, whose sentences relate them, and so fail tier 1,
> which asks each to be realizable whatever the others are. Tier 2 is the
> rely-guarantee reading of such a group; tier 3 is the consistency of
> ACL2's `encapsulate`, Why3's realizations and Alloy's `run`. A group
> that cannot hold together makes every check that uses it vacuous, so the
> report must say which sentences to blame.

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
pub fn candidate_positions(types: ParamTypes, decreasing: Set<Int>, k: Int): Set<Int> := match types {
    ParamTypes::Nil => {},
    ParamTypes::Cons(recursive?, rest) => (if recursive? and k in decreasing then {k} else {}) union candidate_positions(rest, decreasing, k + 1),
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
    out verdict := if direct != CheckVerdict::Inconclusive then direct
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
A spec without lemmas, `assume` items, `require`s, an `expect` in a
function, or a sentence with calls outside a global expectation has the
same messages and verdicts as before this chapter, but that a check that
was Inconclusive may pass by induction (`lang::strict_expansion`).

r[module.expansion.laws]
A trait's laws are the one exception: once their consistency is checked
(`module.axiom.check`), the warning that a verdict rests on laws whose
consistency is not checked (`F0665`) gives way to that check's.

r[module.expansion.corpus]
Each stage that lands compares the messages of Fren's own specs and of the
ui tests, before and after, and every difference is one that
`module.expansion` allows.

```fren
set_option fren.evidence "enumerated" in
pub proc strict_expansion(
    new_forms?,                  -- the spec uses a form of this chapter
    before: CheckVerdict,
    after: CheckVerdict,
    by_induction?,               -- the check passes by induction
): (det allowed?) {
    out allowed? := new_forms? or after = before
        or (before = CheckVerdict::Inconclusive and after = CheckVerdict::Pass and by_induction?)

    expect passes_stay: when not new_forms? and before = CheckVerdict::Pass and allowed?, after = CheckVerdict::Pass
    expect failures_stay: when not new_forms? and before = CheckVerdict::Fail and allowed?, after = CheckVerdict::Fail
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
#fren_check sentence_place
#fren_check sentence_member
#fren_check sentence_role
#fren_check sentence_instantiation
#fren_check get_put_instantiation
#fren_check nested_anchor
#fren_check unbound_variable
#fren_check unordered_application
#fren_check listed_variable
#fren_check sentence_use
#fren_check made_used
#fren_check made_unused
#fren_check made_later
#fren_check consistency
#fren_check induction_variables
#fren_check arm_decided
#fren_check induction_verdict
#fren_check strict_expansion
```
