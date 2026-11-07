# Implementations

An *implementation* gives the abstract items of an interface their
definitions in a module. It is a *theory morphism*: it maps the
interface's `Self` and methods to a type and items of the module, and
*translates* each of the interface's sentences, its laws and lemmas, by
that map. The translated laws are the implementation's *obligations*,
which it proves. The translated lemmas hold of it without another proof,
once its obligations do.

```text
trait Monoid {
    fn op(Self, Self): Self
    fn unit(): Self
    law left(x: Self): op(unit(), x) = x
    law assoc(x: Self, y: Self, z: Self): op(op(x, y), z) = op(x, op(y, z))
    lemma twice(x: Self): op(unit(), op(unit(), x)) = x
}

mod sum: Monoid<Int> { fn op(a: Int, b: Int): Int := a + b; fn unit(): Int := 0 }

lemma zero_twice(n: Int): 0 + (0 + n) = n
```

Here `sum`'s obligations are `left` and `assoc` at `Int`, `twice` holds of
`sum` once they do, and `zero_twice` may use `twice` at `sum`, since `sum`
is declared before it.

Each check rests on the sentences that it uses, and a proof is sound only
where nothing rests on itself. This chapter states the rules of what a
check of a module may use as one model of the module, from which
`lang::module_rests_on` computes what each check rests on. Every rule is a
case of that relation. Soundness is stated once, over the model: nothing
rests on itself, and every pass rests only on axioms that Fren reports as
trusted and on sentences that Fren proves. The solver proves it of every
module, and a bounded enumeration of small modules confirms it apart from
the proof.

The chapter also states how a check uses a sentence, by instantiating it
at the terms of its query, and what it reports of the axioms it rests on.
These are what could change how a spec of today is checked, so each is
computed from the model, as the trust caveat `F0665` is.
[Reports of modules](../ModuleReports.md) computes the verdict of a check
of today's forms, and checks over every model that a spec of today's
forms keeps its verdicts and messages, but for the passes and errors that
`module.expansion` allows.

> **Note:** This chapter is the second half of the design of #669, which
> is not implemented yet. The first, [Modules](ModulesAndInterfaces.md),
> specifies modules as theories, lemma and `assume` items and which
> sentences a check may use, and changes nothing of how today's forms are
> checked. Implementations, written `mod x: I<T>` and replacing the
> `inst` to come of Traits stage 1, views, and instantiation come with
> #669's stage 3. Until then [Traits](Traits.md) says what Fren does.

```fren
pub mod lang
```

## Implementations as morphisms

**Legality rules**

r[implementation.morphism] lang::{theory_term_translation, theory_term_list, theory_translation}
An implementation `mod x: I<T>` of an interface `I` maps `I`'s `Self` to
`T` and each method of `I` that it defines to that definition. Each
sentence of `I`, translated, is a sentence of the module that declares the
implementation, at the implementation's place in the order of its items.

r[implementation.partial]
An implementation is *total* where it defines every method of `I`, and
*partial* otherwise. A law that mentions a method that it leaves abstract
is *trusted* at the implementation: an axiom there, which nothing proves.

r[implementation.obligations] lang::module_sentence, lang::total_obligation, lang::partial_trusted, lang::partial_unproved
Each other law of `I`, translated, is an *obligation* of the implementation,
which Fren checks as it checks a lemma, at the implementation's place. A
partial implementation's report lists the laws it leaves trusted.

r[implementation.refinement]
Each item that implements a method refines it: its `require` clauses are
the method's or weaker, its `ensure` clauses the method's or stronger, as
[Refinement](Refinement.md) checks of each member.

**Dynamic semantics**

r[implementation.theorems] lang::translated_grounded
A lemma of `I`, translated along a total implementation, holds of it
wherever the implementation's obligations hold, and along a partial one,
given the laws it leaves trusted (*functional instantiation*). Fren does not
check it again. It rests on the lemma's check, and on each obligation and
trusted law of the implementation.

r[implementation.view]
A *view* is a named implementation of one module by another, declared
apart from both, so that neither changes, as `le(x, y) := meet(x, y) = x`
makes a lattice a partial order. It owes the laws of the module it
implements, proved from the other's sentences, and is an implementation
in every rule of this chapter. Its keyword is not decided yet (#669).

> **Rationale:** One translation, along every kind of morphism, keeps
> implementations, instances of generic functions and views from differing
> in how they translate a claim. #635 needed seven rounds of review because
> generic functions were instantiated piecemeal. The design follows modular
> type classes (Dreyer, Harper, Chakravarty and Keller, POPL 2007), in
> which a class is a signature and an instance a structure; Clear, OBJ and
> CASL's views; and Specware's morphisms with proof obligations.

## Dispatch

A check that applies a method of `I` at a type takes an implementation of
`I` at it. Which one it takes, and so which translated sentences it may
use, depends on where the check's item is declared.

**Legality rules**

r[implementation.dispatch.order] lang::dispatch::later_never_taken
A check of the item at a place takes an implementation only where the
implementation is declared before that place. One declared after it is not
in scope for the check.

r[implementation.dispatch.choice] lang::dispatch, lang::dispatch_named, lang::dispatch_ambiguous
A check that names an implementation takes it, and it is an error where
that implementation is not in scope. A check that names none takes the one
implementation of `I` in scope, takes none where there is none, and is an
error where there are several, as `Int` is a monoid under `+` and under
`*`. `lang::dispatch` gives the choice, from the model of the module.

## What each check rests on

A *model* of a module has its items in order, each by its kind. An
interface has its numbers of laws and lemmas. An implementation has the
interface it implements, by place, and the laws it leaves trusted, by
number. A model leaves out what no rule here decides: the terms of the
sentences, and which instances a check takes.

A *sentence* of a model is one that a check may see: a law, a lemma of an
interface or of the module, an `assume` item, an implementation's
obligation or trusted law, or a lemma translated along an implementation.
Each is declared at an item's place, and a translated sentence also names
the implementation it is translated along.

**Dynamic semantics**

r[implementation.model] lang::module_sentence
A model's sentences are those that `lang::module_sentence` gives: each law
and lemma of each interface, each lemma and `assume` item of the module,
and for each implementation, each law of its interface as an obligation or
as a trusted law, and each lemma of its interface translated along it.

r[implementation.use] lang::module_rests_on, lang::axioms_used_anywhere
The check of an item other than an interface, at a place, uses every `assume` item of the module,
wherever it is declared, and each lemma of the module declared before that
place.

r[implementation.lemma-order] lang::module_rests_on
The check of an interface's lemma or expectation uses only the interface's
laws and its lemmas declared before it: an interface is a closed theory,
whose checks use no `assume` item, module lemma or translated sentence of
the module that declares it. An expectation uses all of the interface's
lemmas.

r[implementation.use.morphism] lang::module_rests_on, lang::lemma_before_implementation
The check of an item at a place uses the sentences translated along each
implementation that it may take there (`implementation.dispatch.order`),
and the obligations of each such implementation, whose own checks hold
apart.

r[implementation.self] lang::module_rests_on, lang::own_translated_lemma
The check of an implementation's obligation uses the laws that the
implementation leaves trusted, and, of the rest of the implementation,
nothing: none of its other obligations, and none of the lemmas translated
along it. Of the module's other sentences it uses what
`implementation.use` and `implementation.use.morphism` give a check at the
implementation's place.

r[implementation.rests-on] lang::module_rests_on
A sentence *rests on* each sentence that its check uses, and a translated
lemma on what `implementation.theorems` states. These are all the cases:
an axiom rests on nothing.

**Proof obligations**

r[implementation.rests-on.acyclic] lang::rests_on_ranked, lang::small_modules_acyclic
No sentence rests on itself, directly or through other sentences. The
solver proves of every model that each case of `lang::module_rests_on`
goes down in one ranking of the sentences: the
axioms first, then the interfaces' lemmas in order, then the items in the
order of the module, an implementation's obligations after the lemmas
before it, and its translated lemmas after its obligations. A ranking that
each case goes down leaves no cycle. `lang::small_modules_acyclic` checks
the absence of cycles directly, without the ranking, by enumerating every
order of the items of small modules.

r[implementation.rests-on.grounded] lang::module_rests_on::axioms_rest_on_nothing, lang::translated_grounded
Every pass rests only on axioms and on sentences that Fren proves: the
laws of an interface, which hold of its abstract `Self`, the laws an
implementation leaves trusted, and `assume` items, which Fren reports as
trusted; lemmas and obligations, which Fren checks; and translated lemmas,
which hold by `implementation.theorems` of what they rest on.

r[implementation.counterexamples] lang::lemma_before_implementation, lang::own_translated_lemma
The two cycles that reviews of #691 found are rejected. A lemma at 4 does
not use a lemma translated along an implementation at 5. An obligation
does not use a lemma translated along its own implementation, which would
rest on the obligation.

> **Note:** So the obligation of the implementation at 5, proved from the
> lemma at 4, does not rest on itself.

The solver model stores every finite item order as a sequence, so lookup
and length have their exact meanings in its witness checks. Enumeration
uses a linked representation: it cannot index a sequence within a
recursive function. Both use the same predicates, whose accessor gives
raw items; the predicates compute sentence validity, scope and dependencies.

```fren
-- What an item of a module is, to the checks that may use it.
pub enum ModuleItemKind {
    Interface,       -- an interface, today a trait
    Implementation,  -- an implementation of an interface, or a view
    Lemma,           -- a lemma item of the module
    Assume,          -- an `assume` item of the module
    Goal,            -- an `expect` item of the module: checked, never used
    Other,           -- an item that states no claim, as a function or a type
}

-- An item, at its place in the order of the module's items.
pub struct ModuleItem {
    kind: ModuleItemKind,
    laws: Int,               -- an interface's laws, numbered from 0
    lemmas: Int,             -- an interface's lemmas, numbered from 0 in their order
    goals: Int,              -- an interface's expectations, numbered from 0
    implements: Int,         -- an implementation's interface, by its place
    unproved: Set<Int>,      -- the laws that an implementation leaves trusted
    asked?,                  -- a lemma or `expect` item has `require` clauses or calls
    asked_lemmas: Set<Int>,  -- an interface's lemmas with `require` clauses or calls
    asked_goals: Set<Int>,   -- an interface's expectations with assumptions or calls
}

-- A module: its items in order, each at its place.
pub struct ModuleModel { items: Seq<ModuleItem> }

-- What is at a place where no item is.
pub const NO_ITEM: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Other,
    laws := 0,
    lemmas := 0,
    goals := 0,
    implements := -1,
    unproved := {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

-- A sequence retains every finite item order, with lookup and length
-- available to the solver rather than hidden behind recursive contracts.
pub fn item_at(items: Seq<ModuleItem>, i: Int): ModuleItem :=
    if 0 <= i < items.len then items[i] else NO_ITEM

pub fn item_of(m: ModuleModel, i: Int): ModuleItem := item_at(m.items, i)

pub fn item_count(items: Seq<ModuleItem>): Int := items.len

-- A linked representation for executable enumeration: recursive sequence
-- indexes cannot be enumerated. Both representations use the shared
-- predicates, with only their raw-item accessor differing.
pub enum ModuleItems { Nil, Cons(ModuleItem, ModuleItems) }

pub fn linked_item_at(items: ModuleItems, i: Int): ModuleItem := match items {
    ModuleItems::Nil => NO_ITEM,
    ModuleItems::Cons(item, rest) => if i = 0 then item else linked_item_at(rest, i - 1),
}

pub fn linked_item_count(items: ModuleItems): Int := match items {
    ModuleItems::Nil => 0,
    ModuleItems::Cons(_, rest) => 1 + linked_item_count(rest),
}

-- A sentence that a check may see, by the place of the item that declares
-- it, or of the implementation that it is translated along, and its number
-- there.
pub enum ModuleSentence {
    Law(Int, Int),               -- a law of the interface at the place
    InterfaceLemma(Int, Int),    -- a lemma of the interface at the place
    InterfaceGoal(Int, Int),     -- an expectation of the interface at the place
    Obligation(Int, Int),        -- a law, translated along the implementation at the place, that it proves
    TrustedLaw(Int, Int),        -- a law, translated along the implementation at the place, that it leaves trusted
    Translated(Int, Int),        -- a lemma, translated along the implementation at the place
    ModuleLemma(Int),            -- the lemma item at the place
    ModuleGoal(Int),             -- the `expect` item at the place
    Assumed(Int),                -- the `assume` item at the place
}

-- The place of the item that declares `s`, or of the implementation that
-- it is translated along.
pub fn declared_at(s: ModuleSentence): Int := match s {
    ModuleSentence::Law(i, _) => i,
    ModuleSentence::InterfaceLemma(i, _) => i,
    ModuleSentence::InterfaceGoal(i, _) => i,
    ModuleSentence::Obligation(x, _) => x,
    ModuleSentence::TrustedLaw(x, _) => x,
    ModuleSentence::Translated(x, _) => x,
    ModuleSentence::ModuleLemma(t) => t,
    ModuleSentence::ModuleGoal(t) => t,
    ModuleSentence::Assumed(a) => a,
}

pub fn kind_at_from?(get: fn(Int) -> ModuleItem, i: Int, wanted: ModuleItemKind) :=
    0 <= i and get(i).kind = wanted

pub fn kind_at?(m: ModuleModel, i: Int, wanted: ModuleItemKind) :=
    kind_at_from?(|place| item_of(m, place), i, wanted)

-- The place of the interface that the implementation at `x` implements.
pub fn implemented_from(get: fn(Int) -> ModuleItem, x: Int): Int := get(x).implements

pub fn implemented(m: ModuleModel, x: Int): Int := implemented_from(|place| item_of(m, place), x)

pub fn implementation_at_from?(get: fn(Int) -> ModuleItem, x: Int) :=
    kind_at_from?(get, x, ModuleItemKind::Implementation) and kind_at_from?(get, implemented_from(get, x), ModuleItemKind::Interface)

pub fn implementation_at?(m: ModuleModel, x: Int) :=
    implementation_at_from?(|place| item_of(m, place), x)

-- Whether `s` is a sentence of `m`.
set_option fren.lint.undecidable "allow" in
pub fn sentence_of_from?(get: fn(Int) -> ModuleItem, s: ModuleSentence) := match s {
    ModuleSentence::Law(i, k) =>
        kind_at_from?(get, i, ModuleItemKind::Interface) and 0 <= k < get(i).laws,
    ModuleSentence::InterfaceLemma(i, k) =>
        kind_at_from?(get, i, ModuleItemKind::Interface) and 0 <= k < get(i).lemmas,
    ModuleSentence::InterfaceGoal(i, k) =>
        kind_at_from?(get, i, ModuleItemKind::Interface) and 0 <= k < get(i).goals,
    ModuleSentence::Obligation(x, k) =>
        implementation_at_from?(get, x) and 0 <= k < get(implemented_from(get, x)).laws and not k in get(x).unproved,
    ModuleSentence::TrustedLaw(x, k) =>
        implementation_at_from?(get, x) and 0 <= k < get(implemented_from(get, x)).laws and k in get(x).unproved,
    ModuleSentence::Translated(x, k) =>
        implementation_at_from?(get, x) and 0 <= k < get(implemented_from(get, x)).lemmas,
    ModuleSentence::ModuleLemma(t) => kind_at_from?(get, t, ModuleItemKind::Lemma),
    ModuleSentence::ModuleGoal(t) => kind_at_from?(get, t, ModuleItemKind::Goal),
    ModuleSentence::Assumed(a) => kind_at_from?(get, a, ModuleItemKind::Assume),
}

pub fn sentence_of?(m: ModuleModel, s: ModuleSentence) :=
    sentence_of_from?(|place| item_of(m, place), s)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc module_sentence(m: ModuleModel, s: ModuleSentence): (det sentence?) {
    out sentence? := sentence_of?(m, s)

    expect declared_in_the_module: not sentence? or 0 <= declared_at(s) < item_count(m.items)
}

-- The place of the item whose check is `s`'s, or -1 for an axiom, which
-- has no check.
pub fn check_place(s: ModuleSentence): Int := match s {
    ModuleSentence::InterfaceLemma(i, _) => i,
    ModuleSentence::InterfaceGoal(i, _) => i,
    ModuleSentence::Obligation(x, _) => x,
    ModuleSentence::ModuleLemma(t) => t,
    ModuleSentence::ModuleGoal(t) => t,
    _ => -1,
}

-- Whether the item of the check of `s` has a vacuity check under the
-- axioms, as `check::law_premise`'s `asked?` takes it: it has `require`
-- clauses or calls, or, for a trait's expectation, assumptions or calls
-- (`traits.expect.lawful`).
pub fn asked_of?(m: ModuleModel, s: ModuleSentence) := match s {
    ModuleSentence::InterfaceLemma(i, k) => k in item_of(m, i).asked_lemmas,
    ModuleSentence::InterfaceGoal(i, k) => k in item_of(m, i).asked_goals,
    ModuleSentence::ModuleLemma(t) => item_of(m, t).asked?,
    ModuleSentence::ModuleGoal(t) => item_of(m, t).asked?,
    _ => false,
}

-- The implementation that `s` is translated along, or -1.
pub fn translated_along(s: ModuleSentence): Int := match s {
    ModuleSentence::Obligation(x, _) => x,
    ModuleSentence::TrustedLaw(x, _) => x,
    ModuleSentence::Translated(x, _) => x,
    _ => -1,
}

pub fn axiom?(s: ModuleSentence) :=
    s is ModuleSentence::Law(_, _) or s is ModuleSentence::TrustedLaw(_, _) or s is ModuleSentence::Assumed(_)
```

`lang::module_rests_on` is the relation, each of its cases one rule:

```fren
-- `implementation.lemma-order`: what the check of a lemma or expectation
-- of the interface at `i` uses.
pub fn interface_uses?(i: Int, own: Int, goal?, u: ModuleSentence) := match u {
    ModuleSentence::Law(j, _) => j = i,
    ModuleSentence::InterfaceLemma(j, l) => j = i and (goal? or l < own),
    _ => false,
}

-- `implementation.dispatch.order`: whether the check of the item at `p`
-- may take the implementation at `x`.
pub fn implementation_in_scope_from?(get: fn(Int) -> ModuleItem, p: Int, x: Int) :=
    implementation_at_from?(get, x) and x < p

pub fn implementation_in_scope?(m: ModuleModel, p: Int, x: Int) :=
    implementation_in_scope_from?(|place| item_of(m, place), p, x)

-- `implementation.use`, `implementation.use.morphism` and
-- `implementation.self`: what the check of the item at `p` uses, where
-- `own` is the implementation whose obligation it is, or -1.
pub fn item_uses_from?(get: fn(Int) -> ModuleItem, p: Int, own: Int, u: ModuleSentence) := match u {
    ModuleSentence::Assumed(_) => true,
    ModuleSentence::ModuleLemma(t) => t < p,
    ModuleSentence::Obligation(y, _) => y != own and implementation_in_scope_from?(get, p, y),
    ModuleSentence::Translated(y, _) => y != own and implementation_in_scope_from?(get, p, y),
    ModuleSentence::TrustedLaw(y, _) => y = own or implementation_in_scope_from?(get, p, y),
    _ => false,
}

pub fn item_uses?(m: ModuleModel, p: Int, own: Int, u: ModuleSentence) :=
    item_uses_from?(|place| item_of(m, place), p, own, u)

-- `implementation.theorems`: what the lemma `k` translated along the
-- implementation at `x` rests on.
pub fn translation_rests_from?(get: fn(Int) -> ModuleItem, x: Int, k: Int, u: ModuleSentence) :=
    match u {
        ModuleSentence::Obligation(y, _) => y = x,
        ModuleSentence::TrustedLaw(y, _) => y = x,
        ModuleSentence::InterfaceLemma(i, l) => i = implemented_from(get, x) and l = k,
        _ => false,
    }

pub fn translation_rests?(m: ModuleModel, x: Int, k: Int, u: ModuleSentence) :=
    translation_rests_from?(|place| item_of(m, place), x, k, u)

pub fn rests_case_from?(get: fn(Int) -> ModuleItem, n: ModuleSentence, u: ModuleSentence) :=
    match n {
        ModuleSentence::InterfaceLemma(i, k) => interface_uses?(i, k, false, u),
        ModuleSentence::InterfaceGoal(i, k) => interface_uses?(i, k, true, u),
        ModuleSentence::Obligation(x, _) => item_uses_from?(get, x, x, u),
        ModuleSentence::ModuleLemma(t) => item_uses_from?(get, t, -1, u),
        ModuleSentence::ModuleGoal(t) => item_uses_from?(get, t, -1, u),
        ModuleSentence::Translated(x, k) => translation_rests_from?(get, x, k, u),
        _ => false,
    }

pub fn rests_case?(m: ModuleModel, n: ModuleSentence, u: ModuleSentence) :=
    rests_case_from?(|place| item_of(m, place), n, u)

pub fn rests_between?(m: ModuleModel, n: ModuleSentence, u: ModuleSentence) :=
    sentence_of?(m, n) and sentence_of?(m, u) and rests_case?(m, n, u)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc module_rests_on(m: ModuleModel, n: ModuleSentence, u: ModuleSentence): (det rests?) {
    out rests? := rests_between?(m, n, u)

    expect axioms_rest_on_nothing: when axiom?(n), not rests?
    expect goals_unused: when u is ModuleSentence::ModuleGoal(_) or u is ModuleSentence::InterfaceGoal(_, _), not rests?
}
```

`lang::module_rests_on` decides, from the model alone, every fact that
the rules decide: which sentences there are, the places of the items, and
which implementations a check may take. No deciding fact is an input.

The ranking of `implementation.rests-on.acyclic`, as a triple compared in
order:

```fren
pub struct SentenceRank { level: Int, place: Int, step: Int }

pub fn sentence_rank(s: ModuleSentence): SentenceRank := match s {
    ModuleSentence::InterfaceLemma(_, k) => SentenceRank { level := 1, place := k, step := 0 },
    ModuleSentence::InterfaceGoal(_, _) => SentenceRank { level := 2, place := -1, step := 0 },
    ModuleSentence::ModuleLemma(t) => SentenceRank { level := 2, place := t, step := 0 },
    ModuleSentence::ModuleGoal(t) => SentenceRank { level := 2, place := t, step := 0 },
    ModuleSentence::Obligation(x, _) => SentenceRank { level := 2, place := x, step := 1 },
    ModuleSentence::Translated(x, _) => SentenceRank { level := 2, place := x, step := 2 },
    _ => SentenceRank { level := 0, place := 0, step := 0 },
}

pub fn ranked_below?(a: SentenceRank, b: SentenceRank) :=
    a.level < b.level or (a.level = b.level and (a.place < b.place or (a.place = b.place and a.step < b.step)))

-- Each case of `lang::module_rests_on`, in every model, of any size, and
-- whether or not its sentences are the model's.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect rests_on_ranked(m: ModuleModel, n: ModuleSentence, u: ModuleSentence) {
    expect interface_lemmas: when n is ModuleSentence::InterfaceLemma(_, _) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect interface_goals: when n is ModuleSentence::InterfaceGoal(_, _) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect obligations: when n is ModuleSentence::Obligation(_, _) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect module_lemmas: when n is ModuleSentence::ModuleLemma(_) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect module_goals: when n is ModuleSentence::ModuleGoal(_) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect translated: when n is ModuleSentence::Translated(_, _) and rests_case?(m, n, u),
        ranked_below?(sentence_rank(u), sentence_rank(n))
    expect axioms: when axiom?(n), not rests_case?(m, n, u)
}

-- `implementation.rests-on.grounded`: a translated lemma rests on its
-- lemma and on every law of its implementation, proved or trusted, in
-- every model.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect translated_grounded(m: ModuleModel, x: Int, k: Int, j: Int) {
    expect its_lemma: rests_case?(
        m,
        ModuleSentence::Translated(x, k),
        ModuleSentence::InterfaceLemma(implemented(m, x), k)
    )
    expect every_law: rests_case?(
        m,
        ModuleSentence::Translated(x, k),
        ModuleSentence::Obligation(x, j)
    )
        and rests_case?(
            m,
            ModuleSentence::Translated(x, k),
            ModuleSentence::TrustedLaw(x, j)
        )
}
```

The cycles that `implementation.counterexamples` names, in a module whose
items are an interface at 0, with one law and one lemma, lemmas at 1 to 4,
and an implementation of the interface at 5:

```fren
pub const MONOID: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Interface,
    laws := 1,
    lemmas := 1,
    goals := 0,
    implements := -1,
    unproved := {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

pub const MODULE_LEMMA: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Lemma,
    laws := 0,
    lemmas := 0,
    goals := 0,
    implements := -1,
    unproved := {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

pub const SUM: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Implementation,
    laws := 0,
    lemmas := 0,
    goals := 0,
    implements := 0,
    unproved := {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

-- An implementation of the interface at 0 that leaves its law trusted.
pub const HALF_SUM: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Implementation,
    laws := 0,
    lemmas := 0,
    goals := 0,
    implements := 0,
    unproved := {0},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

pub const PARTIAL: ModuleModel := ModuleModel { items := [MONOID, HALF_SUM] }

pub const TOTAL: ModuleModel := ModuleModel { items := [MONOID, SUM] }

-- A total implementation proves its law.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect total_obligation() {
    call r := module_sentence(TOTAL, ModuleSentence::Obligation(1, 0))
    expect obligation: r.sentence?
}

-- A partial one leaves it trusted, and does not prove it.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect partial_trusted() {
    call r := module_sentence(PARTIAL, ModuleSentence::TrustedLaw(1, 0))
    expect trusted_law: r.sentence?
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect partial_unproved() {
    call r := module_sentence(PARTIAL, ModuleSentence::Obligation(1, 0))
    expect no_obligation: not r.sentence?
}

pub const LATE_IMPLEMENTATION: ModuleModel := ModuleModel {
    items := [
        MONOID,
        MODULE_LEMMA,
        MODULE_LEMMA,
        MODULE_LEMMA,
        MODULE_LEMMA,
        SUM,
    ],
}

-- The obligation of the implementation at 5 may use the lemma at 4.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect obligation_from_earlier_lemma() {
    call r := module_rests_on(
        LATE_IMPLEMENTATION,
        ModuleSentence::Obligation(5, 0),
        ModuleSentence::ModuleLemma(4),
    )
    expect obligation_uses_lemma: r.rests?
}

-- So the lemma at 4 may not use the lemma translated along the
-- implementation at 5.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect lemma_before_implementation() {
    call r := module_rests_on(
        LATE_IMPLEMENTATION,
        ModuleSentence::ModuleLemma(4),
        ModuleSentence::Translated(5, 0),
    )
    expect lemma_rejects_translation: not r.rests?
}

-- A lemma translated along an implementation rests on its obligations.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect translation_on_obligation() {
    call r := module_rests_on(
        LATE_IMPLEMENTATION,
        ModuleSentence::Translated(5, 0),
        ModuleSentence::Obligation(5, 0),
    )
    expect translation_rests_on_obligation: r.rests?
}

-- So an obligation may not use a lemma translated along its own
-- implementation.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect own_translated_lemma() {
    call r := module_rests_on(
        LATE_IMPLEMENTATION,
        ModuleSentence::Obligation(5, 0),
        ModuleSentence::Translated(5, 0),
    )
    expect obligation_rejects_translation: not r.rests?
}

-- An `assume` item is used wherever it is declared.
pub const ASSUME_AFTER: ModuleModel := ModuleModel {
    items := [
        MODULE_LEMMA,
        ModuleItem {
            kind := ModuleItemKind::Assume,
            laws := 0,
            lemmas := 0,
            goals := 0,
            implements := -1,
            unproved := {},
            asked? := false,
            asked_lemmas := {},
            asked_goals := {},
        },
    ],
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect axioms_used_anywhere() {
    call r := module_rests_on(
        ASSUME_AFTER,
        ModuleSentence::ModuleLemma(0),
        ModuleSentence::Assumed(1),
    )
    expect later_axiom: r.rests?
}
```

## Dispatch over the model

`lang::dispatch` gives the implementation that a check takes, from the
implementations of the interface that are in scope at the check's place:

```fren
-- Whether the implementation at `x` implements the interface at `i` and is
-- in scope at `p`.
pub fn candidate_from?(get: fn(Int) -> ModuleItem, p: Int, i: Int, x: Int) :=
    implementation_in_scope_from?(get, p, x) and implemented_from(get, x) = i

pub fn candidate?(m: ModuleModel, p: Int, i: Int, x: Int) :=
    candidate_from?(|place| item_of(m, place), p, i, x)

-- The two clauses of dispatch's contract, combined below so that the
-- procedure and its fixed-module examples share the whole contract.
set_option fren.lint.undecidable "allow" in
pub fn dispatch_error_rule_from?(get: fn(Int) -> ModuleItem, p: Int, i: Int, named: Int, error?) :=
    error? iff (if named != -1 then not candidate_from?(get, p, i, named)
        else (exists (x: Int), 0 <= x < p and candidate_from?(get, p, i, x)
        and (exists (y: Int), x < y < p and candidate_from?(get, p, i, y))))

set_option fren.lint.undecidable "allow" in
pub fn dispatch_taken_rule_from?(
    get: fn(Int) -> ModuleItem,
    p: Int,
    i: Int,
    named: Int,
    taken: Int,
    error?
) :=
    if error? then taken = -1 else if named != -1 then taken = named
    else candidate_from?(get, p, i, taken) or (taken = -1 and not (exists (x: Int), 0 <= x < p and candidate_from?(get, p, i, x)))

-- Add dispatch's contract clauses here so changes reach its examples too.
pub fn dispatch_permitted_from?(
    get: fn(Int) -> ModuleItem,
    p: Int,
    i: Int,
    named: Int,
    taken: Int,
    error?
) :=
    dispatch_error_rule_from?(get, p, i, named, error?) and dispatch_taken_rule_from?(get, p, i, named, taken, error?)

pub fn dispatch_permitted?(m: ModuleModel, p: Int, i: Int, named: Int, taken: Int, error?) :=
    dispatch_permitted_from?(|place| item_of(m, place), p, i, named, taken, error?)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc dispatch(
    m: ModuleModel,
    p: Int,          -- the place of the check's item
    i: Int,          -- the interface whose method the check applies
    named: Int,      -- the implementation that the check names, or -1
): (det taken: Int, det error?) {
    ensure permitted: dispatch_permitted?(m, p, i, named, taken, error?)

    expect later_never_taken: when taken != -1, taken < p
    expect taken_implements: when taken != -1, candidate?(m, p, i, taken)
}

-- Of `sum` and `product`, both monoids at `Int` declared before the check,
-- a check that names neither is an error, and one that names `product`
-- takes it.
pub const TWO_MONOIDS: ModuleModel := ModuleModel {
    items := [MONOID, SUM, SUM, MODULE_LEMMA],
}

-- The same module as TWO_MONOIDS, in the executable linked view, to
-- avoid a loop in cvc5's sequence solver on the concrete sequence (#549).
-- dispatch_ambiguous and dispatch_earlier reproduce it with the sequence
-- view; switch them back when that solver issue is fixed.
-- Implementations.lean proves that the two views and the shared dispatch
-- contract agree. These examples quantify every permitted output directly.
pub const TWO_MONOID_ITEMS: ModuleItems := ModuleItems::Cons(
    MONOID,
    ModuleItems::Cons(
        SUM,
        ModuleItems::Cons(SUM, ModuleItems::Cons(MODULE_LEMMA, ModuleItems::Nil))
    )
)

pub fn two_monoid_dispatch?(p: Int, taken: Int, error?) := dispatch_permitted_from?(
    |place| linked_item_at(TWO_MONOID_ITEMS, place),
    p,
    0,
    -1,
    taken,
    error?
)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect dispatch_ambiguous(taken: Int, error?) {
    assume permitted: two_monoid_dispatch?(3, taken, error?)
    expect several: error?
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect dispatch_named() {
    call r := dispatch(TWO_MONOIDS, 3, 0, 2)
    expect named_taken: r.taken = 2 and not r.error?
}

-- A check at 2 has only `sum` in scope.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect dispatch_earlier(taken: Int, error?) {
    assume permitted: two_monoid_dispatch?(2, taken, error?)
    expect only_earlier: taken = 1 and not error?
}
```


## Instantiation

Fren uses a theorem or an axiom in a check by *instantiating* it: it puts
ground terms of the check's query for the sentence's quantified variables,
and adds each instance as a hypothesis. It chooses the instances itself,
from the applications and calls of the query, and no spec writes or sees
how a sentence is instantiated.

**Legality rules**

r[module.subject] lang::sentence_instantiation, lang::ground_subject_step
A sentence's *subject* is the item, of those it applies or calls, that
comes last in that order.

r[module.anchor] lang::sentence_instantiation, lang::ground_selection_step
An *anchor* of a sentence is an application of its subject, as a function,
that mentions no name that a quantifier within the sentence binds, and
that has an argument that is neither a quantified variable nor a closed
term. Where the sentence has no such application, each application of its
subject, as a function, that mentions no such name is an anchor.

r[module.matched] lang::sentence_instantiation, lang::ground_rule_step
The *matched* applications of a sentence are its anchors and each of its
calls that mentions no name that a quantifier within the sentence binds.

r[module.binding] lang::sentence_instantiation, lang::ground_variables_step
Each quantified variable of a sentence that occurs in an application of
it, and whose type is not [listed](Quantifiers.md#types), occurs in a
matched application. A variable that does not is an error that names it
(the *binding rule*).

r[module.binding.outside] lang::{outside_variable, theory_instance, ground_listed_step}
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

r[module.rules.laws] lang::unbound_law_quantified, lang::get_put_kept
Every `law` stays, as today, a quantified hypothesis of every check of its
trait ([Traits](Traits.md#laws)). A `law` that meets the binding rule is
also instantiated as a lemma is, and its instances are added to those
checks' queries (`module.instance.models`). A `law` that does not is not
an error, and is used only quantified.

r[module.rules.report] lang::sentence_instantiation
The error of a lemma or `assume` item that breaks the binding rule names
its first unbound variable. A law that breaks it gets no message
(`module.rules.laws`).

**Dynamic semantics**

r[module.instance] lang::{theory_term_substitution, theory_variable_images, theory_term_list, theory_instance}
An *instance* of a sentence is the sentence with a ground term in place of
each of its quantified variables that has one. It holds wherever the
sentence does.

r[module.instance.matching] lang::{ground_match_step, ground_normalization, ground_join_step, ground_rule_step, ground_preparation_step, ground_prepared_listed_step, ground_prepared_rule_step, ground_instance_list_step, ground_instances_step}
Fren takes the instances at which all the matched applications of the
sentence are terms of the query at once: each anchor an application of the
query, and each call a call of the query, with the same arguments once the
instance's terms are put in. Two terms are the same where they are written
alike, once each name that a `let`, a `where` clause or an `out :=`
defines, and each constant, is replaced by its definition. An application
of a function is not replaced by the function's body.

r[module.instance.ground] lang::{theory_ground_term, theory_variable_images, theory_instance}
An application of the query that mentions a name that a quantifier of the
query binds is not a term at which a sentence is instantiated.

r[module.instance.listed] lang::listed_variable, lang::ground_listed_step
A quantified variable of a listed type that no matched application binds
takes each value of its type, as a [quantifier over listed
types](Quantifiers.md#meaning) does.

r[module.instance.unused] lang::sentence_instantiation, lang::ground_listed_step
A quantified variable that the sentence does not mention takes no term.

r[module.instance.hypothesis] lang::theory_instance, lang::ground_close_step
Each instance adds its claims, under its domain, as one hypothesis of the
query. The applications and calls that the instance has are terms of the
query too, but for those that mention a name that stays quantified.

r[module.instance.quantifiers] lang::theory_instance
A quantifier within a sentence, and a variable that stays quantified
(`module.binding.outside`), are quantifiers of each instance. Where their
types are not listed, the instance is outside the [decidable
core](Decidability.md). Of a lemma or `assume` item, `undecidable` reports
it at the sentence, as it reports an [unbounded
quantifier](Quantifiers.md#unbounded-quantifiers). Sentences of today's
forms (`module.expansion`) are linted as written, as today: a law with a
variable of a type that is not listed is reported whether or not it is
instantiated (`traits.law.undecidable`), and a contract's quantifiers as
[Quantifiers](Quantifiers.md#unbounded-quantifiers) states.

> **Note:** So a law gets the same `undecidable` messages as today, and
> once each.

r[module.closure] lang::ground_activation_step, lang::ground_close_step
Fren instantiates each sentence that the check uses at the terms of the
query and of the instances, until no new instance arises. The *closure* is
the set of all those instances.

r[module.closure.finite] lang::ground_pool_step, lang::ground_universe_step, lang::ground_close_step
The closure of every query is finite. Take the items in reverse order
(`module.order.items`). Apart from its anchors, which are applications of
the query and so add none, an instance applies its subject only to
quantified variables, which matching binds to proper subterms of the query's
applications, or to the arguments and outputs of its calls, which no
instance adds, to values of listed types, and to closed terms of the
sentence. It applies
every other item only where that item comes before the subject. No bound
on the number of rounds is part of the language.

> **Rationale:** Taken in reverse order, the arguments of each item's
> applications are among finitely many terms, once the applications of the
> items after it are finitely many.

r[module.use.instantiated] lang::sentence_use
A check instantiates the sentences that `module.use` gives it and that
meet the binding rule, whose subject the closure applies. In particular,
an interface's checks use only its own laws and lemmas
(`implementation.lemma-order`). An `ensure` is used as a
[contract](Items.md#contracts) is.

r[module.use.subject] lang::sentence_use, lang::no_subject_used, lang::ground_enabled_step
A sentence is used where its subject is applied by the query, or by an
instance of a used sentence. A sentence that applies and calls nothing,
such as an `assume` item about an abstract type alone, has no subject, and
every check that may use it does, as its one instance.

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

set_option fren.lint.undecidable "allow" in
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

set_option fren.lint.undecidable "allow" in
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

set_option fren.lint.undecidable "allow" in
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
set_option fren.lint.undecidable "allow" in
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
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect outside_variable() {
    call r := sentence_instantiation(
        TWO_VARIABLES,
        Applications::Cons(app(1, [SentenceArg::Variable], {0}), Applications::Nil),
    )
    expect instantiable: r.verdict = SentenceInstantiation::Instantiable
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
    require earlier_items: last_item(written) <= function
    require own_at_parameters: not has_compound?(written, function)

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
-- A sentence visible to a check, by its keyword, where it is written, and
-- where it is declared.
pub struct Sentence {
    kind: SentenceKind,
    place: SentencePlace,
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

-- Whether `p` may be used by a check of the item at `check`, where its
-- subject is applied: an axiom, wherever it is declared, or a theorem
-- declared before the item, that meets the binding rule, each by the role
-- that `lang::role_of` gives it (`module.role`).
pub fn fact?(p: Sentence, check: Int) :=
    (role_of(p.kind, p.place) = SentenceRole::Axiom
        or (role_of(p.kind, p.place) = SentenceRole::Theorem and p.position < check))
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

-- The laws of `ps`, which every check of their trait uses as today,
-- quantified, whether or not they are also instantiated
-- (`module.rules.laws`).
pub fn quantified_laws(ps: Sentences): Set<Int> := match ps {
    Sentences::Nil => {},
    Sentences::Cons(p, rest) =>
        (if p.kind = SentenceKind::Law then {p.position} else {}) union quantified_laws(rest),
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
pub fn made(keyword: SentenceKind, place: SentencePlace): Sentences := Sentences::Cons(
    Sentence {
        kind := keyword,
        place,
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
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect made_used() {
    call r := sentence_use(4, made(SentenceKind::Assume, SentencePlace::Module), {2})
    expect used: r.used = {3}
    expect reaches_mkdir: 1 in r.reached
}

-- One that applies only `mkdir` does not.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect made_unused() {
    call r := sentence_use(4, made(SentenceKind::Assume, SentencePlace::Module), {1})
    expect unused: r.used = {}
}

-- An axiom is used by the check of an item declared before it: an
-- `assume` item, and a law, as by an expectation written before it.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect axioms_anywhere() {
    call assumed := sentence_use(2, made(SentenceKind::Assume, SentencePlace::Module), {2})
    expect used_before: assumed.used = {3}
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect laws_anywhere() {
    call law_used := sentence_use(2, made(SentenceKind::Law, SentencePlace::Interface), {2})
    expect used_before: law_used.used = {3}
}

-- `law l(s: Self, t: Self): f(s) <= g(s, t)`, with `g` at 1, `f` at 2
-- and the law at 3, breaks the binding rule, so every check of its trait
-- uses it quantified, whatever its query applies.
pub const UNBOUND_LAW: Sentence := Sentence {
    kind := SentenceKind::Law,
    place := SentencePlace::Interface,
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

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect unbound_law_quantified() {
    call r := sentence_use(4, Sentences::Cons(UNBOUND_LAW, Sentences::Nil), {})
    expect quantified: r.kept_quantified = {3}
    expect not_instantiated: r.used = {}
}

-- `get_put` at 3, which meets the binding rule: a check of its trait at 4
-- that applies `get` both instantiates it and keeps it quantified.
pub const GET_PUT_LAW: Sentence := Sentence {
    kind := SentenceKind::Law,
    place := SentencePlace::Interface,
    position := 3,
    variables := GET_PUT_VARIABLES,
    applications := GET_PUT_APPLICATIONS,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect get_put_kept() {
    call r := sentence_use(4, Sentences::Cons(GET_PUT_LAW, Sentences::Nil), {2})
    expect instantiated: r.used = {3}
    expect quantified: r.kept_quantified = {3}
}

-- `assume one(x: T, y: T): x = y`, about the abstract type `T` at 1 alone,
-- at 2: every later check uses it.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect no_subject_used() {
    call r := sentence_use(
        3,
        Sentences::Cons(
            Sentence {
                kind := SentenceKind::Assume,
                place := SentencePlace::Module,
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

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect lemmas_ranked() {
    call lemma := sentence_use(2, made(SentenceKind::Lemma, SentencePlace::Module), {2})
    expect not_before: lemma.used = {}
}

-- An `ensure` clause of a defined function at 3, which is a theorem: the
-- function's own check does not use it, and a later check does.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect defined_contract_not_own() {
    call own := sentence_use(
        3,
        made(SentenceKind::Ensure, SentencePlace::DefinedFunction),
        {2},
    )
    expect not_own: own.used = {}
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect defined_contract_later() {
    call later := sentence_use(
        4,
        made(SentenceKind::Ensure, SentencePlace::DefinedFunction),
        {2},
    )
    expect used_later: later.used = {3}
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
                place := SentencePlace::UninterpretedFunction,
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
> `f(g(g(c)))`, and so on. A model of the instances alone need not be one
> of the axioms: `forall (n: Nat), f(n) > f(n + 1)`, with `f` to `Nat`, has
> no model, but each finite set of its instances does. Fren chooses the
> instances that F\*'s `SMTPat` and Dafny's triggers have the author
> choose.

## Translation and substitution of terms

This model exposes the structure of resolved terms, lists and sentences
through their constructors and projections. Its equations apply at every
subterm and tail. Sentence parameters, indices bound by inner quantifiers,
and free names of the query occupy separate namespaces. Applications have
a function and an argument; successive applications record several
arguments. A type argument records a type. Literals also record built-in
operations, which a morphism does not rename.

A morphism supplies images of types and signature items. Each image belongs
to the target theory and is not translated again. The type map includes
substitution within type arguments. The same translation applies to the
domain, the calls and the claims of a sentence.

```fren
pub type TheoryTerm
pub type TheoryTerms
pub type TheoryVariables
pub type TheorySentence
pub type TheoryMorphism
pub type TheorySubstitution

pub enum TheoryTermKind { Variable, Bound, Query, Item, Literal, TypeArg, Apply, All, Exists }

pub fn theory_term_kind(TheoryTerm): TheoryTermKind
pub fn theory_term_name(TheoryTerm): TheoryName
pub fn theory_term_index(TheoryTerm): Nat
pub fn theory_term_type(TheoryTerm): Ty
pub fn theory_term_left(TheoryTerm): TheoryTerm
pub fn theory_term_right(TheoryTerm): TheoryTerm
pub fn theory_item(TheoryName): TheoryTerm
pub fn theory_type_arg(Ty): TheoryTerm
pub fn theory_apply(TheoryTerm, TheoryTerm): TheoryTerm
pub fn theory_all(Ty, TheoryTerm): TheoryTerm
pub fn theory_exists(Ty, TheoryTerm): TheoryTerm
pub fn theory_type_image(TheoryMorphism, Ty): Ty
pub fn theory_item_image(TheoryMorphism, TheoryName): TheoryName
pub fn translate_term(TheoryMorphism, TheoryTerm): TheoryTerm

pub proc theory_term_translation(m: TheoryMorphism, term: TheoryTerm): (
    det translated: TheoryTerm,
) {
    ensure rule: translated = match theory_term_kind(term) {
        TheoryTermKind::Item => theory_item(theory_item_image(m, theory_term_name(term))),
        TheoryTermKind::TypeArg => theory_type_arg(theory_type_image(m, theory_term_type(term))),
        TheoryTermKind::Apply => theory_apply(
            translate_term(m, theory_term_left(term)),
            translate_term(m, theory_term_right(term))
        ),
        TheoryTermKind::All => theory_all(
            theory_type_image(m, theory_term_type(term)),
            translate_term(m, theory_term_left(term))
        ),
        TheoryTermKind::Exists => theory_exists(
            theory_type_image(m, theory_term_type(term)),
            translate_term(m, theory_term_left(term))
        ),
        _ => term,
    }
}

pub fn ground_term?(TheoryTerm, Nat)

pub proc theory_ground_term(term: TheoryTerm, depth: Nat): (det ground?) {
    ensure rule: ground? iff match theory_term_kind(term) {
        TheoryTermKind::Variable => false,
        TheoryTermKind::Bound => theory_term_index(term) < depth,
        TheoryTermKind::Apply =>
            ground_term?(theory_term_left(term), depth) and ground_term?(theory_term_right(term), depth),
        TheoryTermKind::All | TheoryTermKind::Exists =>
            ground_term?(theory_term_left(term), depth + 1),
        _ => true,
    }
}

pub fn theory_variable_names(TheoryVariables): Set<TheoryName>
pub fn theory_image_present?(TheorySubstitution, TheoryName)
pub fn theory_image_term(TheorySubstitution, TheoryName): TheoryTerm
pub fn substitute_term(TheorySubstitution, TheoryVariables, TheoryTerm): TheoryTerm

pub proc theory_term_substitution(
    s: TheorySubstitution,
    variables: TheoryVariables,
    term: TheoryTerm,
): (det substituted: TheoryTerm) {
    ensure rule: substituted = match theory_term_kind(term) {
        TheoryTermKind::Variable =>
            if theory_term_name(term) in theory_variable_names(variables) and theory_image_present?(s, theory_term_name(term))
            then theory_image_term(s, theory_term_name(term)) else term,
        TheoryTermKind::Apply => theory_apply(
            substitute_term(s, variables, theory_term_left(term)),
            substitute_term(s, variables, theory_term_right(term))
        ),
        TheoryTermKind::All => theory_all(
            theory_term_type(term),
            substitute_term(s, variables, theory_term_left(term))
        ),
        TheoryTermKind::Exists => theory_exists(
            theory_term_type(term),
            substitute_term(s, variables, theory_term_left(term))
        ),
        _ => term,
    }
}

pub fn theory_variables_empty?(TheoryVariables)
pub fn theory_variable_name(TheoryVariables): TheoryName
pub fn theory_variable_type(TheoryVariables): Ty
pub fn theory_variables_rest(TheoryVariables): TheoryVariables
pub fn theory_no_variables(TheoryVariables): TheoryVariables
pub fn theory_add_variable(TheoryName, Ty, TheoryVariables): TheoryVariables
pub fn remaining_variables(TheorySubstitution, TheoryVariables): TheoryVariables
pub fn ground_images?(TheorySubstitution, TheoryVariables)
pub fn translate_variables(TheoryMorphism, TheoryVariables): TheoryVariables

pub proc theory_variable_images(
    m: TheoryMorphism,
    s: TheorySubstitution,
    variables: TheoryVariables,
): (det accepted?, det remaining: TheoryVariables, det translated: TheoryVariables) {
    ensure ground_rule: accepted? iff theory_variables_empty?(variables) or (
        (not theory_image_present?(s, theory_variable_name(variables))
        or ground_term?(theory_image_term(s, theory_variable_name(variables)), 0))
        and ground_images?(s, theory_variables_rest(variables))
        )
    ensure remaining_rule: remaining = if theory_variables_empty?(variables) then theory_no_variables(variables)
        else if theory_image_present?(s, theory_variable_name(variables))
        then remaining_variables(s, theory_variables_rest(variables))
        else theory_add_variable(
            theory_variable_name(variables),
            theory_variable_type(variables),
            remaining_variables(s, theory_variables_rest(variables))
        )
    ensure translation_rule: translated = if theory_variables_empty?(variables) then theory_no_variables(variables)
        else theory_add_variable(
            theory_variable_name(variables),
            theory_type_image(m, theory_variable_type(variables)),
            translate_variables(m, theory_variables_rest(variables))
        )
}

pub fn theory_terms_empty?(TheoryTerms)
pub fn theory_first_term(TheoryTerms): TheoryTerm
pub fn theory_terms_rest(TheoryTerms): TheoryTerms
pub fn theory_no_terms(TheoryTerms): TheoryTerms
pub fn theory_add_term(TheoryTerm, TheoryTerms): TheoryTerms
pub fn translate_terms(TheoryMorphism, TheoryTerms): TheoryTerms
pub fn substitute_terms(TheorySubstitution, TheoryVariables, TheoryTerms): TheoryTerms

pub proc theory_term_list(
    m: TheoryMorphism,
    s: TheorySubstitution,
    variables: TheoryVariables,
    terms: TheoryTerms,
): (det translated: TheoryTerms, det substituted: TheoryTerms) {
    ensure translation_rule: translated = if theory_terms_empty?(terms) then theory_no_terms(terms)
        else theory_add_term(
            translate_term(m, theory_first_term(terms)),
            translate_terms(m, theory_terms_rest(terms))
        )
    ensure substitution_rule: substituted = if theory_terms_empty?(terms) then theory_no_terms(terms)
        else theory_add_term(
            substitute_term(s, variables, theory_first_term(terms)),
            substitute_terms(s, variables, theory_terms_rest(terms))
        )
}

pub fn theory_sentence_role(TheorySentence): SentenceRole
pub fn theory_sentence_variables(TheorySentence): TheoryVariables
pub fn theory_sentence_domain(TheorySentence): TheoryTerm
pub fn theory_sentence_calls(TheorySentence): TheoryTerms
pub fn theory_sentence_claims(TheorySentence): TheoryTerms

pub fn theory_sentence(
    SentenceRole,
    TheoryVariables,
    TheoryTerm,
    TheoryTerms,
    TheoryTerms
): TheorySentence

pub proc theory_translation(m: TheoryMorphism, sentence: TheorySentence): (
    det translated: TheorySentence,
) {
    out translated := theory_sentence(
        theory_sentence_role(sentence),
        translate_variables(m, theory_sentence_variables(sentence)),
        translate_term(m, theory_sentence_domain(sentence)),
        translate_terms(m, theory_sentence_calls(sentence)),
        translate_terms(m, theory_sentence_claims(sentence))
    )
}

pub proc theory_instance(s: TheorySubstitution, sentence: TheorySentence): (
    det accepted?,
    det instance_sentence: TheorySentence,
) {
    out accepted? := ground_images?(s, theory_sentence_variables(sentence))
    out instance_sentence :=
        if not accepted? then sentence else theory_sentence(
            theory_sentence_role(sentence),
            remaining_variables(s, theory_sentence_variables(sentence)),
            substitute_term(
                s,
                theory_sentence_variables(sentence),
                theory_sentence_domain(sentence)
            ),
            substitute_terms(
                s,
                theory_sentence_variables(sentence),
                theory_sentence_calls(sentence)
            ),
            substitute_terms(
                s,
                theory_sentence_variables(sentence),
                theory_sentence_claims(sentence)
            )
        )
}
```

## Generic function instances

A generic function's type arguments give a morphism: every type in its
signature, body and contract is instantiated with the same arguments.
References to functions and clauses have the images resolved at those
arguments. The images are simultaneous, so an image is not translated
again. The front ends encode their type and item references as theory
terms; their other syntax stays literal. Translation then uses the same
operation as any other theory morphism. Ground value arguments use
`theory_instance` separately; a type argument is not a sentence variable.

```fren
pub fn generic_morphism(Seq<Ty>, TheoryMorphism): TheoryMorphism

pub proc generic_type_image(arguments: Seq<Ty>, items: TheoryMorphism, ty: Ty, name: TheoryName): (
    det image: Ty,
    det item_image: TheoryName,
) {
    out image := instantiated(ty, arguments)
    out item_image := theory_item_image(items, name)
}

pub proc generic_translation(arguments: Seq<Ty>, items: TheoryMorphism, sentence: TheorySentence): (
    det instance_sentence: TheorySentence,
) {
    out instance_sentence := theory_sentence(
        theory_sentence_role(sentence),
        translate_variables(
            generic_morphism(arguments, items),
            theory_sentence_variables(sentence)
        ),
        translate_term(
            generic_morphism(arguments, items),
            theory_sentence_domain(sentence)
        ),
        translate_terms(
            generic_morphism(arguments, items),
            theory_sentence_calls(sentence)
        ),
        translate_terms(
            generic_morphism(arguments, items),
            theory_sentence_claims(sentence)
        )
    )
}
```

## Induction by unfolding

[Structural recursion](Recursion.md#induction) proves a claim of a global
expectation by induction on one of its parameters, where its own check is
Inconclusive, and states the candidates, the cases, their hypotheses and
what is reported. This section states what the design of #669 adds to it:
induction on lemma items, unfolding where each case decides the arm, and
earlier lemmas as hypotheses, as Liquid Haskell's proof by logical
evaluation (PLE) does (Vazou et al., POPL 2018).

```text
lemma more_fuel(f: Fuel, e: Expr): when eval(f, e) is Some(v), eval(Fuel::More(f), e) = Some(v)
```

**Proof obligations**

r[module.induction] lang::induction_candidate, lang::induction_hypotheses, lang::induction_verdict
A lemma item is checked by induction where a global expectation with its
parameters, domain and claims would be. The induction's candidates, cases,
hypotheses and verdict are those of [Recursion's induction](Recursion.md#induction), which reports a
pass by induction as any other pass. Its strict expansion is
`module.expansion.induction`.

r[module.induction.unfolding] lang::arm_decided
In each case, an application of a structural recursion unfolds into the arm
of its body that the case decides: the arm that the case's hypotheses
imply is taken, where they rule out every earlier arm. An application whose
arm the case does not decide stays opaque, with its contract.

r[module.induction.fixpoint]
Unfolding repeats at the applications that the unfolded arms bring, until
no application unfolds. Each application unfolds once.

r[module.induction.lemmas]
Each case uses the sentences that the check of its item may use, at the
terms of the case and of its unfoldings (`module.use.instantiated`).

```fren
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

set_option fren.evidence "solver" in
pub proc arm_decided(arms: Arms): (det unfolds?) {
    out unfolds? := decided?(arms)

    expect first_taken: when arms is Arms::Cons(ArmStatus::Taken, _), unfolds?
    expect open_first: when arms is Arms::Cons(ArmStatus::Open, _), not unfolds?
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

## Reports

What a check reports of the axioms it rests on is computed from the same
model, so that a spec of today's forms is shown to get today's messages,
not assumed to.

**Dynamic semantics**

r[implementation.report.unchecked] lang::caveat_premise, lang::caveat_calculation, lang::laws_of_own_interface, lang::translated_caveat_bounds
The consistency of an `assume` item, and of a trait's laws, is not checked
yet. A verdict carries `F0665` where
[`check::law_premise`](../Evidence.md#the-laws-of-a-trait) gives it. Its
input `laws?` is what `lang::caveat_premise` computes from the model: that
the check rests on an axiom whose consistency is not checked, a law, a law
that an implementation leaves trusted or an `assume` item, directly or
through a lemma translated along an implementation that leaves a law
trusted. Its input `asked?` is what `lang::asked_of?` computes from the
model: that the check's item has a vacuity check under those axioms, as a
lemma or a global expectation with `require` clauses or calls has, and as
a trait's expectation with assumptions or calls has today
(`traits.expect.lawful`).
Contracts and the guarantees of calls carry no caveat, as today.

r[implementation.report.today] lang::today_caveats, lang::today_caveat, lang::today_global_caveat
Of a module of today's forms, whose items are interfaces with laws and
expectations, global expectations and items that state no claim,
`lang::caveat_premise` gives `laws?` exactly as today: an expectation of
an interface rests on its laws where it has some, and a global expectation
on none.

> **Note:** So `F0665` is the same as today on every check of such a
> module whose own verdict is unchanged, as `module.expansion` requires.
> Each new own verdict carries `F0665` where `check::law_premise` gives it.

r[implementation.report.vacuity]
Where the axioms cannot hold together, every check that uses them holds
vacuously.

r[implementation.report.lemma-verdict]
A check uses a lemma whatever the lemma's own verdict. Where the check
passes, the pass rests on the check of each lemma and obligation that
`lang::module_rests_on` gives ([Evidence](../Evidence.md#resting-on-checks)).

r[implementation.report.today-laws]
A law of today is reported as today: one that breaks the binding rule
gets no message, and `undecidable` reports laws as they are written.

r[implementation.report.stage-5]
Once stage 5 checks the laws' consistency, the warning that a verdict
rests on laws whose consistency is not checked (`F0665`) gives way to that
check's messages (`F0602`, `F0608`). A check that passes today keeps its
verdict, and where stage 5 finds the laws inconsistent, it reports that at
the laws, as stage 5 states, not at the check.

```fren
-- Whether the implementation at `x` leaves an actual law trusted.
set_option fren.lint.undecidable "allow" in
pub fn trusted_laws_from?(get: fn(Int) -> ModuleItem, x: Int) :=
    exists (j: Int), 0 <= j < get(implemented_from(get, x)).laws and j in get(x).unproved

pub fn trusted_laws?(m: ModuleModel, x: Int) := trusted_laws_from?(|place| item_of(m, place), x)

-- Whether a check that rests on `u` rests on an axiom whose consistency
-- is not checked: `u` is one, or is a lemma translated along an
-- implementation that leaves a law trusted.
set_option fren.lint.undecidable "allow" in
pub fn caveat_source_from?(get: fn(Int) -> ModuleItem, u: ModuleSentence) := match u {
    ModuleSentence::Law(_, _) => true,
    ModuleSentence::TrustedLaw(_, _) => true,
    ModuleSentence::Assumed(_) => true,
    ModuleSentence::Translated(x, _) => trusted_laws_from?(get, x),
    _ => false,
}

pub fn caveat_source?(m: ModuleModel, u: ModuleSentence) :=
    caveat_source_from?(|place| item_of(m, place), u)

-- Whether `n` rests on a sentence of `m` that is a caveat's source, of
-- each kind of sentence in turn. Of laws, only those of the interface whose
-- check it is, and all alike (`lang::laws_of_own_interface`), so law 0
-- stands for them.
set_option fren.lint.undecidable "allow" in
pub fn caveat_by_sentences?(m: ModuleModel, n: ModuleSentence) :=
    let count := item_count(m.items) in
    (item_of(m, check_place(n)).laws > 0 and rests_between?(m, n, ModuleSentence::Law(check_place(n), 0)))
    or (exists (y: Int), 0 <= y < count and (exists (j: Int), 0 <= j < item_of(m, implemented(m, y)).laws
        and rests_between?(m, n, ModuleSentence::TrustedLaw(y, j))))
    or (exists (a: Int), 0 <= a < count and rests_between?(m, n, ModuleSentence::Assumed(a)))
    or (exists (y: Int), 0 <= y < count and (exists (k: Int), 0 <= k < item_of(m, implemented(m, y)).lemmas
        and rests_between?(m, n, ModuleSentence::Translated(y, k)) and caveat_source?(m, ModuleSentence::Translated(y, k))))

-- On valid sentences, which checks use the trusted laws of the
-- implementation at `y`. An obligation uses its own and earlier ones;
-- a translated lemma uses its own implementation's laws.
pub fn trusts_at?(n: ModuleSentence, y: Int) := match n {
    ModuleSentence::Obligation(x, _) => y <= x,
    ModuleSentence::ModuleLemma(p) => y < p,
    ModuleSentence::ModuleGoal(p) => y < p,
    ModuleSentence::Translated(x, _) => y = x,
    _ => false,
}

pub fn owns_laws_from?(get: fn(Int) -> ModuleItem, n: ModuleSentence) := match n {
    ModuleSentence::InterfaceLemma(i, _) => get(i).laws > 0,
    ModuleSentence::InterfaceGoal(i, _) => get(i).laws > 0,
    _ => false,
}

pub fn owns_laws?(m: ModuleModel, n: ModuleSentence) :=
    owns_laws_from?(|place| item_of(m, place), n)

pub fn uses_assumptions?(n: ModuleSentence) :=
    n is ModuleSentence::Obligation(_, _) or n is ModuleSentence::ModuleLemma(_) or n is ModuleSentence::ModuleGoal(_)

-- Factor sentence validity and the trusted-law search out of the
-- relation's cases. A translated source's trusted law is already used
-- directly at every check that uses the translation.
set_option fren.lint.undecidable "allow" in
pub fn rests_on_caveat_from?(get: fn(Int) -> ModuleItem, count: Int, n: ModuleSentence) :=
    sentence_of_from?(get, n) and (owns_laws_from?(get, n)
        or (exists (y: Int), 0 <= y < count and implementation_at_from?(get, y)
        and trusts_at?(n, y) and trusted_laws_from?(get, y))
        or (uses_assumptions?(n) and (exists (a: Int), 0 <= a < count
        and kind_at_from?(get, a, ModuleItemKind::Assume))))

pub fn rests_on_caveat?(m: ModuleModel, n: ModuleSentence) :=
    rests_on_caveat_from?(|place| item_of(m, place), item_count(m.items), n)

-- Check the factored calculation against the relation on every model,
-- including malformed counts and out-of-range entries in `unproved`. Split
-- by every sentence constructor so the solver simplifies each relation case
-- before searching for a counterexample; x and k remain arbitrary.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect caveat_calculation(m: ModuleModel, x: Int, k: Int) {
    expect law: rests_on_caveat?(m, ModuleSentence::Law(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::Law(x, k))
    expect interface_lemma: rests_on_caveat?(m, ModuleSentence::InterfaceLemma(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::InterfaceLemma(x, k))
    expect interface_goal: rests_on_caveat?(m, ModuleSentence::InterfaceGoal(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::InterfaceGoal(x, k))
    expect obligation: rests_on_caveat?(m, ModuleSentence::Obligation(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::Obligation(x, k))
    expect trusted_law: rests_on_caveat?(m, ModuleSentence::TrustedLaw(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::TrustedLaw(x, k))
    expect translated: rests_on_caveat?(m, ModuleSentence::Translated(x, k)) iff
        caveat_by_sentences?(m, ModuleSentence::Translated(x, k))
    expect module_lemma: rests_on_caveat?(m, ModuleSentence::ModuleLemma(x)) iff
        caveat_by_sentences?(m, ModuleSentence::ModuleLemma(x))
    expect module_goal: rests_on_caveat?(m, ModuleSentence::ModuleGoal(x)) iff
        caveat_by_sentences?(m, ModuleSentence::ModuleGoal(x))
    expect assumed: rests_on_caveat?(m, ModuleSentence::Assumed(x)) iff
        caveat_by_sentences?(m, ModuleSentence::Assumed(x))
}

-- Only the checks of an interface rest on its laws, and on each of them
-- where on one.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect laws_of_own_interface(m: ModuleModel, n: ModuleSentence, i: Int, j: Int) {
    expect own: not rests_case?(m, n, ModuleSentence::Law(i, j)) or i = check_place(n)
    expect alike: rests_case?(m, n, ModuleSentence::Law(i, j)) = rests_case?(m, n, ModuleSentence::Law(i, 0))
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc caveat_premise(m: ModuleModel, n: ModuleSentence): (det laws?) {
    out laws? := rests_on_caveat?(m, n)

    expect axioms_have_none: when axiom?(n), not laws?
}

-- Keep the fixture linked so enumeration needs no unspecified value for
-- an out-of-range sequence index. Its only inputs are four Booleans.
pub fn caveat_bounds_items(
    include_negative?,
    include_valid?,
    include_end?,
    include_large?
): ModuleItems :=
    let unproved: Set<Int> := (if include_negative? then {-1} else {})
    union (if include_valid? then {0} else {}) union (if include_end? then {1} else {})
    union (if include_large? then {5} else {}) in
    ModuleItems::Cons(
        MONOID,
        ModuleItems::Cons(
            { SUM with unproved },
            ModuleItems::Cons(MODULE_LEMMA, ModuleItems::Nil)
        )
    )

-- Prove all 16 combinations of a negative number, valid law 0, the upper
-- bound 1 and a larger number 5, for a one-law interface. Out-of-range
-- entries must not make either the translation a caveat's source or its
-- consumer carry F0665, including when mixed with the valid law.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "enumerated" in
expect translated_caveat_bounds(include_negative?, include_valid?, include_end?, include_large?) {
    expect source_bounded: caveat_source_from?(
        |place| linked_item_at(
            caveat_bounds_items(
                include_negative?,
                include_valid?,
                include_end?,
                include_large?
            ),
            place
        ),
        ModuleSentence::Translated(1, 0)
    ) iff include_valid?
    -- This is the expression that `caveat_premise` defines `laws?` with.
    expect report_bounded: rests_on_caveat_from?(
        |place| linked_item_at(
            caveat_bounds_items(
                include_negative?,
                include_valid?,
                include_end?,
                include_large?
            ),
            place
        ),
        linked_item_count(
            caveat_bounds_items(
                include_negative?,
                include_valid?,
                include_end?,
                include_large?
            )
        ),
        ModuleSentence::ModuleLemma(2)
    ) iff include_valid?
}

-- A module of today's forms: interfaces without lemmas, global
-- expectations, and items that state no claim.
set_option fren.lint.undecidable "allow" in
pub fn today_forms?(m: ModuleModel) :=
    forall (i: Int), when 0 <= i < item_count(m.items),
    item_of(m, i).kind in {
        ModuleItemKind::Interface,
        ModuleItemKind::Goal,
        ModuleItemKind::Other,
    }
    and item_of(m, i).lemmas = 0

-- `Store`, a trait with one law and one expectation, and a global
-- expectation after it.
pub const STORE: ModuleModel := ModuleModel {
    items := [
        ModuleItem {
            kind := ModuleItemKind::Interface,
            laws := 1,
            lemmas := 0,
            goals := 1,
            implements := -1,
            unproved := {},
            asked? := false,
            asked_lemmas := {},
            asked_goals := {},
        },
        ModuleItem {
            kind := ModuleItemKind::Goal,
            laws := 0,
            lemmas := 0,
            goals := 0,
            implements := -1,
            unproved := {},
            asked? := false,
            asked_lemmas := {},
            asked_goals := {},
        },
    ],
}

-- Its expectation rests on its law, as `F0665` of `Store::read_back` says
-- today (`test/cli/results/f0665_unchecked_laws.expected`).
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect today_caveat() {
    call r := caveat_premise(STORE, ModuleSentence::InterfaceGoal(0, 0))
    expect laws: r.laws?
}

-- The global expectation rests on none.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
expect today_global_caveat() {
    call r := caveat_premise(STORE, ModuleSentence::ModuleGoal(1))
    expect none: not r.laws?
}

-- An interface's expectation rests on a law of its interface where it has
-- one, and on nothing else that carries a caveat, in every module of
-- today's forms.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect today_caveats(m: ModuleModel, n: ModuleSentence) {
    call r := caveat_premise(m, n)
    expect interface_goals_on_laws: not today_forms?(m) or not n is ModuleSentence::InterfaceGoal(_, _)
        or not sentence_of?(m, n) or not r.laws? or item_of(m, check_place(n)).laws > 0
    expect first_law: not n is ModuleSentence::InterfaceGoal(_, _) or not sentence_of?(m, n)
        or item_of(m, check_place(n)).laws <= 0 or rests_between?(m, n, ModuleSentence::Law(check_place(n), 0))
    expect interface_goals_with_laws: not n is ModuleSentence::InterfaceGoal(_, _)
        or not sentence_of?(m, n) or item_of(m, check_place(n)).laws <= 0 or r.laws?
    expect global_goals: not today_forms?(m) or not n is ModuleSentence::ModuleGoal(_) or not r.laws?
}
```

## Small modules

`lang::small_modules_acyclic` checks `implementation.rests-on.acyclic`
without the ranking. It builds every module of two interfaces, each with
two laws, two lemmas and an expectation, two implementations, each of
either interface and total or leaving its second law trusted, and three
lemma items, in every order of those seven items. Of each, it removes the
sentences that rest on no sentence left, until none is left, which a
cycle would stop. Orders that differ only in which of two interfaces, two
implementations or three lemmas comes first give the same modules but for
names, so it takes one order of each kind of item: 210 orders and 16
modules of each, 3,360 modules. Its cases are the 840 choices of the
first four items with the 16 choices of the implementations, 13,440
cases, each of six orders, and the chapter's check enumerates them all.

```fren
-- An item of a small module.
pub enum SmallItem { I1, I2, X1, X2, T1, T2, T3 }

pub enum SmallItems { Nil, Cons(SmallItem, SmallItems) }

pub enum SmallOrders { Nil, Cons(SmallItems, SmallOrders) }

pub fn place_in(order: SmallItems, s: SmallItem, k: Int): Int := match order {
    SmallItems::Nil => -1,
    SmallItems::Cons(x, rest) => if x = s then k else place_in(rest, s, k + 1),
}

-- The choices of a small module beyond its order: the interface that
-- each implementation implements, and whether it leaves its second law
-- trusted.
pub struct SmallChoice { x1_second?, x2_second?, x1_partial?, x2_partial? }

pub const SMALL_INTERFACE: ModuleItem := ModuleItem {
    kind := ModuleItemKind::Interface,
    laws := 2,
    lemmas := 2,
    goals := 1,
    implements := -1,
    unproved := {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

pub fn implementation_item(implements: Int, partial?): ModuleItem := ModuleItem {
    kind := ModuleItemKind::Implementation,
    laws := 0,
    lemmas := 0,
    goals := 0,
    implements,
    unproved := if partial? then {1} else {},
    asked? := false,
    asked_lemmas := {},
    asked_goals := {},
}

pub fn small_item(order: SmallItems, choice: SmallChoice, s: SmallItem): ModuleItem := match s {
    SmallItem::I1 => SMALL_INTERFACE,
    SmallItem::I2 => SMALL_INTERFACE,
    SmallItem::X1 => implementation_item(
        place_in(
            order,
            if choice.x1_second? then SmallItem::I2 else SmallItem::I1,
            0
        ),
        choice.x1_partial?
    ),
    SmallItem::X2 => implementation_item(
        place_in(
            order,
            if choice.x2_second? then SmallItem::I2 else SmallItem::I1,
            0
        ),
        choice.x2_partial?
    ),
    _ => MODULE_LEMMA,
}

pub fn small_items(order: SmallItems, choice: SmallChoice, rest: SmallItems): ModuleItems :=
    match rest {
        SmallItems::Nil => ModuleItems::Nil,
        SmallItems::Cons(s, more) => ModuleItems::Cons(
            small_item(order, choice, s),
            small_items(order, choice, more)
        ),
    }

pub enum ModuleSentences { Nil, Cons(ModuleSentence, ModuleSentences) }

pub fn append_sentences(a: ModuleSentences, b: ModuleSentences): ModuleSentences := match a {
    ModuleSentences::Nil => b,
    ModuleSentences::Cons(s, rest) => ModuleSentences::Cons(s, append_sentences(rest, b)),
}

pub fn interface_sentences(k: Int): ModuleSentences := ModuleSentences::Cons(
    ModuleSentence::Law(k, 0),
    ModuleSentences::Cons(
        ModuleSentence::Law(k, 1),
        ModuleSentences::Cons(
            ModuleSentence::InterfaceLemma(k, 0),
            ModuleSentences::Cons(
                ModuleSentence::InterfaceLemma(k, 1),
                ModuleSentences::Cons(ModuleSentence::InterfaceGoal(k, 0), ModuleSentences::Nil)
            )
        )
    )
)

pub fn implementation_sentences(k: Int): ModuleSentences := ModuleSentences::Cons(
    ModuleSentence::Obligation(k, 0),
    ModuleSentences::Cons(
        ModuleSentence::Obligation(k, 1),
        ModuleSentences::Cons(
            ModuleSentence::TrustedLaw(k, 1),
            ModuleSentences::Cons(
                ModuleSentence::Translated(k, 0),
                ModuleSentences::Cons(ModuleSentence::Translated(k, 1), ModuleSentences::Nil)
            )
        )
    )
)

-- Every sentence that the item at `k` may declare, of any choice.
pub fn sentences_at(s: SmallItem, k: Int): ModuleSentences := match s {
    SmallItem::I1 => interface_sentences(k),
    SmallItem::I2 => interface_sentences(k),
    SmallItem::X1 => implementation_sentences(k),
    SmallItem::X2 => implementation_sentences(k),
    _ => ModuleSentences::Cons(ModuleSentence::ModuleLemma(k), ModuleSentences::Nil),
}

pub fn candidates_from(order: SmallItems, k: Int): ModuleSentences := match order {
    SmallItems::Nil => ModuleSentences::Nil,
    SmallItems::Cons(s, rest) => append_sentences(sentences_at(s, k), candidates_from(rest, k + 1)),
}

pub fn present(m: ModuleItems, ns: ModuleSentences): ModuleSentences := match ns {
    ModuleSentences::Nil => ModuleSentences::Nil,
    ModuleSentences::Cons(n, rest) =>
        if sentence_of_from?(|i| linked_item_at(m, i), n) then ModuleSentences::Cons(n, present(m, rest)) else present(m, rest),
}

pub fn rests_on_some?(m: ModuleItems, n: ModuleSentence, us: ModuleSentences) := match us {
    ModuleSentences::Nil => false,
    ModuleSentences::Cons(u, rest) =>
        rests_case_from?(|i| linked_item_at(m, i), n, u) or rests_on_some?(m, n, rest),
}

-- The sentences of `ns` that rest on a sentence of `remaining`.
pub fn still_resting(
    m: ModuleItems,
    ns: ModuleSentences,
    remaining: ModuleSentences
): ModuleSentences := match ns {
    ModuleSentences::Nil => ModuleSentences::Nil,
    ModuleSentences::Cons(n, rest) =>
        if rests_on_some?(m, n, remaining) then ModuleSentences::Cons(n, still_resting(m, rest, remaining))
        else still_resting(m, rest, remaining),
}

-- How many rounds of removal are left.
pub enum Rounds { Out, More(Rounds) }

pub fn removed_by?(m: ModuleItems, remaining: ModuleSentences, rounds: Rounds) := match remaining {
    ModuleSentences::Nil => true,
    ModuleSentences::Cons(_, _) => match rounds {
        Rounds::Out => false,
        Rounds::More(fewer) => removed_by?(m, still_resting(m, remaining, remaining), fewer),
    },
}

-- One more round than the 23 candidate sentences of a small module.
pub const ENOUGH_ROUNDS: Rounds := Rounds::More(
    Rounds::More(
        Rounds::More(
            Rounds::More(
                Rounds::More(
                    Rounds::More(
                        Rounds::More(
                            Rounds::More(
                                Rounds::More(
                                    Rounds::More(
                                        Rounds::More(
                                            Rounds::More(
                                                Rounds::More(
                                                    Rounds::More(
                                                        Rounds::More(
                                                            Rounds::More(
                                                                Rounds::More(
                                                                    Rounds::More(
                                                                        Rounds::More(
                                                                            Rounds::More(
                                                                                Rounds::More(
                                                                                    Rounds::More(
                                                                                        Rounds::More(Rounds::More(Rounds::Out))
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)

pub fn acyclic_small?(order: SmallItems, choice: SmallChoice) :=
    let m := small_items(order, choice, order) in
    removed_by?(m, present(m, candidates_from(order, 0)), ENOUGH_ROUNDS)

-- One order of each class: items of a kind in the order of their names.
pub fn representative?(order: SmallItems) :=
    place_in(order, SmallItem::I1, 0) < place_in(order, SmallItem::I2, 0)
    and place_in(order, SmallItem::X1, 0) < place_in(order, SmallItem::X2, 0)
    and place_in(order, SmallItem::T1, 0) < place_in(order, SmallItem::T2, 0) < place_in(order, SmallItem::T3, 0)

pub fn prefix_each(x: SmallItem, os: SmallOrders): SmallOrders := match os {
    SmallOrders::Nil => SmallOrders::Nil,
    SmallOrders::Cons(o, rest) => SmallOrders::Cons(SmallItems::Cons(x, o), prefix_each(x, rest)),
}

pub fn insertions(s: SmallItem, order: SmallItems): SmallOrders := match order {
    SmallItems::Nil => SmallOrders::Cons(SmallItems::Cons(s, SmallItems::Nil), SmallOrders::Nil),
    SmallItems::Cons(x, rest) => SmallOrders::Cons(
        SmallItems::Cons(s, order),
        prefix_each(x, insertions(s, rest))
    ),
}

pub fn append_orders(a: SmallOrders, b: SmallOrders): SmallOrders := match a {
    SmallOrders::Nil => b,
    SmallOrders::Cons(o, rest) => SmallOrders::Cons(o, append_orders(rest, b)),
}

pub fn insert_each(s: SmallItem, os: SmallOrders): SmallOrders := match os {
    SmallOrders::Nil => SmallOrders::Nil,
    SmallOrders::Cons(o, rest) => append_orders(insertions(s, o), insert_each(s, rest)),
}

pub fn orders(items: SmallItems): SmallOrders := match items {
    SmallItems::Nil => SmallOrders::Cons(SmallItems::Nil, SmallOrders::Nil),
    SmallItems::Cons(s, rest) => insert_each(s, orders(rest)),
}

pub fn without(s: SmallItem, items: SmallItems): SmallItems := match items {
    SmallItems::Nil => SmallItems::Nil,
    SmallItems::Cons(x, rest) => if x = s then rest else SmallItems::Cons(x, without(s, rest)),
}

pub fn orders_acyclic?(os: SmallOrders, choice: SmallChoice) := match os {
    SmallOrders::Nil => true,
    SmallOrders::Cons(o, rest) =>
        (not representative?(o) or acyclic_small?(o, choice)) and orders_acyclic?(rest, choice),
}

pub const SMALL_ITEMS: SmallItems := SmallItems::Cons(
    SmallItem::I1,
    SmallItems::Cons(
        SmallItem::I2,
        SmallItems::Cons(
            SmallItem::X1,
            SmallItems::Cons(
                SmallItem::X2,
                SmallItems::Cons(
                    SmallItem::T1,
                    SmallItems::Cons(
                        SmallItem::T2,
                        SmallItems::Cons(SmallItem::T3, SmallItems::Nil)
                    )
                )
            )
        )
    )
)

-- Every small module whose first four items are `first` to `fourth`, of
-- the choice `x1_second?` to `x2_partial?`, so that each case is six
-- orders, and enumeration still sees every order and choice.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "enumerated" in
expect small_modules_acyclic(
    first: SmallItem,
    second: SmallItem,
    third: SmallItem,
    fourth: SmallItem,
    x1_second?,
    x2_second?,
    x1_partial?,
    x2_partial?,
) {
    assume distinct: first != second and first != third and first != fourth
        and second != third and second != fourth and third != fourth
    expect acyclic: orders_acyclic?(
        prefix_each(
            first,
            prefix_each(
                second,
                prefix_each(
                    third,
                    prefix_each(
                        fourth,
                        orders(
                            without(
                                fourth,
                                without(third, without(second, without(first, SMALL_ITEMS)))
                            )
                        )
                    )
                )
            )
        ),
        SmallChoice {
            x1_second?,
            x2_second?,
            x1_partial?,
            x2_partial?,
        }
    )
}
```

> **Rationale:** The prior art: ACL2's `encapsulate` and functional
> instantiation; Specware's morphisms with proof obligations; Isabelle's
> locales and their interpretations; and Lean's and Coq's type classes,
> whose instances are resolved where they are in scope.

The Lean-hosted front end checks this chapter's items by name, since a
`#fren_check` without a path would check every earlier chapter again:

```fren
#fren_check theory_term_translation
#fren_check theory_ground_term
#fren_check theory_term_substitution
#fren_check theory_variable_images
#fren_check theory_term_list
#fren_check theory_translation
#fren_check theory_instance
#fren_check generic_type_image
#fren_check generic_translation
#fren_check module_sentence
#fren_check module_rests_on
#fren_check rests_on_ranked
#fren_check translated_grounded
#fren_check total_obligation
#fren_check partial_trusted
#fren_check partial_unproved
#fren_check obligation_from_earlier_lemma
#fren_check lemma_before_implementation
#fren_check translation_on_obligation
#fren_check own_translated_lemma
#fren_check axioms_used_anywhere
#fren_check dispatch
#fren_check dispatch_ambiguous
#fren_check dispatch_named
#fren_check dispatch_earlier
#fren_check sentence_instantiation
#fren_check get_put_instantiation
#fren_check nested_anchor
#fren_check unbound_variable
#fren_check listed_variable
#fren_check outside_variable
#fren_check ensure_clause
#fren_check contract_without_result
#fren_check sentence_use
#fren_check made_used
#fren_check made_unused
#fren_check axioms_anywhere
#fren_check laws_anywhere
#fren_check unbound_law_quantified
#fren_check get_put_kept
#fren_check no_subject_used
#fren_check lemmas_ranked
#fren_check defined_contract_not_own
#fren_check defined_contract_later
#fren_check contract_without_result_used
#fren_check arm_decided
#fren_check laws_of_own_interface
#fren_check caveat_calculation
#fren_check caveat_premise
#fren_check translated_caveat_bounds
#fren_check today_caveat
#fren_check today_global_caveat
#fren_check today_caveats
#fren_check small_modules_acyclic
```

### Ground matching equations

These equations refine `module.instance.matching` and the normalization
of [matching terms](../Evidence.md#matching-terms-and-finite-closure) over
the shared theory syntax. Extraction supplies resolved identities, lexical
definition environments, declaration order, term types and finite listed
values. The core computes applications, subjects, anchors, binding and
substitutions. Definitions have no escaping binder indices: sentence
parameters and free query locals have their own resolved names. Applied
item heads stay opaque; only query aliases and item constants are references
to definitions. Builtins, literals, types and bound indices retain syntax.

A match extends one simultaneous substitution and never captures a query
binder. Every anchor and outer call must match at once. Listed variables
without images take their values after matching; unused variables and
outside-only unlisted variables retain their quantifiers. The recursive
calls below are the same operation at immediate subterms or list tails.
`Fren.Core.GroundMatching` implements these equations. Neither front end
uses the engine yet; the following section constructs the finite candidate
universe and closes it. Claim item integration remains a follow-up of #758.

```fren
pub type GroundContext
pub type GroundImages
pub type GroundDefinitions
pub type GroundResult

pub fn ground_type_present?(GroundContext, TheoryTerm)
pub fn ground_type(GroundContext, TheoryTerm): Ty
pub fn ground_image_substitution(GroundImages): TheorySubstitution

pub fn ground_image_present?(images: GroundImages, name: TheoryName): (present?) {
    ensure conversion: present? iff theory_image_present?(ground_image_substitution(images), name)
}

pub fn ground_image(images: GroundImages, name: TheoryName): (value: TheoryTerm) {
    ensure conversion: value = theory_image_term(ground_image_substitution(images), name)
}

pub fn ground_extend(GroundImages, TheoryName, TheoryTerm): GroundImages
pub fn ground_parameter_present?(TheoryVariables, TheoryName)
pub fn ground_parameter(TheoryVariables, TheoryName): Ty
pub fn ground_success(GroundImages): GroundResult
pub fn ground_failure(GroundImages): GroundResult
pub fn ground_succeeded?(GroundResult)
pub fn ground_result_images(GroundResult): GroundImages

pub fn ground_match(
    GroundContext,
    TheoryVariables,
    TheoryTerm,
    TheoryTerm,
    GroundImages
): GroundResult

pub proc ground_match_step(
    ctx: GroundContext,
    variables: TheoryVariables,
    pattern: TheoryTerm,
    target: TheoryTerm,
    images: GroundImages,
): (det result: GroundResult) {
    ensure rule: result = match theory_term_kind(pattern) {
        TheoryTermKind::Variable =>
            if not ground_parameter_present?(variables, theory_term_name(pattern))
            then if pattern = target then ground_success(images) else ground_failure(images)
            else if not ground_term?(target, 0) or not ground_type_present?(ctx, target)
            or ground_type(ctx, target) != ground_parameter(variables, theory_term_name(pattern))
            then ground_failure(images)
            else if ground_image_present?(images, theory_term_name(pattern))
            then if ground_image(images, theory_term_name(pattern)) = target then ground_success(images) else ground_failure(images)
            else ground_success(ground_extend(images, theory_term_name(pattern), target)),
        TheoryTermKind::Apply =>
            if theory_term_kind(target) != TheoryTermKind::Apply then ground_failure(images)
            else if ground_succeeded?(
                ground_match(
                    ctx,
                    variables,
                    theory_term_left(pattern),
                    theory_term_left(target),
                    images
                )
            )
            then ground_match(
                ctx,
                variables,
                theory_term_right(pattern),
                theory_term_right(target),
                ground_result_images(
                    ground_match(
                        ctx,
                        variables,
                        theory_term_left(pattern),
                        theory_term_left(target),
                        images
                    )
                )
            )
            else ground_failure(images),
        TheoryTermKind::All =>
            if theory_term_kind(target) = TheoryTermKind::All and theory_term_type(pattern) = theory_term_type(target)
            then ground_match(
                ctx,
                variables,
                theory_term_left(pattern),
                theory_term_left(target),
                images
            )
            else ground_failure(images),
        TheoryTermKind::Exists =>
            if theory_term_kind(target) = TheoryTermKind::Exists and theory_term_type(pattern) = theory_term_type(target)
            then ground_match(
                ctx,
                variables,
                theory_term_left(pattern),
                theory_term_left(target),
                images
            )
            else ground_failure(images),
        _ => if pattern = target then ground_success(images) else ground_failure(images),
    }
}

pub proc ground_parameter_step(variables: TheoryVariables, name: TheoryName): (
    det present?,
    det result: Ty,
) {
    ensure presence: present? iff name in theory_variable_names(variables)
    ensure rule: result = if theory_variables_empty?(variables) then theory_variable_type(variables)
        else if theory_variable_name(variables) = name then theory_variable_type(variables)
        else ground_parameter(theory_variables_rest(variables), name)
}

pub proc ground_extension_step(
    images: GroundImages,
    name: TheoryName,
    value: TheoryTerm,
    queried: TheoryName,
): (det present?, det result: TheoryTerm) {
    -- The matcher extends only a name without an existing image.
    require fresh: not ground_image_present?(images, name)
    ensure presence: present? iff queried = name or ground_image_present?(images, queried)
    ensure lookup: result = if queried = name then value else ground_image(images, queried)
}

pub fn ground_definitions_empty?(GroundDefinitions)
pub fn ground_definition_name(GroundDefinitions): TheoryTerm
pub fn ground_definition_value(GroundDefinitions): TheoryTerm
pub fn ground_definitions_rest(GroundDefinitions): GroundDefinitions
pub fn ground_add_definition(TheoryTerm, TheoryTerm, GroundDefinitions): GroundDefinitions
pub fn ground_lookup(GroundDefinitions, TheoryTerm): TheoryTerm
pub fn ground_normalize(GroundDefinitions, TheoryTerm): TheoryTerm
pub fn ground_normalize_definitions(GroundDefinitions): GroundDefinitions

pub proc ground_normalization(defs: GroundDefinitions, term: TheoryTerm, other: TheoryTerm): (
    det lookup_value: TheoryTerm,
    det normalized: TheoryTerm,
    det normalized_definitions: GroundDefinitions,
    det same?,
) {
    ensure lookup_rule: lookup_value = if ground_definitions_empty?(defs) then term
        else if ground_definition_name(defs) = term then ground_definition_value(defs)
        else ground_lookup(ground_definitions_rest(defs), term)
    ensure term_rule: normalized = match theory_term_kind(term) {
        TheoryTermKind::Apply => theory_apply(
            if theory_term_kind(theory_term_left(term)) = TheoryTermKind::Item then theory_term_left(term)
                else ground_normalize(defs, theory_term_left(term)),
            ground_normalize(defs, theory_term_right(term))
        ),
        TheoryTermKind::All => theory_all(
            theory_term_type(term),
            ground_normalize(defs, theory_term_left(term))
        ),
        TheoryTermKind::Exists => theory_exists(
            theory_term_type(term),
            ground_normalize(defs, theory_term_left(term))
        ),
        TheoryTermKind::Query | TheoryTermKind::Item => ground_lookup(defs, term),
        _ => term,
    }
    ensure definitions_rule: normalized_definitions = if ground_definitions_empty?(defs) then defs
        else ground_add_definition(
            ground_definition_name(defs),
            ground_normalize(
                ground_normalize_definitions(ground_definitions_rest(defs)),
                ground_definition_value(defs)
            ),
            ground_normalize_definitions(ground_definitions_rest(defs))
        )
    ensure equality: same? iff ground_normalize(ground_normalize_definitions(defs), term)
        = ground_normalize(ground_normalize_definitions(defs), other)
}

pub type GroundOrder
pub type GroundSubject

pub fn ground_order_empty?(GroundOrder)
pub fn ground_order_first(GroundOrder): TheoryName
pub fn ground_order_rest(GroundOrder): GroundOrder
pub fn ground_no_subject(GroundOrder): GroundSubject
pub fn ground_named(TheoryName): GroundSubject
pub fn ground_subject_present?(GroundSubject)
pub fn ground_subject_name(GroundSubject): TheoryName
pub fn ground_subject(GroundOrder, TheoryTerms): GroundSubject
pub fn ground_uses?(TheoryTerms, TheoryName)
pub fn ground_items(GroundContext): Set<TheoryName>
pub fn ground_head(TheoryTerm): TheoryTerm
pub fn ground_args(TheoryTerm): TheoryTerms
pub fn ground_append(TheoryTerms, TheoryTerms): TheoryTerms
pub fn ground_no_terms(TheoryTerm): TheoryTerms
pub fn ground_outer?(TheoryTerm, Nat)
pub fn ground_mentions?(TheoryName, TheoryTerm)
pub fn ground_vars_mention?(TheoryVariables, TheoryTerm)
pub fn ground_compound_arg?(TheoryVariables, TheoryTerm)
pub fn ground_apps(GroundContext, TheoryTerm): TheoryTerms
pub fn ground_argument_apps(GroundContext, TheoryTerm): TheoryTerms

pub proc ground_shape_step(
    ctx: GroundContext,
    term: TheoryTerm,
    variables: TheoryVariables,
    name: TheoryName,
    depth: Nat,
): (
    det head: TheoryTerm,
    det args: TheoryTerms,
    det outer?,
    det mentions?,
    det compound?,
    det apps: TheoryTerms,
    det argument_apps: TheoryTerms,
) {
    ensure head_rule: head = if theory_term_kind(term) = TheoryTermKind::Apply
        then ground_head(theory_term_left(term)) else term
    ensure args_rule: args = if theory_term_kind(term) = TheoryTermKind::Apply
        then ground_append(
            ground_args(theory_term_left(term)),
            theory_add_term(theory_term_right(term), ground_no_terms(term))
        )
        else ground_no_terms(term)
    ensure outer_rule: outer? iff match theory_term_kind(term) {
        TheoryTermKind::Bound => theory_term_index(term) < depth,
        TheoryTermKind::Apply =>
            ground_outer?(theory_term_left(term), depth) and ground_outer?(theory_term_right(term), depth),
        TheoryTermKind::All | TheoryTermKind::Exists =>
            ground_outer?(theory_term_left(term), depth + 1),
        _ => true,
    }
    ensure mentions_rule: mentions? iff match theory_term_kind(term) {
        TheoryTermKind::Variable => theory_term_name(term) = name,
        TheoryTermKind::Apply =>
            ground_mentions?(name, theory_term_left(term)) or ground_mentions?(name, theory_term_right(term)),
        TheoryTermKind::All | TheoryTermKind::Exists =>
            ground_mentions?(name, theory_term_left(term)),
        _ => false,
    }
    ensure compound_rule: compound? iff theory_term_kind(term) != TheoryTermKind::Variable and ground_vars_mention?(variables, term)
    ensure apps_rule: apps = match theory_term_kind(term) {
        TheoryTermKind::Apply => ground_append(
            if theory_term_kind(ground_head(term)) = TheoryTermKind::Item and theory_term_name(ground_head(term)) in ground_items(ctx)
                then theory_add_term(term, ground_no_terms(term)) else ground_no_terms(term),
            ground_append(
                ground_argument_apps(ctx, theory_term_left(term)),
                ground_apps(ctx, theory_term_right(term))
            )
        ),
        TheoryTermKind::All | TheoryTermKind::Exists => ground_apps(ctx, theory_term_left(term)),
        _ => ground_no_terms(term),
    }
    ensure arguments_rule: argument_apps = if theory_term_kind(term) = TheoryTermKind::Apply
        then ground_append(
            ground_argument_apps(ctx, theory_term_left(term)),
            ground_apps(ctx, theory_term_right(term))
        )
        else ground_no_terms(term)
}

pub proc ground_subject_step(order: GroundOrder, apps: TheoryTerms, name: TheoryName): (
    det subject: GroundSubject,
    det subject_used?,
) {
    ensure subject_rule: subject = if ground_order_empty?(order) then ground_no_subject(order)
        else if ground_subject_present?(ground_subject(ground_order_rest(order), apps))
        then ground_subject(ground_order_rest(order), apps)
        else if ground_uses?(apps, ground_order_first(order)) then ground_named(ground_order_first(order))
        else ground_no_subject(order)
    ensure uses_rule: subject_used? iff not theory_terms_empty?(apps) and (
        (theory_term_kind(ground_head(theory_first_term(apps))) = TheoryTermKind::Item
        and theory_term_name(ground_head(theory_first_term(apps))) = name)
        or ground_uses?(theory_terms_rest(apps), name)
        )
}

pub fn ground_subject_apps(GroundSubject, TheoryTerms): TheoryTerms
pub fn ground_compound_apps(TheoryVariables, TheoryTerms): TheoryTerms
pub fn ground_anchors(TheoryVariables, TheoryTerms): TheoryTerms
pub fn ground_any_mentions?(TheoryName, TheoryTerms)
pub fn ground_listed?(GroundContext, Ty)
pub fn ground_binding?(GroundContext, TheoryTerms, TheoryTerms, TheoryVariables)

pub fn ground_any_compound?(TheoryVariables, TheoryTerms)

pub proc ground_selection_step(
    subject: GroundSubject,
    apps: TheoryTerms,
    variables: TheoryVariables,
    name: TheoryName,
): (
    det subject_apps: TheoryTerms,
    det compounds: TheoryTerms,
    det anchors: TheoryTerms,
    det mentioned?,
    det compound_argument?,
) {
    ensure subjects_rule: subject_apps = if theory_terms_empty?(apps) then apps else
        if ground_subject_present?(subject)
        and theory_term_kind(ground_head(theory_first_term(apps))) = TheoryTermKind::Item
        and theory_term_name(ground_head(theory_first_term(apps))) = ground_subject_name(subject)
        and ground_outer?(theory_first_term(apps), 0)
        then theory_add_term(
            theory_first_term(apps),
            ground_subject_apps(subject, theory_terms_rest(apps))
        )
        else ground_subject_apps(subject, theory_terms_rest(apps))
    ensure compounds_rule: compounds = if theory_terms_empty?(apps) then apps else
        if ground_any_compound?(variables, ground_args(theory_first_term(apps)))
        then theory_add_term(
            theory_first_term(apps),
            ground_compound_apps(variables, theory_terms_rest(apps))
        )
        else ground_compound_apps(variables, theory_terms_rest(apps))
    ensure anchors_rule: anchors = if theory_terms_empty?(ground_compound_apps(variables, apps))
        then apps else ground_compound_apps(variables, apps)
    ensure mentions_rule: mentioned? iff not theory_terms_empty?(apps) and (
        ground_mentions?(name, theory_first_term(apps)) or ground_any_mentions?(name, theory_terms_rest(apps))
        )
    ensure compound_arguments_rule: compound_argument? iff not theory_terms_empty?(apps) and (
        ground_compound_arg?(variables, theory_first_term(apps)) or ground_any_compound?(variables, theory_terms_rest(apps))
        )
}

pub proc ground_variables_step(
    ctx: GroundContext,
    variables: TheoryVariables,
    term: TheoryTerm,
    apps: TheoryTerms,
    matched: TheoryTerms,
): (det mentions?, det binding?) {
    ensure mentions_rule: mentions? iff not theory_variables_empty?(variables) and (
        ground_mentions?(theory_variable_name(variables), term) or ground_vars_mention?(theory_variables_rest(variables), term)
        )
    ensure binding_rule: binding? iff theory_variables_empty?(variables) or (
        (ground_listed?(ctx, theory_variable_type(variables))
        or not ground_any_mentions?(theory_variable_name(variables), apps)
        or ground_any_mentions?(theory_variable_name(variables), matched))
        and ground_binding?(ctx, apps, matched, theory_variables_rest(variables))
        )
}

pub type GroundMatches
pub fn ground_matches_empty?(GroundMatches)
pub fn ground_matches_first(GroundMatches): GroundImages
pub fn ground_matches_rest(GroundMatches): GroundMatches
pub fn ground_no_matches(TheoryVariables): GroundMatches
pub fn ground_add_match(GroundImages, GroundMatches): GroundMatches
pub fn ground_append_matches(GroundMatches, GroundMatches): GroundMatches
pub fn ground_unique_matches(GroundMatches): GroundMatches

pub fn ground_targets(
    GroundContext,
    TheoryVariables,
    TheoryTerm,
    TheoryTerms,
    GroundImages
): GroundMatches

pub fn ground_many(
    GroundContext,
    TheoryVariables,
    TheoryTerm,
    TheoryTerms,
    GroundMatches
): GroundMatches

pub fn ground_join(
    GroundContext,
    TheoryVariables,
    TheoryTerms,
    TheoryTerms,
    GroundMatches
): GroundMatches

pub proc ground_join_step(
    ctx: GroundContext,
    variables: TheoryVariables,
    pattern: TheoryTerm,
    patterns: TheoryTerms,
    targets: TheoryTerms,
    images: GroundImages,
    substitutions: GroundMatches,
): (det target_matches: GroundMatches, det many: GroundMatches, det joined: GroundMatches) {
    ensure targets_rule: target_matches = if theory_terms_empty?(targets) then ground_no_matches(variables)
        else if ground_term?(theory_first_term(targets), 0)
        and ground_succeeded?(
            ground_match(ctx, variables, pattern, theory_first_term(targets), images)
        )
        then ground_add_match(
            ground_result_images(
                ground_match(ctx, variables, pattern, theory_first_term(targets), images)
            ),
            ground_targets(ctx, variables, pattern, theory_terms_rest(targets), images)
        )
        else ground_targets(ctx, variables, pattern, theory_terms_rest(targets), images)
    ensure many_rule: many = if ground_matches_empty?(substitutions) then substitutions else
        ground_append_matches(
            ground_targets(
                ctx,
                variables,
                pattern,
                targets,
                ground_matches_first(substitutions)
            ),
            ground_many(
                ctx,
                variables,
                pattern,
                targets,
                ground_matches_rest(substitutions)
            )
        )
    ensure join_rule: joined = if theory_terms_empty?(patterns) then substitutions else
        ground_join(
            ctx,
            variables,
            theory_terms_rest(patterns),
            targets,
            ground_many(
                ctx,
                variables,
                theory_first_term(patterns),
                targets,
                substitutions
            )
        )
}

pub fn ground_listed_values(GroundContext, Ty): TheoryTerms

pub fn ground_typed_extensions(
    GroundContext,
    TheoryName,
    Ty,
    TheoryTerms,
    GroundImages
): GroundMatches

pub fn ground_listed_extensions(
    GroundContext,
    TheoryTerms,
    TheoryName,
    Ty,
    GroundImages
): GroundMatches

pub fn ground_listed_many(GroundContext, TheoryTerms, TheoryName, Ty, GroundMatches): GroundMatches

pub fn ground_complete_listed(
    GroundContext,
    TheoryTerms,
    TheoryVariables,
    GroundMatches
): GroundMatches

pub proc ground_listed_step(
    ctx: GroundContext,
    terms: TheoryTerms,
    name: TheoryName,
    ty: Ty,
    values: TheoryTerms,
    images: GroundImages,
    substitutions: GroundMatches,
    variables: TheoryVariables,
): (
    det typed: GroundMatches,
    det extended: GroundMatches,
    det many: GroundMatches,
    det completed: GroundMatches,
) {
    ensure typed_rule: typed = if theory_terms_empty?(values) then ground_no_matches(variables)
        else if ground_term?(theory_first_term(values), 0) and ground_type_present?(ctx, theory_first_term(values))
        and ground_type(ctx, theory_first_term(values)) = ty
        then ground_add_match(
            ground_extend(images, name, theory_first_term(values)),
            ground_typed_extensions(ctx, name, ty, theory_terms_rest(values), images)
        )
        else ground_typed_extensions(ctx, name, ty, theory_terms_rest(values), images)
    ensure extensions_rule: extended =
        if ground_image_present?(images, name) or not ground_any_mentions?(name, terms) or not ground_listed?(ctx, ty)
        then ground_add_match(images, ground_no_matches(variables))
        else ground_typed_extensions(ctx, name, ty, ground_listed_values(ctx, ty), images)
    ensure many_rule: many = if ground_matches_empty?(substitutions) then substitutions else
        ground_append_matches(
            ground_listed_extensions(ctx, terms, name, ty, ground_matches_first(substitutions)),
            ground_listed_many(ctx, terms, name, ty, ground_matches_rest(substitutions))
        )
    ensure completion_rule: completed = if theory_variables_empty?(variables) then substitutions else
        ground_complete_listed(
            ctx,
            terms,
            theory_variables_rest(variables),
            ground_listed_many(
                ctx,
                terms,
                theory_variable_name(variables),
                theory_variable_type(variables),
                substitutions
            )
        )
}

pub fn ground_apps_list(GroundContext, TheoryTerms): TheoryTerms
pub fn ground_call_apps(GroundContext, TheoryTerms): TheoryTerms
pub fn ground_outer_apps(TheoryTerms): TheoryTerms
pub fn ground_order(GroundContext): GroundOrder
pub fn ground_initial_matches(TheoryVariables): GroundMatches

pub proc ground_sentence_lists_step(ctx: GroundContext, terms: TheoryTerms): (
    det apps: TheoryTerms,
    det calls: TheoryTerms,
    det outer_apps: TheoryTerms,
) {
    ensure apps_rule: apps = if theory_terms_empty?(terms) then terms else
        ground_append(
            ground_apps(ctx, theory_first_term(terms)),
            ground_apps_list(ctx, theory_terms_rest(terms))
        )
    ensure calls_rule: calls = if theory_terms_empty?(terms) then terms else
        ground_append(
            ground_apps_list(ctx, ground_args(theory_first_term(terms))),
            ground_call_apps(ctx, theory_terms_rest(terms))
        )
    ensure outer_rule: outer_apps = if theory_terms_empty?(terms) then terms else
        if ground_outer?(theory_first_term(terms), 0) then theory_add_term(
            theory_first_term(terms),
            ground_outer_apps(theory_terms_rest(terms))
        )
        else ground_outer_apps(theory_terms_rest(terms))
}

pub fn ground_rule_apps(GroundContext, TheorySentence): TheoryTerms
pub fn ground_rule_subject(GroundContext, TheorySentence): GroundSubject
pub fn ground_rule_anchors(GroundContext, TheorySentence): TheoryTerms

pub proc ground_rule_step(
    ctx: GroundContext,
    sentence: TheorySentence,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
): (
    det apps: TheoryTerms,
    det subject: GroundSubject,
    det anchors: TheoryTerms,
    det binding?,
    det substitutions: GroundMatches,
) {
    ensure apps_rule: apps = ground_append(
        ground_apps_list(
            ctx,
            theory_add_term(
                theory_sentence_domain(sentence),
                theory_sentence_claims(sentence)
            )
        ),
        ground_call_apps(ctx, theory_sentence_calls(sentence))
    )
    ensure subject_rule: subject = ground_subject(
        ground_order(ctx),
        ground_append(
            ground_rule_apps(ctx, sentence),
            theory_sentence_calls(sentence)
        )
    )
    ensure anchors_rule: anchors = ground_anchors(
        theory_sentence_variables(sentence),
        ground_subject_apps(
            ground_rule_subject(ctx, sentence),
            ground_rule_apps(ctx, sentence)
        )
    )
    ensure binding_rule: binding? iff ground_binding?(
        ctx,
        ground_append(
            ground_rule_apps(ctx, sentence),
            theory_sentence_calls(sentence)
        ),
        ground_append(
            ground_rule_anchors(ctx, sentence),
            ground_outer_apps(theory_sentence_calls(sentence))
        ),
        theory_sentence_variables(sentence)
    )
    ensure matches_rule: substitutions = if not binding? or (
        ground_subject_present?(ground_rule_subject(ctx, sentence)) and not ground_uses?(
            ground_append(query_apps, query_calls),
            ground_subject_name(ground_rule_subject(ctx, sentence))
        )
        ) then ground_no_matches(theory_sentence_variables(sentence))
        else ground_unique_matches(
            ground_complete_listed(
                ctx,
                theory_add_term(
                    theory_sentence_domain(sentence),
                    ground_append(
                        theory_sentence_calls(sentence),
                        theory_sentence_claims(sentence)
                    )
                ),
                theory_sentence_variables(sentence),
                ground_join(
                    ctx,
                    theory_sentence_variables(sentence),
                    ground_outer_apps(theory_sentence_calls(sentence)),
                    query_calls,
                    ground_join(
                        ctx,
                        theory_sentence_variables(sentence),
                        ground_rule_anchors(ctx, sentence),
                        query_apps,
                        ground_initial_matches(theory_sentence_variables(sentence))
                    )
                )
            )
        )
}

pub fn ground_context_definitions(GroundContext): GroundDefinitions
pub fn ground_normalize_terms(GroundDefinitions, TheoryTerms): TheoryTerms
pub fn ground_normalize_sentence(GroundDefinitions, TheorySentence): TheorySentence

-- Preparation returns syntax; the normalized listed table is stated directly
-- in ground_prepared_listed_step, without an opaque context conversion.
pub proc ground_preparation_step(
    defs: GroundDefinitions,
    sentence: TheorySentence,
    terms: TheoryTerms,
): (det normalized_terms: TheoryTerms, det normalized_sentence: TheorySentence) {
    ensure terms_rule: normalized_terms = if theory_terms_empty?(terms) then terms else
        theory_add_term(
            ground_normalize(defs, theory_first_term(terms)),
            ground_normalize_terms(defs, theory_terms_rest(terms))
        )
    ensure sentence_rule: normalized_sentence = theory_sentence(
        theory_sentence_role(sentence),
        theory_sentence_variables(sentence),
        ground_normalize(defs, theory_sentence_domain(sentence)),
        ground_normalize_terms(defs, theory_sentence_calls(sentence)),
        ground_normalize_terms(defs, theory_sentence_claims(sentence))
    )
}

pub fn ground_prepared_extension(
    GroundContext,
    GroundDefinitions,
    TheoryTerms,
    TheoryName,
    Ty,
    GroundImages
): GroundMatches

pub fn ground_prepared_many(
    GroundContext,
    GroundDefinitions,
    TheoryTerms,
    TheoryName,
    Ty,
    GroundMatches
): GroundMatches

pub fn ground_prepared_complete(
    GroundContext,
    GroundDefinitions,
    TheoryTerms,
    TheoryVariables,
    GroundMatches
): GroundMatches

pub proc ground_prepared_listed_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    terms: TheoryTerms,
    name: TheoryName,
    ty: Ty,
    images: GroundImages,
    substitutions: GroundMatches,
    variables: TheoryVariables,
): (det extended: GroundMatches, det many: GroundMatches, det completed: GroundMatches) {
    ensure extension_rule: extended =
        if ground_image_present?(images, name) or not ground_any_mentions?(name, terms) or not ground_listed?(ctx, ty)
        then ground_add_match(images, ground_no_matches(variables))
        else ground_typed_extensions(
            ctx,
            name,
            ty,
            ground_normalize_terms(defs, ground_listed_values(ctx, ty)),
            images
        )
    ensure many_rule: many = if ground_matches_empty?(substitutions) then substitutions else
        ground_append_matches(
            ground_prepared_extension(
                ctx,
                defs,
                terms,
                name,
                ty,
                ground_matches_first(substitutions)
            ),
            ground_prepared_many(
                ctx,
                defs,
                terms,
                name,
                ty,
                ground_matches_rest(substitutions)
            )
        )
    ensure completion_rule: completed = if theory_variables_empty?(variables) then substitutions else
        ground_prepared_complete(
            ctx,
            defs,
            terms,
            theory_variables_rest(variables),
            ground_prepared_many(
                ctx,
                defs,
                terms,
                theory_variable_name(variables),
                theory_variable_type(variables),
                substitutions
            )
        )
}

pub fn ground_prepared_matches(
    GroundContext,
    GroundDefinitions,
    TheorySentence,
    TheoryTerms,
    TheoryTerms
): GroundMatches

pub proc ground_prepared_rule_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    sentence: TheorySentence,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
): (det substitutions: GroundMatches) {
    ensure matches_rule: substitutions = if not ground_binding?(
        ctx,
        ground_append(
            ground_rule_apps(ctx, sentence),
            theory_sentence_calls(sentence)
        ),
        ground_append(
            ground_rule_anchors(ctx, sentence),
            ground_outer_apps(theory_sentence_calls(sentence))
        ),
        theory_sentence_variables(sentence)
    ) or (ground_subject_present?(ground_rule_subject(ctx, sentence)) and not ground_uses?(
        ground_append(query_apps, query_calls),
        ground_subject_name(ground_rule_subject(ctx, sentence))
    ))
        then ground_no_matches(theory_sentence_variables(sentence))
        else ground_unique_matches(
            ground_prepared_complete(
                ctx,
                defs,
                theory_add_term(
                    theory_sentence_domain(sentence),
                    ground_append(
                        theory_sentence_calls(sentence),
                        theory_sentence_claims(sentence)
                    )
                ),
                theory_sentence_variables(sentence),
                ground_join(
                    ctx,
                    theory_sentence_variables(sentence),
                    ground_outer_apps(theory_sentence_calls(sentence)),
                    query_calls,
                    ground_join(
                        ctx,
                        theory_sentence_variables(sentence),
                        ground_rule_anchors(ctx, sentence),
                        query_apps,
                        ground_initial_matches(theory_sentence_variables(sentence))
                    )
                )
            )
        )
}

-- The list retains the sentence returned by the shared instantiation core.
pub type GroundSentences
pub fn ground_no_sentences(TheorySentence): GroundSentences
pub fn ground_add_sentence(TheorySentence, GroundSentences): GroundSentences

pub fn ground_instances_for(TheorySentence, GroundMatches): GroundSentences

pub proc ground_instance_list_step(sentence: TheorySentence, substitutions: GroundMatches): (
    det instances: GroundSentences,
) {
    call first := theory_instance(
        ground_image_substitution(ground_matches_first(substitutions)),
        sentence,
    )
    ensure instances_rule: instances = if ground_matches_empty?(substitutions) then ground_no_sentences(sentence)
        else if first.accepted? then ground_add_sentence(
            first.instance_sentence,
            ground_instances_for(sentence, ground_matches_rest(substitutions))
        )
        else ground_instances_for(sentence, ground_matches_rest(substitutions))
}

pub fn ground_query_matches(GroundContext, TheorySentence, TheoryTerms, TheoryTerms): GroundMatches

pub fn ground_instances(GroundContext, TheorySentence, TheoryTerms, TheoryTerms): GroundSentences

pub proc ground_instances_step(
    ctx: GroundContext,
    sentence: TheorySentence,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
): (det substitutions: GroundMatches, det instances: GroundSentences) {
    let defs: GroundDefinitions := ground_normalize_definitions(ground_context_definitions(ctx))
    call apps := ground_preparation_step(defs, sentence, query_apps)
    call calls := ground_preparation_step(defs, sentence, query_calls)
    ensure matching_rule: substitutions = ground_prepared_matches(
        ctx,
        defs,
        apps.normalized_sentence,
        ground_append(
            ground_apps_list(ctx, apps.normalized_terms),
            ground_call_apps(ctx, calls.normalized_terms)
        ),
        calls.normalized_terms
    )
    ensure instances_rule: instances = ground_instances_for(
        apps.normalized_sentence,
        ground_query_matches(ctx, sentence, query_apps, query_calls)
    )
}

#fren_check ground_match_step
#fren_check ground_parameter_step
#fren_check ground_extension_step
#fren_check ground_normalization
#fren_check ground_shape_step
#fren_check ground_subject_step
#fren_check ground_selection_step
#fren_check ground_variables_step
#fren_check ground_join_step
#fren_check ground_listed_step
#fren_check ground_sentence_lists_step
#fren_check ground_rule_step
#fren_check ground_prepared_listed_step
#fren_check ground_prepared_rule_step
#fren_check ground_preparation_step
#fren_check ground_instance_list_step
#fren_check ground_instances_step
```

### Ranked candidate construction and activation

The finite universe is built before activation. At each subject, in reverse
item order, images come from ground query subterms, closed sentence terms,
listed values and the applications generated at later subjects. Listed
compound values contribute their subterms too. Construction overapproximates
possible instances; activation requires all anchors and calls together.
Subject use includes all applications of accepted instances, including those
beneath their binders. The ground filter applies to matching witnesses and
the image pool, rather than to subject use.

The activation kernel removes a nonempty part of the pending candidates in
each productive round. It preserves its seeds, adds only candidates and
leaves no enabled candidate pending. `FiniteActivation.Result.least` proves
leastness for every monotone enabling predicate; `GroundClosure.enabled_mono`
and `FiniteActivation.Result.sound` give soundness for this engine. These
proofs quantify over arbitrary finite universes, without a testing bound.
Completeness of the constructed universe under structural matching at the
final query is tested in `FrenTest.GroundClosure`; no Req or Lean theorem
states that property yet.
Front-end extraction and claim integration remain follow-ups of #758.

```fren
pub type GroundRules
pub type GroundCandidate
pub type GroundCandidateResult
pub type GroundCandidates
pub type GroundRanks

pub fn ground_rules_empty?(GroundRules)
pub fn ground_first_rule(GroundRules): TheorySentence
pub fn ground_rest_rules(GroundRules): GroundRules
pub fn ground_add_rule(TheorySentence, GroundRules): GroundRules
pub fn ground_normalize_rules(GroundDefinitions, GroundRules): GroundRules
pub fn ground_closed_rules(GroundRules): TheoryTerms
pub fn ground_listed_variables(GroundContext, GroundDefinitions, TheoryVariables): TheoryTerms
pub fn ground_listed_rules(GroundContext, GroundDefinitions, GroundRules): TheoryTerms
pub fn ground_subterms(TheoryTerm): TheoryTerms
pub fn ground_subterms_many(TheoryTerms): TheoryTerms
pub fn ground_ground_terms(TheoryTerms): TheoryTerms
pub fn ground_unique_terms(TheoryTerms): TheoryTerms
pub fn ground_all_ground?(TheoryTerms)

pub fn ground_typed_many(GroundContext, TheoryTerms, TheoryName, Ty, GroundMatches): GroundMatches

pub fn ground_assign_one(
    GroundContext,
    GroundDefinitions,
    TheorySentence,
    TheoryTerms,
    TheoryName,
    Ty,
    GroundMatches
): GroundMatches

pub fn ground_assign_from(
    GroundContext,
    GroundDefinitions,
    TheorySentence,
    TheoryTerms,
    TheoryVariables,
    GroundMatches
): GroundMatches

pub fn ground_assignments(
    GroundContext,
    GroundDefinitions,
    TheorySentence,
    TheoryTerms
): GroundMatches

pub proc ground_assignment_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    sentence: TheorySentence,
    pool: TheoryTerms,
    name: TheoryName,
    ty: Ty,
    variables: TheoryVariables,
    substitutions: GroundMatches,
):
    (
        det typed: GroundMatches,
        det extended: GroundMatches,
        det assigned: GroundMatches,
        det all_assignments: GroundMatches,
    ) {
        ensure typed_rule: typed = if ground_matches_empty?(substitutions) then substitutions else
            ground_append_matches(
                ground_typed_extensions(ctx, name, ty, pool, ground_matches_first(substitutions)),
                ground_typed_many(ctx, pool, name, ty, ground_matches_rest(substitutions))
            )
        ensure extension_rule: extended = if not ground_any_mentions?(
            name,
            theory_add_term(
                theory_sentence_domain(sentence),
                ground_append(
                    theory_sentence_calls(sentence),
                    theory_sentence_claims(sentence)
                )
            )
        )
            or (not ground_listed?(ctx, ty) and not ground_any_mentions?(
                name,
                ground_append(
                    ground_rule_anchors(ctx, sentence),
                    ground_outer_apps(theory_sentence_calls(sentence))
                )
            ))
            then substitutions else ground_typed_many(
                ctx,
                if ground_any_mentions?(
                    name,
                    ground_append(
                        ground_rule_anchors(ctx, sentence),
                        ground_outer_apps(theory_sentence_calls(sentence))
                    )
                ) then pool else ground_normalize_terms(defs, ground_listed_values(ctx, ty)),
                name,
                ty,
                substitutions
            )
        ensure assigned_rule: assigned = if theory_variables_empty?(variables) then substitutions else
            ground_assign_from(
                ctx,
                defs,
                sentence,
                pool,
                theory_variables_rest(variables),
                ground_assign_one(
                    ctx,
                    defs,
                    sentence,
                    pool,
                    theory_variable_name(variables),
                    theory_variable_type(variables),
                    substitutions
                )
            )
        ensure all_rule: all_assignments = ground_assign_from(
            ctx,
            defs,
            sentence,
            pool,
            theory_sentence_variables(sentence),
            ground_initial_matches(theory_sentence_variables(sentence))
        )
    }

pub fn ground_candidate(
    Nat,
    TheorySentence,
    TheoryTerms,
    TheoryTerms,
    GroundSubject
): GroundCandidate

pub fn ground_no_candidate(TheorySentence): GroundCandidateResult
pub fn ground_some_candidate(GroundCandidate): GroundCandidateResult
pub fn ground_candidate_present?(GroundCandidateResult)
pub fn ground_candidate_value(GroundCandidateResult): GroundCandidate
pub fn ground_candidate_sentence(GroundCandidate): TheorySentence
pub fn ground_candidate_anchors(GroundCandidate): TheoryTerms
pub fn ground_candidate_calls(GroundCandidate): TheoryTerms
pub fn ground_candidate_subject(GroundCandidate): GroundSubject

pub fn ground_make_candidate(
    GroundContext,
    Nat,
    TheorySentence,
    GroundImages
): GroundCandidateResult

pub fn ground_from_assignments(GroundContext, Nat, TheorySentence, GroundMatches): GroundCandidates

pub fn ground_candidates(
    GroundContext,
    GroundDefinitions,
    Nat,
    TheorySentence,
    TheoryTerms
): GroundCandidates

pub fn ground_no_candidates(Nat): GroundCandidates
pub fn ground_add_candidate(GroundCandidate, GroundCandidates): GroundCandidates
pub fn ground_candidates_empty?(GroundCandidates)
pub fn ground_first_candidate(GroundCandidates): GroundCandidate
pub fn ground_rest_candidates(GroundCandidates): GroundCandidates
pub fn ground_append_candidates(GroundCandidates, GroundCandidates): GroundCandidates
pub fn ground_unique_candidates(GroundCandidates): GroundCandidates
pub fn ground_candidate_apps(GroundContext, GroundCandidates): TheoryTerms
pub fn ground_candidate_all_apps(GroundContext, GroundCandidates): TheoryTerms

pub proc ground_candidate_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    index: Nat,
    sentence: TheorySentence,
    images: GroundImages,
    substitutions: GroundMatches,
    pool: TheoryTerms,
):
    (
        det result: GroundCandidateResult,
        det collected: GroundCandidates,
        det candidates: GroundCandidates,
    ) {
        call first := theory_instance(ground_image_substitution(images), sentence)
        let anchors: TheoryTerms := substitute_terms(
            ground_image_substitution(images),
            theory_sentence_variables(sentence),
            ground_rule_anchors(ctx, sentence)
        )
        let calls: TheoryTerms := substitute_terms(
            ground_image_substitution(images),
            theory_sentence_variables(sentence),
            ground_outer_apps(theory_sentence_calls(sentence))
        )
        ensure candidate_rule: result = if first.accepted? and ground_all_ground?(ground_append(anchors, calls))
            then ground_some_candidate(
                ground_candidate(
                    index,
                    first.instance_sentence,
                    anchors,
                    calls,
                    ground_rule_subject(ctx, sentence)
                )
            )
            else ground_no_candidate(sentence)
        ensure collected_rule: collected = if ground_matches_empty?(substitutions) then ground_no_candidates(index)
            else if ground_candidate_present?(
                ground_make_candidate(ctx, index, sentence, ground_matches_first(substitutions))
            )
            then ground_add_candidate(
                ground_candidate_value(
                    ground_make_candidate(ctx, index, sentence, ground_matches_first(substitutions))
                ),
                ground_from_assignments(ctx, index, sentence, ground_matches_rest(substitutions))
            )
            else ground_from_assignments(ctx, index, sentence, ground_matches_rest(substitutions))
        ensure candidates_rule: candidates = ground_from_assignments(
            ctx,
            index,
            sentence,
            ground_assignments(ctx, defs, sentence, pool)
        )
    }

pub fn ground_seed_pool(
    GroundContext,
    GroundDefinitions,
    GroundRules,
    TheoryTerms,
    TheoryTerms
): TheoryTerms

pub proc ground_pool_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    rules: GroundRules,
    variables: TheoryVariables,
    terms: TheoryTerms,
    term: TheoryTerm,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
    candidates: GroundCandidates,
):
    (
        det normalized: GroundRules,
        det closed_terms: TheoryTerms,
        det listed_variables: TheoryTerms,
        det listed_rules: TheoryTerms,
        det subterms: TheoryTerms,
        det many: TheoryTerms,
        det apps: TheoryTerms,
        det all_apps: TheoryTerms,
        det ground_terms: TheoryTerms,
        det all_ground?,
        det seeds: TheoryTerms,
    ) {
        ensure normalized_rule: normalized = if ground_rules_empty?(rules) then rules else
            ground_add_rule(
                ground_normalize_sentence(defs, ground_first_rule(rules)),
                ground_normalize_rules(defs, ground_rest_rules(rules))
            )
        ensure closed_rule: closed_terms = if ground_rules_empty?(rules) then ground_no_terms(term) else
            ground_append(
                theory_add_term(
                    theory_sentence_domain(ground_first_rule(rules)),
                    ground_append(
                        theory_sentence_calls(ground_first_rule(rules)),
                        theory_sentence_claims(ground_first_rule(rules))
                    )
                ),
                ground_closed_rules(ground_rest_rules(rules))
            )
        ensure variables_rule: listed_variables = if theory_variables_empty?(variables) then ground_no_terms(term) else
            ground_append(
                ground_normalize_terms(
                    defs,
                    ground_listed_values(ctx, theory_variable_type(variables))
                ),
                ground_listed_variables(ctx, defs, theory_variables_rest(variables))
            )
        ensure listed_rule: listed_rules = if ground_rules_empty?(rules) then ground_no_terms(term) else
            ground_append(
                ground_listed_variables(
                    ctx,
                    defs,
                    theory_sentence_variables(ground_first_rule(rules))
                ),
                ground_listed_rules(ctx, defs, ground_rest_rules(rules))
            )
        ensure subterms_rule: subterms = theory_add_term(
            term,
            match theory_term_kind(term) {
                TheoryTermKind::Apply => ground_append(
                    ground_subterms(theory_term_left(term)),
                    ground_subterms(theory_term_right(term))
                ),
                TheoryTermKind::All | TheoryTermKind::Exists =>
                    ground_subterms(theory_term_left(term)),
                _ => ground_no_terms(term),
            }
        )
        ensure many_rule: many = if theory_terms_empty?(terms) then terms else
            ground_append(
                ground_subterms(theory_first_term(terms)),
                ground_subterms_many(theory_terms_rest(terms))
            )
        ensure apps_rule: apps = if ground_candidates_empty?(candidates) then ground_no_terms(term) else
            ground_append(
                ground_ground_terms(
                    ground_rule_apps(
                        ctx,
                        ground_candidate_sentence(ground_first_candidate(candidates))
                    )
                ),
                ground_candidate_apps(ctx, ground_rest_candidates(candidates))
            )
        ensure all_apps_rule: all_apps = if ground_candidates_empty?(candidates) then ground_no_terms(term) else
            ground_append(
                ground_rule_apps(
                    ctx,
                    ground_candidate_sentence(ground_first_candidate(candidates))
                ),
                ground_candidate_all_apps(ctx, ground_rest_candidates(candidates))
            )
        ensure ground_rule: ground_terms = if theory_terms_empty?(terms) then terms else
            if ground_term?(theory_first_term(terms), 0) then theory_add_term(
                theory_first_term(terms),
                ground_ground_terms(theory_terms_rest(terms))
            )
            else ground_ground_terms(theory_terms_rest(terms))
        ensure all_ground_rule: all_ground? iff theory_terms_empty?(terms) or
            (ground_term?(theory_first_term(terms), 0) and ground_all_ground?(theory_terms_rest(terms)))
        ensure seeds_rule: seeds = ground_unique_terms(
            ground_ground_terms(
                ground_subterms_many(
                    ground_append(
                        ground_append(query_apps, query_calls),
                        ground_append(
                            ground_closed_rules(rules),
                            ground_listed_rules(ctx, defs, rules)
                        )
                    )
                )
            )
        )
    }

pub fn ground_ranks_empty?(GroundRanks)
pub fn ground_first_rank(GroundRanks): GroundSubject
pub fn ground_rest_ranks(GroundRanks): GroundRanks
pub fn ground_no_ranks(GroundOrder): GroundRanks
pub fn ground_single_rank(GroundSubject): GroundRanks
pub fn ground_append_ranks(GroundRanks, GroundRanks): GroundRanks
pub fn ground_reverse_order(GroundOrder): GroundRanks
pub fn ground_subject_ranks(GroundContext): GroundRanks

pub fn ground_at_rank(
    GroundContext,
    GroundDefinitions,
    GroundRules,
    GroundSubject,
    TheoryTerms,
    Nat
): GroundCandidates

pub fn ground_build_ranks(
    GroundContext,
    GroundDefinitions,
    GroundRules,
    GroundRanks,
    TheoryTerms
): GroundCandidates

pub fn ground_universe(
    GroundContext,
    GroundDefinitions,
    GroundRules,
    TheoryTerms,
    TheoryTerms
): GroundCandidates

pub fn ground_instantiable?(ctx: GroundContext, sentence: TheorySentence): (eligible?) {
    ensure rule: eligible? iff ground_binding?(
        ctx,
        ground_append(
            ground_rule_apps(ctx, sentence),
            theory_sentence_calls(sentence)
        ),
        ground_append(
            ground_rule_anchors(ctx, sentence),
            ground_outer_apps(theory_sentence_calls(sentence))
        ),
        theory_sentence_variables(sentence)
    )
}

pub proc ground_universe_step(
    ctx: GroundContext,
    defs: GroundDefinitions,
    rules: GroundRules,
    subject: GroundSubject,
    ranks: GroundRanks,
    order: GroundOrder,
    pool: TheoryTerms,
    index: Nat,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
):
    (
        det reversed_ranks: GroundRanks,
        det subjects: GroundRanks,
        det at_rank: GroundCandidates,
        det built: GroundCandidates,
        det universe_candidates: GroundCandidates,
    ) {
        ensure order_rule: reversed_ranks = if ground_order_empty?(order) then ground_no_ranks(order) else
            ground_append_ranks(
                ground_reverse_order(ground_order_rest(order)),
                ground_single_rank(ground_named(ground_order_first(order)))
            )
        ensure subjects_rule: subjects = ground_append_ranks(
            ground_single_rank(ground_no_subject(ground_order(ctx))),
            ground_reverse_order(ground_order(ctx))
        )
        ensure rank_rule: at_rank = if ground_rules_empty?(rules) then ground_no_candidates(index) else
            ground_append_candidates(
                if ground_rule_subject(ctx, ground_first_rule(rules)) = subject
                    and ground_instantiable?(ctx, ground_first_rule(rules))
                    then ground_candidates(ctx, defs, index, ground_first_rule(rules), pool) else ground_no_candidates(index),
                ground_at_rank(
                    ctx,
                    defs,
                    ground_rest_rules(rules),
                    subject,
                    pool,
                    index + 1
                )
            )
        ensure build_rule: built = if ground_ranks_empty?(ranks) then ground_no_candidates(index) else
            ground_append_candidates(
                ground_at_rank(ctx, defs, rules, ground_first_rank(ranks), pool, 0),
                ground_build_ranks(
                    ctx,
                    defs,
                    rules,
                    ground_rest_ranks(ranks),
                    ground_unique_terms(
                        ground_append(
                            pool,
                            ground_ground_terms(
                                ground_subterms_many(
                                    ground_candidate_apps(
                                        ctx,
                                        ground_at_rank(
                                            ctx,
                                            defs,
                                            rules,
                                            ground_first_rank(ranks),
                                            pool,
                                            0
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        ensure universe_rule: universe_candidates = ground_unique_candidates(
            ground_build_ranks(
                ctx,
                defs,
                rules,
                ground_subject_ranks(ctx),
                ground_seed_pool(ctx, defs, rules, query_apps, query_calls)
            )
        )
    }

pub fn ground_contains?(TheoryTerms, TheoryTerm)
pub fn ground_order_contains?(GroundOrder, TheoryName)
pub fn ground_no_order(TheoryTerm): GroundOrder
pub fn ground_add_name(TheoryName, GroundOrder): GroundOrder
pub fn ground_term_heads(TheoryTerms): GroundOrder
pub fn ground_query_terms(GroundContext, TheoryTerms, GroundCandidates): TheoryTerms
pub fn ground_query_subjects(GroundContext, TheoryTerms, TheoryTerms, GroundCandidates): GroundOrder
pub fn ground_enabled?(GroundContext, TheoryTerms, TheoryTerms, GroundCandidate, GroundCandidates)

pub proc ground_applications_step(
    ctx: GroundContext,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
    accepted: GroundCandidates,
    terms: TheoryTerms,
    order: GroundOrder,
    term: TheoryTerm,
    name: TheoryName,
):
    (
        det term_present?,
        det name_present?,
        det heads: GroundOrder,
        det applications: TheoryTerms,
        det subjects: GroundOrder,
    ) {
        ensure term_rule: term_present? iff not theory_terms_empty?(terms) and
            (term = theory_first_term(terms) or ground_contains?(theory_terms_rest(terms), term))
        ensure name_rule: name_present? iff not ground_order_empty?(order) and
            (name = ground_order_first(order) or ground_order_contains?(ground_order_rest(order), name))
        ensure heads_rule: heads = if theory_terms_empty?(terms) then ground_no_order(term) else
            if theory_term_kind(ground_head(theory_first_term(terms))) = TheoryTermKind::Item
            then ground_add_name(
                theory_term_name(ground_head(theory_first_term(terms))),
                ground_term_heads(theory_terms_rest(terms))
            )
            else ground_term_heads(theory_terms_rest(terms))
        ensure applications_rule: applications = ground_append(query_apps, ground_candidate_apps(ctx, accepted))
        ensure subjects_rule: subjects = ground_term_heads(
            ground_append(
                ground_append(query_apps, ground_candidate_all_apps(ctx, accepted)),
                query_calls
            )
        )
    }

set_option fren.lint.undecidable "allow" in
pub proc ground_enabled_step(
    ctx: GroundContext,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
    candidate: GroundCandidate,
    accepted: GroundCandidates,
): (det enabled?) {
    ensure rule: enabled? iff
        (forall (t: TheoryTerm), when ground_contains?(ground_candidate_anchors(candidate), t),
        ground_contains?(ground_query_terms(ctx, query_apps, accepted), t))
        and (forall (t: TheoryTerm), when ground_contains?(ground_candidate_calls(candidate), t), ground_contains?(query_calls, t))
        and (when ground_subject_present?(ground_candidate_subject(candidate)),
        ground_order_contains?(
            ground_query_subjects(ctx, query_apps, query_calls, accepted),
            ground_subject_name(ground_candidate_subject(candidate))
        ))
}

pub fn ground_ready(
    GroundContext,
    TheoryTerms,
    TheoryTerms,
    GroundCandidates,
    GroundCandidates
): GroundCandidates

pub fn ground_remaining(
    GroundContext,
    TheoryTerms,
    TheoryTerms,
    GroundCandidates,
    GroundCandidates
): GroundCandidates

pub fn ground_saturate(
    GroundContext,
    TheoryTerms,
    TheoryTerms,
    GroundCandidates,
    GroundCandidates
): GroundCandidates

pub proc ground_activation_step(
    ctx: GroundContext,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
    pending: GroundCandidates,
    initial: GroundCandidates,
):
    (det ready: GroundCandidates, det remaining: GroundCandidates, det result: GroundCandidates) {
        ensure ready_rule: ready = if ground_candidates_empty?(pending) then pending else
            if ground_enabled?(
                ctx,
                query_apps,
                query_calls,
                ground_first_candidate(pending),
                initial
            )
            then ground_add_candidate(
                ground_first_candidate(pending),
                ground_ready(
                    ctx,
                    query_apps,
                    query_calls,
                    ground_rest_candidates(pending),
                    initial
                )
            )
            else ground_ready(
                ctx,
                query_apps,
                query_calls,
                ground_rest_candidates(pending),
                initial
            )
        ensure remaining_rule: remaining = if ground_candidates_empty?(pending) then pending else
            if ground_enabled?(
                ctx,
                query_apps,
                query_calls,
                ground_first_candidate(pending),
                initial
            )
            then ground_remaining(
                ctx,
                query_apps,
                query_calls,
                ground_rest_candidates(pending),
                initial
            )
            else ground_add_candidate(
                ground_first_candidate(pending),
                ground_remaining(
                    ctx,
                    query_apps,
                    query_calls,
                    ground_rest_candidates(pending),
                    initial
                )
            )
        ensure result_rule: result = if ground_candidates_empty?(ground_ready(ctx, query_apps, query_calls, pending, initial)) then initial else
            ground_saturate(
                ctx,
                query_apps,
                query_calls,
                ground_remaining(ctx, query_apps, query_calls, pending, initial),
                ground_append_candidates(
                    initial,
                    ground_ready(ctx, query_apps, query_calls, pending, initial)
                )
            )
    }

pub proc ground_close_step(
    ctx: GroundContext,
    rules: GroundRules,
    query_apps: TheoryTerms,
    query_calls: TheoryTerms,
):
    (det instances: GroundCandidates, det applications: TheoryTerms) {
        let defs: GroundDefinitions := ground_normalize_definitions(ground_context_definitions(ctx))
        let normalized_rules: GroundRules := ground_normalize_rules(defs, rules)
        let apps: TheoryTerms := ground_unique_terms(
            ground_append(
                ground_apps_list(ctx, ground_normalize_terms(defs, query_apps)),
                ground_call_apps(ctx, ground_normalize_terms(defs, query_calls))
            )
        )
        let calls: TheoryTerms := ground_unique_terms(ground_normalize_terms(defs, query_calls))
        let candidates: GroundCandidates :=
            ground_universe(ctx, defs, normalized_rules, apps, calls)
        call activation := ground_activation_step(
            ctx,
            apps,
            calls,
            candidates,
            ground_no_candidates(0),
        )
        ensure instances_rule: instances = activation.result
        ensure applications_rule: applications = ground_unique_terms(ground_query_terms(ctx, apps, activation.result))
    }

#fren_check ground_assignment_step
#fren_check ground_candidate_step
#fren_check ground_pool_step
#fren_check ground_universe_step
#fren_check ground_applications_step
#fren_check ground_enabled_step
#fren_check ground_activation_step
#fren_check ground_close_step
```
