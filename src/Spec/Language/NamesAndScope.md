# Resolution

Resolution is the first part of static semantics: a module is resolved
before it is typed. Resolution takes the tree that the
[syntax chapter](Syntax.md) defines and replaces every written name of a
module by what the name denotes: a local by its level in the enclosing
scope, an item by its canonical identity. Its results are the symbol
environment Σ and the expressions of the Core, which has no names.
This chapter defines both, with the types, identities and contexts they are
made of, and [Core typing](Types.md), the next chapter, types them. The
syntax chapter owns the written forms, and typing owns every question about
types beyond which enumeration a written type names.

The domain is one module of enumerations with payload-free variants and
functions over `Bool`, `Int` and those enumerations, whose bodies are
literals, paths, operators, calls of a written path, `let`, `if` and
`match` on variant patterns.

r[names.overview.domain]
This chapter defines resolution for one complete module of this domain
whose name is one segment. A module that declares an expectation, a
program of more than one module and a module name of more than one
segment are outside what its judgments decide.

## Judgments

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ τ ok` | τ is a well-formed type | `ty_ok?` |
| `Σ ⊢ Γ ok` | every type of Γ is well formed | `ctx_ok?` |
| `⊢ Σ ok` | Σ is a well-formed symbol environment | `symb_ok?` |
| `S(x) = i` | in scope S the name x denotes the local at level i | `resolve_local` |
| `R; S ⊢ p ⇒ t` | the path p denotes the target t | `path_target` |
| `R ⊢ T ⇒ τ` | the written type T denotes the type τ | `resolve_type` |
| `R; S ⊢ l ⇒ l'` | the source layer l resolves to the Core layer l' | `resolve_layer` |
| `R; S ⊢ e ⇒ e'` | the expression e resolves to the Core expression e' | `resolve_expression`, on a [source table that denotes e](#r-names.expression.unfolding) |
| `m ⊢ ds ⇒ Σ` | the declarations ds of module m collect to Σ | `collect` |
| `⊢ m, ds resolves` | every name of the module resolves | `module_resolves?` |

r[names.overview.function]
Every judgment of this chapter that Fren defines is a function of its
inputs: a name, path, written type, layer, source table or module has at
most one resolution, and each Fren definition above computes it:
`module_resolves?` is false, and every other one is `None`, when there is
none. Resolution is therefore decidable. It consults no typing judgment,
value or solver. It resolves the written types of parameters and results,
and the only one it then inspects is the type of a parameter whose name
ends in `?`, which the [suffix rule](#r-names.surface.suffix) compares
with `Bool`. A `let` has no written type to inspect. An expression is given to these
definitions as a source table; that two tables of one expression resolve
alike is a [separate law](#r-names.expression.unique-expression), which is
open.

```text
  resolve_expression : (m, Σ) × scope × source table ⇀ Core table
  collect            : m × declarations ⇀ Σ

  determinism   a source table has at most one resolution
  weakening     a name inserted into every scope, and mentioned nowhere,
                shifts the result as typing's weakening shifts a table
  handoff       every local of the result is a level of its row's scope,
                every item of the result is bound in Σ with the kind its
                position needs, and ⊢ Σ ok
  order         sequences of the same declarations collect alike
```
Determinism needs no law of its own: `resolve_expression` and `collect`
are functions. The other laws are stated where their subjects are defined:
[nearest binding](#r-names.locals.nearest) and
[weakening](#r-names.locals.weakening) for scopes,
[weakening for a layer](#r-names.expression.weakening) and [for a
table](#r-names.expression.table-weakening),
[well-scoped results](#r-names.handoff.scoped) and [bound
items](#r-names.handoff.items) for expressions, and, for collection,
[independence of declaration order](#r-names.collection.permutation) and the
[well-formed environment](#r-names.handoff.environment) that typing assumes.

## Semantic objects

r[names.object.identity] spec::names::{ItemId, Ty}
An *item identity* is the canonical sequence of enclosing module and item
names, which this chapter [assigns to each item](#r-names.identity.child). Value types are `Bool`, the mathematical
integers `Int`, and nominal enumeration types `Nominal(a)`; in Fren their
constructors are `Ty::Boolean`, `Ty::Integer` and `Ty::Nominal`. Types are
compared by equality, including every component of a nominal identity.

```fren
pub mod spec
pub mod spec::names

use spec::surface::{BinaryOp, Parameter, Path, Snoc, SurfaceArm, SurfaceF, TypeName, UnaryOp}

use spec::surface::Snoc::{Empty, Extend}

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }
```

r[names.sequence.snoc] spec::names::{length, lookup}
A *snoc sequence*, the
[syntax chapter's `Snoc`](Syntax.md#r-syntax.tree.types), is either empty,
written `·`, or an earlier snoc sequence extended by one newest entry x,
written `xs, x`. Its length `|xs|` counts
its entries. The *level* of an entry is the number of entries before it, so
the oldest entry has level 0 and the newest has level `|xs| - 1`. `xs(i)`
is the entry at level i, defined exactly when `0 ≤ i < |xs|`. `lookup`
states half of this as its postcondition: where `xs(i)` is defined,
`0 ≤ i < |xs|`.

```fren
pub fn length<T>(xs: Snoc<T>): Nat := match xs {
    Empty => 0,
    Extend(earlier, _) => length(earlier) + 1,
}

pub fn lookup<T>(xs: Snoc<T>, level: Int): (entry: Option<T>) {
    out entry := match xs {
        Empty => None,
        Extend(earlier, x) => if level = length(earlier) then Some(x) else lookup(earlier, level),
    }
    ensure bound: when entry != None, 0 <= level < length(xs)
}
```

r[names.sequence.builders] spec::names::{one, two, three, four}
`one` to `four` build snoc sequences of one to four entries, oldest first.

```fren
pub fn one<T>(a: T): Snoc<T> := Extend(Empty, a)
pub fn two<T>(a: T, b: T): Snoc<T> := Extend(one(a), b)
pub fn three<T>(a: T, b: T, c: T): Snoc<T> := Extend(two(a, b), c)
pub fn four<T>(a: T, b: T, c: T, d: T): Snoc<T> := Extend(three(a, b, c), d)
```

r[names.context.slots] spec::names::Ctx
A *context* Γ is a snoc sequence of value types. Extending Γ by τ produces
`Γ, τ`, whose new entry has level `|Γ|`. A local refers to its entry by level.

```fren
pub type Ctx := Snoc<Ty>
```

r[names.symbols.environment] spec::names::{Sig, ItemKind, Entry, Symb, entry}
A *symbol environment* Σ binds item identities to entries. An entry is a
function signature, a constructor's owning enumeration, or an enumeration
with its constructors. A signature has the parameter types as a context, in
written order, and a result type. `Σ(x)` is the newest entry bound to x.
The environment is shared by every body of a program.

```fren
pub struct Sig { params: Ctx, result: Ty }
pub enum ItemKind { Function(Sig), Constructor(ItemId), Enumeration(Snoc<ItemId>) }
pub struct Entry { item: ItemId, kind: ItemKind }
pub type Symb := Snoc<Entry>

pub fn entry(symb: Symb, item: ItemId): Option<ItemKind> := match symb {
    Empty => None,
    Extend(earlier, binding) =>
        if binding.item = item then Some(binding.kind) else entry(earlier, item),
}
```

r[names.symbols.types-ok] spec::names::{ty_ok?, ctx_ok?}
A type is *well formed* in Σ when it is `Bool`, `Int`, or `Nominal(a)` with
`Σ(a)` an enumeration; a context is well formed when each of its types is.

```text
                                  Σ(a) = enumeration
  Σ ⊢ Bool ok     Σ ⊢ Int ok      ──────────────────
                                  Σ ⊢ Nominal(a) ok

                  Σ ⊢ Γ ok   Σ ⊢ τ ok
  Σ ⊢ · ok        ───────────────────
                  Σ ⊢ Γ, τ ok
```

```fren
pub fn ty_ok?(symb: Symb, ty: Ty) := match ty {
    Ty::Nominal(owner) => entry(symb, owner) is Some(ItemKind::Enumeration(_)),
    _ => true,
}

pub fn ctx_ok?(symb: Symb, ctx: Ctx) := match ctx {
    Empty => true,
    Extend(earlier, ty) => ty_ok?(symb, ty) and ctx_ok?(symb, earlier),
}
```

r[names.symbols.well-formed] spec::names::{member?, constructors_ok?, binding_ok?, bindings_ok?, symb_ok?}
Σ is well formed when it binds each item once, every signature's types are
well formed, every constructor's owner is an enumeration that lists it, and
every enumeration lists distinct constructors, each bound as a constructor
of that enumeration. In the figure, `Σ' ⊢ Σ ok` checks the bindings of
Σ against the whole environment Σ', as `bindings_ok?(Σ', Σ)` does,
x ∉ Σ says that Σ binds no x, and the list c₀, …, cₙ of an enumeration's
constructors may be empty.

```text
                Σ' ⊢ Σ ok   x ∉ Σ   Σ' ⊢ Δ ok   Σ' ⊢ τ ok
  Σ' ⊢ · ok     ─────────────────────────────────────────
                Σ' ⊢ Σ, x = function (Δ) → τ ok

  Σ' ⊢ Σ ok   x ∉ Σ   Σ'(a) = enumeration listing x
  ─────────────────────────────────────────────────
  Σ' ⊢ Σ, x = constructor of a ok

  Σ' ⊢ Σ ok   x ∉ Σ   c₀, …, cₙ distinct   Σ'(cₖ) = constructor of x
  ──────────────────────────────────────────────────────────────────
  Σ' ⊢ Σ, x = enumeration listing c₀, …, cₙ ok

  Σ ⊢ Σ ok
  ────────
  ⊢ Σ ok
```

```fren
pub fn member?(items: Snoc<ItemId>, item: ItemId) := match items {
    Empty => false,
    Extend(earlier, other) => other = item or member?(earlier, item),
}

pub fn constructors_ok?(symb: Symb, constructors: Snoc<ItemId>, owner: ItemId) :=
    match constructors {
        Empty => true,
        Extend(earlier, constructor) =>
            entry(symb, constructor) = Some(ItemKind::Constructor(owner))
            and not member?(earlier, constructor)
            and constructors_ok?(symb, earlier, owner),
    }

pub fn binding_ok?(symb: Symb, binding: Entry) := match binding.kind {
    ItemKind::Function(sig) => ctx_ok?(symb, sig.params) and ty_ok?(symb, sig.result),
    ItemKind::Constructor(owner) => match entry(symb, owner) {
        Some(ItemKind::Enumeration(constructors)) => member?(constructors, binding.item),
        _ => false,
    },
    ItemKind::Enumeration(constructors) => constructors_ok?(symb, constructors, binding.item),
}

pub fn bindings_ok?(symb: Symb, bindings: Symb) := match bindings {
    Empty => true,
    Extend(earlier, binding) =>
        entry(earlier, binding.item) = None
        and binding_ok?(symb, binding)
        and bindings_ok?(symb, earlier),
}

pub fn symb_ok?(symb: Symb) := bindings_ok?(symb, symb)
```

## The Core

The Core is the language that resolution produces and typing types. It has
the following grammar. The Core has no names: x stands for a local, which
the Core writes as its level `#i` in the enclosing scope, and a let binds
the next level.

```text
τ ::= Bool | Int | Nominal(a)
Γ ::= · | Γ, τ
e ::= b | n | x | c | ⊖ e | e ⊕ e | f(e, …, e)
    | let x := e in e | let x : τ := e in e
    | if e then e else e | match e { c ⇒ e | … | c ⇒ e }
```

Here b is a Boolean, n an integer, c a constructor and f a function, each
item named by its canonical identity; ⊖ is a unary and ⊕ a binary operator.
A match has at least one arm.

r[names.core.syntax] spec::names::{ArmF, CoreF, Form}
A Core expression is a finite tree whose nodes have the forms of `CoreF<E>`,
where E is the position of a child. A literal carries its value, and a let
carries the type annotation written on it, if any. A call's arguments and a
match's arms are snoc sequences in written order. An arm has a resolved
constructor pattern and a body, with no binder. Parentheses are concrete
syntax, removed before the Core, and have no form here. Fren cannot declare
a type of trees whose children sit inside snoc sequences, so a whole
expression is given as a table whose rows name their children by row
level, and a `Form` is the form of such a row. `CoreF<E>` is the one form
type that the tables of this chapter and of typing (`E` a row level),
typing's rules (`E` a child's typing) and the maps between them share.

```fren
pub struct ArmF<E> { constructor: ItemId, body: E }

pub enum CoreF<E> {
    BooleanLiteral(Bool),
    IntegerLiteral(Int),
    Local(Int),
    Constructor(ItemId),
    Unary(UnaryOp, E),
    Binary(BinaryOp, E, E),
    Call(ItemId, Snoc<E>),
    Let(Option<Ty>, E, E),
    If(E, E, E),
    Match(E, Snoc<ArmF<E>>),
}

pub type Form := CoreF<Int>
```

r[names.core.shift] spec::names::{shift, shift_form}
*Shifting* at a level n makes room for a new local at n: a level of at
least n becomes the next level, and a lower level is unchanged. Shifting a
layer shifts its local, if it is one, and changes no other form: the
children of a layer are not locals but positions.

```fren
pub fn shift(level: Int, cutoff: Int): Int := if level >= cutoff then level + 1 else level

pub fn shift_form(form: Form, cutoff: Int): Form := match form {
    CoreF::Local(level) => CoreF::Local(shift(level, cutoff)),
    _ => form,
}
```

## Surface elaboration

This section belongs to the derived-forms chapter, which will own it once
that chapter is written. It states how written annotations and binder names
become Core types; the Core itself has no names. Resolution applies these
rules to a [`let`](#r-names.expression.layer) and to a function's
[parameters](#r-names.collection.functions). The [syntax
chapter](Syntax.md#r-syntax.tree.types)'s `let` has no annotation, so
resolution applies `let_annotation?` with no written type.

r[names.surface.suffix] spec::names::{suffix_rule?, let_annotation?}
The *`?` suffix rule*: a parameter or let binder whose name ends in `?` must
have type `Bool`. A parameter's explicit annotation is not overwritten by
the suffix: `b?: Int` is an error. A let binder `x?` elaborates to a Core
let annotated `Bool`, and any other let binder to a Core let without an
annotation.

`let_annotation?` also states the rule for a `let` with a written type:
the annotation must satisfy the suffix rule and is kept. That case is
open. The Fren2 parser reads no annotation on a `let`, so the [syntax
chapter](Syntax.md#r-syntax.tree.types)'s `Let` has none, and
[resolution](#r-names.expression.layer) applies `let_annotation?` only
with no written type. No Fren2 source can therefore write the Core form
`let x : τ := e₁ in e₂` with τ other than the `Bool` of a `?` binder.
[Core typing](Types.md#r-types.expression.let-annotated) still types that
form for every τ, and its informative example
`let b: Bool := n in 0` is read by today's front ends, not by the Fren2
parser. Whether Fren2's `let` gets a written type, or the Core annotation
is restricted to `Bool`, is not decided.

```fren
pub fn suffix_rule?(question?, ty: Ty) := not question? or ty = Ty::Boolean

pub fn let_annotation?(written: Option<Ty>, question?, core: Option<Ty>) := match written {
    Some(annotation) => suffix_rule?(question?, annotation) and core = written,
    None => core = (if question? then Some(Ty::Boolean) else None),
}
```

r[names.surface.annotation] spec::names::parameter_type?
A parameter's type is its written annotation. An omitted parameter
annotation denotes `Bool` only when the parameter's name ends in `?`.

```fren
pub fn parameter_type?(written: Option<Ty>, question?, ty: Ty) :=
    suffix_rule?(question?, ty)
    and match written {
        Some(annotation) => ty = annotation,
        None => question?,
    }
```

## Scopes and levels

r[names.scope.levels] spec::names::{Scope, resolve_local}
A *scope* S is the snoc sequence of the names of the locals in scope,
oldest first. It is parallel to the typing context: the local whose name is
at level i of S has its type at level i of Γ. `S(x)` is the level of the
newest entry of S whose name is x, and is undefined when S has no such
entry.

```text
                       x ≠ y   S(x) = i
  (S, x)(x) = |S|      ────────────────
                       (S, y)(x) = i
```

```fren
pub type Scope := Snoc<String>

pub fn resolve_local(scope: Scope, name: String): Option<Int> := match scope {
    Empty => None,
    Extend(earlier, newest) =>
        if newest = name then Some(length(earlier)) else resolve_local(earlier, name),
}
```

r[names.locals.shadowing] spec::names::shadowing::{newest, passes}
A new binder of x *shadows* every earlier one: `(S, x)(x) = |S|`. A binder
of another name changes nothing: if `x ≠ y`, then `(S, y)(x) = S(x)`, so the
level that a name denotes does not change while its binder is in scope.

```fren
expect shadowing(scope: Scope, name: String, other: String) {
    expect newest: resolve_local(Extend(scope, name), name) = Some(length(scope))
    expect passes: when other != name,
        resolve_local(Extend(scope, other), name) = resolve_local(scope, name)
}
```

r[names.locals.nearest] spec::names::local_binding::{bound, nearest, complete}
If `S(x) = i`, then the entry at level i of S is x, so `0 ≤ i < |S|`, and
no entry at a level above i is x. If `S(x)` is undefined, then no entry of
S is x.

```fren
set_option fren.evidence "random" in
pub proc local_binding(scope: Scope, name: String, level: Int, other: Int): (holds?) {
    ensure output: holds?
    ensure bound: when resolve_local(scope, name) = Some(level), lookup(scope, level) = Some(name)
    ensure nearest: when resolve_local(scope, name) = Some(level) and level < other,
        lookup(scope, other) != Some(name)
    ensure complete: when resolve_local(scope, name) = None, lookup(scope, other) != Some(name)
}
```

r[names.locals.weakening] spec::names::{insert_name, shifted, local_weakening::shifted}
Inserting a binder of another name y at level n of S, with `0 ≤ n ≤ |S|`,
shifts the levels of at least n by one and changes nothing else: `S(x)` is
defined exactly when the new scope's is, and the new level is the old one
[shifted](#r-names.core.shift) at n, as [typing's
weakening](Types.md#r-types.layer.weakening) shifts a context's levels.

```fren
pub fn insert_name(scope: Scope, cutoff: Int, extra: String): Scope := match scope {
    Empty => if cutoff = 0 then Extend(Empty, extra) else Empty,
    Extend(earlier, name) =>
        if cutoff = length(earlier) + 1 then Extend(scope, extra)
        else Extend(insert_name(earlier, cutoff, extra), name),
}

pub fn shifted(level: Option<Int>, cutoff: Int): Option<Int> := match level {
    Some(found) => Some(shift(found, cutoff)),
    None => None,
}

set_option fren.evidence "random" in
pub proc local_weakening(scope: Scope, cutoff: Int, extra: String, name: String): (holds?) {
    ensure output: holds?
    ensure shifted: when 0 <= cutoff <= length(scope) and name != extra,
        resolve_local(insert_name(scope, cutoff, extra), name)
        = shifted(resolve_local(scope, name), cutoff)
}
```

r[names.primitive.nearest] spec::names::nearest_index::converse
The *index* of a local counts from the newest: the newest local has index
0. An index and a level name the same entry of a scope when they sum to
`|S| - 1`. The index of x in S is the one that corresponds to `S(x)`, and
is undefined when `S(x)` is.

```fren
pub proc nearest_index(scope: Scope, name: String): (index: Option<Int>) {
    ensure converse: index = match resolve_local(scope, name) {
        Some(level) => Some(length(scope) - 1 - level),
        None => None,
    }
}
```

r[names.primitive.duplicates] spec::names::same_name::{meaning, repeated, distinct}
Names are compared by spelling: two names are the same name exactly when
their spellings are equal. Every lookup and every duplicate check of this
chapter uses this one comparison.

```fren
pub proc same_name(first: String, second: String): (same?) {
    ensure meaning: same? iff first = second

    expect repeated: when first = second, same?
    expect distinct: when first != second, not same?
}
```

## Item identities

r[names.identity.child] spec::names::{child, identity::{injective, proper, deeper}}
The identity of a module is the sequence of names that leads to it. The
identity of an item x declared in the module m is `m · x`, the identity of
m extended by x, and the identity of a variant v of the enumeration a is
`a · v`. Extension is injective and lengthens the identity, so distinct
names of one parent have distinct identities, and a variant never has the
identity of an item of its enumeration's module.

```fren
-- Extension concatenates sequences, which is outside the decidable core;
-- the solver still proves the three laws below.
set_option fren.lint.undecidable "allow" in
pub fn child(parent: ItemId, name: String): ItemId := parent ++ [name]

expect identity(parent: ItemId, other: ItemId, name: String, second: String, third: String) {
    expect injective: when child(parent, name) = child(other, second),
        parent = other and name = second
    expect proper: child(parent, name) != parent
    expect deeper: child(child(parent, name), second) != child(parent, third)
}
```

r[names.environment.module] spec::names::{Env, module_of}
A *resolution environment* R is the identity of the module's parent, the
module's own name and a symbol environment Σ. The module's identity is its
parent's extended by its name. A module has one item namespace:
enumerations and functions are found by the same lookup, and a variant is
found only through its enumeration.

```fren
pub struct Env { parent: ItemId, name: String, symb: Symb }

pub fn module_of(env: Env): ItemId := child(env.parent, env.name)
```

## Paths

r[names.paths.syntax] spec::names::Target
A *path* is a name or a shorter path followed by `::` and a name; it is
the [syntax chapter's `Path`](Syntax.md#r-syntax.tree.types). A path
denotes a *target*: a local, by its level; an item, by its identity; or
the module itself.

```fren
pub enum Target { Local(Int), Item(ItemId), Module }
```

r[names.paths.head] spec::names::{item_target, head, item_first::shadows}
The first name x of a path resolves, in this order, to the local `S(x)`
when that is defined, else to the item `m · x` when Σ binds it, else to the
module when x is the module's own name. Locals therefore shadow items, and
items shadow the module's name.

```text
  S(x) = i                 S(x) undefined   Σ(m · x) defined
  ─────────────────────    ─────────────────────────────────
  R; S ⊢ x ⇒ local i       R; S ⊢ x ⇒ item m · x

  S(x) undefined   Σ(m · x) undefined   x is the name of m
  ────────────────────────────────────────────────────────
  R; S ⊢ x ⇒ module
```

```fren
pub fn item_target(symb: Symb, item: ItemId): Option<Target> := match entry(symb, item) {
    Some(_) => Some(Target::Item(item)),
    None => None,
}

pub fn head(env: Env, scope: Scope, name: String): Option<Target> :=
    match resolve_local(scope, name) {
        Some(level) => Some(Target::Local(level)),
        None => match item_target(env.symb, child(module_of(env), name)) {
            Some(target) => Some(target),
            None => if name = env.name then Some(Target::Module) else None,
        },
    }

expect item_first(env: Env, scope: Scope) {
    expect shadows: when resolve_local(scope, env.name) = None
        and entry(env.symb, child(module_of(env), env.name)) != None,
        head(env, scope, env.name) = Some(Target::Item(child(module_of(env), env.name)))
}
```

r[names.paths.members] spec::names::{descend, path_target}
Only the module and an enumeration have members. A member x of the module
is the item `m · x`; a member v of the enumeration a is its variant
`a · v`. A local has no members (`F0204`), and neither has a function or a
variant (`F0204`). A name that the module does not declare is an error
(`F0201`), with the message `cannot find NAME in module M`, where `NAME`
and the module's name `M` are displayed in backticks; a name that the
enumeration does not declare is an error (`F0203`). Qualification commits to the target of the shorter path: a
failed member is never retried in another scope.

```text
  R; S ⊢ p ⇒ module   Σ(m · x) defined
  ────────────────────────────────────
  R; S ⊢ p::x ⇒ item m · x

  R; S ⊢ p ⇒ item a   Σ(a) = enumeration   Σ(a · v) defined
  ─────────────────────────────────────────────────────────
  R; S ⊢ p::v ⇒ item a · v
```

```fren
pub fn descend(env: Env, target: Target, name: String): Option<Target> := match target {
    Target::Local(_) => None,
    Target::Module => item_target(env.symb, child(module_of(env), name)),
    Target::Item(item) => match entry(env.symb, item) {
        Some(ItemKind::Enumeration(_)) => item_target(env.symb, child(item, name)),
        _ => None,
    },
}

pub fn path_target(env: Env, scope: Scope, path: Path): Option<Target> := match path {
    Path::Name(name) => head(env, scope, name),
    Path::Member(qualifier, name) => match path_target(env, scope, qualifier) {
        Some(target) => descend(env, target, name),
        None => None,
    },
}
```

r[names.paths.unknown] spec::names::unknown::absent
A first name that is no local, no item and not the module's name is an
error (`F0201`) at that occurrence, with the message
`cannot find NAME in this scope`, where `NAME` is displayed in backticks.
No name is substituted for it and nothing is deferred to a later pass. A
first name has no target exactly when it is no local, Σ does not bind
`m · x` and it is not the module's name.

```fren
expect unknown(env: Env, scope: Scope, name: String) {
    expect absent: (head(env, scope, name) = None)
        iff (resolve_local(scope, name) = None
        and entry(env.symb, child(module_of(env), name)) = None
        and name != env.name)
}
```

r[names.paths.local-members] spec::names::local_members::{first, none}
A name with a binder in scope denotes that local, even when the module
declares an item of the name, and a local has no members: the path `x::y`
denotes nothing while a local `x` is in scope.

```fren
expect local_members(env: Env, scope: Scope, name: String, member: String, level: Int) {
    expect first: head(env, Extend(scope, name), name) = Some(Target::Local(length(scope)))
    expect none: descend(env, Target::Local(level), member) = None
}
```

r[names.paths.positions] spec::names::{value_form, callee_item, pattern_item}
What a path may denote depends on its position. In value position it
denotes a local, giving the Core local of that level, or a variant, giving
the Core constructor of that identity. The callee of a call denotes a
function. A match pattern denotes a variant (else `F0210`, `expected a
variant`). A path that denotes anything else has no resolution in that
position.

The value and callee conditions are what make the result a Core form: the
Core has no function as a value and no local or variant as a callee. They
have no diagnostic code of this chapter.

```fren
pub fn value_form<E>(env: Env, scope: Scope, path: Path): Option<CoreF<E>> :=
    match path_target(env, scope, path) {
        Some(Target::Local(level)) => Some(CoreF::Local(level)),
        Some(Target::Item(item)) => match entry(env.symb, item) {
            Some(ItemKind::Constructor(_)) => Some(CoreF::Constructor(item)),
            _ => None,
        },
        _ => None,
    }

pub fn callee_item(env: Env, scope: Scope, path: Path): Option<ItemId> :=
    match path_target(env, scope, path) {
        Some(Target::Item(item)) => match entry(env.symb, item) {
            Some(ItemKind::Function(_)) => Some(item),
            _ => None,
        },
        _ => None,
    }

pub fn pattern_item(env: Env, scope: Scope, path: Path): Option<ItemId> :=
    match path_target(env, scope, path) {
        Some(Target::Item(item)) => match entry(env.symb, item) {
            Some(ItemKind::Constructor(_)) => Some(item),
            _ => None,
        },
        _ => None,
    }
```

r[names.paths.types] spec::names::{type_item, resolve_type}
A written type, the [syntax chapter's
`TypeName`](Syntax.md#r-syntax.tree.types), is `Bool`, `Int` or a path. `Bool` and `Int` are
[reserved](#r-names.paths.reserved) and denote the built-in types. A path in type position resolves
in the empty scope, so no local is visible in it, and denotes an
enumeration a, giving the type `Nominal(a)` (else `F0210`, `expected a
type`).

```text
                                        R; · ⊢ p ⇒ item a   Σ(a) = enumeration
  R ⊢ Bool ⇒ Bool     R ⊢ Int ⇒ Int     ──────────────────────────────────────
                                        R ⊢ p ⇒ Nominal(a)
```

```fren
pub fn type_item(env: Env, path: Path): Option<ItemId> := match path_target(env, Empty, path) {
    Some(Target::Item(item)) => match entry(env.symb, item) {
        Some(ItemKind::Enumeration(_)) => Some(item),
        _ => None,
    },
    _ => None,
}

pub fn resolve_type(env: Env, written: TypeName): Option<Ty> := match written {
    TypeName::Boolean => Some(Ty::Boolean),
    TypeName::Integer => Some(Ty::Integer),
    TypeName::Named(path) => match type_item(env, path) {
        Some(item) => Some(Ty::Nominal(item)),
        None => None,
    },
}
```

r[names.paths.reserved] spec::names::reserved?
`Bool` and `Int` are [reserved names](Syntax.md#r-syntax.name.reserved),
which nothing that a module declares or binds takes: no enumeration,
variant, function, parameter or `let` binder is named `Bool` or `Int`
(`F0212`). [Collection](#r-names.collection.reserved) rejects the
declarations, and a [`let` layer](#r-names.expression.layer) whose binder
is reserved has no resolution. The syntax chapter also reserves these names
for a module, a global expectation and a member's label. That is open
here: this chapter's [domain](#r-names.overview.domain) has no expectation,
so it has neither an expectation's name nor a member's label to reject, and
`collect` does not inspect the module's name.

```fren
pub fn reserved?(name: String) := name is "Bool" | "Int"
```

## Expressions

r[names.expression.syntax]
A *source layer* is one written expression form over its children: a
value of the [syntax chapter's `SurfaceF<E>`](Syntax.md#r-syntax.tree.types),
where E is the position of a child. Resolution reads the tree that the
parser gives and has no expression type of its own. A source layer differs
from a [Core layer](#r-names.core.syntax) only where the Core has an
identity or a level: a source layer has a path in value position, a path
as a call's callee, a path as each arm's variant pattern, and a binder
name in a `let`.

r[names.expression.layer] spec::names::{resolve_arms, resolve_annotation, resolve_layer, let_handoff::{omitted, reserved}}
A source layer resolves, in R and S, to the Core layer of the same form
with the same children. Its paths resolve in S as their positions
require, and the layer has no resolution when one of them has none. A
`let` layer has no resolution when its binder's name is
[reserved](#r-names.paths.reserved). A written `let` has no type, and its
Core annotation is `Bool` when its binder's name ends in `?` and none
otherwise. That is the annotation which the
[suffix rule](#r-names.surface.suffix)'s `let_annotation?` admits for a
`let` without a written type, as `let_handoff` states. An earlier form of
this rule also resolved a written annotation: `let_handoff` had two more
guarantees, `kept` and `refused`, for an annotation that is kept and for
one that the suffix rule refuses, and the
[examples](#r-names.examples.positions) had `ANNOTATED_LET` and
`QUESTION_LET_REFUSED`. They are removed, since a `SurfaceF::Let` carries
no written type and they could no longer be stated; the annotated `let`
is [open](#r-names.surface.suffix).

```text
  R; S ⊢ p ⇒ local i      R; S ⊢ p ⇒ item c   Σ(c) = constructor
  ─────────────────       ──────────────────────────────────────
  R; S ⊢ p ⇒ #i           R; S ⊢ p ⇒ c

  R; S ⊢ p ⇒ item f   Σ(f) = function
  ─────────────────────────────────────
  R; S ⊢ p(e₀, …, eₙ) ⇒ f(e₀, …, eₙ)

  x is not reserved   x ends in `?`
  ───────────────────────────────────────────────
  R; S ⊢ let x := e₁ in e₂ ⇒ let Bool := e₁ in e₂

  x is not reserved   x does not end in `?`
  ─────────────────────────────────────────
  R; S ⊢ let x := e₁ in e₂ ⇒ let e₁ in e₂

  R; S ⊢ pₖ ⇒ item cₖ   Σ(cₖ) = constructor   (each k)
  ──────────────────────────────────────────────────────
  R; S ⊢ match e { p₀ => e₀, …, pₙ => eₙ }
           ⇒ match e { c₀ => e₀, …, cₙ => eₙ }
```

```fren
pub fn resolve_arms<E>(env: Env, scope: Scope, arms: Snoc<SurfaceArm<E>>): Option<Snoc<ArmF<E>>> :=
    match arms {
        Empty => Some(Empty),
        Extend(earlier, arm) =>
            match resolve_arms(env, scope, earlier), pattern_item(env, scope, arm.variant) {
                Some(resolved), Some(constructor) =>
                    Some(Extend(resolved, ArmF { constructor, body := arm.body })),
                _, _ => None,
            },
    }

pub fn resolve_annotation(binder: String): Option<Option<Ty>> :=
    if reserved?(binder) then None
    else Some(if binder.ends_with?("?") then Some(Ty::Boolean) else None)

pub fn resolve_layer<E>(env: Env, scope: Scope, form: SurfaceF<E>): Option<CoreF<E>> := match form {
    SurfaceF::Boolean(value?) => Some(CoreF::BooleanLiteral(value?)),
    SurfaceF::Integer(value) => Some(CoreF::IntegerLiteral(value)),
    SurfaceF::Name(path) => value_form(env, scope, path),
    SurfaceF::Unary(op, operand) => Some(CoreF::Unary(op, operand)),
    SurfaceF::Binary(op, left, right) => Some(CoreF::Binary(op, left, right)),
    SurfaceF::Call(path, args) => match callee_item(env, scope, path) {
        Some(item) => Some(CoreF::Call(item, args)),
        None => None,
    },
    SurfaceF::Let(name, value, body) => match resolve_annotation(name) {
        Some(core) => Some(CoreF::Let(core, value, body)),
        None => None,
    },
    SurfaceF::If(condition, then_branch, else_branch) =>
        Some(CoreF::If(condition, then_branch, else_branch)),
    SurfaceF::Match(scrutinee, arms) => match resolve_arms(env, scope, arms) {
        Some(resolved) => Some(CoreF::Match(scrutinee, resolved)),
        None => None,
    },
}

set_option fren.evidence "random" in
pub proc let_handoff(name: String, core: Option<Ty>): (holds?) {
    ensure output: holds?
    ensure omitted: when resolve_annotation(name) = Some(core),
        let_annotation?(None, name.ends_with?("?"), core)
    ensure reserved: when reserved?(name), resolve_annotation(name) = None
}
```

r[names.handoff.items] spec::names::bound_items::{constructor, function, pattern}
The items of a resolved layer are bound as typing requires: a resolved
constructor is bound in Σ as a constructor, a resolved callee as a
function, and the item of a resolved pattern as a constructor.

```fren
set_option fren.evidence "random" in
pub proc bound_items(
    env: Env,
    scope: Scope,
    form: SurfaceF<Int>,
    path: Path,
    args: Snoc<Int>,
    item: ItemId,
): (holds?) {
    ensure output: holds?
    ensure constructor: when resolve_layer(env, scope, form) = Some(CoreF::Constructor(item)),
        entry(env.symb, item) is Some(ItemKind::Constructor(_))
    ensure function: when resolve_layer(env, scope, form) = Some(CoreF::Call(item, args)),
        entry(env.symb, item) is Some(ItemKind::Function(_))
    ensure pattern: when pattern_item(env, scope, path) = Some(item),
        entry(env.symb, item) is Some(ItemKind::Constructor(_))
}
```

r[names.expression.weakening] spec::names::{path_head, arms_mention?, mentions?, shifted_form, layer_weakening::shifted}
A layer *mentions* a name when it is the first name of one of the layer's
paths in value, callee or pattern position. Inserting a binder of a name
that the layer does not mention at level n of S, with `0 ≤ n ≤ |S|`, shifts
the layer's resolution at n and changes nothing else, as
[`shift_form`](#r-names.core.shift) does. The law
for a whole table is [stated below](#r-names.expression.table-weakening).

```fren
pub fn path_head(path: Path): String := match path {
    Path::Name(name) => name,
    Path::Member(qualifier, _) => path_head(qualifier),
}

pub fn arms_mention?(arms: Snoc<SurfaceArm<Int>>, name: String) := match arms {
    Empty => false,
    Extend(earlier, arm) => path_head(arm.variant) = name or arms_mention?(earlier, name),
}

pub fn mentions?(form: SurfaceF<Int>, name: String) := match form {
    SurfaceF::Name(path) => path_head(path) = name,
    SurfaceF::Call(path, _) => path_head(path) = name,
    SurfaceF::Match(_, arms) => arms_mention?(arms, name),
    _ => false,
}

pub fn shifted_form(form: Option<Form>, cutoff: Int): Option<Form> := match form {
    Some(core) => Some(shift_form(core, cutoff)),
    None => None,
}

set_option fren.evidence "random" in
pub proc layer_weakening(env: Env, scope: Scope, form: SurfaceF<Int>, cutoff: Int, extra: String): (
    holds?,
) {
    ensure output: holds?
    ensure shifted: when 0 <= cutoff <= length(scope) and not mentions?(form, extra),
        resolve_layer(env, insert_name(scope, cutoff, extra), form)
        = shifted_form(resolve_layer(env, scope, form), cutoff)
}
```

r[names.expression.rows] spec::names::{SrcRow, has_scope?, arguments_scoped?, arms_scoped?, children_scoped?}
An expression is given as a *source table*: a snoc sequence of rows, each a
source layer whose children are the levels of earlier rows, with the scope
in which the layer is read. Every child of a layer is read in the layer's
own scope, with one exception: the body of `let x := e₁ in e₂` is read in
`S, x`, while e₁ is read in S. A child level that names no earlier row
fails.

```fren
pub struct SrcRow { form: SurfaceF<Int>, scope: Scope }

pub fn has_scope?(rows: Snoc<SrcRow>, position: Int, scope: Scope) := match lookup(rows, position) {
    Some(row) => row.scope = scope,
    None => false,
}

pub fn arguments_scoped?(rows: Snoc<SrcRow>, args: Snoc<Int>, scope: Scope) := match args {
    Empty => true,
    Extend(earlier, arg) =>
        arguments_scoped?(rows, earlier, scope) and has_scope?(rows, arg, scope),
}

pub fn arms_scoped?(rows: Snoc<SrcRow>, arms: Snoc<SurfaceArm<Int>>, scope: Scope) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        arms_scoped?(rows, earlier, scope) and has_scope?(rows, arm.body, scope),
}

pub fn children_scoped?(rows: Snoc<SrcRow>, scope: Scope, form: SurfaceF<Int>) := match form {
    SurfaceF::Unary(_, operand) => has_scope?(rows, operand, scope),
    SurfaceF::Binary(_, left, right) =>
        has_scope?(rows, left, scope) and has_scope?(rows, right, scope),
    SurfaceF::Call(_, args) => arguments_scoped?(rows, args, scope),
    SurfaceF::Let(name, value, body) =>
        has_scope?(rows, value, scope) and has_scope?(rows, body, Extend(scope, name)),
    SurfaceF::If(condition, then_branch, else_branch) =>
        has_scope?(rows, condition, scope)
        and has_scope?(rows, then_branch, scope)
        and has_scope?(rows, else_branch, scope),
    SurfaceF::Match(scrutinee, arms) =>
        has_scope?(rows, scrutinee, scope) and arms_scoped?(rows, arms, scope),
    _ => true,
}
```

r[names.locals.siblings] spec::names::siblings::{value, operand}
A binder is in scope only in its `let`'s body: the scope of a `let`'s
value, and of both operands of an operator, is the scope of the layer
itself, whatever its other children bind.

```fren
set_option fren.evidence "random" in
pub proc siblings(
    rows: Snoc<SrcRow>,
    scope: Scope,
    name: String,
    op: BinaryOp,
    first: Int,
    second: Int,
    row: SrcRow,
): (holds?) {
    ensure output: holds?
    ensure value: when children_scoped?(rows, scope, SurfaceF::Let(name, first, second))
        and lookup(rows, first) = Some(row),
        row.scope = scope
    ensure operand: when children_scoped?(rows, scope, SurfaceF::Binary(op, first, second))
        and lookup(rows, second) = Some(row),
        row.scope = scope
}
```

r[names.expression.table] spec::names::{resolve_rows, resolve_expression}
A source table resolves to the snoc sequence of its rows' Core layers, row
by row, when every row's children have their scopes and every row's layer
resolves; a resolved row keeps its level, so child levels mean the same in
both tables. An expression resolves in S when its table resolves and its
root, the last row, has scope S. Rows that no other row uses are resolved
too. A source table has at most one resolution, since `resolve_expression`
is a function.

```fren
pub fn resolve_rows(env: Env, rows: Snoc<SrcRow>): Option<Snoc<Form>> := match rows {
    Empty => Some(Empty),
    Extend(earlier, row) =>
        match resolve_rows(env, earlier), resolve_layer(env, row.scope, row.form) {
            Some(resolved), Some(form) =>
                if children_scoped?(earlier, row.scope, row.form) then Some(Extend(resolved, form))
                else None,
            _, _ => None,
        },
}

pub fn resolve_expression(env: Env, scope: Scope, rows: Snoc<SrcRow>): Option<Snoc<Form>> :=
    match rows {
        Empty => None,
        Extend(_, root) => if root.scope = scope then resolve_rows(env, rows) else None,
    }
```

r[names.expression.unfolding]
A row of a source table *unfolds* to the written expression whose root
form is the row's layer, with each child level replaced by the expression
that the row at that level unfolds to, and argument and arm sequences
replaced element by element. A child names only an earlier row, so
unfolding ends. A source table *denotes*, in the scope of its newest row,
the expression that this row unfolds to. `R; S ⊢ e ⇒ e'` holds when a
source table that denotes e in S resolves to a Core table whose newest row
[unfolds](Types.md#r-types.derivation.unfolding) to e'. Several tables
denote one expression: they differ in the order of their rows, in rows
that several occurrences share and in rows that no child names.

r[names.expression.unique-expression]
Resolution is deterministic for an expression: when two source tables
denote the same expression in the same scope and both resolve, the newest
rows of their results unfold alike. The [function of the
overview](#r-names.overview.function) gives determinism for one source
table only. This law across tables is stated here and open.

r[names.handoff.scoped] spec::names::table_scoping::{aligned, in_scope}
Resolution's result is well scoped for typing. A resolved table has one
Core layer for each source row, and every Core local `#i` of it lies in
the scope of its source row: `0 ≤ i < |S|`. A context parallel to that
scope therefore has an entry at level i, as the [local
rule](Types.md#r-types.expression.local) of typing requires.

```fren
set_option fren.evidence "random" in
pub proc table_scoping(
    env: Env,
    rows: Snoc<SrcRow>,
    forms: Snoc<Form>,
    position: Int,
    row: SrcRow,
    level: Int,
): (holds?) {
    ensure output: holds?
    ensure aligned: when resolve_rows(env, rows) = Some(forms), length(forms) = length(rows)
    ensure in_scope: when resolve_rows(env, rows) = Some(forms)
        and lookup(rows, position) = Some(row)
        and lookup(forms, position) = Some(CoreF::Local(level)),
        0 <= level < length(row.scope)
}
```

r[names.expression.table-weakening] spec::names::{weaken_rows, rows_admit?, shift_forms, shifted_forms, table_weakening::shifted}
Weakening extends from a layer to a table. A table *admits* a binder of
name x at level n when n is a level or the length of every row's scope and
no row mentions x. Inserting such a binder into the scope of every row,
with `0 ≤ n`, shifts every Core layer of the result at n and changes
nothing else: the weakened table resolves exactly when the table does.

```fren
pub fn weaken_rows(rows: Snoc<SrcRow>, cutoff: Int, extra: String): Snoc<SrcRow> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        weaken_rows(earlier, cutoff, extra),
        SrcRow {
            form := row.form,
            scope := insert_name(row.scope, cutoff, extra),
        }
    ),
}

pub fn rows_admit?(rows: Snoc<SrcRow>, cutoff: Int, extra: String) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        rows_admit?(earlier, cutoff, extra)
        and cutoff <= length(row.scope)
        and not mentions?(row.form, extra),
}

pub fn shift_forms(forms: Snoc<Form>, cutoff: Int): Snoc<Form> := match forms {
    Empty => Empty,
    Extend(earlier, form) => Extend(shift_forms(earlier, cutoff), shift_form(form, cutoff)),
}

pub fn shifted_forms(forms: Option<Snoc<Form>>, cutoff: Int): Option<Snoc<Form>> := match forms {
    Some(resolved) => Some(shift_forms(resolved, cutoff)),
    None => None,
}

set_option fren.evidence "random" in
pub proc table_weakening(env: Env, rows: Snoc<SrcRow>, cutoff: Int, extra: String): (holds?) {
    ensure output: holds?
    ensure shifted: when 0 <= cutoff and rows_admit?(rows, cutoff, extra),
        resolve_rows(env, weaken_rows(rows, cutoff, extra))
        = shifted_forms(resolve_rows(env, rows), cutoff)
}

trusted table_weakening: "open: weakening of a whole source table is proved in Lean only for one layer"
```

## Declarations and collection

r[names.collection.syntax] spec::names::{SrcDecl, decl_name, item_names, param_names}
A module's declarations are enumerations, each with a name and its
variants' names in written order, and functions, each with a name, its
parameters in written order, a written result type and the source table of
its body. A parameter is the [syntax chapter's
`Parameter`](Syntax.md#r-syntax.tree.types), with a name and an optional
written type. A `SrcDecl` is the syntax chapter's enumeration or function
declaration with its sequences as snoc sequences, over which collection
recurs, and with the function's body as a source table; the other fields
of a written declaration, such as `pub`, do not affect resolution.

`SrcDecl` is a second representation of a declaration, beside the syntax
chapter's `DeclarationF`, and no function of this chapter converts one to
the other. This is open: resolution should read the syntax chapter's
`FunctionDeclaration` and `EnumDeclaration`, with an explicit conversion
of their sequences to snoc sequences.

```fren
pub enum SrcDecl {
    Enumeration(String, Snoc<String>),
    Function(String, Snoc<Parameter>, TypeName, Snoc<SrcRow>),
}

pub fn decl_name(decl: SrcDecl): String := match decl {
    SrcDecl::Enumeration(name, _) => name,
    SrcDecl::Function(name, _, _, _) => name,
}

pub fn item_names(decls: Snoc<SrcDecl>): Scope := match decls {
    Empty => Empty,
    Extend(earlier, decl) => Extend(item_names(earlier), decl_name(decl)),
}

pub fn param_names(params: Snoc<Parameter>): Scope := match params {
    Empty => Empty,
    Extend(earlier, param) => Extend(param_names(earlier), param.name),
}
```

r[names.collection.reserved] spec::names::unreserved?
A sequence of names is *unreserved* when none of them is
[reserved](#r-names.paths.reserved). An enumeration, variant, function or
parameter named `Bool` or `Int` is an error (`F0212`).

```fren
pub fn unreserved?(names: Scope) := match names {
    Empty => true,
    Extend(earlier, name) => not reserved?(name) and unreserved?(earlier),
}
```

r[names.collection.members] spec::names::{distinct?, decl_names_ok?, decls_names_ok?}
The variant names of one enumeration are distinct, and so are the
parameter names of one function; a repeated name is an error (`F0213`).
Two enumerations may declare variants of the same name: their identities
differ. A declaration's *own names are admitted* when they are distinct
and unreserved and the declaration's name is not reserved.

```fren
pub fn distinct?(names: Scope) := match names {
    Empty => true,
    Extend(earlier, name) => resolve_local(earlier, name) = None and distinct?(earlier),
}

pub fn decl_names_ok?(decl: SrcDecl) := match decl {
    SrcDecl::Enumeration(name, variants) =>
        not reserved?(name) and unreserved?(variants) and distinct?(variants),
    SrcDecl::Function(name, params, _, _) =>
        not reserved?(name) and unreserved?(param_names(params)) and distinct?(param_names(params)),
}

pub fn decls_names_ok?(decls: Snoc<SrcDecl>) := match decls {
    Empty => true,
    Extend(earlier, decl) => decls_names_ok?(earlier) and decl_names_ok?(decl),
}
```

r[names.collection.duplicates] spec::names::names_ok?
Two declarations of one module with the same name are an error (`F0206`),
whatever their kinds and order. A sequence of declarations has *no naming
error* when its declarations' names are distinct and each declaration's
own names are admitted.

```fren
pub fn names_ok?(decls: Snoc<SrcDecl>) := distinct?(item_names(decls)) and decls_names_ok?(decls)
```

r[names.collection.function-types] spec::names::{declares_function?, type_clear?, annotation_clear?, params_clear?, decls_clear?, admitted?}
Collection resolves the written types of signatures in the environment Σ₀
of the module's enumerations, [defined below](#r-names.collection.complete),
which binds no function; every other name resolves in the whole
environment Σ. The two agree on a written type unless its first name is
the name of a function of the module. In Σ that name selects the function
before the module's own name ([path heads](#r-names.paths.head)), and a
function is not a type (`F0210`) and has no members (`F0204`); in Σ₀ it
could select the module. A written type is *clear* when its first name is
not the name of a function of the module. A sequence of declarations is
*admitted* when it has no naming error and every written type of its
signatures is clear, which is the condition under which [Σ₀ and Σ
agree](#r-names.collection.agreement) on those types; collection yields no environment
for a sequence that is not admitted.

```fren
pub fn declares_function?(decls: Snoc<SrcDecl>, name: String) := match decls {
    Empty => false,
    Extend(earlier, decl) => match decl {
        SrcDecl::Enumeration(_, _) => declares_function?(earlier, name),
        SrcDecl::Function(function, _, _, _) =>
            function = name or declares_function?(earlier, name),
    },
}

pub fn type_clear?(all: Snoc<SrcDecl>, written: TypeName) := match written {
    TypeName::Named(path) => not declares_function?(all, path_head(path)),
    _ => true,
}

pub fn annotation_clear?(all: Snoc<SrcDecl>, annotation: Option<TypeName>) := match annotation {
    Some(written) => type_clear?(all, written),
    None => true,
}

pub fn params_clear?(all: Snoc<SrcDecl>, params: Snoc<Parameter>) := match params {
    Empty => true,
    Extend(earlier, param) =>
        params_clear?(all, earlier) and annotation_clear?(all, param.annotation),
}

pub fn decls_clear?(all: Snoc<SrcDecl>, decls: Snoc<SrcDecl>) := match decls {
    Empty => true,
    Extend(earlier, decl) => match decl {
        SrcDecl::Enumeration(_, _) => decls_clear?(all, earlier),
        SrcDecl::Function(_, params, result, _) =>
            decls_clear?(all, earlier) and params_clear?(all, params) and type_clear?(all, result),
    },
}

pub fn admitted?(decls: Snoc<SrcDecl>) := names_ok?(decls) and decls_clear?(decls, decls)
```

r[names.collection.complete] spec::names::{constructors, bind_constructors, collect_types}
Collection has two steps, and both read every declaration before any body
is resolved, so a declaration is visible in the whole module, before and
after the place where it is written. The first step binds every
enumeration `a = m · x` with its variants' identities in written order,
and each variant `a · v` as a constructor of a.

```fren
pub fn constructors(owner: ItemId, variants: Snoc<String>): Snoc<ItemId> := match variants {
    Empty => Empty,
    Extend(earlier, variant) => Extend(constructors(owner, earlier), child(owner, variant)),
}

pub fn bind_constructors(symb: Symb, owner: ItemId, variants: Snoc<String>): Symb :=
    match variants {
        Empty => symb,
        Extend(earlier, variant) => Extend(
            bind_constructors(symb, owner, earlier),
            Entry {
                item := child(owner, variant),
                kind := ItemKind::Constructor(owner),
            }
        ),
    }

pub fn collect_types(module: ItemId, decls: Snoc<SrcDecl>): Symb := match decls {
    Empty => Empty,
    Extend(earlier, decl) => match decl {
        SrcDecl::Enumeration(name, variants) => bind_constructors(
            Extend(
                collect_types(module, earlier),
                Entry {
                    item := child(module, name),
                    kind := ItemKind::Enumeration(constructors(child(module, name), variants)),
                }
            ),
            child(module, name),
            variants
        ),
        SrcDecl::Function(_, _, _, _) => collect_types(module, earlier),
    },
}
```

r[names.collection.functions] spec::names::{param_type, resolve_params, signature, collect_functions, collect}
The second step binds every function `m · f` with its signature. The
written types of its parameters and result resolve in the environment Σ₀
of the first step, which binds every enumeration of the module; no
parameter is in scope in them. A parameter's type is its written type,
which must be `Bool` when the parameter's name ends in `?`. A parameter
written without a type must have a name that ends in `?`, and its type is
`Bool`. These are the conditions of the [parameter
rule](#r-names.surface.annotation), which the Core, having no
names, cannot decide. The signature's parameter context has the
parameters' types in written order. Collection yields the environment of
both steps, and yields none when the declarations are not admitted or a
parameter or result has no type.

```text
  ds is admitted   m ⊢ ds ⇒ Σ₀ (enumerations and variants)
  for each function f(x₀: T₀, …, xₙ: Tₙ): T of ds:
    (m, Σ₀) ⊢ Tₖ ⇒ τₖ (each k)   (m, Σ₀) ⊢ T ⇒ τ
    xₖ does not end in `?`, or τₖ = Bool (each k)
  ─────────────────────────────────────────────────────
  m ⊢ ds ⇒ Σ₀, …, m · f = function (τ₀, …, τₙ) → τ, …
```

```fren
pub fn param_type(env: Env, param: Parameter): Option<Ty> := match param.annotation {
    Some(written) => match resolve_type(env, written) {
        Some(ty) => if suffix_rule?(param.name.ends_with?("?"), ty) then Some(ty) else None,
        None => None,
    },
    None => if param.name.ends_with?("?") then Some(Ty::Boolean) else None,
}

pub fn resolve_params(env: Env, params: Snoc<Parameter>): Option<Ctx> := match params {
    Empty => Some(Empty),
    Extend(earlier, param) => match resolve_params(env, earlier), param_type(env, param) {
        Some(ctx), Some(ty) => Some(Extend(ctx, ty)),
        _, _ => None,
    },
}

pub fn signature(env: Env, params: Snoc<Parameter>, result: TypeName): Option<Sig> :=
    match resolve_params(env, params), resolve_type(env, result) {
        Some(ctx), Some(ty) => Some(Sig { params := ctx, result := ty }),
        _, _ => None,
    }

pub fn collect_functions(env: Env, decls: Snoc<SrcDecl>): Option<Symb> := match decls {
    Empty => Some(env.symb),
    Extend(earlier, decl) => match decl {
        SrcDecl::Enumeration(_, _) => collect_functions(env, earlier),
        SrcDecl::Function(name, params, result, _) =>
            match collect_functions(env, earlier), signature(env, params, result) {
                Some(symb), Some(sig) => Some(
                    Extend(
                        symb,
                        Entry {
                            item := child(module_of(env), name),
                            kind := ItemKind::Function(sig),
                        }
                    )
                ),
                _, _ => None,
            },
    },
}

pub fn collect(parent: ItemId, name: String, decls: Snoc<SrcDecl>): Option<Symb> :=
    if admitted?(decls) then collect_functions(
        Env {
            parent,
            name,
            symb := collect_types(child(parent, name), decls),
        },
        decls
    )
    else None
```

r[names.collection.parameters] spec::names::parameter_handoff::{omitted, kept, refused}
A parameter's type is one that [`parameter_type?`](#r-names.surface.annotation) admits for its
name and written type, and a parameter whose name ends in `?` and whose
written type resolves to another type than `Bool` has none.

```fren
set_option fren.evidence "random" in
pub proc parameter_handoff(env: Env, name: String, written: TypeName, annotation: Ty, ty: Ty): (
    holds?,
) {
    ensure output: holds?
    ensure omitted: when param_type(env, Parameter { name, annotation := None }) = Some(ty),
        parameter_type?(None, name.ends_with?("?"), ty)
    ensure kept: when resolve_type(env, written) = Some(annotation)
        and param_type(env, Parameter { name, annotation := Some(written) }) = Some(ty),
        parameter_type?(Some(annotation), name.ends_with?("?"), ty)
    ensure refused: when resolve_type(env, written) = Some(annotation)
        and not suffix_rule?(name.ends_with?("?"), annotation),
        param_type(env, Parameter { name, annotation := Some(written) }) = None
}
```

r[names.collection.agreement] spec::names::signature_agreement::agree
When collection yields Σ, a clear written type resolves in Σ₀ exactly as
it does in Σ. Every written type of a signature is clear, so the
signatures that collection computes in Σ₀ are the ones that the whole
environment gives.

```fren
set_option fren.evidence "random" in
pub proc signature_agreement(
    parent: ItemId,
    name: String,
    decls: Snoc<SrcDecl>,
    symb: Symb,
    written: TypeName,
): (holds?) {
    ensure output: holds?
    ensure agree: when collect(parent, name, decls) = Some(symb) and type_clear?(decls, written),
        resolve_type(
            Env {
                parent,
                name,
                symb := collect_types(child(parent, name), decls),
            },
            written
        )
        = resolve_type(Env { parent, name, symb }, written)
}
```

r[names.collection.rejected] spec::names::rejected::{duplicate, repeated_variant, reserved_name, reserved_function, reserved_parameter, repeated_parameter, function_as_qualifier}
Collection yields no environment for two declarations of one name, for an
enumeration with a repeated variant, for an enumeration named `Bool`, for
a function named `Int` or with a parameter named `Bool`, or for a function
with a repeated parameter. It yields none either for a
module `M` that declares a function `M` and a signature with the written
type `M::E`: there `M` is the function, which has no member.

```fren
set_option fren.evidence "random" in
pub proc rejected(
    parent: ItemId,
    module: String,
    name: String,
    variant: String,
    first: Snoc<String>,
    second: Snoc<String>,
    ty: TypeName,
    body: Snoc<SrcRow>,
): (holds?) {
    ensure output: holds?
    ensure duplicate: collect(
        parent,
        module,
        Extend(
            Extend(Empty, SrcDecl::Enumeration(name, first)),
            SrcDecl::Enumeration(name, second)
        )
    ) = None
    ensure repeated_variant: collect(
        parent,
        module,
        Extend(
            Empty,
            SrcDecl::Enumeration(name, Extend(Extend(Empty, variant), variant))
        )
    ) = None
    ensure reserved_name: collect(
        parent,
        module,
        Extend(Empty, SrcDecl::Enumeration("Bool", first))
    )
        = None
    ensure reserved_function: collect(
        parent,
        module,
        Extend(
            Empty,
            SrcDecl::Function(
                "Int",
                Extend(Empty, Parameter { name := variant, annotation := Some(ty) }),
                ty,
                body
            )
        )
    ) = None
    ensure reserved_parameter: collect(
        parent,
        module,
        Extend(
            Empty,
            SrcDecl::Function(
                name,
                Extend(Empty, Parameter { name := "Bool", annotation := Some(ty) }),
                ty,
                body
            )
        )
    ) = None
    ensure repeated_parameter: collect(
        parent,
        module,
        Extend(
            Empty,
            SrcDecl::Function(
                name,
                Extend(
                    Extend(Empty, Parameter { name := variant, annotation := Some(ty) }),
                    Parameter { name := variant, annotation := Some(ty) }
                ),
                ty,
                body
            )
        )
    ) = None
    ensure function_as_qualifier: collect(
        parent,
        module,
        Extend(
            Extend(Empty, SrcDecl::Enumeration(name, first)),
            SrcDecl::Function(
                module,
                Empty,
                TypeName::Named(Path::Member(Path::Name(module), name)),
                body
            )
        )
    ) = None
}
```

r[names.collection.order] spec::names::collection_order::{accepted, bindings}
Collection does not depend on the order of declarations: exchanging the
last two declarations changes neither whether collection yields an
environment nor what that environment binds to any identity. The
[next rule](#r-names.collection.permutation) states the law for every
reordering.

```fren
set_option fren.evidence "random" in
pub proc collection_order(
    parent: ItemId,
    name: String,
    decls: Snoc<SrcDecl>,
    first: SrcDecl,
    second: SrcDecl,
    left: Symb,
    right: Symb,
    item: ItemId,
): (holds?) {
    ensure output: holds?
    ensure accepted: (collect(parent, name, Extend(Extend(decls, first), second)) = None)
        iff (collect(parent, name, Extend(Extend(decls, second), first)) = None)
    ensure bindings: when collect(parent, name, Extend(Extend(decls, first), second)) = Some(left)
        and collect(parent, name, Extend(Extend(decls, second), first)) = Some(right),
        entry(left, item) = entry(right, item)
}
```

r[names.collection.permutation] spec::names::{declares?, included?, same_declarations?, collection_permutation::{accepted, bindings}, naming_order::stable}
Two sequences have the *same declarations* when each declaration of one is
a declaration of the other. Two admitted sequences of the same
declarations collect alike: both yield an environment or neither does, and
the two environments bind every identity alike. An admitted sequence has
no repeated declaration, so a sequence of the same declarations and the
same length is a reordering of it, and it is admitted too. With that, every reordering of a module's
declarations is immaterial to collection.

```fren
pub fn declares?(decls: Snoc<SrcDecl>, decl: SrcDecl) := match decls {
    Empty => false,
    Extend(earlier, other) => other = decl or declares?(earlier, decl),
}

pub fn included?(first: Snoc<SrcDecl>, second: Snoc<SrcDecl>) := match first {
    Empty => true,
    Extend(earlier, decl) => included?(earlier, second) and declares?(second, decl),
}

pub fn same_declarations?(first: Snoc<SrcDecl>, second: Snoc<SrcDecl>) :=
    included?(first, second) and included?(second, first)

set_option fren.evidence "random" in
pub proc collection_permutation(
    parent: ItemId,
    name: String,
    first: Snoc<SrcDecl>,
    second: Snoc<SrcDecl>,
    left: Symb,
    right: Symb,
    item: ItemId,
): (holds?) {
    ensure output: holds?
    ensure accepted: when same_declarations?(first, second)
        and admitted?(first)
        and admitted?(second),
        (collect(parent, name, first) = None) iff (collect(parent, name, second) = None)
    ensure bindings: when same_declarations?(first, second)
        and collect(parent, name, first) = Some(left)
        and collect(parent, name, second) = Some(right),
        entry(left, item) = entry(right, item)
}

set_option fren.evidence "random" in
pub proc naming_order(first: Snoc<SrcDecl>, second: Snoc<SrcDecl>): (holds?) {
    ensure output: holds?
    ensure stable: when same_declarations?(first, second)
        and length(first) = length(second)
        and admitted?(first),
        admitted?(second)
}

trusted naming_order: "open: that a reordering of an admitted sequence of declarations is admitted is not yet proved in Lean"
```

r[names.handoff.environment] spec::names::collection_well_formed::well_formed
The environment that collection yields is well formed, `⊢ Σ ok`: it binds
each identity once, every signature's types name enumerations that it
binds, and every enumeration lists exactly its own constructors. This is
the premise that [typing assumes of
resolution](Types.md#r-types.symbols.resolution).

```fren
set_option fren.evidence "random" in
pub proc collection_well_formed(parent: ItemId, name: String, decls: Snoc<SrcDecl>, symb: Symb): (
    holds?,
) {
    ensure output: holds?
    ensure well_formed: when collect(parent, name, decls) = Some(symb), symb_ok?(symb)
}
```

r[names.locals.parameters] spec::names::{parameters_parallel::parallel, bodies_resolve?, module_resolves?}
A function's body resolves in the scope of its parameter names in written
order: the first parameter has level 0, and no other local is in scope.
That scope is parallel to the signature's parameter context, which has one
type for each parameter name. A module *resolves* when its declarations
collect to an environment Σ and every function's body resolves in
`(m, Σ)` and its parameter scope.

```fren
set_option fren.evidence "random" in
pub proc parameters_parallel(env: Env, params: Snoc<Parameter>, result: TypeName, sig: Sig): (
    holds?,
) {
    ensure output: holds?
    ensure parallel: when signature(env, params, result) = Some(sig),
        length(sig.params) = length(param_names(params))
}

pub fn bodies_resolve?(env: Env, decls: Snoc<SrcDecl>) := match decls {
    Empty => true,
    Extend(earlier, decl) =>
        bodies_resolve?(env, earlier)
        and match decl {
            SrcDecl::Enumeration(_, _) => true,
            SrcDecl::Function(_, params, _, body) =>
                resolve_expression(env, param_names(params), body) != None,
        },
}

pub fn module_resolves?(parent: ItemId, name: String, decls: Snoc<SrcDecl>) :=
    match collect(parent, name, decls) {
        Some(symb) => bodies_resolve?(Env { parent, name, symb }, decls),
        None => false,
    }
```

## Examples

r[names.examples.resolved] spec::names::{row, ROOT, LIGHT, LIGHT_RED, LIGHT_GREEN, LIGHT_PATH, RED_PATH, GREEN_PATH, NEXT_BODY, NEXT_DECLS, NEXT_SYMB, NEXT_ENV, NEXT_FORMS, COLLECT_EXAMPLE, BODY_EXAMPLE, MODULE_EXAMPLE, SHADOW_ROWS, SHADOW_EXAMPLE, SIBLING_ROWS, SIBLING_EXAMPLE, worked_examples::valid}
The module `M` declares `enum Light { Red, Green }` and

```text
  fn next(l: Light): Light :=
      match l { Light::Red => Light::Green, Light::Green => Light::Red }
```

Collection yields the environment that binds `M · Light` as an enumeration
listing `M · Light · Red` and `M · Light · Green`, both as its
constructors, and `M · next` as a function from `Nominal(M · Light)` to
`Nominal(M · Light)`. The body's table and its resolution, in the scope
`l`, are:

```text
  0   l                                    #0
  1   Light::Green                         M · Light · Green
  2   Light::Red                           M · Light · Red
  3   match 0 { Light::Red => 1,           match 0 { M · Light · Red => 1,
                Light::Green => 2 }                  M · Light · Green => 2 }
```

In `let x := 1 in let x := true in x` the last `x` is read in the scope
`x, x` and resolves to `#1`, the newer binder. In `(let x := 1 in x) + x`
the right operand is read in the empty scope, as its sibling's binder is
not in scope there, and has no resolution.

```fren
pub fn row(form: SurfaceF<Int>, scope: Scope): SrcRow := SrcRow { form, scope }

pub const ROOT: ItemId := []
pub const LIGHT: ItemId := ["M", "Light"]
pub const LIGHT_RED: ItemId := ["M", "Light", "Red"]
pub const LIGHT_GREEN: ItemId := ["M", "Light", "Green"]
pub const LIGHT_PATH: Path := Path::Name("Light")
pub const RED_PATH: Path := Path::Member(LIGHT_PATH, "Red")
pub const GREEN_PATH: Path := Path::Member(LIGHT_PATH, "Green")

pub const NEXT_BODY: Snoc<SrcRow> := four(
    row(SurfaceF::Name(Path::Name("l")), one("l")),
    row(SurfaceF::Name(GREEN_PATH), one("l")),
    row(SurfaceF::Name(RED_PATH), one("l")),
    row(
        SurfaceF::Match(
            0,
            two(
                SurfaceArm { variant := RED_PATH, body := 1 },
                SurfaceArm { variant := GREEN_PATH, body := 2 }
            )
        ),
        one("l")
    )
)

pub const NEXT_DECLS: Snoc<SrcDecl> := two(
    SrcDecl::Enumeration("Light", two("Red", "Green")),
    SrcDecl::Function(
        "next",
        one(
            Parameter {
                name := "l",
                annotation := Some(TypeName::Named(LIGHT_PATH)),
            }
        ),
        TypeName::Named(LIGHT_PATH),
        NEXT_BODY
    )
)

pub const NEXT_SYMB: Symb := four(
    Entry {
        item := LIGHT,
        kind := ItemKind::Enumeration(two(LIGHT_RED, LIGHT_GREEN)),
    },
    Entry {
        item := LIGHT_RED,
        kind := ItemKind::Constructor(LIGHT),
    },
    Entry {
        item := LIGHT_GREEN,
        kind := ItemKind::Constructor(LIGHT),
    },
    Entry {
        item := ["M", "next"],
        kind := ItemKind::Function(
            Sig {
                params := one(Ty::Nominal(LIGHT)),
                result := Ty::Nominal(LIGHT),
            }
        ),
    }
)

pub const NEXT_ENV: Env := Env {
    parent := ROOT,
    name := "M",
    symb := NEXT_SYMB,
}

pub const NEXT_FORMS: Snoc<Form> := four(
    CoreF::Local(0),
    CoreF::Constructor(LIGHT_GREEN),
    CoreF::Constructor(LIGHT_RED),
    CoreF::Match(
        0,
        two(
            ArmF { constructor := LIGHT_RED, body := 1 },
            ArmF { constructor := LIGHT_GREEN, body := 2 }
        )
    )
)

pub const COLLECT_EXAMPLE: Bool := collect(ROOT, "M", NEXT_DECLS) = Some(NEXT_SYMB)
pub const BODY_EXAMPLE: Bool := resolve_expression(NEXT_ENV, one("l"), NEXT_BODY) = Some(NEXT_FORMS)
pub const MODULE_EXAMPLE: Bool := module_resolves?(ROOT, "M", NEXT_DECLS)

pub const SHADOW_ROWS: Snoc<SrcRow> := Extend(
    four(
        row(SurfaceF::Integer(1), Empty),
        row(SurfaceF::Boolean(true), one("x")),
        row(SurfaceF::Name(Path::Name("x")), two("x", "x")),
        row(SurfaceF::Let("x", 1, 2), one("x"))
    ),
    row(SurfaceF::Let("x", 0, 3), Empty)
)

pub const SHADOW_EXAMPLE: Bool :=
    resolve_expression(NEXT_ENV, Empty, SHADOW_ROWS) = Some(
        Extend(
            four(
                CoreF::IntegerLiteral(1),
                CoreF::BooleanLiteral(true),
                CoreF::Local(1),
                CoreF::Let(None, 1, 2)
            ),
            CoreF::Let(None, 0, 3)
        )
    )

pub const SIBLING_ROWS: Snoc<SrcRow> := Extend(
    four(
        row(SurfaceF::Integer(1), Empty),
        row(SurfaceF::Name(Path::Name("x")), one("x")),
        row(SurfaceF::Let("x", 0, 1), Empty),
        row(SurfaceF::Name(Path::Name("x")), Empty)
    ),
    row(SurfaceF::Binary(BinaryOp::Add, 2, 3), Empty)
)

pub const SIBLING_EXAMPLE: Bool := resolve_expression(NEXT_ENV, Empty, SIBLING_ROWS) = None

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc worked_examples(): (holds?) {
    ensure output: holds?
    ensure valid: COLLECT_EXAMPLE
        and BODY_EXAMPLE
        and MODULE_EXAMPLE
        and SHADOW_EXAMPLE
        and SIBLING_EXAMPLE
}
```

r[names.examples.paths] spec::names::{target, LOCAL_SHADOWS_ITEM, QUALIFIED_VARIANT, FUNCTION_QUALIFIER, VARIANT_QUALIFIER, UNKNOWN_VARIANT, UNKNOWN_MEMBER, SELF_DECLS, ITEM_SHADOWS_MODULE, path_examples::valid}
In the module `M` above:

- in the scope `next`, the name `next` denotes the local at level 0, not
  the function `M · next`: a local shadows an item;
- `M::Light::Red` denotes the variant `M · Light · Red`, as `Light::Red`
  does;
- `next::Red` and `Light::Red::Red` denote nothing, since a function and a
  variant have no members (`F0204`);
- `Light::Blue` denotes nothing, since `Light` declares no `Blue`
  (`F0203`), and neither does `M::Dark`, since `M` declares no `Dark`
  (`F0201`).

In a module `M` that declares only `enum M { A }`, the path `M::A` denotes
the variant `M · M · A`: its first name is the enumeration, which shadows
the module's name. Read from the module, `M::A` would be the item
`M · A`, which is not declared.

```fren
pub fn target(path: Path): Option<Target> := path_target(NEXT_ENV, Empty, path)

pub const LOCAL_SHADOWS_ITEM: Bool :=
    path_target(NEXT_ENV, one("next"), Path::Name("next")) = Some(Target::Local(0))
    and target(Path::Name("next")) = Some(Target::Item(["M", "next"]))

pub const QUALIFIED_VARIANT: Bool :=
    target(Path::Member(Path::Member(Path::Name("M"), "Light"), "Red"))
    = Some(Target::Item(LIGHT_RED))
    and target(RED_PATH) = Some(Target::Item(LIGHT_RED))

pub const FUNCTION_QUALIFIER: Bool := target(Path::Member(Path::Name("next"), "Red")) = None
pub const VARIANT_QUALIFIER: Bool := target(Path::Member(RED_PATH, "Red")) = None
pub const UNKNOWN_VARIANT: Bool := target(Path::Member(LIGHT_PATH, "Blue")) = None
pub const UNKNOWN_MEMBER: Bool := target(Path::Member(Path::Name("M"), "Dark")) = None

pub const SELF_DECLS: Snoc<SrcDecl> := one(SrcDecl::Enumeration("M", one("A")))

pub const ITEM_SHADOWS_MODULE: Bool := match collect(ROOT, "M", SELF_DECLS) {
    Some(symb) => path_target(
        Env { parent := ROOT, name := "M", symb },
        Empty,
        Path::Member(Path::Name("M"), "A")
    )
        = Some(Target::Item(["M", "M", "A"])),
    None => false,
}

set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc path_examples(): (holds?) {
    ensure output: holds?
    ensure valid: LOCAL_SHADOWS_ITEM
        and QUALIFIED_VARIANT
        and FUNCTION_QUALIFIER
        and VARIANT_QUALIFIER
        and UNKNOWN_VARIANT
        and UNKNOWN_MEMBER
        and ITEM_SHADOWS_MODULE
}
```

r[names.examples.positions] spec::names::{layer, CALL_EXAMPLE, LOCAL_CALLEE, FUNCTION_VALUE, NON_VARIANT_PATTERN, QUESTION_LET, RESERVED_LET, position_examples::valid}
Again in the module `M`, with the children of each layer at levels 0
and 1:

- in the scope `l`, the call `next(l)` resolves to the call of `M · next`;
- in the scope `next`, the callee of `next()` is the local, which is no
  function, so the call has no resolution;
- the name `next` in value position has no resolution, since a function is
  not a value;
- the pattern `Light` of `match l { Light => … }` denotes the enumeration,
  not a variant (`F0210`);
- `let x? := … in …` resolves with the annotation `Bool`;
- `let Int := … in …` has no resolution, since its binder is reserved.

```fren
pub fn layer(scope: Scope, form: SurfaceF<Int>): Option<Form> :=
    resolve_layer(NEXT_ENV, scope, form)

pub const CALL_EXAMPLE: Bool :=
    layer(one("l"), SurfaceF::Call(Path::Name("next"), one(0)))
    = Some(CoreF::Call(["M", "next"], one(0)))

pub const LOCAL_CALLEE: Bool := layer(one("next"), SurfaceF::Call(Path::Name("next"), Empty)) = None
pub const FUNCTION_VALUE: Bool := layer(Empty, SurfaceF::Name(Path::Name("next"))) = None

pub const NON_VARIANT_PATTERN: Bool :=
    layer(
        one("l"),
        SurfaceF::Match(0, one(SurfaceArm { variant := LIGHT_PATH, body := 1 }))
    ) = None

pub const QUESTION_LET: Bool :=
    layer(Empty, SurfaceF::Let("x?", 0, 1)) = Some(CoreF::Let(Some(Ty::Boolean), 0, 1))

pub const RESERVED_LET: Bool := layer(Empty, SurfaceF::Let("Int", 0, 1)) = None

set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc position_examples(): (holds?) {
    ensure output: holds?
    ensure valid: CALL_EXAMPLE
        and LOCAL_CALLEE
        and FUNCTION_VALUE
        and NON_VARIANT_PATTERN
        and QUESTION_LET
        and RESERVED_LET
}
```

## Informative source examples

These source programs are checked, with the diagnostics they expect, by
both of today's front ends. They are informative: no rule yet relates a
written source text to this chapter's source tables. The
[syntax chapter](Syntax.md) gives a text its tree, and that a source table
[denotes](#r-names.expression.unfolding) that tree's expression is stated
here, but the front ends that check these programs are not the Fren2
parser and are bound to neither.

```fren example
--@ reference: names.paths.unknown
pub mod bad

pub fn f(x: Int): Int := y + 1  --~ error: cannot find `y` in this scope
```

```fren example
--@ reference: names.collection.duplicates
pub mod duplicate

pub enum Light { Red }
pub enum Light { Green }  --~ error: the name `Light` is already defined in module `duplicate` (as an enum)
```

```fren example
--@ reference: names.collection.members
pub mod duplicate_variant

pub enum Light { Red, Red }  --~ error: variant `Red` is defined multiple times
```
