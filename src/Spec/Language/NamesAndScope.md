# Names and scope

Name resolution connects a written name to a declaration. A *scope* is the
set of declarations available at that occurrence. This chapter specifies
a single-file source domain; [HIR](../Compiler/Hir.md) describes the
resolved result. The parser already accepts these forms, including names
that will fail resolution. Parsing does not establish that a name exists.

## 1. Declarations and source scope

The source file starts with one `mod M` or `pub mod M`, where `M` is one
name. Its remaining declarations are payload-free enumerations,
expression-bodied functions, and global expectations with typed parameters.
Types are `Bool`, `Int` and named enumerations. Expressions are the forms
listed in [Syntax](Syntax.md).
The end-to-end programs use non-recursive functions. Resolving a
reference alone does not establish non-recursion.

r[names.walking.domain]
Resolution of this source domain accepts one complete file in the source domain
and reports unsupported module structure before treating it as resolved.

r[names.collection.complete]
The module's enumerations, functions and global expectations are collected
before any parameter annotation, result annotation or body is resolved.

r[names.collection.duplicates]
Two declarations with the same name in the module are an error (`F0206`),
independently of their kinds or source order.

r[names.collection.members]
Variant names within one enumeration and parameter names within one
parameter list are distinct; a repeated name is an error (`F0213`).

A module has one item namespace. A constructor belongs to its enumeration,
not directly to the module: `Light::Red` and `Signal::Red` are distinct.
Expectation member labels name checks, not expression variables. Labels
within an expectation are distinct, including conflicts with its parameters
(`F0213`); neither `assume` nor `expect` introduces a local expression slot.
No duplicate is resolved by choosing the first or last declaration. A failed
collection may retain data for diagnostics but cannot produce a successful
resolved module.

This order-free collection is intentional. Fren1's declaration-order
restriction is not the Fren2 rule. The following file must resolve even
though the function and enumeration are used before their declarations:

```text
pub mod signals
pub fn use_next(l: Light): Light := next(l)
expect forward(l: Light) { expect same: next(l) = next(l) }
pub fn next(l: Light): Light := Light::Red
pub enum Light { Red, Green }
```

## 2. Local scopes

A local context lists binder entries nearest first. A reference is a de
Bruijn index into that exact context, as in the
[binding contracts](../Compiler/Bindings.md#contexts-and-scope). An index
is not an item identity or a globally stable number for a binder.

r[names.locals.parameters]
All parameters are in scope in their function body or every member body of
their global expectation, with the last written parameter at index zero.

r[names.locals.annotations]
Parameter and result type annotations resolve in the collected module
scope, without the declaration's local parameter slots.

r[names.locals.let]
A `let x := value in body` resolves `value` in the incoming context and
`body` in that context extended by a newest slot named `x`.

r[names.locals.shadowing]
An unqualified expression name selects the nearest local with that spelling
before consulting the collected module items.

r[names.locals.siblings]
A local introduced inside one expression child or match arm is unavailable
in its siblings and outside that child or arm.

The current match patterns are qualified payload-free constructors. They
introduce zero binders. Each arm body starts in the scrutinee's incoming
context; a `let` inside an arm is lexical to that arm body. Payload patterns
and their binders require a later contract extension. Reusing a parameter's
name in a nested `let` is shadowing, not a same-list duplicate. The parser writes that name without Fren1's `!` shadowing suffix.

For `fn f(x: Int, y: Int): Int := let x := x + y in x + y`, the value's
context is `[y, x]`: its uses are indices 1 and 0. The body's context is
`[x(let), y, x(parameter)]`: its uses are 0 and 1. In
`let x := x in x` with no incoming `x` and no module item `x`, the value's
`x` is unknown; the body binder cannot resolve it.

## 3. Written paths and unknown names

A *qualified path* has segments separated by `::`. Looking up the head
selects a declaration; each following segment selects a member of that
declaration. Qualification does not search for an unrelated matching suffix.

r[names.paths.head]
An expression path resolves its head among nearest locals, module items,
and then the current module's own name, in that order.

r[names.paths.members]
Only a module or enumeration has path members in the source domain; module
members are its collected items and enumeration members are its variants.

r[names.paths.types]
A written named type resolves to an enumeration through the module scope;
the AST's built-in `Bool` and `Int` forms denote those built-in types.

r[names.paths.unknown]
An absent unqualified expression name is an error (`F0201`) at that written
occurrence, with the message `cannot find NAME in this scope` where `NAME`
is displayed in backticks.

The current module's name provides `signals::Light::Red` as well as
`Light::Red`. A nearer local named `Light` blocks `Light::Red`; it does not
silently fall back to the enumeration. Qualification through a local or a
function fails, and a missing variant fails. The resolver must return
diagnostic data for these failures, using the established diagnostic
catalogue; this source domain assigns no new diagnostic codes. A bare `Red` is
unknown unless it names a local or module item. There are no imports or
opened variants in this source domain.

A spelling is compared exactly, including a final `?`. The parser's implicit
`Bool` parameter annotation for `b?` remains distinct from a written
annotation; `b?: Int` resolves its written `Int`, leaving suffix/type
consistency to typing. Full paths such as `Int::T` are named type paths,
not a built-in type followed by ignored text. Redefining the built-in type
names as enumerations is outside this source domain.

## 4. Name equality and nearest lookup

These finite contracts isolate deciding facts. Integer atoms stand for
names compared only for equality. The output of each procedure is
constrained from its raw inputs; no caller-supplied "resolved" or "valid"
Boolean is assumed. They define equality and nearest-slot decisions used by the local-context
rules; the arbitrary-context closure is specified by the Lean obligation
listed in the development coverage document.

r[names.primitive.nearest] spec::names::nearest_two::{meaning, newest, older, absent, shadowed}
In a two-slot nearest-first context, lookup returns the first equal name,
or -1 when neither slot matches.

```fren
pub mod spec
pub mod spec::names

pub proc nearest_two(near: Int, far: Int, query: Int): (slot: Int) {
    ensure meaning: slot = if query = near then 0 else if query = far then 1 else -1

    expect newest: when query = near, slot = 0
    expect older: when query != near and query = far, slot = 1
    expect absent: when query != near and query != far, slot = -1
    expect shadowed: when near = far and query = far, slot != 1
}
```

r[names.primitive.duplicates] spec::names::same_scope::{meaning, repeated, distinct}
Two names declared in one scope conflict exactly when their spellings are
equal.

```fren
pub proc same_scope(first: Int, second: Int): (duplicate?) {
    ensure meaning: duplicate? iff first = second

    expect repeated: when first = second, duplicate?
    expect distinct: when first != second, not duplicate?
}
```

The wrapper defines the arbitrary-context nearest-name obligation in Lean
and proves fresh/older slot lookup facts about the existing binding core.
The finite Fren procedures are checked contracts, not production `impl`
bindings. Their examples establish consequences of the contracts, not that
a complete name-search traversal satisfies them.

## 5. Worked failures

These isolated examples pin the established messages.

```fren example
pub mod bad

pub fn f(x: Int): Int := y + 1  --~ error: cannot find `y` in this scope
```

The input parses successfully in Fren2. Resolution must fail at `y` with
`F0201`; it must not substitute `x`, invent a binder or defer the unknown
name to the solver.

```fren example
pub mod duplicate

pub enum Light { Red }
pub enum Light { Green }  --~ error: the name `Light` is already defined in module `duplicate` (as an enum)
```

```fren example
pub mod duplicate_variant

pub enum Light { Red, Red }  --~ error: variant `Red` is defined multiple times
```

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
