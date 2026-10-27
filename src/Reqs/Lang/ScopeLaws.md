# Laws of scope

This chapter ties the [scope](Scope.md) model to the chapters that it
comes before: where a pattern test's binders are in scope, and what layer
of the [core of meaning](Meaning.md#layers) a name is.

## Pattern tests

A pattern test's binders are in scope only in some places around the
test, as [`lang::test_scope`](Expressions.md#pattern-tests) states. In a
[scope](Scope.md#scopes), each is a `Local` whose `visible?` says whether
it is in scope where the name is written. `lang::test_local` is that
local, from where the test is and where the name is mentioned:

```fren
pub mod lang

pub proc test_local(
    declaration: Declared,    -- a binder of the test
    context: TestContext,        -- what the test's chain is a part of
    operands: Nat,               -- the chain's operands
    test_at: Nat,                -- the test's position among them, from 0
    site: Site,                  -- where the name is mentioned
): (det entry: Local) {
    assume within: test_at < operands
    assume binder: declaration.kind = BindingKind::PatternBinder

    out entry := Local { declaration, visible? := visibility.visible? }

    call visibility := test_scope(context, operands, test_at, site)

    -- A binder is in scope in a later operand of its chain, and not in an earlier one.
    expect later: when site is Site::Operand(k) and test_at < k < operands, entry.visible?
    expect earlier: when site is Site::Operand(k) and k <= test_at, not entry.visible?
    -- Nor beside the chain, in an `else` branch or anywhere else.
    expect outside: when site is Site::ElseBranch | Site::Outside, not entry.visible?
}
```

## Names as layers

A name written alone is the layer that its [binding](Scope.md#bindings)
says, `named_head`: a variable, a parameter, an instance, a global
expectation's binder or a bound name is a `Variable`, read from the
environment; a constant or a variant a `Constant`, by its full path; a
name of a `let` or `where` a `Definition`; and a binder a `Binder`, by
where its pattern declares it. A bound name of a listed type is replaced
by its value in each instance of its quantifier, so it is a `Bound` layer
there, and only an unbounded one is read from the environment. A
function, and an item that is not a value, is never a layer alone: it is
applied, or a path's first segment, and is a `Constant` by its path too.

```fren
pub fn named_head(b: Binding): Head := match b.kind {
    BindingKind::Input | BindingKind::Output | BindingKind::Parameter | BindingKind::Instance
    | BindingKind::ExpectBinder | BindingKind::BoundName => Head::Variable(b.name),
    BindingKind::Definition => Head::Definition(b.name),
    BindingKind::PatternBinder => Head::Binder(b.target),
    _ => Head::Constant(b.target),
}
```

`lang::named` is the layer of one name written alone:

```fren
pub proc named(
    binding: Binding,      -- what the name resolves to
): (det head: Head) {
    use self::BindingKind::{Constant, Input, Opened, Output, Variant}

    out head := named_head(binding)

    -- A component's variable is read from the environment, by its name, and
    -- a constant and a variant are not.
    expect read: when binding.kind in {Input, Output}, head = Head::Variable(binding.name)
    expect constant: when binding.kind in {Constant, Variant, Opened}, head = Head::Constant(binding.target)
    -- A binder is named by where its pattern declares it, and a name of a
    -- `let` by its name.
    expect binder: when binding.kind = BindingKind::PatternBinder, head = Head::Binder(binding.target)
    expect definition: when binding.kind = BindingKind::Definition, head = Head::Definition(binding.name)
}
```
