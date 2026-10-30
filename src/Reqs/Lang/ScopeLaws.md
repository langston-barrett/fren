# Laws of scope

This chapter ties the [scope](Scope.md) model to the chapters that it
comes before: where a pattern test's binders are in scope, and what
[expression](Semantics.md#abstract-syntax) a name is.

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

## Names as expressions

A name written alone elaborates to the [expression](Semantics.md#expressions)
that its [binding](Scope.md#bindings) says, `named_expr`: a variable, a
parameter, an instance, a global expectation's binder, a bound name, a
name of a `let` or `where` and a binder of a pattern are a `Var`, read from
the environment, which the procedure, a function's application, a
quantifier's instance, a `Let` or a `Match` binds; a variant, by its full
path, is a `Construct` without a payload; and a constant, by its full
path, is an `Apply` of its definition. A function, and an item that is not
a value, is never an expression alone: it is applied, or a path's first
segment.

```fren
-- The expression that a name written alone elaborates to, where
-- `definition` is the definition of a constant.
pub fn named_expr(b: Binding, definition: Expr): Expr := match b.kind {
    BindingKind::Variant | BindingKind::Opened => Expr::Construct(b.target, Expr::Nil),
    BindingKind::Constant | BindingKind::Function | BindingKind::Builtin | BindingKind::Module
    | BindingKind::Enumeration | BindingKind::Item => Expr::Apply(b.target, Expr::Nil, Params::Nil, definition),
    _ => Expr::Var(b.name),
}
```

`lang::named` is the expression of one name written alone:

```fren
pub proc named(
    binding: Binding,      -- what the name resolves to
    definition: Expr,      -- a constant's definition
): (det expr: Expr) {
    use self::BindingKind::{Constant, Definition, Input, Opened, Output, PatternBinder, Variant}

    out expr := named_expr(binding, definition)

    -- A component's variable is read from the environment, by its name, and
    -- a constant and a variant are not.
    expect read: when binding.kind in {Input, Output}, expr = Expr::Var(binding.name)
    expect constant: when binding.kind = Constant, expr = Expr::Apply(binding.target, Expr::Nil, Params::Nil, definition)
    expect variant: when binding.kind in {Variant, Opened}, expr = Expr::Construct(binding.target, Expr::Nil)
    -- A binder and a name of a `let` are read from the environment that
    -- their `Match` or `Let` extends, by their names.
    expect locals: when binding.kind in {PatternBinder, Definition}, expr = Expr::Var(binding.name)
}
```

So a constant has its definition's outcome in every environment, as
[Constants](Items.md#constants) states:

```fren
expect constant_value(binding: Binding, definition: Expr, i: Interp, env: Env) {
    assume constant: binding.kind = BindingKind::Constant
    call name := named(binding, definition)
    -- The constant has no arguments, whose list is `Nil`, and so no parameters.
    expect definition_outcome: eval(i, env, Expr::Nil) = Outcome::Defined(Value::Nil)
        and bind_params(Params::Nil, Value::Nil) = Env::Empty
        and eval(i, env, name.expr) = eval(i, Env::Empty, definition)
}
```

The Lean-hosted front end checks this chapter's procedures by name, since no
`#fren_check` of its Lean file comes after it, and one without a path would
check every earlier chapter again:

```fren
#fren_check test_local
#fren_check named
#fren_check constant_value
```
