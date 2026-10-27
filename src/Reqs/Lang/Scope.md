# Scope

A name written alone, or as the first segment of a path, *resolves* to a
declaration in scope where it is written: the innermost of that name.
Which declarations are in scope, and which one a name resolves to, is
stated once, in this chapter, as a model that the other chapters
[instantiate](Calls.md): [shadowing](Procedures.md#shadowing), what an
identifier is in a [pattern](Patterns.md#kinds-of-pattern), [module
resolution](Modules.md#resolution), and the [layer](ScopeLaws.md#names-as-layers)
that a name is in the core of meaning.

```fren
pub mod lang
```

## Bindings

Names, of variables, functions, constants, variants and operators, are
`Id`s, `String`s as they are written, so that a payload can hold them:

```fren
pub type Id := String
```

A *binding* is one declaration in scope: its name, the kind of declaration
it is, what it declares (its *target*), and its *depth*, how many scopes
out from where the name is written it is declared, from 0. `lang::BindingKind`
is the kinds:

- `Input` and `Output`, a component's [variables](Procedures.md#members);
  `Parameter`, a [defined function's](Items.md#defined-functions)
  parameter; and `Instance`, a component's [instance](Calls.md); a
  [global expectation's](Global.md) parameters and calls are `Input` and
  `Instance`, as a procedure's are;
- `PatternBinder`, a binder of a [`match` arm](Expressions.md#matches) or
  of a [pattern test](Expressions.md#pattern-tests), whose target is where
  its pattern declares it, as a `Binder` [head](Meaning.md#layers) names
  it, such as `Reply::Value.0`; `BoundName`, a
  [quantifier's](Quantifiers.md#names) bound name; and `Definition`, a
  name of a [`let` or `where`](Let.md);
- `Builtin`, a [cardinality operator](Expressions.md#cardinality);
- `Constant` and `Function`, a [constant](Items.md#constants) and a
  [function](Items.md#functions); `Variant`, a variant imported by name;
  and `Opened`, a variant brought into scope by a glob import, `use E::*`;
- `Module`, `Enumeration` and `Item`, the items that are not values:
  modules, enumerations, and records, abstract types, components and
  global expectations.

The target of an item, imported or not, and of a variant, is its full
path, and that of any other binding but a binder its name. A new form that
declares names, such as a closure's parameters, adds its kind here, and
its scope to the list in [Scopes](#scopes).

```fren
pub enum BindingKind {
    Input,
    Output,
    Parameter,
    Instance,
    PatternBinder,
    BoundName,
    Definition,
    Builtin,
    Constant,
    Function,
    Variant,
    Opened,
    Module,
    Enumeration,
    Item,
}

pub struct Binding { name: Id, kind: BindingKind, target: Id, depth: Nat }

-- A binding names a value, which a declaration may hide: every binding but
-- the items that are not values, which are never named where a variable can be.
pub fn names_value?(k: BindingKind) := not k in {BindingKind::Module, BindingKind::Enumeration, BindingKind::Item}

-- A binding names a variant.
pub fn names_variant?(k: BindingKind) := k in {BindingKind::Variant, BindingKind::Opened}
```

## Scopes

The *scope* where a name is written is the set of the bindings there,
which `lang::context_scope` lists from a `lang::Context`: the declarations around
the name, by where they are declared. From the innermost, at depth 0, out:

1. The *locals*, one depth each, the last declared innermost. In order,
   from the outermost: the variables and instances of its component, the
   parameters of its function;
   then the names that the constructs around it declare, each in the order
   that it is written: the binders of the `match` arms it is in, the bound
   names of the quantifiers it is in, the names of the `let`s and `where`
   clauses it is in, of which a definition sees those before it in its own
   clause and not itself, and the binders of the pattern tests around it.
   A pattern test's binder is in scope only where
   [`lang::test_scope`](Expressions.md#pattern-tests) says, which its
   `Local`'s `visible?` records, as [`lang::test_local`](ScopeLaws.md)
   states. A function is not in scope in its own body.
2. The built-in functions, which are in every scope.
3. Within a component, the names its own `use` declarations import by
   name, and, one depth further out, those that its glob imports bring in.
4. The module's items declared before the name, and the names the module
   imports by name, and, one depth further out, those that the module's
   glob imports bring in. The items are in their declaration's order, and
   `declared` of them are declared before the name: those before the item
   it is written in, as [`lang::declared_before`](Items.md#items) orders
   them, and that item itself where it may contain itself, as a recursive
   enumeration does. So a later item is not in scope, and a declaration
   named like one hides nothing. A module's scope does not include its
   parent's.
5. The [prelude's](Prelude.md) items and variants, `Option`, `Result`,
   `None`, `Some`, `Ok` and `Err`, two depths further out than the
   module's items: below its glob imports, as `modules::resolve` says.

A declaration written `x!` enters the scope as `x`, one depth further in
than what it hides, which is why it hides it (see
[Shadowing](Procedures.md#shadowing)). The names of one depth are
distinct, as their declarations are checked to be (see [Distinct
names](Items.md#distinct-names)), except for those that glob imports bring
in: two enumerations opened in one scope may each have a variant of one
name. Opening one enumeration twice brings in each of its variants twice,
as one binding, since a scope is a set.

```fren
-- A declaration: its name, its kind and what it declares.
pub struct Declared { name: Id, kind: BindingKind, target: Id }

-- A local declaration, and whether it is in scope where the name is
-- written: `false` only for a pattern test's binder that `lang::test_scope`
-- does not show there.
pub struct Local { declaration: Declared, visible? }

-- What a `use` brings into scope, and whether by a glob.
pub struct Import { declaration: Declared, glob? }

pub struct Context {
    locals: Seq<Local>,              -- the locals, outermost first
    builtins: Seq<Id>,               -- the built-in functions
    component?,                -- it is written in a component
    component_imports: Seq<Import>,  -- what the component's `use`s bring in
    items: Seq<Declared>,         -- the module's items, in their declaration's order
    declared: Nat,                   -- how many of them are declared before the name
    module_imports: Seq<Import>,     -- what the module's `use`s bring in
    prelude: Seq<Declared>,          -- the prelude's items and variants
}

-- `b` is the binding of the declaration `d` at depth `k`.
pub fn binding_of?(d: Declared, k: Int, b: Binding) := b.name = d.name and b.kind = d.kind and b.target = d.target
    and b.depth = k

-- `b` is the binding of one of `imports`, at depth `k`, or `k + 1` for a glob's.
set_option fren.lint.undecidable "allow" in
pub fn imported?(imports: Seq<Import>, k: Int, b: Binding) := exists (i: Int), 0 <= i < imports.len
    and binding_of?(imports[i].declaration, if imports[i].glob? then k + 1 else k, b)

-- The depth of the module's items.
pub fn module_depth(cx: Context): Int := cx.locals.len + (if cx.component? then 3 else 1)

-- `b` is a binding of the scope `cx`.
set_option fren.lint.undecidable "allow" in
pub fn in_scope?(cx: Context, b: Binding) := (exists (i: Int), 0 <= i < cx.locals.len and cx.locals[i].visible?
    and binding_of?(cx.locals[i].declaration, cx.locals.len - 1 - i, b))
    or (exists (i: Int), 0 <= i < cx.builtins.len and b.kind = BindingKind::Builtin and b.name = cx.builtins[i]
    and b.target = cx.builtins[i] and b.depth = cx.locals.len)
    or (cx.component? and imported?(cx.component_imports, cx.locals.len + 1, b))
    or (exists (i: Int), 0 <= i < cx.items.len and i < cx.declared and binding_of?(cx.items[i], module_depth(cx), b))
    or imported?(cx.module_imports, module_depth(cx), b)
    or (exists (i: Int), 0 <= i < cx.prelude.len and binding_of?(cx.prelude[i], module_depth(cx) + 2, b))

-- The items and imports alone, without the locals and the built-in functions.
pub fn item_scope(cx: Context): Context := { cx with locals := [], builtins := [] }
```

`lang::context_scope` says which bindings the scope where a name is
written has, one binding at a time: it is the set of those for which
`listed?` holds, and the order it keeps is that of the context. An item
at the module's depth is one declared before the name, so a later item is
in no scope before it:

```fren
set_option fren.lint.undecidable "allow" in
pub proc context_scope(context: Context, binding: Binding): (det listed?) {
    out listed? := in_scope?(context, binding)

    -- An item at the module's depth is one declared before the name.
    expect declared_items: when listed? and binding.depth = module_depth(context)
        and not imported?(context.module_imports, module_depth(context), binding),
        exists (i: Int), 0 <= i < context.declared and i < context.items.len
        and binding_of?(context.items[i], binding.depth, binding)
    -- A binding further in than the built-in functions is the local at its
    -- depth, which is visible there.
    expect locals_exact: when listed? and binding.depth < context.locals.len,
        context.locals[context.locals.len - 1 - binding.depth].visible?
        and binding.name = context.locals[context.locals.len - 1 - binding.depth].declaration.name
        and binding.kind = context.locals[context.locals.len - 1 - binding.depth].declaration.kind
        and binding.target = context.locals[context.locals.len - 1 - binding.depth].declaration.target
    -- A binding at the built-in functions' depth is one of them.
    expect builtins_exact: when listed? and binding.depth = context.locals.len,
        binding.kind = BindingKind::Builtin and binding.name = binding.target and binding.name in context.builtins
    -- The last local declared, if visible, is the innermost binding, and
    -- the first declared the outermost of the locals.
    expect last_local: when context.locals != [] and context.locals[context.locals.len - 1].visible?
        and binding.name = context.locals[context.locals.len - 1].declaration.name
        and binding.kind = context.locals[context.locals.len - 1].declaration.kind
        and binding.target = context.locals[context.locals.len - 1].declaration.target and binding.depth = 0,
        listed?
    expect first_local: when context.locals != [] and context.locals[0].visible?
        and binding_of?(context.locals[0].declaration, context.locals.len - 1, binding), listed?
    -- A glob import's variants are one depth further out than the module's items.
    expect glob_import: when context.module_imports != [] and context.module_imports[0].glob?
        and binding_of?(context.module_imports[0].declaration, module_depth(context) + 1, binding), listed?
    expect module_depths: module_depth(context) = context.locals.len + (if context.component? then 3 else 1)
    -- Nothing is in an empty scope, and the items and imports alone have no locals.
    expect empty: when context.locals = [] and context.builtins = [] and context.component_imports = []
        and context.items = [] and context.module_imports = [] and context.prelude = [], not listed?
    expect items_alone: item_scope(context).locals = [] and item_scope(context).builtins = []
        and item_scope(context).items = context.items
    -- The built-in functions are in every scope, just outside the locals.
    expect builtins: when binding.kind = BindingKind::Builtin and binding.name = binding.target
        and binding.depth = context.locals.len
        and (exists (i: Int), 0 <= i < context.builtins.len and context.builtins[i] = binding.name),
        listed?
}
```

The components below take a scope as the set of its bindings, which
`context_scope` lists from where they are written: each one's `impl`
builds its scope from a `Context` by the code that both front ends call,
`Context.bindings`, proved to list exactly the bindings for which
`listed?` holds.

## Resolution

A name resolves to the binding of that name at the least depth, its
*innermost*. Where several distinct bindings of the name are innermost,
which only glob imports allow, it is *ambiguous*, and where none has the
name, it is *unbound*. `lang::resolve` states this; it is a function with
a contract, as [`step`](Meaning.md#one-layer) is, since its postconditions
determine it: every finite set of bindings has a least depth among those of
a name, if any has it.

```fren
-- What a name resolves to: the kind of its binding, or that it is
-- ambiguous or unbound.
pub enum Lookup { Found(BindingKind), Ambiguous, Unbound }

-- `b` is a binding of `n` in `bindings` at the least depth of those of `n`.
set_option fren.lint.undecidable "allow" in
pub fn innermost?(bindings: Set<Binding>, b: Binding, n: Id) := b in bindings and b.name = n
    and (forall (c: Binding), when c in bindings and c.name = n, b.depth <= c.depth)

-- Some binding in `bindings` is of `n`.
set_option fren.lint.undecidable "allow" in
pub fn declared?(bindings: Set<Binding>, n: Id) := exists (b: Binding), b in bindings and b.name = n

-- `b` is the only innermost binding of `n`.
set_option fren.lint.undecidable "allow" in
pub fn resolves_to?(bindings: Set<Binding>, b: Binding, n: Id) := innermost?(bindings, b, n)
    and (forall (c: Binding), when innermost?(bindings, c, n), c = b)

set_option fren.lint.undecidable "allow" in
pub fn resolve(bindings: Set<Binding>, n: Id): Lookup
    ensure found: forall (b: Binding), when resolves_to?(bindings, b, n), resolve(bindings, n) = Lookup::Found(b.kind)
    ensure ambiguous: when (exists (b c: Binding), innermost?(bindings, b, n) and innermost?(bindings, c, n) and b != c),
    resolve(bindings, n) = Lookup::Ambiguous
    ensure unbound: unless declared?(bindings, n), resolve(bindings, n) = Lookup::Unbound
```

`lang::scope` is one name written in one scope, and what it resolves to.
It is what the chapters below instantiate, each with the scope it reads:

```fren
set_option fren.lint.undecidable "allow" in
pub proc scope(
    bindings: Set<Binding>,      -- the scope where the name is written
    name: Id,                    -- the name, without a `!`
): (det result: Lookup, det value?) {
    out result := resolve(bindings, name)
    -- It names a value, which a declaration of it would hide.
    out value? := match result {
        Lookup::Found(k) => names_value?(k),
        _ => false,
    }

    -- Only a name that is declared resolves.
    expect declared: when result is Lookup::Found(_) | Lookup::Ambiguous, declared?(bindings, name)
    -- The only binding of a name at depth 0, the innermost scope, is the one it resolves to.
    expect innermost_wins: forall (b: Binding), when b in bindings and b.name = name and b.depth = 0
        and (forall (c: Binding), when c in bindings and c.name = name and c.depth = 0, c = b),
        result = Lookup::Found(b.kind)
    -- A binding that only one other of its name is further in than is hidden by it.
    expect inner_hides: forall (b c: Binding), when b in bindings and c in bindings and b.name = name and c.name = name
        and b.depth < c.depth and (forall (d: Binding), when d in bindings and d.name = name, d = b or d = c),
        result = Lookup::Found(b.kind)
    -- An empty scope resolves nothing.
    expect empty: when bindings = {}, result = Lookup::Unbound
    -- Two variants of one name opened in the innermost scope that has it are ambiguous.
    expect two_opened: forall (b c: Binding), when innermost?(bindings, b, name) and innermost?(bindings, c, name)
        and b.kind = BindingKind::Opened and c.kind = BindingKind::Opened and b.target != c.target,
        result = Lookup::Ambiguous
}
```

`lint::Scoped`, an expression as the lints compare it (see [Expressions
as written](../Lint/Meaning.md#expressions-as-written)), has the binders
of pattern tests in scope where it is written, by their targets: the
slice of a scope that may differ between two places in one component.
Two things stand between it and this model. A `Binding` does not tell a
test's binder from a `match` arm's, both being `PatternBinder`s, so the
slice needs a kind of its own, or the `Local`'s place. And the front ends
give a local binding its name as its target, not where its pattern
declares it, since resolution reads only that it hides, so a `Scoped`'s
`scope` would need the front ends to record the pattern path.
