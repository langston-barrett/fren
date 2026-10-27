# Scope

A name written alone, or as the first segment of a path, *resolves* to a
declaration in scope where it is written: the innermost of that name.
Which declarations are in scope, and which one a name resolves to, is
stated once, in this chapter, as a model that the other chapters
[instantiate](Instances.md): [shadowing](Components.md#shadowing), what an
identifier is in a [pattern](Patterns.md#kinds-of-pattern), [module
resolution](Modules.md#resolution), and the [layer](Meaning.md#layers) that
a name is in the core of meaning.

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

- `Input` and `Output`, a component's [variables](Components.md#members);
  `Parameter`, a [defined function's](Items.md#defined-functions)
  parameter; `Instance`, a component's [instance](Instances.md); and
  `ExpectBinder`, a [global expectation's](Global.md) binder;
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
    ExpectBinder,
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

The *scope* where a name is written is the set of the bindings there.
From the innermost, at depth 0, out:

1. The names that the constructs around it declare, each construct one
   scope further out than the one within it: the binders of the `match`
   arms it is in, and of the pattern tests whose names are in scope there
   (see [`lang::test_scope`](Expressions.md#pattern-tests)); the bound names
   of the quantifiers it is in; and the names of the `let`s and `where`
   clauses it is in, of which a definition sees those before it in its
   own clause, and not itself.
2. The variables and instances of its component, the parameters of its
   function, or the binders of its global expectation. A function is not
   in scope in its own body.
3. The built-in functions, which are in every scope.
4. Within a component, the names its own `use` declarations import by
   name, and, one scope further out, those that its glob imports bring in.
5. The items declared in its module and the names the module imports by
   name, and, one scope further out, those that the module's glob imports
   bring in. A module's scope does not include its parent's.

The names of one scope are distinct, as their declarations are checked to
be (see [Distinct names](Items.md#distinct-names)), except for those that
glob imports bring in: two enumerations opened in one scope may each have
a variant of one name. Opening one enumeration twice brings in each of its
variants twice, as one binding, since a scope is a set.

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
pub comp scope {
    in bindings: Set<Binding>    -- the scope where the name is written
    in name: Id                  -- the name, without a `!`

    pub det out result: Lookup := resolve(bindings, name)
    -- It names a value, which a declaration of it would hide.
    pub det out value? := match result {
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
of pattern tests in scope where it is written, by their targets. In this
model, that set is the targets of its scope's bindings of kind
`PatternBinder` whose pattern is a test's rather than a `match` arm's:
the slice of a `lang::scope`'s `bindings` that may differ between two
places in one component, since every other binding is the same throughout
it.
