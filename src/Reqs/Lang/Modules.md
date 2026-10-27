# Modules and visibility

Modules group items and control their visibility. Fren's modules are
independent of Lean's namespaces and files.

```fren
pub mod modules

use lang
```

## Module declarations

```
module := ["pub"] "mod" path
```

`mod a::b` makes `a::b` the current module for the items that follow, up to
the next module declaration or the end of the Lean file (or of the input
file, for the [`fren` command](../Cli.md)). It declares `a` and `a::b` if
they do not exist yet. `pub mod` makes the last segment public. Each file
starts in the root module. A module may be entered any number of times.

## `use` declarations

```
use := "use" path ["::*" | "::{" path ("," path)* [","] "}"]
```

- `use a::b::c` brings the item `c` into scope in the current module, under
  the name `c`. It can also bring in a single variant:
  `use climate::Mode::Heat`.
- `use a::E::*` brings every variant of the enumeration `E` into scope. Only
  enumerations can be opened this way, and it does not bring `E` itself into
  scope. The [lint](../Lint/Style.md#glob-imports) `glob_imports` warns about it
  by default.
- `use a::{b, c::d}` is a group: it does what `use a::b` and `use a::c::d`
  would. A group names at least one path, may end with a `,`, and cannot
  contain `::*`. The names it brings into scope must be distinct, like those
  of separate `use` declarations.
- The path of a `use` declaration is absolute: it starts from the root
  module, unless its first segment is `self`, which stands for the current
  module.

A module's scope consists of the items declared in it and the names it
imports. It does not include the scope of its parent, so a module that
uses a name declared elsewhere must import it, even if its parent did.

### `use` in a component

A `use` declaration can also be a member of a component. It brings its names into
scope for that component's members, wherever they are written in it, and
nowhere else:

```text
comp methods {
    use self::Method::*
    in method: Method
    pub out arity: Int
    ensure rule: arity = match method { Len | Card => 0, _ => 1 }
}
```

A component's imports shadow its module's scope. This is a rule of
resolution, between two scopes, and takes no `!`, unlike a declaration that
[shadows](Components.md#shadowing) a name. The first segment of a
path in the component is resolved as in [Resolution](#resolution), first
among the component's imports alone, and only if it is unbound there,
in its module's scope. So a component can import `ValueType::BoolTy` even
though its module imports another `BoolTy`, or declares one. The names
that a component imports by name are distinct, as a module's are. The
component's imports follow the same rules as a module's: a path starts
from the root module or from `self`, which stands for the component's
module, and the [lints](../Lint/Unused.md#unused-imports) on imports apply to them.

## Visibility

An item is visible from the module that declares it, from that module's
descendants, and, if it is `pub`, from everywhere. A path must be visible
segment by segment: each segment must be visible from the module where the
path is written.

`modules::ModuleName` is the names of a spec's modules, and
`modules::descends?` says whether the first is a descendant of the second:
a submodule of it, at any depth. `modules::item_visible` decides whether one segment is visible, from
whether it is `pub`, the module that declares it, and the module where the
path is written:

```fren
pub type ModuleName

pub fn descends?(ModuleName, ModuleName)

pub comp item_visible {
    in is_pub?
    in owner: ModuleName  -- the module that declares the item
    in here: ModuleName   -- the module where the path is written
    in middle: ModuleName  -- any module, for `transitive`

    -- A submodule of a submodule is a submodule.
    assume transitive: when descends?(here, middle) and descends?(middle, owner), descends?(here, owner)
    pub out visible?

    ensure rule: visible? iff (is_pub? or here = owner or descends?(here, owner))

    expect private_hidden: when not is_pub? and here != owner and not descends?(here, owner), not visible?
    expect owner_sees_all: when here = owner, visible?
}

-- What a module sees, its submodules see.
expect visible_below: forall (a b: item_visible),
    when a.owner = b.owner and a.is_pub? = b.is_pub? and b.middle = a.here
    and descends?(b.here, a.here) and a.visible?,
    b.visible?
```

`descends?` is an uninterpreted function, so `transitive` states what
`visible_below` needs of it. It holds of the implementation's `descends?`,
which is "is a proper prefix of", and a relation's `closure` would say the
same thing, outside the [decidable core](Decidability.md#relations).

## Resolution

Unlike in a `use` declaration, a path in an expression or a type is not
absolute: its first segment is looked up in the current module's scope. So
to write `Mode` in a module other than the one that declares it, first
`use climate::Mode`.

Within a component, a path whose first segment names one of the component's
variables or instances refers to it, and likewise within a [global
expectation](Global.md), for its binders. Otherwise, the first segment
resolves as follows:

1. An item declared in the module, or imported by name, wins. There is at
   most one, since names in a scope are unique.
2. Otherwise, a name brought into scope by exactly one `use E::*` resolves
   to that variant. Opening the same enumeration twice counts once.
3. Otherwise, a name brought into scope by several `use ...::*` declarations
   for different enumerations is ambiguous. That is an error only where the
   name is used.
4. Otherwise, the name is unbound, which is an error.

These are the scopes 4 and 5 of [Scopes](Scope.md#scopes), read by
[`lang::scope`](Scope.md#resolution): an item declared in the module and a
name imported by name are bindings of one scope, so at most one of a name,
and the variants that the glob imports open are bindings of the scope
just outside it, where two distinct variants of a name are ambiguous. A
component's own imports are two scopes further in. `modules::resolve`
states the rule, from the items and imports in scope where the path is
written and its first segment:

```fren
pub enum Resolution { Local, Glob, Ambiguous, Unbound }

use self::Resolution::{Ambiguous, Glob, Local, Unbound}

-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub comp resolve {
    use lang::BindingKind::Opened
    in bindings: Set<lang::Binding>  -- the items and imports in scope where the path is written
    in name: lang::Id                -- its first segment

    pub det out lookup: lang::Lookup := first.result
    pub det out result: Resolution := match lookup {
        lang::Lookup::Found(Opened) => Glob,
        lang::Lookup::Found(_) => Local,
        lang::Lookup::Ambiguous => Ambiguous,
        lang::Lookup::Unbound => Unbound,
    }

    inst first: lang::scope { bindings, name }

    expect nothing_in_scope: when bindings = {}, result = Unbound
    -- A variant that only a glob import opens resolves through it.
    expect only_glob: forall (b: lang::Binding), when lang::resolves_to?(bindings, b, name) and b.kind = Opened,
        result = Glob
    -- An item or a name imported by name wins over the variants that glob imports open further out.
    expect local_wins: forall (b c: lang::Binding), when b in bindings and c in bindings and b.name = name
        and c.name = name and b.kind != Opened and c.kind = Opened and b.depth < c.depth
        and (forall (d: lang::Binding), when d in bindings and d.name = name, d = b or d = c),
        result = Local
    -- Two variants of one name, opened in the innermost scope that has it, are ambiguous.
    expect two_globs: forall (b c: lang::Binding), when lang::innermost?(bindings, b, name)
        and lang::innermost?(bindings, c, name) and b.kind = Opened and c.kind = Opened and b.target != c.target,
        result = Ambiguous
}
```

Each later segment names a member of what the previous segment resolved
to, and that member must be visible from here. The members of a module are
its items. The members of an enumeration are its variants, which are as
visible as the enumeration. The fields of a record are not members: they
are read with `.` (see [Records](Expressions.md#records)), not named by a
path. Nothing else has members. In particular, a
variant brought into scope by `use E::*` has no members.

`Kind` classifies what a segment resolves to when it is an item: `Other`
covers records, abstract types, functions, constants, components, global
expectations, and variants imported by name. `kind_of` is the `Kind` of
a binding's kind.

```fren
pub enum Kind { Module, Enum, Other }

use self::Kind::{Enum, Module, Other}

pub fn kind_of(k: lang::BindingKind): Kind := match k {
    lang::BindingKind::Module => Module,
    lang::BindingKind::Enumeration => Enum,
    _ => Other,
}
```

`modules::member` gives whether one later segment is accepted, from what
the previous segment resolved to and its members, as a scope of one
depth: a module's items, or an enumeration's variants.

```fren
-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub comp member {
    in parent: Kind                  -- what the previous segment resolved to
    in members: Set<lang::Binding>   -- its members
    in name: lang::Id                -- the segment
    in visible?                      -- for a module: that member is visible from here (`item_visible`)

    pub det out found? := segment.result is lang::Lookup::Found(_)  -- it has a member of this name
    pub det out accepted?

    inst segment: lang::scope { bindings := members, name }

    ensure rule: accepted? iff (found? and (if parent = Module then visible? else parent = Enum))

    expect only_modules_hide: when parent = Enum and found?, accepted?
    expect others_empty: when parent = Other, not accepted?
    expect no_members: when members = {}, not accepted?
}
```

`modules::two_segments` puts the two rules together for a path `a::b`.

```fren
-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub comp two_segments {
    in bindings: Set<lang::Binding>  -- the items and imports in scope where the path is written
    in a: lang::Id
    in members: Set<lang::Binding>   -- the members of what `a` resolves to
    in b: lang::Id
    in b_pub?                        -- that member is `pub`
    in b_owner: ModuleName           -- the module declaring `b`: `a`, if `a` is a module
    in here: ModuleName              -- the module where the path is written

    -- What `a` is, when it is declared or imported by name.
    pub det out a_kind: Kind := match first.lookup {
        lang::Lookup::Found(k) => kind_of(k),
        _ => Other,
    }
    pub det out accepted?

    inst first: resolve { bindings, name := a }
    inst seen: item_visible { is_pub? := b_pub?, owner := b_owner, here, middle := here }
    inst second: member { parent := a_kind, members, name := b, visible? := seen.visible? }

    ensure rule: accepted? iff (first.result = Local and second.accepted?)

    expect variants_have_no_members: when first.result != Local, not accepted?
    expect private_member: when a_kind = Module and not b_pub? and here != b_owner and not descends?(here, b_owner),
        not accepted?
    expect variants_visible: when a_kind = Enum and second.found?, accepted?
    expect unbound: when bindings = {}, not accepted?
}

#fren_check
```

## Across files

In Lean, a file sees the modules and items of the Lean files it imports, and
each file starts in the root module. With the `fren` command, the files
given are processed in order with one shared set of modules, and each file
starts in the root module.
