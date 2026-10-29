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

### `use` in a procedure

A `use` declaration can also be a member of a procedure. It brings its
names into scope for that procedure's members, wherever they are written
in its block, and in its signature's types, and nowhere else:

```text
proc methods(method: Method): (arity: Int) {
    use self::Method::*
    ensure rule: arity = match method { Len | Card => 0, _ => 1 }
}
```

A procedure's imports shadow its module's scope. This is a rule of
resolution, between two scopes, and takes no `!`, unlike a declaration that
[shadows](Procedures.md#shadowing) a name. The first segment of a
path in the procedure is resolved as in [Resolution](#resolution), first
among the procedure's imports alone, and only if it is unbound there,
in its module's scope. So a procedure can import `ValueType::BoolTy` even
though its module imports another `BoolTy`, or declares one. The names
that a procedure imports by name are distinct, as a module's are. The
procedure's imports follow the same rules as a module's: a path starts
from the root module or from `self`, which stands for the procedure's
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

pub proc item_visible(
    is_pub?,
    owner: ModuleName,    -- the module that declares the item
    here: ModuleName,     -- the module where the path is written
    middle: ModuleName,    -- any module, for `transitive`
): (visible?) {
    -- A submodule of a submodule is a submodule.
    assume transitive: when descends?(here, middle) and descends?(middle, owner), descends?(here, owner)

    ensure rule: visible? iff (is_pub? or here = owner or descends?(here, owner))

    expect private_hidden: when not is_pub? and here != owner and not descends?(here, owner), not visible?
    expect owner_sees_all: when here = owner, visible?
}

-- What a module sees, its submodules see.
expect visible_below(
    a_is_pub?,
    a_owner: ModuleName,
    a_here: ModuleName,
    a_middle: ModuleName,
    b_is_pub?,
    b_owner: ModuleName,
    b_here: ModuleName,
    b_middle: ModuleName,
) {
    assume a_transitive: when descends?(a_here, a_middle) and descends?(a_middle, a_owner), descends?(a_here, a_owner)
    assume b_transitive: when descends?(b_here, b_middle) and descends?(b_middle, b_owner), descends?(b_here, b_owner)
    call a := item_visible(a_is_pub?, a_owner, a_here, a_middle)
    call b := item_visible(b_is_pub?, b_owner, b_here, b_middle)
    expect visible_below: when a.owner = b.owner and a.is_pub? = b.is_pub? and b.middle = a.here
        and descends?(b.here, a.here) and a.visible?,
        b.visible?
}
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

Within a procedure, a path whose first segment names one of the
procedure's parameters, results, variables or calls refers to it, and
likewise within a [global
expectation](Global.md), for its binders. Otherwise, the first segment
resolves as follows:

1. An item declared in the module, or imported by name, wins. There is at
   most one, since names in a scope are unique.
2. Otherwise, a name brought into scope by exactly one `use E::*` resolves
   to that variant. Opening the same enumeration twice counts once.
3. Otherwise, a name brought into scope by several `use ...::*` declarations
   for different enumerations is ambiguous. That is an error only where the
   name is used.
4. Otherwise, a name that the [prelude](Prelude.md) gives resolves to the
   prelude's item or variant: `Option` and `Result`, and their variants
   `None`, `Some`, `Ok` and `Err`, as Rust's prelude gives them.
5. Otherwise, the name is unbound, which is an error.

The prelude is so the outermost layer of every scope, below the module's
own items, its imports and the variants it opens, as Rust's is: a path
`Some(3)` or `Option::Some(3)` means the prelude's variant wherever nothing
else gives the name. An import, by name or with `*`, that brings in a name
that the prelude gives takes precedence over the prelude, as a component's
imports take precedence over its module's scope: a rule of resolution,
which takes no `!`. A declared item takes precedence too, but is written
with `!`, as `enum Option!<T> { ... }` is, since it shadows (see
[Shadowing](#shadowing-the-prelude)).

Over the [scope model](Scope.md), these are the scopes 3 to 5 of
[Scopes](Scope.md#scopes), `item_scope`,
read by [`lang::scope`](Scope.md#resolution): an item declared before the
path in the module and a name imported by name are bindings of one depth,
so at most one of a name, and the variants that the glob imports open are
bindings of the depth just outside it, where two distinct variants of a
name are ambiguous; the prelude is two depths further out than the items.
A component's own imports are two depths further in. `modules::resolve`
states the rule over the scope, from where the path is written and its
first segment, and the same scope without the prelude, `nearer`, whose
name resolves to nothing exactly where the prelude's item or variant is
the one it resolves to:

```fren
pub enum Resolution { Local, Glob, Ambiguous, Prelude, Unbound }

use self::Resolution::{Ambiguous, Glob, Local, Prelude, Unbound}

-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub proc resolve(
    bindings: Set<lang::Binding>,    -- the scope where it is written, `item_scope` of its context
    nearer: Set<lang::Binding>,      -- the same scope without the prelude
    name: lang::Id,                  -- its first segment
): (det lookup: lang::Lookup, det result: Resolution) {
    use lang::BindingKind::Opened

    -- The prelude is only added to the scope.
    assume nearer_inside: nearer subset bindings

    out lookup := first.result
    out result := match lookup {
        lang::Lookup::Found(Opened) => Glob,
        lang::Lookup::Found(_) => if inner.result = lang::Lookup::Unbound then Prelude else Local,
        lang::Lookup::Ambiguous => Ambiguous,
        lang::Lookup::Unbound => Unbound,
    }

    call first := lang::scope(bindings, name)
    call inner := lang::scope(nearer, name)

    expect nothing_in_scope: when bindings = {}, result = Unbound
    -- Rules 2 and 3: only a variant that a glob import opens resolves through it, and
    -- several are ambiguous.
    expect glob_opened: result = Glob iff lookup = lang::Lookup::Found(Opened)
    expect ambiguous_globs: result = Ambiguous iff lookup = lang::Lookup::Ambiguous
    -- A variant that only a glob import opens resolves through it.
    expect only_glob: forall (b: lang::Binding), when lang::resolves_to?(bindings, b, name) and b.kind = Opened,
        result = Glob
    -- An item or a name imported by name wins over the variants that glob imports open further out.
    expect local_wins: forall (b c: lang::Binding), when b in bindings and c in bindings and b.name = name
        and c.name = name and b.kind != Opened and c.kind = Opened and b.depth < c.depth and b in nearer
        and (forall (d: lang::Binding), when d in bindings and d.name = name, d = b or d = c),
        result = Local
    -- Two variants of one name, opened in the innermost scope that has it, are ambiguous.
    expect two_globs: forall (b c: lang::Binding), when lang::innermost?(bindings, b, name)
        and lang::innermost?(bindings, c, name) and b.kind = Opened and c.kind = Opened and b.target != c.target,
        result = Ambiguous
}
```

`modules::resolve_layers` states this rule over what each layer gives the
name: whether an item of that name is declared or imported by name
(`local?`), how many distinct variants of that name are opened (`n_glob`),
and whether the prelude gives the name (`prelude?`):

```fren
-- `n_glob` is an `Int`, as a sequence's length is (`first_segment`).
set_option fren.lint.manual_nat "allow" in
pub proc resolve_layers(
    local?,
    n_glob: Int,         -- distinct items of this name opened by `use ...::*`
    prelude?,            -- the prelude gives the name
): (result: Resolution) {
    assume counted: n_glob >= 0

    ensure local_wins: when local?, result = Local
    ensure glob: unless local?, when n_glob = 1, result = Glob
    ensure ambiguous: unless local?, when n_glob > 1, result = Ambiguous
    ensure prelude: unless local?, when n_glob = 0 and prelude?, result = Prelude
    ensure unbound: unless local?, when n_glob = 0 and not prelude?, result = Unbound

    expect glob_is_unique: when result = Glob, n_glob = 1
    expect prelude_is_last: when result = Prelude, not local? and n_glob = 0
}
```

`modules::first_segment` states how the first segment resolves, and to
what, over what each layer of its scope gives the name, innermost first:
the item declared in, or imported by name into, the scope; the distinct
variants that `use ...::*` opens; and the prelude's item or variant. Each
is a sequence of paths (`modules::Path`), of one path at most but for the
variants opened. It refines `modules::resolve_layers`. Comparing sequences is
outside the [decidable core](Decidability.md), so it opts out:

```fren
pub type Path

set_option fren.lint.undecidable "allow" in
pub proc first_segment(
    declared: Seq<Path>,           -- the item declared or imported by name
    opened: Seq<Path>,             -- the distinct variants that `use ...::*` opens
    prelude: Seq<Path>,            -- the prelude's item or variant
): (det result: Resolution, det target: Seq<Path>) {
    out result := if declared != [] then Local
        else if opened.len = 1 then Glob
        else if opened.len > 1 then Ambiguous
        else if prelude != [] then Prelude
        else Unbound
    -- What it resolves to: none if it is ambiguous or unbound.
    out target := if declared != [] then declared.at(0)
        else if opened.len = 1 then opened
        else if opened.len > 1 then []
        else prelude.at(0)

    expect declared_wins: when declared != [], target = declared.at(0)
    expect prelude_below_globs: when declared = [] and opened.len = 1, target = opened
    expect resolved_one: target.len <= 1
    expect resolved: target != [] iff not result in {Ambiguous, Unbound}
}

-- `local?` and `prelude?` are `Bool`s, which a comparison of sequences of
-- an abstract type, as `declared != []`, is not in Lean: so `len`.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.length_zero "allow" in
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.lint.eq_op "allow" in
set_option fren.lint.absurd_extreme_comparisons "allow" in
expect first_resolve(declared: Seq<modules::Path>, opened: Seq<modules::Path>, prelude: Seq<modules::Path>) {
    use modules
    assume spec_counted: ((opened).len) >= 0
    call concrete := first_segment(declared, opened, prelude)
    expect local_wins: when ((declared).len > 0), (concrete.result) = modules::Resolution::Local
    expect glob: unless ((declared).len > 0), when ((opened).len) = 1, (concrete.result) = modules::Resolution::Glob
    expect ambiguous: unless ((declared).len > 0), when ((opened).len) > 1, (concrete.result) = modules::Resolution::Ambiguous
    expect prelude_resolution: unless ((declared).len > 0), when ((opened).len) = 0 and ((prelude).len > 0), (concrete.result) = modules::Resolution::Prelude
    expect unbound: unless ((declared).len > 0), when ((opened).len) = 0 and (prelude).len <= 0, (concrete.result) = modules::Resolution::Unbound
}
```

### Shadowing the prelude

An item declared with a name that the prelude gives, in a module where no
item declared or imported by name, nor variant opened with `*`, has it,
hides the prelude's item or variant, and is written with `!` after its
name, as a [declaration that shadows](Procedures.md#shadowing) any name
is: `enum Option!<T> { None, Some(T) }`, `const None!: Int := 0` or
`mod Result!`. Without the `!`, it is an error (`F0217`), and with a `!`
where it hides nothing, so is the `!` (`F0218`). Where the module imports
the name, by name or with `*`, the import is what the declaration
competes with: a name declared and imported by name is an error
(`F0207`), and a declared item takes precedence over a variant opened
with `*`, as before. Uses are written without `!`, and within the module,
the name then means the declared item. Other modules are not affected:
their scopes have the prelude's.

`modules::item_shadowing` states this over the layers of the module's
scope where the item is declared, before it is: the item is fresh, so no
item of its name is declared or imported by name, and the name resolves to
the prelude's, as `modules::first_segment` says, exactly when no variant of
it is opened and the prelude gives it. The item hides a name exactly then.

```fren
-- `hides?` is a `Bool`, which a comparison of sequences of an abstract type,
-- as `opened = []`, is not in Lean: so `len`.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.length_zero "allow" in
pub proc item_shadowing(
    opened: Seq<Path>,             -- the distinct variants of its name that `use ...::*` opens
    prelude: Seq<Path>,            -- the prelude's item or variant of its name
    bang?,                         -- it is written with `!`
): (det hides?, det accepted?) {
    out hides? := opened.len = 0 and prelude.len > 0
    out accepted? := hides? iff bang?

    expect explicit: when prelude != [] and opened = [], accepted? iff bang?
    expect imports_first: when opened.len = 1, accepted? iff not bang?
    expect needless: when prelude = [], accepted? iff not bang?
}

-- The item hides a name exactly when its name, fresh, resolves to the prelude's.
set_option fren.lint.undecidable "allow" in
expect hides_prelude(
    s_opened: Seq<Path>,
    s_prelude: Seq<Path>,
    s_bang?,
    f_declared: Seq<Path>,
    f_opened: Seq<Path>,
    f_prelude: Seq<Path>,
) {
    call s := item_shadowing(s_opened, s_prelude, s_bang?)
    call f := first_segment(f_declared, f_opened, f_prelude)
    expect hides_prelude: when f.declared = [] and f.opened = s.opened and f.prelude = s.prelude, s.hides? iff f.result = Prelude
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
covers records, abstract types, functions, constants, procedures, global
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
the previous segment resolved to.

```fren
set_option fren.evidence "enumerated" in
pub proc member(
    parent: Kind,        -- what the previous segment resolved to
    found?,              -- it has a member of this name
    visible?,            -- for a module: that member is visible from here (`item_visible`)
): (accepted?) {
    ensure rule: accepted? iff (found? and (if parent = Module then visible? else parent = Enum))

    expect only_modules_hide: when parent = Enum and found?, accepted?
    expect others_empty: when parent = Other, not accepted?
}
```

`modules::two_segments` puts the two rules together for a path `a::b`,
whose `a` may be the prelude's, as in `Option::Some`.

```fren
-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub proc two_segments(
    bindings: Set<lang::Binding>,    -- the items and imports in scope where the path is written
    nearer: Set<lang::Binding>,      -- the same without the prelude
    a: lang::Id,
    b_found?,                        -- `a` has a member named `b`
    b_pub?,                          -- that member is `pub`
    b_owner: ModuleName,             -- the module declaring `b`: `a`, if `a` is a module
    here: ModuleName,                -- the module where the path is written
): (det a_kind: Kind, det accepted?) {
    assume nearer_inside: nearer subset bindings

    -- What `a` is, when it is declared or imported by name.
    out a_kind := match first.lookup {
        lang::Lookup::Found(k) => kind_of(k),
        _ => Other,
    }

    call first := resolve(bindings, nearer, a)
    call seen := item_visible(b_pub?, b_owner, here, here)
    call second := member(a_kind, b_found?, seen.visible?)

    ensure rule: accepted? iff second.accepted?

    expect variants_have_no_members: when first.result = Glob, not accepted?
    -- The prelude's enumeration has its variants as members: `Option::Some`.
    expect prelude_variant: when first.result = Prelude and a_kind = Enum and b_found?, accepted?
    expect private_member: when a_kind = Module and not b_pub? and here != b_owner and not descends?(here, b_owner),
        not accepted?
    -- The variants of an enumeration that `a` names are its members, wherever they are written.
    expect variants_visible: when first.lookup = lang::Lookup::Found(lang::BindingKind::Enumeration) and b_found?,
        accepted?
}

#fren_check
```

## Across files

In Lean, a file sees the modules and items of the Lean files it imports, and
each file starts in the root module. With the `fren` command, the files
given are processed in order with one shared set of modules, and each file
starts in the root module.
