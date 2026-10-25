# Unused

The lints of the `unused` group find what is declared but never used.
One of them, `unfulfilled_lint_expectations`, finds an expectation that
no lint fulfils, and is described with [expecting
lints](../Lint.md#expecting-lints).

## Unused imports

A `use` is *used* if a path in the same file and module resolves through
it: the path's first segment resolves (see
[Resolution](../Lang/Modules.md#resolution)) to the item it imports by name,
or to a variant of the enumeration it opens. Paths in expressions, types,
instances, global expectations, claims and `#fren_check` count. The paths of
`use` declarations do not, since they are absolute.

A declaration written with `!` that [shadows](../Lang/Components.md#shadowing)
a name the `use` brings in counts as such a path, since the `!` depends on
the import: without the `use`, the `!` would hide nothing, and be an error.
So `use self::Shape::Square` with `in Square!: Int` is used, `fren fix`
keeps it, and a glob that [`glob_imports`](Style.md#glob-imports) narrows keeps
that name. A `!` that hides a variable or binder instead, which hides the
import too, does not count.

Only uses in the same file count, even though a module's imports are
visible in later files that enter it (see [Modules and
visibility](../Lang/Modules.md#across-files)): in Lean, each file is
elaborated without seeing the files that import it. A Markdown spec read
by `#fren_md` counts as a file of its own, as it does for the `fren`
command.

Opening the same enumeration twice in a module counts once (see
[Resolution](../Lang/Modules.md#resolution)), so only the first such `use` can
be used, and the others are unused. `lint::unused_import` decides whether
a `use` is unused:

```fren
pub mod lint

pub comp unused_import {
    in glob?             -- it is `use ...::*`
    in n_paths: Nat      -- paths in its file and module whose first segment resolves to a name it brings into scope
    in first?            -- no earlier `use` in its file and module opens the same enumeration
    pub det out unused?

    req rule: unused? iff (n_paths = 0 or (glob? and not first?))

    expect named_used: when not glob? and n_paths > 0, not unused?
    expect repeated_glob: when glob? and not first?, unused?
}
```

The message is reported at the `use`'s path at the end of the file, and
suggests removing the `use`.

## Unused variables

`unused_variables` reports a variable of a component that nothing in the
component mentions, a binder of a global expectation that its body
never mentions, and a parameter of a defined function that its body never
mentions. An input that nothing mentions does not affect the
component, and an output that nothing mentions can take any value.

A variable is mentioned by a path in one of the component's constraints,
or in a binding of one of its instances, whose only segment is the
variable's name and that resolves to it: the binding `x` in `inst w: c {
x }` mentions `x`, but in `match s { Shape::Circle(x!) => x > 0, _ =>
true }`, the `x` of the arm is the binder that
[shadows](../Lang/Components.md#shadowing) the variable, so it does not
mention the variable. A binder `w` is mentioned by a path `w.x`, and a
parameter as a variable is. Mentions elsewhere, such as
through an instance of the component in another one, do not count: they
cannot constrain the variable. The variables of the component's own
instances are not reported, and neither are the variables of a component,
or the binders of a global expectation, with a static error.

The message is reported at the variable's declaration, in the order of
declaration.

## Dead code

`dead_code` reports a private enumeration, record, abstract type, function
or constant that no path in its file resolves to. A path to a variant uses
its enumeration, and so does a path through it, such as `Mode::Heat`. A
function is used by applying it, and a record or abstract type by naming
it, as the type of a variable, field, payload or function, or, for a
record, in a record literal. As for [unused
imports](#unused-imports), paths in `use` declarations do not count, and
only uses in the same file count, even though a private item is visible
from its module's descendants, which later files may enter. Uses in Lean
code do not count either. A use counts even when it is in an item that is
itself unused.

Components and global expectations are never dead: each is a requirement,
or a claim about requirements, in its own right, and is checked and
[traced](../Trace.md) whether or not anything uses it. `pub` items may be used
by other files. `lint::Named` is what a name can name, which the
[naming conventions](NonstandardStyle.md#naming-conventions) also use. `lint::dead_item`
states this:

```fren
pub enum Named {
    Module,
    Component,
    Variable,
    Field,
    Binder,
    Function,
    Instance,
    Constraint,
    Global,
    Enumeration,
    Variant,
    Record,
    AbstractType,
    Constant,
}

use self::Named::{AbstractType, Component, Constant, Enumeration, Function, Record}

pub comp dead_item {
    in what: Named
    in pub?
    in n_uses: Nat       -- paths in its file that resolve to it, to one of its variants, or through it
    pub det out dead?

    req rule: dead? iff (what in {Enumeration, Record, AbstractType, Function, Constant} and not pub? and n_uses = 0)

    expect public_lives: when pub?, not dead?
    expect components_live: when what = Component, not dead?
}
```

The message is reported at the item's name, at the end of the file.
