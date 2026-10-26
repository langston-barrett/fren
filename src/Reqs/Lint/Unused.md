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

    ensure rule: unused? iff (n_paths = 0 or (glob? and not first?))

    expect named_used: when not glob? and n_paths > 0, not unused?
    expect repeated_glob: when glob? and not first?, unused?
}
```

The message is reported at the `use`'s path at the end of the file, and
suggests removing the `use`.

## Unused variables

`unused_variables` reports a variable of a component that nothing in the
component mentions, a binder of a global expectation over a component's
behaviours that its body never mentions, and a parameter of a defined
function that neither its body nor its [contract](../Lang/Items.md#contracts)
mentions. It does not report a
[quantifier's](../Lang/Quantifiers.md) bound name, including a binder
of a global expectation over a type's values. An input that nothing mentions does not affect the
component, and an output that nothing mentions can take any value.

A variable is mentioned by a path in one of the component's constraints,
or in a binding of one of its instances, whose only segment is the
variable's name and that resolves to it: the binding `x` in `inst w: c {
x }` mentions `x`, but in `match s { Shape::Circle(x!) => x > 0, _ =>
true }`, the `x` of the arm is the binder that
[shadows](../Lang/Components.md#shadowing) the variable, so it does not
mention the variable, and neither does the `x` of the body of `forall
(x!: Mode), x = Mode::Off`. A binder `w` is mentioned by a path `w.x`, and a
parameter as a variable is. A path in a definition of a [`let` or
`where`](../Lang/Let.md) counts, whether or not the name defined is
mentioned, and the names defined are not reported. Mentions elsewhere, such as
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

Components and global expectations are never dead: each is a guarantee,
or a claim about guarantees, in its own right, and is checked and
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

    ensure rule: dead? iff (what in {Enumeration, Record, AbstractType, Function, Constant} and not pub? and n_uses = 0)

    expect public_lives: when pub?, not dead?
    expect components_live: when what = Component, not dead?
}
```

The message is reported at the item's name, at the end of the file.

## Unused assumptions

`unused_assumption` reports an assumption of a component that mentions
only inputs, one or more, none of them used. An input is *used* when
something mentions it: a constraint other than an assumption, cover goals
among them, as for an [unused variable](#unused-variables); a definition;
a binding of one of the component's instances; a global expectation in
the same file that reads it through an instance of the component, as `a.x` with
the binder `a`; an [instance](../Lang/Instances.md) of the component in
the same file, which binds each of its inputs, and whose assumption check
checks the assumption; or a [refinement](../Lang/Refinement.md) in the
same file of which the component is the abstraction. Such a refinement
reads every input of the abstraction, through its binding or by name, and
the abstraction's assumptions are its hypotheses, so an assumption can
guard a binding: with `n := q.len` and `assume pos: n > 0`, `x := q[0]` is
defined. An input is also used when another assumption mentions it and a
used variable, since the assumption constrains the two together, and so
on transitively: with `assume a: n > 0`, `assume b: m = 2 * n` and `ensure r:
y = m`, `m` is used, so `n` is, and without `a`, `y > 0` would not follow.
An uninterpreted function links assumptions in the same way as a
variable, through its values: it is *used* when one of the above applies
it, and an assumption that applies a used function is used, as is an
input it mentions. With `assume a: n = 3 and g(n) > 0` and `ensure r: y =
g(3)`, `a` says that `g(3) > 0`, so it is used. A constant's value and a
defined function's body apply no uninterpreted function, so they link
nothing. With these rules, removing a reported assumption together with
the reported assumptions it is linked to never makes a check fail. Alone,
it may: with `assume a: n >= 0 and n < q.len` and `assume b: q[n] > 0`,
both are reported, but `a` guards the index in `b`, so `b` without `a` is
not defined (`F0611`). So the message names the reported assumptions
linked to it. The variables `V` and functions of such a group are
mentioned by nothing else, so a check over the component is `forall U V,
A(V) and B(U) implies C(U)`, with `A` the group's assumptions, which is
`(exists V, A(V)) implies (forall U, B(U) implies C(U))`, for every
interpretation of the functions. Since `B` and `C` apply none of `A`'s
functions, `exists V, A(V)` can be made
to hold by changing only those, unless `A` is unsatisfiable, and then the
assumptions' satisfiability check already fails (`F0602`). The group
can also bound the size of an abstract type, as `k1 != k2` does, but that
is safe too: given a counterexample to a check without it, add a fresh
value to the type, extend each uninterpreted function to it, and give
`k1` an old value and `k2` the new one. Nothing else mentions them, so
the counterexample still fails, and the assumption now holds. An unused
input does not affect the component, as for an [unused variable](#unused-variables), but
`unused_variables` does not report it, since the assumption mentions it:
this is what is left after the last guarantee that used the input is
removed. As for [dead code](#dead-code), only the file's global
expectations, instances and refinements count. There is no fix: removing
the inputs would change the component's interface.
`lint::unused_assumption` states when it fires:

```fren
pub comp unused_assumption {
    in n_mentioned: Int  -- variables the assumption mentions
    in all_inputs?       -- each of them is an input
    in mentioned?        -- one of them, or a function it applies, is used in the component, through its other assumptions too
    in read?             -- one of them, or a function it applies, is read in the file, by a global expectation, an instance or a refinement, through the component's other assumptions too
    pub det out fires?

    assume counts: n_mentioned >= 0

    ensure rule: fires? iff (n_mentioned > 0 and all_inputs? and not mentioned? and not read?)
}
```

The message is reported at the assumption's name, at the end of the
file.

## Unused lint settings

`unused_lint_setting` reports a [lint setting](../Lint.md#setting-levels),
a `set_option` of a lint or a group, that is in effect at no item for any
of the lints it sets. A setting is in effect from where it is to the end
of the file, or with `in`, in its item, except where a later setting
replaces it for a lint. So a setting has no effect when, before any item:

- a later setting of the same lint or group replaces it, as in `set_option
  L "allow" in set_option L "warn" in item`, where the inner one wins, or
  in two settings at the top level with no item between them;
- a setting of its group replaces it, since that sets each of its lints;
- the file ends, as for a setting after the last item.

A setting of a lint after one of its group, as `set_option
fren.lint.pedantic "warn"` and then `set_option fren.lint.match_same_arms
"allow"`, is not reported: the group's is still in effect for its other
lints. A check, such as `#fren_check`, is not an item here, since no lint
is about it. A setting of `unfulfilled_lint_expectations` or
`unused_lint_setting` is also in effect at a later setting, whose messages
take their level from it, and so is a `forbid`, which decides whether a
later setting is accepted. A setting to `expect` is not reported: if
nothing fulfils it, `unfulfilled_lint_expectations` reports it.

A replaced `deny` is the most dangerous case, since the lint it denies is
then not an error after all: the message says which setting undoes it.
The message is reported at the setting, at the end of the file. The fix
removes it, as the [fix](../Lint.md#fixing-lints) of
`unfulfilled_lint_expectations` does: since it is in effect at no item,
every item keeps its levels, and since it is in effect at no setting
either, every setting keeps its messages and is accepted or not as
before. `lint::unused_lint_setting` states when it fires:

```fren
pub comp unused_lint_setting {
    in n_places: Int     -- items and later settings where it is in effect for a lint it sets
    in expect?           -- it is to `expect`
    pub det out fires?

    assume counts: n_places >= 0

    ensure rule: fires? iff (n_places = 0 and not expect?)
}
```
