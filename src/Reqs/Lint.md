# Lints

A *lint* is a diagnostic about something that is allowed but probably not
intended, such as an import that nothing uses. Each lint has a
name and a *level*, which says whether it is reported and how. Each lint
has a default level, which can be changed on the command line, in Lean
options, and in the spec itself.

```fren
pub mod lint

use view::Severity
```

## The lints

<!-- keep-sorted start skip_lines=2 -->
| Lint | Code | Group | Default | Reported at |
|---|---|---|---|---|
| `bool_equality` | `F0731` | `pedantic` | `allow` | `a = b` on `Bool`s (see [Comparisons](#comparisons)) |
| `card_zero` | `F0716` | `style` | `warn` | a comparison of a set's or relation's `card` with `0` or `1` that says whether it is empty, such as `s.card = 0` (see [Empty collections](#empty-collections)) |
| `case_split_reqs` | `F0729` | `pedantic` | `allow` | two or more requirements `when T, y = e` of one output, whose tests are of which variant one scrutinee is (see [Variant tests](#variant-tests)) |
| `collapsible_when` | `F0723` | `style` | `warn` | a `when` whose body is a `when`, or an `unless` whose body is an `unless` (see [Conditionals](#conditionals)) |
| `constant_output` | `F0719` | `complexity` | `warn` | a defined output whose definition mentions no variable and no uninterpreted function (see [Outputs](#outputs)) |
| `dead_code` | `F0711` | `unused` | `warn` | a private enumeration, record, abstract type, function or constant that nothing in its file uses (see [Dead code](#dead-code)) |
| `definable_output` | `F0720` | `pedantic` | `allow` | an output that one requirement equates with an expression of other variables (see [Outputs](#outputs)) |
| `double_comparison` | `F0730` | `complexity` | `warn` | two comparisons of the same operands that are one, such as `a < b or a = b` (see [Comparisons](#comparisons)) |
| `double_neg` | `F0740` | `style` | `warn` | a negation of a negation, `- -x` (see [Arithmetic](#arithmetic)) |
| `double_parens` | `F0739` | `complexity` | `warn` | parentheses directly around parentheses, `((e))` (see [Parentheses](#parentheses)) |
| `duplicate_elements` | `F0738` | `suspicious` | `warn` | a set or relation literal with an element written the same as an earlier one, such as `{a, b, a}` (see [Suspicious expressions](#suspicious-expressions)) |
| `else_extends` | `F0733` | `complexity` | `warn` | a conditional operand whose `else` branch extends past its operator, as in `2 * if c? then x else y + 1` (see [Conditional operands](#conditional-operands)) |
| `empty_argument` | `F0745` | `suspicious` | `warn` | a method applied to `""` or `[]`, or a `slice` of length `0`, such as `s.starts_with?("")` (see [Suspicious expressions](#suspicious-expressions)) |
| `eq_op` | `F0736` | `suspicious` | `warn` | an operator whose operands are written the same, such as `x = x` (see [Suspicious expressions](#suspicious-expressions)) |
| `glob_imports` | `F0702` | `style` | `warn` | a `use ...::*` (see [Glob imports](#glob-imports)) |
| `identity_op` | `F0734` | `complexity` | `warn` | an operation that leaves an operand as it is, such as `x + 0`, or the negation in `x + -y` (see [Identities](#identities)) |
| `if_chain_match` | `F0727` | `pedantic` | `allow` | a chain of `if` whose tests are of which variant one scrutinee is (see [Variant tests](#variant-tests)) |
| `if_not_else` | `F0724` | `pedantic` | `allow` | an `if` whose condition is a negation, such as `if not c? then a else b` (see [Conditionals](#conditionals)) |
| `index_after_use` | `F0721` | `suspicious` | `warn` | an index on the left of an `and` whose right bounds the sequence (see [Indexes](#indexes)) |
| `int_plus_one` | `F0741` | `complexity` | `warn` | a non-strict comparison of integers with an operand off by one, such as `x >= y + 1` (see [Arithmetic](#arithmetic)) |
| `length_zero` | `F0715` | `style` | `warn` | a comparison of a string's or sequence's `len` with `0` or `1` that says whether it is empty, such as `s.len = 0` (see [Empty collections](#empty-collections)) |
| `manual_method` | `F0732` | `complexity` | `warn` | a search written with `index_of` or `slice`, such as `s.index_of(t, 0) >= 0` (see [Searches](#searches)) |
| `match_like_membership` | `F0726` | `style` | `warn` | a `match` whose arms are all `true` or `false` (see [Matches](#matches)) |
| `match_same_arms` | `F0725` | `pedantic` | `allow` | an arm of a `match` with the same body as another (see [Matches](#matches)) |
| `membership_chain` | `F0718` | `pedantic` | `allow` | `x = a or x = b or x = c`, or `x != a and x != b and x != c`, three or more (see [Membership](#membership)) |
| `neg_multiply` | `F0742` | `style` | `warn` | a product with `-1`, `x * -1` or `-1 * x` (see [Arithmetic](#arithmetic)) |
| `non_camel_case_types` | `F0704` | `nonstandard_style` | `warn` | an enumeration, variant, record or abstract type not named in `CamelCase` |
| `non_snake_case` | `F0703` | `nonstandard_style` | `warn` | a module, component, variable, function, instance, constraint or global expectation not named in `snake_case` (see [Naming conventions](#naming-conventions)) |
| `non_upper_case_constants` | `F0705` | `nonstandard_style` | `warn` | a constant not named in `UPPER_CASE` |
| `nonminimal_bool` | `F0712` | `complexity` | `warn` | a `Bool` expression with a simpler form, such as `a? = true` (see [Simpler `Bool` expressions](#simpler-bool-expressions)) |
| `redundant_bindings` | `F0735` | `style` | `warn` | a binding or field `x := x` (see [Bindings](#bindings)) |
| `redundant_bool_type` | `F0746` | `style` | `warn` | a `: Bool` that a name ending in `?` implies, as in `in ready?: Bool` (see [Boolean types](#boolean-types)) |
| `redundant_method_chain` | `F0743` | `complexity` | `warn` | a chain of methods with a shorter form, such as `q.rev.rev` (see [Chains of methods](#chains-of-methods)) |
| `same_branches` | `F0737` | `suspicious` | `warn` | `if c then a else a` (see [Suspicious expressions](#suspicious-expressions)) |
| `singleton_membership` | `F0717` | `complexity` | `warn` | `x in {a}` (see [Membership](#membership)) |
| `trivial_match` | `F0747` | `complexity` | `warn` | a `match` of one arm that binds nothing, such as `match x { _ => e }` (see [Trivial matches](#trivial-matches)) |
| `trivial_pattern` | `F0744` | `style` | `warn` | `s.matches?(p)`, where `p` is a string, with `.*` or not at either end (see [Trivial patterns](#trivial-patterns)) |
| `undecidable` | `F0714` | `decidability` | `deny` | a construct outside the decidable core (see [Undecidable constructs](#undecidable-constructs)) |
| `unfulfilled_lint_expectations` | `F0706` | `unused` | `warn` | a `set_option` that expects a lint that never fires (see [Expecting lints](#expecting-lints)) |
| `unless_not` | `F0722` | `style` | `warn` | an `unless` whose condition is a negation, such as `unless not c?, d?` (see [Conditionals](#conditionals)) |
| `unused_imports` | `F0701` | `unused` | `warn` | a `use` that nothing in its file uses (see [Unused imports](#unused-imports)) |
| `unused_variables` | `F0710` | `unused` | `warn` | a variable or binder that nothing mentions (see [Unused variables](#unused-variables)) |
| `wildcard_single_variant` | `F0728` | `pedantic` | `allow` | a `_` arm that matches only one variant (see [Matches](#matches)) |
<!-- keep-sorted end -->

Lints are found while elaborating, like [static
errors](View.md#static-errors), and never ask the solver anything: the
results of [checks](Check.md), such as a redundant constraint, are not
lints.

## Levels

| Level | Effect |
|---|---|
| `allow` | not reported |
| `expect` | not reported, but the lint must fire (see [Expecting lints](#expecting-lints)) |
| `warn` | a warning |
| `deny` | an error |
| `forbid` | an error, and the level can no longer be changed |

```fren
pub enum Level { Allow, Expect, Warn, Deny, Forbid }

use self::Level::{Allow, Deny, Expect, Forbid, Warn}
```

`lint::severity` gives the [severity](View.md#severity) of a lint's
message from its level:

```fren
pub comp severity {
    use view::Severity::{Error, Info, Silent, Warning}
    in level: Level
    pub det out result: Severity

    req rule: result = match level { Allow | Expect => Silent, Warn => Warning, Deny | Forbid => Error }

    expect never_info: result != Info
    expect silent_below_warn: result = Silent iff level in {Allow, Expect}
}
```

A denied lint is a static error, so with the `fren` command no check
runs.

## Groups

Each lint is in exactly one *group*, and its default level is its group's:

<!-- keep-sorted start skip_lines=2 -->
| Group | Default | Lints that |
|---|---|---|
| `complexity` | `warn` | find a simpler expression with the same meaning |
| `decidability` | `deny` | find a construct outside the decidable core: `undecidable` alone |
| `nonstandard_style` | `warn` | find a name in the wrong case |
| `pedantic` | `allow` | are matters of judgement, or would fire on much that reads well as it is |
| `style` | `warn` | find a clearer way to write the same thing |
| `suspicious` | `warn` | find what is probably not what the writer meant |
| `unused` | `warn` | find what is declared but never used |
<!-- keep-sorted end -->

The groups follow those of rustc and Clippy, and a lint modelled on one of
theirs is in the group of the same name: a Clippy lint in `pedantic` is
allowed here too. `glob_imports` and `trivial_pattern` are exceptions:
their Clippy counterparts are `pedantic` and `nursery`, but here both are
in `style` (see [Trivial patterns](#trivial-patterns)), so both are `warn`.

```fren
pub enum Group { Unused, NonstandardStyle, Style, Complexity, Suspicious, Pedantic, Decidability }

pub comp group_default {
    in group: Group
    pub det out level: Level

    req rule: level = match group {
        Group::Pedantic => Level::Allow,
        Group::Decidability => Level::Deny,
        _ => Level::Warn,
    }

    expect never_expect: level != Level::Expect and level != Level::Forbid
}
```

A group's name is never a lint's, and wherever a lint's level is set, a
group's can be, which sets the level of each of its lints. Moving a lint to
another group changes its default level, so it is a breaking change.

## Setting levels

A lint's level is set:

- **On the command line.** `fren check` and `fren trace` take `-A LINT`
  (allow), `-W LINT` (warn), `-D LINT` (deny) and `-F LINT` (forbid), or
  the long forms `--allow`, `--warn`, `--deny` and `--forbid`. In Lean, the command line is the Lean options set outside the
  file, such as `leanOptions` in a Lake package. There is no `expect` on
  the command line: a Lean option set to `expect` outside the file means
  `allow`.
- **In the spec**, with the Lean command `set_option`, which the `fren`
  command also accepts in spec files:

  ```
  lint-setting := "set_option" lint-option STRING ["in" item]
  lint-option  := "fren.lint." IDENT
  ```

  `set_option fren.lint.glob_imports "allow"` sets the level of
  `glob_imports` for the rest of the file (in Lean, for the rest of the
  current `section` or `namespace`, if any). Followed by `in` and an item,
  it sets the level for that item only. The string is one of `allow`,
  `expect`, `warn`, `deny` and `forbid`.

A [group](#groups) is set like a lint, as in `-W pedantic` or `set_option
fren.lint.pedantic "warn"`, and its setting is a setting of each of its
lints, in its place. So `-W pedantic -A match_same_arms` warns of each
pedantic lint but `match_same_arms`.

Each file starts with the levels from the command line, or the defaults
for lints that the command line does not set. On the command line, the last
flag for a lint wins, except that `-F` always wins. In the spec, each
`set_option` replaces the level in effect before it, except that a
forbidden lint keeps its level, and trying to change it is an error at the
`set_option` (`F0709`). Setting `forbid` again is allowed. `lint::setting`
states one such setting:

```fren
pub comp setting {
    in current: Level    -- the level in effect before the setting
    in requested: Level  -- the level the setting asks for
    pub det out accepted?
    pub det out level: Level

    req forbidden: accepted? iff (current != Forbid or requested = Forbid)
    req applied: level = if accepted? then requested else current

    expect forbid_is_final: when current = Forbid, level = Forbid
    expect forbid_is_always_accepted: when requested = Forbid, accepted?
}
```

A group's setting is accepted when each of its lints would accept it, so
when none is forbidden, or when it sets `forbid`; otherwise it is an error
(`F0709`), and changes no level. `lint::group_setting` states it, for one
lint of the group:

```fren
pub comp group_setting {
    in current: Level        -- the lint's level before the setting
    in n_forbidden: Int      -- lints of the group at `forbid` before it
    in requested: Level
    pub det out accepted?
    pub det out level: Level

    assume counts: n_forbidden >= 0

    req forbidden: accepted? iff (n_forbidden = 0 or requested = Level::Forbid)
    req applied: level = if accepted? then requested else current

    expect forbid_is_always_accepted: when requested = Level::Forbid, accepted? and level = Level::Forbid
    expect blocked_keeps_level: when n_forbidden > 0 and requested != Level::Forbid, level = current
}
```

In Lean, the options set outside the file have no order, so there a
lint's own option wins over its group's, whichever is set.
`lint::outside_options` states it:

```fren
pub comp outside_options {
    in default_level: Level
    in own_set?              -- the lint's own option is set
    in own: Level
    in group_set?            -- its group's option is set
    in group: Level
    pub det out level: Level

    req rule: level = if own_set? then own else if group_set? then group else default_level
}
```

`lint::history` states the rule for a whole file's settings of one lint,
in order: after the first `forbid`, only `forbid`. Naming each other level
says "every later setting" without a quantifier, over the settings after
the first `forbid`, `rest`, a private [defined
output](Lang/Components.md#defined-outputs). `in` on a sequence that is not
a literal, and `index_of`, are outside the [decidable
core](Lang/Decidability.md#sequences), so the rule opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub comp history {
    in settings: Seq(Level)      -- the levels a file sets for one lint, in order
    -- The settings after the first `forbid`.
    out rest: Seq(Level) := settings.slice(settings.index_of([Forbid], 0) + 1, settings.len)
    pub det out accepted?

    req rule: accepted? iff not (Forbid in settings
        and (Allow in rest or Expect in rest or Warn in rest or Deny in rest))

    expect forbid_last: when settings = [Warn, Forbid], accepted?
    expect no_unforbid: when settings = [Forbid, Allow], not accepted?
}
```

If `forbid` is not among the settings, `rest` is what the definition gives,
but `rule` does not look at it then.

That a history is accepted exactly when every step that `lint::setting`
takes along it is accepted cannot be stated for every length without a
fold. For a fixed length it can, by a chain of `lint::setting`s, and
`lint::stepwise` does so for three settings, the first made over any level
but `forbid`: `lint::setting` accepts every first setting then, whatever
that level is. `history` refines it. `history` is outside the decidable
core, so the refinement is checked by testing:

```fren
pub comp stepwise {
    in settings: Seq(Level)
    pub out accepted?

    assume three: settings.len = 3

    inst first: setting { current := Warn, requested := settings[0] }
    inst second: setting { current := first.level, requested := settings[1] }
    inst third: setting { current := second.level, requested := settings[2] }

    req rule: accepted? iff (first.accepted? and second.accepted? and third.accepted?)

    expect unforbid_last: when settings = [Warn, Forbid, Allow], not accepted?
}

set_option fren.evidence "tested" in
refine history_is_stepwise: history refines stepwise
```

`lint::effective` puts the sources together, for one lint at one place in
a file: its default, then the command line, then the last `set_option`
before that place that is in effect there. Each step is a `lint::setting`.

```fren
pub comp effective {
    in default_level: Level
    in cli_set?          -- the command line sets the lint
    in cli: Level        -- the level it sets
    in src_set?          -- a `set_option` in the file sets the lint here
    in src: Level        -- the level it sets
    pub det out after_cli: Level  -- the level from the default and the command line
    pub det out level: Level
    pub det out error?   -- the `set_option` tries to change a forbidden lint

    assume no_cli_expect: cli != Expect

    req cli_rule: after_cli = if cli_set? and (default_level != Forbid or cli = Forbid)
        then cli else default_level
    req level_rule: level = if src_set? and (after_cli != Forbid or src = Forbid)
        then src else after_cli
    req error_rule: error? iff (src_set? and after_cli = Forbid and src != Forbid)

    expect default_when_unset: when not cli_set? and not src_set?, level = default_level
    expect source_wins: when src_set? and not error?, level = src
    expect forbid_on_cli_is_final: when cli_set? and cli = Forbid, level = Forbid
}
```

The level that applies to a lint's message is the one in effect at the
item it is about: the `use` for the import lints; for the naming lints
and `unused_variables`, the item that declares the name, which for a
member is its component and for a variant its enumeration; for `dead_code`, the unused item; and for `nonminimal_bool`
and the other lints of expressions, the item the expression is in. So
`set_option ... in` before an item sets the level for that item alone.

A `set_option` naming a lint that does not exist is an error (`F0707`),
and so is a level other than the five (`F0708`). In Lean, an option that
does not exist is Lean's own error, worded differently. The `fren` command
accepts no other `set_option` (see [Input files](Cli.md#input-files)).

## Messages

A lint's message has the lint's code, and the severity that its level
gives. The first message of each lint in a file also says where its level
comes from. The messages of lints that [`fren fix`](#fixing-lints) can
fix say so:

```text
warning[F0701]: unused import `check::Verdict`
 --> spec.fren:3:5
  |
3 | use check::Verdict
  |     ^^^^^^^^^^^^^^ unused
  |
  = help: remove this `use`
  = help: `fren fix` can fix this
  = note: `unused_imports` is `warn` by default
  = help: to allow it, `set_option fren.lint.unused_imports "allow"`
```

When the level was set, the note says so instead, such as ``note:
`unused_imports` is set to `deny` ``, or, when its group's setting set it,
``note: `membership_chain` is set to `warn` by its group, `pedantic` ``, and
there is no help line.

## Unused imports

A `use` is *used* if a path in the same file and module resolves through
it: the path's first segment resolves (see
[Resolution](Lang/Modules.md#resolution)) to the item it imports by name,
or to a variant of the enumeration it opens. Paths in expressions, types,
instances, global expectations, claims and `#fren_check` count. The paths of
`use` declarations do not, since they are absolute.

A declaration written with `!` that [shadows](Lang/Components.md#shadowing)
a name the `use` brings in counts as such a path, since the `!` depends on
the import: without the `use`, the `!` would hide nothing, and be an error.
So `use self::Shape::Square` with `in Square!: Int` is used, `fren fix`
keeps it, and a glob that [`glob_imports`](#glob-imports) narrows keeps
that name. A `!` that hides a variable or binder instead, which hides the
import too, does not count.

Only uses in the same file count, even though a module's imports are
visible in later files that enter it (see [Modules and
visibility](Lang/Modules.md#across-files)): in Lean, each file is
elaborated without seeing the files that import it. A Markdown spec read
by `#fren_md` counts as a file of its own, as it does for the `fren`
command.

Opening the same enumeration twice in a module counts once (see
[Resolution](Lang/Modules.md#resolution)), so only the first such `use` can
be used, and the others are unused. `lint::unused_import` decides whether
a `use` is unused:

```fren
pub comp unused_import {
    in glob?             -- it is `use ...::*`
    in n_paths: Int      -- paths in its file and module whose first segment resolves to a name it brings into scope
    in first?            -- no earlier `use` in its file and module opens the same enumeration
    pub det out unused?

    assume counts: n_paths >= 0

    req rule: unused? iff (n_paths = 0 or (glob? and not first?))

    expect named_used: when not glob? and n_paths > 0, not unused?
    expect repeated_glob: when glob? and not first?, unused?
}
```

The message is reported at the `use`'s path at the end of the file, and
suggests removing the `use`.

## Glob imports

`use E::*` brings every variant of `E` into scope, including variants
added later, so a reader cannot tell where a name comes from, and adding a
variant to one enumeration can make a name in another module
[ambiguous](Lang/Modules.md#resolution). `glob_imports` reports every
`use ...::*`. Its message suggests importing by name the variants the file
uses through it, or writing them qualified, as in `Mode::Heat`.

A glob import that is unused is reported by both lints.

## Naming conventions

The case of a name says what it names:

| Case | Names | Lint |
|---|---|---|
| `snake_case` | modules, components, variables, fields, functions, instances, constraints, global expectations and their binders, and the binders of `match` patterns | `non_snake_case` |
| `CamelCase` | enumerations, variants, records and abstract types | `non_camel_case_types` |
| `UPPER_CASE` | constants | `non_upper_case_constants` |

```fren
pub enum Case { Snake, Camel, Upper }

use self::Case::{Camel, Snake, Upper}

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

use self::Named::{AbstractType, Component, Constant, Enumeration, Function, Record, Variant}

pub comp naming_case {
    in what: Named
    pub det out case: Case

    req rule: case = match what {
        Enumeration | Variant | Record | AbstractType => Camel,
        Constant => Upper,
        _ => Snake,
    }
}
```

A name is in `snake_case` if it has no uppercase letter, in `CamelCase` if
it starts with an uppercase letter and has no `_`, and in `UPPER_CASE` if
it starts with an uppercase letter and has no lowercase letter. Letters
are ASCII letters, and a variable's final `?` is ignored, which the
[patterns](Lang/Expressions.md#patterns) below do, since `?` is neither a
letter nor `_`. `lint::in_case` states the rule, for any name, with a
requirement for each case, so that each pattern is a requirement of its
own, though `case_split_reqs` would suggest merging them:

```fren
set_option fren.lint.case_split_reqs "allow" in
pub comp in_case {
    in case: Case
    in name: String
    pub det out conventional?

    req snake: when case = Snake, conventional? iff not name.matches?(r".*[A-Z].*")
    req camel: when case = Camel, conventional? iff name.matches?(r"[A-Z][^_]*")
    req upper: when case = Upper, conventional? iff name.matches?(r"[A-Z][^a-z]*")

    expect lowercase_is_snake: when not name.matches?(r".*[A-Z].*"), conventional? iff case = Snake
    expect mixed_not_upper: when case = Upper and name.matches?(r"[A-Z]+[a-z][A-Za-z]*"),
        not conventional?
}
```

`lowercase_is_snake` follows from what the patterns mean: a name that
starts with an uppercase letter has one.

So a name in `snake_case` is in no other case:

```fren
expect snake_apart: forall (a b: in_case),
    when a.name = b.name and a.case = Snake and b.case != Snake and a.conventional?,
    not b.conventional?
```

A name in the wrong case is reported where it is declared, with the name
converted to the right case as a suggested edit. Only declarations are
reported: a name used in another case is a different name.

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
[shadows](Lang/Components.md#shadowing) the variable, so it does not
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
[traced](Trace.md) whether or not anything uses it. `pub` items may be used
by other files. `lint::dead_item` states this:

```fren
pub comp dead_item {
    in what: Named
    in pub?
    in n_uses: Int       -- paths in its file that resolve to it, to one of its variants, or through it
    pub det out dead?

    assume counts: n_uses >= 0

    req rule: dead? iff (what in {Enumeration, Record, AbstractType, Function, Constant} and not pub? and n_uses = 0)

    expect public_lives: when pub?, not dead?
    expect components_live: when what = Component, not dead?
}
```

The message is reported at the item's name, at the end of the file.

## Simpler `Bool` expressions

`nonminimal_bool` reports a `Bool` expression that has a simpler form with
the same meaning, in any constraint, binding, constant or global
expectation:

| Written | Simpler form |
|---|---|
| `A = true`, `A != false`, `A iff true` | `A` |
| `A = false`, `A != true`, `A iff false` | `not A` |
| `not not A` | `A` |
| `not (A = B)`, and so on for every comparison | `A != B`, the complement of the comparison, simplified again if it compares with a literal |
| `if C then true else false` | `C` |
| `if C then false else true` | `not C` |
| `if C then A else false` | `C and A` |
| `if C then true else B` | `C or B` |
| `if C then false else B` | `not C and B` |
| `if C then A else true` | `not C or A` |

A literal may be on either side of `=`, `!=` and `iff`; when both sides are
literals, the right one is taken as the literal. The rules are tried in the
order of the table, so `if C then true else false` is `C`, not `C and
true`. The rules for `if` keep the guards (see
[Expressions](Lang/Expressions.md#sequences)): in `if C then A else B`, `A`
is guarded by `C` and `B` by `not C`, as they are in `C and A`, `C or B`,
`not C and B` and `not C or A`. `lint::literal_comparison`
gives the simpler form of a comparison with a literal:

```fren
pub comp literal_comparison {
    in equal?            -- the operator is `=` or `iff`, rather than `!=`
    in literal?          -- the literal is `true`
    pub det out negated?  -- the simpler form is `not A`, rather than `A`

    req rule: negated? iff (equal? != literal?)

    expect equal_true: when equal? and literal?, not negated?
    expect unequal_true: when not equal? and literal?, negated?
}
```

`lint::complement` gives the complement of a comparison, the one that
holds exactly when it does not:

```fren
pub enum Comparison { Eq, Ne, Lt, Le, Gt, Ge }

use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}

pub comp complement {
    in op: Comparison
    pub det out result: Comparison

    req rule: result = match op { Eq => Ne, Ne => Eq, Lt => Ge, Ge => Lt, Gt => Le, Le => Gt }

    expect changes: result != op
}

expect complement_involutive: forall (p q: complement), when q.op = p.result, q.result = p.op
```

The message is reported at the expression, and suggests the simpler form,
in which the operands are simplified too: the suggestion for `not not (a? =
true)` is `a?`. An operand keeps the text it is written with, and is put
in parentheses where [`lang::operand`](Lang/Expressions.md#operators)
requires them, and only there; the simpler form itself is put in
parentheses where it is an operand that requires them and it is not
already in parentheses. For this, a conditional counts as binding more
loosely than any operator, since its `else` extends as far right as
possible. So `x? and not not (a? or b?)` becomes `x? and (a? or b?)`, and
`not (x = 1)` becomes `x != 1`.

The simpler form means what the expression means. Whatever values its
paths, numbers and function applications have, if the expression has a
value, the simpler form has the same one. This is proved in Lean, over a
model of expressions that follows the [operators](Lang/Expressions.md#operators):
the rules above decide what the simpler form is, as an expression rather
than as text, and the proof covers every expression, every rule, and the
simplification of the operands. In the model, as in a spec that
elaborates, the branches of an `if` have the same type, so that in `if C
then A else false`, `A` is a `Bool`. The proof does not cover the text:
that the simpler form, written with its parentheses, parses as the
expression the rules chose.

## Conditionals

`unless_not`, `collapsible_when` and `if_not_else` report a conditional
that reads more simply written another way, in the same places as
`nonminimal_bool`, and suggest the rewritten form, which keeps the meaning
and the guards (see [Expressions](Lang/Expressions.md#sequences)). A
condition is a *negation* if it is `not A` or `a != b`; the condition it
negates is `A`, or `a = b`.

- `unless_not` fires on `unless C, D` where `C` is a negation: `unless not
  A, D` becomes `when A, D`, and `unless a != b, D` becomes `when a = b,
  D`. It does not fire on any other condition, such as `unless x < 3, D`:
  saying when `D` need not hold is what `unless` is for. `D` is guarded by
  `not C` before, and by the condition `C` negates after, which is the
  same.
- `collapsible_when` fires on a conditional whose body is a conditional
  with the same keyword: `when A, when B, D` becomes `when A and B, D`, and
  `unless A, unless B, D` becomes `unless A or B, D`. It does not fire on a
  nest of `when` and `unless`, such as `unless A, when B, D`, which keeps
  apart an exception and a case, as `modules::resolve` does (see
  [Resolution](Lang/Modules.md#resolution)). The guards are the same: `B`
  is guarded by `A` in `A and B`, as it is in `when A, when B, D`, and `D`
  by `A` and `B`. For `unless`, `B` is guarded by `not A` in `A or B`, and
  `D` by `not A` and `not B`, which is `not (A or B)`.
- `if_not_else`, `allow` by default, fires on `if C then A else B` where
  `C` is a negation: `if not C then A else B` becomes `if C then B else
  A`, and `if a != b then A else B` becomes `if a = b then B else A`. It
  does not fire when `B` is itself an `if`, since swapping the branches
  would break a chain of `else if`. `A` is guarded by `not C`, and `B` by
  `C`, before and after. It is `pedantic`, as its Clippy counterpart is.

`A`, `B` and the other operands keep their text, in parentheses where
[`lang::operand`](Lang/Expressions.md#operators) requires them, and only
there, as for `nonminimal_bool`: `unless a? iff b?, unless c?, d?` becomes
`unless (a? iff b?) or c?, d?`. That each rewritten form means what the
expression means is proved in Lean, over the model of expressions of
[`nonminimal_bool`](#simpler-bool-expressions), with each lint's rules
alone, so that the fix of one lint makes none of the changes another
suggests.

What the lints look at in an operand is its outermost operator,
`lint::Head`: `Not` for `not A`, `Unequal` for `a != b`, `If`, `When` and
`Unless` for the conditionals, and `Other` for the rest.
`lint::unless_not`, `lint::collapsible_when` and `lint::if_not_else` state
when they fire:

```fren
pub enum Head { Not, Unequal, If, When, Unless, Other }

pub comp unless_not {
    in unless?           -- the conditional is `unless`, rather than `when`
    in condition: Head
    pub det out fires?

    req rule: fires? iff (unless? and condition in {Head::Not, Head::Unequal})

    expect other: when condition = Head::Other, not fires?
}

pub comp collapsible_when {
    in unless?           -- the conditional is `unless`, rather than `when`
    in body: Head
    pub det out fires?

    req rule: fires? iff body = (if unless? then Head::Unless else Head::When)

    expect mixed: when unless? and body = Head::When, not fires?
}

pub comp if_not_else {
    in condition: Head
    in else_branch: Head
    pub det out fires?

    req rule: fires? iff (condition in {Head::Not, Head::Unequal} and else_branch != Head::If)

    expect chain: when else_branch = Head::If, not fires?
}
```

## Shadowing

No lint is about shadowing. A declaration that hides a name in scope
without `!`, and one with `!` that hides nothing, are static errors,
`F0217` and `F0218` (see [Shadowing](Lang/Components.md#shadowing)). They
replace the lint `shadowed_constants`, which warned of a variable named
like a constant, and whose code `F0713` is not reused.

## Undecidable constructs

`undecidable` fires once for each construct outside the [decidable
core](Lang/Decidability.md), at the construct, with the reason and how to
stay in the core. It is `deny` by default, so a spec opts out explicitly:

```
set_option fren.lint.undecidable "allow" in
comp c { ... }
```

A project that wants every check decidable sets `-F undecidable`. Setting
it to `expect` says that a component is meant to be undecidable, so that
[`unfulfilled_lint_expectations`](#expecting-lints) reports the opt-out
once a change brings it back into the core. `lint::undecidable_fires`
states when it fires:

```fren
use lang::{Construct, in_core}

pub comp undecidable_fires {
    in construct: Construct
    in constant_args?
    in comparable?
    in infinite_output?
    in ground?
    in infinite_elems?
    in finite_range?
    in literal_operand?
    pub det out fires?

    inst core: in_core {
        construct, constant_args?, comparable?, infinite_output?, ground?, infinite_elems?, finite_range?, literal_operand?,
    }

    req rule: fires? iff not core.decidable?
}
```

## Empty collections

`length_zero` fires on a comparison of a string's or sequence's `len` with
`0` or `1` that says that it is empty, or that it is not. A length is never
negative, so `n = 0`, `n <= 0` and `n < 1` each say that it is empty, and
become `s = ""`, or `q = []`, and `n != 0`, `n > 0` and `n >= 1` each say
that it is not, and become `s != ""`. So does each with the length on the
right: `0 < s.len` is `s.len > 0`. `card_zero` is the same for a set's or
relation's `card`, with `{}`. Both are fixable. Other comparisons with `0`
or `1`, such as `n >= 0`, which always holds, are left as they are.
`lint::length_zero` states which comparisons they fire on:

```fren
pub comp length_zero {
    in op: Comparison
    in bound: Int        -- the literal compared with
    in left?             -- the length is the left operand, rather than the right
    pub det out fires?
    pub det out empty?   -- the fix says that it is empty, rather than not

    req rule: fires? iff (if left?
        then (bound = 0 and op in {Eq, Ne, Le, Gt}) or (bound = 1 and op in {Lt, Ge})
        else (bound = 0 and op in {Eq, Ne, Ge, Lt}) or (bound = 1 and op in {Gt, Le}))
    req fix: empty? iff (if left? then op in {Eq, Le, Lt} else op in {Eq, Ge, Gt})

    expect not_negative: when op = Lt and bound = 0 and left?, not fires?
}
```

Each fix is exact: where the lint fires, the comparison of a length `n`
holds exactly when the fix does, `n = 0` if it says that the collection is
empty and `n != 0` if not. `compares?` is the value of a comparison:

```fren
fn compares?(op: Comparison, a: Int, b: Int) := match op {
    Eq => a = b,
    Ne => a != b,
    Lt => a < b,
    Le => a <= b,
    Gt => a > b,
    Ge => a >= b,
}

comp length_zero_exact {
    in op: Comparison
    in bound: Int
    in left?
    in n: Int            -- the length

    assume length: n >= 0

    inst p: length_zero { op, bound, left? }

    expect exact: when p.fires?,
        compares?(op, if left? then n else bound, if left? then bound else n) iff (p.empty? iff n = 0)
}
```

## Membership

`singleton_membership` fires on `x in {a}`, which is `x = a`, and is
fixable. `membership_chain`, `allow` by default, fires on a disjunction of
three or more equations of one expression with others, `x = a or x = b or x
= c`, whose fix is `x in {a, b, c}`, and on its De Morgan dual, a
conjunction of three or more disequations, `x != a and x != b and x != c`,
whose fix is `not x in {a, b, c}`.

In the chain, each operand is guarded by those before it (see
[Expressions](Lang/Expressions.md#sequences)): `x = b` by `not x = a`, and
`x != b` by `x != a`. In the fix, each value is evaluated where the chain
is. A comparison of `x` with values, with `=`, `!=` or `in`, is defined
wherever `x` and the values are, and `x` and the first value are evaluated
where the chain is in either form, so the fix keeps their guards, but not
those of the later values. So the lint does not fire if a value after the
first indexes a sequence, which might be out of range: `x = 1 or x = q[0] or
x = 2` is left as it is. `lint::membership_chain` states when it fires,
from the number of operands of the chain, whether they all equate, or
disequate, the same expression, written the same way, on their left, and
whether a later value indexes a sequence:

```fren
pub comp membership_chain {
    in n: Int            -- operands of the chain of `or`, or of `and`
    in same_left?        -- each is an equation, or for `and` a disequation, with the same left operand
    in later_indexes?    -- a value after the first indexes a sequence
    pub det out fires?

    assume counts: n >= 2

    req rule: fires? iff (same_left? and n >= 3 and not later_indexes?)
}
```

## Outputs

`constant_output` fires on a [defined output](Lang/Components.md#defined-outputs)
whose definition mentions no variable and no uninterpreted function (see
[Mentions](Lang/Expressions.md#mentions)): it is the same in every behaviour,
so it is a constant. `definable_output`, `allow` by default, fires on an
output, not defined, that exactly one requirement constrains, unconditionally,
as `x = e` or `x? iff e`, where `e` does not mention `x`: the requirement
could be its definition. `lint::output_lints` states both:

```fren
pub comp output_lints {
    in defined?              -- the output is defined
    in mentions?             -- its definition mentions a variable or an uninterpreted function, if defined
    in n_reqs: Int           -- requirements that mention it, if not defined
    in equation?             -- the only one is `x = e` or `x? iff e`, with `e` not mentioning `x`
    pub det out constant?    -- `constant_output` fires
    pub det out definable?   -- `definable_output` fires

    assume counts: n_reqs >= 0

    req constant: constant? iff (defined? and not mentions?)
    req definable: definable? iff (not defined? and n_reqs = 1 and equation?)

    expect exclusive: not (constant? and definable?)
}
```

## Indexes

`index_after_use` fires on `a and b`, where `a` indexes a sequence `q` and
`b` bounds it: it mentions `q.len`, or compares `q` with `[]`. The index is
probably meant to be guarded by `b`, but `and` guards its right operand by
its left (see [Expressions](Lang/Expressions.md#sequences)), so the
[definedness check](Check.md#definedness) fails. The fix swaps the
operands, which does not change the meaning. The lint looks only at the
text, never at the solver:

```fren
pub comp index_after_use {
    in indexes_left?     -- `a` indexes a sequence `q`
    in bounds_right?     -- `b` mentions `q.len`, or compares `q` with `[]`
    pub det out fires?

    req rule: fires? iff (indexes_left? and bounds_right?)
}
```

## Chains of methods

`redundant_method_chain` fires on a chain of methods without arguments,
`e.m1.m2...`, that has a shorter form with the same value, and is fixable.
The shorter form rewrites each pair of methods in this table, until none is
left:

| Written | Shorter form | Since |
|---|---|---|
| `q.rev.rev` | `q` | reversing twice gives the elements back in their order |
| `r.inverse.inverse` | `r` | swapping the members of each pair twice gives the pair back |
| `r.closure.closure` | `r.closure` | the transitive closure is idempotent: a chain of pairs of `r.closure` joins chains of pairs of `r` into one |
| `r.inverse.domain` | `r.range` | the first members of the pairs `(b, a)` are the second members of the pairs `(a, b)` |
| `r.inverse.range` | `r.domain` | and the other way around |
| `r.inverse.card` | `r.card` | swapping the members of a pair is one-to-one, so the pairs are as many |
| `q.rev.len` | `q.len` | reversing keeps every element |
| `r.closure.domain` | `r.domain` | `r` is within `r.closure`, and a chain from `a` starts with a pair `(a, b)` of `r` |
| `r.closure.range` | `r.range` | and a chain to `c` ends with a pair `(b, c)` of `r` |

Each holds for every relation and sequence, empty ones included: the
inverse and the closure of an empty relation are empty, and so are its
domain and range, and `[].rev` is `[]`. Each rewrite shortens the chain, so
rewriting ends, and the form it ends with does not depend on which pair is
rewritten first: where two pairs overlap, as in `r.inverse.inverse.domain`,
either order gives `r.domain`. The message is reported once, at the whole
chain. The fix replaces it with its shorter form, in which the receiver
keeps the text it is written with. When no method is left, the receiver
alone is written without the parentheses a receiver may need, and put in
parentheses where it is an operand that requires them
([`lang::operand`](Lang/Expressions.md#operators)), so `(a ++ b).rev.rev = c`
becomes `a ++ b = c`. A method has no guard of its own, and the fix
evaluates the receiver where the chain did, so it keeps every guard: it
only stops evaluating methods, which index nothing.

`lint::method_chain` states the rewrite of a pair, `e.inner.outer`: to `e`,
to `e.single`, or none:

```fren
use lang::{Annot, Method}

pub enum ChainFix { Keep, Receiver, Single }

pub comp method_chain {
    use lang::Method::{Card, Closure, Domain, Inverse, Len, Range, Rev}
    in inner: Method     -- the method of `e.inner`
    in outer: Method     -- the method called on `e.inner`
    pub det out fix: ChainFix
    pub det out single: Method  -- for `Single`, the method of the shorter form

    req rule: fix = if inner = outer and inner in {Rev, Inverse} then ChainFix::Receiver
        else if (inner = Inverse and outer in {Domain, Range, Card}) or (inner = Rev and outer = Len)
        or (inner = Closure and outer in {Closure, Domain, Range}) then ChainFix::Single
        else ChainFix::Keep
    req shorter: single = if inner = Inverse and outer = Domain then Range
        else if inner = Inverse and outer = Range then Domain
        else outer

    expect receiver_twice: when fix = ChainFix::Receiver, inner = outer
    expect closure_kept: when inner = Closure and fix = ChainFix::Single, single = outer
}
```

## Trivial patterns

`trivial_pattern` fires on `s.matches?(p)`, where the
[pattern](Lang/Expressions.md#patterns) `p` is a nonempty string `lit`,
written with characters that are not special and escapes `\c`, with `.*`
at its start, its end, both or neither, and is fixable:

| Pattern | Fix |
|---|---|
| `lit` | `s = "lit"` |
| `lit.*` | `s.starts_with?("lit")` |
| `.*lit` | `s.ends_with?("lit")` |
| `.*lit.*` | `s.contains?("lit")` |

The fix writes `lit` as a string literal that is not raw, with each `\c` as
the character `c`, and with the escapes that a [literal](Lang/Lexical.md#literals)
needs: `\\` for `\`, `\"` for `"`, `\n` and `\t`, and `\xHH` for the other
control characters. So `s.matches?(r"a\.b.*")` becomes
`s.starts_with?("a.b")`. The receiver keeps the text it is written with; in
`s = "lit"`, it is written without the parentheses a receiver may need, and
put in parentheses where it is an operand of `=` that requires them, and so
is the equation, where it is an operand that requires them
([`lang::operand`](Lang/Expressions.md#operators)). The fix evaluates the
receiver where the pattern did, and nothing else, so it keeps every guard.

Clippy's `trivial_regex` is in its `nursery` group, because of the quirks
of Rust's `regex` crate. Fren's patterns have none: a pattern always
matches the whole string, and has no flags, anchors or classes of
characters such as `\d`. So `trivial_pattern` is in `style`. For
[decidability](Lang/Decidability.md#strings), the four forms are the same:
`matches?` with a literal pattern, `starts_with?`, `ends_with?` and
`contains?` with a constant, and an equation with a constant are each in
the decidable core, so the fix never changes whether a component is
decidable.

`lint::trivial_pattern` states when it fires, from the value of the
literal, and which fix it makes:

```fren
pub enum PatternFix { Equality, StartsWith, EndsWith, Contains }

pub comp trivial_pattern {
    in pattern: String       -- the value of the literal
    pub det out fires?
    pub det out fix: PatternFix

    req rule: fires? iff pattern.matches?(r"(\.\*)?([^\\.\[\]()*+?{}|^]|\\[\\.\[\]()*+?{}|^-])+(\.\*)?")
    req which: fix = if pattern.starts_with?(".*") then (if pattern.ends_with?(".*") then PatternFix::Contains
        else PatternFix::EndsWith)
        else if pattern.ends_with?(".*") then PatternFix::StartsWith
        else PatternFix::Equality

    expect not_everything: when pattern = ".*", not fires?
    expect classes_kept: when pattern = "[a-z]", not fires?
}
```

## Boolean types

A name that ends in `?` is a `Bool`, so `in ready?: Bool` declares the same
input as `in ready?` (see [Boolean names](Lang/Types.md#boolean-names)).
`redundant_bool_type` fires on a `: Bool` that the rule implies: on a
variable, input or output, defined or not, on a field of a record, on a
parameter of a defined function, and on a function's result type. It is
reported at `: Bool`, and the fix removes it, with the spaces before it,
from the end of the name, or of the `)` before a result type: `fn ok?(n:
Int): Bool := n > 0` becomes `fn ok?(n: Int) := n > 0`. A declaration has no
guard. `lint::redundant_bool_type` states when it fires, from a declaration
that [`lang::bool_naming`](Lang/Types.md#boolean-names) accepts:

```fren
pub comp redundant_bool_type {
    in name: String      -- the declared name
    in annot: Annot
    pub det out fires?

    req rule: fires? iff (name.ends_with?("?") and annot = Annot::BoolTy)

    expect written: when fires?, annot != Annot::Missing
}
```

## Trivial matches

`trivial_match` fires on a `match` of one arm, whose pattern binds no name:
`_`, the variant of an enumeration with one variant, without a payload or
with `_` for each of its values, or an or-pattern. A `match` is exhaustive
(see [Matches](Lang/Expressions.md#matches)), so that arm matches every
value of the scrutinee, and the `match` is the arm's body. Like Clippy's
`match_single_binding`, it is in `complexity`, and it is fixable. The fix
replaces the `match` with the body, which keeps the text it is written
with, and is put in parentheses where it is an operand that requires them
([`lang::operand`](Lang/Expressions.md#operators)): `x = 2 * match e { _ =>
x - 1 }` becomes `x = 2 * (x - 1)`. The body's guard is the guard of the
`match` and its pattern's test, which every value passes, so it is the
guard of the `match`, where the fix puts the body. The fix only drops the
scrutinee, which removes what was evaluated, so no guard is weaker.
`lint::trivial_match` states when it fires:

```fren
pub comp trivial_match {
    in n_arms: Int
    in binds?            -- the first arm's pattern binds a name
    pub det out fires?

    assume counts: n_arms >= 1

    req rule: fires? iff (n_arms = 1 and not binds?)
}
```

## Matches

The match lints look at the arms of a
[`match`](Lang/Expressions.md#matches) as written. All three are fixable.

`match_same_arms`, `allow` by default, fires on two arms whose bodies are
written the same, ignoring whitespace, and whose patterns bind no names.
It is reported once for each group of such arms, at the first arm that
the fix removes, and says which arm it repeats. The fix depends on the
group:

- If neither arm is `_`, the fix merges the group into one arm, with an
  or-pattern of their alternatives, `A | B => body`, where the first of
  them is.
- If one is `_`, the fix removes the others, and `_` then matches their
  variants.
- If the group is every arm of the `match`, the fix replaces the `match`
  with the body, in parentheses where `lang::operand` requires them.

Neither changes what the `match` means. No variant is named twice, and
`_` is the last arm, so a variant is matched by the same body after the
fix as before, whatever the order of the arms. A body's guard is the test
of its arm's pattern, and after the fix it is the disjunction of the
guards of the arms it replaces, under each of which the body was already
evaluated. A pattern that binds a name is not merged, since its body
could mention the name. `lint::match_same_arms` states when it fires on
two arms, and the fix of their group:

```fren
pub enum ArmsFix { Merge, Remove, Replace }

pub comp match_same_arms {
    in same_body?        -- the bodies are written the same, ignoring whitespace
    in binds?            -- the pattern of either binds a name
    in wildcard?         -- one of the group is `_`
    in all?              -- the group is every arm of the `match`
    pub det out fires?
    pub det out fix: ArmsFix

    req rule: fires? iff (same_body? and not binds?)
    req group_fix: fix = if all? then ArmsFix::Replace else if wildcard? then ArmsFix::Remove else ArmsFix::Merge
}
```

`match_like_membership` fires on a `match` on `x` whose bodies are the
literals `true` and `false`, each at least once, and whose patterns name
only variants without a payload, or are `_`. It says whether `x` is one of
the variants whose arms are `true`. The fix is `x in {E::A, E::B}`, of
those variants, or `x = E::A` for one, if the `_` arm is `false`, or if
there is no `_` arm and no more variants are `true` than `false`.
Otherwise it is `not x in {...}`, or `x != E::A`, of the variants that are
`false`. The variants are written as the patterns write them, so a variant
brought into scope by `use` stays unqualified, and `x` and the result are
in parentheses where `lang::operand` requires them. The bodies are
literals, which guard nothing, and `x` is evaluated as before. A `match`
whose arms are all `true`, or all `false`, is left to `match_same_arms`.
`lint::match_like_membership` states when it fires, and when its fix is
negated:

```fren
pub comp match_like_membership {
    in bool_bodies?      -- every body is `true` or `false`, and each is some body
    in no_payloads?      -- every pattern names variants without a payload, or is `_`
    in wildcard?         -- there is a `_` arm
    in wildcard_true?    -- its body is `true`
    in n_true: Int       -- variants named by arms whose body is `true`
    in n_false: Int      -- and by arms whose body is `false`
    pub det out fires?
    pub det out negated?  -- the fix is a negated membership, of the `false` variants

    assume counts: n_true >= 0 and n_false >= 0

    req rule: fires? iff (bool_bodies? and no_payloads?)
    req negated: negated? iff (if wildcard? then wildcard_true? else n_true > n_false)

    expect fewer_listed: when not wildcard? and negated?, n_false < n_true
}
```

`wildcard_single_variant`, `allow` by default, fires on a `_` arm that
matches exactly one variant. The fix names it: `E::V`, or `E::V(_, _)`
with one `_` per value of its payload, written as another pattern of the
`match` writes its variant's path, or as `V` or `E::V` if one of those
names it. If none does, the lint has no fix. A variant added to the
enumeration later then makes the `match` non-exhaustive, a static error,
rather than being matched by `_` without notice. The arm matches the same
variant as before, and its body's guard, that no earlier arm matches, is
then the test of that variant, which means the same. If `fren fix` also
removes an arm of the `match` that has the body of the `_` arm
(`match_same_arms`), `_` then matches more than one variant, so
`wildcard_single_variant` is not fixed. `lint::wildcard_single_variant`
states when it fires:

```fren
pub comp wildcard_single_variant {
    in n_matched: Int    -- variants that no other arm names
    pub det out fires?

    assume reachable: n_matched >= 1

    req rule: fires? iff n_matched = 1
}
```

## Variant tests

`if_chain_match`, `allow` by default, fires on a chain `if T1 then a else
if T2 then b ... else z` of two or more tests, each a *variant test*: a test
of which variant a scrutinee `x` is, `x = E::V`, `x in {E::V, E::W}`, or an
`or` of such tests. The scrutinee is written the same in every test,
ignoring whitespace, and each variant has no payload: `x = E::V(a)` compares
the payload too. The chain starts at an `if` that is not the `else` branch
of another. Its fix is a [`match`](Lang/Expressions.md#matches), `match x {
V => a, W | X => b, ..., _ => z }`, with an arm for each test, whose
pattern is an or-pattern if the test names several variants. A `match`
names no variant twice, so the lint does not fire if a variant is tested
twice. If the tests name every variant, the final `else` is never taken,
and the fix drops it, since a `_` arm that covers no variant is an error.

The fix keeps the meaning, and the guards. In the chain, a branch is
guarded by its test and the negations of the tests before it, which, since
no variant is tested twice, is its test alone: the test of its arm's
pattern. `z` and the `_` arm are both guarded by the negations of all the
tests. The scrutinee is evaluated once, where the first test was. A body
that is a top-level `when` or `unless`, which an arm's body cannot be, is
put in parentheses, and so is a scrutinee with a `{`, which after `match`
would start the arms. `lint::if_chain_match` states when it fires and
whether the fix has a `_` arm:

```fren
pub comp if_chain_match {
    in n_tests: Int      -- tests in the chain
    in variant_tests?    -- each is a variant test of the same scrutinee
    in n_repeated: Int   -- times a test names a variant that it, or an earlier test, names before
    in n_untested: Int   -- variants of the enumeration that no test names
    pub det out fires?
    pub det out wildcard?  -- the fix keeps the final `else`, as the `_` arm

    assume counts: n_tests >= 1 and n_repeated >= 0 and n_untested >= 0

    req rule: fires? iff (variant_tests? and n_tests >= 2 and n_repeated = 0)
    req fix: wildcard? iff n_untested > 0
}
```

`case_split_reqs`, `allow` by default, fires on a component with two or
more requirements `when T, y = e`, or `when T, y? iff e`, of one output
`y`, whose conditions `T` are variant tests of one scrutinee `x`, naming no
variant twice. Together they say what one requirement `y = match x { ...
}` says, with an arm for each, and `_ => y` if some variant is not tested,
for which they leave `y` unconstrained. Its message is reported at the
second of them, names them all, and suggests that requirement. A
requirement `unless T, y = e` is not one of them: it constrains `y` for the
variants that `T` does not name. As in a `match` arm, `e` is guarded by
`T`. There is no fix: traces, claims and `impl`s refer to requirements by
name, so merging them changes the structure of the spec, not only its text.
`lint::case_split_reqs` states when it fires:

```fren
pub comp case_split_reqs {
    in n_cases: Int      -- requirements `when T, y = e` of one output, whose `T` are variant tests of one scrutinee
    in n_repeated: Int   -- times a test names a variant that it, or an earlier test, names before
    pub det out fires?

    assume counts: n_cases >= 0 and n_repeated >= 0

    req rule: fires? iff (n_cases >= 2 and n_repeated = 0)
}
```

## Bindings

`redundant_bindings` fires on a binding of an instance, or a field of a
record literal, written `x := x`, and is fixable. The fix is `x`, which
means `x := x` by definition, for [bindings](Lang/Instances.md)
and [fields](Lang/Expressions.md#records) alike, so it keeps the meaning
and the guards. `lint::redundant_bindings` states when it fires, from the
texts of the name and of the expression after `:=`:

```fren
pub comp redundant_bindings {
    in name: String      -- the name bound, or the field given
    in value: String     -- the expression after `:=`, as written
    pub det out fires?

    req rule: fires? iff value = name
}
```

## Suspicious expressions

These lints fire on expressions that are legal but probably not what the
writer meant. Two expressions are *written the same* if their texts agree
but for whitespace: outside string literals, whitespace that does not
separate two names, numbers or keywords is ignored, and the parentheses
around an operand are not part of it. The lints look only at the text,
never at types or the solver, so `f(x) = f(x)` is written the same, and
`x = (x)`, but `x + 1 = 1 + x` is not.

`eq_op` fires on an infix operator whose two operands are written the
same, where the expression is then always the same value, or the same as
its operand: `x = x`, `x <= x`, `x >= x`, `a? iff a?` and `s subset s`
are always `true`; `x != x`, `x < x` and `x > x` are always `false`;
`x - x` is always `0` and `s minus s` always `{}`; `a? and a?`, `a? or
a?`, `s union s` and `s inter s` are the operand. The message says which.
It has no fix: the likely mistake is a typo in one operand, which no
rewrite can repair. It does not fire on `+`, `*`, `++` or `join`, where `x
+ x` and `r join r` mean something, nor on `in`. `lint::eq_op` states
this:

```fren
pub enum InfixOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset, Add, Sub, Concat, Union, Minus, Mul, Inter, Join,
}

pub enum EqOpValue { AlwaysTrue, AlwaysFalse, Zero, Empty, Operand }

pub comp eq_op {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Operand, Zero}
    use self::InfixOp::{Add, Concat, Eq, Ge, Gt, Iff, In, Join, Le, Lt, Minus, Mul, Ne, Sub, Subset}
    in op: InfixOp
    in same?             -- the operands are written the same
    pub det out fires?
    pub out value: EqOpValue  -- what the expression is, where it fires

    req rule: fires? iff (same? and not op in {Add, Mul, Concat, Join, In})
    req values: when fires?, value = match op {
        Eq | Le | Ge | Iff | Subset => AlwaysTrue,
        Ne | Lt | Gt => AlwaysFalse,
        Sub => Zero,
        Minus => Empty,
        _ => Operand,
    }

    expect needs_same: when fires?, same?
}
```

`same_branches` fires on `if c then a else b`, where `a` and `b` are
written the same: the condition decides nothing. The fix replaces the
conditional with `a`, in parentheses where
[`lang::operand`](Lang/Expressions.md#operators) requires them, from the
operator that the conditional is an operand of, and only there; a
conditional counts as binding more loosely than any operator, as for
[`nonminimal_bool`](#simpler-bool-expressions). The value is `a`'s, and
the [guards](Lang/Expressions.md#sequences) of what remains get no
weaker: the copy of `a` guarded by `c` and the one guarded by `not c` are
both defined exactly when `a` is defined under the guard of the
conditional, which is `a`'s guard after the fix, and removing `c` only
removes something that is evaluated. A `match` whose arms are all written
the same is left to other lints. `lint::same_branches` states when it
fires:

```fren
pub comp same_branches {
    in same?             -- the branches are written the same
    pub det out fires?

    req rule: fires? iff same?
}
```

`duplicate_elements` fires on a set or relation literal with an element
written the same as an earlier one, as in `{a, b, a}` or `{(a, b), (a,
b)}`, and is reported once for the literal. A set has no repeats, so the
fix, which removes each repeat with the `,` before it, keeps the meaning,
and it keeps the guards, which are the same for every element of the
literal. It does not fire on a sequence literal, where a repeat means
something. `lint::duplicate_elements` states when it fires:

```fren
pub comp duplicate_elements {
    in n_repeats: Int    -- elements written the same as an earlier one
    pub det out fires?

    assume counts: n_repeats >= 0

    req rule: fires? iff n_repeats > 0
}
```

`empty_argument` fires on a method applied to an empty argument, where
its value at that [edge](Lang/Expressions.md#methods) does not depend on
the receiver as it seems to. An argument is empty if it is written `""`
or `[]`, or, as the length of `slice`, `0`. Where `s` is the receiver, a
string or a sequence, and `e` the empty argument:

| Written | Value |
|---|---|
| `s.starts_with?(e)`, `s.ends_with?(e)`, `s.contains?(e)` | `true` |
| `s.replace(e, b)` | `b ++ s` |
| `s.replace_all(e, b)` | `s` |
| `s.index_of(e, i)` | `i` if `0 <= i <= s.len`, and `-1` otherwise |
| `s.slice(i, 0)` | `""`, or `[]` |

The message says what the expression is. It has no fix: the likely
mistake is the argument, and writing the value instead would keep the
mistake and hide it. `lint::empty_argument` states when it fires, from the
method and the position of an empty argument:

```fren
pub comp empty_argument {
    use lang::Method::{Contains, EndsWith, IndexOf, Replace, ReplaceAll, Slice, StartsWith}
    in method: Method
    in index: Int        -- the position of the argument, from 0
    in empty?            -- it is written `""` or `[]`, or `0`
    pub det out fires?

    assume position: index >= 0

    req rule: fires? iff (empty? and match method {
        StartsWith | EndsWith | Contains | Replace | ReplaceAll | IndexOf => index = 0,
        Slice => index = 1,
        _ => false,
    })
}
```

## Comparisons

The lints of this section and the next three look at the operators and
method calls of an expression, in any constraint, binding, definition,
constant or global expectation, and are fixable. Like `nonminimal_bool`,
each fix puts an operand in parentheses where
[`lang::operand`](Lang/Expressions.md#operators) requires them, and only
there, and puts the fix itself in parentheses where it is an operand that
requires them and is not already in them; for this, a conditional counts
as binding more loosely than any operator. Two expressions are *written the
same* when their texts are the same, ignoring whitespace.

`double_comparison` fires on two comparisons of the same two operands,
written the same, joined by `and` or `or`, that together are one
comparison of those operands other than either of them:

| Written | Fix |
|---|---|
| `a < b or a = b` | `a <= b` |
| `a > b or a = b` | `a >= b` |
| `a < b or a > b` | `a != b` |
| `a <= b and a >= b` | `a = b` |
| `a <= b and a != b` | `a < b` |
| `a >= b and a != b` | `a > b` |
| `a subset b and b subset a` | `a = b` |

The two comparisons may come in either order, and the second may have its
operands the other way around, as in `b > a`, which is `a < b`; the fix
keeps the first's order. Orderings compare `Int`s or `String`s, which are
totally ordered, so whether a comparison holds depends only on whether `a`
is below, equal to or above `b`, and `lint::double_comparison_meaning`
checks that the fix holds in exactly the same cases as the two. Two sets
or relations are equal exactly when each is a subset of the other. The fix
keeps the guards: the second comparison is guarded by the first or by its
negation, but both evaluate the same operands, which the first does
unguarded, so the second is defined wherever the first is, and so is the
fix.

```fren
pub enum Order { Below, Same, Above }

pub comp comparison_holds {
    in op: Comparison
    in order: Order      -- how the left operand compares with the right
    pub det out holds?

    req rule: holds? iff match op {
        Eq => order = Order::Same,
        Ne => order != Order::Same,
        Lt => order = Order::Below,
        Le => order != Order::Above,
        Gt => order = Order::Above,
        Ge => order != Order::Below,
    }
}

pub comp double_comparison {
    in conjunction?      -- the comparisons are joined by `and`, rather than `or`
    in first: Comparison
    in second: Comparison  -- with its operands in the first's order
    pub det out fires?
    pub det out result: Comparison  -- the fix, if it fires; otherwise `first`

    req fires: fires? iff first != second and (if conjunction?
        then first in {Le, Ge, Ne} and second in {Le, Ge, Ne}
        else first in {Lt, Gt, Eq} and second in {Lt, Gt, Eq})
    req fix: result = if not fires? then first
        else if conjunction? then (if first != Ne and second != Ne then Eq else if Le in {first, second} then Lt else Gt)
        else (if first != Eq and second != Eq then Ne else if Lt in {first, second} then Le else Ge)
}

expect double_comparison_meaning: forall (d: double_comparison) (x y z: comparison_holds),
    when d.fires? and x.op = d.first and y.op = d.second and z.op = d.result
    and x.order = z.order and y.order = z.order,
    z.holds? iff (if d.conjunction? then x.holds? and y.holds? else x.holds? or y.holds?)
```

`bool_equality`, `allow` by default, fires on `a = b` where both operands
are `Bool`s, and its fix is `a iff b`, which means the same and says that
the two are equivalent. `iff` binds more loosely than `=`, so the fix may
need parentheses that the equation did not: `a? = b? and c?` becomes `(a?
iff b?) and c?`. The fix evaluates the same operands under the same guard.
It does not fire on `!=`, or where an operand is `true` or `false`, which
[`nonminimal_bool`](#simpler-bool-expressions) simplifies:

```fren
pub comp bool_equality {
    in op: Comparison
    in bools?            -- both operands are `Bool`s
    in literal?          -- an operand is `true` or `false`
    pub det out fires?

    req rule: fires? iff (op = Eq and bools? and not literal?)
}
```

## Searches

`manual_method` fires on a search written with `index_of` or `slice` that
a [method](Lang/Expressions.md#methods) says directly, on a string or a
sequence, whose methods have the same values:

| Written | Fix |
|---|---|
| `s.index_of(t, 0) >= 0`, `s.index_of(t, 0) > -1`, `s.index_of(t, 0) != -1` | `s.contains?(t)` |
| `s.index_of(t, 0) < 0`, `s.index_of(t, 0) <= -1`, `s.index_of(t, 0) = -1` | `not s.contains?(t)` |
| `s.index_of(t, 0) = 0` | `s.starts_with?(t)` |
| `s.slice(0, t.len) = t` | `s.starts_with?(t)` |

The bound, or the `t` that the slice is compared with, may be on the left.
For the slice, the receiver of `len` is written the same as the other
operand, or is it in parentheses.

`s.index_of(t, 0)` is the first position at which `t` occurs in `s`, which
is at least `0`, or `-1` if there is none. If `t` is `""`, it is `0`, since
`0 <= 0 <= s.len`, and `""` occurs in every `s`, as its prefix. If `s` is
shorter than `t`, `t` occurs nowhere in it, and it is `-1`. So the index is
at least `0` exactly when `t` occurs in `s`, which is `s.contains?(t)`, and
it is `0` exactly when `t` occurs at position `0`, which is
`s.starts_with?(t)`. `s.slice(0, t.len)` is the first `t.len` elements of
`s`, or all of `s` if it is shorter, and `""` if `t` is `""` (`n > 0`
fails) or `s` is (`0 < s.len` fails). It is `t` exactly when `t` is a
prefix of `s`: if `t` is `""`, both are `""`, and if `s` is shorter than
`t`, so is the slice. Every method is total, and the fix evaluates `s` and
`t` where the comparison did, so it keeps the guards.

`lint::index_test` states which comparisons of `index_of` fire, from the
operator and the bound, with the call on the left, and checks each against
every value that the call can take:

```fren
pub enum IndexTest { Found, Absent, AtStart, Other }

pub comp index_test {
    use self::IndexTest::{Absent, AtStart, Found, Other}
    in op: Comparison
    in bound: Int
    in position: Int     -- any value of `s.index_of(t, 0)`
    pub det out test: IndexTest

    assume positions: position >= -1

    req rule: test = match op {
        Ge => if bound = 0 then Found else Other,
        Gt | Ne => if bound = -1 then Found else Other,
        Lt => if bound = 0 then Absent else Other,
        Le => if bound = -1 then Absent else Other,
        Eq => if bound = -1 then Absent else if bound = 0 then AtStart else Other,
    }

    expect found: when test = Found, compares?(op, position, bound) iff position >= 0
    expect absent: when test = Absent, compares?(op, position, bound) iff position = -1
    expect at_start: when test = AtStart, compares?(op, position, bound) iff position = 0
}
```

The fix can bring a spec into the [decidable core](Lang/Decidability.md).
`index_of`, and `slice` of a sequence, are outside it unless every operand
is a constant, but `contains?` and `starts_with?` of a string are in it
when `t` is a constant, and `starts_with?` of a sequence is in it when `t`
is a literal. So on strings, each fix of `index_of` with a constant `t`
brings the comparison into the core, and the fix of `slice` changes
nothing, since `s.slice(0, t.len) = t` is already in the core when `t` is a
constant. On sequences, the fixes to `starts_with?` with a literal `t` do,
and those to `contains?` do not, since `contains?` of a sequence is outside
the core too.

## Conditional operands

A conditional is an atom, but its `else` branch extends as far right as
possible (see [Conditionals](Lang/Expressions.md#conditionals)): `2 * if
c? then x else y + 1` means `2 * (if c? then x else (y + 1))`, not `(2 * if
c? then x else y) + 1`. `else_extends` fires on a conditional, not in
parentheses, that is an operand of a binary operator, and whose `else`
branch would need parentheses in its place, as an operand of that
operator, under `lang::operand`. If the `else` branch is itself a
conditional not in parentheses, its own `else` branch counts instead, and
so on. The fix puts that branch in parentheses, as it is parsed, which
keeps the meaning and the guards, and shows where it ends:

```fren
use lang::{Assoc, operand}

pub comp else_extends {
    in outer: Int        -- the precedence of the operator
    in inner: Int        -- the precedence of the `else` branch's operator
    in assoc: Assoc      -- the associativity of the operator
    in right?            -- the conditional is the operator's right operand
    pub det out fires?

    inst place: operand { outer, inner, assoc, right? }

    req rule: fires? iff not place.bare?
}
```

## Identities

`identity_op` fires on an operation that leaves one operand as it is, and
its fix is that operand:

| Written | Fix |
|---|---|
| `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` | `x` |
| `s ++ ""`, `"" ++ s`, `q ++ []`, `[] ++ q` | `s`, `q` |
| `a union {}`, `{} union a`, `a minus {}` | `a` |

It also fires on `x + -y`, whose fix is `x - y`, and on `x - -y`, whose fix
is `x + y`. The fix has the operation's value and its type: the operands
of `+`, `-`, `*`, `++`, `union` and `minus` have the same type as the
result, and `""`, `[]` and `{}` are their identities, as `0` is of `+` and
`-` and `1` of `*`; `[]` and `{}` take their type from the other operand,
which keeps it. The operand removed is a literal, or a negation whose
operand the fix evaluates where it was, so the fix keeps the guards.
`lint::identity_op` states what the fix is, from the operator and what
each operand is:

```fren
pub enum IdentityOperator { Add, Sub, Mul, Concat, Union, Minus }

-- An operand as written: `Empty` is `""`, `[]` or `{}`, and `Negation` is `-y`.
pub enum IdentityOperand { Zero, One, Empty, Negation, Other }

pub enum Rewrite { KeepLeft, KeepRight, Flip, Unchanged }

pub comp identity_op {
    use self::IdentityOperand::{Empty, Negation, One, Zero}
    use self::IdentityOperator::{Add, Concat, Minus, Mul, Sub, Union}
    use self::Rewrite::{Flip, KeepLeft, KeepRight, Unchanged}
    in op: IdentityOperator
    in left: IdentityOperand
    in right: IdentityOperand
    pub det out rewrite: Rewrite  -- `Flip` is `x - y` for `x + -y`, and `x + y` for `x - -y`

    req rule: rewrite = match op {
        Add => if right = Zero then KeepLeft else if left = Zero then KeepRight
            else if right = Negation then Flip else Unchanged,
        Sub => if right = Zero then KeepLeft else if right = Negation then Flip else Unchanged,
        Mul => if right = One then KeepLeft else if left = One then KeepRight else Unchanged,
        Concat | Union => if right = Empty then KeepLeft else if left = Empty then KeepRight else Unchanged,
        Minus => if right = Empty then KeepLeft else Unchanged,
    }

    expect flips_only_sums: when rewrite = Flip, op in {Add, Sub}
}
```

## Arithmetic

`double_neg` fires on a negation of a negation, `- -x`, through
parentheses, as in `-(-x)` and `-(-(x))`: it is `x`, which is its fix.
`neg_multiply` fires on a product with `-1`, the negation of the literal
`1`, through parentheses: `x * -1` and `-1 * x` are `-x`, which is its fix.
`Int` is the integers, without overflow, so both fixes are exact. Both are
fixable:

```fren
pub comp double_neg {
    in negated_operand?  -- the operand of the negation, through parentheses, is a negation
    pub det out fires?

    req rule: fires? iff negated_operand?
}

pub comp neg_multiply {
    in left_minus_one?   -- the left operand, through parentheses, is `-1`
    in right_minus_one?  -- the right operand is
    pub det out fires?
    pub det out negate_left?  -- the fix negates the left operand, rather than the right

    req rule: fires? iff (left_minus_one? or right_minus_one?)
    req fix: negate_left? iff right_minus_one?
}
```

`int_plus_one` fires on a non-strict comparison of integers with an
operand off by one, where its fix is the strict comparison without the
offset. Where `1` is the literal, and `1 + b` is the same as `b + 1`:

| Written | Fix |
|---|---|
| `a >= b + 1`, `a >= 1 + b`, `a - 1 >= b` | `a > b` |
| `b + 1 <= a`, `1 + b <= a`, `b <= a - 1` | `b < a` |

Where both operands are off by one, as in `a - 1 >= b + 1`, the fix drops
the `+ 1`: `a - 1 > b`. `lint::int_plus_one` states this, from the offset
of each operand of the comparison:

```fren
pub enum Offset { Zero, PlusOne, MinusOne }

use self::Offset::{MinusOne, PlusOne, Zero}

pub comp int_plus_one {
    in op: Comparison
    in left: Offset      -- `e + 1` and `1 + e` are `PlusOne`, `e - 1` is `MinusOne`, and any other operand `Zero`
    in right: Offset
    pub det out fires?
    pub det out result: Comparison  -- the comparison of the fix
    pub det out drop_left?          -- the fix drops the offset of the left operand, rather than the right

    req rule: fires? iff ((op = Ge and (right = PlusOne or left = MinusOne))
        or (op = Le and (left = PlusOne or right = MinusOne)))
    req strict: result = (if op = Ge then Gt else if op = Le then Lt else op)
    req drop: drop_left? iff (if op = Ge then right != PlusOne else op = Le and left = PlusOne)
}
```

The fix is exact: over the integers, where the lint fires, the comparison
of the operands, `a` and `b` with their offsets, holds exactly when the
fix does:

```fren
fn offset_value(o: Offset): Int := match o { Zero => 0, PlusOne => 1, MinusOne => -1 }

comp int_plus_one_exact {
    in op: Comparison
    in left: Offset
    in right: Offset
    in a: Int            -- the left operand, without its offset
    in b: Int            -- the right operand, without its offset

    inst p: int_plus_one { op, left, right }

    expect exact: when p.fires?, compares?(op, a + offset_value(left), b + offset_value(right))
        iff compares?(p.result, if p.drop_left? then a else a + offset_value(left),
        if p.drop_left? then b + offset_value(right) else b)
}
```

Each of these fixes writes its operands with the text they are written
with, in parentheses where [`lang::operand`](Lang/Expressions.md#operators)
requires them, and only there, and the fix itself in parentheses where it
is an operand that requires them and is not already in parentheses, as for
[`nonminimal_bool`](#simpler-bool-expressions): `2 * - -(x + y)` becomes `2
* (x + y)`, `(a + b) * -1` becomes `-(a + b)`, and `(x) >= y + 1` becomes
`x > y`. A negation of an operand that starts with `-` is written with a
space, `- -y`, since `--` starts a comment. No fix adds or removes an
`and`, `or`, `when`, `unless`, `if` or `match`, and each operand is
evaluated where it was, so the guards are kept.

## Parentheses

`double_parens` fires on parentheses directly around parentheses, with
nothing but whitespace between them: `((e))` means what `(e)` means. It
fires once for each run of such pairs, at the outermost, and its fix keeps
only the innermost: `(((e)))` becomes `(e)`. The parentheses of an
application or a method call are its own, not around its argument, so
`f((x))` has one pair around `x`. Parentheses only group, so the fix
changes neither the meaning nor the guards. `lint::double_parens` states
when it fires:

```fren
pub comp double_parens {
    in depth: Int        -- pairs of parentheses, each directly around the next
    pub det out fires?

    assume counts: depth >= 1

    req rule: fires? iff depth >= 2
}
```

## Expecting lints

`set_option fren.lint.LINT "expect"` says that the lint should fire where
the setting is in effect: the lint's messages
there are not reported, and if it does not fire at all there, the
`set_option` gets a message from the lint `unfulfilled_lint_expectations`,
at the end of the file. This documents a known lint where it is
deliberate, and points out the setting once it is no longer needed.

A lint *fires* where its condition holds and its level is not `allow`. A
lint that fires is reported with the severity of its level, or, at
`expect`, fulfils the expectation in effect there.

`set_option fren.lint.GROUP "expect"` is one expectation, for every lint
of the group, and any of them that fires there fulfils it.

Each `set_option` to `expect` is its own expectation: a lint that fires
fulfils only the expectation in effect where it fires, so the second of
two such settings in a row is fulfilled only by what follows it. The level
of `unfulfilled_lint_expectations` is the one in effect at the
`set_option`; for it, `expect` means `allow`. `lint::expectation` states
when an expectation is fulfilled:

```fren
pub comp expectation {
    in n_fired: Int      -- times the lint fires where this expectation is in effect
    in level: Level      -- of `unfulfilled_lint_expectations`, at the `set_option`
    pub det out fulfilled?
    pub det out reported?

    assume counts: n_fired >= 0

    req fulfilled: fulfilled? iff n_fired > 0
    req reported: reported? iff (not fulfilled? and not level in {Allow, Expect})

    expect fired_is_quiet: when n_fired > 0, not reported?
}
```

## Fixing lints

```
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
```

`fren fix` reads and elaborates the files as [`fren check`](Cli.md) does,
then rewrites them to fix the lints that fire, where a fix cannot change
what the spec means:

<!-- keep-sorted start skip_lines=2 -->
| Lint | Fix |
|---|---|
| `bool_equality` | replaces `a = b` with `a iff b` |
| `card_zero` | compares the set with `{}`, as the message suggests |
| `collapsible_when` | collapses the two conditionals into one, as the message suggests |
| `double_comparison` | replaces the two comparisons with the one they are |
| `double_neg` | replaces `- -x` with `x` |
| `double_parens` | removes all but the innermost pair of parentheses |
| `duplicate_elements` | removes each repeated element, with the `,` before it |
| `else_extends` | puts the `else` branch in parentheses |
| `glob_imports` | imports by name the variants that the file uses through the glob: `use E::*` becomes `use E::{A, B}`, or `use E::A` for a single variant |
| `identity_op` | replaces the operation with the operand it leaves as it is, `x + -y` with `x - y`, and `x - -y` with `x + y` |
| `if_chain_match` | replaces the chain with a `match` |
| `if_not_else` | removes the negation and swaps the branches, as the message suggests |
| `index_after_use` | swaps the operands of the `and` |
| `int_plus_one` | replaces the comparison with the strict one, without the offset |
| `length_zero` | compares the string with `""`, or the sequence with `[]`, as the message suggests |
| `manual_method` | replaces the comparison with a call of `contains?` or `starts_with?`, as the message suggests |
| `match_like_membership` | replaces the `match` with a membership, `x in {E::A, E::B}`, as the message suggests |
| `match_same_arms` | merges the arms into one with an or-pattern, removes those with the body of the `_` arm, or replaces the `match` with its body, as the message suggests |
| `membership_chain` | replaces the chain with a membership, `x in {a, b, c}`, or `not x in {a, b, c}` |
| `neg_multiply` | replaces `x * -1` or `-1 * x` with `-x` |
| `nonminimal_bool` | replaces the expression with its simpler form, as the message suggests |
| `redundant_bindings` | replaces `x := x` with `x` |
| `redundant_bool_type` | removes the `: Bool` |
| `redundant_method_chain` | replaces the chain with its shorter form |
| `same_branches` | replaces the conditional with its `then` branch |
| `singleton_membership` | replaces `x in {a}` with `x = a` |
| `trivial_match` | replaces the `match` with its arm's body |
| `trivial_pattern` | replaces `s.matches?(p)` with an equation or a call of `starts_with?`, `ends_with?` or `contains?` |
| `unfulfilled_lint_expectations` | removes the `set_option`, or for `set_option ... in item`, removes `set_option ... in` and keeps the item |
| `unless_not` | removes the negation and writes `when`, as the message suggests |
| `unused_imports` | removes the `use`, or the name from a grouped `use` |
| `wildcard_single_variant` | names the variant, `E::V`, or `E::V(_, _)` with one `_` per value of its payload |
<!-- keep-sorted end -->

Each fix that rewrites an expression keeps what the expression means, for
every value of what it mentions. `lint::fixes_keep_meaning` states it for
each such fix, with the written form, which the lint fires on, on the left
of each `iff`, and the fixed form on the right. It expects the lints, so
it also checks that each of them fires somewhere in it, though not that
it fires on every form. `index_after_use` is left out: its fix only swaps
the operands of `and`, which means the same either way round, and its
written form has an index that may be out of range.

```fren
set_option fren.lint.nonminimal_bool "expect" in
set_option fren.lint.length_zero "expect" in
set_option fren.lint.card_zero "expect" in
set_option fren.lint.singleton_membership "expect" in
set_option fren.lint.membership_chain "expect" in
pub comp fixes_keep_meaning {
    in a?
    in c?
    in x: Int
    in y: Int
    in z: Int
    in w: Int
    in s: String
    in q: Seq(Int)
    in t: Set(Int)
    in r: Rel(Bool, Bool)

    expect true_literals: ((a? = true) iff a?) and ((a? != false) iff a?) and ((a? iff true) iff a?)
    expect false_literals: ((a? = false) iff not a?) and ((a? != true) iff not a?) and ((a? iff false) iff not a?)
    expect literals_left: ((true = a?) iff a?) and ((true iff a?) iff a?) and ((false = a?) iff not a?)
    expect double_negation: (not not a?) iff a?
    expect negated_literal: (not (a? = true)) iff not a?
    expect complements: ((not (x = y)) iff x != y) and ((not (x != y)) iff x = y)
        and ((not (x < y)) iff x >= y) and ((not (x <= y)) iff x > y)
        and ((not (x > y)) iff x <= y) and ((not (x >= y)) iff x < y)
    expect conditionals: ((if c? then true else false) iff c?) and ((if c? then false else true) iff not c?)
    expect string_length_zero: ((s.len = 0) iff s = "") and ((s.len <= 0) iff s = "") and ((s.len > 0) iff s != "")
    expect sequence_length_zero: ((q.len = 0) iff q = []) and ((q.len <= 0) iff q = []) and ((q.len > 0) iff q != [])
    expect card_zero: ((t.card = 0) iff t = {}) and ((t.card <= 0) iff t = {}) and ((t.card > 0) iff t != {})
    expect relation_card_zero: ((r.card = 0) iff r = {}) and ((r.card > 0) iff r != {})
    expect singleton: (x in {y}) iff x = y
    expect chain: (x = y or x = z or x = w) iff x in {y, z, w}
}
```

The other lints have no fix. Renaming a declaration, as the naming lints
would need, would also have to rename every use
of it, including uses in Lean code and in files that are not given, and so
would removing a dead item. Removing an unused variable would change its
component's interface, and merging the requirements that `case_split_reqs`
reports would change what traces, claims and `impl`s name. A message of a lint that `fren fix` fixes says so, with the line
`` help: `fren fix` can fix this ``. In Lean, only the messages in a
[Markdown spec](Markdown.md) have this line, since `fren fix` does not read
Lean files.

- A lint is fixed where it fires at `warn`, `deny` or `forbid`, so `-A`
  and the other [level options](#setting-levels) choose what is fixed too.
  A lint at `expect` or `allow` is left as it is.
- `--only LINT` fixes only the lints given, and `--skip LINT` fixes all but
  those given. Both may be repeated, and a lint given to both is not fixed.
- `--ignore GLOB` leaves the matching files as they are. They are still
  read, since the other files may use their modules. Globs are as for
  [`fren fmt`](Fmt.md).
- With `--fmt`, `fren fix` then [formats](Fmt.md) each file that
  `--ignore` does not match, as `fren fmt` would.
- With `--check`, `fren fix` writes nothing, and instead prints what it
  would change, as a diff on standard output.

`lint::Lint` is the lints. `lint::fix_selected` gives whether a lint that
fires is fixed, from the sets given to `--only` and `--skip`, each empty
when the option is not given. A group given to either gives each of its
lints. A lint given twice is given once:

```fren
pub type Lint

pub comp fix_selected {
    in lint: Lint
    in only: Set(Lint)   -- the lints given to `--only`
    in skip: Set(Lint)   -- the lints given to `--skip`
    pub det out fixed?

    req rule: fixed? iff ((only = {} or lint in only) and not lint in skip)

    expect default_all: when only = {} and not lint in skip, fixed?
    expect only_excludes: unless only = {} or lint in only, not fixed?
    expect skip_wins: when lint in skip, not fixed?
}

-- Skipping more never fixes more.
expect skip_monotone: forall (a b: fix_selected),
    when a.lint = b.lint and a.only = b.only and a.skip subset b.skip and b.fixed?, a.fixed?
```

The lints that are not fixed are reported as `fren check` reports them. A
static error other than a denied lint stops `fren fix` before it writes
anything. The fixes are found from the files as given, and then again
from the files as fixed, until no fix is left: one fix can overlap
another, of which only the outer is made, or leave something that another
lint fixes. There
are at most 10 passes, in case two fixes undo each other, and a pass whose
fixes would make a static error is not kept. The lints reported are those left
in the files as fixed, or with `--check`, which writes nothing, those that
the first pass does not fix, in the files as given. The fixes do not change the layout of what they
leave behind, which may then need formatting, as `--fmt` does.

`lint::import_fix` gives the fix of one `use` that is not in a group,
from the lints that fire at it and whether each is fixed. For a glob that
is both unused and fixed by `unused_imports`, removing it wins. A glob that
is unused is not imported by name, since nothing would use those names.

```fren
pub enum ImportFix { Keep, Remove, ByName }

pub comp import_fix {
    in unused?           -- `unused_imports` fires at the `use`
    in glob?             -- `glob_imports` fires at it
    in fix_unused?       -- `unused_imports` is fixed: `--only` and `--skip` allow it
    in fix_glob?         -- `glob_imports` is fixed
    in n_used: Int       -- distinct variants the file uses through it
    pub det out fix: ImportFix

    assume counts: n_used >= 0

    req rule: fix = if unused? and fix_unused? then ImportFix::Remove
        else if glob? and fix_glob? and not unused? and n_used > 0 then ImportFix::ByName
        else ImportFix::Keep

    expect quiet_kept: when not unused? and not glob?, fix = ImportFix::Keep
    expect by_name_is_glob: when fix = ImportFix::ByName, glob?
    expect skipped_kept: when not fix_unused? and not fix_glob?, fix = ImportFix::Keep
}
```

In a grouped `use`, each name is a `use` of its own, which is never a
glob: the names that `lint::import_fix` removes are removed from the group,
and if none is left, so is the `use`.

`lint::fix_exit` gives the exit status:

| Status | Meaning |
|---|---|
| 0 | the files were fixed, or, with `--check`, no file would change |
| 1 | with `--check`: some file would change |
| 2 | nothing was fixed: an unreadable file, bad arguments, or a static error other than a denied lint |

```fren
pub comp fix_exit {
    in check?            -- `--check` was given
    in loaded?           -- every file was read, and has no static error but denied lints
    in unchanged?        -- no file changes: no lint that is fixed fires, and with `--fmt`, every file is formatted
    pub det out code: Int

    req failed: unless loaded?, code = 2
    req pending: when loaded? and check? and not unchanged?, code = 1
    req fixed: when loaded? and (not check? or unchanged?), code = 0

    expect documented_codes: code >= 0 and code <= 2
}
```

`lint::fix_exit` follows the convention of every command,
[`cli::exit_status`](Cli.md#exit-status), with `fren fix` able to run
exactly when every file is loaded:

```fren
use cli::exit_status

refine fix_exit_status: fix_exit refines exit_status { ran? := loaded? }

#fren_check
```
