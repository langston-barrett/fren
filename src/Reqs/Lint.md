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
| Lint | Code | Default | Reported at |
|---|---|---|---|
| `card_zero` | `F0716` | `warn` | a comparison of a set's or relation's `card` with `0`, such as `s.card = 0` (see [Empty collections](#empty-collections)) |
| `constant_output` | `F0719` | `warn` | a defined output whose definition mentions no variable (see [Outputs](#outputs)) |
| `dead_code` | `F0711` | `warn` | a private enumeration, record, abstract type, function or constant that nothing in its file uses (see [Dead code](#dead-code)) |
| `definable_output` | `F0720` | `allow` | an output that one requirement equates with an expression of other variables (see [Outputs](#outputs)) |
| `glob_imports` | `F0702` | `warn` | a `use ...::*` (see [Glob imports](#glob-imports)) |
| `index_after_use` | `F0721` | `warn` | an index on the left of an `and` whose right bounds the sequence (see [Indexes](#indexes)) |
| `length_zero` | `F0715` | `warn` | a comparison of a string's or sequence's `len` with `0`, such as `s.len = 0` (see [Empty collections](#empty-collections)) |
| `membership_chain` | `F0718` | `allow` | `x = a or x = b or x = c`, three or more (see [Membership](#membership)) |
| `non_camel_case_types` | `F0704` | `warn` | an enumeration, variant, record or abstract type not named in `CamelCase` |
| `non_snake_case` | `F0703` | `warn` | a module, component, variable, function, instance, constraint or global expectation not named in `snake_case` (see [Naming conventions](#naming-conventions)) |
| `non_upper_case_constants` | `F0705` | `warn` | a constant not named in `UPPER_CASE` |
| `nonminimal_bool` | `F0712` | `warn` | a `Bool` expression with a simpler form, such as `a? = true` (see [Simpler `Bool` expressions](#simpler-bool-expressions)) |
| `shadowed_constants` | `F0713` | `warn` | a variable named like a constant in scope (see [Shadowed constants](#shadowed-constants)) |
| `singleton_membership` | `F0717` | `warn` | `x in {a}` (see [Membership](#membership)) |
| `undecidable` | `F0714` | `deny` | a construct outside the decidable core (see [Undecidable constructs](#undecidable-constructs)) |
| `unfulfilled_lint_expectations` | `F0706` | `warn` | a `set_option` that expects a lint that never fires (see [Expecting lints](#expecting-lints)) |
| `unused_imports` | `F0701` | `warn` | a `use` that nothing in its file uses (see [Unused imports](#unused-imports)) |
| `unused_variables` | `F0710` | `warn` | a variable or binder that nothing mentions (see [Unused variables](#unused-variables)) |
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
but `rule` does not look at it then. That a history is accepted exactly when
every step that `lint::setting` takes along it is cannot be stated without
a fold, so it is a tested claim.

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
item it is about: the `use` for the import lints; for the naming lints,
`unused_variables` and `shadowed_constants`, the item that declares the
name, which for a member is its component and for a variant its
enumeration; for `dead_code`, the unused item; and for `nonminimal_bool`,
the item the expression is in. So `set_option ... in` before an item sets
the level for that item alone.

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
`unused_imports` is set to `deny` ``, and there is no help line.

## Unused imports

A `use` is *used* if a path in the same file and module resolves through
it: the path's first segment resolves (see
[Resolution](Lang/Modules.md#resolution)) to the item it imports by name,
or to a variant of the enumeration it opens. Paths in expressions, types,
instances, global expectations, claims and `#fren_check` count. The paths of
`use` declarations do not, since they are absolute.

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
letter nor `_`. `lint::in_case` states the rule, for any name:

```fren
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
variable's name: the binding `x` in `inst w: c { x }` mentions `x`. A
binder `w` is mentioned by a path `w.x`. Mentions elsewhere, such as
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

A literal may be on either side of `=`, `!=` and `iff`; when both sides are
literals, the right one is taken as the literal. `lint::literal_comparison`
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
simplification of the operands. It does not cover the text: that the
simpler form, written with its parentheses, parses as the expression the
rules chose.

## Shadowed constants

A component's variables shadow names from its module (see
[Components](Lang/Components.md#members)), so a variable named like a
constant hides it, and `x * RATE` multiplies by the variable `RATE`.
`shadowed_constants` reports a variable of a component whose name resolves,
in the component's module, to a constant: one declared there or imported by
name. It is reported at the variable's declaration. Since constants are
named in `UPPER_CASE` and variables in `snake_case`, it only fires where a
[naming lint](#naming-conventions) would fire too, or is allowed.

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

`length_zero` fires on a comparison of `len` with `0` that says that a
string or sequence is empty, or that it is not: `s.len = 0` and `s.len <=
0` become `s = ""`, or `q = []`, and `s.len > 0` becomes `s != ""`.
`card_zero` is the same for a set's or relation's `card`, with `{}`. Both
are fixable. `lint::length_zero` states which comparisons they fire on,
with the length on the left and the literal on the right:

```fren
pub comp length_zero {
    in op: Comparison
    in bound: Int        -- the literal compared with
    pub det out fires?
    pub det out empty?   -- the fix says that it is empty, rather than not

    req rule: fires? iff (bound = 0 and op in {Eq, Le, Gt})
    req fix: empty? iff op != Gt

    expect not_negative: when op = Lt and bound = 0, not fires?
}
```

## Membership

`singleton_membership` fires on `x in {a}`, which is `x = a`, and is
fixable. `membership_chain`, `allow` by default, fires on a disjunction of
three or more equations of one expression with others, `x = a or x = b or x
= c`, and its fix is `x in {a, b, c}`. `lint::membership_chain` states when
it fires, from the number of disjuncts and whether they all equate the
same expression, written the same way, on their left:

```fren
pub comp membership_chain {
    in n: Int            -- disjuncts in the chain of `or`
    in same_left?        -- each is an equation with the same left operand
    pub det out fires?

    assume counts: n >= 2

    req rule: fires? iff (same_left? and n >= 3)
}
```

## Outputs

`constant_output` fires on a [defined output](Lang/Components.md#defined-outputs)
whose definition mentions no variable: it is the same in every behaviour,
so it is a constant. `definable_output`, `allow` by default, fires on an
output, not defined, that exactly one requirement constrains, unconditionally,
as `x = e` or `x? iff e`, where `e` does not mention `x`: the requirement
could be its definition. `lint::output_lints` states both:

```fren
pub comp output_lints {
    in defined?              -- the output is defined
    in n_variables: Int      -- variables its definition mentions, if defined
    in n_reqs: Int           -- requirements that mention it, if not defined
    in equation?             -- the only one is `x = e` or `x? iff e`, with `e` not mentioning `x`
    pub det out constant?    -- `constant_output` fires
    pub det out definable?   -- `definable_output` fires

    assume counts: n_variables >= 0 and n_reqs >= 0

    req constant: constant? iff (defined? and n_variables = 0)
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
| `card_zero` | compares the set with `{}`, as the message suggests |
| `glob_imports` | imports by name the variants that the file uses through the glob: `use E::*` becomes `use E::{A, B}`, or `use E::A` for a single variant |
| `index_after_use` | swaps the operands of the `and` |
| `length_zero` | compares the string with `""`, or the sequence with `[]`, as the message suggests |
| `membership_chain` | replaces the chain with a membership, `x in {a, b, c}` |
| `nonminimal_bool` | replaces the expression with its simpler form, as the message suggests |
| `singleton_membership` | replaces `x in {a}` with `x = a` |
| `unfulfilled_lint_expectations` | removes the `set_option`, or for `set_option ... in item`, removes `set_option ... in` and keeps the item |
| `unused_imports` | removes the `use`, or the name from a grouped `use` |
<!-- keep-sorted end -->

The other lints have no fix. Renaming a declaration, as the naming lints
and `shadowed_constants` would need, would also have to rename every use
of it, including uses in Lean code and in files that are not given, and so
would removing a dead item. Removing an unused variable would change its
component's interface. A message of a lint that `fren fix` fixes says so, with the line
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
when the option is not given. A lint given twice is given once:

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
anything. The fixes are found from the files as given, in a single pass.
They do not change the layout of what they leave behind, which may then
need formatting, as `--fmt` does.

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

#fren_check
```
