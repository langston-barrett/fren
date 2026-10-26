# Nonstandard style

The lints of the `nonstandard_style` group find a name in the wrong case
for what it names.

## Naming conventions

The case of a name says what it names:

| Case | Names | Lint |
|---|---|---|
| `snake_case` | modules, components, variables, fields, functions, instances, constraints, global expectations and their binders, and the binders of `match` patterns | `non_snake_case` |
| `CamelCase` | enumerations, variants, records and abstract types | `non_camel_case_types` |
| `UPPER_CASE` | constants | `non_upper_case_constants` |

`lint::naming_case` gives the case of the names of each
[`lint::Named`](Unused.md#dead-code):

```fren
pub mod lint

pub enum Case { Snake, Camel, Upper }

use self::Case::{Camel, Snake, Upper}

pub comp naming_case {
    use self::Named::{AbstractType, Constant, Enumeration, Record, TypeAlias, Variant}
    in what: Named
    pub det out case: Case

    ensure rule: case = match what {
        Enumeration | Variant | Record | AbstractType | TypeAlias => Camel,
        Constant => Upper,
        _ => Snake,
    }
}
```

A name is in `snake_case` if it has no uppercase letter, in `CamelCase` if
it starts with an uppercase letter and has no `_`, and in `UPPER_CASE` if
it starts with an uppercase letter and has no lowercase letter. Letters
are ASCII letters, and a variable's final `?` is ignored, which the
[patterns](../Lang/Expressions.md#patterns) below do, since `?` is neither a
letter nor `_`. `lint::in_case` states the rule, for any name, with a
guarantee for each case, so that each pattern is a guarantee of its
own, though `case_split_guarantees` would suggest merging them:

```fren
set_option fren.lint.case_split_guarantees "allow" in
pub comp in_case {
    in case: Case
    in name: String
    pub det out conventional?

    ensure snake: when case = Snake, conventional? iff not name.matches?(r".*[A-Z].*")
    ensure camel: when case = Camel, conventional? iff name.matches?(r"[A-Z][^_]*")
    ensure upper: when case = Upper, conventional? iff name.matches?(r"[A-Z][^a-z]*")

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
