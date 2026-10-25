# Decidability

The `decidability` group has one lint, `undecidable`, which finds a
construct outside the decidable core. It is the only group that is `deny`
by default.

## Undecidable constructs

`undecidable` fires once for each construct outside the [decidable
core](../Lang/Decidability.md), at the construct, with the reason and how to
stay in the core. It is `deny` by default, so a spec opts out explicitly:

```
set_option fren.lint.undecidable "allow" in
comp c { ... }
```

Where `undecidable` is denied or forbidden, the lint is a static error, so
no check runs, with either front end ([Static
errors](../View.md#static-errors)): nothing outside the decidable core
reaches the solver unless the spec opts in, since the solver may not only
fail to decide such a query but abort, which would end a `lake build`.
In Lean, an item where it is denied is never checked, even where its
error does not stop `#fren_check`, as inside a `#guard_msgs`. The same holds for a global expectation, and for a refinement where it is
denied, or in either of its components.

A project that wants every check decidable sets `-F undecidable`. Setting
it to `expect` says that a component is meant to be undecidable, so that
[`unfulfilled_lint_expectations`](../Lint.md#expecting-lints) reports the opt-out
once a change brings it back into the core. `lint::undecidable_fires`
states when it fires:

```fren
pub mod lint

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

#fren_check
```
