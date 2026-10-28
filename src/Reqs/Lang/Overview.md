# Language overview

A spec is a sequence of *items*: modules, `use` declarations,
enumerations, records, abstract types, type aliases, functions, constants, procedures
and global expectations. Items are
grouped into [modules](Modules.md). A [procedure](Procedures.md) declares
its parameters and results, and constraints on them: assumptions,
guarantees, expectations and cover goals. Constraints are
[expressions](Expressions.md) of type `Bool`. A [global
expectation](Global.md) relates behaviours of procedures.

For example, this spec describes a thermostat that chooses a mode from the
current temperature and a target:

```
mod climate

pub enum Mode { Off, Heat, Cool }
use self::Mode::{Off, Heat, Cool}

const MIN_TARGET: Int := 50
const MAX_TARGET: Int := 90

type SubsetOverview1 = subset_value: Int  where invariant: subset_value is MIN_TARGET..=MAX_TARGET
pub proc thermostat(temp: Int, target: SubsetOverview1): (mode: Mode) {
  ensure heat: when temp < target - 2, mode = Heat
  ensure cool: when temp > target + 2, mode = Cool
  ensure idle: unless temp < target - 2 or temp > target + 2, mode = Off

  expect cold_heats: when temp < 40, mode = Heat
}
```

- `mod climate` makes `climate` the current module.
- `enum Mode` declares an enumeration with three variants, and `use
  self::Mode::*` makes them available by their bare names.
- `MIN_TARGET` and `MAX_TARGET` are [constants](Items.md#constants): each
  stands for its value.
- `thermostat` has two parameters, `temp` and `target`, and one result,
  `mode`. `target`'s type is a [pattern type](Types.md#pattern-types): an
  `Int` that matches the range `MIN_TARGET..=MAX_TARGET`, so the procedure
  assumes that the environment only ever sets a target between 50 and 90.
- The guarantees `heat`, `cool` and `idle` say which mode the system must
  choose.
- The expectation `cold_heats` claims a consequence: given the type of
  `target` and the guarantees, a temperature below 40 always means heating.

Checking this spec (see [Checks](../Check.md)) confirms that some mode
always satisfies all three guarantees, that `cold_heats` follows, and that
the condition of each guarantee and of the expectation can actually occur.

In Lean, the same spec is a Lean file that starts with `import Fren` and
`open Fren.Lang`, and ends with `#fren_check` to run the checks (see [Lean
embedding](../Lean.md)). The `fren` command checks it as it stands (see
[The `fren` command](../Cli.md)).

```fren
pub mod lang
```
