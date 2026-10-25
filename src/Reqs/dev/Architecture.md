# Architecture

Following the lessons of Veil ("Lessons from Building an Auto-Active
Verifier in Lean", Dafny '26):

- Fren keeps its own model of specs (modules, items, imports, enumerations, components)
  in Lean environment extensions (`Fren.Model`). Only Fren's elaborators
  change it, and nothing is recovered by reading generated Lean declarations
  back.
- Model, controller and view are separate: elaborators record specs
  (`Fren.Elab`), checks turn the model into solver queries and return plain
  results (`Fren.Check`), and `#fren_check` presents them (`Fren.View`).
- Generated definitions are ordinary Lean definitions (shallow at the object
  level).
- Fren's syntax is scoped to `Fren.Lang`, so its keywords don't leak into
  other Lean code.

## Libraries

| Library | Contents | Depends on |
|---|---|---|
| `FrenCore` | Names, modules and visibility; check algorithms, generic over a solver backend; message text | Lean core |
| `Fren` | The Lean-hosted front end; lean-smt backend; implementations. `Fren.Spec` is the part without the checker | `FrenCore`, lean-smt (`Fren.Spec`: `FrenCore`) |
| `FrenCli` | The `fren` command's lexer, parser, type checker and cvc5 backend | `FrenCore`, lean-cvc5 |
| `Reqs` | Fren's requirements | `Fren` |
| `Impls` | Fren's code linked to `Reqs` with `impl` | `Reqs`, `FrenCore`, `FrenCli.Exit`, `FrenCli.MutateOutcome` |

The executables also link `c/glibc_c23.c`, the one non-Lean source: it
defines the C23 glibc functions that cvc5's static Linux release calls,
which the older glibc that Lean links against lacks.

Importing `Fren` never builds `FrenCli`, and building the `fren` command never builds
lean-smt or lean-auto (Lake still clones them, as `require` is per package).
