# Testing

- **ui tests** (`lake test`): each `test/ui/**/*.fren` covers one topic and
  states its expected messages as comments:
  `--~ error: TEXT` expects an error on that line whose text contains `TEXT`
  (`--~^` for the line above), every message must be expected, and `--@`
  lines expect the summary and exit code. Both front ends run every file and
  must satisfy the same annotations; `--~[cli]` and `--~[hosted]` mark the
  few messages that legitimately differ (parse and type errors, which the Lean
  front end gets from Lean). This is how `cli::agreement` is tested. See
  `src/FrenTest/Ui.lean` for the format.
- **Snapshots** (`lake test`): `test/cli/**/X.fren` must make the `fren` command print
  `test/cli/**/X.expected` exactly, for formatting that annotations don't cover.
  Each distinct message has one, named after its code (`f0105_eqeq.fren`).
  A line `--@ args: ARGS` runs `fren ARGS X.fren`, and `--@ argv: ARGS` runs
  `fren ARGS` alone. `lake test -- --bless` updates them.
- **Layout:** tests are in subdirectories by area. Under `test/cli/`, the
  snapshots of codes are by their [group](../View.md#error-codes) (`syntax/`,
  `names/`, `types/`, `instances/`, `traceability/`, `results/`), those of
  lints by lint group (`lints/style/` and so on, and `lints/settings/` for
  setting levels), and the others by command (`args/`, `fix/`, `fmt/`,
  `commands/`). Under `test/ui/`, they are `lang/`, `checks/`, `lints/`,
  `syntax/` and `lean/`.
- **Error codes** (`lake test`): every code used in the sources must be
  explained in `src/FrenCore/Codes.lean` and reported by some snapshot.
  Each explanation's first ```` ```fren ```` block must report its code,
  and its other blocks must not. A new message needs a code, an
  explanation and a snapshot.
- **Lean-only behaviour** (`lake build`): `#guard_msgs` tests in
  `src/FrenTest`, e.g. the shape of generated definitions.
- **Fren's own requirements**: checked by `lake build` (`#fren_md`) and by
  the `fren` command under `lake test`.
- **Conformance corpus** (`lake test`): random components whose
  constraints are all in the [decidable core](../Lang/Decidability.md),
  one corpus each for strings, sets, relations and sequences, from a fixed
  seed, must be checked with no inconclusive result: the core promises
  that the solver decides them.
- **Formatting** (`lake test`): every `.fren` and Markdown spec in the
  repository must be formatted, as `fren fmt --check` says, except those
  listed as `--ignore` globs in `fmtIgnore` in `src/FrenTestMain.lean`:
  fixtures that are deliberately unformatted or do not parse. Run `fren fmt`
  on a spec after editing it. Formatting every spec must also keep its
  tokens, imports and comments, and be idempotent (`fmt::safe`).

- **Mutants** (`lake test`): over the corpus of Fren's own requirements and
  the snapshots of `fren mutate` (`test/cli/mutate_*.fren`,
  `f0613_*.fren` and `f0614_*.fren`), every [mutant](../Mutate.md) changes
  the text and has no static error (*well-formed*: mutants are made so, and
  a failure is fixed in the operator rather than by filtering), has an
  identifier that no other mutant has, leaves the identifiers of the
  mutants of other items alone (*stable*), and, for a swap, has a mutant
  that swaps it back (*involutive*). A larger `--sample` contains a smaller
  one. The snapshot `mutate_list.fren` lists a mutant of every origin, at
  every kind of site; a new operator extends it.
- **Confirmed models** (`lake test`): `fren check` confirms every model the
  solver returns with the evaluator (see
  [Evaluation and testing](../Eval.md#confirming-models)), so every test that
  runs the checks also checks the translation of its spec on the solver's
  models. A refuted model is an internal error, which fails the test.
- **Differential fuzzing** (`lake exe fren_fuzz [--count N] [--seed N]
  [--out DIR]`): generates random specs and compares each verdict of `fren
  check` with one computed by brute force from the evaluator. The specs stay
  in a fragment where brute force is exact: `Bool`s, enumerations, `Int`s
  that constraints named `range_*` bound to a few values, abstract types,
  and functions from them to `Bool`s, sets and relations of an enumeration
  or of `Bool`, and sequences of one that `range_*` constraints bound to
  two elements, with instances, `det out`s and global expectations. Each
  index is guarded, before or after it, so that every constraint has a
  value whatever an index out of range is. Brute force enumerates every behaviour and interpretation
  of that fragment, and decides each check from its definition in
  [Checks](../Check.md). It also confirms that each reported set of
  constraints (a conflict, a vacuity or a redundancy) entails what the
  message says and is minimal, and that each counterexample can be
  completed to a behaviour with the reported values. Each disagreement is
  written to `DIR` (default `.lake/fuzz`) as a `.fren` file, with what
  differed in a comment. The verdicts of redundancy for `range_*`
  constraints are not compared, since without them brute force is not
  exact. A component with too many behaviours to enumerate is skipped,
  and counted in the summary.
- **Front-end fuzzing** (`lake exe fren_fuzz_frontends [--count N]
  [--seed N] [--out DIR] [--avoid-known]`): generates random specs and
  checks each with both front ends, the `fren` command's pipeline and the
  Lean front end (in an environment that imports `Fren`, as the ui
  tests do), whose reports must agree (`cli::agreement`): the same errors
  and warnings on the same lines, and the same summary. The specs aim at
  the analyses that each front end implements on its own: constants,
  defined outputs, defined and uninterpreted functions, instances,
  `match`, string methods and `++`, products, and sets and relations with
  `card`, so as to reach `linear_product`, the
  [decidable core](../Lang/Decidability.md) and the lints. What may
  legitimately differ is not compared: Lean's own parse and type errors
  stand for the `fren` command's errors on the same line; messages are
  compared by their first line, without the values of a model, which may
  differ, or the solver's reason for an undecided check; checks by
  testing, which Lean does not run, are left out, as is the summary of
  a spec that has them; and after a static error, which stops the `fren`
  command, so are the checks' results, the summary, and Lean's lints of an
  item with an error other than a lint. Each spec where the front ends
  differ is written to `DIR` (default `.lake/fuzz`) with the differences
  and both reports in comments, and the differences are summarized by
  kind; those only in undecided checks, which time limits may explain,
  are counted apart. `--avoid-known` steers clear of differences already
  known, to find others; `--files FILE...` compares the front ends on
  given files, and `--print SEED` prints a generated spec.

`lake test` runs its tests as jobs, in parallel: each job is a process of
its own (`fren_test --job NAME ARG...`), and the ui tests run in batches of
at most eight files, each importing `Fren` once. The mutants are checked in
a job per group of the corpus, and those of Fren's own requirements in
eight jobs, its *slices*, each taking every eighth mutant: each slice makes
every mutant of its group, which the checks of one mutant compare it with,
and the checks of the whole group run in the first slice. A mutation job
whose group or slice is out of range is an error, rather than a job that
checks nothing, and a crash in one is reported with the files of its group.
As many jobs run at once as the machine has cores, but at most sixteen.
This cap is a heuristic: the solver's time limit is in wall-clock time, so
too many jobs at once could make checks inconclusive, and a job can take
about 2.5 GB of memory, so a machine with less than 40 GB may need fewer.
`FREN_TEST_JOBS=N` runs `N` at once instead, for a positive integer `N`;
any other value, including an empty one and `0`, is an error. The jobs are
independent, but for one: with `--bless`, the snapshots job rewrites the
snapshots that the error codes job reads, so it runs first, alone. A job
that crashes is a failure, and so is one that writes to stderr, such as
with a `panic!`, which prints and carries on: what it wrote is reported.
The failures are reported sorted, so that their order does not depend on
which job finished first.

## Coverage

Every declaration of Fren's code must be run by `lake test`, or say why it
never runs. Coverage is measured on the compiled code with gcov, so it is
per declaration, not per line or per `match` arm:

```text
find .lake/build -name '*.gcda' -delete
lake -R -Kcoverage=RUNTIME build fren fren_test fren_coverage
lake -Kcoverage=RUNTIME test
lake exe fren_coverage GCOV...
```

The counters add up over runs, so the first line clears those of earlier
ones.

`-Kcoverage=RUNTIME` compiles `FrenCore`, `Fren` and `FrenCli` with gcov's
counters, and links the executables that run them with the profiling
runtime at the path `RUNTIME`, which Lean's toolchain lacks. It also turns
off the inlining of small functions, whose code would otherwise run in
their callers and seem never to run. `-R` is needed to change it, since
Lake keeps the configuration of the last build. On macOS, the runtime is
Apple's, such as
`/Library/Developer/CommandLineTools/usr/lib/clang/21/lib/darwin/libclang_rt.profile_osx.a`,
and `GCOV` is `xcrun llvm-cov gcov`. CI installs LLVM's of the version of
Lean's clang.

`fren_coverage` reads the counters with `GCOV`. A declaration ran if one of
its entry points ran: its own function, or its boxed or reduced-arity
version, which callers may call instead. A specialization
`f._at_.g.spec_N` is an entry point of `f`, with arguments from `g`, and
`g` may itself be one. Lambdas, join points and closed terms are no
declaration's: the compiler shares them among declarations whose code is
alike, so that running one would seem to run another. Calls made while a
module is initialized count, as when a closed term applies a function. The declarations counted are the compiled definitions
of `FrenCore`, `Fren` and `FrenCli` that are written in the source and
compile to a function: not theorems, constructors, recursors, matchers,
projections, `@[inline]` definitions, instances that `deriving` makes, or
definitions without arguments, which are constants computed at
initialization. A declaration that compiles to a function that gcov does
not report did not run. The proofs of `impl`s are not code, but the
definitions they are about are counted.

Only compiled code is measured. The Lean-hosted front end's elaborators
run in Lean's interpreter where a test elaborates Fren in Lean, so some of
them are listed although the ui tests elaborate them.

`test/coverage.txt` lists the counted declarations that no test runs, one
per line. One that is never meant to run, such as code that runs only when
the evaluator refutes the solver, says why after ` -- `. `fren_coverage`
fails on a counted declaration that does not run and is not listed, and on
a listed one that runs or is no longer counted, so the list can only
shrink; `fren_coverage --write` rewrites it as the run found it, keeping
the reasons. The aim is a list of reasons alone. CI runs it on `main`,
with Lean CI.
