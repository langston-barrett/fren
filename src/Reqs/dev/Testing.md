# Testing

- **ui tests** (`lake test`): each `test/ui/**/*.fren` covers one topic and
  states its expected messages as comments:
  `--~ error: TEXT` expects an error on that line whose text contains `TEXT`
  (`--~^` for the line above), every message must be expected, and `--@`
  lines expect the summary and exit code. Both front ends run every file and
  must satisfy the same annotations, and both or neither must say that a
  static error stopped the checks; `--~[cli]` and `--~[hosted]` mark the
  only messages that may differ, parse errors, which the Lean front end gets
  from Lean's parser, and `--~?` allows a message without expecting
  it, for one that may be in one of several places, such as a conflict's
  note at whichever guarantee the solver's model picks. This is how
  `cli::agreement` is tested. See
  `src/FrenTest/Ui.lean` for the format.
- **Example specs** (`lake test`): each `examples/**/*.fren` is a complete
  spec for readers, and is checked as a ui test, so its annotations
  (usually none) must match both front ends' messages. The example specs
  are also in the ui tests' backjumping and enumeration corpora.
  An example's Lean implementation, such as `examples/Rle.lean`, reads its
  spec with `#fren_md` and proves it meets the spec; `lake build` checks
  the proofs of those listed in the `Examples` library.
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
  `syntax/` and `lean/`. The example specs are in `examples/`, outside
  `test/`.
- **Error codes** (`lake test`): every code used in the sources must be
  explained in `src/FrenCore/Codes/CODE.md` and reported by some snapshot.
  Each explanation's first ```` ```fren ```` block must report its code,
  and its other blocks must not. A new message needs a code, an
  explanation and a snapshot.
- **Libraries** (`lake test`): the modules that copy a root module's
  imports, to keep it off the build's critical path, import exactly its
  modules; each module of `Reqs` reads only the specs that its library in
  `lakefile.lean` needs; and only the modules of `Impls` whose library needs
  the tests, `ImplsTested`, make `tested` claims.
- **Lean-only behaviour** (`lake build`): `#guard_msgs` tests in
  `src/FrenTest`, e.g. the shape of generated definitions.
- **Fren's own requirements**: checked by `lake build` (`#fren_md`) and by
  the `fren` command under `lake test`.
- **Conformance corpus** (`lake test`): random procedures whose
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

- **Mutants** (`lake test`): over the corpus of Fren's own requirements,
  the snapshots of `fren mutate` (every file under `test/cli/`, in any
  subdirectory, named `mutate_*.fren`, `f0613_*.fren` or `f0614_*.fren`,
  so a snapshot of its arguments, such as `args/mutate_by.fren`, is in it
  too) and the examples of its decisions
  (`test/mutate/*.fren`, below), every [mutant](../Mutate.md) changes
  the text and has no static error (*well-formed*: mutants are made so, and
  a failure is fixed in the operator rather than by filtering), has an
  identifier that no other mutant has, leaves the identifiers of the
  mutants of other items alone (*stable*), and, for a swap, has a mutant
  that swaps it back (*involutive*). A larger `--sample` contains a smaller
  one, and the shards of `--shard K/N` partition a selection, sampled or
  not. The snapshot `mutate_list.fren` lists a mutant of every origin, at
  every kind of site; a new operator extends it.
- **Decisions of `fren mutate`** (`lake test`): these run `fren mutate`
  end to end, as treemut's meta-mutation tests (M1, M2, M5 and M8) do,
  over the examples in
  `test/mutate/`: small specs whose expectations and cover goals pin them
  down. Beside an example `X.fren`, `X.equivalent` lists the mutants that
  no check can kill, one per line as `ID REASON`, where the reason says why
  the mutant means what the spec means. Strengthening the spec, so that the
  mutant is not made or is killed, is better than listing it. Each example
  must be:
  - *adequate*: it passes `fren check`, and `fren mutate` kills every
    mutant of it but those listed, each of which survives or is shown
    equivalent, either of which may happen, since the solver's time limit
    for equivalence is in wall-clock time;
  - *sample invariant*: with `--sample` of half of its mutants, so that
    each is run after fewer others and with fewer answers to solver queries
    kept, `fren mutate` decides each mutant, and finds the check that kills
    it, as it does without;
  - *shard invariant*: with `--shard K/3`, for each `K`, `fren mutate`
    decides each mutant of the shard as it does without, and the three
    shards together hold each mutant once;
  - *every expectation needed*: without any one of its expectations and
    cover goals, local or global, some mutant survives that was killed. It
    must survive, not be shown equivalent: a mutant that some check killed
    means something else than the spec, so this also tests the solver's
    answers about equivalence;
  - *selection sound*: checking only the procedures whose fingerprint a
    mutant changes (`Mutate.fingerprint`) decides what checking every
    procedure does, and every check that kills the mutant then also kills
    it when every check of every procedure is run;
  - *verdicts sound*: each check that kills a mutant, when every check of
    every procedure is run, passes under `fren check` of the spec and fails
    under `fren check` of the mutant's text, and a mutant that is not
    killed fails no check there that passes on the spec.

  The last two are checked on a sample of at most 24 mutants of each
  example. A new origin may need the examples strengthened, or new
  mutants listed.
- **Enumeration agrees with the solver** (`lake test`): every ui test that
  the binary checks without a static error is checked again with every
  check set to enumeration (`set_option fren.evidence "enumerated"` before
  its first item), and each verdict of enumeration must match the solver's
  on the same check (see [Verdicts of
  enumeration](../Check.md#verdicts-of-enumeration)): a failure is genuine,
  so the solver must not pass the check, and a pass that is not bounded is
  a decision, so the solver must not fail it; and a value given where a
  pattern type is declared, which stays the solver's, keeps its result.
  The ui tests
  `checks/enumerated*.fren` and `checks/evidence_obligations.fren` cover
  enumeration in both front ends.
- **Confirmed models** (`lake test`): `fren check` confirms every model the
  solver returns with the evaluator (see
  [Evaluation and testing](../Eval.md#confirming-models)), so every test that
  runs the checks also checks the translation of its spec on the solver's
  models. A refuted model is an internal error, which fails the test.
- **Differential fuzzing** (`lake exe fren_fuzz [--count N] [--seed N]
  [--out DIR]`): generates random specs and compares each verdict of `fren
  check` with one computed by brute force from the evaluator. The specs stay
  in a fragment where brute force is exact: `Bool`s, enumerations,
  ordered or not, `Int`s that constraints named `range_*` bound to a few
  values, and values of a [newtype](../Lang/Items.md#newtypes) of `Int`
  that they bound so, abstract types,
  and functions from them to `Bool`s, sets and relations of an enumeration
  or of `Bool`, and sequences of one that `range_*` constraints bound to
  two elements, with calls, `det` outputs, cover goals, global
  expectations, quantifiers over the enumeration and over `Bool`, and
  `Bool` tables, by conditions and over a `Bool` or an `Int`. Each index is guarded, before or after it, so that every
  constraint has a value whatever an index out of range is; a table has
  one even where no row holds, which is the interpretation's unspecified
  value of its type. Its constraints include
  pattern tests and `match`es with literal and range patterns on `Bool`s
  and `Int`s, and on the one enumeration with payloads, `P { A, B(Bool),
  C(Bool) }`, pattern tests of its variants and `match`es that read its
  payloads; deeper nested patterns are left to the ui tests. Brute force enumerates every behaviour and interpretation
  of that fragment, and decides each check from its definition in
  [Checks](../Check.md). It also confirms that each reported set of
  constraints (a conflict, a vacuity or a redundancy) entails what the
  message says and is minimal, and that each counterexample can be
  completed to a behaviour with the reported values, and each witness of a
  cover goal to a behaviour in which the goal holds, and that each clash
  note's sides [force](../Check.md#forced-outputs) what it says, a whole
  value or only a variant, and clash. Each disagreement is
  written to `DIR` (default `.lake/fuzz`) as a `.fren` file, with what
  differed in a comment. The verdicts of redundancy for `range_*`
  constraints are not compared, since without them brute force is not
  exact. A procedure with too many behaviours to enumerate is skipped,
  and counted in the summary.
- **Front-end fuzzing** (`lake exe fren_fuzz_frontends [--count N]
  [--seed N] [--out DIR] [--avoid-known] [--spec-timeout SECONDS]`):
  generates random specs and checks each with both front ends, the `fren`
  command's pipeline and the Lean front end (in an environment that
  imports `Fren`, as the ui tests do), whose reports must agree
  (`cli::agreement`, `cli::agrees_with_build`): the same errors, warnings
  and notes on the same lines, the same summary, and the exit status
  that Lean's messages call for: 2 after a static error, else 1 when Lean
  reports an error, 3 when it reports a warning, and 0 otherwise. The specs aim at the
  analyses that each front end implements on its own: constants, definitions
  of results and `let` variables, defined and uninterpreted functions, calls, `match`, tables,
  string methods and `++`, products, orderings and `min` and `max` of an ordered
  enumeration, a newtype of `Int` and its operators, an enumeration with
  payloads, whose outputs' variants clash notes may give, and sets and
  relations with `card`, so as to reach `linear_product`, the [decidable core](../Lang/Decidability.md)
  and the lints. Only what may legitimately differ is not compared:
  - A parse error stops the `fren` command, while Lean recovers at the
    next command: Lean must then report a parse error in the same item, on
    the parse error's line, or on the last line before it that is not blank
    or a comment, since Lean places a parse error at the end of the token
    before the offending one, and nothing else is compared. An
    item is one Lean command, so any other error of Lean's in it means
    that Lean parsed what the `fren` command rejects. Lean's parse errors
    are its messages that start with `unexpected`, `unterminated`, or
    `expected` but do not go on with `, but`, as Fren's own do.
  - Lean's parse errors stand for the `fren` command's static
    errors on the same line, but not for a check's result: a check that
    fails where Lean rejects the constraint is a difference. Any other
    error of either front end is compared.
  - Messages are compared by their first line, without the values of a
    model, which may differ, or the solver's reason for an undecided check.
    The names of the constraints that a message reports are compared,
    except the guarantees that a realizability failure names in its note,
    and its notes at them, of [forced outputs](../Check.md#forced-outputs)
    or of whom they conflict with: they are a minimal set that conflicts
    on its input, so they are compared only when both report the same
    input, and the notes at them only when both also name the same
    guarantees.
  - Checks by testing, which Lean does not run, are left out, and so are
    the summary and exit status of a spec that has them.
  - Both front ends must say that a static error stopped the checks
    (`could not check due to previous errors`, which has no location), or
    neither, even after a parse error. Any other message without a location
    is compared too.

  Each spec where the front ends differ is written to `DIR` (default
  `.lake/fuzz`) with the differences and both reports in comments, and the
  differences are summarized by kind; those only in undecided checks,
  which time limits may explain, are counted apart. Specs run in worker
  processes, so a crash of the solver is recorded against its spec, and a
  spec that runs longer than `--spec-timeout` (default 30 s; a spec takes
  well under a second) is stopped and recorded as a timeout. Crashes and
  timeouts are findings, like differences: the run then exits nonzero. A
  worker that dies while checking no spec is blamed on none. Each run's
  work files are its own, but the findings are named by seed, so runs with
  overlapping seeds in one `DIR` overwrite each other's. `--avoid-known` steers clear of differences
  already known, to find others; `--files FILE...` compares the front ends
  on given files, and `--print SEED` prints a generated spec. The
  comparison itself is tested in `FrenTest/FrontendsCompare.lean`.

`lake test` runs its tests as jobs, in parallel: each job is a process of
its own (`fren_test --job NAME ARG...`), and the ui tests run in batches of
at most eight files, each importing `Fren` once. The mutants are checked in
a job per group of the corpus, and those of Fren's own requirements in
eight jobs, its *slices*, each taking every eighth mutant: each slice makes
every mutant of its group, which the checks of one mutant compare it with,
and the checks of the whole group run in the first slice. A mutation job
whose group or slice is out of range is an error, rather than a job that
checks nothing, and a crash in one is reported with the files of its group.
The decisions of `fren mutate` are checked in a job per example.
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

## Learning from review

Review findings are evidence about the requirements and their connection
to the implementation, as well as about the code. Revisit that connection
as findings arrive, when a fix crosses another implementation path, and
when the same kind of failure recurs. Do not wait until the final review.

For each substantive finding, distinguish the following causes; a finding
can have more than one:

- **Missing rule:** the requirements allow the wrong behavior or leave a
  choice ambiguous. Specify the domain, assumptions, allowed outcomes and
  boundary cases before changing the implementation.
- **Model abstraction:** the rule is stated, but its executable model
  omits what failed. Strengthen the model with the relevant values,
  propositions, behaviors, interpretations or identities and their
  relationships. A collection of expected Boolean answers is not a model
  of those relationships.
- **Implementation conformance:** the rule and model are adequate, but
  the implementation path is not checked against them. Add a regression
  through the actual parser, lowering, query construction or evidence
  adapter that violated the rule. Checking a second copy of the model
  does not establish that connection.

Use the smallest counterexample that distinguishes the intended semantics
from the faulty implementation, and a valid neighboring case when a fix
could reject too much. For example, two individually satisfiable cover
members can have no common witness; a constrained record field can make
two records equal although their unrestricted base values differ; a proof
of one proposition must not establish another through changed metadata.
Test actual check identities and verdicts where identity matters, rather
than relying on unchanged summary totals.

Run shared semantic cases through both front ends and every applicable
evidence method. Keep the interpretation and witness fixed when the rule
requires them to be shared. Exercise the boundaries introduced by the
change: empty and singleton groups, nested values, defined outputs,
imported declarations, unknown results and exhausted budgets, as relevant.
An unsupported method must say so; silently omitting a check is not
agreement. Record the requirement and conformance test strengthened by a
review fix in its change description.

Recurring difficulty stating these relationships can motivate a language
feature. Propose it with concrete cases that are awkward or impossible
today, the intended syntax and semantics, counterexamples it must reject,
and its effects on decidability and evidence. Distinguish a limitation of
the language from a missing model or test. A proposal does not authorize
expanding the implementation's scope automatically.

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
version, which callers may call instead. An executable's `main` is emitted
as `_lean_main`, and is `main`'s. A specialization
`f._at_.g.spec_N` is an entry point of `f`, with arguments from `g`, and
`g` may itself be one. Lambdas, join points and closed terms are no
declaration's: the compiler shares them among declarations whose code is
alike, so that running one would seem to run another. Calls made while a
module is initialized count, as when a closed term applies a function. The declarations counted are the compiled definitions
of `FrenCore`, `Fren` and `FrenCli` that are written in the source and
compile to a function: not theorems, constructors, recursors, matchers,
projections, `@[inline]` definitions, instances that `deriving` makes, or
definitions without arguments, which are constants computed at
initialization. A definition of a function type written without
parameters, as `def f : Nat → Nat := g`, compiles with its parameters, so
it is counted. A declaration that compiles to a function that gcov does
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
