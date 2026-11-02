# Testing

The test driver's rules are stated here as the module `testing`, and
`Impls.Testing` proves the driver's code meets them, for any jobs and any
messages: which jobs each shard runs ([Shards](#shards)), when the
front-end fuzzer stops a spec ([Fuzzer time limit](#fuzzer-time-limit)), when a ui test
passes ([Expectations](#expectations)), and, trusted to Lake, when a
test's result is that of the files it reads ([Fresh
results](#fresh-results)).

```fren
pub mod testing
```

- **ui tests** (`lake test`): each `test/ui/**/*.fren` covers one topic and
  states its expected messages as comments:
  `--~ error: TEXT` expects an error on that line whose text contains `TEXT`
  (`--~^` for the line above), every message must be expected, and `--@`
  lines expect the summary and exit code. Both front ends run every file and
  must satisfy the same annotations, both or neither must say that a
  static error stopped the checks, and a message that both report on a
  line, with the same severity and first line, must be at the same column
  in both, which the annotations do not state, except on the lines known
  to differ until they are fixed (`knownColumnDifferences`, which fails
  for a line that no longer differs); `--~[cli]` and `--~[hosted]` mark the
  only messages that may differ, parse errors, which the Lean front end gets
  from Lean's parser, and a known disagreement that a test pins until it is
  fixed, with its issue, as `lang/traits_frontends.fren` does for
  #493. `--~$` expects a message with no line, such as the Lean front end's
  error at the `#fren_check` that the test adds, and `--~?` allows a
  message without expecting it, for one that may be in one of several
  places, such as a conflict's
  note at whichever guarantee the solver's model picks. This is how
  `cli::agreement` is tested. See
  `src/FrenTest/Ui.lean` for the format, and
  [Expectations](#expectations) for when a file passes.
- **Example specs** (`lake test`): each `examples/**/*.fren` is a complete
  spec for readers, and is checked as a ui test, so its annotations
  (usually none) must match both front ends' messages. An example that one
  front end cannot check, for a known limit with its issue, may be checked
  by the other alone (`--@ only: cli`), with a comment that names the issue
  and says to drop the line once it is fixed, as `examples/filesystem.fren`
  does for #417. The example specs are also in the ui tests' backjumping and
  enumeration corpora.
  An example's Lean implementation, such as `examples/Rle.lean`, reads its
  spec with `#fren_md` and proves it meets the spec; `lake build` checks
  the proofs of those listed in the `Examples` library.
- **The reference's examples** (`lake test`, `manualExamples`): each block
  fenced as ```` ```fren example ```` in `src/Reqs/**/*.md` is a spec of its
  own, outside its chapter's module, and is checked as a ui test, so its
  annotations must match both front ends' messages (see
  [Writing the reference](Style.md#examples)).
- **Rule identifiers** (`lake test`, `ruleIds`): every line of
  `src/Reqs/**/*.md` outside a code block that starts with `r[` is a
  well-formed rule identifier, and no two are the same (see [Writing the
  reference](Style.md#rule-identifiers)).
- **Rules and their requirements** (`lake test`, `ruleReqs`): each rule of
  **Legality rules** or **Dynamic semantics** has a requirement or is
  listed in `test/unformalized_rules.txt`, with why where its chapter's
  section is not "(Interlock pending)", and a rule that is only partly
  formalized is listed too, saying what is missing once its chapter's
  section is done; every item and clause that a marker names exists, and
  the clauses that it names alone are clauses of the item they resolve to;
  a block that formalizes a rule of
  its chapter follows it; each item of a module named as one of its
  chapter's constructs has a rule of its name, or, if it has clauses, each
  of them does, where the name is shaped as a rule identifier; and every
  rule that a test cites with `--@ reference: ID` exists
  (see [Writing the reference](Style.md#rules-and-requirements)). The
  report of these links, a page of the book under [Writing the
  reference](Style.md), is written when the book is built.
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
  `syntax/`, `lean/` and `misread/`. The example specs are in `examples/`, outside
  `test/`.
- **Error codes** (`lake test`): every code used in the sources must be
  explained in `src/FrenCore/Codes/CODE.md` and reported by some snapshot.
  Each explanation's first ```` ```fren ```` block must report its code,
  and its other blocks must not. A new message needs a code, an
  explanation and a snapshot.
- **Libraries** (`lake test`): `lake build` rebuilds a module when a file
  that it reads changes. Lake rebuilds it when a file changes that the
  library that builds it needs. A library builds the modules of its globs
  in `lakefile.lean` with its own `needs`, and a module that a build
  reaches only by an import, with those of the last library that has it.
  So no module is in the globs of two libraries; each module of `Reqs`
  reads only the specs that its library needs; only the modules of `Impls`
  whose library needs the tests, `ImplsTested`, make `tested` claims; and
  only the tests of `FrenTestFiles`, whose library needs the files that
  they read, read files with `#fren_md`, and they, and the files that they
  read, read only files that it needs. Also, the modules that copy a root
  module's imports, to keep it off the build's critical path, import
  exactly its modules.
- **Lean-only behaviour** (`lake build`): `#guard_msgs` tests in
  `src/FrenTest` and `src/FrenTestFiles`, e.g. the shape of generated
  definitions.
- **Fren's own requirements** (`lake test`, `ownSpec`): checked by the
  `fren` command; `lake build` only elaborates them, and Lean checks them
  on `main` (see [Own requirements](#own-requirements)).
- **Conformance corpus** (`lake test`): random procedures whose
  constraints are all in the [decidable core](../Lang/Decidability.md),
  one corpus each for strings, sets, relations and sequences, from a fixed
  seed, must be checked with no inconclusive result: the core promises
  that the solver decides them.
- **Formatting** (`lake test`): every `.fren` and Markdown spec in the
  repository must be formatted, as `fren fmt --check` says, except those
  listed as `--ignore` globs in `fmtIgnore` in `src/FrenTestMain.lean`:
  fixtures that are deliberately unformatted or do not parse, and those
  listed in `fmtPending`: test fixtures that `fren fmt`'s move to rustfmt's
  layout would lay out anew. Their expected outputs and `--~` annotations
  name their lines, so formatting them means updating those too. They are
  formatted a group at a time, each only where the new layout reads better
  than the old, and `fmtPending` is then removed (#509). Run `fren fmt`
  on a spec after editing it. Formatting every spec must also keep its
  tokens and comments in order (`fmt::order`) and its imports, leave no
  comma, trailing ones included, after a line break or a line comment,
  and be idempotent (`fmt::safe`), and each
  spec, laid out again at random, must format as it does
  (`fmt::layout_free`).

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
  subset type is declared, which stays the solver's, keeps its result.
  The ui tests
  `checks/enumerated*.fren` and `checks/evidence_obligations.fren` cover
  enumeration in both front ends.
- **Solver lifetime** (`lake test`, `solverLifetime`): 500 queries in a
  row must not grow the test driver's memory by more than 100 MB, as they
  did by 1.5 MB each while no solver was freed (see [Solver
  queries](../Cli.md#solver-queries)); and sixteen threads that each ask
  300 queries in `ALL`, a logic with nonlinear arithmetic, and 100 in
  `QF_UFDTLIA`, a linear one, at once must get every answer right. The
  `ALL` ones crashed about one run in three while their solvers
  initialized and were freed at the same time; the linear ones take no
  lock (`FrenCli.Cvc5`).
- **The binary's shared reading** (`lake test`, `sharedSpec`): only the
  `fren` binary reads the spec once, marks it and what else the threads
  read persistent, and shares it with every thread (`FrenCli.Args.persist`);
  the other jobs call `check` and `quickcheck` within the test driver,
  which gives each thread a reading of its own. So `sharedSpec` runs the
  binary's path, each run in a process of its own, since what it marks is
  never freed: `fren check` of Fren's own requirements, with a fresh query
  cache, and `fren check` and `fren quickcheck` of ui tests that fail and
  leave checks undecided, at `--jobs 4`. Each must give the same output
  and exit status as the tests' path at `--jobs 1` (see [Parallel
  checking](../Cli.md#parallel-checking)).
- **Confirmed models** (`lake test`): `fren check` confirms every model the
  solver returns with the evaluator (see
  [Evaluation and testing](../Eval.md#confirming-models)), so every test that
  runs the checks also checks the translation of its spec on the solver's
  models. A refuted model is an internal error, which fails the test.
  Both front ends also confirm each model that they report, at the values
  that their readers read (see [Reading models](../Models.md)). The ui tests in
  `test/ui/misread/` run with `FREN_MISREAD_MODELS` set, which makes both
  readers misread every integer, to check that the confirmation catches it.
- **Differential fuzzing** (`lake exe fren_fuzz [--count N] [--seed N]
  [--out DIR]`): generates random specs and compares each verdict of
  `fren check` with one computed by brute force from the evaluator. The
  specs stay in a fragment where brute force is exact: `Bool`s,
  enumerations, ordered or not, `Int`s that constraints named `range_*`
  bound to a few values, and values of a
  [newtype](../Lang/Items.md#newtypes) of `Int` that they bound so,
  abstract types, and functions from them to `Bool`s, sets and relations
  of an enumeration or of `Bool`, and sequences of one that `range_*`
  constraints bound to two elements, with calls, `det` outputs, cover
  goals, global expectations, quantifiers over the enumeration and over
  `Bool`, and `Bool` tables, by conditions and over a `Bool` or an
  `Int`. Each index is guarded, before or after it, so that every
  constraint has a value whatever an index out of range is; a table has
  one even where no row holds, which is the interpretation's unspecified
  value of its type. Its constraints include pattern tests and `match`es
  with literal and range patterns on `Bool`s and `Int`s, and on the one
  enumeration with payloads, `P { A, B(Bool), C(Bool) }`, pattern tests
  of its variants and `match`es that read its payloads; deeper nested
  patterns are left to the ui tests. Brute force enumerates every
  behaviour and interpretation of that fragment, and decides each check
  from its definition in [Checks](../Check.md). It also confirms that
  each reported set of constraints (a conflict, a vacuity or a
  redundancy) entails what the message says and is minimal, and that
  each counterexample can be completed to a behaviour with the reported
  values, and each witness of a cover goal to a behaviour in which the
  goal holds, and that each clash note's sides
  [force](../Check.md#forced-outputs) what it says, a whole value or
  only a variant, and clash. Each disagreement is written to `DIR`
  (default `.lake/fuzz`) as a `.fren` file, with what differed in a
  comment. The verdicts of redundancy for `range_*` constraints are not
  compared, since without them brute force is not exact. A procedure
  with too many behaviours to enumerate is skipped, and counted in the
  summary.
- **Front-end fuzzing** (`lake exe fren_fuzz_frontends [--count N]
  [--seed N] [--out DIR] [--avoid-known] [--guards] [--sites]
  [--confirm] [--spec-timeout SECONDS]`): generates random specs and checks each
  with both front ends, the `fren` command's pipeline and the Lean front
  end (in an environment that imports `Fren`, as the ui tests do), whose
  reports must agree (`cli::agreement`, `cli::agrees_with_build`): the
  same errors, warnings and notes at the same lines and columns, the
  same summary, and the exit status that Lean's messages call for: 2
  after a static error, else 1 when Lean reports an error, 3 when it
  reports a warning, and 0 otherwise. The specs aim at the analyses that
  each front end implements on its own: constants, definitions of
  results and `let` variables, defined and uninterpreted functions,
  calls, `match`, tables, string methods and `++`, products, orderings
  and `min` and `max` of an ordered enumeration, a newtype of `Int` and
  its operators, an enumeration with payloads, whose outputs' variants
  clash notes may give, and sets and relations with `card`, so as to
  reach `linear_product`, the [decidable core](../Lang/Decidability.md)
  and the lints; and quantifiers whose
  [guards](../Lang/Quantifiers.md#guards) each front end reads on its
  own: over `Int`, `Nat`, a pattern type, newtypes over each, a newtype
  over a newtype, one that is not ordered, an ordered record, an ordered
  enumeration and `String`, read through their fields, with ranges with
  one or both bounds, chains, memberships in sets and sequences, and
  each comparison on either side; and [traits](../Lang/Traits.md), with
  methods in both forms, laws, and expectations in both forms over them.
  `--guards` generates those quantifiers alone, so that many specs run
  fast. `--sites` generates expressions that do not synthesize their
  types, at each kind of [site](../Lang/Types.md#checking-and-synthesis)
  where they are checked, and, at the end, one where they are not, an
  error that stops the spec's other checks, which the default generator
  therefore never writes. `--confirm` generates what the [confirmation of
  models](../Models.md#known-values) evaluates: `div` and `mod` by a
  literal, an index in an argument that a function's body never reads,
  and the formulas whose value confirmation knows where an index is out
  of range. It checks them with both front ends misreading models, as
  `FREN_MISREAD_MODELS` makes them ([Testing](../Models.md#testing)), so
  that what one front end knows and the other does not is a message that
  differs: one refutes the model, and the other shows it. Only what may
  legitimately differ is not compared:
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
  - Under `--confirm`'s misread models, the front ends' solvers may give
    different models, and a model's confirmation says something about what
    a front end knows only of that model. So two results of a check, at
    the same position and of the same subject, are compared only where both front ends
    read the same model (`Fren reads the model as …`, or the
    counterexample or witness), and the summary and exit status only if
    every pair was.
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
  well under a second), leaving out its solver queries that reached their
  time limit ([Fuzzer time limit](#fuzzer-time-limit)), is stopped and
  recorded as a timeout. Crashes and
  timeouts are findings, like differences: the run then exits nonzero. A
  fresh worker takes over every 25 specs, a workaround for #650, to be
  raised or dropped once it is fixed: a worker slows down as it checks
  more, since the hosted front end's memory grows with each spec, and on
  CI, with four workers, a worker's 97th and 98th specs, which take under
  a second on their own, took 22 s and more than 30 s. A
  worker that dies while checking no spec is blamed on none. Each run's
  work files are its own, but the findings are named by seed, so runs with
  overlapping seeds in one `DIR` overwrite each other's. `--avoid-known`
  steers clear of differences already known, to find others: the generator
  parenthesizes every method's receiver that is not a name, and a spec
  whose every difference is of a known kind is counted apart, as known,
  rather than as a finding. A kind is known if the [front-end
  corpus](#front-end-corpus)'s `knownDifferences` lists it for a seed of
  `--avoid-known`, or `knownKinds` lists it: the kinds that runs of fresh
  seeds found, each recorded on its issue, with the seed where a run found
  it first, which no corpus spec has, so that `lake test` does not check
  them. An entry of `knownKinds` may write `*` for any text, so that one
  entry stands for a family: after a static error, any lint that only
  `fren` reports. Each difference's kind, with the issue of its entry, is
  recorded in the run's results (`results-ID.jsonl`), and `--report DIR`
  gives every result in `DIR` as Markdown: the specs that fail, each with
  its kinds, new or known, and each known kind, with its issue and the
  seeds of the specs that have it, and each spec that took more than 20 s,
  with how long it spent in queries that reached their time limit. A
  kind is the difference without its line, names and values, as the
  fuzzer's summary gives it (`signature`). Of its numbers, only those that
  place it or count what the spec happens to have are values: a line, a
  row's or an arm's number, and a count of behaviours. Every other number
  is part of the kind: an exit code, a size bound, the counts of a
  summary's verdicts or of a note's checks. Nor is a difference whose
  wording a kind masks whole, as a summary or the core of a realizability
  check (`fren says …, Lean says …`) is, listed as a kind on its own: it is a
  disagreement on a verdict, to be fixed, and is known only alongside a
  kind that explains it, as Lean's failure to decide a check explains the
  summary's count of inconclusive results, or where the difference itself
  passes a test of what the kind masks (`test?`), as a conflict core whose
  clauses, by name, are `fren`'s and more on Lean's side
  (`leanCoreHasMore`). A kind that a static error
  explains, as the front ends' different recovery from it does, is
  listed as such (`afterStaticError`), and is known only on a spec where
  both front ends report a static error, at the same place, at or before
  its line (an internal error, as the evaluator's, is none): a static
  error that only one front end reports is a difference itself, and
  explains nothing; and
  one that another difference explains, as the evaluator's internal error
  explains an exit code, only alongside that difference (`alongside?`),
  and, where the entry says so, only at its line (`onItsLine`), as Lean's
  failure to decide a check explains what only `fren` reports of that
  check.
  `compare` masks only what may legitimately differ, above; a known
  difference is fixed, or listed in `knownDifferences` or `knownKinds`
  with its issue, and not masked. The known column differences of #555 are of static errors
  that the generator does not write (an unknown method or field, a
  `refines`, an invalid string pattern, a higher-order call's arity), so
  `compare` masks no column. `--files FILE...` compares the front ends on
  given files, and `--print SEED` prints a generated spec. The comparison
  itself is tested in `FrenTest/FrontendsCompare.lean`.
- **Front-end corpus** (`lake test`): the front-end fuzzer's specs of a
  fixed set of seeds, from its generators, the default one, `--guards`,
  `--sites` and `--confirm` (`corpus` in `src/FrenTest/FuzzFrontends.lean`), are checked
  with both front ends and compared as above, in `frontendFuzz` jobs of a
  few dozen seeds each. Every difference must be listed in
  `knownDifferences`, beside the corpus, by its generator, its seed and
  the difference itself, line, column and names included, with the issue
  that tracks it; each entry stands for one occurrence, so a difference
  that occurs more often than it is listed fails too; and every listed one
  must still occur, so that the list only shrinks, as
  `knownColumnDifferences` does for the ui tests' columns. The
  differences that time limits may explain, each about an undecided
  check, and the summary's and exit status's when one of those is among
  them, are left out one by one, and a listed one that no longer occurs
  does not fail on a spec where either front end left a check undecided.
  The matching is the pure function `unmatched`, tested with `#guard`s
  beside it. A failure says how to reproduce the spec, and the entry that
  would list it.

  An extension of the generator leaves every seed's spec as it was, up to
  what it appends, so the corpus's differences stay as they were: it is
  never absorbed by relisting `knownDifferences`. Its random draws come
  after all the existing ones, and its items in a group of their own at
  the end. The default generator marks where each group that it appends
  after `bodyFns` starts (`Wide.genWideCuts`), and the job fails on a
  static error of the `fren` command (an error that is not a check's
  result) located in one of those groups (`appendedErrors`), since an
  error stops every check of the spec: deliberate errors go in a mode of
  their own. The check reads where the errors are, not whether the spec
  stops, so it sees a group's error even on the many specs that already
  stop before it: the procedures and `bodyFns`, older than this rule,
  write static errors, some on purpose (a body of another type) and some
  not (#589), and about half the default seeds' specs stop before
  `bodyFns`'s group. The comparison of check results sees nothing on those
  specs. The check has two blind spots: it reads only the `fren` command's
  errors, so an error that only Lean reports is left to the comparison,
  where `knownDifferences` may list it; and a parse error before the first
  cut hides every later error, as it stops the `fren` command (no corpus
  spec has one today). A static error without a location is blamed on the
  first group. An entry of `knownDifferences` holds the whole difference:
  its line and column, the names that a front end gives its own facts, as
  Lean's `f0.equation0.1`, and the message's wording. A change to any of
  those, such as to where a front end places a message or to the generated
  text before it on its line, shows as an unlisted and a vanished
  difference on the same line, to be relisted; on a spec with an undecided
  check, only the unlisted one shows. The corpus is sized to take about 2
  minutes of one CI machine. A crash of the solver fails its job, and a
  spec that never ends holds it up, as in any other job.

`lake test` runs its tests as jobs, in parallel: each job is a process of
its own (`fren_test --job NAME ARG...`), and the ui tests run in batches of
at most eight files, each importing `Fren` once. The mutants are checked in
a job per group of the corpus, and those of Fren's own requirements in
64 jobs, its *slices*, each taking every 64th mutant: each slice makes
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

CI splits the jobs over machines. `lake test -- --shard K/N`, for
`K < N`, runs the `K`th of `N` shards, which together run each job once:
shard 0 runs only the first job, which checks Fren's own requirements
with the binary and takes about as long on one machine as all the other
jobs but the mutants of Fren's own requirements, and the others are dealt
in turn to shards 1 to `N - 1`, so that the slowest, which come first,
spread over them.
`--skip-own-mutants` leaves out the slices of the mutants of Fren's own
requirements, the slowest jobs, which only the CI run on `main` checks.
The selection is made before `--bless` runs the snapshots job first.
`--timings` prints how long each job took, to balance the shards.

## Shards

A job is the arguments of `fren_test --job`, and `testing::own_mutants?`
says which jobs are slices of the mutants of Fren's own requirements:
those of the first group of the corpus, which is Fren's own requirements.
`testing::shard` states which shard runs each job, for any list of jobs,
as `FrenTest.Jobs.placement` gives it: every job that `--skip-own-mutants`
keeps is run by exactly one shard, of `0` to `N - 1`, and no other job is
run; and shard 0 runs only the first job kept. Without `--shard`, there
is one shard, which runs every job kept. `jobs` in `src/FrenTestMain.lean`
lists `ownSpec` first. The shard `K/N` runs, in order, the jobs that
`placement` puts in `K` (`FrenTest.Jobs.selectJobs`), so the shards
together run each job kept once. How the other jobs are dealt over shards
1 to `N - 1`, in turn, is left to the code: it only balances the shards.

```fren
-- The job checks a slice of the mutants of Fren's own requirements:
-- `mutation 0 SLICE SLICES`.
pub fn own_mutants?(job: Seq<String>) := job.len = 4 and job[0] = "mutation" and job[1] = "0"

-- `--skip-own-mutants`, if `skip?`, leaves out the job.
pub fn skipped?(job: Seq<String>, skip?) := skip? and own_mutants?(job)

-- Each job before position `i` is left out.
set_option fren.lint.undecidable "allow" in
pub fn first_kept?(jobs: Seq<Seq<String>>, skip?, i: Int) :=
    forall (h: Int), when 0 <= h < i, skipped?(jobs[h], skip?)

-- Over any number of jobs, so outside the decidable core: tested here, and
-- proved in Lean of the driver's code.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc shard(
    jobs: Seq<Seq<String>>,     -- the jobs, as `jobs` lists them, the slowest first
    skip?,                      -- `--skip-own-mutants` is given
    n: Int,                     -- `N` of `--shard K/N`, or 1 without it
    i: Int,                     -- a position in `jobs`
): (
    det runs?,                  -- some shard runs the job at `i`
    k: Int,                     -- the shard that runs it, or -1
) {
    assume shards: n >= 1
    assume position: 0 <= i < jobs.len

    ensure kept: runs? iff not skipped?(jobs[i], skip?)
    ensure once: if runs? then 0 <= k < n else k = -1
    ensure first_alone: when runs? and n >= 2, k = 0 iff first_kept?(jobs, skip?, i)

    expect one_shard: when n = 1 and runs?, k = 0
    expect others_kept: unless skip?, runs?
}
```

## Fuzzer time limit

The front-end fuzzer stops a spec that runs longer than `--spec-timeout`
and records it as a timeout, a finding. A solver query that reaches its
time limit (10 s by default, in both front ends) is slow by design, and
a spec whose checks leave three or more undecided that way, one after
another, can take more than 30 s on any machine, with nothing wrong
(seed 1198158 has four). So the time that counts leaves out the
wall-clock time that queries which ended at their time limit cover. Each
front end records it as it goes (`Fren.Core.solverCredit`), and the
worker reports it while a spec runs.

Queries run in parallel, in both front ends, so what is left out is not
the sum of their durations, which would leave out 40 s for four queries
that time out together in 10 s, and so hide 30 s of anything else. Each
query that times out leaves out only its part after the latest end of
the queries left out before it (`testing::solver_credit`): every part
left out is within its query and after every earlier part, whatever
order the queries end in, so the parts never overlap, and the time left
out is at most the length of the union of the queries, and never more
than the wall time from the first one's start. A query counts from its
start, but for at most its own time limit and a second
(`Fren.Core.slackMs`) before it ended: what a front end does before the
solver starts, such as lean-smt's translation of the goal in Lean, still
counts, though the binary times only cvc5's `checkSat`.

What still counts is a hang: a loop of Fren's own, in the evaluator or
anywhere else, and a query that runs on past its time limit, which
reports nothing until it ends. A query that is still running counts in
full. A hang that runs at the same time as a query that times out, in
another check or the other front end's, is hidden while they overlap, by
at most that query's time (its time limit and the slack): what is left
out is wall time, which the hang shares. The spec is stopped once the
time since it started, less what was left out since then (`timed_out`),
is more than the limit (`testing::fuzz_overdue`).

```fren
pub proc solver_credit(
    credit: Nat,                -- the milliseconds left out so far
    covered: Nat,               -- the latest end of a query left out so far
    start: Nat,                 -- when a query that ended at its time limit started, or its limit and the slack before it ended, if later
    stop: Nat,                  -- when it ended
    first: Nat,                 -- when the first query left out started
): (det credit_after: Nat, det covered_after: Nat) {
    assume times: first <= start <= stop

    ensure new_time: credit_after = credit + (if stop > start.max(covered) then stop - start.max(covered) else 0)
    ensure covers: covered_after = covered.max(stop)

    -- What a query leaves out lies within it...
    expect within_query: credit_after <= credit + (stop - start)
    -- ...and after all that was left out before, so the parts never overlap.
    expect after_covered: credit_after <= credit + (if stop > covered then stop - covered else 0)
    -- So, by induction over the queries from nothing left out, with
    -- `within_query`, `after_covered` and `covers`, the time left out is at
    -- most the length of the union of the queries, and never more than the
    -- wall time since the first one started.
    expect within_wall_time: when credit + first <= covered.max(first), credit_after + first <= covered_after.max(first)
    -- Four queries at once leave out the time of one.
    expect parallel: when credit = 10000 and covered = 10000 and start = 0 and stop = 10000, credit_after = 10000
    -- The 5 s between two queries are not left out, so a hang there counts.
    expect gap: when credit = 10000 and covered = 10000 and start = 15000 and stop = 25000,
        credit_after = 20000 and covered_after - credit_after = 5000
    cover overlapping: start < covered < stop
}

pub proc fuzz_overdue(
    limit: Nat,                 -- `--spec-timeout`, in seconds
    elapsed: Nat,               -- milliseconds since the spec started
    timed_out: Nat,             -- how much `solver_credit` left out since then
): (det overdue?) {
    ensure rule: overdue? iff elapsed > limit * 1000 + timed_out

    expect no_timeouts: when timed_out = 0, overdue? iff elapsed > limit * 1000
    expect left_out: when elapsed <= timed_out, not overdue?
    cover hang: overdue? and timed_out > 0
}
```

## Expectations

A ui file passes, for a front end, exactly when each of its messages is
expected, and each expectation is met once, on its line. The annotations
give the expectations: `--~` one on its line, `--~^` one on the line above,
and so on, `--~$` one with no line, which is line 0, `--~?` one that may
go without a message, and `--~[cli]` or `--~[hosted]` one for that front
end alone, which for the other expects nothing and allows nothing. A
message *meets* an expectation that applies to its front end when it is on
its line, of its severity, and its text contains the expectation's.
`testing::met?` says that the expectations can each be given the position
of a message that meets it, or `-1`, if it may go without one, a different
message for each, so that every message is given to one. The `--@` lines
expect a summary and an exit code: the summary must then be that one, and
the exit code too, where the front end has one, as the binary does and
Lean does not.

Giving each expectation the first message left that meets it is not
enough: with expectations `x` and `xy` on one line, and messages `xy` and
`x` there, `x` would take `xy`, which `xy` needed. Searching every way of
giving them, as `FrenTest.Ui.assignable` does, takes time exponential in
the number of expectations that the same messages meet, multiplied across
lines. So `FrenTest.Ui.check` gives them by bipartite matching (`solve`),
in time polynomial in the numbers of expectations and messages: first
each message an expectation that it meets, by augmenting paths, and then
each expectation that needs a message one, without taking any message's
away. Its answer comes with what shows it right, which `check` checks: a
way of giving them, or a set of messages that meet fewer expectations
than there are of them, or a set of expectations that need a message and
are met by fewer messages than there are of them, either of which shows
that there is no way. That the answer always passes the check is tested,
not proved; should it fail, `check` falls back on `assignable`'s search,
so that its verdict is proved either way. It reports each expectation and
each message that the matching could not give. How the annotations are
read from a file's text is tested, in `src/FrenTest/UiCheck.lean`, not proved.

```fren
-- A front end's message, on its line, or 0 for one with no line.
pub struct Message { line: Int, severity: String, text: String }

-- An annotation's expectation: of a message on `line`, with `severity`,
-- whose text contains `text`, for `front_end` alone if it is given, and
-- `optional?` for `--~?`.
pub struct Expectation { line: Int, severity: String, text: String, front_end: Option<String>, optional? }

-- The expectation applies to the front end `front_end`.
pub fn applies?(e: Expectation, front_end: String) := match e.front_end {
    Option::None => true,
    Option::Some(f) => f = front_end,
}

-- The message meets the expectation.
set_option fren.lint.undecidable "allow" in
pub fn meets?(m: Message, e: Expectation) :=
    m.line = e.line and m.severity = e.severity and m.text.contains?(e.text)

-- `a` gives the expectation at `i` the position of a message that meets
-- it, or -1 where it may go without one.
set_option fren.lint.undecidable "allow" in
pub fn gives?(ms: Seq<Message>, es: Seq<Expectation>, front_end: String, a: Seq<Int>, i: Int) :=
    if a[i] = -1 then es[i].optional? or not applies?(es[i], front_end)
    else 0 <= a[i] < ms.len and applies?(es[i], front_end) and meets?(ms[a[i]], es[i])

-- `a` gives each expectation a message or -1, a different message for
-- each, and every message to one.
set_option fren.lint.undecidable "allow" in
pub fn assigns?(ms: Seq<Message>, es: Seq<Expectation>, front_end: String, a: Seq<Int>) :=
    a.len = es.len
    and (forall (i: Int), when 0 <= i < es.len, gives?(ms, es, front_end, a, i))
    and (forall (i: Int) (j: Int), when 0 <= i < j < es.len and a[i] != -1, a[i] != a[j])
    and (forall (m: Int), when 0 <= m < ms.len, exists (i: Int), 0 <= i < es.len and a[i] = m)

-- The messages meet the expectations.
set_option fren.lint.undecidable "allow" in
pub fn met?(ms: Seq<Message>, es: Seq<Expectation>, front_end: String) :=
    exists (a: Seq<Int>), assigns?(ms, es, front_end, a)

set_option fren.lint.undecidable "allow" in
pub proc ui_file(
    ms: Seq<Message>,               -- the front end's messages
    es: Seq<Expectation>,           -- the file's expectations
    front_end: String,              -- `cli` or `hosted`
    summary: Option<String>,        -- `--@ summary:`
    got_summary: Option<String>,    -- the front end's summary
    exit: Option<Int>,              -- `--@ exit:`
    got_exit: Option<Int>,          -- the front end's exit code; Lean has none
): (det passes?) {
    ensure rule: passes? iff met?(ms, es, front_end)
        and (match summary {
            Option::None => true,
            Option::Some(s) => got_summary = Option::Some(s),
        })
        and (match exit, got_exit {
            Option::Some(x), Option::Some(g) => x = g,
            _, _ => true,
        })
}
```

## Fresh results

A test's result is *fresh* when it is that of the files it reads as they
are now: its module was rebuilt after the last change to any of them, or
none of them changed. Lake rebuilds a module when a file that its library
needs changed since its last build, which Fren trusts; that each module
that reads files, with `#fren_md`, reads only files that its library
needs is what the `libraries` job checks, by reading the sources and
`lakefile.lean`, so it is tested, not proved. `testing::fresh` states how
the two give freshness: whenever the files read are among those needed,
the result is fresh.

The same goes for the driver itself: `lake test` runs `fren_test`, its
test driver, after Lake has rebuilt it from the sources as they are now.
Running the driver by hand, as `lake env .lake/build/bin/fren_test --job
...`, runs whatever was built last, which nothing checks: build it first
with `lake build fren_test`.

```fren
-- A file of the repository.
pub type File

pub proc fresh(
    reads: Set<File>,       -- the files that the module reads when it is built
    needs: Set<File>,       -- the files that its library needs
    changed: Set<File>,     -- the files changed since its last build
    rebuilt?,               -- Lake rebuilds it
): (det fresh?) {
    assume lake: when needs inter changed != {}, rebuilt?
    ensure rule: fresh? iff (rebuilt? or reads inter changed = {})

    expect read_needed: when reads subset needs, fresh?
    cover stale: not fresh?
}

#fren_check
```

## Heavy jobs

`lake build`, `lake test`, the fuzzers and mutation runs each use every
core, so parallel jobs on one machine slow each other down and can run
it out of memory. `scripts/heavy COMMAND` runs COMMAND while it holds
one of a few slots shared by the whole machine, waiting for a free one,
and keeps the jobs that hold them under a memory cap. Its state is in
`~/.cache/heavy/`, so every worktree and every copy of the script share
the slots. Both limits are read again while jobs run, so changing a file
takes effect at once, without a restart:

- **Slots:** `HEAVY_SLOTS`, else the number in `~/.cache/heavy/slots`,
  else 2.
- **Memory:** `HEAVY_MEM_GB` gigabytes, else the number in
  `~/.cache/heavy/mem_gb`, else 80% of the machine's physical memory,
  summed over each job's process group. A job waits to start while the
  running ones use more than 60% of the cap; when they use more than
  the cap, heavy kills the newest and exits with 137.

A setting that is set but is not a positive finite number is ignored,
with a warning.

`scripts/heavy --offline COMMAND` runs COMMAND with no network. On Linux
it runs in a new user and network namespace (`unshare -rn`, which needs
unprivileged user namespaces), whose loopback is down, as uid 0 mapped
to the user. On macOS it runs under `sandbox-exec` with a profile that
denies IP networking, loopback included, and name lookups. Where it cannot cut the network, it
fails rather than run COMMAND online. Use it to run binaries that a pull
request built, the fuzzers and mutation runs, which never need the
network. Builds and `lake test` stay online: Lake fetches packages and
elan fetches toolchains. `python3 scripts/heavy_test.py` tests its
argument parsing, its memory cap and the order of its overrides, and
the `lint` workflow runs it.

## Shared builds

Lake keeps an artifact cache for each toolchain on a machine, which
`lakefile.lean` enables, and which every worktree on the machine shares.
Each step of a build, a module's elaboration, its C compilation or a link,
is keyed by a hash of its inputs by their content: the module's source,
the outputs of the modules that it imports, the files that its library
needs, its options and the toolchain. A step whose key a build on the
machine met before takes that build's outputs from the cache, linked into
`.lake/build`, instead of running. So a new worktree, a reviewer's
checkout of a head or a probe of a merge commit runs only the steps that
no build on the machine ran with the same inputs. The key covers every
file that the module's library needs, so `testing::fresh` holds as
before.

A coverage build (`-Kcoverage`) uses the cache only with
`-Kcoverage_dir=DIR`, where DIR is the worktree's own directory, which
`coverage_new.py` passes: each of its object files names the directory
where it writes its counters, and the option puts that directory into the
key of the step that compiles it, so no other worktree is given it.
`lakefile.lean` compares DIR with its own directory, and another, such as
one copied from another worktree's command, turns the cache off. The
coverage build's other steps, whose outputs name no directory, are
shared. The key covers `-Kcoverage`'s compiler options too, so a coverage
build's outputs and a normal build's never mix. Compiling an object also
writes gcov's notes (`.gcno`) beside it, which the cache does not keep: a
module edited and then reverted gets its first object back with the
notes of the second, and one whose `.lake/build` was deleted gets it back
with none. So `coverage_new.py` deletes an object whose notes are missing
or newer than it, and its copy in the cache, which only this worktree's
builds use, and builds again, which compiles it (Lake warns that the copy
is gone); and `fren_coverage` checks that each module's notes and
counters have the same stamp, that of the object that wrote the counters,
and otherwise stops, naming the module. Without `-Kcoverage_dir`, as on
CI, a coverage build does not use the cache.

The cache keeps a step's outputs but not its messages. A module that is
up to date in a worktree's own `.lake/build` replays its messages from its
trace, as before; one taken from the cache reports none. So a local `lake
build --wfail` passes over a warning that only another worktree's build of
the same module reported, and `ownSpecAgreement`, which reads Lean's
messages from the traces, reports a module taken from the cache as one
whose checks it cannot tell ran. `pre-merge` stays the gate: each of CI's
machines starts with an empty cache.

The cache only grows. Each build adds the outputs of every step that it
runs, several hundred MB to some 1 GB for a head that changes `Fren` or
`FrenCore`, and its `.lake/build` links to them, read-only. So deleting a
worktree's `.lake` breaks nothing but frees almost nothing either: the
cache keeps the outputs, and frees them only when pruned. That holds when
the worktrees are on the filesystem of the toolchain's directory, as
`/tmp` and `~/.elan` often are: across filesystems, Lake copies the
outputs instead of linking them, so they take disk twice and link counts
say nothing of which a worktree uses. The cache is per toolchain, so
after a toolchain bump the old one's cache stays until it is pruned with
`--cache DIR` or deleted, once no worktree builds with that toolchain.

`scripts/lake_cache.py size` prints how much the cache holds, and how much
of it no worktree links to. `scripts/heavy python3 scripts/lake_cache.py prune`
deletes the outputs that no worktree links to and whose links have not
changed for 7 days (`--days`), and the cache's entries that name them: the
entries first, so that a build that finds an entry gone runs the step and
saves its outputs again, and then, after a grace of a minute, each output
whose link count and `ctime` are still those it scanned, so that one that
a build linked or saved again in the meantime stays, but for one that a
build links in the microseconds between that check and the deletion. A build that finds
an entry whose outputs are gone warns, which fails `--wfail`, and runs
the step; pruning deletes such entries too. It refuses to prune a cache on
another filesystem than the worktree that runs it. It checks only that
worktree: another on another filesystem holds copies of its outputs, which
pruning leaves alone, but they count as no link, so the entries of its
steps may be pruned, and a build that would take them from the cache runs
them again. Run it under `scripts/heavy`, when
the disk is short or once a week; `python3 scripts/lake_cache.py test`
checks it on a scratch cache, and the `lint` workflow runs that test.
`lake cache clean`, which empties the cache at
once, is safe only while no build runs.

A step's outputs must then not depend on where it ran, or a worktree
would get another's. Lean names a module's source by its absolute path,
and a definition's `source?` (`Fren.DefinedInfo`) keeps the name of the
file that declares it, for the messages about it. It keeps the name
relative to the directory that Lean runs in (`Fren.keptFileName`, which
`testing::portable_name` states, with that directory as its input). Lake
runs Lean in the directory that Lake was started in, which is the
package's root for `lake build` and `lake test` run there, as
`scripts/heavy` runs them and CI does. A build started elsewhere, as
`lake -d ROOT build`, keeps absolute names, and its outputs, which
another worktree may take from the cache, then differ only in the names
that messages about other files' definitions show. A message about the
definition names the current file as Lean names it, if the definition is
in it, and the other file by the kept name otherwise
(`Fren.shownFileName`).

`scripts/relocatable.py` checks that no `.olean` or `.ilean` file, and no
file of C code or object code under `.lake/build/ir`, that a build wrote
names the worktree's directory, which it would if anything else kept an
absolute path. The build jobs of `pre-merge` and `lean ci` run it
after `lake build --wfail`, over the outputs written after the build began:
the others are `main`'s, checked by the build that wrote them, or stale
files of modules that the build no longer has. It checks Fren's own
outputs, not the dependencies' in `.lake/packages`: lean-smt's shared
libraries keep the absolute install name of the directory that built them,
which nothing reads, since Lean loads each of them by its path.

```fren
set_option fren.lint.undecidable "allow" in
pub proc portable_name(root: String, file: String): (det name: String) {
    out name :=
        if file.starts_with?(root ++ "/") then file.slice(root.len + 1, file.len - root.len - 1) else file

    expect round_trip: when file.starts_with?(root ++ "/"), root ++ "/" ++ name = file
    cover inside: file.starts_with?(root ++ "/")
    cover outside: not file.starts_with?(root ++ "/")
}

#fren_check
```

## Own requirements

`lake build` elaborates Fren's own requirements, the specs of `src/Reqs`
that `#fren_md` reads, but does not check them. The libraries of `Reqs` in
`lakefile.lean` set `fren.runChecks` to false (`Reqs/Lean#options`), so
each spec's items are elaborated, with their static errors and lints, and
its definitions are there for the `impl`s of `Impls`, whose proofs the
build still checks, but its `#fren_check`s check nothing. The binary
checks them: `lake test`'s `ownSpec` job runs `fren check` over
`ownSpecFiles`, which must list every spec that a `#fren_md` of
`src/Reqs` reads. It runs the same checks at the same evidence as
`#fren_check` would, and also those set to random testing, which Lean
does not run. It runs in shard 0 of `pre-merge`, so it is the gate of
every pull request.

On `main`, the `lean ci` workflow's `own-spec-agreement` job checks them
in Lean too. `lake -R -Kcheck_reqs=1 build --wfail Reqs` builds the
modules of `Reqs` with `fren.runChecks` on, so that a failing or
inconclusive check in Lean fails it. The test driver's
`ownSpecAgreement` job, which is not among `lake test`'s jobs, then
compares the messages that Lean reported about each spec, which Lake
keeps in each module's trace, with those of `fren check`, spec by spec,
as the front-end fuzzer compares a spec's (`FrenTest.Frontends`). It
leaves out the summaries, since Lean reports one for each `#fren_check`,
and what only the binary runs: the checks set to random testing and those
that rest on them, which Lean leaves to `fren check` and does not report
([Evidence](../Evidence.md#lean)). Lean and the binary report the checks
of an item that has one of Lean's notes that it leaves checks to `fren
check` differently, so the comparison leaves out every message that the
binary gives about such an item: a check of it that Lean failed to report
would go unnoticed there, though the binary's result still gates. Lean reports a check once for each
`#fren_check` of its file that runs it, so each of its messages counts
once. It fails if a module was built without its checks. A pull request does not
run it, so a difference between the front ends that a pull request
causes in Fren's own requirements fails `main`'s next run, not the pull
request's.

## Continuous integration

On a pull request, the `pre-merge` workflow checks the head merged into
`main`, starting from the `.lake` that `main`'s last build left: one
machine runs `lake build --wfail`, and others run `lake test --
--skip-own-mutants --shard K/N`, each building only the test driver. On
`main`, the `lean ci` workflow runs `lake build --wfail` and the whole
`lake test`, samples mutants of Fren's own requirements, checks them in
Lean and compares the front ends' messages about them ([Own
requirements](#own-requirements)), measures the coverage, and saves the
`.lake` for pull requests. Each job of a `lean ci` run waits for the same
job of the run before it, not for the whole run, so that the build job
saves the `.lake` as soon as it has built. A `pre-merge` run that starts
before the `.lake` of its `main` is saved starts from an older one, and
each of its machines rebuilds what `main` changed since. Over the runs of
2026-11-01 and 2026-11-02, almost half did; had each build job waited only
for the one before it, the median time from a push to `main` to its
`.lake` being saved would have been some 6 minutes instead of 13, and a
fifth would have. The runners' artifact caches ([Shared
builds](#shared-builds)) start empty, so on CI every step that `.lake`
does not have runs, and reports its messages. It also compares the methods on every check that each can run
(`methodsAgree`, [Agreement of methods](../Methods.md#agreement-of-methods)), and runs the
front-end fuzzer on seeds that no run used before, from the run's number,
with `--avoid-known`, of both generators. What fails that job is exactly a
spec with a difference of a kind that is not known, a crash, or a
timeout; a spec whose differences are all of known kinds
(`knownDifferences` for `--avoid-known`, and `knownKinds`), or only in
undecided checks, does not. The job's summary gives `--report`'s
Markdown, so that what it found and did not fail on is not lost, and the
specs it found are uploaded as the artifact `fuzz-frontends-RUN` (those
of known kinds as `known-fe-seedN.fren`). A spec of a new kind is fixed,
or its kind is recorded on its issue and listed in `knownKinds`; CI posts
to no issue. The known kinds go unchecked on those seeds, of either
generator: today Lean's extra report of a chain of methods that has a
shorter form (`F0743`, #493), the front ends' different recovery after a
static error (#493, #295), and the kinds of #493, #484 and #485 that
`knownKinds`'s comments name. The kinds listed only for the default
generator are checked there. A run of `lean ci` by hand
(`workflow_dispatch`), on any branch, may run that job alone
(`fuzz-only`) and on more seeds (`fuzz-count`). The `lint` workflow runs `lun run --check` on
both. The book is built by the `book` job, with no Lean: it runs the
stripped test driver that its run's shard 0 built and uploaded as
`fren_test-SHA`, to write the page of the rules ([Writing the
reference](Style.md#rules-and-requirements)). On a pull request it is a job
of `pre-merge`, shown as `book / book`; on `main`, a job of `lean ci`,
shown as `book / book` in that run, after its shards. Where shard 0 was
cancelled or failed before it uploaded the driver, `book` builds nothing
and passes, with a notice. The `pre-merge` workflow's last job, also named
`pre-merge`, passes only if its build and every shard passed and, on a
pull request, the book was built and passed (`scripts/pre_merge_verdict.py`,
which `lint` tests on every combination of its jobs' results): it is the
status that reviewers and the coordinator rely on.

Where each check runs, and why. The rule is the speed of development as a
whole: a check that is cheap gates every pull request, and one that is
expensive runs on `main` only, where a failure is fixed by a small pull
request of its own rather than slowing every pull request down.

| Check | `pre-merge` | `lean ci` | Why |
|---|---|---|---|
| `lake build --wfail`: the code, the regression tests, the `impl`s' proofs, the examples, and Fren's own requirements elaborated | yes | yes | it is the build |
| `lake test`, but for the mutants of Fren's own requirements | yes | yes | under 10 minutes in each shard |
| `ownSpec`: Fren's own requirements checked by the binary | yes | yes, with an empty query cache | some 25 s on CI with the query cache, so it is the gate |
| The mutants of Fren's own requirements (`mutation 0 …`) | no | yes | the slowest jobs of `lake test` |
| Fren's own requirements checked in Lean, and `ownSpecAgreement` ([Own requirements](#own-requirements)) | no | yes | in `lake build`, the checks took some 80 s of `Reqs.Lang` (256 s with them, 176 s without) and 76 s of `Reqs.Lint` (239 s, 163 s), both on the critical path, which they made 155 s longer, and raised the peak memory of each from some 2.5 GiB to some 10 GiB (one run each) |
| `methodsAgree`: every check of Fren's own requirements, the ui tests and the fuzzer's corpus under the solver, enumeration and random testing, compared ([Agreement of methods](../Methods.md#agreement-of-methods)) | no | yes | it checks everything three times, and the solver, asked the checks that the specs leave to the other methods, took 9.4 GB on Fren's own requirements at two procedures at once, as the job runs them (13.8 GB at four), and some 4 minutes, and 8.8 GB on the ui tests at fourteen, on macOS: more than a `lake test` shard can spare |
| The book, with the page of the rules (`book`) | yes, on a pull request, and part of `pre-merge`'s verdict | yes | some minutes, with the test driver of shard 0, and no Lean |
| A sample of `fren mutate` over Fren's own requirements, the front-end fuzzer on fresh seeds, the coverage | no | yes | each needs a build or seeds of its own, and what they find is filed or fixed after |

On a pull request, `pre-merge` also uploads stripped copies of the
binaries that it built and tested, so that a reviewer can probe the head
without building it: `fren`, once the build has passed, as the artifact
`fren-SHA`, and `fren_test`, once shard 0 has built it, as
`fren_test-SHA`, where SHA is the full sha of the pull request's head.
They are kept for 3 days. They are Linux binaries, built on
`ubuntu-24.04`, which run on Linux machines such as sky but not on macOS.
On `main`, `lean ci`'s shard 0 uploads its stripped `fren_test` as
`fren_test-SHA` too, where SHA is `main`'s commit, for the book; that one
has no `MERGE_SHA`, since it is built from that commit itself.

They are built from the head merged into `main`, as the tests are, not
from the head itself, so each artifact holds the merge commit's sha in
`MERGE_SHA`, and its parents, `main`'s commit and the head, in
`MERGE_PARENTS`. Probe in a checkout of exactly that commit. Once `main`
has moved past the head's base, the head's own tree differs from the code
compiled into the binary: `fren_test` would read test files and specs
that do not match it, and the hosted front end's jobs would load
`.olean` files of other code next to its compiled code, which can give
wrong results or crash. GitHub moves the pull request's merge ref when
`main` moves, so fetch the commit by its sha; if that fails, merging the
head into `main`'s commit, as `MERGE_PARENTS` names them, rebuilds the same
tree. A zip artifact may lose the executable bit, which `chmod` restores:

```sh
gh run list --workflow pre-merge --branch BRANCH --json headSha,databaseId
gh run download RUN -n fren-SHA -D /tmp/fren-SHA
chmod +x /tmp/fren-SHA/fren
git fetch origin "$(cat /tmp/fren-SHA/MERGE_SHA)"
git checkout --detach "$(cat /tmp/fren-SHA/MERGE_SHA)"
scripts/heavy --offline /tmp/fren-SHA/fren check FILE
```

`fren` needs nothing else, for `fren check`, `quickcheck`, `mutate` and
`fmt`. `fren_test --job JOB` reads the test files and specs of the
checkout, and writes scratch files under its `.lake`. Its jobs `ui`,
`uiMisread`, `smtAgreement` and `leanTokens` load the hosted front end,
the `.olean` files of `Fren` and its dependencies; for them, run
`scripts/heavy lake build Fren` in the checkout, which compiles no C
code and links nothing, and then `scripts/heavy --offline lake env
/tmp/fren_test-SHA/fren_test --job ui FILE`. Run the binaries that CI
built under `scripts/heavy --offline` ([Heavy jobs](#heavy-jobs)), since
they never need the network. The other jobs, such as `snapshots`,
`errorCodes` and `mutation`, need only the binary. On CI, `fren` is 161
MB, 116 MB stripped and 45 MB compressed, and `fren_test` is 320 MB, 235
MB stripped and 78 MB compressed. The `.olean` files are not uploaded:
those of `Fren` and its dependencies came to some 340 MB, 96 MB
compressed, on macOS.

The `pr-review` workflow reviews each pull request's head with Claude once
`pre-merge` has passed on it, by AGENTS.md's review rules: a full review,
or a light check when the last comment that names the head starts with
"fixes only" or "rebase only" (`.github/pr-review/kind.py`), and none for
an update from `main` of a reviewed head. It never reviews a pull request
from a fork. Its comment counts as the pull request's review, for
everything, and says which probes it ran and which it could not, such as
those that need a rebuild. The only code of the pull request that it runs
is these binaries, `fren check` of each spec that the pull request
changes, in a job of its own with no secret, in a container as `nobody`
with no network, a read-only root and read-only mounts, no capabilities,
no variable of the runner and no docker socket
(`.github/pr-review/sandbox.sh`), so that a probe can affect nothing but
its own output, which `lint` tests with a hostile stand-in for `fren`
(`test_sandbox.sh`). Each probe's output is framed as a code block that
nothing in it can close (`frame.py`, which `lint` tests with a CommonMark
parser). Only comments by the repository's owner, members and
collaborators count as reviews or requests. The reviewer, in the job that
holds the Claude token, reads the probes' output as text, with a checkout
of the head and the diffs that the workflow wrote, with no shell and no
reads outside the checkout, and suggests any other probe in its findings.
The workflow posts the review as one comment, once its check of the
review passes: the first line, a mark on each finding that agrees with
the verdict, the paragraph on the probes, no copy of a token, plain or
encoded, and no names of machines. Whatever it posts, the review or a
note that it failed, which quotes nothing of it, loads nothing from
outside github.com and mentions no one. The Claude token is a repository
secret, which anyone who can push a branch can read, until it is moved to
an environment that only `main` can use. Run by hand (`gh workflow run
pr-review -f pr=N`), it posts only on the pull request that its `post`
input names.

Pull requests merge through GitHub's merge queue. The queue merges each
pull request into the current `main`, behind any pull requests ahead of it
in the queue, and runs `pre-merge` and `lint` on that merge commit. It
merges the pull request only if both pass there, so that two pull requests
that each pass on their own cannot break `main` together.

## Query cache

`lake test` checks Fren's own requirements with `fren check`'s [query
cache](../Cli.md#query-cache), so that a query asked by an earlier run is
answered without the solver. The test driver's `ownSpec` job reads the
directory from `FREN_QUERY_CACHE`, which is `.lake/query-cache` if it is
not set, and keeps no answers if it is empty. `FREN_VERIFY_QUERY_CACHE`, if
set, is the directory to compare with (`--verify-query-cache`): the job
fails if `fren check` compared no answers with it, unless it holds no
entry of the current `queryCacheVersion` and cvc5, which no answer could
be compared with. Only that job uses the cache, and the `queryCache` job
tests the cache itself: the same output cold, in a fresh directory, as
warm, a warm run that writes no entry, so that it answered every query
from the cache, the same entries from two cold runs, a comparison that
compares answers and finds no contradiction, one with entries whose
answers are flipped that reports each as a contradiction with no
position, and a `sat` entry without a model that does not answer a query
that wants one.

Locally, the cache grows with each run: copying a worktree's `.lake`
copies it too, and deleting `.lake/query-cache` clears it. An answer from
it is the one that the solver would give the same key, so a cache from
another branch, or from before a change to the checker, is as good as a
fresh one, as long as every change that alters how `fren check` runs a
script or reads its answer bumped `queryCacheVersion`. A change that
should have bumped it and did not is answered from stale entries, by a
local `lake test` as by `pre-merge`, and only `main`'s cold run below
finds it. To check such a change, or to rule the cache out of a puzzling
result, run with the cache off, `FREN_QUERY_CACHE= lake test`, or delete
`.lake/query-cache`.

On CI, shard 0 of `main`'s `lean ci` run asks every query of the solver,
with an empty cache, and compares each answer with that of the cache that
the previous `main`'s run saved, so that a key that leaves out something
that changes an answer fails `main`'s run. After a change that alters
every key, a bump of `queryCacheVersion` or a new cvc5, the previous
cache has nothing to compare with, and the run compares nothing and
passes; a change to every script, such as to the script's header, that
does not bump `queryCacheVersion` leaves old entries of the same version
and cvc5 that no query asks, and fails the run once, so such a change
bumps it too. It then saves its cache, which
is exactly the answers of that run: entries that no query asks any more
are dropped, so the cache does not grow. A run that found a contradiction
leaves a mark next to its cache and does not save it, so that `main` stays
red, comparing with the last good cache, until the key is fixed. Shard 0
of `pre-merge` restores the last saved cache and never saves one. With
most queries answered from it, Fren's own requirements took some 35% less
CPU in the `fren` command, measured locally: the rest is building the
queries and testing.

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
lake -R -Kcoverage=RUNTIME build fren fren_test fren_coverage FrenFuzz FrenFuzzFrontends
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

`fren_coverage` reads the counters with `GCOV`, without the library path
that `lake exe` sets to Lean's toolchain, whose LLVM libraries are not the
ones that `GCOV` is linked with. It stops with an error, and no report,
when it finds no counters, when `GCOV` fails on one module's, or when the
counters show that nothing ran: each means that the counters were not
read, and a report would list every declaration as never run.

A declaration ran if one of its entry points ran: its own function, or
its boxed or reduced-arity version, which callers may call instead. An
executable's `main` is emitted as `_lean_main`, and is `main`'s. A
specialization `f._at_.g.spec_N` is an entry point of `f`, with
arguments from `g`, and `g` may itself be one. Lambdas, join points and
closed terms are no declaration's: the compiler shares them among
declarations whose code is alike, so that running one would seem to run
another. Calls made while a module is initialized count, as when a
closed term applies a function. The declarations counted are the
compiled definitions of `FrenCore`, `Fren` and `FrenCli` that are
written in the source and compile to a function: not theorems,
constructors, recursors, matchers, projections, `@[inline]` definitions,
`@[extern]` declarations, whose code is C of their own, instances that
`deriving` makes, or definitions without arguments, which
are constants computed at initialization. A definition of a function
type written without parameters, as `def f : Nat → Nat := g`, compiles
with its parameters, so it is counted. A declaration that compiles to a
function that gcov does not report did not run. The proofs of `impl`s
are not code, but the definitions they are about are counted.

Only compiled code is measured, and only code that the executables can
run can be a gap. `fren_coverage` follows the compiled code of each
executable that `lakefile.lean` declares (`lean_exe`), in that
executable's own environment, from its entry points:

- its `main`;
- the initialization of Fren's modules, which runs their `initialize`
  functions and computes their constants: the calls in a constant's
  definition, but not the closures that it makes, which run only through
  code that reads it;
- `@[export]` functions, which C may call;
- the functions whose type is a named function type, such as
  `CommandElab`, which Lean looks up by name and calls, as the attributes
  that register elaborators, macros, formatters and lean-smt's
  translators require;
- every definition of the modules of `specRuntime`: `Fren.Prelude`,
  `Fren.Seq`, `Fren.SeqElems`, `Fren.FinSet`, `Fren.Finite`,
  `Fren.Enumerate`, `FrenCore.Prelude`, `FrenCore.Str` and
  `FrenCore.Regex`. For each spec, the hosted front end generates Lean
  definitions, and compiles and runs them, in `lean` and in the tests.
  Those definitions may call the definitions of these modules: by names
  built from strings, by instances that synthesis finds, and by the
  spec's own identifiers, none of which the compiled code shows.

From what it reaches, it follows each call and each closure of the
compiled code (the IR), and the declarations that a reached definition
names with a `Name` literal or a syntax quotation. A counted declaration
that none of this reaches is no gap, and is not listed
(`testing::coverage`), for one of three reasons:

- only proofs, and what Lean interprets while a module builds, such as
  `#guard`s, `#eval`s and `run_cmd`s, use it, so no test of an
  executable can run it;
- its compiled callers have its code inlined or specialized, even with
  `-Dcompiler.small=0`, so its own function never runs, but its code
  runs, and counts, in theirs, as an `@[inline]` definition's does;
- it is the reference of a `@[csimp]` replacement, which runs in its
  place, or only such a reference uses it. One that ran although nothing
reaches it shows a call that the graph does not see, such as one into
`specRuntime` from a module that it should list; `fren_coverage` warns of
each, by name, on GitHub Actions as an annotation too. The Lean-hosted
front end's elaborators run in the interpreter where a test elaborates
Fren in Lean, so some of them are listed although the ui tests elaborate
them.

`testing::coverage` is proved of `fren_coverage`'s verdict on each
declaration (`FrenTest.Coverage.fails` and `stale`). Its inputs are
trusted: `ran?` is gcov's counters, and `reached?` is
`FrenCoverage.reached`, which no Req states and no evidence backs (#679).

```fren
pub proc coverage(
    ran?,                       -- gcov's counters show that one of its entry points ran
    reached?,                   -- an entry point reaches it, of an executable or of generated code
    listed?,                    -- `test/coverage.txt` lists it
): (det fails?, det stale?) {
    ensure gap: fails? iff not ran? and reached? and not listed?
    ensure needless_line: stale? iff listed? and (ran? or not reached?)

    -- A function that no entry point reaches, such as one that only proofs
    -- use, never fails, and needs no line...
    expect proof_only: when not reached?, not fails? and (stale? iff listed?)
    -- ...but one that an executable can run fails until a test runs it or
    -- a line says why none can.
    expect compiled_untested: when reached? and not ran?, fails? iff not listed?
    -- A line is needed exactly where it keeps a declaration from failing.
    expect line_needed: when listed?, not stale? iff not ran? and reached?
    cover failing: fails?
}
```

A counted definition that nothing refers to at all, not even a proof, is
dead: it is deleted, not listed. `fren_coverage` reports each as `DEAD`,
in its log and in the job's summary, but does not fail on them, since it
finds them in the sources' text: a `def`, `abbrev` or `opaque` without an
attribute whose name appears nowhere in `src` or `examples`, in Lean or in
Markdown, but in its own declaration. A name that code builds from
strings would seem dead; and dead code whose short name another
declaration, or prose, shares goes unreported.

`test/coverage.txt` lists the counted declarations that no test runs, one
per line. One that is never meant to run, such as code that runs only when
the evaluator refutes the solver, says why after ` -- `. `fren_coverage`
fails on a counted declaration that does not run and is not listed: code
that no test runs fails on `main`, in the push that adds it. A listed one
that runs or is no longer counted only weakens the list, and gets a
warning, on GitHub Actions an annotation of the run too, that names the
line to remove; `fren_coverage --write` rewrites the list as the run found
it, keeping the reasons. The aim is a list of reasons alone. CI runs it on
`main`, with Lean CI, and not in `pre-merge`: the instrumented build and
the whole `lake test` on one machine take 20 to 35 minutes, about twice
`pre-merge`'s 12 to 15, so a pull request that adds code no test runs
fails `main` right after it merges, and a small pull request lists or
tests it. The job's summary gives the counts, the failures, the stale
lines and the dead code.

Before pushing, an author checks the definitions that the branch adds,
in two steps, with `main`'s job as the backstop:

1. `python3 scripts/coverage_new.py` (`fren_coverage --static --new
   origin/main`) lists each counted definition that the working tree adds
   since its merge base with `origin/main`, or in a file that git does
   not track yet. It first brings up to date the `.olean` files that it
   reads, of `Fren` and of every executable's root, which takes seconds
   on a built worktree: `UNREACHED` needs no test, `DEAD` is deleted (and
   fails the step), and `REACHED` needs a test, which the pull request
   names. A normal build inlines small functions, whose calls are then
   gone from the compiled code, so this step also counts as reached what
   any reached definition's definition uses.
2. `python3 scripts/coverage_new.py --run JOB ARG...`, with `--run` once
   for each `fren_test` job that the change affects, builds `fren_test`
   with the counters, using the artifact cache, so that only what changed
   is compiled again ([Shared builds](#shared-builds)); clears the
   counters; runs those jobs; and fails on a reached new definition that
   none of them ran and that `test/coverage.txt` does not list. For
   example, a change to one module, `FrenCli.Run`, with the rest built
   before, took under a minute with one ui job, on one machine on
   2026-11-02. Afterwards the worktree's build is the instrumented one,
   and `lake -R build` returns to the normal one, from the artifact
   cache.
