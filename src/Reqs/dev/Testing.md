# Testing

The test driver's rules are stated here as the module `testing`, and
`Impls.Testing` proves the driver's code meets them, for any jobs and any
messages: which jobs each shard runs ([Shards](#shards)), when a ui test
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
  fixed, with its issue, as `checks/simp_recursion_depth.fren` does for
  #417. `--~$` expects a message with no line, such as the Lean front end's
  error at the `#fren_check` that the test adds, and `--~?` allows a
  message without expecting it, for one that may be in one of several
  places, such as a conflict's
  note at whichever guarantee the solver's model picks. This is how
  `cli::agreement` is tested. See
  `src/FrenTest/Ui.lean` for the format, and
  [Expectations](#expectations) for when a file passes.
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
  fixtures that are deliberately unformatted or do not parse, and those
  listed in `fmtPending`: test fixtures that `fren fmt`'s move to rustfmt's
  layout would lay out anew. Their expected outputs and `--~` annotations
  name their lines, so formatting them means updating those too. They are
  formatted a group at a time, each only where the new layout reads better
  than the old, and `fmtPending` is then removed (#509). Run `fren fmt`
  on a spec after editing it. Formatting every spec must also keep its
  tokens, imports and comments, and be idempotent (`fmt::safe`), and each
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
  [--seed N] [--out DIR] [--avoid-known] [--guards] [--sites] [--spec-timeout SECONDS]`):
  generates random specs and checks each with both front ends, the `fren`
  command's pipeline and the Lean front end (in an environment that
  imports `Fren`, as the ui tests do), whose reports must agree
  (`cli::agreement`, `cli::agrees_with_build`): the same errors, warnings
  and notes at the same lines and columns, the same summary, and the exit status
  that Lean's messages call for: 2 after a static error, else 1 when Lean
  reports an error, 3 when it reports a warning, and 0 otherwise. The specs aim at the
  analyses that each front end implements on its own: constants, definitions
  of results and `let` variables, defined and uninterpreted functions, calls, `match`, tables,
  string methods and `++`, products, orderings and `min` and `max` of an ordered
  enumeration, a newtype of `Int` and its operators, an enumeration with
  payloads, whose outputs' variants clash notes may give, and sets and
  relations with `card`, so as to reach `linear_product`, the [decidable core](../Lang/Decidability.md)
  and the lints; and quantifiers whose [guards](../Lang/Quantifiers.md#guards) each
  front end reads on its own: over `Int`, `Nat`, a pattern type,
  newtypes over each, a newtype over a newtype, one that is not ordered,
  an ordered record, an ordered enumeration and `String`, read through
  their fields, with ranges with one or both bounds, chains, memberships
  in sets and sequences, and each comparison on either side. `--guards`
  generates those quantifiers alone, so that many specs run fast.
  `--sites` generates expressions that do not synthesize their types, at
  each kind of [site](../Lang/Types.md#checking-and-synthesis) where they
  are checked, and, at the end, one where they are not, an error that
  stops the spec's other checks, which the default generator therefore
  never writes. Only what may legitimately differ is not compared:
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
  overlapping seeds in one `DIR` overwrite each other's. `--avoid-known`
  steers clear of differences already known, to find others: the
  generator parenthesizes every method's receiver that is not a name, and
  a spec whose every difference is of a kind that the [front-end
  corpus](#front-end-corpus)'s `knownDifferences` lists is counted apart,
  as known, rather than as a finding. `compare` masks only what may
  legitimately differ, above; a known difference is fixed, or listed in
  `knownDifferences` with its issue, and not masked. The known column
  differences of #555 are of static
  errors that the generator does not write (an unknown method or field, a
  `refines`, an invalid string pattern, a higher-order call's arity), so
  `compare` masks no column. `--files FILE...` compares the front ends
  on given files, and `--print SEED` prints a generated spec. The
  comparison itself is tested in `FrenTest/FrontendsCompare.lean`.
- **Front-end corpus** (`lake test`): the front-end fuzzer's specs of a
  fixed set of seeds, from its generators, the default one, `--guards`
  and `--sites` (`corpus` in `src/FrenTest/FuzzFrontends.lean`), are checked
  with both front ends and compared as above, in `frontendFuzz` jobs of a
  few dozen seeds each. Every difference must be listed in
  `knownDifferences`, beside the corpus, by its generator, its seed and its
  kind (the difference without its line, names and values, as the
  fuzzer's summary gives it), with the issue that tracks it; and every
  listed one must still occur, so that the list only shrinks, as
  `knownColumnDifferences` does for the ui tests' columns. A spec whose
  front ends differ only in undecided checks, which time limits may
  explain, is left out both ways. A failure says how to reproduce the
  spec, and the entry that would list it. A change to the generator
  changes the spec of every seed, and so the corpus's differences: each
  one is then fixed or listed with its issue, as for any other change.
  The corpus is sized to take about 2 minutes of one CI machine. A crash
  of the solver fails its job, and a spec that never ends holds it up, as
  in any other job.

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

## Continuous integration

On a pull request, the `pre-merge` workflow checks the head merged into
`main`, starting from the `.lake` that `main`'s last build left: one
machine runs `lake build --wfail`, and others run `lake test --
--skip-own-mutants --shard K/N`, each building only the test driver. On
`main`, the `lean ci` workflow runs `lake build --wfail` and the whole
`lake test`, samples mutants of Fren's own requirements, measures the
coverage, and saves the `.lake` for pull requests. It also runs the
front-end fuzzer on seeds that no run used before, from the run's number,
with `--avoid-known`, of both generators: a difference of a kind that
`knownDifferences` does not list, a crash or a timeout fails the run, and
the specs it found are uploaded as the artifact `fuzz-frontends-RUN`, to
be filed (with the issue's number, in `knownDifferences` if the corpus
reaches the kind) or fixed. The `lint` workflow runs
`lun run --check` on both. The `pre-merge` workflow's last job, also named
`pre-merge`, passes only if its build and every shard passed: it is the
status that reviewers and the coordinator rely on.

On a pull request, `pre-merge` also uploads stripped copies of the
binaries that it built and tested, so that a reviewer can probe the head
without building it: `fren`, once the build has passed, as the artifact
`fren-SHA`, and `fren_test`, once shard 0 has built it, as
`fren_test-SHA`, where SHA is the full sha of the pull request's head.
They are kept for 3 days. They are Linux binaries, built on
`ubuntu-24.04`, which run on Linux machines such as sky but not on macOS.

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
/tmp/fren-SHA/fren check FILE
```

`fren` needs nothing else, for `fren check`, `quickcheck`, `mutate` and
`fmt`. `fren_test --job JOB` reads the test files and specs of the
checkout, and writes scratch files under its `.lake`. Its jobs `ui`,
`uiMisread`, `smtAgreement` and `leanTokens` load the hosted front end,
the `.olean` files of `Fren` and its dependencies; for them, run `heavy
lake build Fren` in the checkout, which compiles no C code and links
nothing, and then `lake env /tmp/fren_test-SHA/fren_test --job ui FILE`.
The other jobs, such as `snapshots`, `errorCodes` and `mutation`, need
only the binary. On CI, `fren` is 161 MB, 116 MB stripped and 45 MB
compressed, and `fren_test` is 320 MB, 235 MB stripped and 78 MB
compressed. The `.olean` files are not uploaded: those of `Fren` and its
dependencies came to some 340 MB, 96 MB compressed, on macOS.

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
fails if `fren check` compared no answers with it. Only that job uses the
cache, and the `queryCache` job tests the cache itself: the same output
cold, in a fresh directory, as warm, the same entries from two cold runs,
and a comparison that compares answers and finds no contradiction.

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
that changes an answer fails `main`'s run. It then saves its cache, which
is exactly the answers of that run: entries that no query asks any more
are dropped, so the cache does not grow. A run that found a contradiction
leaves a mark next to its cache and does not save it, so that `main` stays
red, comparing with the last good cache, until the key is fixed. Shard 0
of `pre-merge` restores the last saved cache and never saves one. With
most queries answered from it, Fren's own requirements took some 25% less
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

`fren_coverage` reads the counters with `GCOV`, without the library path
that `lake exe` sets to Lean's toolchain, whose LLVM libraries are not the
ones that `GCOV` is linked with. It stops with an error, and no report,
when it finds no counters, when `GCOV` fails on one module's, or when the
counters show that nothing ran: each means that the counters were not
read, and a report would list every declaration as never run.

A declaration ran if one of its entry points ran: its own function, or its
boxed or reduced-arity version, which callers may call instead. An
executable's `main` is emitted as `_lean_main`, and is `main`'s. A
specialization
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
