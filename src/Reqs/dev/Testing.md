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
  `cli::agreement` is tested. The Lean front end runs them with
  `fren.checkTypeCache`, under which each type that it takes from its
  cache of the types of terms (`typeOf`) is checked against the term's
  type elaborated again, an error where they differ: locally, in one
  run each, the ui tests of `test/ui/lang` took 61 s of CPU with it and
  57 s without. See `src/FrenTest/Ui.lean` for the format, and
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
  well-formed rule identifier, alone or followed by one space and the
  rule's links, and no two are the same (see [Writing the
  reference](Style.md#rule-identifiers)).
- **Rules and their requirements** (`lake test`, `ruleReqs`): each rule of
  **Legality rules**, **Dynamic semantics**, or (in a `dev/` chapter)
  **Rules** has a requirement or is listed in
  `test/unformalized_rules.txt`, with why where its chapter's
  section is not "(Interlock pending)", and a rule that is only partly
  formalized is listed too, saying what is missing once its chapter's
  section is done; the links on each rule's identifier line are well
  formed, name nothing twice nor what the rule's name links, and every
  item and clause that they name exists; no rule's prose names a
  requirement in parentheses; a block that
  formalizes a rule of its chapter follows it; each item of a module named as one of its
  chapter's constructs has a rule of its name, or, if it has clauses, each
  of them does, where the name is shaped as a rule identifier; and every
  rule that a test cites with `--@ reference: ID` exists
  (see [Writing the reference](Style.md#rules-and-requirements)). Only
  chapters under `src/Reqs/dev/` have rules under **Rules**. The
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
  `syntax/`, `lean/`, `misread/` and `ask_again/`. The example specs are
  in `examples/`, outside `test/`.
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
  whose library needs the tests, `ImplsTested`, make `tested` claims.
  The files named by those claims and the converse scan (`fren.testGlobs`)
  must be among that library's actual `needs`; an unreadable dependency
  declaration fails the check. Only the tests of `FrenTestFiles`, whose
  library needs the files that they read, read files with `#fren_md`, and
  they, and the files that they read, read only files that it needs.
  Also, the modules that copy a root module's imports, to keep it off the
  build's critical path, import exactly its modules.
- **Lean-only behaviour** (`lake build`): `#guard_msgs` tests in
  `src/FrenTest` and `src/FrenTestFiles`, e.g. the shape of generated
  definitions.
- **Fren's own requirements** (`lake test`, `ownSpec`): checked by the
  `fren` command; `lake build` only elaborates them, and Lean checks them
  on `main` (see [Own requirements](#own-requirements)).
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
- **Enumeration agrees with the solver** (`lake test`, `enumeration`):
  each ui test and example in the binary's corpus (excluding hosted-only
  files and files annotated with exit 2) runs with `Args.evidence?` forced
  to the solver, then forced to enumeration. The argument overrides the
  file's own settings, including scoped ones. A solver run with a static
  error is skipped, after checking for internal errors. Every recorded
  result must name the requested method, except functions, constants and
  subset-value definedness obligations, which must name the solver.
  Results are matched by item and every field of their check identity,
  in both directions. A missing counterpart fails, except a solver check
  that enumeration explicitly skips under `check::method_run`, or the
  enumerated checks of the particular procedure named by an unsupported
  enumeration diagnostic (`F0645`) or behaviour/quantifier cap diagnostic
  (`F0644`, the 65,536-value limit). A redundancy check may also be absent
  when its constraint's vacuity has no witness up to the bound, or the
  procedure reports no input/output up to the bound: `check::redundancy_asked`
  can skip it in the bounded search even when the solver runs it.
  In a run that reaches checking, solver-only checks may never be omitted
  and must keep their verdicts. The exact caller redundancy checks in
  `cover.fren` and `constants.fren` whose bounded calls make the comparison
  set empty are listed in `methodExceptions` with this semantic reason;
  an entry fails as stale once its counterpart appears.
  For the other matched results, a failure of enumeration is genuine, so
  the solver must not pass the check; a pass that is not bounded is a
  decision, so the solver must not fail it (see [Verdicts of
  enumeration](../Check.md#verdicts-of-enumeration)). Known contradictions
  are listed by file and exact check identity in `methodExceptions`, with
  their issue or semantic reason. Known adapter defects use exact
  diagnostic/check keys in the same registry. The seven internal errors,
  four wrong-method checks (under each affected method), and 74 missing
  enumeration counterparts tracked by #813 pass only while their exact
  entries occur. Diagnostic keys include the requested method, severity,
  code and headline; wrong-method keys include the requested and actual
  methods; missing counterparts name the complete check identity. Known
  entries are printed with their issue. Any applicable entry that
  disappears fails as stale and must be removed as #813's fixes land.
  Enumeration alone does not require an entry specific to random testing
  to occur. Unexpected new errors, wrong methods and missing identities
  still fail. At least 500 checks must be compared.
  Both runs retain their diagnostics and exit status. Internal errors and
  unexpected error diagnostics fail, even beside normal results, unless
  they match an exact known entry above. Nonzero
  exits fail unless explained: exit 1 by ordinary failed-check diagnostics
  or `F0644`/`F0645`, exit 3 by warnings, and the solver baseline's exit 2 by
  static-error diagnostics. Exit 2 under enumeration is expected only
  when every error is the exact `F0215` rejection of enumeration for a
  trait expectation and the stopped-checking header, and no results were
  recorded (`lang::trait_expectation_evidence`). That rejection stops all
  checks of the file, so it is reported and the file's comparisons are
  skipped. Every other enumeration exit 2 fails.
  Adapter regressions also inject missing counterparts, wrong recorded
  methods, internal errors and unexplained exits, and run a spec with
  conflicting source evidence settings under each forced method. The ui
  tests `checks/enumerated*.fren` and `checks/evidence_obligations.fren`
  cover enumeration in both front ends.
- **Methods agree** (`methodsAgree`, on `main`): Fren's own requirements,
  the same ui/example corpus as `enumeration`, and every seed of the
  front-end fuzzer's fixed corpus run with argument overrides for the
  solver, enumeration and random testing. Every record's method is
  validated as above, including records left to the solver, before each
  method's own records are selected. The union of those check identities
  is compared with `check::methods_agree`; inconclusive results and
  methods that did not run contribute no verdict. Missing checks are
  counted separately from inconclusive ones; this job does not require
  a counterpart for every check. It also checks that the exact documented
  missing-check cases in the shared registry still occur. The same exact
  `methodExceptions` apply
  and fail when stale. Comparison floors for each corpus part guard
  against a method silently ceasing to contribute.
  Diagnostics and exit statuses are retained and checked as for
  `enumeration`, with `F0639` accepted only under random testing and
  `F0644`/`F0645` only under enumeration. These expected unsupported-method
  diagnostics are reported with their corpus entry, method, code and
  headline; every other error must be an ordinary failed-check diagnostic
  or an exact known entry, or fail the job. The exact trait-expectation rejection (`F0215`) is
  accepted for either non-solver method, with the exit-2 conditions above;
  no checks of that run contribute, and its diagnostics are reported.
  An internal error fails unless it matches an exact known entry, including
  in the solver baseline of a spec with static errors. A solver baseline with ordinary static errors
  skips that spec; every other method-specific exit 2 fails.
  This job also runs the adapter regressions described above.
- **Solver lifetime** (`lake test`, `solverLifetime`): 500 queries in a
  row must not grow the test driver's memory by more than 100 MB, as they
  did by 1.5 MB each while no solver was freed (see [Solver
  queries](../Cli.md#solver-queries)); and sixteen threads that each ask
  300 queries in `ALL`, a logic with nonlinear arithmetic, and 100 in
  `QF_UFDTLIA`, a linear one, at once must get every answer right. The
  `ALL` ones crashed about one run in three while their solvers
  initialized and were freed at the same time; the linear ones take no
  lock (`FrenCli.Cvc5`). Half of the `ALL` ones initialize their solvers
  at a `push` before their definition, and let the lock go there. And
  each command that the lock is let go after must initialize a solver in
  cvc5, each must be tried, and the declarations and options before it
  must not initialize one. On Linux, a block that glibc allocates for
  itself must be mimalloc's, which `c/mimalloc_malloc.c` makes every
  executable's `malloc` (see [Architecture](Architecture.md)).
- **Solver statistics** (`lake test`, `solverStats`): `fren check
  --solver-stats` adds only its own lines to the output, and with it the
  output, the exit status and the answers and models of the query cache
  are those without it. With `--solver-stats=all` it lists every query it
  asked, with its item and check, and `--solver-stats=N` lists `N` of
  them. The report's counts and inferences show that cvc5's statistics
  were read. And a warm run, which asks nothing, reports none (see [Solver
  statistics](#solver-statistics)).
- **Confirmed models** (`lake test`): `fren check` confirms every model the
  solver returns with the evaluator (see
  [Evaluation and testing](../Eval.md#confirming-models)), so every test that
  runs the checks also checks the translation of its spec on the solver's
  models. A refuted model is an internal error, which fails the test.
  Both front ends also confirm each model that they report, at the values
  that their readers read (see [Reading models](../Models.md)). The ui tests in
  `test/ui/misread/` run with `FREN_MISREAD_MODELS` set, which makes both
  readers misread every integer, to check that the confirmation catches it.
  Those in `test/ui/ask_again/` run with `FREN_ASK_AGAIN` set, which makes
  both front ends ask every query that has a model again, as they ask one
  whose model is contradicted (see [Asking again](../Models.md#asking-again)).
- **The binary's shared reading** (`lake test`, `ownSpec`, which runs
  `sharedSpec` after its own check): only the `fren` binary reads the spec
  once, marks it and what else the threads read persistent, and shares it
  with every thread (`FrenCli.Args.persist`); the other jobs call `check`
  and `quickcheck` within the test driver, which gives each thread a
  reading of its own. So `sharedSpec` runs the binary's path, each run in
  a process of its own, since what it marks is never freed: `fren check`
  of Fren's own requirements, and `fren check` and `fren quickcheck` of ui
  tests that fail and leave checks undecided, at `--jobs 4`. Each must
  give the same output and exit status as the tests' path (see [Parallel
  checking](../Cli.md#parallel-checking)): for Fren's own requirements,
  `ownSpec`'s own run, at the default `--jobs`, and for the ui tests, a
  run at `--jobs 1`. Fren's own requirements are checked with a copy of
  `ownSpec`'s [query cache](#query-cache), if it has one, taken once that
  run has filled it, so that their queries are answered from it rather
  than solved under load, where one could reach its time limit; with no
  cache (`FREN_QUERY_CACHE` empty), they are checked with an empty one, so
  solved. So the shared path's own-spec run is not independent of the
  tests' path's solver answers: it answers from the cache that `ownSpec`'s
  run filled, and a wrong answer that the solver gave there would be given
  again. Only a difference in a query's script, which changes its key, is
  solved anew. Run alone (`--job sharedSpec`), the tests' path is a run at
  `--jobs 1` with a copy of the cache of its own, so it does not answer
  from the shared path's answers either; and the ui tests' runs keep no
  answers. A case whose outputs differ only where queries reached their
  time limit runs again once, and is skipped if it still differs so. Each
  differing decided diagnostic must match one timeout of the other run,
  at most once, by its full file, line and column and its check question:
  the same subject and kind, including any target, type, and row or arm
  numbers named in the message. Unrecognized or ambiguous results cannot
  match. A timeout may instead correspond to a silent passing check.
  Summary counts and explain hints are excused only when these timeouts
  explain every diagnostic difference; `lake test` shows each skip
  as a `skipped: …` line. Any other difference fails.
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
  [--confirm] [--obligations] [--scrutinees] [--inductions]
  [--induction-forms] [--keywords] [--fact-scopes] [--induction-candidates]
  [--decidable] [--spec-timeout SECONDS]`): generates random
  specs and checks each with both front ends, the `fren` command's pipeline
  and the Lean front end (in an environment that imports `Fren`, as the ui
  tests do), whose reports must agree (`cli::agreement`, `cli::agrees_with_build`): the
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
  differs: one refutes the model, and the other shows it. `--scrutinees`
  generates repeated and distinct columns of matches and tables, through
  calls, fields, definitions and nested expressions, including generic
  types and lambda matches. It has its own mode to preserve the older
  generators' seeds and keep earlier static errors from stopping these
  checks. Its corpus rejects generated static errors. `--keywords`
  generates one block, a procedure's, a function's, a trait method's or a
  global expectation's, with a clause written with the other block's
  keyword among parts that the block rejects or that are errors of their
  own syntax, so that both front ends must report the same first error of
  the block ([The keyword of an
  assumption](../Lang/Procedures.md#the-keyword-of-an-assumption)), now and
  then after an item of each kind that holds clauses with such a clause in
  one of its members, and with an error of Lean's grammar later in the
  item, which both must report instead, and often followed by an item with messages of its own,
  which an error of a clause's keyword must leave to be reported. Its
  errors are on purpose, and an error stops every other check of a spec,
  so `lake test`'s corpus leaves the mode out. `--fact-scopes`
  generates separate queries with disjoint contract chains, over scalar,
  collection and compound result types, with applications under binders
  and through definitions, and a cover goal that mentions none of them.
  The mode compares the front ends' reports on these queries;
  `test/ui/checks/fact_scope.fren` pins the expected verdicts and witness.
  `--induction-candidates` generates companion parameter types, nested
  restrictions, decreasing-argument positions, shadowing, derived arguments,
  assumptions and comparisons of recursive applications. Its generator is
  split off the seed, so its draws leave the other modes unchanged. Like
  `--scrutinees`, it has an empty cut: its corpus rejects generated static
  errors, which would stop the spec's checks.
  `--decidable` moves
  the former conformance generator here: each spec has random procedures
  in the decidable core of strings, sets, relations and sequences, with no
  opt-outs. Its own mode leaves all older seeds' specs unchanged, and a few
  of its seeds are in the corpus, which rejects internal errors even when
  both front ends agree. An unknown answer without reaching a time or
  resource limit is an internal error (`check::decidable_unknown`). After
  those procedures it appends an output-invariant case
  (`Wide.outputInvariantCore`): an opaque recursion in an invariant, through
  a generic definition, `let` or a helper's `where` clause, over integers,
  naturals, Booleans, enumerations, records, newtypes and abstract types,
  directly or through an alias; concrete carriers also nest in data. A
  generic recursion covers an abstract carrier. Defined outputs also cover
  strings, sets, relations, sequences and recursive enumerations.
  Definitions that ignore parameters check that only the arguments left
  after unfolding count. These exercise the rule for generated queries
  (`check::output_query_core`) without changing any older random draw or
  adding a static error. A run with
  `--obligations` also compares the front ends' [obligations
  dumps](../Cli.md#obligations), but for their metadata, from runs with
  the dump on, whose messages it then compares. It is off by default, so
  that a run compares the messages of what users run, which is what CI
  runs. It writes the dumps of each spec where they differ
  to `DIR` as `obligations-seed*`, counted in its summary, both all of them
  and those that differ other than in the names of their constants: an
  early signal, which fails nothing yet. Only what may
  legitimately differ is not compared:
  - A parse error stops the `fren` command, while Lean recovers at the
    next command: Lean must then report a parse error in the same item, on
    the parse error's line, or on the last line before it that is not blank
    or a comment, since Lean places a parse error at the end of the token
    before the offending one, and nothing else is compared. An
    item is one Lean command, so any other error of Lean's in it means
    that Lean parsed what the `fren` command rejects. `F0169` is not
    among these parse errors: both front ends report it once the item is
    read, for that item alone ([`lang::item_error`](../Lang/Procedures.md#the-keyword-of-an-assumption)),
    so what follows it is compared. Lean's parse errors
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
  `--sites`, `--confirm`, `--scrutinees`, `--inductions`, `--induction-forms`,
  `--fact-scopes`, `--induction-candidates` and `--datatype-elements`
  (`corpus` in `src/FrenTest/FuzzFrontends.lean`), are checked
  with both front ends and compared as above, in `frontendFuzz` jobs of at
  most five specs each, including those listed outside the ranges. Each
  job imports `Fren` once; small batches spread the work over the shards
  and keep a large batch from outlasting their other jobs. The flattened
  jobs must keep the corpus's modes and seeds in order, exactly once,
  which `#guard`s beside `corpusJobs` check. Every difference must be
  listed in `knownDifferences`, beside the corpus, by its generator, its
  seed and the difference itself, line, column and names included, with
  the issue that tracks it; each entry stands for one occurrence, so a
  difference that occurs more often than it is listed fails too; and every
  listed one must still occur, so that the list only shrinks, as
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
    require shards: n >= 1
    require position: 0 <= i < jobs.len

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
    require times: first <= start <= stop

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
needs changed since its last build, which Fren trusts.

**Rules**

r[lake.reader-inputs]
The `libraries` job rejects a reader in `Reqs`, `ImplsTested`, or
`FrenTestFiles` if a file it reads through `#fren_md`, `tested`, or the
converse scan (`fren.testGlobs`) is outside its owning library's actual
`needs`, or if a dependency declaration cannot be read.

The job checks the real sources and resolves library ownership and input
paths and filters from `lakefile.lean`. This rule has no formal Req
binding; its regressions exercise the concrete check. The abstract
`testing::fresh` states how the subset gives freshness: whenever the
files read are among those needed, the result is fresh.

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
    require lake: when needs inter changed != {}, rebuilt?
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
the slots. The settings are read again while jobs wait or run, so changing
a file takes effect without a restart:

- **Slots:** `HEAVY_SLOTS`, else the number in `~/.cache/heavy/slots`,
  else 2.
- **Memory:** `HEAVY_MEM_GB` gigabytes, else the number in
  `~/.cache/heavy/mem_gb`, else 80% of the machine's physical memory,
  summed over each job's process group. A job waits to start while the
  running ones use more than 60% of the cap; when they use more than
  the cap, heavy kills the newest compatible owner and exits with 137.
- **Load (off by default):** `HEAVY_MAX_LOAD`, else the number in
  `~/.cache/heavy/max_load`. A waiting job also needs the 1-minute load
  to be below this value. After 10 minutes waiting it may start whatever
  the load, since the load includes unrelated work and decays slowly;
  it still needs a slot and memory. An unavailable load reading lets it
  start too. `HEAVY_MAX_LOAD=off` disables even a value in the file.

A setting that is set but is not a positive finite number is ignored,
with a warning.

Slot locks, not numeric PIDs, determine whether jobs are live. Each owner
has a unique `job_id` and a sequence number allocated under `registry.lock`.
It atomically publishes its own process-group RSS about every second in
`.slotN.json` while holding `slotN`; admission sums these reports across
namespaces. Acquisition and release also hold the registry lock, so a new
compatible holder cannot inherit the previous holder's report. Slot files themselves
are never replaced or removed while in use. A report without a held lock
is ignored, including after a crash or PID reuse. An empty slot status
file does not mean its lock is unheld.

Each new holder writes its `job_id` at the end of the slot status as
`[heavy-job=...]`; the leading PID and timestamp remain readable by legacy
copies. A report must match that token. On Linux, ownership verification
requires a matching kernel lock entry and a readable monitor identity.
Its PID namespace, local PID and process start counter must match the
report's monitor identity. These are read through the
kernel's PID in this procfs view, never through a PID from slot text.
Without a visible owner, a matching token is accepted only for fresh reports;
after ten seconds an unverified stale report is treated as legacy. Missing,
malformed and mismatched reports are legacy too. Thus a legacy holder that
reuses a crashed owner's status cannot reserve the entire cap indefinitely.

Every registry acquisition uses nonblocking attempts with a 0.2-second
monotonic deadline. A timeout blocks admission and skips shared accounting
for that monitor tick; local RSS measurement and the job's own cap still
apply. Release also has this deadline: on timeout it closes the slot and
leaves inactive metadata. Once it holds the registry lock, it closes the
slot before releasing it, even if cleanup fails. Termination signals are
unblocked only after the registry lock is released, so child cleanup cannot
hold up the registry. A stopped holder can prevent shared accounting from
progressing, but cannot make another monitor wait indefinitely on the lock.

Reports include the owner's `/proc/self/ns/pid` identity and label numeric
PIDs as namespace-local diagnostics. No other owner resolves or signals
those PIDs. Newest means the greatest sequence number, not the greatest
PID or wall-clock timestamp. Each owner checks the combined total and only
the selected owner terminates its own command for the combined cap. Every
owner also terminates its own command if its local RSS exceeds the cap, even
when another owner is selected or stopped. Local signaling first reaps the
leader nonblocking, then probes the local group with `killpg(PGID, 0)`:
a reaped leader alone does not mean the workers are gone. TERM-to-KILL
escalation continues while the group exists. SIGINT, SIGTERM and SIGHUP are
blocked around the completion check and signal, and while the registry lock
is held; handlers are restored after monitoring.
When heavy is PID 1 of its namespace, it also reaps adopted orphan workers
after collecting the leader's exit status and RSS. Dead workers must not
keep the process group visible as zombies until both escalation waits expire.

If `/proc` belongs to an ancestor PID namespace, the owner translates its
own child through parentage and `NSpid` before measuring it in that procfs
view. Linux requires `NSpid` in `/proc/self/status` for every job, and in
candidate status files when translating from ancestor procfs. Kernels and
procfs emulations without these entries are unsupported. This covers both
`unshare --pid --fork` with an inherited `/proc` and jobs with a remounted
`/proc`, such as bwrap jobs. If it cannot identify its own group, or cannot
measure or publish its memory for a reason other than the bounded registry
timeout above, it stops its own command and exits with 125 rather than
applying a foreign numeric PID.
Job records identify this protocol as `memory_accounting` =
`"slot_owner_reports_v3"`, alongside `job_id`, `admission_order` and `pid_namespace`.

Reports use protocol version 3 and `updated_monotonic`, sampled from
`time.monotonic()` in a shared time namespace. PID namespaces do not
change that clock. Wall-clock corrections do not affect freshness, and
Linux's monotonic clock excludes suspended time, so resume does not age
all reports by the suspension's duration. Reports use a common clock;
time namespaces with different monotonic offsets are outside this protocol.

Admission and eviction have different totals. Admission counts a fresh
compatible report's RSS. A verified current owner with stale or future-dated
data reserves one full cap. A legacy holder with verified visible RSS
contributes that reading. All unobserved legacy holders together reserve
`ceil(cap / 2)`, at least 1 KB, once for the entire set. This shared forecast
leaves admission room even when several legacy holders occupy the other
slots. It is not a claim that an unknown holder uses zero. Charging a full
cap for every unknown holder made coexistence impossible even when a slot
and substantial memory were free.
With a free slot, new work starts whenever the sum of these charges is at
most 60% of the cap. Legacy holders therefore do not require a coordinated
drain before a new version can admit work. A memory wait names each reserving
slot and its stale-report charge or legacy estimate.
Those details appear only when the memory threshold blocks admission;
a load-only wait does not recommend freeing memory. A registry deadline
reports a registry wait, including races at slot acquisition and recheck.

On Linux 4.9 and later, legacy measurements discover the current flock
holder by device and inode in
[`/proc/locks`](https://man7.org/linux/man-pages/man5/proc_locks.5.html),
then sum its direct child process groups in that same procfs view. The scan
rechecks the lock owner and its process start counter. It runs outside the
registry lock. Filtered, inaccessible or changed ownership leaves the
reading unknown and uses the forecast. A numeric PID in a legacy slot is
never resolved, so an unrelated process with that number cannot inflate it.
Older kernels and other systems use the fixed forecast.
Kernel verification also requires the slot's `stat` device and inode to
match the identifiers in `/proc/locks`. On filesystems where the device
identifiers differ, including btrfs subvolumes and some stacked filesystems,
the owner cannot be matched. Compatible reports then use the freshness
fallback, an unverified stale report becomes legacy after ten seconds, and
legacy RSS remains unobserved. In that case the lookup cannot verify stopped
owners or measure legacy holders; accounting uses freshness and the shared
forecast instead. The current implementation does not translate filesystem
device identifiers.

Eviction counts compatible owners' last reported RSS and verified legacy
measurements. Forecasts never contribute to this total. When it exceeds the
cap, only the greatest compatible admission sequence is selected; legacy
holders are never signal targets. A partially unknown set of leases does
not suppress eviction when its known measurements alone exceed the cap.
Running monitors also enforce their own cap. Old versions keep their own
admission and eviction rules, so global newest-first ordering applies only
among compatible owners.

Legacy forecasts can underestimate invisible memory. Mixed-version
accounting cannot guarantee a hard combined memory limit; a shared kernel
limit is needed for that. A stale reading can also underestimate current
use. This policy keeps visible measurements and forecasts separate while
allowing deployment across worktrees on different bases.
Cleanup can leave metadata behind after a write error; unlocking still
makes that report inactive. Accounting is sampled, not a kernel memory
cgroup limit. A stopped monitor cannot publish new RSS, but its last reading
never becomes a whole-cap eviction charge merely because it stops reporting.

`scripts/heavy_test.py` runs in the `lint` workflow, not in `lake test`.
It checks lease accounting, bounded registry waits and local termination, and
runs the cross-namespace cap integration with inherited and remounted
procfs where unprivileged PID namespaces are supported. If the kernel or
container refuses `unshare`, that integration prints a skip; portable
lease and translation tests still run. `HEAVY_REQUIRE_PIDNS_TEST=1` makes
lack of PID-namespace support a failure. Hosted CI may skip this integration,
so its result alone does not establish cross-namespace coverage.

Each completed job appends one JSON line to `~/.cache/heavy/log.jsonl`,
or `HEAVY_LOG` if set. It records the shortened command, worktree,
enqueue, start and end times (Unix seconds), monotonic wait and run
durations, exit status, peak RSS in KB, and the 1-minute load at start
and about every 30 seconds, with its mean and maximum. Peak RSS is the
larger of the process group's sampled sum and the kernel's high-water
mark for the child and its waited-for descendants; a short overlap of
workers between samples can be missed. A log failure never fails the
job. Each job also records its admission policy: the `max_load` value
or `"off"`, and the slot count, rechecked after acquiring its slot. Its
admission timestamp and policy are recorded together before execution;
later flips cannot reassign the job. It also records `enqueued_max_load`,
`enqueued_slots` and `wait_policy_changed` to diagnose a change observed
while waiting. Enqueue settings never decide the job's accounting label. Its
job kind is computed from the full command before shortening it, removing
paths, seeds and numbers while retaining executable and script basenames,
flags and job names. Tests use scratch directories, including for logs.
A missing bare command exits with 127 before waiting or taking a slot;
it has no admission and produces no job record.

The following requirements compute compatibility, admission and eviction
from raw held-slot observations: a report, its status token, the observed
monitor identity and any independently measured legacy RSS. `MemoryLeases`
does not classify its entries in advance. `heavy_lease` calls
`heavy_report_owner`; the recursive accounting functions use the same
`report_owner?` definition, so victim selection and owned signaling also
decide compatibility. A legacy job can admit new work only when a slot is
free and the memory rule holds. Time values use one integral unit of the
shared monotonic clock. Python tests check the concrete lock, clock, procfs and
signal operations through `tested` claims in `Impls.Trace`; these tests run
in the `lint` workflow, not in `lake test`. `heavy_registry` models the retry
and signal-deferral decisions, including refusal to retry after the deadline.
These are per-attempt rules: the supplied deadline does not model its
allocation once per acquisition, nor a finite sequence of retries. The Req
cannot reject a deadline recomputed on every retry or a blocking flock.
The stopped-lock-holder subprocess test checks concrete bounded progress;
no Req here proves that Python uses nonblocking flock or that the OS schedules
a monitor. Elaborating each `tested` claim reads its named file and requires
a matching `fren-covers` marker. `fren.testGlobs` controls the separate
converse scan for markers without matching claims; its current patterns
omit `scripts/`.
The lease and victim requirements alone take lock state and reports as inputs,
so they cannot detect an unbounded wait before those inputs are read.

```fren
pub proc heavy_registry(available?, now: Int, deadline: Int, held?, requested?): (
    det acquired?,
    det retry?,
    det timed_out?,
    det deferred?,
) {
    ensure acquired: acquired? iff available?
    ensure retry: retry? iff not available? and now < deadline
    ensure timeout: timed_out? iff not available? and now >= deadline
    ensure defer_signal: deferred? iff held? and requested?
    expect bounded: when now >= deadline, not retry?
    expect stopped: unless available?, not acquired? and (retry? or timed_out?)
    expect masked: when held? and requested?, deferred?
}

pub proc heavy_wait_message(rss: Nat, cap: Nat, reservations: Seq<String>, registry_busy?): (
    det memory_details?,
    det registry_message?,
) {
    ensure memory: memory_details? iff not registry_busy? and 5 * rss > 3 * cap and reservations != []
    ensure registry: registry_message? iff registry_busy?
    expect load_only: when 5 * rss <= 3 * cap, not memory_details?
    expect registry_priority: when registry_busy?, registry_message? and not memory_details?
}

pub struct MemoryOwner { job: String, sequence: Int }
pub struct MonitorIdentity { pid: Int, start: Int, space: String }

pub struct MemoryReport {
    owner: MemoryOwner,
    rss: Int,
    updated: Int,
    monitor: Option<MonitorIdentity>,
}

-- Raw observations of a held slot, before compatibility is decided.
pub struct MemoryLease {
    report: Option<MemoryReport>,
    status_job: String,
    observed: Option<MonitorIdentity>,
    legacy_rss: Option<Int>,
}

pub const UNKNOWN_LEASE: MemoryLease := MemoryLease {
    report := Option::None,
    status_job := "",
    observed := Option::None,
    legacy_rss := Option::None,
}

pub enum MemoryLeases {
    Nil,
    Cons(MemoryLease, MemoryLeases),
}

pub fn legacy_reservation(cap: Nat, observed: Option<Int>): Int := match observed {
    Option::Some(rss) => if rss >= 0 then rss else ((cap + 1) div 2).max(1),
    Option::None => ((cap + 1) div 2).max(1),
}

pub fn legacy_memory(observed: Option<Int>): Int := match observed {
    Option::Some(rss) => rss.max(0),
    Option::None => 0,
}

pub proc heavy_legacy_lease(cap: Nat, free?, locked?, observed: Option<Int>, other: Nat): (
    det live?,
    det admission: Int,
    det eviction: Int,
    det fits?,
) {
    ensure live: live? iff locked?
    out admission := if locked? then legacy_reservation(cap, observed) else 0
    out eviction := if locked? then legacy_memory(observed) else 0
    ensure memory_rule: fits? iff free? and 5 * (admission + other) <= 3 * cap
    expect coexists: when cap >= 5 and free? and observed = Option::None and other = 0, fits?
    expect full: unless free?, not fits?
    expect measured: match observed {
        Option::Some(rss) => (when locked? and rss >= 0, admission >= rss and eviction = rss),
        Option::None => eviction = 0,
    }
    expect high_memory: when locked? and 5 * eviction > 3 * cap, not fits?
    expect unlocked: unless locked?, admission = 0 and eviction = 0
}

pub fn valid_report?(r: MemoryReport) := r.rss >= 0 and r.owner.sequence > 0

pub fn fresh_report?(r: MemoryReport, now: Int, ttl: Nat) := 0 <= now - r.updated <= ttl

pub fn report_owner?(
    report: Option<MemoryReport>,
    status_job: String,
    observed: Option<MonitorIdentity>,
    now: Int,
    ttl: Nat
) := match report {
    Option::Some(r) =>
        valid_report?(r) and status_job = r.owner.job and (match observed {
            Option::Some(m) => r.monitor = Option::Some(m),
            Option::None => fresh_report?(r, now, ttl),
        }),
    Option::None => false,
}

pub proc heavy_report_owner(
    report: Option<MemoryReport>,
    status_job: String,
    observed: Option<MonitorIdentity>,
    now: Int,
    ttl: Nat,
): (det compatible?) {
    out compatible? := report_owner?(report, status_job, observed, now, ttl)
    expect replaced: match report, observed {
        Option::Some(r), Option::Some(m) => (when r.monitor != Option::Some(m), not compatible?),
        Option::Some(r), Option::None => (unless fresh_report?(r, now, ttl), not compatible?),
        _, _ => not compatible?,
    }
    expect token: match report {
        Option::Some(r) => (when status_job != r.owner.job, not compatible?),
        Option::None => not compatible?,
    }
}

pub fn admission_memory(cap: Nat, report: Option<MemoryReport>, now: Int, ttl: Nat): Int :=
    match report {
        Option::Some(r) =>
            if valid_report?(r) then (if fresh_report?(r, now, ttl) then r.rss else cap)
            else legacy_reservation(cap, Option::None),
        Option::None => legacy_reservation(cap, Option::None),
    }

pub fn eviction_memory(report: Option<MemoryReport>): Int := match report {
    Option::Some(r) => if valid_report?(r) then r.rss else 0,
    Option::None => 0,
}

pub proc heavy_lease(cap: Nat, locked?, lease: MemoryLease, now: Int, ttl: Nat): (
    det live?,
    det admission: Int,
    det eviction: Int,
) {
    call owner := heavy_report_owner(lease.report, lease.status_job, lease.observed, now, ttl)
    ensure live: live? iff locked?
    out admission :=
        if not locked? then 0
        else if owner.compatible? then admission_memory(cap, lease.report, now, ttl)
        else legacy_reservation(cap, lease.legacy_rss)
    out eviction :=
        if not locked? then 0
        else if owner.compatible? then eviction_memory(lease.report)
        else legacy_memory(lease.legacy_rss)
    expect unlocked: unless locked?, admission = 0 and eviction = 0
    expect unknown: when locked? and lease.report = Option::None and lease.legacy_rss = Option::None,
        admission > 0 and eviction = 0
    expect stale: match lease.report, lease.observed {
        Option::Some(r), Option::Some(m) => (when locked? and valid_report?(r)
            and lease.status_job = r.owner.job and r.monitor = Option::Some(m)
            and not fresh_report?(r, now, ttl),
            admission = cap and eviction = r.rss),
        _, _ => true,
    }
    expect unverified_stale: match lease.report {
        Option::Some(r) => (when locked? and lease.observed = Option::None and not fresh_report?(r, now, ttl),
            admission = legacy_reservation(cap, lease.legacy_rss) and eviction = legacy_memory(lease.legacy_rss)),
        Option::None => true,
    }
    expect wrong_token: match lease.report {
        Option::Some(r) => (when locked? and lease.status_job != r.owner.job,
            admission = legacy_reservation(cap, lease.legacy_rss) and eviction = legacy_memory(lease.legacy_rss)),
        Option::None => true,
    }
}

pub fn observed_admission(cap: Nat, leases: MemoryLeases, now: Int, ttl: Nat): (rss: Int) {
    out rss := match leases {
        MemoryLeases::Nil => 0,
        MemoryLeases::Cons(lease, rest) =>
            (if report_owner?(lease.report, lease.status_job, lease.observed, now, ttl)
                then admission_memory(cap, lease.report, now, ttl) else legacy_memory(lease.legacy_rss))
            + observed_admission(cap, rest, now, ttl),
    }
    ensure empty: when leases = MemoryLeases::Nil, rss = 0
    ensure single_legacy: match leases {
        MemoryLeases::Cons(lease, MemoryLeases::Nil) => (unless report_owner?(
            lease.report,
            lease.status_job,
            lease.observed,
            now,
            ttl
        ),
            rss = legacy_memory(lease.legacy_rss)),
        _ => true,
    }
}

pub fn unknown_legacy?(leases: MemoryLeases, now: Int, ttl: Nat) := match leases {
    MemoryLeases::Nil => false,
    MemoryLeases::Cons(lease, rest) =>
        (not report_owner?(lease.report, lease.status_job, lease.observed, now, ttl) and (match lease.legacy_rss {
            Option::Some(rss) => rss < 0,
            Option::None => true,
        })) or unknown_legacy?(rest, now, ttl),
}

pub fn admission_total(cap: Nat, leases: MemoryLeases, now: Int, ttl: Nat): Int :=
    observed_admission(cap, leases, now, ttl)
    + (if unknown_legacy?(leases, now, ttl) then legacy_reservation(cap, Option::None) else 0)

pub fn eviction_total(leases: MemoryLeases, now: Int, ttl: Nat): (rss: Int) {
    out rss := match leases {
        MemoryLeases::Nil => 0,
        MemoryLeases::Cons(lease, rest) =>
            (if report_owner?(lease.report, lease.status_job, lease.observed, now, ttl)
                then eviction_memory(lease.report) else legacy_memory(lease.legacy_rss))
            + eviction_total(rest, now, ttl),
    }
    ensure empty: when leases = MemoryLeases::Nil, rss = 0
    ensure single_legacy: match leases {
        MemoryLeases::Cons(lease, MemoryLeases::Nil) => (unless report_owner?(
            lease.report,
            lease.status_job,
            lease.observed,
            now,
            ttl
        ),
            rss = legacy_memory(lease.legacy_rss)),
        _ => true,
    }
}

pub fn newest_owner(first: Option<MemoryOwner>, second: Option<MemoryOwner>): Option<MemoryOwner> :=
    match first, second {
        Option::None, _ => second,
        _, Option::None => first,
        Option::Some(a), Option::Some(b) => if b.sequence > a.sequence then second else first,
    }

pub fn latest_owner(leases: MemoryLeases, now: Int, ttl: Nat): (owner: Option<MemoryOwner>) {
    out owner := match leases {
        MemoryLeases::Nil => Option::None,
        MemoryLeases::Cons(lease, rest) => newest_owner(
            match lease.report {
                Option::Some(r) =>
                    if report_owner?(lease.report, lease.status_job, lease.observed, now, ttl)
                    then Option::Some(r.owner) else Option::None,
                Option::None => Option::None,
            },
            latest_owner(rest, now, ttl)
        ),
    }
    ensure empty: when leases = MemoryLeases::Nil, owner = Option::None
}

pub proc heavy_memory_victim(cap: Nat, leases: MemoryLeases, now: Int, ttl: Nat): (
    det admission: Int,
    det total: Int,
    det selected: Option<MemoryOwner>,
) {
    out admission := admission_total(cap, leases, now, ttl)
    out total := eviction_total(leases, now, ttl)
    out selected := if total > cap then latest_owner(leases, now, ttl) else Option::None
    expect within_cap: when total <= cap, selected = Option::None
    expect legacy: when latest_owner(leases, now, ttl) = Option::None, selected = Option::None
    expect estimates_only: match leases {
        MemoryLeases::Cons(lease, MemoryLeases::Nil) => (when lease.report = Option::None and lease.legacy_rss = Option::None,
            selected = Option::None and total = 0),
        _ => true,
    }
    expect shared_forecast: when leases = MemoryLeases::Cons(
        UNKNOWN_LEASE,
        MemoryLeases::Cons(UNKNOWN_LEASE, MemoryLeases::Nil)
    ),
        admission = legacy_reservation(cap, Option::None) and total = 0
    expect stale_fits: match leases {
        MemoryLeases::Cons(lease, rest) => match lease.report {
            Option::Some(r) => (when report_owner?(
                lease.report,
                lease.status_job,
                lease.observed,
                now,
                ttl
            )
                and not fresh_report?(r, now, ttl) and r.rss + eviction_total(rest, now, ttl) <= cap,
                selected = Option::None),
            Option::None => true,
        },
        _ => true,
    }
}

pub proc heavy_group_gone(leader_reaped?, group_exists?): (det gone?) {
    ensure rule: gone? iff leader_reaped? and not group_exists?
    expect worker: when group_exists?, not gone?
    expect leader_running: unless leader_reaped?, not gone?
}

pub proc heavy_owned_signal(
    own: String,
    leases: MemoryLeases,
    cap: Nat,
    own_rss: Nat,
    now: Int,
    ttl: Nat,
    requested?,
    leader_reaped?,
    group_exists?,
): (det signal?) {
    call eviction := heavy_memory_victim(cap, leases, now, ttl)
    call termination := heavy_group_gone(leader_reaped?, group_exists?)
    let memory_requested? := match eviction.selected {
        Option::Some(owner) => owner.job = own or own_rss > cap,
        Option::None => own_rss > cap,
    }
    ensure rule: signal? iff (requested? or memory_requested?) and not termination.gone?
    expect own_cap: when own_rss > cap and not termination.gone?, signal?
    expect completed: when termination.gone?, not signal?
    expect escalation: when requested? and group_exists?, signal?
}
```

The log has no automatic size limit or rotation, and `--stats` reads it
all, including the load samples of long jobs. Keep the raw log for the
trial. Archive it between trials while the controller and heavy jobs
are stopped; preserve the flip records with their jobs so that exposure
can still be measured. Automatic retention remains future work.

`scripts/heavy --stats [HOURS]` compares completions in the last HOURS
(default 24), grouped by admission policy and slot count: jobs per hour,
wait, run and total latency percentiles, and mean sampled load. It divides
each policy's `rate_jobs` by that policy's active hours in the window,
including idle time, from the flip records below. Only completions whose
admission falls in a matching logged policy interval within the window
count toward `rate_jobs`. Jobs admitted before the first flip, outside
the window or under a different policy do not inflate that rate.
Without flip records its policy rate is `null`, rather than an estimate
from first and last jobs.
A completion stays attributed to its admission policy if a flip happened
while it ran. For policy comparisons, waits that span an observed change
of load threshold or slot count are excluded from wait and total-latency
percentiles and from `rate_jobs`. Records without enough information about
the wait are excluded too. `wait_jobs` counts the jobs used for these percentiles;
`excluded_waits` reports the other jobs with their admission and enqueue
policies, timestamps, durations and reason. This keeps a backlog released
by a flip from inflating the new policy's comparison waits or completion rate.
Failed jobs are counted separately. Samples from overlapping
jobs both count toward mean load. Malformed and incomplete lines are skipped.
At the top level, `hours` is the requested window, while `observed_hours`
is the total logged exposure across policies. Its `rate_jobs` is the sum
of the policy numerators, and its `jobs_per_hour` divides that sum by
the total exposure, using the same admission rule as the policy entries.
With no logged exposure the rate is `null`. Raw counts and run times retain
the admission policy; these and the top-level wait and latency summaries
include every completion in the requested window.

`by_kind` compares successful run-time percentiles within each job kind.
For each load threshold it also reports the ratio of its median run time
to off's median for each kind with the same slot count. The aggregate
`normalized_run_ratio_vs_off` is the geometric mean of these ratios,
giving every kind observed under both policies equal weight. A value
below 1 means faster runs with load admission. It reports the number of
matched kinds and excludes kinds missing from either policy and failed
runs. This controls for different frequencies of job kinds; differences
in the amount of work within a kind can still affect the comparison.

`scripts/heavy --alternate MINUTES VALUE` runs one controller for all
agents on the machine. It immediately writes VALUE to `max_load`, then
removes the file after MINUTES, repeating on and off until stopped. The
writes are atomic and every flip appends a policy record with its time
and slot count. A lock prevents a second controller. SIGINT, SIGTERM or SIGHUP
removes the file and logs off before exiting, unless inherited as ignored.
In particular, SIGHUP remains ignored under `nohup`. Further signals cannot
interrupt cleanup, and inherited handlers are restored afterwards. An abrupt
kill can leave the last setting in place. Run it directly, without holding
a heavy slot.
Unset `HEAVY_MAX_LOAD` on every agent so that all use the shared file;
use the same slot count and memory limit on every agent and keep them
constant throughout the trial.

The load policy stays off by default until a field A/B on this machine
shows better development throughput. To judge the setting, run
`scripts/heavy --alternate 60 8` for about a day of alternating hourly
blocks across all agents, then compare the real log with
`scripts/heavy --stats 24`: jobs per active policy hour, mean load,
wait and run time percentiles, and the comparisons by job kind. Inspect
failures, sparse kinds and jobs crossing block or trial boundaries when
judging the result; lower load alone does not show better throughput.

`scripts/heavy --offline COMMAND` runs COMMAND with no network. On Linux
it runs in a new user and network namespace (`unshare -rn`, which needs
unprivileged user namespaces), whose loopback is down, as uid 0 mapped
to the user. On macOS it runs under `sandbox-exec` with a profile that
denies IP networking, loopback included, and name lookups. Where it cannot cut the network, it
fails rather than run COMMAND online. Use it to run binaries that a pull
request built, the fuzzers and mutation runs, which never need the
network. Builds and `lake test` stay online: Lake fetches packages and
elan fetches toolchains. `python3 scripts/heavy_test.py` tests its
argument parsing, overrides, admission with injected load, job logs,
policy comparisons and flips without sleeping, and
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
`main`, starting from the `.lake` that `main`'s last build left: two
machines run `lake build --wfail`, and others run `lake test --
--skip-own-mutants --shard K/N`, each building only the test driver. One
build machine builds Fren's own requirements and their `impl`s (`lake
build --wfail Reqs Impls`), the other the rest of the default targets:
the code, the tests, the examples and the binaries, among them the C code
that the first needs none of. The build's critical path runs from
`Fren.Elab` through the chapter modules from `Reqs.Lang.Base` to
`Reqs.Lang.ScopeLaws`, then `Reqs.Lang`, `Reqs.Lint` and `Impls.Lint`.
Before the chapters were split,
on one machine the chain's modules shared the runner's four logical CPUs
with the rest: where everything was rebuilt, the build's steps took some
2,400 CPU seconds, so that the chain's ran at about half speed. On
2026-11-02, in three runs of one commit, which rebuilt from `FrenCore`
up, with the old single build job beside the two, the single build took
729, 705 and 679 s, the build of the requirements 361, 443 and 316 s,
and that of the rest 321, 392 and 297 s; so the build no longer outlasts
the test shards. Both build what both import, from `FrenCore` to `Fren`, and
`lake test`'s `libraries` job checks that the two lists of targets
together are `lakefile.lean`'s default targets. On
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
does not have runs, and reports its messages.

Before it saves the `.lake`, `main`'s build job also builds the test
driver, as `lake test` does. Of the C code of `Fren` and `FrenTest`, the
default targets link only `Fren.Seq`'s (through `fren`), so without it
the `.lake` had the object files of none of their other modules, and each
test shard of each pull request compiled them all again: on 2026-11-03,
on a runner, `lake build fren_test` from `main`'s `.lake` took 71 and 74
s where nothing had changed, and 0 and 1 s once the objects were
there. Lake recompiles a module's C code only if the code differs, and
`lean` writes the same C code for the same module: after a comment at the
end of `Fren/Check.lean`, the shard rebuilt the `.olean` files of
`Fren.Check` and of what imports it (66 and 67 s), but compiled no C code,
since `Check.c` came out byte for byte the same. So a cache of compiled C
code such as ccache would add nothing to the objects in the `.lake`. Each
`.lake` is about 470 MB, and the repository's caches share 10 GB, past
which GitHub evicts the least recently used. So once the build job has
saved one, the `prune-lake-caches` job, the only one that may delete the
repository's caches, deletes all but the newest three that `main` saved,
which keeps the small caches, the query cache and mdbook's, from being
evicted. A pull request whose base's `.lake` was deleted restores the
newest, and Lake rebuilds what differs.

The requirements' chain is the critical path of most `pre-merge` runs
that rebuild it, and the runners slow it: they have four logical CPUs, two
cores of two threads each. On 2026-11-03, on a runner, elaborating
`Reqs/Lint.lean` alone took 82 and 83 s, with one other module elaborated
beside it 90 and 95 s, and with three others 112 and 123 s, while in the
build, beside the rest of `Reqs` and `Impls`, it takes 121 to 152 s.

The `lean ci` workflow also compares the methods on every check that
each can run (`methodsAgree`, [Agreement of
methods](../Methods.md#agreement-of-methods)), and runs the front-end
fuzzer on seeds that no run used before, from the run's number, with
`--avoid-known`, of both generators. What fails that job is exactly a
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
| `lake build --wfail`: the code, the regression tests, the `impl`s' proofs, the examples, and Fren's own requirements elaborated | yes, on two machines | yes | it is the build |
| `lake test`, but for the mutants of Fren's own requirements | yes | yes | under 10 minutes in each shard |
| `ownSpec`: Fren's own requirements checked by the binary | yes | yes, with an empty query cache | some 25 s on CI with the query cache, so it is the gate |
| The mutants of Fren's own requirements (`mutation 0 …`) | no | yes | the slowest jobs of `lake test` |
| Fren's own requirements checked in Lean, and `ownSpecAgreement` ([Own requirements](#own-requirements)) | no | yes | before the chapter split, in `lake build`, the checks took some 80 s of `Reqs.Lang` (256 s with them, 176 s without) and 76 s of `Reqs.Lint` (239 s, 163 s), both on the critical path, which they made 155 s longer, and raised the peak memory of each from some 2.5 GiB to some 10 GiB (one run each) |
| `methodsAgree`: every check of Fren's own requirements, the ui tests and the fuzzer's corpus under the solver, enumeration and random testing, compared ([Agreement of methods](../Methods.md#agreement-of-methods)) | no | yes | it checks everything three times, and the solver, asked the checks that the specs leave to the other methods, took 9.4 GB on Fren's own requirements at two procedures at once, as the job runs them (13.8 GB at four), and some 4 minutes, and 8.8 GB on the ui tests at fourteen at once, as many as there were cores, on macOS: more than a `lake test` shard can spare |
| The book, with the page of the rules (`book`) | yes, on a pull request, and part of `pre-merge`'s verdict | yes | some minutes, with the test driver of shard 0, and no Lean |
| A sample of `fren mutate` over Fren's own requirements, the front-end fuzzer on fresh seeds, the coverage | no | yes | each needs a build or seeds of its own, and what they find is filed or fixed after |

On a pull request, `pre-merge` also uploads stripped copies of the
binaries that it built and tested, so that a reviewer can probe the head
without building it: `fren`, once the build of all but the requirements
has passed, as the artifact
`fren-SHA`, and `fren_test`, once shard 0 has built it, as
`fren_test-SHA`, where SHA is the full sha of the pull request's head.
They are kept for 3 days. They are Linux binaries, built on
`ubuntu-24.04`, which run on Linux but not on macOS.
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
`uiMisread`, `uiAskAgain`, `smtAgreement`, `obligationsAgreement` and
`leanTokens` load the hosted front end, the `.olean` files of `Fren` and
its dependencies; for them, run
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
an update from `main` of a reviewed head, or for a head whose last naming
comment starts with "wording only", whose only parent is the head of the
last clean review before that comment, and that changes neither
AGENTS.md nor `.github/`. That skip's log says "Nothing to review:
wording only:", and for that head the coordinator confirms instead that
each change answers a finding that the comment lists and changes only
prose as AGENTS.md defines it, and that nothing else changed. The
workflow never reviews a pull request from a fork. Its comment counts as the pull request's review, for
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
outside github.com and mentions no one. Markdown images are refused even
in code, as are links to hosts other than github.com. HTML tags are not
refused. After the checks, every `<` in the posted comment is replaced
with U+FF1C `＜`, inside code and out, without parsing Markdown. Thus `<`
shows as `＜` in posted reviews, including in type applications, and no
literal HTML opener remains.
The Claude token is a repository secret, which anyone who can push a
branch can read, until it is moved to an environment that only `main`
can use. Run by hand (`gh workflow run pr-review -f pr=N`), it posts only
on the pull request that its `post` input names.

`scripts/local-review` gives an author a pre-push check of its branch, by
OpenAI's Codex CLI, before CI's review (AGENTS.md says when). It composes
the brief with `compose.py` and `brief.md` as `origin/main` (or `--base
REF`) has them, adds a preamble that says where the check differs from
CI's review, and runs Codex in a scratch copy of the head's tree. The copy
lacks the files that CI removes (AGENTS.md, CLAUDE.md, `.claude`,
`.mcp.json`, `review.md`, `.review` and symbolic links) and those that
steer Codex (AGENTS.override.md, `.codex` and `.agents`). Codex runs with a
read-only sandbox, which stops writes and the network but not reads
elsewhere, and with no web search, apps, browsers or user configuration.
It prints the result, whose first line starts "Pre-push check of", never
"Review of", and saves it in `.lake/local-review/`; it posts nothing.
`--dry-run` prints the prompt and runs no model, and `python3 -I -B
scripts/local_review_test.py` tests the script with a stand-in for Codex.

A pull request merges once `pre-merge` and `lint` pass on its head. Its
branch need not be up to date with `main`: `pre-merge` tests the head
merged into `main` as `main` was when the run started. So two pull
requests that each pass on their own, and merge cleanly, can still break
`main` together. `main`'s own CI is the last check, and when it fails,
fixing or reverting the cause comes before any other merge.

## Query cache

`lake test` checks Fren's own requirements with `fren check`'s [query
cache](../Cli.md#query-cache), so that a query asked by an earlier run is
answered without the solver. The test driver's `ownSpec` job reads the
directory from `FREN_QUERY_CACHE`, which is `.lake/query-cache` if it is
not set, and keeps no answers if it is empty. `FREN_VERIFY_QUERY_CACHE`,
if set, is the directory to compare with (`--verify-query-cache`): the job
fails if `fren check` compared no answers with it, unless it holds no
entry of the current `queryCacheVersion` and cvc5, which no answer could
be compared with. Only that job uses the cache, and `sharedSpec`, which it
runs, a copy of it. The `queryCache` job tests the cache itself: the same
output cold, in a fresh directory, as warm, a warm run that writes no
entry, so that it answered every query from the cache, the same entries
from two cold runs, a comparison that compares answers and finds no
contradiction, one with entries whose answers are flipped that reports
each as a contradiction with no position, and a `sat` entry without a
model that does not answer a query that wants one; and, in memory, a
script asked again gets the answer that it got first, whichever of the
cache's maps holds it.

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

## Solver statistics

`fren check --solver-stats` is a developer's tool for work on the
solver's speed, not a feature of the `fren` command for users: it is
left out of its `--help` and of [the command's chapter](../Cli.md), and
what it prints may change with any cvc5. It reports, on standard error
after the summary and any [timings](../Cli.md#timings), where the time of
each query asked of the solver went (`FrenCli.SolverStats`), as in
this report of Fren's own requirements, of which only the first logic's
line and the first listed query are shown, and their lines shortened
where they show `…`:

```text
solver-stats: queries asked of the solver: 6267, 15922.7 ms (setup 1504.0, init 1733.5, assert 1391.8, check 9587.8, model 509.5, free 1196.1 ms)
solver-stats: logic ALL, queries: 6247, 15900.4 ms (setup 1499.9, init 1728.2, assert 1391.0, check 9579.3, model 508.4, free 1193.6 ms)
solver-stats: checkSat of queries of 5 ms or more: 360, 6566.2 ms, by cvc5's timers: SAT search and the rest 2260 ms, datatypes 1036 ms, strings 1012 ms, …
solver-stats: 1. 311.3 ms: `cli::query_symbols` (expectation), ALL, 3.0 KB, unsat, dominated by SAT search and the rest
solver-stats:   phases: setup 0.2, init 0.3, assert 0.1, check 308.2, model 0.0, free 2.4 ms
solver-stats:   checkSat 308 ms: SAT search and the rest 107 ms, strings 94 ms, arith 88 ms, datatypes 10 ms, clausal form 9 ms
solver-stats:   counts: 6306 decisions, 58 conflicts, 53715 propagations; 35505 theory checks, 28965 rewrites, 455 lemmas, 0 instantiations, 80509 resource units
solver-stats:   inferences: ARITH_CONF_SIMPLEX 175, DATATYPES_INST 172, STRINGS_I_NORM_S 127, …
```

- **The phases** are Fren's own measure of each query, from making its
  term manager to freeing it, in wall-clock time: `setup` makes the
  solver and parses its options and declarations; `init` is the first
  command that initializes its theories (`FrenCli.Cvc5.initializes`),
  where cvc5 sets up every theory of the logic, or nothing if `checkSat`
  is the first; `assert` is the other commands; `check` is `checkSat`;
  `model` reads the model's values; and `free` frees the solver and the
  term manager. The lines by logic sum them over the queries of each
  logic, so a change of logic shows in `init` and `setup` (#755). In a
  logic that shares libpoly's state, such as `ALL`, the commands up to
  and including the first that initializes, and freeing the solver, wait
  for `solverLock` (`FrenCli.Cvc5`), so under `--jobs` more than 1,
  `setup`, `init` and `free` include that wait, and so does `check` for a
  query with no command that initializes the solver.
- **cvc5's timers** split `checkSat`: each theory's checks
  (`theory::T::checkTime`), preprocessing, the clausal form and theory
  combination, in cvc5's whole milliseconds. What none of them accounts
  for is `SAT search and the rest`: the SAT solver's own search and
  propagation, and whatever else `checkSat` does. The report takes the
  timers to be disjoint, which is not read from cvc5's source: no query of
  Fren's own requirements had timed parts that summed to more than its
  `checkSat`, but timers that overlap in part, as the clausal form of a
  theory's lemmas may within its check, would still meet that bound, and
  make `SAT search and the rest` too small. A query whose timed parts
  exceed its `checkSat` says by how much, and a line after the summed one
  says how many of all the queries did, not only of those summed. The
  timers are also read in whole milliseconds, so the rest takes in what
  they leave out, which makes it too large: of the queries of Fren's own
  requirements whose `checkSat` took under 5 ms, it was 2,054 ms of their
  2,485 ms, with cvc5 1.3.2, when the report was added (#757). So the
  summed line sums only the queries whose `checkSat` took 5 ms or more
  (`summedMs`), and the rest is rough for a short query that is listed. In
  cvc5 1.3.2, each theory has one `checkTime`, the arrays' as
  `theory::arrays::theory::arrays::checkTime`. The theories' checks are
  made from within the search, so a query that makes tens of thousands of
  cheap theory checks, as `cli::query_symbols`' do, shows its search's
  cost spread over the search and the theories. A query is `dominated by`
  its largest part. cvc5 has no timer of its own for parts of a theory,
  such as the datatypes solver's cycle check, so those need a profile.
- **A query whose command answers with an error**, answered `error`,
  has its time up to the failure in the phases it reached, and none in
  the later ones. One that throws, as on a parse error, has the time
  since its last mark in `free`. In either case cvc5's statistics are not
  read, so its counts are 0 and its `checkSat` shows no timer. Fren
  writes every script, so neither is expected.
- **The counts** are cvc5's: the SAT solver's decisions, conflicts and
  propagations, the theory checks and rewrites that its resource manager
  counts, every theory's lemmas, quantifier instantiations, the resource
  units that `--resource-limit` limits, and the five commonest of the
  theories' inferences, by cvc5's names.

It lists the 20 slowest queries; `--solver-stats=N` lists `N` of them, and
`--solver-stats=all` every one. The value is written after `=`, not as the
next argument as other options' are, so that the bare flag needs none. The
flag is in no help text, but `fren` suggests the bare flag for a
misspelled option, as it does every option, without its `=N`. A query
answered from the [query cache](#query-cache), or by the same script that
another item asked earlier in the run, asks the solver nothing and is not
reported. Under `--jobs` more than 1, two items can ask the same script at
once, before either answer is kept, and both are then reported. So measure
with no `--query-cache` and with `--jobs 1`, which times each query alone
and asks each script once.

Without the flag, nothing of this runs: Fren reads no clock of its own,
only the one around `checkSat` that every query reads
(`Fren.Core.timeQuery`), and asks cvc5 nothing more. A check of Fren's own
requirements took the same instructions, within 0.02 %, and the same time
as before the report was added, with cvc5 1.3.2 (#757). With it, each
query reads cvc5's statistics once, after its answer and model, so that
the answers, models and messages are the same, which the `solverStats`
test checks. cvc5 keeps the statistics whether or not they are read
(#742), but writing them as text is not cheap: it tries each value as a
number, and throws an exception for each that is not, so a cold check of
Fren's own requirements at `--jobs 1` takes some 40 % more instructions
with the flag. That time is outside every phase that the report measures.
lean-cvc5 does not bind cvc5's `getStatistics`, which would read them
without the text.

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
`testing::coverage` comes after the chapter's last `#fren_check`, so it is
named, and the Lean-hosted front end then checks it, as the `fren` command
checks every procedure. `lake test`'s `ownSpec` job fails on an item that
no `#fren_check` checks in Lean (`hostedChecks`):

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

#fren_check coverage
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
