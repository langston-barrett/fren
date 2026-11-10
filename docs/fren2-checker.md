# Checking a Fren2 source file

Build the ordinary standalone command and run it from a checkout with the
repository's pinned local cvc5 available:

```sh
scripts/heavy lake build fren2_check --wfail
scripts/heavy --offline .lake/build/bin/fren2_check example.fren
```

For example, save this as `example.fren`:

```text
mod example
fn next(n: Int): Int := n + 1
expect safe(n: Int) {
  assume nonnegative: n >= 0
  expect grows: next(n) > n
}
```

The command reads one UTF-8 file, preserves its bytes and line endings, and
uses the actual Fren2 parser, resolver, walking typechecker and validators,
logical passes, SMT producer, bounded solver transport,
model decoder and source confirmation. `FrenCli2.checkText` and `checkFile`
provide the same reusable library entry. This supports the current admitted
walking language only; it adds no syntax, imports or declaration semantics.
Invalid or unsupported source cannot produce a verified result.

Every check prints one JSON object containing the aggregate verdict, exit
class, configuration and every question's owner, kind, UTF-8 byte span (when
available), status and reason. Spans are half-open `[start_byte, stop_byte)`
ranges in the file named by `file`; `file_id` is the invocation-local ID 0.
Frontend diagnostics retain their actual byte spans. A source-confirmed
witness or counterexample includes an assignment preview in parameter order;
`parameter_index` refers to that owner's written parameter list. Explanatory
strings are limited to 1024 characters (assignment values to 256), with an
explicit truncation marker. At most 16 assignment values are shown, with an
`omitted_values` count. No question rows are omitted, including blocked and
incomplete ones. Raw SMT scripts and model responses are not printed.

Exit classes are deterministic:

| Exit | Verdict | Meaning |
| --- | --- | --- |
| 0 | `verified` | The production report verified all required questions. |
| 1 | `refuted` | A counterexample was confirmed against the source. |
| 2 | `inconsistent` | Owner assumptions are inconsistent; vacuous goals do not verify the program. |
| 3 | `inconclusive` | Unknown, unsupported, blocked, unconfirmed, resource, process or evidence failure. Inspect all rows. |
| 4 | `noChecks` | No proof obligations; this includes an empty module. |
| 5 | `inputFailure` | Arguments, file/UTF-8 input, parse, resolution, typing or admission failed. |

`--help` prints usage and exits 0 without checking a program. A successful
process exit alone is therefore not a verification certificate. Consumers
should inspect the JSON verdict as well as the exit status. Other report
outcomes use the production checker's precedence and retain all question rows.

The source cap is 1,048,576 bytes. The solver is fixed to the pinned executable
under `.lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5` in the source tree
containing `.lake/build/bin/fren2_check`; nothing else, Python included, is
needed at runtime. Missing assets produce explicit failures;
the command does not download or install them. Filenames are passed as argv
and filesystem paths, with `--` before a filename beginning with a dash.

```sh
scripts/heavy --offline .lake/build/bin/fren2_check --wall-ms 500 --solver-ms 250 example.fren
scripts/heavy --offline .lake/build/bin/fren2_check -- -example.fren
```

Options precede the single filename. All limits are decimal integers:

| Option | Default | Allowed range |
| --- | --- | --- |
| `--wall-ms` | 2000 | 1–10000 |
| `--solver-ms` | 1000 | 1–10000 |
| `--solver-resources` | 1000000 | 1–1000000000 |
| `--input-bytes` | 1048576 | 1–1048576 |
| `--output-bytes` | 65536 | 1–1048576 |
| `--evaluation-depth` | 10000 | 0–10000 |

Time, resource and byte limits apply to each physical solver invocation;
SAT model readback is another invocation. Source confirmation uses the
evaluation-depth bound. These limits are not a whole-file wall-time or memory
guarantee. Existing transport process cleanup and protocol checks apply.
The command uses no shell interpolation or solver-command override.

Verification remains conditional on the current trusted solver, encoding,
physical transport and source evaluator. Universal source/encoding soundness,
model existence, confirmation adequacy and `CheckerContract` remain unproved.
The next section describes how a model is confirmed. This command adds no
soundness claim to the production checker.

## How a model is confirmed

`src/Spec/Compiler/Smt.md` states what a confirmed answer means: rule
`smt.model.candidate` defines the `SourceCandidate` relation, and rule
`smt.model.confirmation` reads the four statuses against it. This section
describes the procedure, `FrenOirToSmt.confirmAssignment`, that computes a
status. The correspondence between the two is the unproved
`ConfirmationContract`.

### Gates before evaluation

Confirmation regenerates the program from the original admitted source and
selects the question by its index. It evaluates nothing, and the row is
unconfirmed, unless all of the following hold:

- the question is ready;
- every definition that the question depends on exists; and
- every prerequisite question exists, is ready and is a definedness question.

The assignment must then have the exact source arity, the type of each
parameter and real enum membership. Otherwise the candidate is rejected.

### Hypotheses and goals

Every retained hypothesis is evaluated on its original source body and must be
true. A false hypothesis rejects the candidate. A satisfiability question then
yields a concrete witness. A validity question also evaluates its retained
source goal: false yields a concrete counterexample, and true rejects the
candidate.

Each such observation evaluates the body under the assignment by the
demand-driven interpreter, and must yield a Boolean. A consumed assumption or
goal may divide, directly or through called functions. When the body or a
function that it transitively calls mentions `div` or `%`, the body is also
evaluated strictly, and the strict value must equal the interpreter's. A body
that reaches no `div` or `%` has no undefined primitive step, so it skips
strict evaluation: the demand-driven value alone decides, and confirmation
costs no more than the interpreter.

Strict evaluation follows the retained verification tree of rule
`lir.walking.demand`. It evaluates:

- both operands of every operator, including `and` and `or`;
- every let value, even if unused;
- every call argument, followed by the callee body; and
- only the selected branch of an `if` or `match`.

A `div` or `%` by zero has no value, so any undefined step fails strict
evaluation and leaves the row unconfirmed. One 10,000-step budget is shared
across the consumed premises and the goal of each confirmation. Exhausting it
leaves the row unconfirmed with an evaluation budget reason. Successful calls
are memoized by callee, argument values and remaining depth, so a shallower
call cannot reuse a result that needed more recursion.

### Definedness sites

A definedness counterexample evaluates no goal. Its question must retain a
`div` or `%` as its origin and ask that the divisor differ from zero; any
other form is unconfirmed. After the hypotheses, confirmation follows the path
to that site in its source body:

- A `let` whose body encloses the site has its value evaluated and bound.
- An `if` or `match` whose branch encloses the site has its condition or
  scrutinee evaluated. If the selected branch does not enclose the site, the
  candidate is rejected as unreachable.
- An operand, a call argument, a let value, a condition or a scrutinee that
  itself encloses the site is entered without evaluation.

Terms off the path are not evaluated. The divisor is then evaluated in the
environment of the site: zero yields a concrete counterexample, and any other
integer rejects the candidate. The site's `div` or `%` itself is never
evaluated.

The terms that confirmation evaluates are the let values, conditions and
scrutinees needed to reach the site, and then the divisor. Each of them is
evaluated twice, by the demand-driven interpreter and strictly, whether or not
it mentions `div` or `%`. The two values must be equal. The strict evaluations
draw on the budget that the hypotheses share. An evaluated term with no strict
value, such as a let value `false and (1 div x = 1)` at `x = 0`, leaves the
row unconfirmed.

### What the static inventory still covers

Both Boolean operands and unused lets retain static obligations; `if` and
`match` guard their branches. An unrelated partial expression does not prevent
a nonvacuity witness or counterexample in another body from being confirmed.
The complete inventory still includes every function's definedness checks.
Unsupported sites, undefined or exhausted prefix evaluation, dependency cycles
and absent nonvacuity witnesses remain explicit incomplete outcomes.

## Tests

Build and run the focused normal test job with:

```sh
scripts/heavy lake build fren2_test --wfail
scripts/heavy --offline .lake/build/bin/fren2_test --job smtControls
scripts/heavy --offline .lake/build/bin/fren_test --job fren2 smtControls
```

`smtControls` retains the existing checker controls and adds the library and
actual source command controls. It is also included in the child and parent
default paths, under the existing 30-second child-job deadline. Command failure
fixtures use an isolated temporary tree's fixed solver path; the shipped solver
and runtime files are unchanged.

The annotated known-verdict corpus is in `test/fren2-verdicts/`. Run it with
`.lake/build/bin/fren2_test --job verdictCorpus`. The `definednessControls` job
checks source-site confirmation and evidence-binding controls for both `div`
and `%`. Both are separate jobs in the child and parent default paths, each
under its own 30-second deadline.
