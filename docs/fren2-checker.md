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
identity desugaring, logical passes, SMT producer, bounded solver transport,
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
Divisor definedness counterexamples are confirmed by evaluating the source
assumptions, lexical bindings, conditional guards and divisor at the retained
site. That confirmation never evaluates the site's `div` or `mod` itself.
Both Boolean operands and unused lets retain static obligations; `if` and
`match` guard their branches. An unrelated partial expression does not prevent
a nonvacuity witness or counterexample in another body from being confirmed.
The complete inventory still includes every function's definedness checks.
Assumptions and goals that a witness or counterexample consumes may divide,
directly or through called functions. They are evaluated strictly under the
model's assignment: both Boolean operands, unused let values and callee bodies
are evaluated, and only an `if` or `match` selects a branch. Any `div` or `mod`
by zero there leaves the row unconfirmed, and the demand-driven interpreter's
value must agree with the strict one. Unsupported sites, undefined
or exhausted prefix evaluation, dependency cycles and absent nonvacuity
witnesses remain explicit incomplete outcomes. This command adds no soundness
claim to the production checker.

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
and `mod`. Both are separate jobs in the child and parent default paths, each
under its own 30-second deadline.
