# Textual tests (development helper, #980 partial)

`FrenTextTests` provides one file parser, exact comparator and result-span writer
for build-time and native tests. `FrenTextDemo` exercises real multiline sums
with a parsed natural-number initial sum. Its context is demonstration syntax,
not Fren. FrenParse and FrenAst are stubs: the remaining #980 dependency is a
shared parser adapter producing the real Fren Context (including nested binding
types and optional values). That adapter belongs to the walking skeleton.

A library supplies `parseContext : String → Except String Context` and
`run : Context → String → IO (Except String String)`, then registers their typed
adapter:

```lean
@[fren_text_tests "test/MyLibrary"]
public def textTests : Fren.TextTests.Runner :=
  .of parseContext run
```

The attribute is on the bundled adapter, so each library can use its actual
parsed Context type. Raw strings are never claimed to be parsed Fren values.
The exact suffix after `-- context:` (including spaces) goes to the adapter;
absence supplies `""`. Context errors and callback `.error m` render as `error: m`.
Callbacks may return multiple lines. Results compare exactly; callback newlines
are LF, with literal CR supported as result content too.

Each `test/<Library>/*.fren` file contains unique nonempty `-- case: name` lines,
an optional immediately following `-- context:` line, one or more physical input
lines, and an optional `-- result: text` with immediate `--  continuation` lines
(two spaces after the dashes). Names are matched by case-sensitive substring.
Input can contain arbitrary multiline text and blank lines. Its final physical
LF/CRLF separates it from the marker and is excluded from callback input; all
other input bytes survive unchanged. Result markers decode physical LF/CRLF to
LF. One optional space after `-- result:` is formatting; other spaces are data.

Column-zero `-- case:`, `-- context:`, `-- result:` and `--  ` are reserved,
even inside a quoted string or multiline input. There is no marker escape syntax.
A case marker always starts a case; a result marker always ends its input.
Repeated/misplaced context or result markers, duplicate names, orphan
continuations, empty inputs and non-comment text after results are errors.
Preambles and post-result comments/blank lines are retained. Without a result,
every line until the next case or EOF is input. Invalid UTF-8 is rejected.

A build-time test module uses `meta import MyLibrary` and
`#fren_tests MyLibrary.textTests`. Declare its own `input_dir` with path
`"test/MyLibrary"`, `text := false`, `filter := .extension #["fren"]`, and add it to
that test library's `needs`, as `FrenTextDemoTests` does in `lakefile.lean`.
Include `moreLeanArgs := textTestLeanArgs` for the explicit unsupported-blessing
diagnostic. Editing a case then invalidates that test library without pulling
test helpers into production IR libraries. These must be byte-sensitive inputs.
With fixed runner code/configuration, equal build keys must imply identical
parsed context, callback input and expected-result data (subject to the usual
content-hash assumption). Lake's text hashes normalize CRLF, while callback
input retains internal physical EOLs. `FrenTextBytes` supplies a one-case byte-count control: `1\n2`
has size 3 and `1\r\n2` has size 4, so an EOL-only edit must rerun the check.

Build `FrenTextDemoTests` for an interpreter check, or build `fren2_test` and run:

```sh
scripts/heavy --offline .lake/build/bin/fren2_test --lib FrenTextDemo
scripts/heavy --offline .lake/build/bin/fren2_test --lib FrenTextDemo --filter sum_00
scripts/heavy --offline .lake/build/bin/fren2_test --lib FrenTextDemo --bless
scripts/heavy --offline python3 scripts/fren_text_tests_test.py
```

The native driver materializes all imported registrations with
`fren_test_runners`; import each new adapter there to discover it. Duplicate
registered directories are rejected. Both modes sort the same flat file paths
and run the same cases. The executable's no-argument S-expression checks and
property-test meta imports remain in place. Building it also builds the helper
regressions and maintained demo checks.

Blessing is **native-only** and requires explicit `--bless`.
`lake build -R -Kbless=1 FrenTextDemoTests` fails with an explanatory diagnostic.
Without `-R`, Lake can reuse its previous configuration and ignore changed
`-K` values; `-Kbless=1` alone never enables blessing. Normal builds always
check and never write. Build artifacts can be restored
without executing commands, so source rewriting is not a supported build effect.
No artifact cache is disabled or purged. Native blessing replaces only selected
mismatching/missing result spans. Every other byte, including CRLF, Unicode,
comments and EOF newline status, is retained. Adding a missing result inserts
its separating newline if necessary. An EOF input ending in literal CR gets a
separate CRLF separator, even after an LF header.

The input-preservation law is stronger than byte-prefix preservation: for a
well-formed parsed file and ordered, disjoint edits to its parsed result spans,
reparsing the rewritten file retains all case names, raw contexts and callback
inputs in order. Selected expected results become the supplied callback texts;
other expected results remain unchanged. Every byte outside those original
result spans remains identical, with missing results inserted at empty spans.
Thus a deterministic callback computes the blessed result again on recheck.
The helper regressions exercise this law across LF/CRLF/mixed/EOF boundaries,
including literal trailing CR and otherwise empty CR input; these are finite
regressions, not a universal proof of the law.

All files are parsed before any writes;
symlink files/directories and paths outside flat `test/<Library>` are rejected.
The writer also checks for a concurrent file edit before writing. Concurrent
writers are unsupported; blessing is not a transaction across multiple files.

Native status is 0 for success (including expected errors and explicit blessing),
1 for mismatches, malformed files or IO/callback exceptions, and 2 for invalid
arguments, unknown/ambiguous library names or a filter selecting no cases.
Check mode accumulates case mismatches rather than stopping at the first one.
