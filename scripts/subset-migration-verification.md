# Subset migration verification

The one-off migration was run on the #371 worktree after its CLI build passed.
The baseline executable was saved before subset implementation as
`/private/tmp/fren-371-before`. The new executable supported declared subset
aliases and temporarily retained old inline syntax so both forms could be
compared before retiring the old parser.

`migrate-subsets.py --verify OLD_FREN NEW_FREN` migrated 51 tracked files:
49 standalone Fren/Markdown inputs and two hosted Lean inputs. It ran every
standalone input before writing any files, then ran every changed standalone
input after all writes. Complete commands' exit statuses, stdout, stderr,
generated declarations, and source edits were saved in
`/private/tmp/fren-371-subset-migration.json`.

Of these inputs, 33 produced check summaries on both versions. Their totals
were 541 passed, 73 failed, one inconclusive, and two redundant before;
619 passed, 73 failed, one inconclusive, and two redundant after. Every one
of these files retained its own failed, inconclusive, and redundant counts.
The additional passes include the new subset declaration obligations.
These count comparisons are a regression screen, rather than proof that
every individual check has the same identity and verdict. UI annotations,
diagnostic snapshots, and hosted guards also need checking after migration.

Files containing deliberate static errors or non-standalone documentation
fragments did not produce check summaries. Their diagnostics are retained
in the report. Retired pattern-type diagnostics intentionally require new
negative fixtures and snapshots: binding patterns are now ordinary
expression-pattern errors, and the former nested-alias prohibition is
removed. The former F0369 fixture changed exit status from 2 to 3 while its
old warning directives remained; this requires fixture cleanup, rather
than being counted as a preserved result.

The migration leaves expression `is` tests, strings, comments, and non-Fren
Markdown fences intact. Six executable Python regressions check open-range
delimiters, nested type arguments, negative bounds, command wrappers,
generated-name and binder capture, qualified Bool aliases, and idempotence.
Raw string-generated specs and prose outside code fences require manual
audit. Hosted build validation and the final test suite are recorded
separately once complete.
