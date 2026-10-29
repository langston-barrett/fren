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
Markdown fences intact. Seven executable Python regressions check open-range
delimiters, nested type arguments, negative bounds, command wrappers,
generated-name and binder capture, qualified Bool aliases, generic wildcard
parameters, and idempotence. Boolean literal constraints use the binder or
its negation, preserving their truth without introducing an equality lint.
Raw string-generated specs and prose outside code fences require manual
audit. Hosted build validation and the final test suite are recorded
separately once complete.

## Human readability and semantic audit

The one-off script deliberately allocated fresh fallback names rather than
claiming to understand domain terminology. Those generated names were not a
finished editorial migration. A subsequent review covers every generated
`Subset…N` declaration and `subset_value` binder in tracked specifications,
examples, requirement chapters, hosted tests, diagnostic examples and fixtures.
The script remains a historical one-off tool; it must not be rerun over the
reviewed declarations to restore generated names.

The README now uses `Status` with binder `status` and label `status_range`,
and one shared `Pos` with binder `n` and label `positive` for attempts, early
attempts and late attempts. This removes two duplicate declarations (two
successful declaration checks in the actual CLI); it does not change the admitted values or
any procedure/expectation. Run-length encoding uses the same readable `Pos`
name for its count. Other fixtures retain independent declarations where
separate declaration checks are part of the regression. Diagnostic test
labels named `invariant` remain deliberate stable labels, rather than being
renamed speculatively along with the domain.

Each remaining rename preserves the base type, bounds, constructor pattern
and invariant formula, updating all type uses and expected diagnostic names.
Declaration binders are renamed only within their declaration, with a check
that the chosen binder cannot capture a free bound endpoint. Domain names
are checked against existing type/enum/struct declarations in their file.
The review also includes the newer recursive-successor and positional
refinement fixtures introduced after the original 51-file migration.

This audit distinguishes cosmetic cleanup from semantic preservation: aliases
remain base-type aliases; expression pattern tests remain expressions; wrapper
scope and explicit evidence settings remain in place; finite-pattern metadata
and general nested invariant enforcement are required by their existing
regressions. The earlier aggregate verdict screen is not upgraded into a
claim of per-check proof. No new semantic migration change is hidden by these
name changes. The protected original-workspace `README.fren` is not a tracked
worktree input and is not edited here.

Reviewed generated declaration names:

| File | Generated name | Reviewed name |
| --- | --- | --- |
| `README.md` | `SubsetREADME1` | `Pos` |
| `README.md` | `SubsetREADME2` | `Pos` |
| `README.md` | `SubsetREADME3` | `Pos` |
| `examples/rle.fren` | `SubsetRle1` | `Pos` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes8` | `Digit` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes5` | `FirstPercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes6` | `SecondPercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes7` | `ThirdPercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes2` | `LeftPercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes3` | `MiddlePercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes4` | `RightPercent` |
| `src/FrenCore/Codes.lean` | `SubsetErrorCodes1` | `SmallSigned` |
| `src/FrenTest/ForcedVariants.lean` | `SubsetForcedVariants1` | `Pos` |
| `src/FrenTest/Interp.lean` | `SubsetInterp1` | `SizeByte` |
| `src/FrenTest/Interp.lean` | `SubsetInterp2` | `ClampedByte` |
| `src/FrenTest/Interp.lean` | `SubsetInterp3` | `ProvedByte` |
| `src/FrenTest/Interp.lean` | `SubsetInterp4` | `Pos` |
| `src/FrenTest/Interp.lean` | `SubsetInterp5` | `CappedByte` |
| `src/Reqs/Lang/Items.md` | `SubsetItems1` | `Pos` |
| `src/Reqs/Lang/Overview.md` | `SubsetOverview1` | `Target` |
| `test/cli/args/dump_smt_generic_pattern.fren` | `SubsetDumpSmtGenericPattern1` | `Digit` |
| `test/cli/commands/eval_pattern_types.fren` | `SubsetEvalPatternTypes1` | `Byte` |
| `test/cli/commands/eval_pattern_types.fren` | `SubsetEvalPatternTypes2` | `AtLeastTen` |
| `test/cli/commands/refines_pattern.fren` | `SubsetRefinesPattern2` | `Pos` |
| `test/cli/fmt/pattern_types.expected` | `SubsetPatternTypes1` | `Pos` |
| `test/cli/fmt/pattern_types.expected` | `SubsetPatternTypes1` | `Pos` |
| `test/cli/fmt/pattern_types.fren` | `SubsetPatternTypes1` | `Pos` |
| `test/cli/results/enumerated_counterexample.fren` | `SubsetEnumeratedCounterexample1` | `SmallSigned` |
| `test/cli/results/f0601_forced_variant.fren` | `SubsetF0601ForcedVariant1` | `Pos` |
| `test/cli/results/f0601_forced_variant_all.fren` | `SubsetF0601ForcedVariantAll1` | `Pos` |
| `test/cli/results/f0601_forced_variant_none.fren` | `SubsetF0601ForcedVariantNone1` | `Pos` |
| `test/cli/results/f0644_too_many.fren` | `SubsetF0644TooMany1` | `FirstPercent` |
| `test/cli/results/f0644_too_many.fren` | `SubsetF0644TooMany2` | `SecondPercent` |
| `test/cli/results/f0644_too_many.fren` | `SubsetF0644TooMany3` | `ThirdPercent` |
| `test/cli/results/f0645_generic.fren` | `SubsetF0645Generic1` | `LeftTwoBit` |
| `test/cli/results/f0645_generic.fren` | `SubsetF0645Generic2` | `RightTwoBit` |
| `test/cli/syntax/f0154_size.fren` | `SubsetF0154Size1` | `TwoBit` |
| `test/cli/types/f0389_recursive_argument.fren` | `SubsetF0389RecursiveArgument1` | `Digit` |
| `test/ui/checks/enumerated.fren` | `SubsetEnumerated1` | `Trit` |
| `test/ui/checks/enumerated.fren` | `SubsetEnumerated2` | `SixBit` |
| `test/ui/checks/enumerated.fren` | `SubsetEnumerated3` | `BoundedCount` |
| `test/ui/checks/enumerated_errors.fren` | `SubsetEnumeratedErrors1` | `FirstPercent` |
| `test/ui/checks/enumerated_errors.fren` | `SubsetEnumeratedErrors2` | `SecondPercent` |
| `test/ui/checks/enumerated_errors.fren` | `SubsetEnumeratedErrors3` | `ThirdPercent` |
| `test/ui/checks/enumerated_errors.fren` | `SubsetEnumeratedErrors4` | `InputByte` |
| `test/ui/checks/enumerated_errors.fren` | `SubsetEnumeratedErrors5` | `OtherByte` |
| `test/ui/checks/enumerated_functions.fren` | `SubsetEnumeratedFunctions1` | `Trit` |
| `test/ui/checks/enumerated_static.fren` | `SubsetEnumeratedStatic1` | `TwoBit` |
| `test/ui/checks/pattern_obligations.fren` | `SubsetPatternObligations1` | `RequiredTrue` |
| `test/ui/checks/pattern_obligations.fren` | `SubsetPatternObligations2` | `Digit` |
| `test/ui/checks/recursion_hoare.fren` | `SubsetRecursionHoare1` | `Successor` |
| `test/ui/lang/generic_uninterpreted.fren` | `SubsetGenericUninterpreted1` | `TwoBit` |
| `test/ui/lang/generics_pattern_elements.fren` | `SubsetGenericsPatternElements1` | `NodeDigit` |
| `test/ui/lang/generics_pattern_elements.fren` | `SubsetGenericsPatternElements2` | `BagDigit` |
| `test/ui/lang/generics_pattern_elements.fren` | `SubsetGenericsPatternElements3` | `ElementDigit` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes1` | `Mark` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes2` | `Digit` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes3` | `Pos` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes4` | `Trit` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes5` | `TritElement` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes6` | `OneOrTwo` |
| `test/ui/lang/generics_pattern_types.fren` | `SubsetGenericsPatternTypes7` | `CounterexampleTrit` |
| `test/ui/lang/generics_static.fren` | `SubsetGenericsStatic1` | `OtherDigit` |
| `test/ui/lang/higher_order_static.fren` | `SubsetHigherOrderStatic1` | `Nonnegative` |
| `test/ui/lang/ordered_structs.fren` | `SubsetOrderedStructs1` | `MinorVersion` |
| `test/ui/lang/ordered_structs.fren` | `SubsetOrderedStructs2` | `Nonnegative` |
| `test/ui/lang/ordered_structs.fren` | `SubsetOrderedStructs3` | `HttpStatus` |
| `test/ui/lang/pattern_types.fren` | `SubsetPatternTypes2` | `Pos` |
| `test/ui/lang/pattern_types_meaning.fren` | `SubsetPatternTypesMeaning1` | `Enabled` |
| `test/ui/lang/pattern_types_meaning.fren` | `SubsetPatternTypesMeaning2` | `LevelValue` |
| `test/ui/lang/pattern_types_meaning.fren` | `SubsetPatternTypesMeaning3` | `ThreeBit` |
| `test/ui/lang/pattern_types_meaning.fren` | `SubsetPatternTypesMeaning4` | `OtherDigit` |
| `test/ui/lang/pattern_types_meaning.fren` | `SubsetPatternTypesMeaning5` | `Nonnegative` |
| `test/ui/lang/procedures.fren` | `SubsetProcedures1` | `Temperature` |
| `test/ui/lang/quantifiers_unbounded.fren` | `SubsetQuantifiersUnbounded1` | `Nonnegative` |
| `test/ui/lang/refines_pattern.fren` | `SubsetRefinesPattern1` | `Pos` |
| `test/ui/lang/type_facts.fren` | `SubsetTypeFacts1` | `TwoBit` |
| `test/ui/lang/type_facts.fren` | `SubsetTypeFacts2` | `SmallPayload` |
| `test/ui/lang/type_facts.fren` | `SubsetTypeFacts3` | `TritElement` |
| `test/ui/lang/type_facts.fren` | `SubsetTypeFacts4` | `OneOrTwo` |
| `test/ui/syntax/angle_brackets.fren` | `SubsetAngleBrackets1` | `Digit` |
| `test/ui/syntax/pattern_type_upto.fren` | `SubsetPatternTypeUpto1` | `Negative` |

Readability validation so far: all seven migration regressions pass. Native
README checks before/after preserve the same one intentional infeasibility
failure and zero inconclusive/redundant results; passes change from 20 to 18
because the two duplicate positive-Nat declarations are removed. The RLE
example reports 15 passes, zero failures/inconclusive/redundant results. Its
constraint label is also renamed from `invariant` to `positive`. All 26
changed UI fixtures pass in both native and hosted frontends (the runner
returns an empty failure array). `FrenTest.Interp` builds successfully (595
jobs), including kernel proofs and interpretation-result diagnostics.
Independent review compared 114 actual declarations and found identical
base types, bounds and predicate formulas after binder alpha-renaming; the
other six binder records describe the formatter snapshot rather than new
declarations. Final snapshots and full build are recorded by integration.

A second role-name review caught and corrected the generic-function fixture's
`InputTwoBit`/`OutputTwoBit` pair: both parameters are inputs, so their names
are `LeftTwoBit` and `RightTwoBit`. Both declarations and their checks remain.
The other introduced role names were checked against their actual use sites:
`InputByte` is an input, node/bag/element digits describe their respective
payloads or collection elements, and size/clamped/proved/capped byte aliases
name the functions whose result constraints they exercise.

The final full build caught one additional naming collision: the proposed
`PartAt` binder `part` shadowed the existing `lang::part` function. It is
`part_index` instead; the base type and `0..=6` predicate are unchanged.
The earlier checks were bounded: declaration alpha-equivalence, 26 paired UI
files, the hosted interpretation regression, and the migration-script tests.
They did not compile every changed requirements chapter or validate all
namespace lookup. The full `lake build --wfail` exposed this collision, so
those earlier results are not a claim that the complete migration compiled.
Every changed requirements chapter must pass the final full build after the
correction, followed by the full test suite. Integration records those final
results separately against the tested commit.
