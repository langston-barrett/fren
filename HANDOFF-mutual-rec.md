# Unit 34 / #604: parked handoff

Worktree: `/home/langston/code/fren-mutual-rec`, branch `mutual-recursion`.
Everything is uncommitted. No commits, pushes, PRs, comments, issue edits, or other GitHub writes were made. Nothing under `.github/workflows/` was touched. No files from PR #815's file list were touched.

The coordinator stopped the run and instructed that this unit be parked. No further builds, tests, or code edits were made after that instruction. An attempt to interrupt the previously running build session reported `Unknown process id 35929`, consistent with the run already having been stopped.

## Design decisions

Read `AGENTS.md`, `/tmp/recursion-modules-brief.md`, `gh issue view 604 --repo langston-barrett/fren`, and `gh pr diff 815 --repo langston-barrett/fren --name-only`.

The existing implementation is organized around one function's self-recursion throughout name resolution, termination checking, SMT reflection, contract checking, and Lean generation. I scoped the proposed first PR as the shared termination foundation, without adding group surface syntax or forward references. This scope was communicated in commentary. It does **not** implement the parser example from #604 or finish unit 34.

The group model records:

- For each member, its parameter count and a proposed decreasing parameter position.
- For each use, the caller and callee member indices, the use form (`applied`, `inClosure`, `passed`), and each argument's origin: `payload(caller_parameter_index)` or `other`.
- A candidate is valid only if all chosen parameter positions are in bounds and every edge passes a payload of the caller's chosen parameter to the callee's chosen parameter. Positions may differ between members. Every edge must strictly decrease; same-size edges are not supported by this model.
- Closure uses and passed member functions are rejected. Invalid indices and missing selected arguments are explicitly rejected before their indexing defaults can affect the decision.
- Search enumerates the finite Cartesian product of parameter positions in lexicographic order, choosing the first candidate that passes. Zero-parameter members have no candidate; the empty group with no uses has the empty candidate.

Existing self-recursion is adapted to a singleton group. The adapter only records the diagonal origin information that can decide a self call's descent; the original `RecUse` is retained for first-failure diagnostics. The old core entry point `recursion` was renamed to `selfRecursion`, and all four production call sites were updated.

No surface syntax decision was made. Arbitrary measures and mutually recursive datatype declarations were explicitly left outside this first step. The planned later PRs were (1) group scope/signature registration, cross-call extraction, and simultaneous definitions/evaluation, initially without group contracts; (2) simultaneous Hoare contracts, dependency propagation, reflected equations/result facts, confirmation, and exported Lean contract proofs.

## Files changed

Tracked modifications:

- `src/Reqs/Lang/Recursion.md`: added a "Structural groups" section before "Meaning". Added `GroupParameter`, `GroupArg`, and `GroupUse`; predicates `group_call_decreases?`, `group_structural?`, and `group_counts_match?`; and requirements `structural_group` and `structural_group_search`. The search requirement specifies existence from raw parameter counts and uses, rather than accepting a precomputed existence fact. The prose explicitly says surface groups are not implemented yet. The existing statement that mutual recursion cannot currently be written remains true.
- `src/FrenCore/Recursion.lean`: added the corresponding raw core types; `groupCallDecreases`, `structuralGroup`, `groupCandidates`, `recursionGroup`, and `RecUse.inGroup`. Replaced the successful-selection path of the old singleton algorithm with the group search in `selfRecursion`; kept the original first-failure computation for rejected uses.
- `src/Fren/Elab.lean`: both hosted call sites now use `Core.selfRecursion` (incremental rejection and completed-body classification).
- `src/FrenCli/Elab.lean`: CLI completed-body classification now uses `Fren.Core.selfRecursion`.
- `src/FrenCli/Elab/Model.lean`: CLI incremental rejection now uses `Fren.Core.selfRecursion`.
- `src/Impls/Lang.lean`: imports the new `Impls.Recursion` module.
- `src/FrenTest/FuzzFrontends.lean`: minimal integration of the separate generator via the new `recursionPositions` mode / `--recursion-positions` flag, including parsing, formatting, worker arguments, usage, and 20 corpus seeds appended after the existing modes. Existing generators and their random draws were not edited.

New, untracked files (must be included if this work is resumed):

- `src/Impls/Recursion.lean`: draft `impl` bindings for both new requirements, representation conversions, a general sequence-index helper, proof attempts relating the core candidate judgment to the spec, candidate-generation completeness, search existence and returned-candidate soundness. **This file has not successfully compiled; the proof attempts need validation and likely repair.** The final search-binding/helper edits happened while the larger build was running.
- `src/FrenTest/MutualRecursion.lean`: core `#guard` tests for different parameter positions across two members, reversed call order, a self edge, conflicting position choices, closure/passed uses, non-payload arguments, empty groups, zero/negative parameter counts, invalid indices, and missing selected arguments. Includes a bounded comparison against a copied legacy singleton algorithm for 0–3 parameters and lists of up to two uses with every form and two-argument origin combination. This module imports `Impls.Recursion`, so it has not been validated yet.
- `src/FrenTest/FuzzRecursion.lean`: standalone singleton generator. Varies parameter count/position, ordinary vs generic recursive enumerations, direct vs nested patterns, expression vs function-block definitions, primitive/collection/option/generic/recursive result types, type-appropriate comparisons, and isolated invalid uses (unchanged parameter, constructed argument, `let` alias, closure, passed function). Valid cases append a comparison at constant leaf arguments; invalid cases are their own specs. **Not yet compiled or fuzzed.**
- `test/ui/lang/recursion_group_singleton.fren`: positive singleton tests choosing first/middle/last parameters, including nested descent and a block definition, plus three constant-value expectations.
- `test/ui/lang/recursion_group_singleton_static.fren`: no-common-decreasing-position diagnostic. Kept separate so its intentional error does not suppress the positive file's checks.

Draft coordinator artifacts already exist:

- `/tmp/mutual-rec-pr-body.md`: title on line 1, body describing the foundational scope and remaining stack; ends with the required attribution. Validation still says pending. It was written before the final search `impl` work and is a draft, not a readiness claim.
- `/tmp/mutual-rec-commit-msg.txt`: draft commit message.

## Build and test progress at stop

All build commands used the requested environment:

```sh
env PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin:$PATH" \
  NIX_CFLAGS_LINK_x86_64_unknown_linux_gnu=-fuse-ld=lld \
  /home/langston/code/fren/scripts/heavy lake build ...
```

Both attempts waited several minutes for a shared heavy-job slot.

1. `lake build Reqs.Lang FrenCore.Recursion`: failed in `FrenCore.Recursion` because the lambda over `List.range n.toNat` inferred an `Int` binder. Fixed by explicitly declaring `(i : Nat)` and coercing its stored position to `Int`.
2. `lake build Impls.Recursion FrenTest.MutualRecursion fren_fuzz_frontends fren_test`: latest observed output successfully built `FrenCore.Recursion` and its C object, the shared dependents, CLI elaboration modules, `Fren.Elab` and its C object, `Fren.Spec`, `Fren.Impl`, `Fren.Trace`, `Fren.Enumerate`, `Fren.View`, `Fren.Literate`, and `Fren`. It reported a failure in `FrenTest.FuzzRecursion` because `at` is a Lean keyword. That local variable was renamed to `pos`, but there was no successful rerun. The latest observed progress was `773/779`; no successful `Reqs.Lang`, `Impls.Recursion`, test-driver, or fuzzer completion was observed.

The fuzzer generator import was also corrected during iteration to `FrenCli.Search` with `open FrenCli.Eval`, where its RNG/state helpers are actually defined. These final generator changes are unvalidated.

No test jobs or differential fuzz runs were executed. `lake build --wfail` was **not** run. No claim that the branch builds or passes is justified. A read-only `git diff --check` passed at an intermediate point; that does not validate the code or proofs.

## Remaining work if resumed

1. Reassess the first-PR scope with the coordinator after the overlap clears. This is a model/core foundation, not a user-visible mutual-recursion implementation.
2. Compile and repair `Reqs.Lang`, `Impls.Recursion`, the core tests, and the fuzzer generator. Pay particular attention to the draft proofs' simplification of generated Boolean predicates, sequence indexing, list-map conversions, `impl` goal shape, and candidate enumeration. Do not assume those proof scripts work.
3. Validate singleton equivalence and diagnostic preservation. The bounded comparison is only regression coverage; there is not yet a general theorem equating `selfRecursion` with the legacy algorithm. Consider adding one if appropriate.
4. Run the two new UI files and existing structural/generic recursion and recursive-contract UI tests through both front ends. Use the distinct `uiMisread`/`uiAskAgain` jobs for fixtures from those directories.
5. Build `fren_test` and `fren_fuzz_frontends` explicitly. Run the new corpus mode, then a few thousand fresh `--recursion-positions` specs. Inspect that generated errors are the intended recursion errors rather than accidental parser/type errors. Fix new differences caused by the change; do not relist known differences.
6. Run the affected metadata/formatting/library checks and the required full `lake build --wfail`. Binaries/test jobs must use `/home/langston/code/fren/scripts/heavy --offline`; builds stay online.
7. Update the draft PR body with actual validation and any changed scope. Leave git and GitHub writes to the coordinator. Do not touch the current files of in-flight PR #815 without renewed coordination.

## Open questions and limitations

- Is a termination-foundation PR the desired first cut, or should this remain parked until forward scoping and Lean generation can be developed together? No surface syntax has been selected or implemented.
- The current candidate model requires strict descent on every intra-group edge. It does not support a cycle with an unchanged edge followed by a decreasing edge, nor arbitrary measures. Confirm the intended structural-group boundary before exposing it as language behavior.
- `groupCandidates` eagerly materializes the Cartesian product. This is small for the existing singleton callers, but larger future groups may need lazy/backtracking search with the same selection order.
- Only existence/completeness and returned-candidate validity have draft general proofs. Lexicographic first-choice behavior is implemented and described in prose, but has no separate ordering proof yet.
- Group-level diagnostics, signature/type compatibility, generics across group members, duplicate member handling, group privacy/scope, contract dependencies, reflection, and actual Lean `mutual` declarations remain untouched.
- The code and proof drafts were not reviewed by a fresh agent. There is no PR head or CI review to consult.
