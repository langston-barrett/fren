import Lake

open System Lake DSL

-- Lake's artifact cache, one for each toolchain on a machine, which every
-- worktree shares: a step whose inputs, by their content, are those of a
-- step that a build on the machine ran before takes that step's outputs
-- from the cache instead of running (`Reqs/dev/Testing#shared-builds`).
-- They are linked into `.lake/build` too, where `lake env` and the tests'
-- runs of the hosted front end look for them. A coverage build (below)
-- uses it only when its key covers the worktree's directory, which its
-- object files name.
--
-- `-Kcoverage_dir=DIR` if DIR is this worktree's own directory, where a
-- coverage build's objects write their counters (below): another
-- directory, as one copied from another worktree's command, turns the
-- artifact cache off for the coverage build.
def coverageDir? : Option String := (get_config? coverage_dir).filter (· == (__dir__).toString)

package fren where
  srcDir := "src"
  testDriver := "fren_test"
  version := v!"0.1.0"
  enableArtifactCache := (get_config? coverage).isNone || coverageDir?.isSome
  restoreAllArtifacts := true

-- `lake -R -Kcoverage=RUNTIME build` compiles the code whose coverage is
-- measured with gcov's counters, and links the executables that run it
-- with the profiling runtime at the path RUNTIME, which Lean's toolchain
-- lacks (`Reqs/dev/Testing#coverage`). Its object files name the directory
-- where they write their counters, so it uses the artifact cache only
-- with `-Kcoverage_dir=DIR`, the worktree's own directory, which their key
-- then covers (`coverageDir?`, above): no other worktree gets them.
def coverageArgs : Array String := match get_config? coverage with
  | some _ => #["--coverage"] ++ (coverageDir?.map (s!"-DFREN_COVERAGE_DIR={·}")).toArray
  | none => #[]
-- The compiler inlines small functions, whose code then runs in their
-- callers, so that they would seem never to run.
def coverageLeanArgs : Array String := if (get_config? coverage).isSome then #["-Dcompiler.small=0"] else #[]
def coverageLinkArgs : Array String := match get_config? coverage with
  | some runtime => #[runtime]
  | none => #[]

-- Fren's fork of the Mathlib-free lean-smt that Veil uses (verse-lab's
-- `v4.32.0-veil-no-mathlib`), with five patches: under `trust`, the
-- preprocessing skips the proofs of the goal's simplification, which Fren
-- discards, and which take time quadratic in the number of binders;
-- inductive types with type parameters are translated as SMT-LIB parametric
-- datatypes (`Reqs/Lang/Generics`); and universe-polymorphic ones, Lean's
-- `Option` and `Except`, which the prelude's types are, at universe 0, with
-- a hygienic field named after its position (`Reqs/Lang/Prelude`); and a
-- datatype's `Bool` fields and `Bool` type arguments in a model are
-- reconstructed as `Bool`s, not propositions, as Fren's own readers of
-- sets, relations and sequences do (`Fren/SmtTranslate`); and the
-- registered translators are evaluated once, not at every subterm, which
-- in the interpreter cost more than translating. The commit is on the
-- fork's branch `cache-translators`, on top of `fren-bool-payloads`,
-- `parametric-datatypes-v3`, `parametric-datatypes-v2` and
-- `trust-skip-proofs`.
require plausible from "vendor/plausible"

require smt from git "https://github.com/langston-barrett/lean-smt.git"@"97e7501e330fde1ba2c412ac1c0e5011568c49c5"

-- Which library builds a module: a library builds each module of its
-- `globs` (by default, its root) with its own configuration, its `needs`
-- and compiler arguments, even if another library has the module too. A
-- module that a build reaches only by an import is built with that of the
-- last library that has it, in its globs or under one of its roots. So that
-- each module is built one way, no module is in the globs of two libraries,
-- which `lake test`'s `libraries` job checks.

-- Fren2 libraries own their roots and modules imported beneath those roots.
lean_lib FrenBase

lean_lib FrenBaseTests

lean_lib FrenSource

lean_lib FrenSourceTests

lean_lib FrenDiag

lean_lib FrenDiagTests

lean_lib FrenSexp

lean_lib FrenSexpTests

-- Development helpers; no production IR library depends on them.
lean_lib FrenTextTests

lean_lib FrenTextTestsTests

lean_lib FrenTextDemo

-- Include this in text-test libraries: -Kbless=1 must fail clearly, and its
-- compiler option must be part of Lake's artifact key. Bless natively instead.
def textTestLeanArgs : Array String :=
  if (get_config? bless).isSome then #["-Dfren.textTests.bless=true"] else #[]

lean_lib FrenTextDemoTests where
  moreLeanArgs := textTestLeanArgs
  needs := #[`@/fren_text_demo, `@/fren_text_bytes]

input_dir fren_text_demo where
  path := "test/FrenTextDemo"
  text := false
  filter := .extension #["fren"]

-- Callback input retains internal physical EOLs, so its inputs need byte hashes.
input_dir fren_text_bytes where
  path := "test/FrenTextBytes"
  text := false
  filter := .extension #["fren"]

lean_lib FrenProp

lean_lib FrenPropTests

lean_lib FrenAst

lean_lib FrenAstTests where
  moreLeanArgs := textTestLeanArgs
  needs := #[`@/fren_ast_text]

input_dir fren_ast_text where
  path := "test/FrenAst"
  text := false
  filter := .extension #["fren"]

lean_lib FrenModule

lean_lib FrenModuleTests

lean_lib FrenExpr

lean_lib FrenExprTests

lean_lib FrenMir

lean_lib FrenMirTests

lean_lib FrenLir

lean_lib FrenLirTests

lean_lib FrenOir

lean_lib FrenOirTests

lean_lib FrenParse

lean_lib FrenParseTests where
  moreLeanArgs := textTestLeanArgs
  needs := #[`@/fren_parse_text]

input_dir fren_parse_text where
  path := "test/FrenParse"
  text := false
  filter := .extension #["fren"]

lean_lib FrenAstToHir

lean_lib FrenAstToHirTests where
  needs := #[`@/fren_resolve_inputs]

input_dir fren_resolve_inputs where
  path := "test/FrenResolve"
  text := false
  filter := .extension #["fren", "refs"]

lean_lib FrenHirToThir

lean_lib FrenHirToThirTests where
  moreLeanArgs := textTestLeanArgs
  needs := #[`@/fren_typecheck_inputs, `@/fren_resolve_inputs, `@/fren_walking_inputs]

input_dir fren_walking_inputs where
  path := "test/FrenWalking"
  text := false
  filter := .extension #["fren"]

input_dir fren_typecheck_inputs where
  path := "test/FrenTypecheck"
  text := false
  filter := .extension #["fren"]

-- The walking skeleton's whole-pipeline adapter (parse, resolve, admit, type,
-- validate) over the legacy `Resolved` representation, kept out of the passes.
lean_lib FrenWalking

lean_lib FrenWalkingTests

lean_lib FrenThirDesugar

lean_lib FrenThirDesugarTests

lean_lib FrenThirToMir

lean_lib FrenThirToMirTests

lean_lib FrenMirToMono

lean_lib FrenMirToMonoTests

lean_lib FrenMonoToFo

lean_lib FrenMonoToFoTests

lean_lib FrenFoToFlat

lean_lib FrenFoToFlatTests

lean_lib FrenMirToLean

lean_lib FrenMirToLeanTests

lean_lib FrenFlatToLir

lean_lib FrenFlatToLirTests

lean_lib FrenLirToOir

lean_lib FrenLirToOirTests

lean_lib FrenOirToSmt

lean_lib FrenOirToSmtTests

lean_lib FrenEval

lean_lib FrenEvalTests

lean_lib FrenLirEval

lean_lib FrenLirEvalTests

lean_lib FrenGen

lean_lib FrenGenTests

lean_lib FrenCli2

lean_lib FrenCli2Tests

lean_lib FrenHosted2

lean_lib FrenHosted2Tests

-- Standalone scheduler kernels: only Lean core/Std, independent of Fren.
lean_lib Heavy where
  globs := #[.submodules `Heavy]
  roots := #[]

-- Shared by the Lean library and the binary; depends only on Lean core, and
-- on the parser of the binary, with which `FrenCore.Lint` reads the Fren
-- quotations of its fixes when it is built (`FrenCli.Quote`). All of its
-- modules, not only those that the module `FrenCore` imports.
--
-- Neither it nor `Fren` is precompiled (`precompileModules`), although the
-- hosted front end's elaborators, which run on every build of `Reqs`, would
-- then run as native code rather than in Lean's interpreter: a module that
-- imports a precompiled one waits for its C code to be compiled and linked,
-- which put `Fren.Elab`'s, some 13 s, on the build's critical path, for a
-- second or so less in each of the slowest modules of `Reqs`. With
-- `Fren.Elab` at `-O0` (below), it is still no faster: `Reqs` then waits
-- for the C code of every module of `Fren` and of `FrenCore`, and for their
-- shared libraries, for 1–3 s less CPU in `Reqs.Lang` before its chapter
-- split, and in `Reqs.Lint` and `Reqs.Check`. (Precompiling needs the
-- libraries layered by imports, with the modules that `Fren.Elab` imports
-- in a library of their own, and `roots := #[]` on each library with no root
-- module, so that Lake loads it with `--load-dynlib` rather than as a plugin.)
@[default_target] lean_lib FrenCore where
  globs := #[.andSubmodules `FrenCore]
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- `FrenCoreCodes` reads the explanations of the codes, a Markdown file
-- each in `src/FrenCore/Codes`, when it is compiled, hence `needs`. It is
-- not a module of `FrenCore`, whose globs would build it without them.
lean_lib FrenCoreCodes where
  needs := #[`@/codes_md]
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

input_dir codes_md where
  path := "src/FrenCore/Codes"
  text := true
  filter := .extension #["md"]

-- The Lean-hosted front end (uses lean-smt).
@[default_target] lean_lib Fren where
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- `Fren.Elab` and its submodules, the hosted elaborators, are compiled
-- without optimization. Only the executables that load `Fren` run this C code
-- (`fren_test`, `fren_fuzz_frontends`, `fren_coverage`): `lean` interprets
-- the elaborators on every build of `Reqs`. On the original single module,
-- clang took 17 s at `-O3` on the path of `lake test`'s build, and 3 s at
-- `-O0`, with no longer test runs. The library gives every elaborator module
-- these compiler arguments (see the top of this file).
lean_lib FrenElab where
  globs := #[.andSubmodules `Fren.Elab]
  moreLeancArgs := coverageArgs ++ #["-O0"]
  moreLeanArgs := coverageLeanArgs

-- `lake build` only elaborates Fren's own requirements, which the `impl`s of
-- `Impls` need, and runs none of their checks (`fren.runChecks`): `fren
-- check` checks them, in `lake test`'s `ownSpec` job, with the same checks
-- at the same evidence. `lake -R -Kcheck_reqs=1 build Reqs` checks them in
-- Lean too, as the `lean ci` workflow does on `main`, and its
-- `ownSpecAgreement` job compares the two front ends' messages
-- (`Reqs/dev/Testing#own-requirements`).
def reqsArgs : Array String :=
  if (get_config? check_reqs).isSome then #[] else #["-Dweak.fren.runChecks=false"]

-- Fren's own requirements, written in Fren, elaborated on every build. They
-- are Markdown specs (`src/Reqs/*.md`) read by `#fren_md`, which Lake can't
-- see, hence `needs`. The libraries after `Reqs` hold its modules by the
-- specs that they read, so that editing a spec rebuilds only the modules
-- that read it, and those that import them; a module that none of them
-- lists is in `Reqs`, which needs every spec. The root `Reqs` imports them,
-- so each is built in the last library that has it (see the top of this
-- file). `lake test`'s `libraries` job checks that each module reads only
-- the specs of its library.
@[default_target] lean_lib Reqs where
  globs := #[`Reqs, `Spec.All]
  needs := #[`@/reqs_md]
  moreLeanArgs := reqsArgs

input_dir reqs_md where
  path := "src/Reqs"
  text := true
  filter := .extension #["md"]

lean_lib ReqsChapters where
  globs := #[`Reqs.Check, `Reqs.Cli, `Reqs.Eval, `Reqs.Fmt, `Reqs.Generated, `Reqs.Impl, `Reqs.Markdown, `Reqs.Models, `Reqs.Mutate, `Reqs.Trace, `Reqs.View]
  needs := #[`@/reqs_chapters_md]
  moreLeanArgs := reqsArgs

-- Add after scaffold 978 merges; each module has exactly its own input.
lean_lib SpecLanguageIndex where
  globs := #[`Spec.Language.Index]
  needs := #[`@/spec_language_index_md]

input_file spec_language_index_md where
  path := "src/Spec/Language/index.md"
  text := true

lean_lib SpecLanguageLexicalStructure where
  globs := #[`Spec.Language.LexicalStructure]
  needs := #[`@/spec_language_lexical_structure_md]

input_file spec_language_lexical_structure_md where
  path := "src/Spec/Language/LexicalStructure.md"
  text := true

lean_lib SpecLanguageSyntax where
  globs := #[`Spec.Language.Syntax]
  needs := #[`@/spec_language_syntax_md]

input_file spec_language_syntax_md where
  path := "src/Spec/Language/Syntax.md"
  text := true

lean_lib SpecLanguageNamesAndScope where
  globs := #[`Spec.Language.NamesAndScope]
  needs := #[`@/spec_language_names_and_scope_md]

input_file spec_language_names_and_scope_md where
  path := "src/Spec/Language/NamesAndScope.md"
  text := true

-- Lean support that spec chapters share: it reads no spec of its own.
lean_lib SpecSupport where
  globs := #[`Spec.Support.Tables, `Spec.Support.Core]

lean_lib SpecLanguageTypes where
  globs := #[`Spec.Language.Types, `Spec.Language.Types.Adequacy]
  needs := #[`@/spec_language_types_md]

input_file spec_language_types_md where
  path := "src/Spec/Language/Types.md"
  text := true

lean_lib SpecLanguageStaticSemantics where
  globs := #[`Spec.Language.StaticSemantics]
  needs := #[`@/spec_language_static_semantics_md]

input_file spec_language_static_semantics_md where
  path := "src/Spec/Language/StaticSemantics.md"
  text := true

lean_lib SpecLanguageDenotationalSemantics where
  globs := #[`Spec.Language.DenotationalSemantics]
  needs := #[`@/spec_language_denotational_semantics_md]

input_file spec_language_denotational_semantics_md where
  path := "src/Spec/Language/DenotationalSemantics.md"
  text := true

lean_lib SpecLanguageDynamicSemantics where
  globs := #[`Spec.Language.DynamicSemantics]
  needs := #[`@/spec_language_dynamic_semantics_md]

input_file spec_language_dynamic_semantics_md where
  path := "src/Spec/Language/DynamicSemantics.md"
  text := true

lean_lib SpecLanguagePatterns where
  globs := #[`Spec.Language.Patterns]
  needs := #[`@/spec_language_patterns_md]

input_file spec_language_patterns_md where
  path := "src/Spec/Language/Patterns.md"
  text := true

lean_lib SpecLanguageFunctionsAndRecursion where
  globs := #[`Spec.Language.FunctionsAndRecursion]
  needs := #[`@/spec_language_functions_and_recursion_md]

input_file spec_language_functions_and_recursion_md where
  path := "src/Spec/Language/FunctionsAndRecursion.md"
  text := true

lean_lib SpecLanguageProcedures where
  globs := #[`Spec.Language.Procedures]
  needs := #[`@/spec_language_procedures_md]

input_file spec_language_procedures_md where
  path := "src/Spec/Language/Procedures.md"
  text := true

lean_lib SpecLanguagePropertiesAndChecks where
  globs := #[`Spec.Language.PropertiesAndChecks]
  needs := #[`@/spec_language_properties_and_checks_md]

input_file spec_language_properties_and_checks_md where
  path := "src/Spec/Language/PropertiesAndChecks.md"
  text := true

lean_lib SpecLanguageModulesAndViews where
  globs := #[`Spec.Language.ModulesAndViews]
  needs := #[`@/spec_language_modules_and_views_md]

input_file spec_language_modules_and_views_md where
  path := "src/Spec/Language/ModulesAndViews.md"
  text := true

lean_lib SpecToolingIndex where
  globs := #[`Spec.Tooling.Index]
  needs := #[`@/spec_tooling_index_md]

input_file spec_tooling_index_md where
  path := "src/Spec/Tooling/index.md"
  text := true

lean_lib SpecToolingEvidence where
  globs := #[`Spec.Tooling.Evidence]
  needs := #[`@/spec_tooling_evidence_md]

input_file spec_tooling_evidence_md where
  path := "src/Spec/Tooling/Evidence.md"
  text := true

lean_lib SpecToolingDiagnosticsAndLints where
  globs := #[`Spec.Tooling.DiagnosticsAndLints]
  needs := #[`@/spec_tooling_diagnostics_and_lints_md]

input_file spec_tooling_diagnostics_and_lints_md where
  path := "src/Spec/Tooling/DiagnosticsAndLints.md"
  text := true

lean_lib SpecToolingFormatting where
  globs := #[`Spec.Tooling.Formatting]
  needs := #[`@/spec_tooling_formatting_md]

input_file spec_tooling_formatting_md where
  path := "src/Spec/Tooling/Formatting.md"
  text := true

lean_lib SpecLanguageLeanInterop where
  globs := #[`Spec.Language.LeanInterop]
  needs := #[`@/spec_language_lean_interop_md]

input_file spec_language_lean_interop_md where
  path := "src/Spec/Language/LeanInterop.md"
  text := true

lean_lib SpecLanguageExample where
  globs := #[`Spec.Language.Example]
  needs := #[`@/spec_language_example_md]

input_file spec_language_example_md where
  path := "src/Spec/Language/Example.md"
  text := true

lean_lib SpecCompilerIndex where
  globs := #[`Spec.Compiler.Index]
  needs := #[`@/spec_compiler_index_md]

input_file spec_compiler_index_md where
  path := "src/Spec/Compiler/index.md"
  text := true

lean_lib SpecCompilerOverview where
  globs := #[`Spec.Compiler.Overview]
  needs := #[`@/spec_compiler_overview_md]

input_file spec_compiler_overview_md where
  path := "src/Spec/Compiler/Overview.md"
  text := true

lean_lib SpecCompilerBaseDefinitions where
  globs := #[`Spec.Compiler.BaseDefinitions]
  needs := #[`@/spec_compiler_base_definitions_md]

input_file spec_compiler_base_definitions_md where
  path := "src/Spec/Compiler/BaseDefinitions.md"
  text := true

lean_lib SpecCompilerBindings where
  globs := #[`Spec.Compiler.Bindings]
  needs := #[`@/spec_compiler_bindings_md]

input_file spec_compiler_bindings_md where
  path := "src/Spec/Compiler/Bindings.md"
  text := true

lean_lib SpecCompilerAstAndParsing where
  globs := #[`Spec.Compiler.AstAndParsing]
  needs := #[`@/spec_compiler_ast_and_parsing_md]

input_file spec_compiler_ast_and_parsing_md where
  path := "src/Spec/Compiler/AstAndParsing.md"
  text := true

lean_lib SpecCompilerHir where
  globs := #[`Spec.Compiler.Hir]
  needs := #[`@/spec_compiler_hir_md]

input_file spec_compiler_hir_md where
  path := "src/Spec/Compiler/Hir.md"
  text := true

lean_lib SpecCompilerThir where
  globs := #[`Spec.Compiler.Thir, `Spec.Compiler.Thir.Hir, `Spec.Compiler.Thir.Adequacy, `Spec.Compiler.Thir.Infer]
  needs := #[`@/spec_compiler_thir_md]

input_file spec_compiler_thir_md where
  path := "src/Spec/Compiler/Thir.md"
  text := true

lean_lib SpecCompilerDesugaring where
  globs := #[`Spec.Compiler.Desugaring]
  needs := #[`@/spec_compiler_desugaring_md]

input_file spec_compiler_desugaring_md where
  path := "src/Spec/Compiler/Desugaring.md"
  text := true

lean_lib SpecCompilerWalking where
  globs := #[`Spec.Compiler.Walking]
  needs := #[`@/spec_compiler_walking_md]

input_file spec_compiler_walking_md where
  path := "src/Spec/Compiler/Walking.md"
  text := true

lean_lib SpecCompilerEvaluator where
  globs := #[`Spec.Compiler.Evaluator]
  needs := #[`@/spec_compiler_evaluator_md]

input_file spec_compiler_evaluator_md where
  path := "src/Spec/Compiler/Evaluator.md"
  text := true

lean_lib SpecCompilerMir where
  globs := #[`Spec.Compiler.Mir]
  needs := #[`@/spec_compiler_mir_md]

input_file spec_compiler_mir_md where
  path := "src/Spec/Compiler/Mir.md"
  text := true

lean_lib SpecCompilerMonomorphization where
  globs := #[`Spec.Compiler.Monomorphization]
  needs := #[`@/spec_compiler_monomorphization_md]

input_file spec_compiler_monomorphization_md where
  path := "src/Spec/Compiler/Monomorphization.md"
  text := true

lean_lib SpecCompilerClosureSpecialization where
  globs := #[`Spec.Compiler.ClosureSpecialization]
  needs := #[`@/spec_compiler_closure_specialization_md]

input_file spec_compiler_closure_specialization_md where
  path := "src/Spec/Compiler/ClosureSpecialization.md"
  text := true

lean_lib SpecCompilerMatchCompilation where
  globs := #[`Spec.Compiler.MatchCompilation]
  needs := #[`@/spec_compiler_match_compilation_md]

input_file spec_compiler_match_compilation_md where
  path := "src/Spec/Compiler/MatchCompilation.md"
  text := true

lean_lib SpecCompilerLir where
  globs := #[`Spec.Compiler.Lir]
  needs := #[`@/spec_compiler_lir_md]

input_file spec_compiler_lir_md where
  path := "src/Spec/Compiler/Lir.md"
  text := true

lean_lib SpecCompilerOir where
  globs := #[`Spec.Compiler.Oir]
  needs := #[`@/spec_compiler_oir_md]

input_file spec_compiler_oir_md where
  path := "src/Spec/Compiler/Oir.md"
  text := true

lean_lib SpecCompilerSmt where
  globs := #[`Spec.Compiler.Smt]
  needs := #[`@/spec_compiler_smt_md]

input_file spec_compiler_smt_md where
  path := "src/Spec/Compiler/Smt.md"
  text := true

lean_lib SpecCompilerLeanEmission where
  globs := #[`Spec.Compiler.LeanEmission]
  needs := #[`@/spec_compiler_lean_emission_md]

input_file spec_compiler_lean_emission_md where
  path := "src/Spec/Compiler/LeanEmission.md"
  text := true

lean_lib SpecCompilerMetatheory where
  globs := #[`Spec.Compiler.Metatheory]
  needs := #[`@/spec_compiler_metatheory_md]

input_file spec_compiler_metatheory_md where
  path := "src/Spec/Compiler/Metatheory.md"
  text := true

lean_lib SpecCompilerExample where
  globs := #[`Spec.Compiler.Example]
  needs := #[`@/spec_compiler_example_md]

input_file spec_compiler_example_md where
  path := "src/Spec/Compiler/Example.md"
  text := true


-- The shared chapters in `src/Reqs` itself, excluding the separately built
-- ModuleReports chapter and the language chapters in its subdirectory.
input_dir reqs_chapters_md where
  path := "src/Reqs"
  text := true
  filter := .ofFn fun p => p.extension == some "md" && (p.parent.bind (·.fileName)) == some "Reqs" && p.fileName != some "ModuleReports.md"

lean_lib ReqsModuleReports where
  globs := #[`Reqs.ModuleReports]
  needs := #[`@/reqs_module_reports_md]
  moreLeanArgs := reqsArgs

input_file reqs_module_reports_md where
  path := "src/Reqs/ModuleReports.md"
  text := true

-- The language chapters share Fren's `lang` module, but each Lean module
-- needs only its own Markdown file. Neither this umbrella nor Base reads
-- Markdown; giving them a directory dependency would serialize the chapters
-- again on every edit.
lean_lib ReqsLang where
  globs := #[`Reqs.Lang, `Reqs.Lang.Base]
  moreLeanArgs := reqsArgs

lean_lib ReqsLangOverview where
  globs := #[`Reqs.Lang.Overview]
  needs := #[`@/reqs_lang_overview_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_overview_md where
  path := "src/Reqs/Lang/Overview.md"
  text := true

lean_lib ReqsLangLexical where
  globs := #[`Reqs.Lang.Lexical]
  needs := #[`@/reqs_lang_lexical_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_lexical_md where
  path := "src/Reqs/Lang/Lexical.md"
  text := true

lean_lib ReqsLangTypes where
  globs := #[`Reqs.Lang.Types]
  needs := #[`@/reqs_lang_types_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_types_md where
  path := "src/Reqs/Lang/Types.md"
  text := true

lean_lib ReqsLangSubsetTypes where
  globs := #[`Reqs.Lang.SubsetTypes]
  needs := #[`@/reqs_lang_subset_types_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_subset_types_md where
  path := "src/Reqs/Lang/SubsetTypes.md"
  text := true

lean_lib ReqsLangBooleanBlocks where
  globs := #[`Reqs.Lang.BooleanBlocks]
  needs := #[`@/reqs_lang_boolean_blocks_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_boolean_blocks_md where
  path := "src/Reqs/Lang/BooleanBlocks.md"
  text := true

lean_lib ReqsLangItems where
  globs := #[`Reqs.Lang.Items]
  needs := #[`@/reqs_lang_items_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_items_md where
  path := "src/Reqs/Lang/Items.md"
  text := true

lean_lib ReqsLangGenerics where
  globs := #[`Reqs.Lang.Generics]
  needs := #[`@/reqs_lang_generics_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_generics_md where
  path := "src/Reqs/Lang/Generics.md"
  text := true

lean_lib ReqsLangGenericFunctions where
  globs := #[`Reqs.Lang.GenericFunctions]
  needs := #[`@/reqs_lang_generic_functions_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_generic_functions_md where
  path := "src/Reqs/Lang/GenericFunctions.md"
  text := true

lean_lib ReqsLangTraits where
  globs := #[`Reqs.Lang.Traits]
  needs := #[`@/reqs_lang_traits_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_traits_md where
  path := "src/Reqs/Lang/Traits.md"
  text := true

lean_lib ReqsLangPrelude where
  globs := #[`Reqs.Lang.Prelude]
  needs := #[`@/reqs_lang_prelude_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_prelude_md where
  path := "src/Reqs/Lang/Prelude.md"
  text := true

lean_lib ReqsLangScope where
  globs := #[`Reqs.Lang.Scope]
  needs := #[`@/reqs_lang_scope_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_scope_md where
  path := "src/Reqs/Lang/Scope.md"
  text := true

lean_lib ReqsLangProcedures where
  globs := #[`Reqs.Lang.Procedures]
  needs := #[`@/reqs_lang_procedures_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_procedures_md where
  path := "src/Reqs/Lang/Procedures.md"
  text := true

lean_lib ReqsLangGlobal where
  globs := #[`Reqs.Lang.Global]
  needs := #[`@/reqs_lang_global_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_global_md where
  path := "src/Reqs/Lang/Global.md"
  text := true

lean_lib ReqsLangDecidability where
  globs := #[`Reqs.Lang.Decidability]
  needs := #[`@/reqs_lang_decidability_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_decidability_md where
  path := "src/Reqs/Lang/Decidability.md"
  text := true

lean_lib ReqsLangPatterns where
  globs := #[`Reqs.Lang.Patterns]
  needs := #[`@/reqs_lang_patterns_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_patterns_md where
  path := "src/Reqs/Lang/Patterns.md"
  text := true

lean_lib ReqsLangLet where
  globs := #[`Reqs.Lang.Let]
  needs := #[`@/reqs_lang_let_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_let_md where
  path := "src/Reqs/Lang/Let.md"
  text := true

lean_lib ReqsLangQuantifiers where
  globs := #[`Reqs.Lang.Quantifiers]
  needs := #[`@/reqs_lang_quantifiers_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_quantifiers_md where
  path := "src/Reqs/Lang/Quantifiers.md"
  text := true

lean_lib ReqsLangElementQuantifiers where
  globs := #[`Reqs.Lang.ElementQuantifiers]
  needs := #[`@/reqs_lang_element_quantifiers_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_element_quantifiers_md where
  path := "src/Reqs/Lang/ElementQuantifiers.md"
  text := true

lean_lib ReqsLangSemantics where
  globs := #[`Reqs.Lang.Semantics]
  needs := #[`@/reqs_lang_semantics_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_semantics_md where
  path := "src/Reqs/Lang/Semantics.md"
  text := true

lean_lib ReqsLangEvaluationRules where
  globs := #[`Reqs.Lang.EvaluationRules]
  needs := #[`@/reqs_lang_evaluation_rules_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_evaluation_rules_md where
  path := "src/Reqs/Lang/EvaluationRules.md"
  text := true

lean_lib ReqsLangExpressions where
  globs := #[`Reqs.Lang.Expressions]
  needs := #[`@/reqs_lang_expressions_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_expressions_md where
  path := "src/Reqs/Lang/Expressions.md"
  text := true

lean_lib ReqsLangHigherOrder where
  globs := #[`Reqs.Lang.HigherOrder]
  needs := #[`@/reqs_lang_higher_order_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_higher_order_md where
  path := "src/Reqs/Lang/HigherOrder.md"
  text := true

lean_lib ReqsLangRecursion where
  globs := #[`Reqs.Lang.Recursion]
  needs := #[`@/reqs_lang_recursion_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_recursion_md where
  path := "src/Reqs/Lang/Recursion.md"
  text := true

lean_lib ReqsLangScopeLaws where
  globs := #[`Reqs.Lang.ScopeLaws]
  needs := #[`@/reqs_lang_scope_laws_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_scope_laws_md where
  path := "src/Reqs/Lang/ScopeLaws.md"
  text := true

lean_lib ReqsLangModulesAndInterfaces where
  globs := #[`Reqs.Lang.ModulesAndInterfaces]
  needs := #[`@/reqs_lang_modules_and_interfaces_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_modules_and_interfaces_md where
  path := "src/Reqs/Lang/ModulesAndInterfaces.md"
  text := true

lean_lib ReqsLangImplementations where
  globs := #[`Reqs.Lang.Implementations]
  needs := #[`@/reqs_lang_implementations_md]
  moreLeanArgs := reqsArgs

input_file reqs_lang_implementations_md where
  path := "src/Reqs/Lang/Implementations.md"
  text := true

lean_lib ReqsCalls where
  globs := #[`Reqs.Calls]
  needs := #[`@/reqs_calls_md]
  moreLeanArgs := reqsArgs

input_file reqs_calls_md where
  path := "src/Reqs/Lang/Calls.md"
  text := true

lean_lib ReqsModules where
  globs := #[`Reqs.Modules]
  needs := #[`@/reqs_modules_md]
  moreLeanArgs := reqsArgs

input_file reqs_modules_md where
  path := "src/Reqs/Lang/Modules.md"
  text := true

lean_lib ReqsRefine where
  globs := #[`Reqs.Refine]
  needs := #[`@/reqs_refine_md]
  moreLeanArgs := reqsArgs

input_file reqs_refine_md where
  path := "src/Reqs/Lang/Refinement.md"
  text := true

-- Each lint group has its own Markdown dependency. The umbrella reads
-- no Markdown; subchapters in a group elaborate in parallel where their
-- imports allow it. A new chapter can be read with one #fren_md in its
-- group's wrapper; the binary tests follow the wrappers too. A new
-- top-level wrapper needs its own library and Markdown input below.
lean_lib ReqsLint where
  globs := #[`Reqs.Lint]
  moreLeanArgs := reqsArgs

lean_lib ReqsLintBase where
  globs := #[`Reqs.Lint.Base]
  needs := #[`@/reqs_lint_base_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_base_md where
  path := "src/Reqs/Lint.md"
  text := true

lean_lib ReqsLintMeaning where
  globs := #[`Reqs.Lint.Meaning]
  needs := #[`@/reqs_lint_meaning_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_meaning_md where
  path := "src/Reqs/Lint/Meaning.md"
  text := true

lean_lib ReqsLintUnused where
  globs := #[`Reqs.Lint.Unused]
  needs := #[`@/reqs_lint_unused_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_unused_md where
  path := "src/Reqs/Lint/Unused.md"
  text := true

lean_lib ReqsLintNonstandardStyle where
  globs := #[`Reqs.Lint.NonstandardStyle]
  needs := #[`@/reqs_lint_nonstandard_style_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_nonstandard_style_md where
  path := "src/Reqs/Lint/NonstandardStyle.md"
  text := true

lean_lib ReqsLintStyle where
  globs := #[.andSubmodules `Reqs.Lint.Style]
  needs := #[`@/reqs_lint_style_md, `@/reqs_lint_style_chapters_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_style_md where
  path := "src/Reqs/Lint/Style.md"
  text := true

input_dir reqs_lint_style_chapters_md where
  path := "src/Reqs/Lint/Style"
  text := true
  filter := .extension #["md"]

lean_lib ReqsLintComplexity where
  globs := #[.andSubmodules `Reqs.Lint.Complexity]
  needs := #[`@/reqs_lint_complexity_md, `@/reqs_lint_complexity_chapters_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_complexity_md where
  path := "src/Reqs/Lint/Complexity.md"
  text := true

input_dir reqs_lint_complexity_chapters_md where
  path := "src/Reqs/Lint/Complexity"
  text := true
  filter := .extension #["md"]

lean_lib ReqsLintSuspicious where
  globs := #[.andSubmodules `Reqs.Lint.Suspicious]
  needs := #[`@/reqs_lint_suspicious_md, `@/reqs_lint_suspicious_chapters_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_suspicious_md where
  path := "src/Reqs/Lint/Suspicious.md"
  text := true

input_dir reqs_lint_suspicious_chapters_md where
  path := "src/Reqs/Lint/Suspicious"
  text := true
  filter := .extension #["md"]

lean_lib ReqsLintPedantic where
  globs := #[.andSubmodules `Reqs.Lint.Pedantic]
  needs := #[`@/reqs_lint_pedantic_md, `@/reqs_lint_pedantic_chapters_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_pedantic_md where
  path := "src/Reqs/Lint/Pedantic.md"
  text := true

input_dir reqs_lint_pedantic_chapters_md where
  path := "src/Reqs/Lint/Pedantic"
  text := true
  filter := .extension #["md"]

lean_lib ReqsLintRestriction where
  globs := #[`Reqs.Lint.Restriction]
  needs := #[`@/reqs_lint_restriction_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_restriction_md where
  path := "src/Reqs/Lint/Restriction.md"
  text := true

lean_lib ReqsLintDecidability where
  globs := #[`Reqs.Lint.Decidability]
  needs := #[`@/reqs_lint_decidability_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_decidability_md where
  path := "src/Reqs/Lint/Decidability.md"
  text := true

lean_lib ReqsLintPrinting where
  globs := #[`Reqs.Lint.Printing]
  needs := #[`@/reqs_lint_printing_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_printing_md where
  path := "src/Reqs/Lint/Printing.md"
  text := true

lean_lib ReqsLintRewrites where
  globs := #[`Reqs.Lint.Rewrites]
  needs := #[`@/reqs_lint_rewrites_md]
  moreLeanArgs := reqsArgs

input_file reqs_lint_rewrites_md where
  path := "src/Reqs/Lint/Rewrites.md"
  text := true

lean_lib ReqsDev where
  globs := #[`Reqs.Testing]
  needs := #[`@/reqs_dev_md]
  moreLeanArgs := reqsArgs

input_dir reqs_dev_md where
  path := "src/Reqs/dev"
  text := true
  filter := .extension #["md"]

-- Fren's own code linked to its requirements with `impl`. It imports both
-- the requirements and the code, so that neither depends on the other. A
-- `tested` claim reads the tests, so its module's library needs them: only
-- `Impls.Evidence`, `Impls.Lint` and `Impls.Trace` make such claims, in
-- `ImplsTested`, so that editing a test rebuilds only those three, and a new
-- module of `Impls` needs no entry here. The root `Impls`, which the library
-- `Impls` builds, imports them, so they are built in `ImplsTested`, the last
-- library that has them (see the top of this file). A module that makes one
-- elsewhere fails `lake test`'s `libraries` job, which also checks that
-- `testReaders` in `src/FrenTestMain.lean` lists these three. The files
-- named by their `tested` claims and the converse scan (`fren.testGlobs`)
-- must be among their library's actual `needs`; an unreadable dependency
-- declaration fails the job.
@[default_target] lean_lib Impls

lean_lib ImplsTested where
  globs := #[`Impls.Evidence, `Impls.Lint, `Impls.Trace]
  needs := #[`@/tests, `@/test_lean, `@/test_files_lean, `@/test_main, `@/heavy_test_py]

input_file heavy_test_py where
  path := "scripts/heavy_test.py"
  text := true

input_dir tests where
  path := "test"
  text := true
  filter := .star

input_dir test_lean where
  path := "src/FrenTest"
  text := true
  filter := .extension #["lean"]

input_dir test_files_lean where
  path := "src/FrenTestFiles"
  text := true
  filter := .extension #["lean"]

input_file test_main where
  path := "src/FrenTestMain.lean"
  text := true

-- Regression tests: each file checks its own messages with `#guard_msgs`.
@[default_target] lean_lib FrenTest where globs := #[`FrenTest.+]

-- The tests that read Markdown or `.fren` files with `#fren_md`: the
-- fixtures in `src/FrenTestFiles`, and two ui tests, hence `needs`, so that
-- editing one rebuilds them. They are not modules of `FrenTest`, whose globs
-- would build them without these files. `lake test`'s `libraries` job
-- checks that no other test reads a file, and that these, and the files
-- that they read, read only files that this library needs.
@[default_target] lean_lib FrenTestFiles where
  globs := #[`FrenTestFiles.+]
  needs := #[`@/test_fixtures, `@/test_lambda_match, `@/test_multi_match_names]

input_dir test_fixtures where
  path := "src/FrenTestFiles"
  text := true
  filter := .extension #["md", "fren"]

input_file test_lambda_match where
  path := "test/ui/lang/lambda_match.fren"
  text := true

input_file test_multi_match_names where
  path := "test/ui/lang/multi_match_names.fren"
  text := true

-- The example specs' Lean implementations, each proved to meet the spec it
-- reads with `#fren_md`, hence `needs` (the `.fren` specs only: an example
-- that reads a Markdown spec needs that file too). Each is listed in
-- `globs`, as there is no root module.
@[default_target] lean_lib Examples where
  srcDir := "../examples"
  globs := #[`Arith, `Rle, `Stlc, `Stoplight]
  needs := #[`@/examples_fren]

input_dir examples_fren where
  path := "examples"
  text := true
  filter := .extension #["fren"]

-- `__isoc23_strtol` and `__isoc23_fscanf`, which cvc5's static Linux release
-- calls but the older glibc that Lean links executables against lacks
-- (`c/glibc_c23.c`). Linked into every executable; unused elsewhere. Lean
-- links with lld, which resolves archives in any order on the link line.
target glibc_c23.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "glibc_c23.c")
  buildO (pkg.buildDir / "c" / "glibc_c23.o") src #[] #["-std=gnu17", "-fPIC", "-O2"]

extern_lib glibc_c23 pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "glibc_c23") #[← glibc_c23.o.fetch]

-- Process ownership primitives of Fren2's solver transport and test
-- runner (`c/fren2_process.c`, bound in `FrenOirToSmt.Process`): observing
-- a child's exit without reaping it, group signals and reaping, signal
-- watches, subreaping and pidfds, which Lean's `IO.Process` lacks. Linked
-- into every executable, like `glibc_c23`.
target fren2_process.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "fren2_process.c")
  buildO (pkg.buildDir / "c" / "fren2_process.o") src #["-I", (← getLeanIncludeDir).toString] #["-std=gnu17", "-fPIC", "-O2"]

extern_lib fren2_process pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "fren2_process") #[← fren2_process.o.fetch]

-- `malloc`, and the functions around it, by the mimalloc that Lean's
-- runtime links in, on Linux (`c/mimalloc_malloc.c`), so that cvc5
-- allocates with it. Linked into every executable, as an object of its
-- own (`moreLinkObjs`), never into a library that a process could load
-- after it had started allocating with glibc's `malloc`.
target mimalloc_malloc.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "mimalloc_malloc.c")
  buildO (pkg.buildDir / "c" / "mimalloc_malloc.o") src #["-I", (← getLeanIncludeDir).toString] #["-std=gnu17", "-fPIC", "-O2"]

-- And for the executables that run the Lean-hosted front end, whose
-- solvers are never freed, mimalloc commits its arenas' memory as it needs
-- it (`c/mimalloc_lazy_commit.c`).
target mimalloc_lazy_commit.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "mimalloc_lazy_commit.c")
  buildO (pkg.buildDir / "c" / "mimalloc_lazy_commit.o") src #["-I", (← getLeanIncludeDir).toString] #["-std=gnu17", "-fPIC", "-O2"]

-- Process-local core protection after exec, only for the test driver's
-- explicitly protected children (`c/native_test_core.c`).
target native_test_core.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "native_test_core.c")
  buildO (pkg.buildDir / "c" / "native_test_core.o") src #["-I", (← getLeanIncludeDir).toString] #["-std=gnu17", "-fPIC", "-O2"]

-- The standalone binary for `.fren` files: a native executable with cvc5
-- linked in, needing no .olean files at runtime. There is no module `FrenCli`,
-- so the library is its modules.
--
-- Unlike `Fren.Elab`, `FrenCli.Elab` and its support modules keep `-O3`.
-- Before the module split, clang took some 40 s on its C code (locally),
-- spread over its functions since no function elaborates every kind of
-- item (`FrenCli.elabItem`). At `-O0` (3 s), the binary elaborated 40–50%
-- slower, and `lake test`, whose mutation jobs elaborate Fren's own
-- requirements once for each mutant, took about 25% more CPU;
-- `-O1 -fno-inline` (12 s) still cost a mutation job 10%.
lean_lib FrenCli where
  globs := #[.submodules `FrenCli]
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

@[default_target] lean_exe fren where
  root := `FrenCli.Main
  moreLinkObjs := #[`@/mimalloc_malloc.o]
  moreLinkArgs := coverageLinkArgs

-- `lake test`: ui tests through both front ends, and snapshot tests for the
-- binary. It loads Fren's Lean environment at runtime, hence the interpreter.
lean_exe fren_test where
  -- The executable smoke job must exercise a freshly built fuzzer.
  needs := #[`@/fren_fuzz_frontends, `@/fren2_test,
    `@/FrenBase, `@/FrenBaseTests, `@/FrenSource, `@/FrenSourceTests, `@/FrenDiag,
    `@/FrenDiagTests, `@/FrenSexp, `@/FrenSexpTests, `@/FrenProp, `@/FrenPropTests, `@/FrenAst,
    `@/FrenAstTests, `@/FrenModule, `@/FrenModuleTests, `@/FrenExpr, `@/FrenExprTests, `@/FrenMir,
    `@/FrenMirTests, `@/FrenLir, `@/FrenLirTests, `@/FrenOir, `@/FrenOirTests, `@/FrenParse,
    `@/FrenParseTests, `@/FrenAstToHir, `@/FrenAstToHirTests, `@/FrenHirToThir,
    `@/FrenHirToThirTests, `@/FrenWalking, `@/FrenWalkingTests, `@/FrenThirDesugar, `@/FrenThirDesugarTests, `@/FrenThirToMir,
    `@/FrenThirToMirTests, `@/FrenMirToMono, `@/FrenMirToMonoTests, `@/FrenMonoToFo,
    `@/FrenMonoToFoTests, `@/FrenFoToFlat, `@/FrenFoToFlatTests, `@/FrenMirToLean,
    `@/FrenMirToLeanTests, `@/FrenFlatToLir, `@/FrenFlatToLirTests, `@/FrenLirToOir,
    `@/FrenLirToOirTests, `@/FrenOirToSmt, `@/FrenOirToSmtTests, `@/FrenEval, `@/FrenEvalTests,
    `@/FrenLirEval, `@/FrenLirEvalTests, `@/FrenGen, `@/FrenGenTests, `@/FrenCli2,
    `@/FrenCli2Tests, `@/FrenHosted2, `@/FrenHosted2Tests]
  root := `FrenTestMain
  moreLinkObjs := #[`@/mimalloc_malloc.o, `@/mimalloc_lazy_commit.o, `@/native_test_core.o]
  supportInterpreter := true
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_fuzz`: random specs, checked by `fren check` and by brute
-- force from the evaluator (`Reqs/dev/Testing`). A default target, so that
-- `lake build` keeps it building.
@[default_target] lean_exe fren_fuzz where
  root := `FrenFuzz
  moreLinkObjs := #[`@/mimalloc_malloc.o]
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_coverage GCOV...`: the declarations that `lake test` did
-- not run, after a build with `-Kcoverage` (`Reqs/dev/Testing#coverage`).
-- It loads Fren's Lean environment, hence the interpreter.
lean_exe fren_coverage where
  root := `FrenCoverage
  moreLinkObjs := #[`@/mimalloc_malloc.o, `@/mimalloc_lazy_commit.o]
  supportInterpreter := true
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_fuzz_frontends`: random specs, checked by both front ends,
-- whose reports must agree (`Reqs/dev/Testing`). It loads Fren's Lean
-- environment at runtime, hence the interpreter. The fuzzer is the module
-- `FrenTest.FuzzFrontends.Main`; `fren_test` imports `Checks` and `Corpus`
-- to check its fixed corpus. An executable's root is in no library, so no
-- module may import it, since Lake would then use a stale `.olean` of it.
lean_exe fren_fuzz_frontends where
  root := `FrenFuzzFrontends
  moreLinkObjs := #[`@/mimalloc_malloc.o, `@/mimalloc_lazy_commit.o]
  supportInterpreter := true
  moreLinkArgs := coverageLinkArgs

-- Default S-expression checks and selected registered textual tests.
lean_exe fren2_test where
  needs := #[`@/FrenTextDemoTests, `@/FrenTextTestsTests, `@/fren2_check, `@/fren2_fake_solver]
  root := `Fren2TestMain

-- Ordinary single-file Fren2 source checker; runtime assets ship with this tree.
lean_exe fren2_check where
  root := `Fren2CheckMain

-- Owned solver failures for the transport and command controls of
-- `fren2_test`; never solver evidence.
lean_exe fren2_fake_solver where
  root := `Fren2FakeSolver
