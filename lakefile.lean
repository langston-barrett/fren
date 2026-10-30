import Lake

open System Lake DSL

package fren where
  srcDir := "src"
  testDriver := "fren_test"
  version := v!"0.1.0"

-- `lake -R -Kcoverage=RUNTIME build` compiles the code whose coverage is
-- measured with gcov's counters, and links the executables that run it
-- with the profiling runtime at the path RUNTIME, which Lean's toolchain
-- lacks (`Reqs/dev/Testing#coverage`).
def coverageArgs : Array String := if (get_config? coverage).isSome then #["--coverage"] else #[]
-- The compiler inlines small functions, whose code then runs in their
-- callers, so that they would seem never to run.
def coverageLeanArgs : Array String := if (get_config? coverage).isSome then #["-Dcompiler.small=0"] else #[]
def coverageLinkArgs : Array String := match get_config? coverage with
  | some runtime => #[runtime]
  | none => #[]

-- Fren's fork of the Mathlib-free lean-smt that Veil uses (verse-lab's
-- `v4.32.0-veil-no-mathlib`), with three patches: under `trust`, the
-- preprocessing skips the proofs of the goal's simplification, which Fren
-- discards, and which take time quadratic in the number of binders;
-- inductive types with type parameters are translated as SMT-LIB parametric
-- datatypes (`Reqs/Lang/Generics`); and universe-polymorphic ones, Lean's
-- `Option` and `Except`, which the prelude's types are, at universe 0, with
-- a hygienic field named after its position (`Reqs/Lang/Prelude`). The
-- commit is on the fork's branch `parametric-datatypes-v3`, on top of
-- `parametric-datatypes-v2` and `trust-skip-proofs`.
require smt from git "https://github.com/langston-barrett/lean-smt.git"@"82f3143e407a3008c47069220a2a393410bd9d48"

-- Shared by the Lean library and the binary; depends only on Lean core.
-- All of its modules, not only those that the module `FrenCore` imports.
--
-- Neither it nor `Fren` is precompiled (`precompileModules`), although the
-- hosted front end's elaborators, which run on every build of `Reqs`, would
-- then run as native code rather than in Lean's interpreter: a module that
-- imports a precompiled one waits for its C code to be compiled and linked,
-- which put `Fren.Elab`'s, some 13 s, on the build's critical path, for a
-- second or so less in each of the slowest modules of `Reqs`. With
-- `Fren.Elab` at `-O0` (below), it is still no faster: `Reqs` then waits
-- for the C code of every module of `Fren` and of `FrenCore`, and for their
-- shared libraries, for 1–3 s less CPU in each of `Reqs.Lang`, `Reqs.Lint`
-- and `Reqs.Check`. (Precompiling needs the libraries layered by imports,
-- with the modules that `Fren.Elab` imports in a library of their own, and
-- `roots := #[]` on each library with no root module, so that Lake loads
-- it with `--load-dynlib` rather than as a plugin.)
@[default_target] lean_lib FrenCore where
  globs := #[.andSubmodules `FrenCore]
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- The Lean-hosted front end (uses lean-smt).
@[default_target] lean_lib Fren where
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- `Fren.Elab`, the hosted front end's elaborators, is compiled without
-- optimization. Only the executables that load `Fren` run its C code
-- (`fren_test`, `fren_fuzz_frontends`, `fren_coverage`): `lean` interprets
-- it on every build of `Reqs`. At `-O3`, clang took 17 s on it, on the path
-- of `lake test`'s build; at `-O0` it takes 3 s, and `lake test`'s run takes
-- no longer. (Lake places a module in the last library that has it.)
lean_lib FrenElab where
  globs := #[`Fren.Elab]
  moreLeancArgs := coverageArgs ++ #["-O0"]
  moreLeanArgs := coverageLeanArgs

-- Fren's own requirements, written in Fren and checked on every build. They
-- are Markdown specs (`src/Reqs/*.md`) read by `#fren_md`, which Lake can't
-- see, hence `needs`. The libraries after `Reqs` hold its modules by the
-- specs that they read, so that editing a spec rebuilds only the modules
-- that read it, and those that import them; a module that none of them
-- lists is in `Reqs`, which needs every spec. (Lake places a module in the
-- last library that has it.) `lake test`'s `libraries` job checks that each
-- module reads only the specs of its library.
@[default_target] lean_lib Reqs where needs := #[`@/reqs_md]

input_dir reqs_md where
  path := "src/Reqs"
  text := true
  filter := .extension #["md"]

lean_lib ReqsChapters where
  globs := #[`Reqs.Check, `Reqs.Cli, `Reqs.Eval, `Reqs.Fmt, `Reqs.Generated, `Reqs.Impl, `Reqs.Mutate, `Reqs.Trace, `Reqs.View]
  needs := #[`@/reqs_chapters_md]

-- The specs in `src/Reqs` itself, not in its subdirectories.
input_dir reqs_chapters_md where
  path := "src/Reqs"
  text := true
  filter := .ofFn fun p => p.extension == some "md" && (p.parent.bind (·.fileName)) == some "Reqs"

lean_lib ReqsLang where
  globs := #[`Reqs.Calls, `Reqs.Lang, `Reqs.Modules, `Reqs.Refine]
  needs := #[`@/reqs_lang_md]

input_dir reqs_lang_md where
  path := "src/Reqs/Lang"
  text := true
  filter := .extension #["md"]

lean_lib ReqsLint where
  globs := #[`Reqs.Lint]
  needs := #[`@/reqs_lint_md, `@/reqs_lint_chapter_md]

input_dir reqs_lint_md where
  path := "src/Reqs/Lint"
  text := true
  filter := .extension #["md"]

input_file reqs_lint_chapter_md where
  path := "src/Reqs/Lint.md"
  text := true

-- Fren's own code linked to its requirements with `impl`. It imports both
-- the requirements and the code, so that neither depends on the other. Its
-- `tested` claims read the tests, hence `needs`. Only `Impls`, `Impls.Lint`
-- and `Impls.Trace` make such claims (checked by `lake test`'s `libraries`
-- job), so the other modules are in `ImplsProofs`, which needs no tests,
-- and editing a test rebuilds only those three.
@[default_target] lean_lib Impls where needs := #[`@/tests, `@/test_lean, `@/test_main]

input_dir tests where
  path := "test"
  text := true
  filter := .star

input_dir test_lean where
  path := "src/FrenTest"
  text := true
  filter := .extension #["lean"]

input_file test_main where
  path := "src/FrenTestMain.lean"
  text := true

lean_lib ImplsProofs where
  globs := #[`Impls.Calls, `Impls.Chains, `Impls.Check, `Impls.Cli, `Impls.Enumeration, `Impls.Eval, `Impls.Fmt, `Impls.Generated, `Impls.HigherOrder,
    `Impls.Impl, `Impls.Lang, `Impls.Meaning, `Impls.Modules, `Impls.Mutate, `Impls.PatternTests, `Impls.PatternTypes, `Impls.Procedures, `Impls.Scope,
    `Impls.TypeFacts, `Impls.View]

-- Regression tests: each file checks its own messages with `#guard_msgs`.
@[default_target] lean_lib FrenTest where globs := #[`FrenTest.+]

-- The example specs' Lean implementations, each proved to meet the spec it
-- reads with `#fren_md`, hence `needs` (the `.fren` specs only: an example
-- that reads a Markdown spec needs that file too). Each is listed in
-- `globs`, as there is no root module.
@[default_target] lean_lib Examples where
  srcDir := "../examples"
  globs := #[`Arith, `Rle]
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

-- The standalone binary for `.fren` files: a native executable with cvc5
-- linked in, needing no .olean files at runtime. There is no module `FrenCli`,
-- so the library is its modules.
--
-- Unlike `Fren.Elab`, `FrenCli.Elab` keeps `-O3`, although clang takes
-- 23–30 s on its C code, most of it on `elabExpr`. At `-O0` (3 s), the
-- binary elaborates 40–50% slower, and `lake test`, whose mutation jobs
-- elaborate Fren's own requirements once for each mutant, took about 25%
-- more CPU; `-O1 -fno-inline` (12 s) still costs a mutation job 10%.
lean_lib FrenCli where
  globs := #[.submodules `FrenCli]
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

@[default_target] lean_exe fren where
  root := `FrenCli.Main
  moreLinkArgs := coverageLinkArgs

-- `lake test`: ui tests through both front ends, and snapshot tests for the
-- binary. It loads Fren's Lean environment at runtime, hence the interpreter.
lean_exe fren_test where
  root := `FrenTestMain
  supportInterpreter := true
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_fuzz`: random specs, checked by `fren check` and by brute
-- force from the evaluator (`Reqs/dev/Testing`). A default target, so that
-- `lake build` keeps it building.
@[default_target] lean_exe fren_fuzz where
  root := `FrenFuzz
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_coverage GCOV...`: the declarations that `lake test` did
-- not run, after a build with `-Kcoverage` (`Reqs/dev/Testing#coverage`).
-- It loads Fren's Lean environment, hence the interpreter.
lean_exe fren_coverage where
  root := `FrenCoverage
  supportInterpreter := true

-- `lake exe fren_fuzz_frontends`: random specs, checked by both front ends,
-- whose reports must agree (`Reqs/dev/Testing`). It loads Fren's Lean
-- environment at runtime, hence the interpreter.
lean_exe fren_fuzz_frontends where
  root := `FrenFuzzFrontends
  supportInterpreter := true
  moreLinkArgs := coverageLinkArgs
