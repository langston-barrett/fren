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

-- Mathlib-free fork of lean-smt (the fork Veil uses).
require smt from git "https://github.com/verse-lab/lean-smt.git"@"v4.32.0-veil-no-mathlib"

-- Shared by the Lean library and the binary; depends only on Lean core.
-- All of its modules, not only those that the module `FrenCore` imports.
--
-- Neither it nor `Fren` is precompiled (`precompileModules`), although the
-- hosted front end's elaborators, which run on every build of `Reqs`, would
-- then run as native code rather than in Lean's interpreter: a module that
-- imports a precompiled one waits for its C code to be compiled and linked,
-- which put `Fren.Elab`'s, some 13 s, on the build's critical path, for a
-- second or so less in each of the slowest modules of `Reqs`.
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
  globs := #[`Reqs.Check, `Reqs.Cli, `Reqs.Eval, `Reqs.Fmt, `Reqs.Impl, `Reqs.Mutate, `Reqs.Trace, `Reqs.View]
  needs := #[`@/reqs_chapters_md]

-- The specs in `src/Reqs` itself, not in its subdirectories.
input_dir reqs_chapters_md where
  path := "src/Reqs"
  text := true
  filter := .ofFn fun p => p.extension == some "md" && (p.parent.bind (·.fileName)) == some "Reqs"

lean_lib ReqsLang where
  globs := #[`Reqs.Inst, `Reqs.Lang, `Reqs.Modules, `Reqs.Refine]
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
  globs := #[`Impls.Check, `Impls.Cli, `Impls.Eval, `Impls.Fmt, `Impls.Impl, `Impls.Inst, `Impls.Lang, `Impls.Modules,
    `Impls.Mutate, `Impls.PatternTypes, `Impls.Refine, `Impls.View]

-- Regression tests: each file checks its own messages with `#guard_msgs`.
@[default_target] lean_lib FrenTest where globs := #[`FrenTest.+]

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
