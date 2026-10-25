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
@[default_target] lean_lib FrenCore where
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- The Lean-hosted front end (uses lean-smt).
@[default_target] lean_lib Fren where
  moreLeancArgs := coverageArgs
  moreLeanArgs := coverageLeanArgs

-- Fren's own requirements, written in Fren and checked on every build. They
-- are Markdown specs (`src/Reqs/*.md`) read by `#fren_md`, which Lake can't
-- see, hence `needs`.
@[default_target] lean_lib Reqs where needs := #[`@/reqs_md]

input_dir reqs_md where
  path := "src/Reqs"
  text := true
  filter := .extension #["md"]

-- Fren's own code linked to its requirements with `impl`. It imports both
-- the requirements and the code, so that neither depends on the other. Its
-- `tested` claims read the tests, hence `needs`.
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
-- force from the evaluator (`Reqs/dev/Testing`).
lean_exe fren_fuzz where
  root := `FrenFuzz
  moreLinkArgs := coverageLinkArgs

-- `lake exe fren_coverage GCOV...`: the declarations that `lake test` did
-- not run, after a build with `-Kcoverage` (`Reqs/dev/Testing#coverage`).
-- It loads Fren's Lean environment, hence the interpreter.
lean_exe fren_coverage where
  root := `FrenCoverage
  supportInterpreter := true
