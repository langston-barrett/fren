import Lake

open System Lake DSL

package fren where
  srcDir := "src"
  testDriver := "fren_test"
  version := v!"0.1.0"

-- Mathlib-free fork of lean-smt (the fork Veil uses).
require smt from git "https://github.com/verse-lab/lean-smt.git"@"v4.32.0-veil-no-mathlib"

-- Shared by the Lean library and the binary; depends only on Lean core.
@[default_target] lean_lib FrenCore

-- The Lean-hosted front end (uses lean-smt).
@[default_target] lean_lib Fren

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
lean_lib FrenCli where globs := #[.submodules `FrenCli]

@[default_target] lean_exe fren where root := `FrenCli.Main

-- `lake test`: ui tests through both front ends, and snapshot tests for the
-- binary. It loads Fren's Lean environment at runtime, hence the interpreter.
lean_exe fren_test where
  root := `FrenTestMain
  supportInterpreter := true

-- `lake exe fren_fuzz`: random specs, checked by `fren check` and by brute
-- force from the evaluator (`Reqs/dev/Testing`).
lean_exe fren_fuzz where root := `FrenFuzz
