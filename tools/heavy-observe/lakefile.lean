import Lake
open Lake DSL System

package heavyObserve

lean_lib Heavy where
  srcDir := "../../src"
  globs := #[`Heavy.Process, `Heavy.Budget, `Heavy.Ownership, `Heavy.Forecast, `Heavy.CompilerForecast]

lean_lib BudgetAdapter

lean_lib CompilerRecords

target observer.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "observer.c")
  let gate ← inputTextFile (pkg.dir / "budget.c")
  let src := src.zipWith (fun path _ => path) gate
  buildO (pkg.buildDir / "observer.o") src #["-I", (← getLeanIncludeDir).toString]
    #["-std=gnu17", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"]

extern_lib observer pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "observer") #[← observer.o.fetch]

-- Use the pinned installation's runtime, as its lean executable does. This
-- avoids copying Lean's JSON/macro runtime into each private compiler overlay.
-- Installed toolchain assets must remain immutable, as for the overlay itself.
target leanRuntime _pkg : FilePath := do
  return Job.pure (← getLeanSharedLib)

@[default_target] lean_exe heavy_observe where
  root := `Main
  moreLinkObjs := #[leanRuntime]

lean_exe process_tests where
  root := `ProcessTests

lean_exe budget_session where
  root := `BudgetMain

lean_exe budget_tests where
  root := `BudgetTests

lean_exe compiler_advice where
  root := `ForecastMain
