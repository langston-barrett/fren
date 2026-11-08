import Lake
open Lake DSL System

package heavyObserve

lean_lib Heavy where
  srcDir := "../../src"
  globs := #[`Heavy.Process, `Heavy.Budget, `Heavy.Ownership, `Heavy.Forecast, `Heavy.CompilerForecast]

lean_lib BudgetAdapter

target observer.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "observer.c")
  let gate ← inputTextFile (pkg.dir / "budget.c")
  let src := src.zipWith (fun path _ => path) gate
  buildO (pkg.buildDir / "observer.o") src #["-I", (← getLeanIncludeDir).toString]
    #["-std=gnu17", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"]

extern_lib observer pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "observer") #[← observer.o.fetch]

@[default_target] lean_exe heavy_observe where
  root := `Main

lean_exe process_tests where
  root := `ProcessTests

lean_exe budget_session where
  root := `BudgetMain

lean_exe budget_tests where
  root := `BudgetTests

lean_exe compiler_advice where
  root := `ForecastMain
