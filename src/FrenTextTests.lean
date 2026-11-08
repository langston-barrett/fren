module

public import FrenTextTests.Runner
public meta import FrenTextTests.Runner
public meta import Lean

public section
namespace Fren.TextTests
open Lean Elab Command

meta section
register_option fren.textTests.bless : Bool := {
  defValue := false
  descr := "reserved: build-time blessing is unsupported; use fren2_test --bless"
}
end

syntax (name := fren_text_tests) "fren_text_tests" str : attr

meta initialize runnerAttr : ParametricAttribute String ← registerParametricAttribute {
  name := `fren_text_tests
  descr := "register a typed textual-test adapter under test/<Library>"
  getParam := fun name stx => do
    let `(attr| fren_text_tests $path:str) := stx | throwError "expected test directory"
    unless validDirectory path.getString do throwError "expected test/<Library>"
    let info ← getConstInfo name
    unless info.type == mkConst ``Runner do throwError "registered declaration must have type Fren.TextTests.Runner"
    return path.getString
}

private meta def registrations (env : Environment) : Array (Name × String) :=
  (env.constants.toList.toArray.filterMap fun (n, _) =>
    (runnerAttr.getParam? env n).map (n, ·)).qsort (fun a b => a.2 < b.2)

private meta def checkedRegistrations : CommandElabM (Array (Name × String)) := do
  let entries := registrations (← getEnv)
  for i in [:entries.size] do
    if i > 0 && entries[i-1]!.2 == entries[i]!.2 then
      throwError "duplicate text-test directory: {entries[i]!.2}"
  return entries

private meta unsafe def evalRunnerUnsafe (name : Name) : MetaM Runner :=
  Meta.evalExpr Runner (mkConst ``Runner) (mkConst name)

@[implemented_by evalRunnerUnsafe]
private meta opaque evalRunner (name : Name) : MetaM Runner

/-- Build-time checks only. Blessing is deliberately native-only because cached
Lean artifacts cannot safely represent a source-rewriting build action. -/
elab "#fren_tests " runner:ident : command => do
  if fren.textTests.bless.get (← getOptions) then
    throwError "build-time blessing is unsupported; use fren2_test --lib Library --bless"
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo runner
  let entries ← checkedRegistrations
  let some (_, directory) := entries.find? (·.1 == name)
    | throwError "{name} is not registered with fren_text_tests"
  let value ← liftTermElabM <| evalRunner name
  let start ← IO.monoMsNow
  let summary ← runDirectory ⟨directory, value⟩
  for d in summary.diagnostics do logError m!"{d}"
  if summary.selected == 0 then throwError "{directory}: no cases"
  logInfo m!"{directory}: {summary.selected} text cases ({(← IO.monoMsNow) - start} ms)"

/-- Materialize precisely the imported attribute registry for a native driver. -/
elab "fren_test_runners " name:ident : command => do
  let entries ← checkedRegistrations
  let values ← entries.mapM fun (runner, directory) => do
    let id := mkIdent runner
    let path := Syntax.mkStrLit directory
    `(term| (⟨$path, $id⟩ : Fren.TextTests.Registered))
  elabCommand (← `(command| def $name : Array Fren.TextTests.Registered := #[$values,*]))
end Fren.TextTests
