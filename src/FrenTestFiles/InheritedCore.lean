-- keep-sorted start
import Fren.Literate
import FrenCli.Elab
import FrenCore.Check.Reporting
-- keep-sorted end
open Fren.Lang

-- fren-covers: lang::inherited_core
-- Inspect both readers' actual classifications, independently of whether
-- a solver happens to decide an outside-core query on this machine.
#fren_md "InheritedCore.fren"

private def incompleteMessages (path : Lean.Name) (core : Bool) : Bool :=
  [Fren.Core.CheckKind.realizable, .expect, .cover].all fun kind =>
    let r : Fren.Core.CheckResult :=
      { kind, comp := path, prop? := none, verdict := .inconclusive, detail := .unknown "INCOMPLETE" }
    let ms := Fren.Core.messages false r core
    ms.size == 1 && ms[0]!.severity == (if core then .error else .warning)

open Lean Elab Command in
elab "#check_inherited_core" : command => do
  let state ← Fren.getState
  for name in [`defined, `calling, `higher, `constants, `field, `contracts] do
    let some c := state.comps.get? (`inherited_core_test ++ name)
      | throwError "missing inherited-core procedure {name}"
    if c.decidable then throwError "{name} lost its dependency's opt-out"
    unless incompleteMessages c.path c.decidable do
      throwError "{name} reports an outside-core unknown as an internal error"
  for name in [`unused, `plain] do
    let some c := state.comps.get? (`inherited_core_test ++ name)
      | throwError "missing core procedure {name}"
    unless c.decidable do throwError "{name} inherited an unrelated opt-out"
  let some g := state.globals.get? `inherited_core_test.global
    | throwError "missing inherited-core global"
  if g.decidable then throwError "global lost its contract's opt-out"
  for name in [`bounded?, `wrapped?, `generic?, `higher?, `FLAG, `BOX, `first, `second, `third] do
    unless state.outsideCoreItems.contains (`inherited_core_test ++ name) do
      throwError "{name} did not retain its core classification"
  for name in [`apply?, `nat, `core, `uninterpreted] do
    if state.outsideCoreItems.contains (`inherited_core_test ++ name) then
      throwError "{name} retained a previous item's opt-out"
  liftTermElabM do
    let text ← IO.FS.readFile "src/FrenTestFiles/InheritedCore.fren"
    let chars := text.toList.toArray
    let .ok tokens := FrenCli.lex chars | throwError "fixture does not lex"
    let .ok (items, starts) := FrenCli.parseItems tokens chars | throwError "fixture does not parse"
    let st := (FrenCli.elabFile 0 chars items starts #[] #[] |>.run ({} : FrenCli.State).withPrelude).2
    if st.diags.any (·.severity == .error) then
      throwError "standalone fixture has static errors: {repr (st.diags.map (·.msg.headline))}"
    for name in [`defined, `calling, `higher, `constants, `field, `contracts, `unused, `plain] do
      let some c := st.comps.find? (·.path == `inherited_core_test ++ name)
        | throwError "missing standalone procedure {name}"
      unless c.decidable == (name == `unused || name == `plain) do
        throwError "standalone {name} has the wrong core classification"
      unless incompleteMessages c.path c.decidable do
        throwError "standalone {name} reports an unknown with the wrong severity"
    let some g := st.globals.find? (·.path == `inherited_core_test.global)
      | throwError "missing standalone global"
    if g.decidable then throwError "standalone global lost its contract's opt-out"
    for name in [`apply?, `nat, `core, `uninterpreted] do
      if st.outsideCoreItems.contains (`inherited_core_test ++ name) then
        throwError "standalone {name} retained a previous item's opt-out"
    for name in [`bounded?, `wrapped?, `generic?, `higher?, `FLAG, `BOX, `first, `second, `third] do
      unless st.outsideCoreItems.contains (`inherited_core_test ++ name) do
        throwError "standalone {name} did not retain its core classification"
    let imported := "mod inherited_core_import_test\nuse inherited_core_test::wrapped?\npub proc imported(n: Int): (y?) { ensure value: y? iff wrapped?(n) }\n"
    let chars := imported.toList.toArray
    let .ok tokens := FrenCli.lex chars | throwError "imported fixture does not lex"
    let .ok (items, starts) := FrenCli.parseItems tokens chars | throwError "imported fixture does not parse"
    let st := (FrenCli.elabFile 1 chars items starts #[] #[] |>.run st).2
    if st.diags.any (·.severity == .error) then
      throwError "imported fixture has static errors: {repr (st.diags.map (·.msg.headline))}"
    let some c := st.comps.find? (·.path == `inherited_core_import_test.imported)
      | throwError "missing standalone imported-core procedure"
    if c.decidable then throwError "a helper read from another file lost its opt-out"
    let rejected := "mod inherited_core_import_test\nuse inherited_core_test::defined\npub proc rejected(n: Int) { call r := defined(n)\n expect value: r.y? }\n"
    let chars := rejected.toList.toArray
    let .ok tokens := FrenCli.lex chars | throwError "rejected fixture does not lex"
    let .ok (items, starts) := FrenCli.parseItems tokens chars | throwError "rejected fixture does not parse"
    let st := (FrenCli.elabFile 2 chars items starts #[] #[] |>.run st).2
    unless st.diags.any (fun d => d.severity == .error && d.msg.code? == some "F0714") do
      throwError "a caller without its opt-out did not reject the inherited outside-core procedure"
#check_inherited_core
