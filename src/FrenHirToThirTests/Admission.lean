module

public import FrenHirToThirTests.Support

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir

def runAdmission : IO Unit := do
  let r ← resolved "mod m\nenum E { A, B }\nfn f(x: Int, y: Bool): Int := let x := x in if y then x else 0"
  let .ok a := admit r | throw (IO.userError "actual producer rejected")
  require (a.val == r) "admission retained different input"
  let mut rejectedCount := 0
  let rejects (changed : Resolved) : IO Unit := do
    let .error d := check changed | throw (IO.userError "edited resolved data admitted")
    require (d.code.isNone && d.headline == "walking type error: incoherent resolved input")
      "admission must precede type traversal"
  for i in [:r.references.size] do
    let some ref := r.references[i]? | throw (IO.userError "mutation reference")
    let mutations := #[{ref with role := if ref.role == .expression then .pattern else .expression},
      {ref with target := .local 999}, {ref with target := if ref.target == .intType then .boolType else .intType},
      {ref with context := r.scope.name :: ref.context},
      {ref with written := .builtin r.scope.name}]
    for changed in mutations do
      rejects {r with references := r.references.set! i changed}
      rejectedCount := rejectedCount + 1
    rejects {r with references := r.references.extract 0 i ++ r.references.extract (i + 1) r.references.size}
    rejectedCount := rejectedCount + 1
  let some first := r.references[0]? | throw (IO.userError "missing admission fixture reference")
  for changed in [
    {r with references := r.references.push first},
    {r with references := r.references.reverse},
    {r with scope := {r.scope with id := key "invented"}},
    {r with scope := {r.scope with items := #[]}},
    {r with scope := {r.scope with items := r.scope.items.reverse}},
    {r with document := {r.document with source := r.document.source ++ " junk"}},
    {r with document := {r.document with tape := #[]}},
    {r with document := {r.document with root := .declarations #[]}},
    {r with document := {r.document with entry := .context}}] do
    rejects changed
    rejectedCount := rejectedCount + 1
  for i in [:r.scope.items.size] do
    let some item := r.scope.items[i]? | throw (IO.userError "mutation item")
    for changed in [{item with kind := if item.kind == .function then .constructor else .function},
      {item with id := (key "Other").named item.name.text}] do
      rejects {r with scope := {r.scope with items := r.scope.items.set! i changed}}
      rejectedCount := rejectedCount + 1
  -- Specifically choose another in-range local index, not just an absurd one.
  for i in [:r.references.size] do
    let some ref := r.references[i]? | throw (IO.userError "mutation reference")
    if let .local index := ref.target then
      let other := if index == 0 then 1 else 0
      rejects {r with references := r.references.set! i {ref with target := .local other}}
      rejects {r with references := r.references.set! i {ref with context := ref.context.reverse}}
      rejectedCount := rejectedCount + 2
  -- Ill-typed producer output is admitted, then fails actual whole typing.
  let ill ← resolved "mod m\nfn f(x: Bool): Int := x + 1"
  require ((admit ill).isOk && !(check ill).isOk) "admission is not typing"
  require ((localType [] 0).isNone) "raw missing-local lookup fabricated a type"
  IO.println s!"typing admission: actual producer + admitted ill-typed tree; {rejectedCount} deleted/duplicate/stale/context/identity/document mutations rejected"

end FrenHirToThirTests
