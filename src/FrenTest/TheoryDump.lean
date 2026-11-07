-- keep-sorted start
import FrenTest.FuzzFrontends.Running
import FrenTest.Resolved
-- keep-sorted end

/-! # Structural theories (`Reqs/Cli#theories`) -/

namespace FrenTest.TheoryDump

#guard ((FrenCli.parseArgs {} ["check", "--dump=theories", "--dump=theories", "spec.fren"]).toOption.map
  (·.dumpTheories)) == some true
#guard (FrenCli.parseArgs {} ["trace", "--dump=theories", "spec.fren"]).toOption.isNone
#guard (FrenCli.parseArgs {} ["check", "--dump=theory", "spec.fren"]).toOption.isNone
#guard Fren.Core.theorySourceName (Fren.Core.preludeModule ++ `Option)
#guard !Fren.Core.theorySourceName (Lean.Name.mkNum `f 0 ++ `T)

-- Two imported generics with the same short name stay distinct even when
-- applied at a caller's symbolic type parameter. Reversing extraction order
-- must not alter the canonical view.
private def symbolic : Fren.Core.TheoryDumpInput :=
  { items := #[
      { item := { kind := .fnItem, path := `a.id, owner := `a, isPub := true },
        parameters := #[`T], types := #[.param 0 `T, .param 0 `T] },
      { item := { kind := .fnItem, path := `b.id, owner := `b, isPub := true },
        parameters := #[`T], types := #[.param 0 `T, .param 0 `T] },
      { item := { kind := .fnItem, path := `caller, owner := .anonymous, isPub := true },
        parameters := #[`T], types := #[.param 0 `T, .param 0 `T] }],
    genericUses := #[
      { file := 0, item := `caller, caller? := some `caller, callee := `a.id, targs := #[.param 0 `T] },
      { file := 0, item := `caller, caller? := some `caller, callee := `b.id, targs := #[.param 0 `T] }] }

#guard (Fren.Core.theoryDiagram symbolic).instances.size == 2
#guard (Fren.Core.theoryDiagram symbolic).instances.all fun i => (`caller).isPrefixOf i.name
#guard Fren.Core.dumpTheories (Fren.Core.theoryDiagram symbolic) ==
  Fren.Core.dumpTheories (Fren.Core.theoryDiagram { symbolic with
    items := symbolic.items.reverse, genericUses := symbolic.genericUses.reverse })

-- A trait's own Self and function are signature entries, not imports.
-- Actual imports retain their inclusions, and opening a local enum stays
-- an open morphism.
private def ownScope : Fren.Core.TheoryDumpInput :=
  { items := #[], uses := #[
      { module := `library, scope := `library.Sized, target := `library.Sized.Self, glob := false },
      { module := `library, scope := `library.Sized, target := `library.Sized.size, glob := false },
      { module := `client, target := `library.Sized, glob := false },
      { module := `library, scope := `library.Sized, target := `library.Sized.Choice, glob := true }] }

#guard (Fren.Core.theoryDiagram ownScope).morphisms.map (fun m => (m.kind, m.source, m.target)) ==
  #[("inclusion", `library.Sized, `client), ("open", `library.Sized.Choice, `library.Sized)]

/-- Check independent extractions, separate CLI streams, static errors, failed
checks, parallel loading and composition with the other dump flags. -/
def check (env : Lean.Environment) : IO (Array String) := do
  let mut failures := #[]
  let dir : System.FilePath := ".lake/theories-test"
  IO.FS.createDirAll dir
  for path in #["test/cli/args/dump_theories.fren", "test/ui/lang/theories.fren",
      "test/cli/args/dump_resolved.fren"] do
    let text ← IO.FS.readFile path
    let ran ← FuzzFrontends.runFrontends env (dir / "agreement.fren") text
    unless ran.comparison.found.isEmpty do
      failures := failures.push s!"{path}: front-end diagnostics differ:\n{ran.reports}"
    match ran.theories? with
    | some (a, b) =>
      if path == "test/ui/lang/theories.fren" then
        unless a.contains "(sentence \"theories::c::valid\" domain".toSlice && !a.contains "@1".toSlice do
          failures := failures.push "theories: a written clause was replaced by named-predicate checking leaves"
      unless a == b && !a.isEmpty do
        let stem := (System.FilePath.mk path).fileStem.getD "dump"
        IO.FS.writeFile (dir / s!"{stem}.native.txt") a
        IO.FS.writeFile (dir / s!"{stem}.hosted.txt") b
        failures := failures.push s!"{path}: structural theories differ (see {dir})"
    | none => failures := failures.push s!"{path}: no structural theories"
  let path := "test/ui/lean/dump_theories_bindings.fren"
  let (diags, _) ← Ui.hostedDiagnostics env path (← IO.FS.readFile path)
  unless diags.any (fun d => d.text.contains "(morphism interpretation".toSlice) &&
      diags.any (fun d => d.text.contains "(morphism implementation".toSlice && d.text.contains "(opaque".toSlice) do
    failures := failures.push s!"theories: missing opaque Lean interpretation or implementation: {diags.toList.map (·.text)}"
  for path in #["test/cli/args/dump_theories.fren", "test/cli/args/dump_theories_error.fren",
      "test/cli/args/dump_resolved_failed.fren", "test/cli/args/dump_resolved_markdown.md"] do
    let run (flags : Array String) := Resolved.run (#["check", "--color=never"] ++ flags ++ #[path])
    let plain ← run #["--jobs", "1"]
    let one ← run #["--jobs", "1", "--dump=theories"]
    let many ← run #["--jobs", "4", "--dump=theories", "--dump=theories"]
    unless one.stdout == many.stdout && one.stderr == plain.stderr && many.stderr == plain.stderr &&
        one.exitCode == plain.exitCode && many.exitCode == plain.exitCode do
      failures := failures.push s!"{path}: theories dumping changed diagnostics, exit status or job-count determinism"
    if path.endsWith "_error.fren" then
      unless one.stdout.isEmpty && one.exitCode == 2 do
        failures := failures.push s!"{path}: static error failed to suppress theories"
    else
      unless one.stdout.startsWith "; theories\n" && one.stdout.endsWith "; end of theories\n" do
        failures := failures.push s!"{path}: incomplete theory dump:\n{one.stderr}"
      if path.endsWith "_failed.fren" && one.exitCode != 1 then
        failures := failures.push s!"{path}: failed check did not fail"
      unless plain.stdout.isEmpty do failures := failures.push s!"{path}: plain check wrote to stdout"
  let library := dir / "library.fren"
  let client := dir / "client.fren"
  IO.FS.writeFile library "pub mod library\npub fn id<T>(x: T): T := x\n"
  IO.FS.writeFile client "mod client\nuse library::id\nproc c(x: Int): (det y: Int) { out y := id(x) }\n"
  let args := #["check", "--color=never", library.toString, client.toString]
  let one ← Resolved.run (args ++ #["--dump=theories", "--jobs", "1"])
  let many ← Resolved.run (args ++ #["--dump=theories", "--jobs", "4"])
  unless one.exitCode == 0 && one.stdout == many.stdout &&
      one.stdout.contains "(instantiation \"library::id<Int>\"".toSlice do
    failures := failures.push "theories: imported generic instance missing or parallel loading differs"
  let combined ← Resolved.run (args ++ #["--dump=resolved", "--dump=theories", "--dump=obligations", "--dump=smt"])
  let rest := combined.stdout
  let afterResolved := (rest.splitOn "; end of resolved\n")[1]?.getD ""
  unless combined.exitCode == one.exitCode && rest.startsWith "; resolved\n" &&
      afterResolved.startsWith one.stdout && rest.contains "; obligations\n".toSlice &&
      rest.contains "(check-sat)".toSlice do
    failures := failures.push "theories: combining dump flags lost output or changed exit status"
  return failures

end FrenTest.TheoryDump
