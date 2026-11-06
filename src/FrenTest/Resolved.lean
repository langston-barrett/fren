-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-! # The resolved surface (`Reqs/Cli#resolved-surface`) -/

namespace FrenTest.Resolved

#guard ((FrenCli.parseArgs {} ["check", "--dump=resolved", "--dump=resolved", "spec.fren"]).toOption.map
  (·.dumpResolved)) == some true
#guard (FrenCli.parseArgs {} ["trace", "--dump=resolved", "spec.fren"]).toOption.isNone
#guard (FrenCli.parseArgs {} ["check", "--dump=resolve", "spec.fren"]).toOption.isNone

/-- Runs the CLI in a fresh copy of this driver, with its separate streams
and exit code, through the hidden `resolvedRun` job. -/
def run (args : Array String) : IO IO.Process.Output := do
  IO.Process.output { cmd := (← IO.appPath).toString, args := #["--job", "resolvedRun"] ++ args }

/-- Exercises the CLI's separate streams, both loading paths, repeated
flags, and successful, statically invalid and failed specs. Dumping must
leave diagnostics and exit status unchanged. -/
def check (bless : Bool) : IO (Array String) := do
  let mut failures := #[]
  -- Induction creates hidden functions whose synthetic syntax shares the
  -- claim's spans. It must not overwrite the claim's surface annotations.
  let src := "pub enum L { Nil, Cons(L) }\n\
    pub fn len(xs: L): Int := match xs { L::Nil => 0, L::Cons(tail) => 1 + len(tail) }\n\
    expect claim(xs: L) { expect same: len(xs) = len(xs) }\n"
  let st := FrenCli.elabText (FrenCli.initialState #[] none true) 0 src.toList.toArray
  if st.inductionBodies.isEmpty then
    failures := failures.push "resolved dump: the induction regression generated no induction function"
  for a in st.resolved?.getD #[] do
    if st.inductionBodies.toArray.any fun (p, _) => a.value.contains (FrenCli.resolvedPath p).toSlice then
      failures := failures.push "resolved dump: a hidden induction function leaked into the surface"
  -- A subset predicate reuses the invariant label as its generated name's
  -- span. Its result type must not turn that label into a typed declaration.
  let src := "pub type Pos = x: Int where positive: x > 0\n"
  let st := FrenCli.elabText (FrenCli.initialState #[] none true) 0 src.toList.toArray
  let label := (src.splitOn "positive")[0]!.length
  let exprStart := (src.splitOn "x >")[0]!.length
  if st.diags.any (·.severity == .error) then
    failures := failures.push "resolved dump: the subset regression did not elaborate"
  if (st.resolved?.getD #[]).any fun a => a.kind == "type" && a.span.start == label then
    failures := failures.push "resolved dump: a hidden subset predicate typed the invariant label"
  unless (st.resolved?.getD #[]).any fun a => a.kind == "expr" &&
      a.span.start == exprStart && a.span.stop == exprStart + 5 && a.value == "Bool" do
    failures := failures.push "resolved dump: the subset invariant lost its expression annotation"
  let src := "pub type Digit = Int is 0..=9\n"
  let st := FrenCli.elabText (FrenCli.initialState #[] none true) 0 src.toList.toArray
  let base := (src.splitOn "Int")[0]!.length
  if st.diags.any (·.severity == .error) then
    failures := failures.push "resolved dump: the shorthand regression did not elaborate"
  for a in st.resolved?.getD #[] do
    if (a.kind == "local" && Fren.Core.generatedName a.value) ||
        (a.kind == "expr" && a.span.start == base) then
      failures := failures.push "resolved dump: the shorthand's unwritten binder leaked into the surface"
  unless (st.resolved?.getD #[]).any fun a => a.kind == "type" &&
      a.span.start == base && a.span.stop == base + 3 && a.value == "Int" do
    failures := failures.push "resolved dump: the shorthand lost its written base type"
  for path in #["test/cli/args/dump_resolved.fren", "test/cli/args/dump_resolved_error.fren",
      "test/cli/args/dump_resolved_failed.fren", "test/ui/lang/resolved_surface.fren",
      "test/cli/args/dump_resolved_markdown.md"] do
    let run (flags : Array String) := run (#["check", "--color=never"] ++ flags ++ #[path])
    let plain ← run #["--jobs", "1"]
    let one ← run #["--jobs", "1", "--dump=resolved"]
    let many ← run #["--jobs", "4", "--dump=resolved", "--dump=resolved"]
    unless one.stdout == many.stdout do
      failures := failures.push s!"{path}: resolved dumps differ between jobs 1 and 4 or repeated flags"
    for out in #[one, many] do
      unless out.stderr == plain.stderr && out.exitCode == plain.exitCode do
        failures := failures.push s!"{path}: resolved dumping changes diagnostics or exit status"
    if path.endsWith "_error.fren" then
      unless one.stdout.isEmpty && one.exitCode == 2 do
        failures := failures.push s!"{path}: a static error printed a resolved dump or had the wrong exit status"
    else
      unless one.stdout.startsWith "; resolved\n" && one.stdout.endsWith "; end of resolved\n" do
        failures := failures.push s!"{path}: no complete resolved dump on stdout:\n{one.stderr}"
      if path.endsWith "_failed.fren" && one.exitCode != 1 then
        failures := failures.push s!"{path}: the failed check did not fail"
      if !path.endsWith "_failed.fren" && one.exitCode != 0 then
        failures := failures.push s!"{path}: the successful fixture failed:\n{one.stderr}"
      unless plain.stdout.isEmpty do
        failures := failures.push s!"{path}: ordinary checking printed to stdout"
    if path.endsWith ".md" then
      let expected := (System.FilePath.mk path).withExtension "expected"
      if bless then IO.FS.writeFile expected one.stdout
      else
        let snapshot ← if ← expected.pathExists then IO.FS.readFile expected else pure ""
        unless one.stdout == snapshot do
          failures := failures.push s!"{path}: blanked Markdown surface or offsets differ from the snapshot\n--- expected\n{snapshot}--- actual\n{one.stdout}---"
  -- The annotations of an imported generic are captured at its declaration,
  -- rather than at one of the concrete instances used by a later file.
  let dir : System.FilePath := ".lake/resolved-test"
  IO.FS.createDirAll dir
  let lib := dir / "library.fren"
  let client := dir / "client.fren"
  IO.FS.writeFile lib "pub mod dump_library\npub fn id<T>(x: T): T := x\n"
  IO.FS.writeFile client "mod dump_client\nuse dump_library::id\nproc c(x: Int): (det y: Int) { out y := id(x) }\n"
  let runFiles (jobs : String) := run #["check", "--color=never", "--dump=resolved", "--jobs", jobs,
      lib.toString, client.toString]
  let one ← runFiles "1"
  let many ← runFiles "4"
  unless one.exitCode == 0 && many.exitCode == 0 && one.stdout == many.stdout do
    failures := failures.push "resolved dump: multi-file loading failed or differs by job count"
  unless (one.stdout.splitOn "(file ").length == 3 &&
      one.stdout.contains "\"dump_library::id\"".toSlice && one.stdout.contains "\"T\"".toSlice &&
      one.stdout.contains "\"<Int>\"".toSlice do
    failures := failures.push "resolved dump: missing files, imported path or generic parameter"
  let combined ← run #["check", "--color=never", "--dump=resolved", "--dump=obligations",
      "--dump=smt", lib.toString, client.toString]
  unless combined.exitCode == one.exitCode && combined.stdout.startsWith one.stdout &&
      combined.stdout.contains "; obligations\n".toSlice && combined.stdout.contains "(check-sat)".toSlice do
    failures := failures.push "resolved dump: combining dumps loses output or changes exit status"
  return failures

end FrenTest.Resolved
