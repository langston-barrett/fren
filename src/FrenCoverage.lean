-- keep-sorted start
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.InlineAttrs
import Lean.Compiler.NameMangling
import Lean.Meta.Match.MatcherInfo
-- keep-sorted end

/-!
# Test coverage of Fren's code (`Reqs/dev/Testing#coverage`)

`lake exe fren_coverage GCOV...` reads the counters that a run of `lake
test` left in the build directory, after a build with `-Kcoverage`, and
reports which of Fren's declarations no test ran. `GCOV` is the command
that reads them, such as `llvm-cov gcov`.

Coverage is per declaration: a declaration ran if one of its entry
points ran, its own function, its boxed or reduced-arity version, or a
specialization of it. Lambdas, join points and closed terms count for no
one, since the compiler shares them among declarations. The declarations
counted are the definitions of `FrenCore`, `FrenCoreCodes`, `Fren` and
`FrenCli` that are compiled to a function and written in the source: not
theorems, constructors, recursors, matchers, projections, instances that
`deriving` makes, constants, or `@[inline]` definitions, whose code runs in
their callers.

The declarations that no test runs are listed in `test/coverage.txt`, one
per line, each followed by ` -- ` and why, if it is never meant to run.
The run fails on a counted declaration that does not run and is not
listed. A listed one that runs or is no longer counted only weakens the
list, so it gets a warning, which names the line to remove: `pre-merge`
does not measure coverage, so a pull request that makes a test run a listed
declaration merges with its line still listed.
-/

open Lean

namespace FrenCoverage

/-- The libraries whose code is counted. -/
def counted : List Name := [`FrenCore, `FrenCoreCodes, `Fren, `FrenCli]

/-- `parts` as a name, component by component: `++` refuses names with
macro scopes. -/
def ofParts (parts : List Name) : Name :=
  parts.foldl (init := .anonymous) fun acc p => match p with
    | .str _ s => acc.mkStr s
    | .num _ i => acc.mkNum i
    | .anonymous => acc

/-- The declaration that the C function `sym`, one of the package's, is an
entry point of: the declaration's own function, or its boxed or
reduced-arity version, which callers call instead, or `main`, which is emitted as `_lean_main`.
A specialization,
`f._at_.g.spec_N`, is an entry point of `f`, with arguments from `g`, which
may itself be one, as in `f._at_.g._at_.h.spec_0.spec_1`.
Lambdas, join points and closed terms are no one's: the compiler shares
them among declarations whose code is alike, so that running one would
seem to run the others. -/
def declOf? (sym : String) : Option Name := do
  -- An executable's `main` is emitted as `_lean_main`, without the
  -- package's prefix.
  if sym == "_lean_main" then return `main
  let body ← (sym.dropPrefix? "lp_fren_").map (·.toString)
  let parts := (Name.demangle body).components
  let str : Name → Option String := fun | .str _ s => some s | _ => none
  let entry (s : String) := s == "_boxed" || s == "_redArg"
  match parts.findIdx? fun p => (str p).any fun s => s.startsWith "_" && (entry s || s == "_at_" || s.startsWith "_lam"
      || s.startsWith "_elam" || s.startsWith "_jp" || s.startsWith "_closed" || s == "_impl") with
  | none => return ofParts parts
  | some k =>
    let rest := parts.drop k
    let decl := ofParts (parts.take k)
    guard !decl.isAnonymous
    if (rest.head?.bind str) == some "_at_" then
      -- `_at_`, the declaration it is specialized at, which may itself be a
      -- specialization, a `spec_N` for each, then entry parts.
      let isSpec (p : Name) := (str p).any (·.startsWith "spec_")
      let some last := (List.range rest.length).reverse.find? (fun i => rest[i]?.any isSpec) | none
      guard ((rest.drop (last + 1)).all fun p => (str p).any entry)
      return decl
    guard (rest.all fun p => (str p).any entry)
    return decl

#guard declOf? "_lean_main" == some `main
#guard declOf? "lp_fren_FrenCli_run" == some `FrenCli.run
#guard declOf? "lp_fren_FrenCli_run___boxed" == some `FrenCli.run
#guard declOf? "lean_main" == none

/-- The functions of one module's report from `gcov -f`, each with whether
any of its lines ran. -/
def parseGcov (out : String) : Array (String × Bool) := Id.run do
  let mut fs := #[]
  let mut current? : Option String := none
  for line in out.splitOn "\n" do
    if let some rest := line.dropPrefix? "Function '" then
      current? := some (rest.toString.dropEnd 1).toString
    else if let some f := current? then
      if let some rest := line.dropPrefix? "Lines executed:" then
        let pct := (rest.toString.takeWhile (· != '%')).toString
        fs := fs.push (f, pct != "0.00")
        current? := none
  return fs

/-- A declaration is counted if it is a compiled definition of a counted
library, written in the source. -/
def isCounted (env : Environment) (n : Name) : Bool := Id.run do
  let some m := env.getModuleIdxFor? n | return false
  let some modName := env.header.moduleNames[m.toNat]? | return false
  unless counted.contains modName.getRoot do return false
  let some ci := env.find? n | return false
  unless ci matches .defnInfo _ | .opaqueInfo _ do return false
  if (IR.findEnvDecl env n).isNone then return false
  if isAuxRecursor env n || Meta.isMatcherCore env n || env.isProjectionFn n then return false
  if Compiler.hasInlineAttribute env n || Compiler.hasMacroInlineAttribute env n then return false
  -- Names that the user did not write, such as `instReprFoo` from
  -- `deriving` and `Foo.ctorIdx`, are internal, or have no source range of
  -- their own.
  let user := (privateToUserName? n).getD n
  if user.isInternalDetail then return false
  return (declRangeExt.find? env n).isSome

/-- The listed declarations: each with why it is never meant to run, if
it says. -/
def parseList (src : String) : Array (String × Option String) :=
  (src.splitOn "\n").toArray.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else
    match line.splitOn " -- " with
    | [n] => some (n, none)
    | n :: why => some (n, some (" -- ".intercalate why))
    | [] => none

unsafe def main (args : List String) : IO UInt32 := do
  -- `--write` rewrites the list as the run found it, keeping the reasons.
  let write := args.head? == some "--write"
  let args := if write then args.drop 1 else args
  let some gcov := args.head? | IO.eprintln "usage: fren_coverage [--write] GCOV [ARG...]"; return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Fren }, { module := `FrenCli.Main }] {} (loadExts := true)
  -- Every module's counters, read by `gcov`.
  let mut ran : Std.HashMap Name Bool := {}
  let mut read := 0
  for m in env.header.moduleNames do
    unless counted.contains m.getRoot do continue
    let base : System.FilePath := ".lake" / "build" / "ir" / (System.mkFilePath (m.components.map (·.toString)))
    let gcda := base.withExtension "c.o.gcda"
    unless ← gcda.pathExists do continue
    -- Without the library path that `lake exe` sets to Lean's toolchain,
    -- whose LLVM libraries are not the ones that `GCOV` is linked with: on
    -- Linux, LLVM's `llvm-cov` fails to load under it (#537).
    let gcovArgs := (args.drop 1).toArray ++ #["-f", "-n", "-o", (gcda.parent.getD ".").toString, gcda.toString]
    let out ← IO.Process.output { cmd := gcov, args := gcovArgs, env := #[("LD_LIBRARY_PATH", none), ("DYLD_LIBRARY_PATH", none)] }
    -- A run that read no counters would report every declaration as never
    -- run, so a failure to read them stops it.
    unless out.exitCode == 0 do
      IO.eprintln s!"fren_coverage: `{gcov}` failed on {gcda} (exit {out.exitCode}):\n{out.stderr}"
      return 2
    read := read + 1
    for (f, r) in parseGcov out.stdout do
      if let some d := declOf? f then ran := ran.insert d (ran.getD d false || r)
  if read == 0 then
    IO.eprintln "fren_coverage: no counters in .lake/build/ir: build with -Kcoverage and run lake test first"
    return 2
  unless ran.toList.any (·.2) do
    IO.eprintln s!"fren_coverage: the counters of {read} modules show no declaration run: did `{gcov}` read them?"
    return 2
  -- A definition without arguments is a constant, computed when its module
  -- is initialized, and compiles to no function. One with arguments that
  -- gcov does not report did not run.
  let hasParams (n : Name) := (IR.findEnvDecl env n).any (!·.params.isEmpty)
  let decls := env.constants.toList.map (·.1) |>.filter (fun n => isCounted env n && hasParams n)
    |>.toArray |>.qsort (·.toString < ·.toString)
  -- Instances that `deriving` makes, whose range is in the clause.
  let mut sources : Std.HashMap Name (Array String) := {}
  let mut derived := #[]
  for d in decls do
    let some m := env.getModuleIdxFor? d | continue
    let some modName := env.header.moduleNames[m.toNat]? | continue
    let some r := declRangeExt.find? env d | continue
    let lines ← match sources[modName]? with
      | some ls => pure ls
      | none =>
        let path : System.FilePath := "src" / (System.mkFilePath (modName.components.map (·.toString))) |>.addExtension "lean"
        let ls := ((← IO.FS.readFile path).splitOn "\n").toArray
        sources := sources.insert modName ls
        pure ls
    if ((lines[r.range.pos.line - 1]?.getD "").splitOn " ").contains "deriving" then derived := derived.push d
  let decls := decls.filter (!derived.contains ·)
  let file : System.FilePath := "test" / "coverage.txt"
  let current ← if ← file.pathExists then IO.FS.readFile file else pure ""
  let listed := parseList current
  let uncovered := decls.filter (!ran.getD · false)
  if write then
    let header := (current.splitOn "\n").takeWhile (·.startsWith "#")
    let lines := uncovered.toList.map fun d => match (listed.find? (·.1 == d.toString)).bind (·.2) with
      | some why => s!"{d} -- {why}"
      | none => d.toString
    IO.FS.writeFile file ("\n".intercalate (header ++ lines) ++ "\n")
    IO.println s!"fren_coverage: wrote {uncovered.size} declarations to {file}"
    return 0
  let mut failures := #[]
  for d in uncovered do
    unless listed.any (·.1 == d.toString) do failures := failures.push s!"{d}: no test runs it"
  -- A stale listing only weakens the list, so it is a warning, which says
  -- the line to remove: a pull request that makes a test run a listed
  -- declaration is not checked for coverage before it merges.
  -- By the name as written, which `toString` gives, private names and `«»`
  -- included.
  let mut stale : Array (String × String) := #[]
  for (d, _) in listed do
    match decls.find? (·.toString == d) with
    | none => stale := stale.push (d, "listed in test/coverage.txt, but not a counted declaration")
    | some n => if ran.getD n false then stale := stale.push (d, "listed in test/coverage.txt, but a test runs it")
  let covered := decls.size - uncovered.size
  IO.println s!"fren_coverage: {covered} of {decls.size} declarations run by the tests ({if decls.isEmpty then 100 else 100 * covered / decls.size}%), {(listed.filter (·.2.isSome)).size} never meant to run"
  -- On GitHub Actions, also as an annotation of the run.
  let annotate := (← IO.getEnv "GITHUB_ACTIONS") == some "true"
  let lines := (current.splitOn "\n").map (·.trimAscii.toString)
  for (d, why) in stale do
    let line := (lines.find? fun l => (parseList l).any (·.1 == d)).getD d
    let msg := s!"{d}: {why}: remove the line `{line}` from test/coverage.txt"
    IO.eprintln s!"WARN {msg}"
    if annotate then IO.println s!"::warning title=fren_coverage::{msg}"
  for f in failures do IO.eprintln s!"FAIL {f}"
  return if failures.isEmpty then 0 else 1

end FrenCoverage

unsafe def main (args : List String) : IO UInt32 := FrenCoverage.main args
