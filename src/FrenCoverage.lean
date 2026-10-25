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

Coverage is per declaration: a declaration ran if any of the C functions
compiled from it ran, its body, its lambdas and join points, its boxed
and reduced-arity versions, or a specialization of it. Closed terms run
when a module is initialized, so they do not count. The declarations
counted are the definitions of `FrenCore`, `Fren` and `FrenCli` that are
compiled and written in the source: not theorems, constructors,
recursors, matchers, projections or instances that `deriving` makes, and
not `@[inline]` definitions, whose code runs in their callers.

The declarations that no test runs are listed in `test/coverage.txt`, one
per line, each followed by ` -- ` and why, if it is never meant to run.
The run fails if a declaration that is not listed did not run, or if one
that is listed ran or no longer exists, so that the list only shrinks.
-/

open Lean

namespace FrenCoverage

/-- The libraries whose code is counted. -/
def counted : List Name := [`FrenCore, `Fren, `FrenCli]

/-- A component that the compiler adds to a declaration's name for code
that it makes from the declaration. -/
def compilerPart (s : String) : Bool :=
  ["_boxed", "_redArg", "_lam", "_lambda", "_elam", "_jp", "_impl", "_closed", "_at_", "_spec"].any fun p =>
    s == p || s.startsWith (p ++ "_")

/-- `parts` as a name, component by component: `++` refuses names with
macro scopes. -/
def ofParts (parts : List Name) : Name :=
  parts.foldl (init := .anonymous) fun acc p => match p with
    | .str _ s => acc.mkStr s
    | .num _ i => acc.mkNum i
    | .anonymous => acc

/-- The declarations whose code the C function `sym` runs, if it is one of
the package's, and whether the function is a closed term. A
specialization, `f._at_.g.spec_N`, is `f`'s code with arguments from `g`,
whose lambdas it inlines, so it runs both. -/
def declsOf? (sym : String) : Option (Array Name × Bool) := do
  let body ← (sym.dropPrefix? "lp_fren_").map (·.toString)
  let parts := (Name.demangle body).components
  let isPart (p : String → Bool) : Name → Bool := fun | .str _ s => p s | _ => false
  let closed := parts.any (isPart (·.startsWith "_closed"))
  let k := (parts.findIdx? (isPart compilerPart)).getD parts.length
  let mut decls := #[ofParts (parts.take k)]
  if let some a := parts.findIdx? (isPart (· == "_at_")) then
    let rest := parts.drop (a + 1)
    let stop := (rest.findIdx? (isPart fun s => s.startsWith "spec_" || compilerPart s)).getD rest.length
    decls := decls.push (ofParts (rest.take stop))
  let named := decls.filter (!·.isAnonymous)
  guard !named.isEmpty
  return (named, closed)

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
def parseList (src : String) : Array (Name × Option String) :=
  (src.splitOn "\n").toArray.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else
    match line.splitOn " -- " with
    | [n] => some (n.toName, none)
    | n :: why => some (n.toName, some (" -- ".intercalate why))
    | [] => none

unsafe def main (args : List String) : IO UInt32 := do
  -- `--write` rewrites the list as the run found it, keeping the reasons.
  let write := args.head? == some "--write"
  let args := if write then args.drop 1 else args
  let some gcov := args.head? | IO.eprintln "usage: fren_coverage [--write] GCOV [ARG...]"; return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Fren }, { module := `FrenCli.Run }] {} (loadExts := true)
  -- Every module's counters, read by `gcov`.
  let mut ran : Std.HashMap Name Bool := {}
  for m in env.header.moduleNames do
    unless counted.contains m.getRoot do continue
    let base : System.FilePath := ".lake" / "build" / "ir" / (System.mkFilePath (m.components.map (·.toString)))
    let gcda := base.withExtension "c.o.gcda"
    unless ← gcda.pathExists do continue
    let out ← IO.Process.output { cmd := gcov, args := (args.drop 1).toArray ++ #["-f", "-n", "-o", (gcda.parent.getD ".").toString, gcda.toString] }
    for (f, r) in parseGcov out.stdout do
      if let some (ds, closed) := declsOf? f then
        unless closed do
          for d in ds do ran := ran.insert d (ran.getD d false || r)
  -- A definition without arguments is a constant, computed when its module
  -- is initialized, and compiles to no function.
  let decls := env.constants.toList.map (·.1) |>.filter (fun n => isCounted env n && ran.contains n)
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
    if (lines[r.range.pos.line - 1]?.getD "").contains "deriving" then derived := derived.push d
  let decls := decls.filter (!derived.contains ·)
  let file : System.FilePath := "test" / "coverage.txt"
  let current ← if ← file.pathExists then IO.FS.readFile file else pure ""
  let listed := parseList current
  let uncovered := decls.filter (!ran.getD · false)
  if write then
    let header := (current.splitOn "\n").takeWhile (·.startsWith "#")
    let lines := uncovered.toList.map fun d => match (listed.find? (·.1 == d)).bind (·.2) with
      | some why => s!"{d} -- {why}"
      | none => d.toString
    IO.FS.writeFile file ("\n".intercalate (header ++ lines) ++ "\n")
    IO.println s!"fren_coverage: wrote {uncovered.size} declarations to {file}"
    return 0
  let mut failures := #[]
  for d in uncovered do
    unless listed.any (·.1 == d) do failures := failures.push s!"{d}: no test runs it"
  for (d, _) in listed do
    if !decls.contains d then failures := failures.push s!"{d}: listed in test/coverage.txt, but not a counted declaration"
    else if ran.getD d false then failures := failures.push s!"{d}: listed in test/coverage.txt, but a test runs it"
  let covered := decls.size - uncovered.size
  IO.println s!"fren_coverage: {covered} of {decls.size} declarations run by the tests ({if decls.isEmpty then 100 else 100 * covered / decls.size}%), {(listed.filter (·.2.isSome)).size} never meant to run"
  for f in failures do IO.eprintln s!"FAIL {f}"
  return if failures.isEmpty then 0 else 1

end FrenCoverage

unsafe def main (args : List String) : IO UInt32 := FrenCoverage.main args
