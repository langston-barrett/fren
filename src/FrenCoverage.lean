-- keep-sorted start
import FrenTest.Coverage
import Lean.Compiler.ExportAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.InitAttr
import Lean.Compiler.InlineAttrs
import Lean.Compiler.NameMangling
import Lean.Meta.Match.MatcherInfo
import Lean.Util.ForEachExprWhere
import Lean.Util.Recognizers
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
`deriving` makes, constants, `@[extern]` declarations, whose code is C, or
`@[inline]` definitions, whose code runs in their callers.

Only what the executables can run is a gap: a declaration that no entry
point reaches (`reached`) is not counted against the tests. Only proofs,
and what Lean interprets while a module builds, use it; or its compiled
callers have its code inlined or specialized; or it is the reference of a
`@[csimp]` replacement, which runs in its place.

The declarations that the executables can run but no test runs are listed
in `test/coverage.txt`, one per line, each followed by ` -- ` and why, if
it is never meant to run. The run fails on a counted declaration that does
not run, is reached, and is not listed (`FrenTest.Coverage.fails`). A
listed one that runs, that nothing reaches, or that is no longer counted
only weakens the list, so it gets a warning, which names the line to
remove: `pre-merge` does not measure coverage, so a pull request that
makes a test run a listed declaration merges with its line still listed.
Dead code, which nothing refers to, not even a proof, is reported to be
deleted (`deadOf`).

`--static` reads no counters, and `--new BASE` judges only the definitions
that the working tree adds since its merge base with `BASE`, as
`scripts/coverage_new.py` does before a push.
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

/-- The declaration that the IR declaration `n` is part of: `n` up to its
first component that the compiler adds, such as `_boxed`, `_redArg`,
`_lam_0`, `_at_`, `_spec_1` or `_closed_0`, or `n` itself. Unlike
`declOf?`, a lambda counts for the declaration it was lifted out of, so
that what reaches it reaches the declaration. -/
def ownerOf (n : Name) : Name :=
  let parts := n.components
  let compilerMade (p : Name) := match p with
    | .str _ s => s.startsWith "_" && s != "_private"
    | _ => false
  match (parts.drop 1).findIdx? compilerMade with
  | some k => ofParts (parts.take (k + 1))
  | none => n

#guard ownerOf `FrenCli.run._lam_0 == `FrenCli.run
#guard ownerOf `FrenCli.run._at_.FrenCli.main.spec_0 == `FrenCli.run
#guard let atom := ((Name.mkNum `_private.FrenCli.Parse.PatternSyntax 0).mkStr "FrenCli").mkStr "atom"
  ownerOf (atom.mkStr "_boxed") == atom
#guard ownerOf `Fren.Core.Ty.node == `Fren.Core.Ty.node

/-- The functions that `b` calls (`fap`), and those that it makes closures
of (`pap`), with those before them in `acc`. -/
partial def callsOf (b : IR.FnBody) (acc : Array Name × Array Name) : Array Name × Array Name :=
  match b with
  | .vdecl _ _ v rest =>
    let acc := match v with
      | .fap f _ => (acc.1.push f, acc.2)
      | .pap f _ => (acc.1, acc.2.push f)
      | _ => acc
    callsOf rest acc
  | .jdecl _ _ v rest => callsOf rest (callsOf v acc)
  | .case _ _ _ alts => alts.foldl (fun acc alt => callsOf alt.body acc) acc
  | e => if e.isTerminal then acc else callsOf e.body acc

/-- The declarations that the definition `e` names: the `Name` literals in
it, such as ``` ``Fren.Seq.rev ``` and those of a syntax quotation, and also,
if `consts`, the constants that it uses. -/
def namedIn (e : Expr) (consts : Bool) : IO (Array Name) := do
  let found ← IO.mkRef (#[] : Array Name)
  e.forEachWhere (fun e => e.isApp || e.isConst) fun e => do
    if let some n := e.name? then found.modify (·.push n)
    else if consts then if let .const c _ := e then found.modify (·.push c)
  found.get

/-- The modules whose definitions the Lean definitions that the hosted
front end generates for a spec may call: the types and methods of Fren's
values, the prelude's selectors, `decide`'s instances and the
enumeration's decoders. Each of their definitions is an entry point. -/
def specRuntime : List Name :=
  [`Fren.Prelude, `Fren.Seq, `Fren.SeqElems, `Fren.FinSet, `Fren.Finite, `Fren.Enumerate,
    `FrenCore.Prelude, `FrenCore.Str, `FrenCore.Regex]

/-- The IR declarations that the compiled code of `env`, an executable's,
can run, from its entry points: its `main`, the functions of `@[export]`
declarations, which C may call, those whose type is a named function type,
which Lean may look up by name and call, as attributes do, every
definition of the modules of `specRuntime`, which the code that the hosted
front end generates for a spec may call, and the initialization of each of the modules in `ofPackage`, which runs their
`initialize` functions and computes their constants, the declarations
without parameters. A closure that a constant's body makes (`pap`) is
reached only through code that is reached and reads the constant:
computing it calls nothing. Code that is reached also reaches the
declarations that its definition names, as the hosted front end names
those that the terms it elaborates call, which Lean then runs; and, if
`consts`, all those that its definition uses, which a build that inlines
small functions (one without `-Kcoverage`) needs, since their calls are
then gone from the compiled code. What Lean interprets only while a
module builds, as `#guard`s, `#eval`s and `run_cmd`s, is no entry point. -/
def reached (env : Environment) (ofPackage : Array ModuleIdx) (consts : Bool) : IO NameSet := do
  let callsOfDecl (n : Name) : Array Name × Array Name := match IR.findEnvDecl env n with
    | some (.fdecl _ _ _ b _) => callsOf b (#[], #[])
    | _ => (#[], #[])
  let inPackage (n : Name) := (env.getModuleIdxFor? n).any ofPackage.contains
  let mut todo : Array Name := #[`main]
  for m in ofPackage do
    let runtime := (env.header.moduleNames[m.toNat]?).any specRuntime.contains
    for d in IR.declMapExt.getModuleEntries env m do
      let n := d.name
      -- What the Lean definitions generated for a spec may call, which the
      -- hosted front end compiles and runs, in `lean` and in the tests: by
      -- names built from strings, by instances that synthesis finds, or by
      -- the spec's own identifiers, none of which the compiled code shows.
      if runtime then todo := todo.push n
      if let some f := getInitFnNameFor? env n then todo := todo.push f
      if isIOUnitInitFn env n || (getExportNameFor? env n).isSome then todo := todo.push n
      -- What Lean looks up by name and calls through `evalConst`, as each
      -- attribute that registers code does (`@[command_elab]`, `@[macro]`,
      -- `@[combinator_formatter]`, lean-smt's `@[smt_translate]`): a
      -- function whose type is a named one, such as `CommandElab`, which
      -- `evalConstCheck` requires.
      if !d.params.isEmpty && (env.find? n).any (·.type matches .const ..) then todo := todo.push n
      -- A constant's body runs when its module is initialized; a constant
      -- that it reads is computed by its own module's initialization.
      if d.params.isEmpty then
        for f in (callsOfDecl n).1 do
          if (IR.findEnvDecl env f).any (!·.params.isEmpty) then todo := todo.push f
  let mut seen : NameSet := {}
  let mut scanned : NameSet := {}
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let (calls, closures) := callsOfDecl n
    todo := todo ++ calls ++ closures
    if let some f := getInitFnNameFor? env n then todo := todo.push f
    let o := ownerOf n
    if inPackage o && !scanned.contains o then
      scanned := scanned.insert o
      -- A `partial def`'s code is its `_unsafe_rec`'s definition.
      for d in [o, o.str "_unsafe_rec"] do
        if let some v := (env.find? d).bind (·.value? (allowOpaque := true)) then
          for c in ← namedIn v consts do
            if (IR.findEnvDecl env c).isSome then todo := todo.push c
  return seen

/-- The roots of the executables that `lakefile.lean` declares
(`lean_exe`): each one's `root`, or by default its name. -/
def exeRoots (lakefile : String) : Except String (Array Name) := Id.run do
  let mut roots := #[]
  let lines := (lakefile.splitOn "\n").toArray
  for i in [:lines.size] do
    let decl := ((lines[i]!.dropPrefix? "@[default_target] ").map (·.toString)).getD lines[i]!
    let some rest := decl.dropPrefix? "lean_exe " | continue
    let name := ((rest.toString.splitOn " ").headD "")
    let mut root := name
    for j in [i + 1:lines.size] do
      unless lines[j]!.startsWith " " do break
      if let some r := lines[j]!.trimAscii.toString.dropPrefix? "root := `" then root := r.toString.trimAscii.toString
    if root.isEmpty || root.any (fun c => !(c.isAlphanum || c == '_' || c == '.')) then
      return .error s!"lakefile.lean: cannot read the root of the executable `{name}`"
    roots := roots.push ((root.splitOn ".").foldl Name.mkStr .anonymous)
  if roots.isEmpty then return .error "lakefile.lean: no `lean_exe`"
  return .ok roots

#guard match exeRoots "lean_exe fren where\n  root := `FrenCli.Main\n\n@[default_target] lean_exe fren_fuzz where\n  root := `FrenFuzz\nlean_exe Foo\n" with
  | .ok rs => rs == #[`FrenCli.Main, `FrenFuzz, `Foo]
  | .error _ => false

/-- The identifiers in `src`, each with how many times it occurs: the
maximal runs of the characters that a component of a Lean name has. -/
def identCounts (src : String) (acc : Std.HashMap String Nat := {}) : Std.HashMap String Nat := Id.run do
  let mut acc := acc
  let mut cur := ""
  for c in src.toList ++ [' '] do
    if c.isAlphanum || c == '_' || (!cur.isEmpty && (c == '\'' || c == '!' || c == '?')) then cur := cur.push c
    else if !cur.isEmpty then
      acc := acc.insert cur (acc.getD cur 0 + 1)
      cur := ""
  return acc

#guard (identCounts "Fren.Core.f x (f' y) f? !f").toList.lookup "f" == some 2

/-- The text of `lines` from `pos` to `endPos`. -/
def textBetween (lines : Array String) (pos endPos : Position) : String :=
  let first := pos.line - 1
  let last := endPos.line - 1
  let parts := (List.range (last + 1 - first)).map fun k =>
    let line := lines[first + k]?.getD ""
    let line := if first + k == last then (line.toList.take endPos.column |> String.ofList) else line
    if k == 0 then (line.toList.drop pos.column |> String.ofList) else line
  "\n".intercalate parts

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
  -- An `@[extern]` declaration's code is C of its own, which gcov does
  -- not count with Lean's.
  unless (IR.findEnvDecl env n) matches some (.fdecl ..) do return false
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

/-- The source of each module of the package, by the module's name, from
`src`, and its lines. -/
def sourceLines (m : Name) : IO (Option (Array String)) := do
  let path : System.FilePath := "src" / (System.mkFilePath (m.components.map (·.toString))) |>.addExtension "lean"
  unless ← path.pathExists do return none
  return some ((← IO.FS.readFile path).splitOn "\n").toArray

/-- The declarations that some compiled entry point of an executable of
`lakefile.lean` reaches, as `ownerOf` gives them, from each executable's
environment in turn: their `main`s clash. -/
unsafe def reachedByExes (consts : Bool) : IO (Except String NameSet) := do
  let roots ← match exeRoots (← IO.FS.readFile "lakefile.lean") with
    | .ok rs => pure rs
    | .error e => return .error e
  let mut owners : NameSet := {}
  for root in roots do
    let env ← importModules #[{ module := root }] {}
    let mut ofPackage := #[]
    for h : i in [:env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      let path : System.FilePath := "src" / (System.mkFilePath (m.components.map (·.toString))) |>.addExtension "lean"
      if ← path.pathExists then ofPackage := ofPackage.push (i : ModuleIdx)
    for n in ← reached env ofPackage consts do
      -- A lambda, join point or closed term may be shared with other
      -- declarations whose code is alike (`declOf?`): reaching it reaches
      -- none of them.
      -- Only before `_at_`: `X._at_.Y._lam_0.spec_0` is a specialization
      -- of `X`, at a lambda of `Y`.
      let shared := (n.components.takeWhile (· != .str .anonymous "_at_")).any fun
        | .str _ s => s.startsWith "_lam" || s.startsWith "_elam" || s.startsWith "_jp" || s.startsWith "_closed"
        | _ => false
      unless shared do owners := owners.insert (ownerOf n)
  return .ok owners

/-- The declarations of `decls` that nothing refers to, not even a proof:
whose name is written in its own declaration, which has no attribute, and
nowhere else in `src` or `examples`, in Lean or in Markdown. -/
def deadOf (env : Environment) (decls : Array Name) : IO (Array Name) := do
  let mut counts : Std.HashMap String Nat := {}
  for dir in ["src", "examples"] do
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" || f.extension == some "md" then
        counts := identCounts (← IO.FS.readFile f) counts
  let mut sources : Std.HashMap Name (Array String) := {}
  let mut dead : Array Name := #[]
  for d in decls do
    let short : String := match (privateToUserName? d).getD d with
      | .str _ s => s
      | _ => ""
    if short.isEmpty then continue
    let some m := env.getModuleIdxFor? d | continue
    let some modName := env.header.moduleNames[m.toNat]? | continue
    let some r := declRangeExt.find? env d | continue
    let lines ← match sources[modName]? with
      | some ls => pure ls
      | none =>
        let ls := (← sourceLines modName).getD #[]
        sources := sources.insert modName ls
        pure ls
    let own := textBetween lines r.range.pos r.range.endPos
    let inOwn := (identCounts own).getD short 0
    -- Only a `def`, `abbrev` or `opaque`, or a function of a `where`, that
    -- names itself: a name that the declaration does not write is made for
    -- it, as by `syntax`; and an attribute, or an instance, may have Lean
    -- call it.
    let before := textBetween lines r.range.pos r.selectionRange.pos
    let words := ((before.replace "\n" " ").splitOn " ").filter (!·.isEmpty)
    let keyword := ["def", "abbrev", "opaque"].contains (words.getLastD "") || r.range.pos == r.selectionRange.pos
    if inOwn == 0 || before.contains "@[" || !keyword then continue
    if counts.getD short 0 == inOwn then dead := dead.push d
  return dead

/-- The lines that `git diff -U0` adds to each file, by its path, and the
text of those that it removes. -/
def diffLines (diff : String) : Std.HashMap String (Array Nat × Array String) := Id.run do
  let mut out : Std.HashMap String (Array Nat × Array String) := {}
  let mut file := ""
  let mut line := 0
  for l in diff.splitOn "\n" do
    if let some f := l.dropPrefix? "+++ b/" then
      file := f.toString
    else if l.startsWith "+++ " || l.startsWith "--- " then
      continue
    else if let some h := l.dropPrefix? "@@ " then
      -- `@@ -a,b +c,d @@`: the added lines start at `c`.
      let plus := ((h.toString.splitOn " ")[1]?.getD "").drop 1
      line := ((plus.toString.splitOn ",").headD "").toNat?.getD 0
    else if l.startsWith "+" then
      let (a, r) := out.getD file (#[], #[])
      out := out.insert file (a.push line, r)
      line := line + 1
    else if let some t := l.dropPrefix? "-" then
      let (a, r) := out.getD file (#[], #[])
      out := out.insert file (a, r.push t.toString)
  return out

#guard (diffLines "+++ b/src/A.lean\n@@ -3,0 +4,2 @@\n+def f := 1\n+def g := 2\n@@ -9 +11 @@\n-def h := 3\n+def h := 4\n").get? "src/A.lean"
  == some (#[4, 5, 11], #["def h := 3"])

/-- The declarations of `decls` that the working tree adds since its
merge base with `base`: whose name is on a line that `git diff` adds, or
in a file that git does not track yet, and on none that it removes from
the same file. -/
def newSince (env : Environment) (decls : Array Name) (base : String) : IO (Except String (Array Name)) := do
  let mb ← IO.Process.output { cmd := "git", args := #["merge-base", base, "HEAD"] }
  unless mb.exitCode == 0 do return .error s!"git merge-base {base} HEAD failed:\n{mb.stderr}"
  let out ← IO.Process.output { cmd := "git", args := #["diff", "-U0", "--no-color", mb.stdout.trimAscii.toString, "--", "src"] }
  unless out.exitCode == 0 do return .error s!"git diff failed:\n{out.stderr}"
  let mut lines := diffLines out.stdout
  -- A new file that is not yet tracked is in no diff: all of it is added.
  let others ← IO.Process.output { cmd := "git", args := #["ls-files", "--others", "--exclude-standard", "--", "src"] }
  unless others.exitCode == 0 do return .error s!"git ls-files failed:\n{others.stderr}"
  for f in others.stdout.splitOn "\n" do
    if f.endsWith ".lean" then
      let n := ((← IO.FS.readFile f).splitOn "\n").length
      lines := lines.insert f ((List.range (n + 1)).toArray, #[])
  return .ok <| decls.filter fun d => Id.run do
    let some m := env.getModuleIdxFor? d | return false
    let some modName := env.header.moduleNames[m.toNat]? | return false
    let some r := declRangeExt.find? env d | return false
    let path := "src/" ++ "/".intercalate (modName.components.map (·.toString)) ++ ".lean"
    let some (added, removed) := lines.get? path | return false
    let short := match (privateToUserName? d).getD d with
      | .str _ s => s
      | _ => ""
    return added.contains r.selectionRange.pos.line && !removed.any fun t => (identCounts t).getD short 0 > 0

/-- `GITHUB_STEP_SUMMARY`'s file, on GitHub Actions. -/
def summarize (md : String) : IO Unit := do
  let some path ← IO.getEnv "GITHUB_STEP_SUMMARY" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStr md

/-- Data in a workflow annotation: escape percent before CR and LF, so
an existing escape stays literal and the annotation stays on one line. -/
def escapeAnnotation (text : String) : String :=
  ((text.replace "%" "%25").replace "\r" "%0D").replace "\n" "%0A"

#guard escapeAnnotation "plain text" == "plain text"
#guard escapeAnnotation "%0A\r\n::warning::next" == "%250A%0D%0A::warning::next"

/-- The options of `fren_coverage`, and the command that reads counters
with its arguments. -/
structure Options where
  /-- `--write`: rewrite `test/coverage.txt` as the run found it. -/
  write : Bool := false
  /-- `--static`: read no counters. -/
  static : Bool := false
  /-- `--new BASE`: only the definitions that the working tree adds since
  its merge base with `BASE`. -/
  new? : Option String := none
  gcov : List String := []

def parseArgs : List String → Options → Option Options
  | "--write" :: rest, o => parseArgs rest { o with write := true }
  | "--static" :: rest, o => parseArgs rest { o with static := true }
  | "--new" :: base :: rest, o => parseArgs rest { o with new? := some base }
  | rest, o => if rest.head?.any (·.startsWith "--") then none else some { o with gcov := rest }

def usage : String :=
  "usage: fren_coverage [--write] GCOV [ARG...]\n       fren_coverage --static [--new BASE]\n       fren_coverage --new BASE GCOV [ARG...]"

unsafe def main (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | IO.eprintln usage; return 2
  if o.static == !o.gcov.isEmpty || (o.write && (o.static || o.new?.isSome)) then IO.eprintln usage; return 2
  let gcov := o.gcov.headD ""
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Fren }, { module := `FrenCli.Main }] {} (loadExts := true)
  -- Every module's counters, read by `gcov`.
  let mut ran : Std.HashMap Name Bool := {}
  let mut read := 0
  for m in env.header.moduleNames do
    if o.static then break
    unless counted.contains m.getRoot do continue
    let base : System.FilePath := ".lake" / "build" / "ir" / (System.mkFilePath (m.components.map (·.toString)))
    let gcda := base.withExtension "c.o.gcda"
    unless ← gcda.pathExists do continue
    -- An object that a coverage build took from the artifact cache comes
    -- without its notes (`.gcno`), which only compiling writes: the notes
    -- in `.lake/build` may then be those of another version of the module,
    -- which gcov would misread. The notes and the counters each carry the
    -- object's stamp, after the magic number and the version.
    let gcno := base.withExtension "c.o.gcno"
    let stamp (f : System.FilePath) : IO ByteArray := do
      if ← f.pathExists then return (← IO.FS.readBinFile f).extract 8 12 else return .empty
    let s ← stamp gcno
    if s.isEmpty || s.data != (← stamp gcda).data then
      IO.eprintln s!"fren_coverage: {gcno} is not of the object that wrote {gcda}, which the artifact cache gave: `scripts/coverage_new.py --run` compiles it again"
      return 2
    -- Without the library path that `lake exe` sets to Lean's toolchain,
    -- whose LLVM libraries are not the ones that `GCOV` is linked with: on
    -- Linux, LLVM's `llvm-cov` fails to load under it (#537).
    let gcovArgs := (o.gcov.drop 1).toArray ++ #["-f", "-n", "-o", (gcda.parent.getD ".").toString, gcda.toString]
    let out ← IO.Process.output { cmd := gcov, args := gcovArgs, env := #[("LD_LIBRARY_PATH", none), ("DYLD_LIBRARY_PATH", none)] }
    -- A run that read no counters would report every declaration as never
    -- run, so a failure to read them stops it.
    let failures := FrenTest.Oracle.toolFailures out.stdout out.stderr out.exitCode.toNat
    unless failures.isEmpty do
      IO.eprintln s!"fren_coverage: `{gcov}` failed on {gcda}: {failures}\n{out.stdout}{out.stderr}"
      return 2
    read := read + 1
    for (f, r) in parseGcov out.stdout do
      if let some d := declOf? f then ran := ran.insert d (ran.getD d false || r)
  if !o.static then
    let failures := FrenTest.Coverage.inputFailures read (ran.toList.countP (·.2))
    unless failures.isEmpty do
      IO.eprintln s!"fren_coverage: {failures}: build with -Kcoverage and run lake test; did `{gcov}` read the counters?"
      return 2
  -- A definition without arguments is a constant, computed when its module
  -- is initialized, and compiles to no function. One with arguments that
  -- gcov does not report did not run.
  let hasParams (n : Name) := (IR.findEnvDecl env n).any (!·.params.isEmpty)
  let defs := env.constants.toList.map (·.1) |>.filter (isCounted env ·) |>.toArray |>.qsort (·.toString < ·.toString)
  -- Instances that `deriving` makes, whose range is in the clause.
  let mut sources : Std.HashMap Name (Array String) := {}
  let mut derived := #[]
  for d in defs do
    let some m := env.getModuleIdxFor? d | continue
    let some modName := env.header.moduleNames[m.toNat]? | continue
    let some r := declRangeExt.find? env d | continue
    let lines ← match sources[modName]? with
      | some ls => pure ls
      | none =>
        let ls := (← sourceLines modName).getD #[]
        sources := sources.insert modName ls
        pure ls
    if ((lines[r.range.pos.line - 1]?.getD "").splitOn " ").contains "deriving" then derived := derived.push d
  let defs := defs.filter (!derived.contains ·)
  let decls := defs.filter hasParams
  -- What the compiled code of the executables can run. A declaration that
  -- none of it reaches is used only by proofs, `#guard`s and `#eval`s, or
  -- inlined into its callers, or replaced by a `@[csimp]` lemma's function:
  -- no test can run its own function, and it is no gap.
  -- Without counters, the build may be one that inlines small functions.
  let reachedSet ← match ← reachedByExes o.static with
    | .ok s => pure s
    | .error e => IO.eprintln s!"fren_coverage: {e}"; return 2
  let reachedBy (d : Name) := reachedSet.contains d
  let ranBy (d : Name) := ran.getD d false
  let file : System.FilePath := "test" / "coverage.txt"
  let current ← if ← file.pathExists then IO.FS.readFile file else pure ""
  let listed := parseList current
  let isListed (d : Name) := listed.any (·.1 == d.toString)
  let annotate := (← IO.getEnv "GITHUB_ACTIONS") == some "true"
  -- Only the definitions that a branch adds, for its author to check
  -- before pushing.
  if let some base := o.new? then
    let new ← match ← newSince env defs base with
      | .ok ns => pure ns
      | .error e => IO.eprintln s!"fren_coverage: {e}"; return 2
    let dead ← deadOf env new
    let mut code : UInt32 := 0
    for d in new do
      if dead.contains d then
        IO.println s!"DEAD {d}: nothing refers to it, not even a proof: delete it"
        code := 1
      else if !hasParams d then
        IO.println s!"CONSTANT {d}: computed when its module is initialized, not counted"
      else if !reachedBy d then
        IO.println s!"UNREACHED {d}: no entry point reaches it: only proofs, `#guard`s or `#eval`s use it, its callers inline it, or a `@[csimp]` replacement runs in its place: no test needed"
      else if o.static then
        IO.println s!"REACHED {d}: needs a test: name it in the pull request, and check that it runs it with `scripts/coverage_new.py --run JOB...`"
      else if ranBy d then
        IO.println s!"RAN {d}"
      else if isListed d then
        IO.println s!"LISTED {d}: not run, and listed in test/coverage.txt"
      else
        IO.println s!"NOT RUN {d}: needs a test that runs it, or a line in test/coverage.txt that says why none can"
        code := 1
    IO.println s!"fren_coverage: {new.size} definitions new since {base}"
    return code
  let unreached := decls.filter (!reachedBy ·)
  let dead ← deadOf env defs
  -- Dead code is deleted, not listed. It is reported, not failed on: what
  -- finds it reads the sources' text, so a name that something builds, or
  -- that a test file reads, would seem dead.
  let deadReport : IO Unit := do
    for d in dead do
      let msg := s!"{d}: nothing refers to it, not even a proof: delete it"
      IO.eprintln s!"DEAD {msg}"
      if annotate then IO.println s!"::warning title=fren_coverage dead code::{escapeAnnotation msg}"
  if o.static then
    IO.println s!"fren_coverage: {unreached.size} of {decls.size} declarations reached by no compiled entry point, {(unreached.filter isListed).size} of them listed"
    for d in unreached do
      IO.println s!"UNREACHED{if isListed d then ", LISTED" else ""} {d}"
    deadReport
    return 0
  let uncovered := decls.filter fun d => !ranBy d && reachedBy d
  if o.write then
    let header := (current.splitOn "\n").takeWhile (·.startsWith "#")
    let lines := uncovered.toList.map fun d => match (listed.find? (·.1 == d.toString)).bind (·.2) with
      | some why => s!"{d} -- {why}"
      | none => d.toString
    IO.FS.writeFile file ("\n".intercalate (header ++ lines) ++ "\n")
    IO.println s!"fren_coverage: wrote {uncovered.size} declarations to {file}"
    return 0
  let mut failures := #[]
  for d in decls do
    if FrenTest.Coverage.fails (ranBy d) (reachedBy d) (isListed d) then failures := failures.push s!"{d}: no test runs it"
  -- A stale listing only weakens the list, so it is a warning, which says
  -- the line to remove: a pull request that makes a test run a listed
  -- declaration is not checked for coverage before it merges.
  -- By the name as written, which `toString` gives, private names and `«»`
  -- included.
  let mut stale : Array (String × String) := #[]
  for (d, _) in listed do
    match decls.find? (·.toString == d) with
    | none => stale := stale.push (d, "listed in test/coverage.txt, but not a counted declaration")
    | some n =>
      if FrenTest.Coverage.stale (ranBy n) (reachedBy n) true then
        stale := stale.push (d, if ranBy n then "listed in test/coverage.txt, but a test runs it"
          else "listed in test/coverage.txt, but no compiled entry point reaches it")
  -- What ran although nothing reaches it, through calls that the compiled
  -- code does not show, such as the interpreter's into compiled code.
  let ranUnreached := unreached.filter ranBy
  let covered := (decls.filter ranBy).size
  let counted := decls.size - (unreached.filter (!ranBy ·)).size
  let pct := if counted == 0 then 100 else 100 * covered / counted
  let summary := s!"{covered} of {counted} declarations run by the tests ({pct}%), {(listed.filter (·.2.isSome)).size} never meant to run; {unreached.size - ranUnreached.size} more that no entry point reaches: used only by proofs, `#guard`s or `#eval`s, inlined into their callers, or replaced by `@[csimp]`"
  IO.println s!"fren_coverage: {summary}"
  -- Each shows a hole in the entry points, such as a module that
  -- `specRuntime` should list.
  for d in ranUnreached do
    let msg := s!"{d}: ran, although no compiled entry point reaches it: a call that `FrenCoverage.reached` does not see"
    IO.eprintln s!"WARN {msg}"
    if annotate then IO.println s!"::warning title=fren_coverage::{escapeAnnotation msg}"
  -- On GitHub Actions, also as an annotation of the run.
  let lines := (current.splitOn "\n").map (·.trimAscii.toString)
  for (d, why) in stale do
    let line := (lines.find? fun l => (parseList l).any (·.1 == d)).getD d
    let msg := s!"{d}: {why}: remove the line `{line}` from test/coverage.txt"
    IO.eprintln s!"WARN {msg}"
    if annotate then IO.println s!"::warning title=fren_coverage::{escapeAnnotation msg}"
  deadReport
  for f in failures do IO.eprintln s!"FAIL {f}"
  let bullets (xs : Array String) := String.join (xs.toList.map (s!"- `{·}`\n"))
  summarize <| s!"## Coverage\n\n{summary}.\n\n"
    ++ (if failures.isEmpty then "" else s!"### Run by no test\n\n{bullets failures}\n")
    ++ (if stale.isEmpty then "" else s!"### Stale lines of `test/coverage.txt`\n\n{bullets (stale.map fun (d, why) => s!"{d}: {why}")}\n")
    ++ (if dead.isEmpty then "" else s!"### Dead code\n\nNothing refers to these, not even a proof: delete them.\n\n{bullets (dead.map toString)}\n")
  return if failures.isEmpty then 0 else 1

end FrenCoverage

unsafe def main (args : List String) : IO UInt32 := FrenCoverage.main args
