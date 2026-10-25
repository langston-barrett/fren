-- keep-sorted start
import Fren
import FrenCli.Run
import FrenTest.Ui
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# `lake test`

- **ui tests:** every `test/ui/*.fren` is checked by both front ends against
  its annotations (`FrenTest.Ui`). The binary's checker runs in-process; the
  Lean front end elaborates the file in an environment that imports `Fren`.
  Passing both is how `cli::agreement` is tested.
- **Snapshots:** each `test/cli/X.fren` must make the binary print
  `test/cli/X.expected` exactly (output and exit code), for formatting that
  annotations don't cover. A line `--@ args: ARGS` runs `fren ARGS X.fren`
  instead of `fren check X.fren`. `lake test -- --bless` (or `FREN_BLESS=1`)
  rewrites them.
- Fren's own requirements must pass under the binary.
- **Formatting:** every spec in the repository that parses must be
  formatted, keeps its tokens, imports and comments when formatted, and
  formatting it again changes nothing (`fmt::safe`); `fren fmt` rewrites a
  file in place.

The tests run as jobs, in parallel (see "Jobs" below), and the failures are
reported sorted.
-/

-- fren-covers: cli::agreement, fmt::safe

open System Lean FrenTest.Ui

def sortedFiles (dir : FilePath) (ext : String) : IO (Array FilePath) := do
  let es ← dir.readDir
  return (es.filter (·.path.extension == some ext)).map (·.path) |>.qsort (·.toString < ·.toString)

/-! ## Snapshots -/

/-- Compares `actual` with the snapshot at `path`, or writes it when blessing. -/
def expectFile (bless : Bool) (path : FilePath) (actual : String) : IO (Option String) := do
  if bless then
    IO.FS.writeFile path actual
    return none
  let expected ← if ← path.pathExists then IO.FS.readFile path else pure ""
  if expected == actual then return none
  return some s!"{path}: output differs from snapshot\n--- expected\n{expected}--- actual\n{actual}---"

/-- Runs `fren check` on `files`, returning its output and exit code. -/
def runCheck (files : Array String) : IO (String × UInt32) :=
  IO.FS.withIsolatedStreams (FrenCli.check { files })

/-- Runs `fren` with `args`, returning its output (stdout and stderr) and
exit code. -/
def runFren (args : List String) : IO (String × UInt32) :=
  IO.FS.withIsolatedStreams (FrenCli.run args)

/-- A snapshot runs `fren check FILE`, or `fren ARGS FILE` if the file has a
line `--@ args: ARGS`, or `fren ARGS` (without the file) if it has a line
`--@ argv: ARGS`. -/
def snapshots (bless : Bool) : IO (Array String) := do
  (← sortedFiles ("test" / "cli") "fren").filterMapM fun f => do
    let src ← IO.FS.readFile f
    let directive (d : String) := (src.splitOn "\n").findSome? (·.dropPrefix? s!"--@ {d}: ") |>.map (·.toString.splitOn " ")
    let argv := match directive "argv" with
      | some argv => argv
      | none => (directive "args").getD ["check"] ++ [f.toString]
    let (out, code) ← runFren argv
    expectFile bless (f.withExtension "expected") s!"{out}exit={code}\n"

/-! ## ui tests -/

/-- The header of a rendered diagnostic, `error[F0105]: text`: its severity
(`note` is `info`) and text. -/
def header? (line : String) : Option (String × String) :=
  [("error", "error"), ("warning", "warning"), ("note", "info")].findSome? fun (label, sev) => do
    let rest ← (line.dropPrefix? label).map (·.toString)
    let rest := if rest.startsWith "[" then ((rest.splitOn "]").drop 1 |> "]".intercalate) else rest
    let text ← (rest.dropPrefix? ": ").map (·.toString)
    return (sev, text)

/-- The binary's messages about `file`, and its summary line. A message's
text is its headline, then its `= note` lines and `help:` suggestions. -/
def cliDiagnostics (file : String) (out : String) : Array Diagnostic × Option String := Id.run do
  let mut diags : Array Diagnostic := #[]
  let mut summary := none
  -- A header whose ` --> ` line is still to come
  let mut pending : Option (String × String) := none
  for line in out.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if let some h := header? line then
      pending := some h
    else if let some loc := trimmed.dropPrefix? "--> " then
      if let some (sev, text) := pending then
        -- `file:line:col`
        let parts := loc.toString.splitOn ":"
        if parts.length ≥ 3 && ":".intercalate (parts.take (parts.length - 2)) == file then
          diags := diags.push { line := parts[parts.length - 2]!.toNat!, severity := sev, text }
        else diags := diags.push { line := 0, severity := "other-file", text }
      pending := none
    else if line.startsWith "fren: " then
      summary := some (line.drop 6).toString
    else if let some d := diags.back? then
      if let some n := trimmed.dropPrefix? "= " then
        diags := diags.pop.push { d with text := d.text ++ "\n" ++ n.toString }
      else if line.startsWith "help: " then
        diags := diags.pop.push { d with text := d.text ++ "\n" ++ line }
  return (diags.filter (·.severity != "other-file"), summary)

/-- The Lean front end's messages about a ui test, and its summary. -/
def hostedDiagnostics (env : Environment) (file : String) (src : String) :
    IO (Array Diagnostic × Option String) := do
  -- One line of header; message lines are shifted back below.
  let input := "open Fren.Lang\n" ++ src ++ "\n#fren_check\n"
  let (_, log) ← Elab.process input env {} file
  let mut diags := #[]
  let mut summary := none
  for m in log.toList do
    let text := (← m.data.toString).trimAscii.toString
    let sev := match m.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "info"
    if sev == "info" && text.startsWith "fren: " then
      summary := some (text.drop 6).toString
    else
      diags := diags.push { line := m.pos.line - 1, severity := sev, text }
  return (diags, summary)

/-- The ui tests of `files`. -/
def uiTests (env : Environment) (files : Array FilePath) : IO (Array String) := do
  let mut failures := #[]
  for f in files do
    let src ← IO.FS.readFile f
    let spec ← match parse src with
      | .ok s => pure s
      | .error e => failures := failures.push s!"{f}: {e}"; continue
    if spec.only? != some "hosted" then
      let (out, code) ← runCheck #[f.toString]
      let (diags, summary) := cliDiagnostics f.toString out
      for e in check "cli" spec diags summary (some code.toNat) do
        failures := failures.push s!"{f} (binary): {e}"
    if spec.only? != some "cli" then
      let (diags, summary) ← hostedDiagnostics env f.toString src
      for e in check "hosted" spec diags summary none do
        failures := failures.push s!"{f} (Lean): {e}"
  return failures

/-! ## Fren's own requirements -/

/-! ## Error codes -/

/-- The ```` ```fren ```` blocks of a Markdown text. -/
def frenBlocks (md : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur : Option (Array String) := none
  for line in md.splitOn "\n" do
    match cur with
    | none => if line.trimAscii.toString == "```fren" then cur := some #[]
    | some ls =>
      if line.trimAscii.toString == "```" then
        out := out.push ("\n".intercalate ls.toList ++ "\n")
        cur := none
      else cur := some (ls.push line)
  return out

/-- The codes in the sources of both front ends, as string literals. -/
def codesInSources : IO (Array String) := do
  let mut out := #[]
  for dir in ["src/FrenCore", "src/FrenCli", "src/Fren"] do
    for f in ← System.FilePath.walkDir dir do
      if f.toString.endsWith "Codes.lean" || f.extension != some "lean" then continue
      for part in ((← IO.FS.readFile f).splitOn "\"F").drop 1 do
        let digits := part.takeWhile Char.isDigit |>.toString
        if digits.length == 4 && (part.drop 4).startsWith "\"" then out := out.push s!"F{digits}"
  return out.toList.eraseDups.toArray

/-- Codes that no snapshot can report reliably: a solver that gives up
depends on the machine. -/
def unsnapshotted : List String := ["F0608"]

/-- Every code is explained and covered by a snapshot; each explanation's
erroneous example reports its code, and its fixed versions report no static
errors and not the code. -/
def errorCodes : IO (Array String) := do
  let mut failures := #[]
  let codes := Fren.Core.errorCodes.map (·.code)
  if codes.toList.eraseDups.length != codes.size then failures := failures.push "error codes: duplicate codes"
  -- fren-covers: view::code_group
  for c in codes ++ Fren.Core.Lint.all.map (·.code) do
    let ok := c.length == 5 && c.startsWith "F0" && (c.toList.drop 2).all Char.isDigit
      && ['1', '2', '3', '4', '5', '6', '7'].contains (c.toList[2]!)
    unless ok do failures := failures.push s!"{c}: not of the form `F0` followed by a group from 1 to 7 and two digits"
  let snapshots ← (← sortedFiles ("test" / "cli") "expected").mapM IO.FS.readFile
  for c in ← codesInSources do
    unless codes.contains c do failures := failures.push s!"{c}: used in the sources but not explained in `FrenCore/Codes.lean`"
  for c in Fren.Core.errorCodes do
    unless unsnapshotted.contains c.code || snapshots.any (·.contains s!"[{c.code}]:".toSlice) do
      failures := failures.push s!"{c.code}: no snapshot in test/cli reports it"
    let blocks := frenBlocks c.explanation
    let some args := c.args | continue
    let some bad := blocks[0]? | failures := failures.push s!"{c.code}: the explanation has no erroneous example"; continue
    IO.FS.createDirAll (".lake" / "explain-test")
    let file := s!".lake/explain-test/{c.code}.fren"
    IO.FS.writeFile file bad
    let (out, _) ← runFren (args ++ [file])
    unless out.contains s!"[{c.code}]:".toSlice do
      failures := failures.push s!"{c.code}: the erroneous example does not report it:\n{out}"
    for good in blocks.extract 1 do
      IO.FS.writeFile file good
      let (out, _) ← runFren ["check", file]
      if out.contains s!"[{c.code}]:".toSlice || out.contains "could not check".toSlice then
        failures := failures.push s!"{c.code}: a fixed example still fails:\n{good}\n{out}"
  return failures

def ownSpec : IO (Array String) := do
  let files := #["Lang/Overview", "Lang/Lexical", "Lang/Types", "Lang/Items", "Lang/Components", "Lang/Decidability", "Lang/Expressions", "Lang/Modules", "Lang/Instances", "Check", "View", "Lint", "Cli", "Eval", "Lang/Refinement", "Fmt", "Impl", "Trace"].map fun r => s!"src/Reqs/{r}.md"
  let (out, code) ← runCheck files
  return if code == 0 then #[] else #[s!"src/Reqs failed under the binary:\n{out}"]

/-! ## Formatting -/

/-- The specs in the repository: its `.fren` and Markdown files, outside
`.lake`, `.git`, the built book and `.claude`, which may hold other
worktrees. -/
def specFiles : IO (Array String) := do
  let skip (p : FilePath) : IO Bool := pure !([".lake", ".git", "book", ".lun", ".claude"].contains (p.fileName.getD ""))
  let fs ← System.FilePath.walkDir "." skip
  let fs := fs.filter fun f => f.extension == some "fren" || f.extension == some "md"
  return (fs.map fun f => ((f.toString.dropPrefix? "./").map (·.toString)).getD f.toString).qsort (· < ·)

/-- Specs that are not formatted, as `--ignore` globs: those deliberately
not formatted, and those that `fren fmt` cannot parse, such as tests of
syntax errors and of Lean code, and the examples of Markdown specs. -/
def fmtIgnore : List String :=
  ["test/cli/f01*.fren", "test/cli/f0216_member_option.fren", "test/cli/fix_*.fren", "test/cli/fmt_check.fren", "test/cli/fmt_parse_error.fren", "test/ui/syntax_*.fren",
   "test/ui/impl.fren", "test/ui/lean_*.fren", "test/ui/trace.fren", "src/Reqs/Markdown.md"]

/-- What formatting keeps (`fmt::safe`): the tokens, but for the trailing
commas of lists and claims and for `use` items; the paths the `use` items
import, sorted; and the comments. -/
def fmtKept (path src : String) : Option (Array String × Array (Array String) × Array String) := do
  let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
  let chars := src.toList.toArray
  let (toks, comments) ← (FrenCli.lexWithComments chars).toOption
  let lay ← (FrenCli.parseLayout toks).toOption
  let inUse (k : Nat) : Bool := lay.uses.any fun (f, l) => f ≤ k && k ≤ l
  let isStr (k : Nat) : Bool := toks[k]?.any (·.tok matches .str _)
  let mut kept := #[]
  for h : k in [0:toks.size] do
    if inUse k then continue
    let t := toks[k]
    let trailing := t.tok == .kw "," &&
      (toks[k + 1]?.any (·.tok == .kw "}") || (k > 0 && isStr (k - 1) && !isStr (k + 1)))
    if !trailing then kept := kept.push (reprStr t.tok)
  let paths := (lay.uses.flatMap fun (f, l) =>
    let (ps, glob) := FrenCli.Fmt.usePaths toks f l
    if glob then ps.map (·.push "*") else ps).qsort FrenCli.Fmt.pathLt
  return (kept, paths, comments.map fun c => (FrenCli.Fmt.text chars c).trimAsciiEnd.toString)

/-! ## Conformance corpus (`Reqs/Lang/Decidability`) -/

/-- Random components whose constraints are all in the decidable core of
strings, from a fixed seed. -/
def stringCorpus (n : Nat) : String := Id.run do
  let mut seed : Nat := 20261023
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\n"
  let lits := #["\"\"", "\"a\"", "\"ab\"", "\"b\"", "\"F0\"", "\"x?\""]
  let pats := #["r\"[a-z]*\"", "r\"a+b?\"", "r\".*[A-Z].*\"", "r\"[^_]*\"", "r\"(ab|ba){1,2}\"", "r\"F0[1-7][0-9]\""]
  for k in [0:n] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let v := pick #["s", "t"] 1
      let l := pick lits 2
      let i := toString ((seed / 13) % 4)
      atoms := atoms.push <| pick #[
        s!"{v}.starts_with?({l})", s!"{v}.ends_with?({l})", s!"{v}.contains?({l})",
        s!"{v}.matches?({pick pats 3})", s!"{v}.len <= {i}", s!"{v}.len + 1 >= {i}", s!"{v} = {l}", "s = t",
        "s != t", s!"s.len + t.len = {i}", s!"({v} ++ {l}).len > {i}", s!"{v}.at({i}) = {l}",
        s!"{v}.slice(0, {i}) != {l}", s!"{v} < {l}"] 5
    out := out ++ s!"comp c{k} \{\n    in s: String\n    in t: String\n    pub out p?\n\n    \
      assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    req r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect e: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Random components whose constraints are all in the decidable core of
sets: Boolean algebra with cardinality. -/
def setCorpus (n : Nat) : String := Id.run do
  let mut seed : Nat := 20261024
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\nenum E { A, B, C }\n\n"
  let sets := #["s", "t", "(s union t)", "(s inter t)", "(s minus t)", "{1, 2}", "(t minus t)"]
  for k in [0:n] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick sets 1
      let b := pick sets 2
      let i := toString ((seed / 13) % 4)
      atoms := atoms.push <| pick #[
        s!"x in {a}", s!"{a} subset {b}", s!"{a} = {b}", s!"{a} != {b}", s!"{a}.card <= {i}",
        s!"{a}.card + {b}.card >= {i}", s!"e in es", "es = {E::A, E::B}", s!"es.card = {i}", "x in s and not x in t",
        "s = {}"] 5
    out := out ++ s!"comp c{k} \{\n    in s: Set(Int)\n    in t: Set(Int)\n    in x: Int\n    in es: Set(E)\n    in e: E\n    \
      pub out p?\n\n    assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    req r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Relations over finite types, which are in the decidable core: the
relational operators, with the set operators, but not `card`, which the core
does not combine with them. -/
def relationCorpus (n : Nat) : String := Id.run do
  let mut seed : Nat := 20261024
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\nenum E { A, B, C }\n\n"
  let rels := #["r", "q", "(r union q)", "(r inter q)", "(r minus q)", "(r join q)", "r.inverse", "r.closure",
    "{(E::A, E::B), (E::B, E::C)}", "(q join r.closure)"]
  let sets := #["s", "r.domain", "r.range", "r.image(s)", "q.image({E::A})", "{E::B}", "r.closure.image(s)"]
  for k in [0:n] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick rels 1
      let b := pick rels 2
      let u := pick sets 3
      atoms := atoms.push <| pick #[
        s!"(x, y) in {a}", s!"{a} subset {b}", s!"{a} = {b}", s!"x in {u}", s!"{u} subset s", s!"{u} != {b}.domain",
        s!"(x, x) in {a}", "r = {}", s!"{a} != \{}"] 5
    out := out ++ s!"comp c{k} \{\n    in r: Rel(E, E)\n    in q: Rel(E, E)\n    in s: Set(E)\n    in x: E\n    in y: E\n    \
      pub out p?\n\n    assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    req r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Sequences in the decidable core: indexing, `len`, `update`, equality,
and operations with a literal operand. -/
def sequenceCorpus (n : Nat) : String := Id.run do
  let mut seed : Nat := 20261024
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\n"
  let seqs := #["q", "r", "[1, 2]", "q.update(0, x)", "r.update(i, 2)", "[x]", "[0, x, 1]"]
  for k in [0:n] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick seqs 1
      let b := pick seqs 2
      let j := toString ((seed / 13) % 3)
      atoms := atoms.push <| pick #[
        s!"{a} = {b}", s!"{a} != {b}", s!"{a}.len <= {j}", s!"x in [1, {j}]", s!"q.starts_with?([{j}])",
        s!"q.ends_with?([x, {j}])", s!"(q.len > {j} and q[{j}] = x)", s!"(0 <= i and i < r.len and r[i] > {j})",
        s!"{a}.len + {b}.len >= {j}"] 5
    out := out ++ s!"comp c{k} \{\n    in q: Seq(Int)\n    in r: Seq(Int)\n    in x: Int\n    in i: Int\n    \
      pub out p?\n\n    assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    req r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- The corpora, by name. -/
def corpora : List (String × (Nat → String)) :=
  [("strings", stringCorpus), ("sets", setCorpus), ("relations", relationCorpus), ("sequences", sequenceCorpus)]

/-- The solver decides every query of the corpus `name`: nothing is
inconclusive. -/
def conformance (name : String) (corpus : Nat → String) : IO (Array String) := do
  IO.FS.createDirAll (".lake" / "corpus")
  let file := s!".lake/corpus/{name}.fren"
  IO.FS.writeFile file (corpus 40)
  let (out, _) ← runFren ["check", file]
  if out.contains "could not check".toSlice || !out.contains " 0 inconclusive".toSlice then
    return #[s!"the {name} corpus ({file}) is not decided:\n{out}"]
  return #[]

/-- `fmt::safe` over every spec in the repository, and every spec that
parses is formatted. -/
def formatting : IO (Array String) := do
  let mut failures := #[]
  for f in ← specFiles do
    let src ← IO.FS.readFile f
    let .ok new := FrenCli.Fmt.formatFile f src | continue
    if fmtKept f src != fmtKept f new then
      failures := failures.push s!"{f}: formatting changes its tokens, imports or comments"
    if (FrenCli.Fmt.formatFile f new).toOption != some new then
      failures := failures.push s!"{f}: formatting it twice changes it again"
  -- Every other spec is formatted, as `fren fmt --check` says.
  let ignore := fmtIgnore.flatMap (["--ignore", ·])
  let (out, code) ← runFren (["fmt", "--check"] ++ ignore ++ (← specFiles).toList)
  if code != 0 then
    failures := failures.push s!"specs are not formatted (exit {code}); run `fren fmt {" ".intercalate ignore} FILE...`:\n{out}"
  -- In place: the file becomes formatted, and is then left alone.
  IO.FS.createDirAll (".lake" / "fmt-test")
  let file := ".lake/fmt-test/spec.fren"
  let src ← IO.FS.readFile ("test" / "cli" / "fmt_check.fren")
  IO.FS.writeFile file src
  let (out, code) ← runFren ["fmt", file]
  let written ← IO.FS.readFile file
  if code != 0 || !out.isEmpty || (FrenCli.Fmt.formatFile file src).toOption != some written || written == src then
    failures := failures.push s!"`fren fmt` did not format {file} in place (exit {code}):\n{out}"
  let (out, code) ← runFren ["fmt", "--check", file]
  if code != 0 || !out.isEmpty then
    failures := failures.push s!"`fren fmt --check` reports a formatted file (exit {code}):\n{out}"
  return failures

/-- `fren fix` rewrites a Markdown spec in place, keeping its prose, and
then has nothing left to fix. -/
def fixing : IO (Array String) := do
  let mut failures := #[]
  IO.FS.createDirAll (".lake" / "fix-test")
  let file := ".lake/fix-test/spec.md"
  let block (body : String) := s!"```fren\n{body}\n```\n"
  let spec (uses : String) :=
    "# Spec\n\nProse with `use`.\n\n" ++ block "pub mod m\n\npub enum Mode { Heat, Cool }" ++
    "\nMore prose.\n\n" ++ block s!"mod n\n\n{uses}comp c \{\n    in x: Mode\n    pub out h?\n    req r: h? iff x = Heat\n}"
  IO.FS.writeFile file (spec "use m::Mode\nuse m::Mode::*\nuse m::Mode::Cool\n\n")
  let (out, code) ← runFren ["fix", file]
  let written ← IO.FS.readFile file
  let want := spec "use m::Mode\nuse m::Mode::Heat\n\n"
  if code != 0 || written != want then
    failures := failures.push s!"`fren fix` did not fix {file} in place (exit {code}):\n{out}\n{written}"
  let (out, code) ← runFren ["fix", "--check", file]
  if code != 0 || !out.isEmpty then
    failures := failures.push s!"`fren fix --check` reports a fixed file (exit {code}):\n{out}"
  return failures

/-! ## Jobs

The tests are independent, so `main` runs them as jobs, in parallel, each
in a process of its own (`fren_test --job NAME ARG...`): the binary's
output is captured by redirecting the process's streams, which threads
cannot share. A job prints its failures, as JSON, on its last line. When
blessing, `snapshots` rewrites the snapshots that `errorCodes` reads, so it
runs first, alone. -/

/-- The ui tests run in batches of at most this many files, each in a
process that imports `Fren` once. -/
def uiBatch : Nat := 8

/-- The jobs, as the arguments of `--job`, the slowest first. -/
def jobs : IO (Array (List String)) := do
  let ui ← sortedFiles ("test" / "ui") "fren"
  let n := (ui.size + uiBatch - 1) / uiBatch
  -- Every `n`th file, so that the slow ones spread over the batches.
  let batches := (List.range n).toArray.map fun k =>
    "ui" :: ((List.range ui.size).filter (· % n == k)).map (ui[·]!.toString)
  return #[["ownSpec"]] ++ batches ++ (corpora.map (["conformance", ·.1])).toArray
    ++ #[["snapshots"], ["formatting"], ["errorCodes"], ["fixing"]]

/-- Runs a job in this process. -/
unsafe def runJob (bless : Bool) : List String → IO (Array String)
  | "ui" :: files => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Fren }] {} (loadExts := true)
    uiTests env (files.toArray.map FilePath.mk)
  | ["snapshots"] => snapshots bless
  | ["errorCodes"] => errorCodes
  | ["ownSpec"] => ownSpec
  | ["conformance", name] => match corpora.lookup name with
    | some corpus => conformance name corpus
    | none => throw (IO.userError s!"unknown corpus `{name}`")
  | ["formatting"] => formatting
  | ["fixing"] => fixing
  | job => throw (IO.userError s!"unknown job `{" ".intercalate job}`")

/-- Runs `job` in a process of its own, returning its failures. -/
def spawnJob (bless : Bool) (job : List String) : IO (Array String) := do
  let args := #["--job"] ++ job.toArray ++ (if bless then #["--bless"] else #[])
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args }
  let last := ((out.stdout.splitOn "\n").filter (!·.isEmpty)).getLast?.getD ""
  let name := " ".intercalate job
  match Json.parse last >>= fromJson? with
  | .ok failures =>
    if out.exitCode == 0 then
      -- Such as a `panic!`, which prints and carries on.
      if out.stderr.isEmpty then return failures
      return failures.push s!"the job `{name}` wrote to stderr:\n{out.stderr}"
  | .error _ => pure ()
  return #[s!"the job `{name}` crashed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"]

/-- At most this many jobs run at once, unless `FREN_TEST_JOBS` says
otherwise: a job can take about 2 GB of memory, and the solver's time limit
is in wall-clock time, so too many jobs at once could make checks
inconclusive. -/
def maxJobs : Nat := 16

/-- How many jobs run at once: `FREN_TEST_JOBS`, or as many as the machine
has cores, up to `maxJobs`. -/
def jobCount : IO Nat := do
  if let some v ← IO.getEnv "FREN_TEST_JOBS" then
    match v.toNat? with
    | some n => if n > 0 then return n
    | none => pure ()
    throw (IO.userError s!"FREN_TEST_JOBS must be a positive integer, not `{v}`")
  return max 1 (min maxJobs (System.Platform.Internal.getHardwareConcurrency ()).toNat)

/-- Runs `jobs`, at most `jobCount` at once. -/
def runJobs (bless : Bool) (jobs : Array (List String)) : IO (Array String) := do
  let next ← IO.mkRef 0
  let worker : IO (Array String) := do
    let mut failures := #[]
    repeat
      let k ← next.modifyGet fun k => (k, k + 1)
      let some job := jobs[k]? | break
      failures := failures ++ (← spawnJob bless job)
    return failures
  let tasks ← (List.range (← jobCount)).mapM fun _ => IO.asTask worker .dedicated
  tasks.foldlM (init := #[]) fun acc t => return acc ++ (← IO.ofExcept t.get)

unsafe def main (args : List String) : IO UInt32 := do
  let bless := args.contains "--bless" || (← IO.getEnv "FREN_BLESS").isSome
  if let "--job" :: job := args then
    IO.println (toJson (← runJob bless (job.filter (· != "--bless")))).compress
    return 0
  let (first, rest) := (← jobs).partition (bless && · == ["snapshots"])
  let failures := ((← runJobs bless first) ++ (← runJobs bless rest)).qsort (· < ·)
  for f in failures do IO.eprintln s!"FAIL {f}"
  if failures.isEmpty then
    IO.println "fren_test: all passed"
    return 0
  IO.eprintln s!"fren_test: {failures.size} failure(s); `lake test -- --bless` accepts new snapshots"
  return 1
