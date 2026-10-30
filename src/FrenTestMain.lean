-- keep-sorted start
import Fren
import FrenCli.Eval
import FrenCli.Run
import FrenTest.Messages
import FrenTest.Quote
import FrenTest.Ui
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# `lake test`

- **ui tests:** every `test/ui/**/*.fren`, and every example in
  `examples/**/*.fren`, is checked by both front ends against
  its annotations (`FrenTest.Ui`). The binary's checker runs in-process; the
  Lean front end elaborates the file in an environment that imports `Fren`.
  Passing both is how `cli::agreement` is tested.
- **Snapshots:** each `test/cli/**/X.fren` must make the binary print
  `test/cli/**/X.expected` exactly (output and exit code), for formatting that
  annotations don't cover. A line `--@ args: ARGS` runs `fren ARGS X.fren`
  instead of `fren check X.fren`. `lake test -- --bless` (or `FREN_BLESS=1`)
  rewrites them.
- Fren's own requirements must pass under the binary.
- **Formatting:** every spec in the repository that parses must be
  formatted, keeps its tokens, imports and comments when formatted, and
  formatting it again changes nothing (`fmt::safe`); `fren fmt` rewrites a
  file in place.
- **Mutants:** every mutant of the corpus is well-formed, identified,
  stable and, for a swap, involutive (`mutation`).
- **Lean's tokens:** the tokens that both front ends read as identifiers,
  and reject as declarations, are Lean's (`leanTokens`).
- **Printing fixes:** what the printer of fixes writes for random trees
  reads back as each tree, by the parser of the `fren` command, and needs
  each pair of parentheses that it adds, but those of its exceptions
  (`printing`, `lint::printing`).
- **Decisions of `fren mutate`:** on each example of `test/mutate/`, it is
  adequate, decides a mutant as a sample or a shard does, needs every expectation, and
  selects the components to check, and decides each check, soundly
  (`decisions`).

The tests run as jobs, in parallel (see "Jobs" below), and the failures are
reported sorted.
-/

-- fren-covers: cli::agreement, fmt::safe

open System Lean FrenTest.Ui

/-- The files under `dir`, in its subdirectories too, with extension `ext`. -/
def sortedFiles (dir : FilePath) (ext : String) : IO (Array FilePath) := do
  let fs ← dir.walkDir
  return (fs.filter (·.extension == some ext)) |>.qsort (·.toString < ·.toString)

/-- The ui tests: `test/ui/**/*.fren`, and the examples, `examples/**/*.fren`,
which are checked as ui tests too. -/
def uiFiles : IO (Array FilePath) :=
  return (← sortedFiles ("test" / "ui") "fren") ++ (← sortedFiles "examples" "fren")

/-! ## Snapshots -/

/-- `out` with the note that lists every lint (`Fren.Core.lintsNote`)
written as `lintsPlaceholder`, so that a snapshot that shows it does not
change when a lint is added, and lints added at once merge cleanly. The
note is made from `Lint.all`, which `lintTable` compares with the table of
lints. -/
def lintsShown (out : String) : String := out.replace Fren.Core.lintsNote lintsPlaceholder
where lintsPlaceholder := "note: the lints are {Lint.all}"

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
    expectFile bless (f.withExtension "expected") s!"{lintsShown out}exit={code}\n"

/-! ## ui tests -/

/-- The ui tests of `files`. -/
def uiTests (env : Environment) (files : Array FilePath) : IO (Array String) := do
  let mut failures := #[]
  let isStopped (d : Diagnostic) := d.line == 0 && d.text == Fren.Core.couldNotHeadline
  for f in files do
    let mut cliStopped := none
    let src ← IO.FS.readFile f
    let spec ← match parse src with
      | .ok s => pure s
      | .error e => failures := failures.push s!"{f}: {e}"; continue
    if spec.only? != some "hosted" then
      let (out, code) ← runCheck #[f.toString]
      let (diags, summary) := cliDiagnostics f.toString out
      for e in check "cli" spec diags summary (some code.toNat) do
        failures := failures.push s!"{f} (binary): {e}"
      cliStopped := some (out.contains s!"error: {Fren.Core.couldNotHeadline}")
    if spec.only? != some "cli" then
      let (diags, summary) ← hostedDiagnostics env f.toString src
      let stopped := diags.any isStopped
      for e in check "hosted" spec (diags.filter (!isStopped ·)) summary none do
        failures := failures.push s!"{f} (Lean): {e}"
      -- Both front ends say that a static error stopped the checks, or
      -- neither does (`cli::agreement`).
      if let some c := cliStopped then
        if c != stopped then
          failures := failures.push
            s!"{f}: {if c then "only the binary" else "only Lean"} says `{Fren.Core.couldNotHeadline}`"
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
depends on the machine; and removed codes, which nothing reports, and
whose explanations say what replaced them. -/
def unsnapshotted : List String :=
  [
    -- keep-sorted start
    "F0137",
    "F0142",
    "F0143",
    "F0155",
    "F0156",
    "F0158",
    "F0159",
    "F0160",
    "F0164",
    "F0369",
    "F0370",
    "F0399",
    "F0406",
    "F0407",
    "F0412",
    "F0413",
    "F0414",
    "F0415",
    "F0416",
    "F0420",
    "F0448",
    "F0608",
    "F0622",
    "F0623",
    "F0713",
    -- keep-sorted end
  ]

/-- The rows of the table of lints in `Reqs/Lint.md` that disagree with
the code: each lint's row gives its name, code, group and default level,
and each row is a lint's. keep-sorted keeps the rows in order of name. -/
def lintTable : IO (Array String) := do
  let md ← IO.FS.readFile ("src" / "Reqs" / "Lint.md")
  let cell (c : String) := ((c.trimAscii.toString.dropPrefix "`").dropSuffix "`").toString
  let rows := (md.splitOn "\n").filterMap fun line =>
    match line.splitOn "|" with
    | _ :: name :: code :: group :: dflt :: _ =>
      if (code.trimAscii.toString.startsWith "`F0") then some (cell name, cell code, cell group, cell dflt) else none
    | _ => none
  let want := Fren.Core.Lint.all.map fun l => (l.name, l.code, l.group.name, l.default.name)
  let mut failures := #[]
  for w in want do
    unless rows.contains w do
      failures := failures.push s!"{w.1}: no row `| `{w.1}` | `{w.2.1}` | `{w.2.2.1}` | `{w.2.2.2}` |` in the table of src/Reqs/Lint.md"
  for r in rows do
    unless want.contains r do failures := failures.push s!"{r.1}: a row of the table of src/Reqs/Lint.md that is no lint as written"
  return failures

/-- `Fren.Core.leanBangTokens` and `Fren.Core.leanKeywords` list Lean's
tokens, with `Fren` imported and `Fren.Lang` open, that are an identifier
followed by `!`, and that have the shape of an identifier but are not
reserved words (`Reqs/Lang/Lexical#keywords`). The tokens are those of the
`lean` that Lake runs, which has builtin parsers, and so tokens, that this
program does not link. -/
def leanTokens : IO (Array String) := do
  let src := "import Fren\nopen Fren.Lang\nopen Lean Elab Command in\n" ++
    "#eval show CommandElabM Unit from do\n" ++
    "  for t in (Lean.Parser.getTokenTable (← getEnv)).values do IO.println t\n"
  let child ← IO.Process.spawn { cmd := ((← findSysroot) / "bin" / "lean").toString, args := #["--stdin"]
                                 stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr src
  stdin.flush
  let (_, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept stdout.get
  if code != 0 then return #[s!"leanTokens: `lean` failed (exit {code}):\n{out}{stderr}"]
  let toks := ((out.splitOn "\n").filter (!·.isEmpty)).toArray.qsort (· < ·)
  -- An identifier of Fren's, without its `!`: `?` only at its end.
  let isIdent (t : String) := (t.front.isAlpha || t.front == '_') && !(t.dropEnd 1).contains '?'
    && t.all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '?'
  let bang := toks.filter fun t => t.length > 1 && t.endsWith "!" && isIdent (t.dropEnd 1).toString
  let keywords := toks.filter fun t => t != "_" && !FrenCli.reserved.contains t && isIdent t
  let mut failures := #[]
  unless bang == Fren.Core.leanBangTokens.toArray.qsort (· < ·) do
    failures := failures.push s!"Fren.Core.leanBangTokens: Lean's tokens that are an identifier and `!` are {bang}"
  unless keywords == Fren.Core.leanKeywords.toArray.qsort (· < ·) do
    failures := failures.push s!"Fren.Core.leanKeywords: Lean's keywords that are identifiers are {keywords}"
  return failures

/-- Every code is explained and covered by a snapshot; each explanation's
erroneous example reports its code, and its fixed versions report no static
errors and not the code. -/
def errorCodes : IO (Array String) := do
  let mut failures := #[]
  let codes := Fren.Core.errorCodes.map (·.code)
  failures := failures ++ (← lintTable)
  if codes.toList.eraseDups.length != codes.size then failures := failures.push "error codes: duplicate codes"
  -- fren-covers: view::code_group
  for c in codes ++ Fren.Core.Lint.all.map (·.code) do
    let ok := c.length == 5 && c.startsWith "F0" && (c.toList.drop 2).all Char.isDigit
      && ['1', '2', '3', '4', '5', '6', '7', '8'].contains (c.toList[2]!)
    unless ok do failures := failures.push s!"{c}: not of the form `F0` followed by a group from 1 to 8 and two digits"
  let snapshots ← (← sortedFiles ("test" / "cli") "expected").mapM IO.FS.readFile
  for c in ← codesInSources do
    unless codes.contains c do failures := failures.push s!"{c}: used in the sources but not explained in `src/FrenCore/Codes/{c}.md`"
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

/-- The Markdown specs of Fren's own requirements, in an order in which
each module is declared before it is used. -/
def ownSpecFiles : Array String :=
  #[
    "Lang/Overview",
    "Lang/Lexical",
    "Lang/Types",
    "Lang/SubsetTypes",
    "Lang/BooleanBlocks",
    "Lang/Items",
    "Lang/Generics",
    "Lang/GenericFunctions",
    "Lang/Prelude",
    "Lang/Scope",
    "Lang/Procedures",
    "Lang/Global",
    "Lang/Decidability",
    "Lang/Patterns",
    "Lang/Let",
    "Lang/Quantifiers",
    "Lang/ElementQuantifiers",
    "Lang/Semantics",
    "Lang/EvaluationRules",
    "Lang/Expressions",
    "Lang/HigherOrder",
    "Lang/Recursion",
    "Lang/ScopeLaws",
    "Lang/Modules",
    "Lang/Calls",
    "Check",
    "View",
    "Cli",
    "Lint",
    "Lint/Meaning",
    "Lint/Unused",
    "Lint/NonstandardStyle",
    "Lint/Style",
    "Lint/Style/Comparisons",
    "Lint/Style/PatternTests",
    "Lint/Style/PatternTestFixes",
    "Lint/Style/Naturals",
    "Lint/Style/Records",
    "Lint/Style/Matches",
    "Lint/Style/Let",
    "Lint/Style/Closures",
    "Lint/Complexity",
    "Lint/Complexity/Comparisons",
    "Lint/Complexity/Operators",
    "Lint/Complexity/Methods",
    "Lint/Complexity/Matches",
    "Lint/Complexity/Patterns",
    "Lint/Complexity/Integers",
    "Lint/Complexity/Updates",
    "Lint/Suspicious",
    "Lint/Suspicious/Expressions",
    "Lint/Suspicious/Methods",
    "Lint/Suspicious/Literals",
    "Lint/Suspicious/Comparisons",
    "Lint/Suspicious/Integers",
    "Lint/Pedantic",
    "Lint/Pedantic/Matches",
    "Lint/Pedantic/Records",
    "Lint/Pedantic/Text",
    "Lint/Pedantic/Comparisons",
    "Lint/Pedantic/Conditionals",
    "Lint/Restriction",
    "Lint/Decidability",
    "Lint/Printing",
    "Eval",
    "Lang/Refinement",
    "Mutate",
    "Fmt",
    "Impl",
    "Generated",
    "Trace",
  ].map fun r => s!"src/Reqs/{r}.md"

/-- The Markdown specs that the Lean front end reads, by the `#fren_md`
commands of `src/Reqs`, each as a path from the repository's root. -/
def hostedSpecFiles : IO (Array String) := do
  let mut files := #[]
  for entry in ← System.FilePath.readDir "src/Reqs" do
    if entry.path.extension != some "lean" then continue
    for line in (← IO.FS.readFile entry.path).splitOn "\n" do
      if let [_, rest] := line.splitOn "#fren_md \"" then
        if let some name := (rest.splitOn "\"").head? then files := files.push s!"src/Reqs/{name}"
  return files

/-- The lines of the `fren` blocks of the Markdown text `md`. -/
def frenBlockLines (md : String) : Array String := Id.run do
  let mut out := #[]
  let mut inBlock := false
  for line in md.splitOn "\n" do
    if line.startsWith "```" then inBlock := line.startsWith "```fren"
    else if inBlock then out := out.push line
  return out

/-- The procedures and global expectations that the `fren` block lines
`ls` declare, which a `#fren_check` checks: each by its name. -/
def checkedItems (ls : Array String) : Array String :=
  ls.filterMap fun l =>
    let l := ((l.dropPrefix? "pub ").map (·.toString)).getD l
    let word (pre : String) : Option String := (l.dropPrefix? pre).map fun r =>
      (r.toString.takeWhile fun c => c.isAlphanum || c == '_' || c == '?').toString
    (word "proc ").orElse fun _ => word "expect "

/-- The problems of Lean's checks of `src/Reqs`: each chapter that a Lean file
reads by `#fren_md`, and that declares procedures or global expectations, is
checked by a `#fren_check` without a path in it or in a later chapter of
that file, or by a `#fren_check` of each of them in it. A `#fren_check`
checks what is declared before it in its file (`Reqs/Lean#commands`), so a
chapter after a file's last one is not checked in Lean at all: the hosted
counterpart of `ownSpecFiles`. -/
def hostedChecks : IO (Array String) := do
  let mut failures := #[]
  for entry in ← System.FilePath.readDir "src/Reqs" do
    if entry.path.extension != some "lean" then continue
    let chapters := (← IO.FS.readFile entry.path).splitOn "\n" |>.filterMap fun line =>
      match line.splitOn "#fren_md \"" with
      | [_, rest] => (rest.splitOn "\"").head?
      | _ => none
    let texts ← chapters.toArray.mapM fun (c : String) => IO.FS.readFile (("src" : FilePath) / "Reqs" / c)
    -- A chapter's `#fren_check`s, in its `fren` blocks or on lines of their own.
    let checks := texts.map fun t => (t.splitOn "\n").toArray.filter (·.trimAscii.toString.startsWith "#fren_check")
    for c in chapters.toArray, t in texts, k in [0:texts.size] do
      let items := checkedItems (frenBlockLines t)
      if items.isEmpty then continue
      let bare := (checks.extract k checks.size).any (·.any (·.trimAscii.toString == "#fren_check"))
      let named := checks[k]!.filterMap fun l => (l.trimAscii.toString.dropPrefix? "#fren_check ").map (·.toString.trimAscii.toString)
      for i in items do
        unless bare || named.contains i do
          failures := failures.push s!"src/Reqs/{c}: `{i}` is checked by no `#fren_check` in Lean, as the chapter comes after its file's last `#fren_check`: name it, as `#fren_check {i}`"
  return failures

/-- Fren's own requirements pass under the binary, and it checks every
chapter that the Lean front end does; and Lean checks every chapter too
(`hostedChecks`). -/
def ownSpec : IO (Array String) := do
  let missing := (← hostedSpecFiles).filter (!ownSpecFiles.contains ·)
  let (out, code) ← runCheck ownSpecFiles
  return (missing.map (s!"{·} is read by `#fren_md` but not in `ownSpecFiles`, so the binary does not check it"))
    ++ (if code == 0 then #[] else #[s!"src/Reqs failed under the binary:\n{out}"])
    ++ (← hostedChecks)

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
  ["test/cli/syntax/*.fren", "test/cli/names/f0216_member_option.fren", "test/cli/fix/*.fren", "test/cli/fmt/check.fren",
   "test/cli/fmt/chain_error.fren", "test/cli/fmt/quantifier.fren", "test/cli/fmt/quantifier_error.fren", "test/cli/fmt/quantifier_unbounded.fren",
   "test/cli/fmt/is.fren", "test/cli/fmt/parse_error.fren", "test/cli/fmt/patterns.fren", "test/cli/fmt/shadow.fren", "test/cli/fmt/update.fren",
   "test/cli/fmt/cover.fren",
   "test/cli/fmt/generics.fren", "test/cli/fmt/generic_functions.fren", "test/cli/fmt/closures.fren",
   "test/cli/fmt/newtypes.fren",
   "test/cli/fmt/table.fren", "test/cli/fmt/pattern_types.fren",
   "test/cli/fmt/contract.fren",
   "test/cli/fmt/guards.fren", "test/cli/fmt/table_scrutinee.fren",
   "test/cli/commands/mutate_unformatted.fren", "test/ui/lints/unary_formatting.fren",
   "test/cli/lints/suspicious/f0762_suspicious_unary_op_formatting.fren", "test/ui/syntax/*.fren", "test/ui/lean/*.fren",
   "test/ui/checks/trace.fren", "src/Reqs/Markdown.md",
   -- The explanations of the codes, whose first examples are erroneous.
   "src/FrenCore/Codes/*.md",
   -- The README's example keeps its hand-aligned continuation lines.
   "README.md",
   -- `#fren_md` in a block, which only the Lean front end reads.
   "src/FrenTest/chapters/LiterateOuter.md", "src/FrenTest/chapters/LiterateReader.md",
   "src/FrenTest/chapters/deep/LiterateDeep.md", "src/FrenTest/chapters/LiterateReplacing.md",
   -- Lean code in a block, likewise.
   "src/FrenTest/chapters/LiterateNoPosition.md",
   -- Trailing commas that `unnecessary_trailing_comma` reports.
   "test/cli/lints/pedantic/f0801_unnecessary_trailing_comma.fren", "test/ui/lints/ranges_literals_commas.fren"]

/-- What formatting keeps (`fmt::safe`): the tokens, but for the trailing
commas of lists and claims and for `use` items; the paths the `use` items
import, sorted; and the comments. -/
def fmtKept (path src : String) : Option (Array String × Array (Array String) × Array String) := do
  let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
  let chars := src.toList.toArray
  let (toks, comments) ← (FrenCli.lexWithComments chars).toOption
  let lay ← (FrenCli.parseLayout toks chars).toOption
  let inUse (k : Nat) : Bool := lay.uses.any fun (f, l) => f ≤ k && k ≤ l
  let isStr (k : Nat) : Bool := toks[k]?.any (·.tok matches .str _)
  let mut kept := #[]
  for h : k in [0:toks.size] do
    if inUse k then continue
    let t := toks[k]
    let trailing := t.tok == .kw "," &&
      (toks[k + 1]?.any (fun n => n.tok == .kw "}" || n.tok == .kw ")") || (k > 0 && isStr (k - 1) && !isStr (k + 1)))
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
    out := out ++ s!"proc c{k}(s: String, t: String): (p?) \{\n    \
      assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
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
    out := out ++ s!"proc c{k}(s: Set<Int>, t: Set<Int>, x: Int, es: Set<E>, e: E): (p?) \{\n    \
      assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
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
    out := out ++ s!"proc c{k}(r: Rel<E, E>, q: Rel<E, E>, s: Set<E>, x: E, y: E): (p?) \{\n    \
      assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
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
    out := out ++ s!"proc c{k}(q: Seq<Int>, r: Seq<Int>, x: Int, i: Int): (p?) \{\n    \
      assume a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
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
  let src ← IO.FS.readFile ("test" / "cli" / "fmt" / "check.fren")
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
    "\nMore prose.\n\n" ++ block s!"mod n\n\n{uses}proc c(x: Mode): (h?) \{\n    ensure r: h? iff x = Heat\n}"
  IO.FS.writeFile file (spec "use m::Mode\nuse m::Mode::*\nuse m::Mode::Cool\n\n")
  let (out, code) ← runFren ["fix", file]
  let written ← IO.FS.readFile file
  let want := spec "use m::Mode\nuse m::Mode::Heat\n\n"
  if code != 0 || written != want then
    failures := failures.push s!"`fren fix` did not fix {file} in place (exit {code}):\n{out}\n{written}"
  let (out, code) ← runFren ["fix", "--check", file]
  if code != 0 || !out.isEmpty then
    failures := failures.push s!"`fren fix --check` reports a fixed file (exit {code}):\n{out}"
  -- fren-covers: cli::fix_static_errors
  -- A static error in any input rejects the whole write transaction.
  let other := ".lake/fix-test/invalid.md"
  let unfixed := spec "use m::Mode\nuse m::Mode::*\nuse m::Mode::Cool\n\n"
  for invalid in #[
      "proc p(x: Int): (y: Int) { ensure same: y = x }\nexpect old: forall (a: p), a.y = a.x",
      "refine old: missing refines missing"] do
    let text := "# Invalid\n\nProse stays byte for byte.\n\n" ++ block invalid
    for flags in #[#[], #["--check"], #["--fmt"], #["--only", "unused_imports"]] do
      IO.FS.writeFile file unfixed
      IO.FS.writeFile other text
      let (out, code) ← runFren (["fix"] ++ flags.toList ++ [file, other])
      if code != 2 || (← IO.FS.readFile file) != unfixed || (← IO.FS.readFile other) != text then
        failures := failures.push s!"invalid input changed a file under `fren fix` (exit {code}):\n{out}"
  -- fren-covers: lint::labelled_clause_identity
  -- Removing a duplicated block member must preserve every other byte,
  -- and the result must remain valid and need no further fixes.
  for fixture in #["labeled_constraints", "labeled_constraints_readme"] do
    let original ← IO.FS.readFile ("test/cli/fix" / (fixture ++ ".fren"))
    let target : System.FilePath := ".lake/fix-test" / (fixture ++ ".fren")
    IO.FS.writeFile target original
    let (out, code) ← runFren ["fix", target.toString]
    let expected := original.replace "        copy: x > 0, -- remove only this member and its comment\n" ""
      |>.replace "        copy: x > 0, -- remove the comma too\n" ""
    if code != 0 || (← IO.FS.readFile target) != expected then
      failures := failures.push s!"labelled constraint fix changed siblings or wrappers: {fixture} (exit {code}):\n{out}"
    let (out, code) ← runFren ["fix", "--check", target.toString]
    if code != 0 || !out.isEmpty then
      failures := failures.push s!"labelled constraint fix was not valid and idempotent: {fixture} (exit {code}):\n{out}"
  -- fren-covers: lang::match_vector
  -- A value-level match rewrite would lose an implicit closure's scope.
  let original ← IO.FS.readFile "test/ui/lang/lambda_match.fren"
  let target := ".lake/fix-test/lambda_match.fren"
  IO.FS.writeFile target original
  for flags in #[#[], #["--check"]] do
    let (out, code) ← runFren (["fix"] ++ flags.toList ++ [target])
    if code != 0 || !out.isEmpty || (← IO.FS.readFile target) != original then
      failures := failures.push s!"implicit match fix changed its closure or scope (exit {code}):\n{out}"
  return failures

/-! ## Libraries

Some modules copy a list of imports, or are placed in a library by what
they read, so that the build is faster (`lakefile.lean`); nothing else
would notice if those drifted. -/

/-- Modules that import a root module's modules rather than the root, which
would wait for its own build too: each must import exactly the root's. -/
def rootCopies : List (String × List String) :=
  [("Fren", ["Reqs.Check", "Reqs.Calls", "Reqs.Lang", "Reqs.Modules"])]

/-- The libraries of Reqs that need only some of its specs, as module and
the specs, relative to `src/Reqs`, that it may read. -/
def specsRead : List (List String × (String → Bool)) :=
  [(["Reqs.Check", "Reqs.Cli", "Reqs.Eval", "Reqs.Fmt", "Reqs.Generated", "Reqs.Impl", "Reqs.Mutate", "Reqs.Trace", "Reqs.View"],
      fun p => !p.contains '/'),
    (["Reqs.Calls", "Reqs.Lang", "Reqs.Modules", "Reqs.Refine"], (·.startsWith "Lang/")),
    (["Reqs.Lint"], fun p => p == "Lint.md" || p.startsWith "Lint/")]

/-- The modules of Impls whose library needs the tests, `ImplsTested` in
`lakefile.lean` (`libraryGlobs`). -/
def testReaders : List String := ["src/Impls.lean", "src/Impls/Lint.lean", "src/Impls/Trace.lean"]

/-- The source file of module `m`. -/
def sourceOf (m : String) : System.FilePath := "src" / ((m.replace "." "/") ++ ".lean")

/-- The source files of the modules in the `globs` of the library `lib` in
`lakefile.lean`, when they are plain module names. -/
def libraryGlobs (lib : String) : IO (List String) := do
  let text ← IO.FS.readFile "lakefile.lean"
  let some after := (text.splitOn s!"lean_lib {lib} where")[1]? | return []
  let some globs := (after.splitOn "globs := #[")[1]? | return []
  let names := ((globs.splitOn "]").headD "").splitOn "," |>.map fun n => ((n.trimAscii.toString.dropPrefix "`").toString)
  return names.filter (!·.isEmpty) |>.map fun n => (sourceOf n).toString

/-- The modules that `m` imports. -/
def importsOf (m : String) : IO (Array String) := do
  let path := sourceOf m
  let header ← Lean.parseImports' (← IO.FS.readFile path) path.toString
  return header.imports.map (·.module.toString)

/-- The files that the `#fren_md` commands of the source `src` read. -/
def specsOf (src : String) : Array String :=
  (src.splitOn "\n").toArray.filterMap fun line =>
    if line.startsWith "#fren_md \"" then (line.drop 10).takeWhile (· != '"') |>.toString else none

/-- Each copy of a root's imports is the root's; each module of Reqs reads
only the specs that its library needs; and only modules whose library
needs the tests make `tested` claims. -/
def libraries : IO (Array String) := do
  let mut failures := #[]
  for (root, copies) in rootCopies do
    let ofRoot (ms : Array String) := (ms.filter (·.startsWith s!"{root}.")).qsort (· < ·)
    let want := ofRoot (← importsOf root)
    for m in copies do
      let got := ofRoot (← importsOf m)
      if got != want then
        failures := failures.push s!"{sourceOf m}: imports {got.toList} of `{root}`'s modules, not `{root}`'s {want.toList}"
  for (mods, ok) in specsRead do
    for m in mods do
      for spec in specsOf (← IO.FS.readFile (sourceOf m)) do
        unless ok spec do
          failures := failures.push s!"{sourceOf m}: reads `{spec}`, which its library in `lakefile.lean` does not need"
  let tested ← libraryGlobs "ImplsTested"
  unless tested.toArray.qsort (· < ·) == testReaders.toArray.qsort (· < ·) do
    failures := failures.push s!"lakefile.lean: `ImplsTested` holds {tested}, but `testReaders` in src/FrenTestMain.lean is {testReaders}"
  for f in (← System.FilePath.walkDir "src/Impls").push "src/Impls.lean" do
    if f.extension != some "lean" || testReaders.contains f.toString then continue
    if (← IO.FS.readFile f).splitOn "\n" |>.any (·.startsWith "tested ") then
      failures := failures.push s!"{f}: makes a `tested` claim, but its library in `lakefile.lean` does not need the tests"
  return failures

/-! ## Mutants

The properties of `fren mutate`'s mutants (`Reqs/dev/Testing`), over the
*corpus*: Fren's own requirements, each snapshot of `fren mutate`, and
each example of its decisions (`decisions`). -/

/-- The examples of `fren mutate`'s decisions. -/
def decisionExamples : IO (Array FilePath) := sortedFiles ("test" / "mutate") "fren"

/-- The corpus, as groups of files: Fren's own requirements first. -/
def mutationCorpus : IO (Array (Array String)) := do
  let snaps := (← sortedFiles ("test" / "cli") "fren").filter fun f =>
    let n := f.fileName.getD ""
    n.startsWith "mutate_" || n.startsWith "f0613" || n.startsWith "f0614"
  return #[ownSpecFiles] ++ (snaps ++ (← decisionExamples)).map fun f => #[f.toString]

/-- The files of a group, read as `fren` reads them. -/
def readGroup (paths : Array String) : IO (Array (String × Array Char)) :=
  paths.mapM fun (path : String) => do
    let src ← IO.FS.readFile path
    let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
    return (path, src.toList.toArray)

/-- The mutants of Fren's own requirements are checked in this many jobs,
each taking every `n`th mutant; every other group is one job. -/
def mutationSlices : Nat := 8

/-- The mutants of the text `chars` of file `file`, whose parse is
`parsed` (`FrenCli.parseText`), as `fren` makes them, where the spec's
enumerations are `enums`. -/
def mutantsOfParsed (file : Nat) (path : String) (chars : Array Char) (parsed : FrenCli.Parsed)
    (enums : FrenCli.Mutate.Enums) : Array FrenCli.Mutate.Mutant :=
  match parsed with
  | .ok (toks, items, _) => FrenCli.Mutate.ofFile { file, path, chars, toks, enums } items
  | .error _ => #[]

/-- The mutants of the text `chars` of file `file`, as `fren` makes them. -/
def mutantsOfText (file : Nat) (path : String) (chars : Array Char) (enums : FrenCli.Mutate.Enums) : Array FrenCli.Mutate.Mutant :=
  mutantsOfParsed file path chars (FrenCli.parseText chars) enums

/-- The tree of a chained comparison of `es` with the operators `ops`, as
`shapeWith` writes it: with one operator, a comparison. -/
def chainShape (go : FrenCli.Expr → String) (es : Array FrenCli.Expr) (ops : Array String) : String :=
  if ops.size == 1 then s!"({ops[0]!} {go es[0]!} {go es[1]!})"
  else s!"(chain {go es[0]!}{String.join ((ops.zip (es.extract 1)).toList.map fun (op, e) => s!" {op} {go e}")})"

open FrenCli in
/-- The tree of `e`, without spans or parentheses, but where `f` gives a
node's tree instead: operators with their operands, and leaves as their
text. -/
partial def shapeWith (s : Mutate.Src) (f : FrenCli.Expr → Option String) (e : FrenCli.Expr) : String :=
  let go := shapeWith s f
  let list (es : Array FrenCli.Expr) := " ".intercalate (es.toList.map go)
  match f e with
  | some t => t
  | none => match e with
    | .bin _ op l r => s!"({op} {go l} {go r})"
    | .when _ neg c b => s!"({if neg then "unless" else "when"} {go c} {go b})"
    | .ite _ c a b => s!"(if {go c} {go a} {go b})"
    | .not _ e => s!"(not {go e})"
    | .neg _ e => s!"(- {go e})"
    | .app _ fn as => s!"(app {fn.map (·.name)} {list as})"
    | .record _ ty fs => s!"(record {ty.map (·.name)} {fs.toList.map fun (x, e?) => (x.name, e?.map go)})"
    | .update _ r fs => s!"(update {go r} {fs.toList.map fun (x, e?) => (x.name, e?.map go)})"
    | .field _ e x => s!"(field {go e} {x.name})"
    | .match _ sc arms _ =>
      s!"(match {go sc} {arms.toList.map fun (p, g?, b) => (Mutate.idText (s.text p.span), g?.map go, go b)})"
    | .matches _ scs arms _ =>
      s!"(matches {list scs} {arms.toList.map fun (ps, g?, b) =>
        (ps.toList.map fun (p : FrenCli.Pattern) => Mutate.idText (s.text p.span), g?.map go, go b)})"
    | .is _ sc p => s!"(is {go sc} {Mutate.idText (s.text p.span)})"
    | .set _ es => s!"(set {list es})"
    | .pair _ a b => s!"(pair {go a} {go b})"
    | .seq _ es => s!"(seq {list es})"
    | .index _ a i => s!"(index {go a} {go i})"
    | .method _ r x as => s!"(method {go r} {x.name} {list as})"
    | .chain _ es ops => chainShape go es (ops.map (·.1))
    | .«let» _ defs body w =>
      s!"({if w then "where" else "let"} {defs.toList.map fun (x, _, d) => (x.name, go d)} {go body})"
    | .quant _ all bs b => s!"({if all then "forall" else "exists"} {bs.toList.map fun x => Mutate.idText (s.text x.span)} {go b})"
    | .table _ rows => s!"(table {rows.toList.map fun (_, c?, v) => (c?.map go, go v)})"
    | .closure _ ps b => s!"(closure {ps.toList.map fun (x, _) => x.name} {go b})"
    | e => Mutate.idText (s.text e.span)

open FrenCli in
/-- The tree that the operator mutant `m` means to make of `e`. -/
def intended (s : Mutate.Src) (m : Mutate.Mutant) (e : FrenCli.Expr) : String :=
  let plain := shapeWith s fun _ => none
  shapeWith s (fun
    | .bin sp op l r =>
      let opAt := (s.wordIn { start := l.span.stop, stop := r.span.start } op).any (·.span == m.span)
      if m.origin == .dropConjunct && sp == m.span then
        some (if Mutate.idText m.after == Mutate.idText (s.text (s.outer sp l.span)) then plain l else plain r)
      else if m.origin != .dropConjunct && opAt then some s!"({m.after} {plain l} {plain r})"
      else if m.origin == .swapAndOr && sp == m.span then some s!"({if op == "and" then "or" else "and"} {plain l} {plain r})"
      else none
    | .chain sp es ops =>
      let names := ops.map (·.1)
      if let some k := ops.findIdx? (·.2 == m.span) then
        some (chainShape plain es (names.set! k m.after))
      else if m.origin == .dropConjunct && sp == m.span then
        let dropFirst := Mutate.idText m.after == Mutate.idText (s.text { start := (s.outer sp es[1]!.span).start, stop := sp.stop })
        some (if dropFirst then chainShape plain (es.extract 1) (names.extract 1) else chainShape plain es.pop names.pop)
      else none
    | .quant sp all bs b =>
      if m.origin == .swapQuantifier && sp.start == m.span.start then
        some s!"({if all then "exists" else "forall"} {bs.toList.map fun x => Mutate.idText (s.text x.span)} {plain b})"
      else none
    | .when sp neg c b =>
      if m.origin == .negateTrigger && sp.start == m.span.start then some s!"({if neg then "when" else "unless"} {plain c} {plain b})"
      else if m.origin == .dropTrigger && sp == m.span then some (plain b)
      else none
    | .ite sp c a b =>
      if m.origin == .swapBranches && (s.outer sp a.span).start == m.span.start && (s.outer sp b.span).stop == m.span.stop then
        some s!"(if {plain c} {plain b} {plain a})"
      else none
    | .not sp k | .neg sp k => if m.origin == .dropNegation && sp == m.span then some (plain k) else none
    | _ => none) e

/-- The expressions of the items of the text `chars` that mutants change. -/
def sitesOfParsed (parsed : FrenCli.Parsed) : Array (Lean.Name × FrenCli.Expr) :=
  match parsed with
  | .ok (_, items, _) => (FrenCli.Mutate.sites items).map fun (n, _, e) => (n, e)
  | .error _ => #[]

def sitesOfText (chars : Array Char) : Array (Lean.Name × FrenCli.Expr) := sitesOfParsed (FrenCli.parseText chars)

/-- Swaps, which a second swap undoes. -/
def isSwap (m : FrenCli.Mutate.Mutant) : Bool :=
  [.swapComparison, .swapArithmetic, .negateTrigger, .swapQuantifier, .flipBool, .swapRepetition, .swapRows, .swapBranches, .swapArms,
    .swapMinMax, .swapAffix].contains m.origin
    || (m.origin == .swapAndOr && !m.after.startsWith "(")

deriving instance BEq for FrenCli.CClaim
deriving instance BEq for Fren.Core.UseRecord
deriving instance BEq for Fren.Core.ExpectationRecord
deriving instance BEq for Fren.Core.LintReport
deriving instance BEq for FrenCli.UseLoc
deriving instance BEq for Fren.Core.ItemRecord
deriving instance BEq for Fren.Core.HofParamRecord
deriving instance BEq for Fren.Core.FnArgRecord
deriving instance BEq for FrenCli.LintFix
deriving instance BEq for FrenCli.NatReport
deriving instance BEq for Fren.Core.SettingRecord
deriving instance BEq for Fren.Core.AssumptionRecord

/-- Whether `a` and `b` agree on what `fren mutate` reads of a mutant's
state (`FrenCli.mutate`). -/
def sameForMutate (a b : FrenCli.State) : Bool :=
  let diag (d : FrenCli.Diag) := s!"{d.file} {d.span.start} {d.span.stop} {repr d.severity} {repr d.msg} {d.lint?.map (·.ctorIdx)} {d.fixed}"
  a.diags.map diag == b.diags.map diag && a.comps == b.comps && a.globals == b.globals
    && a.bodies == b.bodies && a.defs == b.defs && a.preludeText == b.preludeText && a.consts.toList == b.consts.toList
    && a.constInts.toList == b.constInts.toList && FrenCli.sameForLater a b

/-- Every mutant of the corpus:
- **well-formed:** changes the text, and elaborates with no static error;
- **identified:** has an identifier that no other mutant of its group has;
- **stable:** leaves the identifiers of the mutants of other items alone,
  and keeps its own when the file is formatted with `fren fmt`;
- **involutive:** if it is a swap, has a mutant that swaps back;
- **as intended:** if it changes an operator, parses as the tree intended,
  with each other operator binding as before.

And a larger sample of mutants contains a smaller one, and the shards of
a selection partition it.

These are the checks of the group `paths` for the mutants whose index is
`slice` modulo `slices`; the checks of the whole group are in slice 0. Each
slice computes every mutant of the group, which the checks of one mutant
compare it with. -/
def mutation (paths : Array String) (slice slices : Nat) : IO (Array String) := do
  let mut failures := #[]
  let files ← readGroup paths
  let (before, all) := FrenCli.mutantsOf files #[]
  let parsed := files.map (FrenCli.parseText ·.2)
  let names := parsed.map FrenCli.writtenNames
  let enums := FrenCli.Mutate.enumsOf (parsed.flatMap fun
    | .ok (_, items, _) => items
    | .error _ => #[])
  let ids := all.map (·.id)
  if slice == 0 && ids.toList.eraseDups.length != ids.size then
    failures := failures.push s!"mutants of {files.map (·.1)}: duplicate identifiers"
  -- The tokens and sites of each file, unmutated.
  let toks := files.map fun (_, chars) => (FrenCli.lex chars).toOption.getD #[]
  let fileSites := files.map fun (_, chars) => sitesOfText chars
  for m in all, i in [0:all.size] do
    if i % slices != slice then continue
    let (path, chars) := files[m.file]!
    let chars' := m.apply chars
    if chars' == chars then failures := failures.push s!"{m.id}: changes nothing"
    -- Lexed and parsed once, for each of the reads below.
    let parsed' := FrenCli.parseText chars'
    -- Only the mutated file: mutants change no declaration, so the files
    -- after it elaborate as before.
    let st := FrenCli.elabParsed (before[m.file]?.getD {}) m.file chars' parsed'
    -- Some of the mutants: `mutantState`, which elaborates again only the
    -- files after it that it must, reads as elaborating all of them again.
    if (i / slices) % 16 == 0 then
      let all := (files.extract (m.file + 1)).zipIdx.foldl (init := st) fun s ((_, cs), k) =>
        FrenCli.elabParsed s (m.file + 1 + k) cs parsed[m.file + 1 + k]!
      unless sameForMutate (FrenCli.mutantState files parsed names before m chars' parsed') all do
        failures := failures.push s!"{m.id}: `mutantState` differs from elaborating every file after it again"
    if let some d := (st.diags.filter fun d => d.severity == .error && d.file == m.file)[0]? then
      failures := failures.push s!"{m.id}: has a static error: {d.msg.headline}"
    let again := mutantsOfParsed m.file path chars' parsed' enums
    let againIds : Std.HashSet String := .ofArray (again.map (·.id))
    for m₂ in all do
      if m₂.file == m.file && m₂.item != m.item && !againIds.contains m₂.id then
        failures := failures.push s!"{m₂.id}: its identifier changes when {m.id} is applied"
    if m.origin == .narrowClass && chars[m.span.start - 1]? == some '[' && chars[m.span.stop]? == some '^' then
      failures := failures.push s!"{m.id}: leaves `^` first in a class, negating it"
    if isSwap m && !again.any (fun b => b.origin == m.origin && b.apply chars' == chars) then
      failures := failures.push s!"{m.id}: no mutant swaps it back"
    if [.swapComparison, .swapArithmetic, .swapAndOr, .dropConjunct, .negateTrigger, .swapQuantifier, .swapBranches, .dropNegation,
        .dropTrigger].contains m.origin then
      let src : FrenCli.Mutate.Src := { file := m.file, path, chars, toks := toks[m.file]! }
      let src' : FrenCli.Mutate.Src := { src with chars := chars', toks := (FrenCli.lex chars').toOption.getD #[] }
      let sites := fileSites[m.file]!
      let sites' := sitesOfParsed parsed'
      match (Array.range sites.size).find? fun k =>
          sites[k]!.1 == m.item && sites[k]!.2.span.start ≤ m.span.start && m.span.stop ≤ sites[k]!.2.span.stop with
      | some k =>
        let want := intended src m sites[k]!.2
        let got := (sites'[k]?.map fun (_, e) => shapeWith src' (fun _ => none) e).getD "(missing)"
        if want != got then failures := failures.push s!"{m.id}: parses as {got}, not {want}"
      | none => failures := failures.push s!"{m.id}: is in no site of its item"
  -- Each file elaborates as it does after a state whose fields that
  -- `elabFile` sets before reading them are another file's, or the first's
  -- (`State.withPerFileOf`), so `sameForLater` need not compare them.
  if slice == 0 then
    for (_, chars) in files, j in [0:files.size] do
      let other := before[if j == 0 then files.size else 0]?.getD {}
      let st := FrenCli.elabParsed (before[j]?.getD {}) j chars parsed[j]!
      let st' := FrenCli.elabParsed ((before[j]?.getD {}).withPerFileOf other) j chars parsed[j]!
      unless same_fields% FrenCli.State st st' except [bound] && st.bound.size == st'.bound.size do
        failures := failures.push s!"{files[j]!.1}: elaborates differently after a state with another file's per-file fields"
  if slice != 0 then return failures
  -- Formatting each file keeps the identifiers.
  for (path, chars) in files, i in [0:files.size] do
    let src ← IO.FS.readFile path
    let .ok formatted := FrenCli.Fmt.formatFile path src | failures := failures.push s!"{path}: does not format"
    let text := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown formatted else formatted
    let ids := (mutantsOfText i path chars enums).map (·.id)
    let ids' := (mutantsOfText i path text.toList.toArray enums).map (·.id)
    if ids.qsort (· < ·) != ids'.qsort (· < ·) then
      failures := failures.push s!"{path}: formatting changes the identifiers of {(ids.filter (!ids'.contains ·)).toList}"
  for n in [0:20] do
    let small := FrenCli.Mutate.select all none #[] (some n) 7 |>.map (·.id)
    let large := FrenCli.Mutate.select all none #[] (some (n + 1)) 7 |>.map (·.id)
    unless small.all large.contains && small.size == min n all.size do
      failures := failures.push s!"mutants of {files.map (·.1)}: a sample of {n + 1} does not contain the sample of {n}"
  -- The shards of a selection, sampled or not, partition it.
  for sample? in [none, some 20] do
    let whole := FrenCli.Mutate.select all none #[] sample? 7 |>.map (·.id)
    for n in [1:5] do
      let shards := (List.range n).map fun k => FrenCli.Mutate.select all none #[] sample? 7 (shard? := some (k, n)) |>.map (·.id)
      let union : Std.HashSet String := .ofList (shards.flatMap (·.toList))
      unless (shards.map (·.size)).sum == whole.size && whole.all union.contains do
        failures := failures.push s!"mutants of {files.map (·.1)}: the {n} shards of a selection do not partition it"
  return failures

/-! ## Mutation testing, end to end

The properties of what `fren mutate` decides about each mutant
(`Reqs/dev/Testing`), over the examples in `test/mutate/`: specs whose
expectations and cover goals pin them down, each with the mutants that no
check can kill listed beside it, in `X.equivalent`. -/

/-- The mutants of an example are run in this many shards too. -/
def decisionShards : Nat := 3

/-- At most this many mutants of an example are checked again, with every
component, and under `fren check`. -/
def decisionSample : Nat := 24

/-- The mutants of `path` that no check can kill, listed in
`path.equivalent` by identifier, and the problems of that file. Each line
is `ID REASON`, where the reason says why the mutant means what the spec
means, and a line that starts with `--` is a comment. -/
def listedEquivalents (path : FilePath) : IO (Array String × Array String) := do
  let file := path.withExtension "equivalent"
  unless ← file.pathExists do return (#[], #[])
  let mut problems := #[]
  let mut listed := #[]
  for line in (← IO.FS.readFile file).splitOn "\n" do
    if line.isEmpty || line.startsWith "--" then continue
    match line.splitOn " " with
    | id :: reason@(_ :: _) =>
      if reason.all (·.isEmpty) then problems := problems.push s!"{file}: `{id}` has no reason"
      else if listed.contains id then problems := problems.push s!"{file}: `{id}` is listed twice"
      else listed := listed.push id
    | _ => problems := problems.push s!"{file}: `{line}` is not `ID REASON`"
  return (problems, listed)

/-- How a test names an outcome. -/
def outcomeName : FrenCli.Mutate.Outcome → String
  | .killed => "is killed"
  | .survived => "survives"
  | .equivalent => "is equivalent"
  | .unviable => "is unviable"

/-- The decisions of `fren mutate` about the mutants of `files`, or of
those named by `ids`, or `sample?` of them, or the shard `shard?`, in
order; checking every component of every mutant if `exhaustive`. -/
def decisionsOf (files : Array String) (ids : Array String := #[]) (sample? : Option Nat := none)
    (shard? : Option (Nat × Nat) := none) (exhaustive := false) : IO (Array FrenCli.Decision) := do
  let decisions ← IO.mkRef #[]
  let _ ← IO.FS.withIsolatedStreams
    (FrenCli.mutate { command := .mutate, files, mutantIds := ids, sample?, shard? } (some { exhaustive, decisions }))
  decisions.get

/-- The results of `fren check` of `files`, by the key of their item and
their own (`FrenCli.Mutate.keyed`), and its exit code. -/
def checkResultsOf (files : Array String) :
    IO (Std.HashMap String (Array (String × Fren.Core.CheckResult)) × UInt32) := do
  let record ← IO.mkRef #[]
  let (_, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files } (some record))
  let byItem := (← record.get).foldl (init := ({} : Std.HashMap String (Array Fren.Core.CheckResult)))
    fun m (k, r) => m.insert k ((m.getD k #[]).push r)
  return (byItem.map fun _ rs => FrenCli.Mutate.keyed rs, code)

/-- The checks that pass in `before` and fail in `after`, as `item|check`. -/
def passToFail (before after : Std.HashMap String (Array (String × Fren.Core.CheckResult))) : Array String :=
  after.toArray.flatMap fun (item, rs) =>
    (FrenCli.Mutate.killers (before.getD item #[]) rs).map fun (k, _) => s!"{item}|{k}"

/-- The expectations and cover goals of the text `chars`, local and
global, each with its name and the lines that it takes. -/
def expectationsOf (chars : Array Char) : Array (String × FrenCli.Span) :=
  let lines (sp : FrenCli.Span) : FrenCli.Span :=
    let start := (List.range sp.start).reverse.find? (chars[·]? == some '\n') |>.map (· + 1) |>.getD 0
    let stop := ((List.range chars.size).drop sp.stop).find? (chars[·]? == some '\n') |>.map (· + 1) |>.getD chars.size
    { start, stop }
  match FrenCli.parseText chars with
  | .ok (_, items, _) => items.flatMap fun
    | .comp _ c _ members _ spans _ | .globalBlock c _ members _ spans _ => (members.zip spans).filterMap fun
      | (.prop k n _, sp) => if k == .expect || k == .cover then some (s!"{c.name}::{n.name}", lines sp) else none
      | _ => none
    | .global n _ body => #[(n.name, lines { start := n.span.start, stop := body.span.stop })]
    | _ => #[]
  | .error _ => #[]

/-- `chars` written to a file named `name` in a new temporary directory,
for `f`. -/
def withText (name : String) (chars : Array Char) (f : String → IO α) : IO α :=
  IO.FS.withTempDir fun dir => do
    let path := dir / name
    IO.FS.writeFile path (String.ofList chars.toList)
    f path.toString

/-- What `fren mutate` decides about the mutants of the example `path`:
- **adequate:** the example passes `fren check`, and every mutant is killed
  but those listed as equivalent, each of which survives or is shown
  equivalent;
- **sample and shard invariant:** a sample of half of the mutants, each run
  after fewer others, decides each as the whole run does, and so does each
  of `decisionShards` shards, which together hold each mutant once;
- **every expectation needed:** without any one of its expectations and
  cover goals, some mutant survives that was killed, and is not shown
  equivalent, which it cannot be: it was killed, so it means something
  else than the spec;
- **selection sound:** checking only the components whose fingerprint a
  mutant changes decides as checking every component does, and finds
  only checks that checking every component finds;
- **verdicts sound:** each check that kills a mutant, of every component,
  passes under `fren check` of the spec, and fails under `fren check` of
  the mutant's text; a mutant that is not killed fails no check there that
  passes on the spec.

The last two are checked on a sample of `decisionSample` mutants. -/
def decisions (path : String) : IO (Array String) := do
  let name := (FilePath.mk path).fileName.getD path
  let (problems, listed) ← listedEquivalents path
  let mut failures := problems
  let files ← readGroup #[path]
  let chars := files[0]!.2
  let (_, all) := FrenCli.mutantsOf files #[]
  let (before, code) ← checkResultsOf #[path]
  if code != 0 then failures := failures.push s!"{path}: `fren check` exits with {code}, not 0"
  -- Adequacy.
  let decided ← decisionsOf #[path]
  -- Whether the solver shows a listed mutant equivalent within its time
  -- limit, which is in wall-clock time, can depend on the machine's load,
  -- so a listed mutant may either survive or be equivalent.
  for d in decided do
    match d.outcome, listed.contains d.id with
    | .killed, true => failures := failures.push s!"{path}: {d.id} is listed as equivalent, but is killed"
    | .killed, false | .equivalent, true | .survived, true => pure ()
    | o, false => failures := failures.push s!"{path}: {d.id} {outcomeName o}, and is not listed as equivalent"
    | .unviable, true => failures := failures.push s!"{path}: {d.id} is unviable"
  for id in listed do
    unless decided.any (·.id == id) do failures := failures.push s!"{path}: {id} is listed, but is no mutant"
  -- Whether a mutant that is not killed is shown equivalent depends on
  -- the solver's time limit, as above.
  let kind (o : FrenCli.Mutate.Outcome) := if o == .equivalent then .survived else o
  -- A sample, in which each mutant runs after fewer others, with fewer
  -- answers kept (`Reqs/Cli#solver-queries`), decides each as the whole
  -- run does.
  for d in ← decisionsOf #[path] (sample? := some (all.size / 2)) do
    let some d₀ := decided.find? (·.id == d.id) | continue
    if kind d.outcome != kind d₀.outcome || d.killers != d₀.killers then
      failures := failures.push s!"{path}: {d.id} {outcomeName d₀.outcome}, killed by {d₀.killers.toList}, but in a sample \
        {outcomeName d.outcome}, killed by {d.killers.toList}"
  -- So do the shards, which together hold each mutant once.
  let shards ← (List.range decisionShards).toArray.flatMapM fun k => decisionsOf #[path] (shard? := some (k, decisionShards))
  if (shards.map (·.id)).qsort (· < ·) != (decided.map (·.id)).qsort (· < ·) then
    failures := failures.push s!"{path}: the {decisionShards} shards do not hold each mutant once"
  for d in shards do
    let some d₀ := decided.find? (·.id == d.id) | continue
    if kind d.outcome != kind d₀.outcome || d.killers != d₀.killers then
      failures := failures.push s!"{path}: {d.id} {outcomeName d₀.outcome}, killed by {d₀.killers.toList}, but in its shard \
        {outcomeName d.outcome}, killed by {d.killers.toList}"
  -- Every expectation and cover goal is needed.
  let killed := decided.map (·.outcome == .killed)
  for (what, sp) in expectationsOf chars do
    let chars' := chars.extract 0 sp.start ++ chars.extract sp.stop chars.size
    let failure? ← withText name chars' fun path' => do
      let (_, all') := FrenCli.mutantsOf (← readGroup #[path']) #[]
      -- The same mutants, in order, but for their identifiers, which
      -- read the file's path.
      if all'.size != all.size || (all.zip all').any fun (m, m') => m.item != m'.item || m.change != m'.change then
        return some s!"{path}: without `{what}`, the mutants are not the same"
      let decided' ← decisionsOf #[path']
      -- A mutant that the deleted check killed now means something else
      -- than the spec, so it survives: it is not shown equivalent.
      let outcomes := (killed.zip (decided'.map (·.outcome))).filter (·.1) |>.map (·.2)
      if outcomes.contains .survived then return none
      if outcomes.contains .equivalent then
        return some s!"{path}: without `{what}`, a mutant that was killed is shown equivalent to the spec"
      return some s!"{path}: without `{what}`, every mutant that was killed still is"
    failures := failures ++ failure?.toArray
  -- Selection and verdicts, on a sample.
  let sample := FrenCli.Mutate.select all none #[] (some decisionSample) 0
  let full ← decisionsOf #[path] (sample.map (·.id)) (exhaustive := true)
  for m in sample do
    let some d := full.find? (·.id == m.id) | failures := failures.push s!"{path}: {m.id} is not decided"
    let some d₀ := decided.find? (·.id == m.id) | continue
    if kind d.outcome != kind d₀.outcome then
      failures := failures.push
        s!"{path}: {m.id} {outcomeName d₀.outcome}, but {outcomeName d.outcome} when every component is checked"
    for (item, k) in d₀.killers do
      unless d.killers.contains (item, k) do
        failures := failures.push s!"{path}: {m.id} is killed by {item}|{k}, which checking every component does not find"
    let (after, _) ← withText name (m.apply chars) (checkResultsOf #[·])
    let found := passToFail before after
    for (item, k) in d.killers do
      unless found.contains s!"{item}|{k}" do
        failures := failures.push s!"{path}: {m.id} is killed by {item}|{k}, which `fren check` does not fail on it"
    if d.outcome != .killed && !found.isEmpty then
      failures := failures.push s!"{path}: {m.id} {outcomeName d.outcome}, but `fren check` fails it on {found.toList}"
  return failures

/-- `fren mutate` elaborates a file again when a mutant of an earlier file
changes a type alias or a pattern type that it uses (`FrenCli.skipFile?`):
the mutant's state is then that of elaborating every file again, and
differs from the original's. -/
def laterFiles : IO (Array String) := do
  let a := "pub mod a\n\npub type Byte = n: Int where range: n is 0..=255\npub enum Level { Low, Mid, High }\n" ++
    "pub type Loud = level: Level where chosen: level is Level::Mid | Level::High\n"
  let b := "pub mod b\n\nuse a::{Byte, Level, Loud}\n\nproc c(x: Byte, l: Loud): (y: Int) {\n" ++
    "    ensure r: y = (if l = Level::High then x else x + 1)\n}\n"
  let files := #[("a.fren", a.toList.toArray), ("b.fren", b.toList.toArray)]
  let (states, _) := FrenCli.mutantsOf files #[]
  let parsed := files.map (FrenCli.parseText ·.2)
  let names := parsed.map FrenCli.writtenNames
  let mut failures := #[]
  if states.any (·.diags.any (·.severity == .error)) then
    failures := failures.push "the files of `laterFiles` have a static error"
  -- Mutants that `fren mutate` does not make, but that change only what the
  -- later file sees through `Byte` and `Loud`.
  for (item, before, after) in [(`a.Byte, "255", "25"), (`a.Loud, "Level::Mid | ", "")] do
    let start := ((a.splitOn before)[0]!).length
    let m : FrenCli.Mutate.Mutant :=
      { origin := .shiftInteger, file := 0, item, comp? := none, span := ⟨start, start + before.length⟩, before, after }
    let chars' := m.apply files[0]!.2
    let parsed' := FrenCli.parseText chars'
    let all := FrenCli.elabParsed (FrenCli.elabParsed (states[0]?.getD {}) 0 chars' parsed') 1 files[1]!.2 parsed[1]!
    unless sameForMutate (FrenCli.mutantState files parsed names states m chars' parsed') all do
      failures := failures.push s!"`{before}` to `{after}` in `{item}`: `mutantState` differs from elaborating `b.fren` again"
    if sameForMutate all (states[2]?.getD {}) then
      failures := failures.push s!"`{before}` to `{after}` in `{item}`: changes nothing that `b.fren` sees"
  return failures

/-! ## Backjumping -/

open FrenCli.Eval in
/-- Whether the search with backjumping finds what backtracking over the
same candidates finds, in no more steps, and draws the same random numbers
(`Reqs/Eval#backjumping`), for every component of the spec in `paths`, or
of each ui test (`uiFiles`) on its own if `paths` is empty. Its problems are
those of a test's searches: a behaviour that meets the component, and one
in which an expectation is false, each under two random interpretations.
Returns the failures and the number of problems. -/
def backjumpingOf (paths : Array String) : IO (Array String × Nat) := do
  -- fren-covers: eval::backjumping
  let files ← readGroup paths
  -- Only a spec without static errors is tested, as `fren quickcheck` does.
  let st := files.zipIdx.foldl (init := FrenCli.initialState #[]) fun st ((_, chars), i) =>
    FrenCli.elabParsed st i chars (FrenCli.parseText chars)
  if st.diags.any (·.severity == .error) then return (#[], 0)
  let .ok sp := FrenCli.specOf files | return (#[], 0)
  let mut failures := #[]
  let mut problems := 0
  for c in sp.comps do
    let all := sp.meaning c
    let expects := c.constraints.filter (·.kind == .expect)
    let lits := all ++ atomsOf .anonymous expects
    let ints := intsOf lits
    let strs := (stringsOf lits).run' ⟨hash c.path⟩
    let sp := sp.withMatchMemo lits strs
    let goals := #[all] ++ expects.map fun e => all.push { label := e.name, pfx := .anonymous, e := .not e.e }
    for atoms in goals, t in [0:goals.size] do
      for k in [0:2] do
        let (w, g) := (World.random sp).run ⟨mix (hash c.path) (2 * t + k).toUInt64⟩
        let I := w.interp sp
        let p : Problem := { vars := sp.order c, atoms, ints, strs }
        let ((bt, n), g₁) := (p.search sp w I {} (backjump := false)).run g
        let ((bj, m), g₂) := (p.search sp w I {} (backjump := true)).run g
        problems := problems + 1
        let shown (r : Option Env) := r.map fun env => p.vars.map fun (x, _) => env[x]?
        let name := s!"{c.path} ({t}, {k})"
        if g₁.s != g₂.s then failures := failures.push s!"{name}: backjumping draws other random numbers"
        if m > n then failures := failures.push s!"{name}: backjumping takes {m} steps, backtracking {n}"
        if bt.isSome && shown bj != shown bt then
          failures := failures.push s!"{name}: backjumping finds other values than backtracking"
        if bt.isNone && n < 4000 && bj.isSome then
          failures := failures.push s!"{name}: backjumping finds values where backtracking tries every candidate"
  return (failures, problems)

/-- `backjumpingOf` Fren's own requirements, or each ui test. -/
def backjumping (corpus : String) : IO (Array String) := do
  let groups : Array (Array String) ← if corpus == "reqs" then pure #[ownSpecFiles] else
    do pure ((← uiFiles).map fun f => #[f.toString])
  let mut failures := #[]
  let mut problems := 0
  for g in groups do
    let (fs, n) ← backjumpingOf g
    failures := failures ++ fs
    problems := problems + n
  return if problems < 100 then failures.push s!"backjumping: only {problems} problems in `{corpus}`" else failures

/-! ## Enumeration agrees with the solver -/

/-- `src` with every check set to enumeration that no setting of its own
sets otherwise (`Reqs/Check#checking-by-enumeration`). -/
def enumeratedText (src : String) : String := "set_option fren.evidence \"enumerated\"\n" ++ src

/-- The ui tests whose checks enumeration is compared with the solver's:
those that the binary checks, without a static error. -/
def enumerationCorpus : IO (Array FilePath) := do
  (← uiFiles).filterM fun f => do
    let src ← IO.FS.readFile f
    return !(src.splitOn "--@ only: hosted").length > 1 && (src.splitOn "--@ exit: 2").length == 1

/-- Each verdict of enumeration on the ui tests matches the solver's on the
same check (`Reqs/Check#verdicts-of-enumeration`): a failure is genuine, so
the solver must not pass the check, and a pass that is not bounded is a
decision, so the solver must not fail it; and the obligations of pattern
types, which stay the solver's, keep their results. -/
def enumerationAgrees : IO (Array String) := do
  let mut failures := #[]
  let mut compared := 0
  for f in ← enumerationCorpus do
    let src ← IO.FS.readFile f
    let (solver, code) ← checkResultsOf #[f.toString]
    if code == 2 then continue
    let (enumerated, _) ← withText (f.fileName.getD "spec.fren") (enumeratedText src).toList.toArray fun p =>
      checkResultsOf #[p]
    for (item, rs) in enumerated do
      let ss := solver.getD item #[]
      for (k, r) in rs do
        let some (_, s) := ss.find? (·.1 == k) | continue
        compared := compared + 1
        let bad := match r.verdict, s.verdict with
          | .fail, .pass => true
          | .pass, .fail => r.bounded?.isNone
          | _, _ => false
        if bad then
          let bounded := if r.bounded?.isSome then " up to the bound" else ""
          failures := failures.push s!"{f}: `{item}` {k}: enumeration {repr r.verdict}{bounded}, but the solver {repr s.verdict}"
    -- A value given where a pattern type is declared stays the solver's
    -- (`check::by_evidence`): its result is not dropped.
    for (item, ss) in solver do
      for (k, s) in ss do
        unless s.kind == .definedness && s.patTy?.isSome do continue
        let same := ((enumerated.getD item #[]).find? (·.1 == k)).any (·.2.verdict == s.verdict)
        unless same do failures := failures.push s!"{f}: `{item}` {k}: the solver's obligation is missing with enumeration"
  return if compared < 500 then failures.push s!"enumeration: only {compared} checks compared" else failures

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

/-! ## The queries of both front ends -/

/-- The specs whose datatypes both front ends must declare alike, by the
same symbols (`Reqs/Lang/Prelude#meaning`). -/
def smtAgreementSpecs : List String := ["test/cli/args/dump_smt_prelude.fren"]

/-- The `declare-datatypes` commands of `text`, each once, in order. -/
def datatypeDecls (text : String) : Array String :=
  ((text.splitOn "\n").map (·.trimAscii.toString)).filter (·.startsWith "(declare-datatypes") |>.toArray
    |>.foldl (init := #[]) fun acc d => if acc.contains d then acc else acc.push d

/-- The terms of `text` that start with `pre`, each whole, to its closing
parenthesis, each once. -/
def termsFrom (pre : String) (text : String) : Array String := Id.run do
  let cs := text.toList.toArray
  let p := pre.toList.toArray
  let mut out := #[]
  for i in [0:cs.size] do
    if cs.extract i (i + p.size) == p then
      let mut depth := 0
      let mut j := i
      while j < cs.size do
        if cs[j]! == '(' then depth := depth + 1
        if cs[j]! == ')' then
          depth := depth - 1
          if depth == 0 then break
        j := j + 1
      let t := String.ofList (cs.extract i (j + 1)).toList
      unless out.contains t do out := out.push t
  return out

/-- What both front ends' queries must say alike of the prelude's types,
in `text`: the datatypes' declarations, as written; and, without `|`s,
which the binary writes around every other symbol and lean-smt around
none it need not, the constants of their sorts, their qualified
constructors and their selectors' applications. -/
def preludeQueryParts (text : String) : Array String :=
  let lean (d : String) := d.startsWith "(declare-datatypes ((Option " || d.startsWith "(declare-datatypes ((Except "
  let plain := text.replace "|" ""
  let consts := ((plain.splitOn "\n").map (·.trimAscii.toString)).filter (fun l =>
    l.startsWith "(declare-const " && (l.contains "(Option " || l.contains "(Except ")) |>.toArray
  (datatypeDecls text).filter lean ++ consts.foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]
    ++ termsFrom "(as Option." plain ++ termsFrom "(as Except." plain
    ++ termsFrom "(Option.some.val " plain ++ termsFrom "(Except.ok.field1 " plain ++ termsFrom "(Except.error.field1 " plain

/-- That the `fren` command's queries (`--dump-smt`) say of the prelude's
types exactly what the Lean-hosted front end's do, which lean-smt writes
(`preludeQueryParts`): the same datatypes, constructors, selectors and
parameters, and the same constants of their sorts (`lang::prelude_smt`). -/
def smtAgreement (env : Environment) : IO (Array String) := do
  let mut failures := #[]
  for path in smtAgreementSpecs do
    let src ← IO.FS.readFile path
    let (out, _) ← runFren ["check", "--dump-smt", path]
    let input := "open Fren.Lang\nset_option trace.smt true\n" ++ src ++ "\n#fren_check\n"
    let (_, log) ← Elab.process input env {} path
    let hosted := preludeQueryParts ("\n".intercalate (← log.toList.mapM fun m => m.data.toString))
    let cli := preludeQueryParts out
    unless cli.any (·.startsWith "(declare-datatypes") do
      failures := failures.push s!"{path}: the binary declares none of the prelude's datatypes"
    for d in cli do
      unless hosted.contains d do failures := failures.push s!"{path}: only the binary's queries have {d}"
    for d in hosted do
      unless cli.contains d do failures := failures.push s!"{path}: only Lean's queries have {d}"
  return failures

/-- The jobs, as the arguments of `--job`, the slowest first. -/
def jobs : IO (Array (List String)) := do
  let ui ← uiFiles
  let n := (ui.size + uiBatch - 1) / uiBatch
  -- Every `n`th file, so that the slow ones spread over the batches.
  let batches := (List.range n).toArray.map fun k =>
    "ui" :: ((List.range ui.size).filter (· % n == k)).map (ui[·]!.toString)
  return #[["ownSpec"]] ++ (List.range mutationSlices).toArray.map (["mutation", "0", toString ·, toString mutationSlices])
    ++ batches ++ (corpora.map (["conformance", ·.1])).toArray
    ++ #[["snapshots"], ["formatting"], ["errorCodes"], ["printing"], ["fixing"], ["libraries"], ["leanTokens"], ["laterFiles"], ["backjumping", "reqs"], ["backjumping", "ui"],
      ["enumeration"], ["smtAgreement"]]
    ++ ((List.range (← mutationCorpus).size).drop 1).toArray.map (["mutation", toString ·, "0", "1"])
    ++ (← decisionExamples).map (["decisions", ·.toString])

/-- Runs a job in this process. -/
unsafe def runJob (bless : Bool) : List String → IO (Array String)
  | "ui" :: files => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Fren }] {} (loadExts := true)
    uiTests env (files.toArray.map FilePath.mk)
  | ["leanTokens"] => leanTokens
  | ["snapshots"] => snapshots bless
  | ["errorCodes"] => errorCodes
  -- fren-covers: lint::printing, lint::parenthesization
  | ["printing"] => pure (FrenTest.Quote.roundTrips 5000)
  | ["ownSpec"] => ownSpec
  | ["conformance", name] => match corpora.lookup name with
    | some corpus => conformance name corpus
    | none => throw (IO.userError s!"unknown corpus `{name}`")
  | ["formatting"] => formatting
  | ["fixing"] => fixing
  | ["libraries"] => libraries
  | ["backjumping", corpus] => backjumping corpus
  | ["decisions", path] => decisions path
  | ["laterFiles"] => laterFiles
  | ["enumeration"] => enumerationAgrees
  | ["smtAgreement"] => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    smtAgreement (← importModules #[{ module := `Fren }] {} (loadExts := true))
  | ["mutation", group, slice, slices] => do
    -- A slice out of range would check nothing, and pass.
    match (group.toNat?.bind ((← mutationCorpus)[·]?)), slice.toNat?, slices.toNat? with
    | some paths, some k, some n => if k < n then return ← mutation paths k n
    | _, _, _ => pure ()
    throw (IO.userError s!"unknown mutation job `{group} {slice} {slices}`")
  | job => throw (IO.userError s!"unknown job `{" ".intercalate job}`")

/-- The name of `job` in its failures: its arguments, and for a mutation
job, the files of its group. -/
def jobName (job : List String) : IO String := do
  let name := " ".intercalate job
  if let ["mutation", group, _, _] := job then
    if let some g := group.toNat? then
      if let some paths := (← mutationCorpus)[g]? then
        return if g == 0 then s!"{name} (Fren's own requirements)" else s!"{name} ({", ".intercalate paths.toList})"
  return name

/-- Runs `job` in a process of its own, returning its failures. -/
def spawnJob (bless : Bool) (job : List String) : IO (Array String) := do
  let args := #["--job"] ++ job.toArray ++ (if bless then #["--bless"] else #[])
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args }
  let last := ((out.stdout.splitOn "\n").filter (!·.isEmpty)).getLast?.getD ""
  let name ← jobName job
  match Json.parse last >>= fromJson? with
  | .ok failures =>
    if out.exitCode == 0 then
      -- Such as a `panic!`, which prints and carries on.
      if out.stderr.isEmpty then return failures
      return failures.push s!"the job `{name}` wrote to stderr:\n{out.stderr}"
  | .error _ => pure ()
  return #[s!"the job `{name}` crashed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"]

/-- At most this many jobs run at once, unless `FREN_TEST_JOBS` says
otherwise. This is a heuristic, not a bound on memory: the solver's time
limit is in wall-clock time, so too many jobs at once could make checks
inconclusive, and a job can take about 2.5 GB of memory, so sixteen can
take 40 GB. A machine with less sets `FREN_TEST_JOBS` lower. -/
def maxJobs : Nat := 16

/-- How many jobs run at once: `FREN_TEST_JOBS`, or as many as the machine
has cores, up to `maxJobs`. A `FREN_TEST_JOBS` that is not a positive
integer, including an empty one and `0`, is an error. -/
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
