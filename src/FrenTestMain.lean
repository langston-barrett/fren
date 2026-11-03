-- keep-sorted start
import Fren
import FrenCli.Eval
import FrenCli.Run
import FrenTest.Frontends
import FrenTest.FuzzFrontends
import FrenTest.Jobs
import FrenTest.Messages
import FrenTest.OutOfFuel
import FrenTest.Quote
import FrenTest.SmallValues
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
  formatted, keeps its tokens and comments in order and its imports when
  formatted, with no comma after a line break or a line comment,
  formatting it again changes nothing, and it formats as it does when it
  is laid out again at random (`fmt::safe`, `fmt::layout_free`); `fren fmt`
  rewrites a file in place.
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
- **Front-end corpus:** the front-end fuzzer's specs of fixed seeds are
  checked by both front ends, whose differences must be those that
  `FrenTest.FuzzFrontends.knownDifferences` lists (`frontendFuzz`).

The tests run as jobs, in parallel (see "Jobs" below), and the failures are
reported sorted.
-/

-- fren-covers: cli::agreement, fmt::safe

open System Lean FrenTest.Ui FrenTest.Jobs

/-- The files under `dir`, in its subdirectories too, with extension `ext`. -/
def sortedFiles (dir : FilePath) (ext : String) : IO (Array FilePath) := do
  let fs ← dir.walkDir
  return (fs.filter (·.extension == some ext)) |>.qsort (·.toString < ·.toString)

/-- The ui tests that run with the readers of solver models misreading
them, to see that confirmation catches it (`Reqs/Models#testing`). -/
def misreadDir : FilePath := "test" / "ui" / "misread"

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

/-- `out` with each time of `fren check --timings` (`Reqs/Cli#timings`)
written as `_`, so that a snapshot that shows them does not depend on how
fast the machine is: every run of digits and dots on a line that starts
with `timing: `. -/
def timingsShown (out : String) : String :=
  "\n".intercalate <| (out.splitOn "\n").map fun line =>
    if !line.startsWith "timing: " then line else Id.run do
      let mut acc := ""
      let mut inNumber := false
      for ch in line.toList do
        if ch.isDigit || (inNumber && ch == '.') then
          unless inNumber do acc := acc.push '_'
          inNumber := true
        else
          acc := acc.push ch
          inNumber := false
      return acc

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
    expectFile bless (f.withExtension "expected") s!"{timingsShown (lintsShown out)}exit={code}\n"

/-! ## ui tests -/

/-- The lines of ui tests where the front ends are known to report a
message alike but at different columns, until each is fixed (#555): Lean
at a method's or field's receiver, the binary at its name; the binary at
`refines`, Lean at the call that it refines; Lean at a pattern's `r"`,
the binary at its text; and Lean at a higher-order call, the binary at
its argument. A line here that no longer differs fails, so that it is
removed. -/
def knownColumnDifferences : List (String × Nat) :=
  [("test/ui/checks/refinement_bindings_static.fren", 19), ("test/ui/checks/refinement_bindings_static.fren", 29),
   ("test/ui/checks/refinement_bindings_static.fren", 39), ("test/ui/checks/refinement_bindings_static.fren", 44),
   ("test/ui/lang/constants_methods_static.fren", 5), ("test/ui/lang/constants_static.fren", 20),
   ("test/ui/lang/datatypes_static.fren", 32), ("test/ui/lang/datatypes_static.fren", 33),
   ("test/ui/lang/div_mod_static.fren", 32), ("test/ui/lang/div_mod_static.fren", 36),
   ("test/ui/lang/higher_order_static.fren", 59), ("test/ui/lang/nat_static.fren", 39),
   ("test/ui/lang/newtypes_static.fren", 53), ("test/ui/lang/newtypes_static.fren", 56),
   ("test/ui/lang/ordered_enums_static.fren", 23), ("test/ui/lang/ordered_enums_static.fren", 25),
   ("test/ui/lang/ordered_enums_static.fren", 33), ("test/ui/lang/ordered_enums_static.fren", 35),
   ("test/ui/lang/ordered_structs_static.fren", 35), ("test/ui/lang/ordered_structs_static.fren", 37),
   ("test/ui/lang/ordered_structs_static.fren", 42), ("test/ui/lang/patterns_static.fren", 6),
   ("test/ui/lang/patterns_static.fren", 8), ("test/ui/lang/patterns_static.fren", 10),
   ("test/ui/lang/patterns_static.fren", 12), ("test/ui/lang/patterns_static.fren", 14),
   ("test/ui/lang/relations_static.fren", 9), ("test/ui/lang/relations_static.fren", 27),
   ("test/ui/lang/sequences_static.fren", 10), ("test/ui/lang/strings_static.fren", 4),
   ("test/ui/lang/strings_static.fren", 8)]

/-- A path as `knownColumnDifferences` writes it: without a leading `./`. -/
partial def withoutDotSlash (p : String) : String :=
  match p.dropPrefix? "./" with
  | some rest => withoutDotSlash rest.toString
  | none => p

#guard withoutDotSlash "./test/ui/a.fren" == "test/ui/a.fren"
#guard withoutDotSlash "test/ui/a.fren" == "test/ui/a.fren"

/-- The ui tests of `files`. -/
def uiTests (env : Environment) (files : Array FilePath) : IO (Array String) := do
  let mut failures := #[]
  let isStopped (d : Diagnostic) := d.line == 0 && d.text == Fren.Core.couldNotHeadline
  for f in files do
    let mut cliStopped := none
    let mut cliDiags : Array Diagnostic := #[]
    let src ← IO.FS.readFile f
    let spec ← match parse src with
      | .ok s => pure s
      | .error e => failures := failures.push s!"{f}: {e}"; continue
    if spec.only? != some "hosted" then
      let (out, code) ← runCheck #[f.toString]
      let (diags, summary) := cliDiagnostics f.toString out
      cliDiags := diags
      for e in check "cli" spec diags summary (some code.toNat) do
        failures := failures.push s!"{f} (binary): {e}"
      cliStopped := some (out.contains s!"error: {Fren.Core.couldNotHeadline}")
    if spec.only? != some "cli" then
      -- Each type that the hosted front end takes from its cache checked
      -- against the term's elaborated again (`Fren.typeOf`).
      let (diags, summary) ← hostedDiagnostics env f.toString src (Fren.fren.checkTypeCache.set {} true)
      let stopped := diags.any isStopped
      for e in check "hosted" spec (diags.filter (!isStopped ·)) summary none do
        failures := failures.push s!"{f} (Lean): {e}"
      -- A message that both front ends report on a line, alike, is at
      -- the same column in both (`cli::agreement`), but on the lines
      -- known to differ, which must still differ.
      let known := knownColumnDifferences.filterMap fun (g, l) => if g == withoutDotSlash f.toString then some l else none
      let mut differing := #[]
      for h in diags do
        let alike := cliDiags.filter fun c => c.line == h.line && c.line != 0 && c.severity == h.severity
          && FrenTest.Frontends.normHead c.text == FrenTest.Frontends.normHead h.text
        unless alike.isEmpty || alike.any (·.col == h.col) do
          differing := differing.push h.line
          unless known.contains h.line do
            failures := failures.push
              s!"{f}:{h.line}: Lean reports `{FrenTest.Frontends.headOf h}` at column {h.col + 1}, the binary at {(alike.map (·.col + 1)).toList}"
      if spec.only?.isNone then
        for l in known do
          unless differing.contains l do
            failures := failures.push s!"{f}:{l}: the front ends' columns no longer differ; remove it from `knownColumnDifferences`"
      -- Both front ends say that a static error stopped the checks, or
      -- neither does (`cli::agreement`).
      if let some c := cliStopped then
        if c != stopped then
          failures := failures.push
            s!"{f}: {if c then "only the binary" else "only Lean"} says `{Fren.Core.couldNotHeadline}`"
  return failures

/-! ## The reference's examples and rule identifiers -/

/-- The ```` ```fren example ```` blocks of a Markdown text, each with the
line of its opening fence (`Reqs/dev/Style#examples`). -/
def exampleBlocks (md : String) : Array (Nat × String) :=
  (Fren.Core.fencedBlocks md).filterMap fun b =>
    if b.info == Fren.Core.frenExampleInfo then some (b.line, "\n".intercalate b.body.toList ++ "\n") else none

#guard exampleBlocks "a\n```fren example\nx\n```\n```fren\ny\n```\n" == #[(2, "x\n")]
#guard exampleBlocks "````text\n```fren example\nx\n```\n````\n" == #[]
#guard exampleBlocks "```` ```fren example ```` inline\n```fren example\nx\n```\n" == #[(2, "x\n")]

/-- The Markdown files of the reference, `src/Reqs/**/*.md`. -/
def manualFiles : IO (Array FilePath) := sortedFiles ("src" / "Reqs") "md"

/-- Each ```` ```fren example ```` block of the reference, as a spec of its
own, passes as a ui test through both front ends
(`Reqs/dev/Style#examples`). Its failures name the Markdown file and the
line of the block's fence; the lines within them are the block's, from 1. -/
def manualExamples (env : Environment) : IO (Array String) := do
  let dir : FilePath := ".lake" / "manual-examples"
  IO.FS.createDirAll dir
  let mut files := #[]
  let mut origins := #[]
  let mut failures := #[]
  for md in ← manualFiles do
    for (line, src) in exampleBlocks (← IO.FS.readFile md) do
      let origin := s!"{md}, the example at line {line}"
      -- Every example runs through both front ends.
      if (parse src).toOption.any (·.only?.isSome) then
        failures := failures.push s!"{origin}: an example runs through both front ends, so it has no `--@ only`"
        continue
      let f := dir / s!"{md.toString.replace "/" "_"}_{line}.fren"
      IO.FS.writeFile f src
      files := files.push f
      origins := origins.push origin
  -- A reader that finds no example would make this job check nothing.
  if files.isEmpty && failures.isEmpty then
    return #["src/Reqs: no ```` ```fren example ```` block found, so the examples' reader is broken"]
  let ui ← uiTests env files
  return failures ++ ui.map fun msg => (files.zip origins).foldl (fun m (f, o) => m.replace f.toString o) msg

/-- A fence problem of a Markdown spec is a static error that stops the
checks in both front ends alike (`Reqs/Markdown#code-blocks`): the spec's
own `#fren_check` after a block that looks like `fren`, and one after a
Markdown file of prose whose block is never closed, check nothing, though
each has an expectation that fails. -/
def markdownFences (env : Environment) : IO (Array String) := do
  let dir : FilePath := ".lake" / "markdown-fences"
  IO.FS.createDirAll dir
  let after := "pub proc after_prose(a?): (b?) {\n    ensure same: b? iff a?\n\n    expect wrong: b? iff not a?\n}\n"
  let afterFile := dir / "after_prose.fren"
  IO.FS.writeFile afterFile after
  let cases : List (String × String) := [("LiterateNearFren.md", ""), ("LiterateUnclosedProse.md", after)]
  let mut failures := #[]
  for (md, code) in cases do
    let files := #[s!"src/FrenTestFiles/{md}"] ++ (if code.isEmpty then #[] else #[afterFile.toString])
    let (out, _) ← runCheck files
    unless out.contains Fren.Core.couldNotHeadline.toSlice && !out.contains "does not hold".toSlice do
      failures := failures.push s!"{md} (binary): a fence problem does not stop the checks:\n{out}"
    let (diags, summary) ← hostedDiagnostics env "src/FrenTestFiles/MarkdownFences.lean" s!"#fren_md \"{md}\"\n{code}"
    unless diags.any (·.text == Fren.Core.couldNotHeadline) && !diags.any (·.text.contains "does not hold".toSlice)
        && summary.isNone do
      failures := failures.push s!"{md} (Lean): a fence problem does not stop the checks: {diags.map (·.text)}"
  return failures

/-- Whether `id` is a rule identifier: `r[`, segments of lowercase words and
digits joined by `-`, separated by `.`, and `]` (`Reqs/dev/Style#rule-identifiers`). -/
def isRuleId (id : String) : Bool :=
  match (id.dropPrefix? "r[").bind (·.toString.dropSuffix? "]") with
  | none => false
  | some body => (body.toString.splitOn ".").all fun seg =>
      (seg.splitOn "-").all fun w => !w.isEmpty && w.all fun c => c.isLower || c.isDigit

#guard isRuleId "r[quantifier.guard.strict]" && isRuleId "r[quantifier.not-listed]"
#guard !isRuleId "r[Quantifier]" && !isRuleId "r[a..b]" && !isRuleId "r[a-]" && !isRuleId "r[]"

/-- The lines of a Markdown text outside its code blocks, each with its
number, from 1. -/
def proseLines (md : String) : Array (Nat × String) := Id.run do
  let inBlock := (Fren.Core.fencedBlocks md).foldl (init := #[]) fun acc b =>
    acc ++ (List.range (b.body.size + 2)).toArray.map (b.line + ·)
  let mut out := #[]
  for line in md.splitOn "\n", i in [1:md.length + 2] do
    unless inBlock.contains i do out := out.push (i, line)
  return out

/-- The rule identifiers of a Markdown text, outside its code blocks, each
with its line: every line that starts with `r[` once its blanks are
removed, as written, so that `ruleIds` rejects one that mdbook-spec, which
reads only a whole line `r[...]`, would not render. -/
def ruleIdLines (md : String) : Array (Nat × String) :=
  (proseLines md).filter (·.2.trimAscii.toString.startsWith "r[")

#guard ruleIdLines "r[a.b]\nx\n```text\nr[a.b]\n```\n" == #[(1, "r[a.b]")]
#guard ruleIdLines "```` ```text ```` inline\nr[a.b]\n" == #[(2, "r[a.b]")]
#guard ruleIdLines "  r[a.b]\n" == #[(1, "  r[a.b]")]

/-- The rules that a Markdown text cites, outside its code blocks, each with
its line: the code spans that look like a rule identifier of the
constructs `prefixes`, such as `quantifier.guard.strict`. -/
def ruleCitations (prefixes : Array String) (md : String) : Array (Nat × String) :=
  (proseLines md).foldl (init := #[]) fun acc (i, line) =>
    let spans := ((line.splitOn "`").zipIdx.filter (·.2 % 2 == 1)).map (·.1)
    acc ++ (spans.filter fun c => c.contains '.' && isRuleId s!"r[{c}]"
      && prefixes.contains ((c.splitOn ".").head!)).toArray.map (i, ·)

#guard ruleCitations #["a"] "as `a.b` says, not `x.y` or `a`\n" == #[(1, "a.b")]

/-- Every rule identifier of the reference is well formed, on a line of its
own, and unique, and every rule that the reference cites exists
(`Reqs/dev/Style#rule-identifiers`). -/
def ruleIds : IO (Array String) := do
  let mut failures := #[]
  let mut seen : Array (String × String) := #[]
  let texts ← (← manualFiles).mapM fun md => return (md, ← IO.FS.readFile md)
  for (md, text) in texts do
    for (line, id) in ruleIdLines text do
      let here := s!"{md}:{line}"
      unless isRuleId id do
        failures := failures.push s!"{here}: `{id}` is not a rule identifier, alone on its line and not indented: lowercase words and digits, joined by `-`, in segments separated by `.`"
      match seen.find? (·.1 == id) with
      | some (_, first) => failures := failures.push s!"{here}: `{id}` is already the identifier of the rule at {first}"
      | none => seen := seen.push (id, here)
  let ids := seen.map fun (id, _) => ((id.drop 2).dropEnd 1).toString
  let prefixes := (ids.map fun (i : String) => (i.splitOn ".").head!).toList.eraseDups.toArray
  for (md, text) in texts do
    for (line, c) in ruleCitations prefixes text do
      unless ids.contains c do
        failures := failures.push s!"{md}:{line}: `{c}` cites no rule"
  return failures

/-! ## Rules and their requirements -/

/-- A rule of the reference: its identifier, without `r[` and `]`; the line
of the identifier; the label that it is under, such as `Legality rules`, or
`""`; and its text, the rest of its paragraph. -/
structure Rule where
  id : String
  line : Nat
  label : String
  text : String
  deriving Inhabited

/-- The labels whose rules each have a requirement, or are listed in
`unformalizedFile` (`Reqs/dev/Style#rules-and-requirements`). -/
def formalLabels : Array String := #["Legality rules", "Dynamic semantics"]

/-- The rules of a Markdown text, each under the last label before it: a
line that is a bold run-in label (`**Legality rules**`), or a `Syntax`
heading, which is the label `Syntax`. Any other heading ends a label. -/
def rulesOf (md : String) : Array Rule := Id.run do
  let lines := (md.splitOn "\n").toArray
  let mut label := ""
  let mut out := #[]
  for (i, line) in proseLines md do
    let t := line.trimAscii.toString
    if t.startsWith "#" then
      label := if (t.dropWhile (· == '#')).trimAscii.toString == "Syntax" then "Syntax" else ""
    else if t.startsWith "**" && t.endsWith "**" && t.length > 4 then
      label := ((t.drop 2).dropEnd 2).toString
    else if line.startsWith "r[" && isRuleId t then
      let para := (lines.extract i lines.size).toList.takeWhile fun l =>
        !l.trimAscii.isEmpty && !l.startsWith "```"
      out := out.push { id := ((t.drop 2).dropEnd 1).toString, line := i, label, text := " ".intercalate para }
  return out

#guard (rulesOf "## Syntax\n\nr[a.syntax]\nx\n\n## B\n\n**Legality rules**\n\nr[a.b]\nOne `p::q`\ntwo.\n\nr[a.c]\n```fren\n```\n").map
    (fun r => (r.id, r.line, r.label, r.text)) ==
  #[("a.syntax", 3, "Syntax", "x"), ("a.b", 10, "Legality rules", "One `p::q` two."), ("a.c", 14, "Legality rules", "")]

/-- An item of a ```` ```fren ```` block of the reference, a requirement:
its path, such as `lang::guard_bound`; the Markdown file and line where it
is declared; and the names of its clauses: a procedure's or a block
expectation's `ensure`s, `expect`s and `cover`s, and a function's
postconditions. -/
structure ReqItem where
  path : String
  file : String
  line : Nat
  clauses : Array String
  deriving Inhabited

/-- The name of an item, and the names of its clauses. -/
partial def itemDecl : FrenCli.Item → Option (FrenCli.Ident × Array String)
  | .enum _ n .. | .record _ n .. | .newtype _ n .. | .abstractType _ n | .typeAlias _ n _
  | .subsetType _ n .. | .const _ n .. | .global n .. | .trait _ n .. => some (n, #[])
  | .function _ n _ _ _ _ clauses .. => some (n, clauses.filterMap fun (post, c, _) => if post then some c.name else none)
  | .comp _ n _ members .. | .globalBlock n _ members .. =>
    some (n, members.filterMap fun
      | .prop kind c _ => if kind == .assume then none else some c.name
      | _ => none)
  | .lintSetting _ _ _ _ _ (some item) => itemDecl item
  | _ => none

/-- The items of the ```` ```fren ```` blocks of the Markdown file `file`,
whose text is `md`, each in the module that the last `mod` before it
enters. -/
def reqItemsOf (file md : String) : Except String (Array ReqItem) := do
  let chars := (Fren.Core.unwrapMarkdown md).toList.toArray
  let lineOf (p : Nat) := ((chars.extract 0 p).filter (· == '\n')).size + 1
  match FrenCli.parseText chars with
  | .error (span, _) => throw s!"{file}:{lineOf span.start}: its ```` ```fren ```` blocks do not parse"
  | .ok (_, items, _, _) =>
    let mut current := #[]
    let mut out := #[]
    for item in items do
      if let .mod _ path := item then current := path.map (·.name)
      else if let some (n, clauses) := itemDecl item then
        out := out.push { path := "::".intercalate (current.push n.name).toList, file, line := lineOf n.span.start, clauses }
    return out

#guard ((reqItemsOf "f" "```fren\npub mod a::b\n\nproc p(x?): (y?) {\n    assume a: x?\n    ensure c: y? = x?\n    expect d: y?\n}\n```\n").toOption.getD #[]).map
    (fun i => (i.path, i.line, i.clauses)) == #[("a::b::p", 4, #["c", "d"])]

/-- The path of the requirement that is named as the rule `id` is: its
segments joined by `::`, with each `-` an `_`. -/
def reqPathOf (id : String) : String := "::".intercalate ((id.replace "-" "_").splitOn ".")

#guard reqPathOf "quantifier.type.not-listed" == "quantifier::type::not_listed"

/-- Whether `s` is shaped as a segment of a rule identifier is, once each
`-` is an `_`: lowercase words and digits joined by `_`. -/
def ruleShaped (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isLower || c.isDigit || c == '_'

/-- A piece of Markdown prose: text, or a code span's content. -/
inductive Piece where
  | text (s : String)
  | code (s : String)
  deriving BEq, Repr, Inhabited

/-- A text as its pieces, one character of text at a time: a code span
opens with a run of backticks and closes with the next run of as many, and
a run that nothing closes is text. -/
def pieces (s : String) : Array Piece := Id.run do
  let cs := s.toList.toArray
  let runAt (i : Nat) : Nat := ((cs.extract i cs.size).toList.takeWhile (· == '`')).length
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! != '`' then
      out := out.push (.text (String.singleton cs[i]!))
      i := i + 1
      continue
    let n := runAt i
    let mut j := i + n
    let mut close := none
    while j < cs.size && close.isNone do
      if cs[j]! == '`' then
        if runAt j == n then close := some j
        j := j + runAt j
      else
        j := j + 1
    match close with
    | some k =>
      let body := String.ofList (cs.extract (i + n) k).toList
      let body := if body.length ≥ 2 && body.startsWith " " && body.endsWith " " then ((body.drop 1).dropEnd 1).toString else body
      out := out.push (.code body)
      i := k + n
    | none =>
      for c in cs.extract i (i + n) do out := out.push (.text (String.singleton c))
      i := i + n
  return out

/-- The parenthesized groups of `ps`, the pieces of a rule's text, each as
the pieces between its parentheses, the inner ones first. A parenthesis in
a code span does not count. -/
def groupsOf (ps : Array Piece) : Array (Array Piece) := Id.run do
  let mut opens : Array Nat := #[]
  let mut out := #[]
  for h : k in [0:ps.size] do
    match ps[k] with
    | .text "(" => opens := opens.push k
    | .text ")" =>
      if let some o := opens.back? then
        opens := opens.pop
        out := out.push (ps.extract (o + 1) k)
    | _ => pure ()
  return out

/-- An element of a parenthesized group, as a reference to requirements:
an item, by its path (`lang::guard_bound`), or a clause by its item's path
and its name (`lang::lazy_rules::and_true`); clauses of an item (`taken` of
`lang::match_rules`); or clauses alone (`falls_through`), of the last item
that the group names, or else of the last item that the latest marker
before it in the chapter names. -/
inductive Ref where
  | item (path : String)
  | clauses (names : Array String) (path : Option String)
  deriving BEq, Repr, Inhabited

/-- Whether a code span is a path, such as `lang::guard_bound`. -/
def isPath (c : String) : Bool :=
  (c.splitOn "::").length > 1 && (c.splitOn "::").all fun s =>
    !s.isEmpty && s.all fun ch => ch.isAlphanum || ch == '_' || ch == '?'

/-- Whether a code span names a clause, such as `and_true`. -/
def isClauseName (c : String) : Bool :=
  match c.toList with
  | first :: _ => (first.isLower || first == '_') && (c.dropEnd (if c.endsWith "?" then 1 else 0)).all fun ch =>
      ch.isLower || ch.isDigit || ch == '_'
  | [] => false

/-- The element `ps` of a group, which commas and semicolons separate, as a reference:
`none` if it is not one, and `some none` if it is a code span that names no
requirement, such as an error code (`F0356`). -/
def refOf (ps : Array Piece) : Option (Option Ref) := Id.run do
  -- Its words and code spans, without blanks, and without a leading `and`.
  let mut toks : Array Piece := #[]
  let mut word := ""
  for p in ps.push (.text " ") do
    match p with
    | .text t =>
      if t.trimAscii.isEmpty then
        unless word.isEmpty do toks := toks.push (.text word)
        word := ""
      else word := word ++ t
    | .code c =>
      unless word.isEmpty do toks := toks.push (.text word)
      word := ""
      toks := toks.push (.code c)
  if toks[0]? == some (.text "and") then toks := toks.extract 1 toks.size
  match toks.toList with
  | [.code c] =>
    if isPath c then return some (some (.item c))
    if isClauseName c then return some (some (.clauses #[c] none))
    return some none
  | _ =>
    let (names, path) := match toks.toList.reverse with
      | .code p :: .text "of" :: rest => if isPath p then (rest.reverse, some p) else (toks.toList, none)
      | _ => (toks.toList, none)
    -- Clause names, joined by `and`.
    let ok := names.length % 2 == 1 && (names.zipIdx.all fun (p, i) => match p with
      | .code c => i % 2 == 0 && isClauseName c
      | .text t => i % 2 == 1 && (t == "and" || t == "or"))
    if !ok then return none
    return some (some (.clauses (names.filterMap fun | .code c => some c | _ => none).toArray path))

/-- Whether the path `q` is in a module that the reference declares an
item in, such as `lang`, unlike an example such as `Shape::Circle`. -/
def inDeclaredModule (items : Array ReqItem) (q : String) : Bool :=
  items.any fun i => (i.path.splitOn "::").head! == (q.splitOn "::").head!

/-- Whether the reference `ref` is a marker's among `items`: one that names
a path in a module that the reference declares (`inDeclaredModule`), or
clauses alone, in a group that names such a path (`pathGroup`) or that are
clauses of some item. So "(`true` or `false`)" and "(`Shape::Circle`)"
are no reference. -/
def isMarkerRef (items : Array ReqItem) (pathGroup : Bool) : Ref → Bool
  | .item q | .clauses _ (some q) => inDeclaredModule items q
  | .clauses names none => pathGroup || names.all fun c => items.any (·.clauses.contains c)

/-- The references of a parenthesized group, if it is a marker: one with
an element, between its commas and semicolons, that is a reference and
nothing else (`isMarkerRef`). A code span within prose, as in "(over
`lang::q`)", is no reference. -/
def markerRefs (items : Array ReqItem) (g : Array Piece) : Option (Array Ref) := do
  let elements := g.foldl (init := #[#[]]) fun acc p =>
    if p == .text "," || p == .text ";" then acc.push #[] else acc.modify (acc.size - 1) (·.push p)
  let all := elements.filterMap fun e => (refOf e).bind id
  let pathGroup := all.any fun
    | .item q | .clauses _ (some q) => inDeclaredModule items q
    | _ => false
  let refs := all.filter (isMarkerRef items pathGroup)
  guard !refs.isEmpty
  return refs

/-- Items for the `#guard`s below, each with its clauses. -/
def guardItems (is : List (String × List String)) : Array ReqItem :=
  is.toArray.map fun (path, cs) => { path, file := "c", line := 100, clauses := cs.toArray }

#guard (groupsOf (pieces "x (`F0356`, `lang::size`) and (`a_b` and `c` of `lang::rules`) (`x::y` is (`z`)) (`g`)")).filterMap
    (markerRefs (guardItems [("lang::size", []), ("lang::rules", ["a_b", "c", "z"]), ("x::y", [])])) ==
  #[#[.item "lang::size"], #[.clauses #["a_b", "c"] (some "lang::rules")], #[.clauses #["z"] none]]
#guard (groupsOf (pieces "(see [`lang::m`](M.md#a)) (`lang::p`, over `lang::q`) (``a`b``) (`c`; see [S](S.md)) (`true` or `false`) (`lang::none`)")).filterMap
    (markerRefs (guardItems [("lang::m", []), ("lang::p", ["c"]), ("lang::q", [])])) ==
  #[#[.item "lang::p"], #[.clauses #["c"] none], #[.item "lang::none"]]
-- Example paths in prose are no marker; a misspelt clause beside a path is
-- one (the review of #688).
#guard (groupsOf (pieces "(`Shape::Circle`, `m::f`) (`a` of `E::V`) (`lang::p`, `conditon`) (`skiped`)")).filterMap
    (markerRefs (guardItems [("lang::p", ["condition"]), ("lang::q", ["skipped"])])) ==
  #[#[.item "lang::p", .clauses #["conditon"] none]]

/-- The requirements that formalize each rule of the chapter `md`, in
order, each item with the clauses named, and the problems of its markers:
the item named as the rule is, or whose clause is (`quantifier::guard`
with `ensure strict` for `quantifier.guard.strict`); and the items and
clauses that the rule names in a marker, a parenthesized group with a
reference (`markerRefs`). Clauses alone are of the last item that their
group names, or else of the last item that the latest marker before names,
which must have them (`Reqs/dev/Style#rules-and-requirements`). -/
def reqsOfChapter (md : String) (items : Array ReqItem) (rules : Array Rule) :
    Array (Rule × Array (ReqItem × Array String)) × Array String := Id.run do
  let find (p : String) := items.find? (·.path == p)
  let code (names : Array String) := ", ".intercalate (names.map (s!"`{·}`")).toList
  -- The last item that the latest marker names.
  let mut context : Option String := none
  let mut out := #[]
  let mut problems := #[]
  for r in rules do
    let here := s!"{md}:{r.line}"
    let p := reqPathOf r.id
    let mut links : Array (ReqItem × Array String) := #[]
    for i in items do
      if i.path == p then links := links.push (i, #[])
      for c in i.clauses do
        if s!"{i.path}::{c}" == p then links := links.push (i, #[c])
    for g in groupsOf (pieces r.text) do
      let some refs := markerRefs items g | continue
      let groupItem := refs.foldl (init := none) fun acc ref => match ref with
        | .item q | .clauses _ (some q) => some q
        | _ => acc
      for ref in refs do
        let (q?, names) := match ref with
          | .item q => (some q, #[])
          | .clauses names q => (q <|> groupItem <|> context, names)
        let some q := q?
          | problems := problems.push s!"{here}: the rule `{r.id}` names {code names} alone, and no marker before it names an item"
            continue
        -- A clause written as its item's path and its name.
        let segs := q.splitOn "::"
        let pre := "::".intercalate segs.dropLast
        let (q, names) := match ref, find q, find pre with
          | .item _, none, some j => if j.clauses.contains segs.getLast! then (pre, #[segs.getLast!]) else (q, names)
          | _, _, _ => (q, names)
        let some i := find q
          | problems := problems.push s!"{here}: the rule `{r.id}` names `{q}`, which is no item of the reference, nor a clause of one"
            continue
        let missing := names.filter (!i.clauses.contains ·)
        if missing.isEmpty then links := links.push (i, names)
        else
          for c in missing do
            let other := items.find? (·.clauses.contains c)
            let hint := other.map (fun j => s!": write \"`{c}` of `{j.path}`\" for that item's") |>.getD ""
            problems := problems.push s!"{here}: the rule `{r.id}` names `{c}`, which is no clause of `{q}`{hint}"
      if let some q := groupItem then
        if (find q).isSome then context := some q
    -- One entry for each item, with the clauses of all of its links.
    let merged := links.foldl (init := #[]) fun (acc : Array (ReqItem × Array String)) (i, cs) =>
      match acc.findIdx? (·.1.path == i.path) with
      | some k => acc.modify k fun (j, ds) => (j, ds ++ cs.filter (!ds.contains ·))
      | none => acc.push (i, cs)
    out := out.push (r, merged)
  return (out, problems)

/-- The links and problems of `reqsOfChapter` on rules with these texts,
for the `#guard`s below: each link as its item's path and clauses. -/
def guardLinks (items : List (String × List String)) (texts : List String) :
    Array (Array (String × Array String)) × Array String :=
  let rules := texts.toArray.zipIdx.map fun (text, k) => ({ id := s!"r.r{k}", line := k + 1, label := "", text } : Rule)
  let (out, problems) := reqsOfChapter "c" (guardItems items) rules
  (out.map fun (_, ls) => ls.map fun (i, cs) => (i.path, cs), problems)

-- A clause of another item than the latest marker's says which, though the
-- latest one has a clause of that name too (the review of #688).
#guard guardLinks [("lang::if_rules", ["then_branch", "condition"]), ("lang::guards_evaluation", ["one_branch", "condition"])]
    ["(`then_branch` of `lang::if_rules`)", "(`one_branch` of `lang::guards_evaluation`)", "(`condition` of `lang::if_rules`)", "(`condition`)"] ==
  (#[#[("lang::if_rules", #["then_branch"])], #[("lang::guards_evaluation", #["one_branch"])],
     #[("lang::if_rules", #["condition"])], #[("lang::if_rules", #["condition"])]], #[])
-- Clauses alone are of the latest marker's last item only, and of no
-- earlier one.
#guard guardLinks [("lang::if_rules", ["then_branch", "condition"]), ("lang::guards_evaluation", ["one_branch"])]
    ["(`then_branch` of `lang::if_rules`)", "(`one_branch` of `lang::guards_evaluation`)", "(`condition`)"] ==
  (#[#[("lang::if_rules", #["then_branch"])], #[("lang::guards_evaluation", #["one_branch"])], #[]],
   #["c:3: the rule `r.r2` names `condition`, which is no clause of `lang::guards_evaluation`: write \"`condition` of `lang::if_rules`\" for that item's"])
#guard guardLinks [("lang::method_rules", []), ("lang::call_rules", ["recursive"])]
    ["(`lang::method_rules`, `lang::call_rules`)", "(`recursive`)", "(`a` alone)", "x (`recursive`)"] ==
  (#[#[("lang::method_rules", #[]), ("lang::call_rules", #[])], #[("lang::call_rules", #["recursive"])], #[],
     #[("lang::call_rules", #["recursive"])]], #[])
-- A misspelt marker fails where it is written, and leaves the context to
-- the markers that name an item (the review of #688).
#guard guardLinks [("lang::lazy_rules", ["and_false", "and_unevaluated", "and_true"])]
    ["(`and_false` of `lang::lazy_rules`)", "(`and_unevaluatd` of `lang::lazy_rules`)", "(`lang::lazy_rule`)", "(`and_true`)"] ==
  (#[#[("lang::lazy_rules", #["and_false"])], #[], #[], #[("lang::lazy_rules", #["and_true"])]],
   #["c:2: the rule `r.r1` names `and_unevaluatd`, which is no clause of `lang::lazy_rules`",
     "c:3: the rule `r.r2` names `lang::lazy_rule`, which is no item of the reference, nor a clause of one"])
-- A misspelt clause beside a path fails; a clause written as a path links.
#guard guardLinks [("lang::if_rules", ["condition"]), ("lang::lazy_rules", ["and_true"])]
    ["(`lang::if_rules`, `conditon`)", "(`lang::lazy_rules::and_true`)"] ==
  (#[#[("lang::if_rules", #[])], #[("lang::lazy_rules", #["and_true"])]],
   #["c:1: the rule `r.r0` names `conditon`, which is no clause of `lang::if_rules`"])
#guard (guardLinks [("lang::p", ["c"])] ["(`c`)"]).2 == #["c:1: the rule `r.r0` names `c` alone, and no marker before it names an item"]

/-- The requirements of `reqs`, which formalize the rule `r` of the chapter
`md`, that are declared in `md` before it: a ```` ```fren ```` block
follows the rules that it formalizes (`Reqs/dev/Style#checked-blocks`). -/
def declaredBefore (md : String) (r : Rule) (reqs : Array ReqItem) : Array ReqItem :=
  reqs.filter fun i => i.file == md && i.line < r.line

#guard (declaredBefore "c" { id := "a", line := 5, label := "", text := "" }
    #[{ path := "x::p", file := "c", line := 4, clauses := #[] }, { path := "x::q", file := "c", line := 6, clauses := #[] },
      { path := "x::r", file := "d", line := 1, clauses := #[] }]).map (·.path) == #["x::p"]

/-- The rules of the reference's Legality rules and Dynamic semantics that
no requirement formalizes yet (`Reqs/dev/Style#rules-and-requirements`). -/
def unformalizedFile : FilePath := "test" / "unformalized_rules.txt"

/-- The mark of a section of `unformalizedFile` whose chapter's Interlock
step is still to come, after the chapter's path in its heading. -/
def pendingMark : String := " (Interlock pending)"

/-- What a line of `unformalizedFile` says of a rule whose markers link
only some of what it states, which stays listed until they link all of it. -/
def partlyMark : String := "partly formalized"

/-- Whether `why`, the reason on a line of `unformalizedFile`, says
`partlyMark`, alone or followed by `:` and what is missing. -/
def isPartly (why : String) : Bool := why == partlyMark || why.startsWith s!"{partlyMark}:"

#guard isPartly "partly formalized" && isPartly "partly formalized: no claim for max"
#guard !isPartly "partly formalized max" && !isPartly "unformalized"

/-- An entry of a list such as `unformalizedFile`: its line, the rule's
identifier, why it has no requirement (`""` if it does not say), the
chapter of the section that it is in (`""` before any), and whether that
section is marked `pendingMark`. -/
structure Listed where
  line : Nat
  id : String
  why : String
  chapter : String
  pending : Bool
  deriving BEq, Repr

/-- The entries of a list such as `unformalizedFile`: each line but a blank
one or a comment, `#`, as the rule's identifier, then ` -- ` and why, if it
says. A comment `# src/...md` starts the section of that chapter. -/
def listedRules (text : String) : Array Listed := Id.run do
  let mut chapter := ""
  let mut pending := false
  let mut out := #[]
  for l in text.splitOn "\n", i in [1:text.length + 2] do
    if let some h := l.dropPrefix? "# src/" then
      let h := h.toString
      pending := h.endsWith pendingMark
      chapter := "src/" ++ (if pending then (h.dropEnd pendingMark.length).toString else h)
      continue
    let id := ((l.splitOn " -- ").head!).trimAscii.toString
    if id.isEmpty || id.startsWith "#" then continue
    out := out.push { line := i, id, why := " -- ".intercalate ((l.splitOn " -- ").drop 1), chapter, pending }
  return out

#guard listedRules "# x\n# src/A.md (Interlock pending)\na.b\n\n# src/B.md\nc.d -- why\n" ==
  #[{ line := 3, id := "a.b", why := "", chapter := "src/A.md", pending := true },
    { line := 6, id := "c.d", why := "why", chapter := "src/B.md", pending := false }]

/-- The rules that a test cites, each with its line: `--@ reference: ID`
(`Reqs/dev/Style#rules-and-requirements`). A line with `--@ reference`
that is not so written cites `""`, which is no rule. -/
def citedRules (src : String) : Array (Nat × String) :=
  ((src.splitOn "\n").zipIdx.filterMap fun (l, i) =>
    (l.splitOn "--@ reference")[1]?.map fun rest =>
      (i + 1, ((rest.dropPrefix? ": ").map (·.toString.trimAscii.toString)).getD "")).toArray

#guard citedRules "a\n--@ reference: q.r\n--@ reference:q.s\n" == #[(2, "q.r"), (3, "")]

/-- The `impl`s of `src/Impls`, each with its name, the path of the
requirement that it is bound to, and its file. -/
def implBindings : IO (Array (String × String × String)) := do
  let mut out := #[]
  for f in ← sortedFiles ("src" / "Impls") "lean" do
    for line in (← IO.FS.readFile f).splitOn "\n" do
      if let some rest := line.dropPrefix? "impl " then
        if let name :: after :: _ := rest.toString.splitOn ": " then
          out := out.push (name, (after.splitOn " ").head!, f.toString)
  return out

/-- The rules of the reference with their requirements, by chapter, the
rules that tests cite, each with the test, and the problems that
`ruleReqs` finds (`Reqs/dev/Style#rules-and-requirements`). -/
def ruleLinks : IO (Array (String × Array (Rule × Array (ReqItem × Array String))) × Array (String × String) × Array String) := do
  let texts ← (← manualFiles).mapM fun md => return (md.toString, ← IO.FS.readFile md)
  let mut failures := #[]
  let mut items := #[]
  for (md, text) in texts do
    match reqItemsOf md text with
    | .ok is => items := items ++ is
    | .error e => failures := failures.push e
  let mut chapters := #[]
  for (md, text) in texts do
    let rules := rulesOf text
    if rules.isEmpty then continue
    let (linked, problems) := reqsOfChapter md items rules
    failures := failures ++ problems
    chapters := chapters.push (md, linked)
  let rules := chapters.flatMap fun (md, rs) => rs.map fun (r, reqs) => (md, r, reqs)
  -- Each rule of Legality rules or Dynamic semantics has a requirement, or
  -- is listed, and not both.
  let listed := listedRules (← IO.FS.readFile unformalizedFile)
  for e in listed, k in [0:listed.size] do
    let here := s!"{unformalizedFile}:{e.line}"
    if (listed.extract 0 k).any (·.id == e.id) then
      failures := failures.push s!"{here}: `{e.id}` is listed already"
      continue
    match rules.find? (·.2.1.id == e.id) with
    | none => failures := failures.push s!"{here}: `{e.id}` is no rule"
    | some (md, r, reqs) =>
      if !formalLabels.contains r.label then
        failures := failures.push s!"{here}: `{e.id}` ({md}:{r.line}) is not under **Legality rules** or **Dynamic semantics**, so it needs no requirement: remove its line"
      else if !reqs.isEmpty && !isPartly e.why then
        failures := failures.push s!"{here}: `{e.id}` ({md}:{r.line}) is formalized by `{reqs[0]!.1.path}`: remove its line, or say ` -- {partlyMark}` if that is only part of the rule"
      else if reqs.isEmpty && isPartly e.why then
        failures := failures.push s!"{here}: `{e.id}` ({md}:{r.line}) has no requirement at all, so it is not `{partlyMark}`"
      else if e.chapter != md then
        failures := failures.push s!"{here}: `{e.id}` is a rule of {md}, so it is listed under `# {md}`"
      else if e.why == partlyMark && !e.pending then
        failures := failures.push s!"{here}: `{e.id}` says it is `{partlyMark}`, but not what is missing, though its chapter's Interlock step is done: write ` -- {partlyMark}: WHAT`"
      else if e.why.isEmpty && !e.pending then
        failures := failures.push s!"{here}: `{e.id}` says no reason, after ` -- `, though its chapter's Interlock step is done (no `{pendingMark.trimAscii}`)"
  for (md, r, reqs) in rules do
    let here := s!"{md}:{r.line}"
    if formalLabels.contains r.label && reqs.isEmpty && !listed.any (·.id == r.id) then
      failures := failures.push s!"{here}: the rule `{r.id}` has no requirement: name one in a marker, \"(`lang::p`)\", or give one its name (`{reqPathOf r.id}`), or list it in {unformalizedFile}"
    -- The block that formalizes a rule follows it.
    for i in declaredBefore md r (reqs.map (·.1)) do
      failures := failures.push s!"{here}: the rule `{r.id}` is formalized by `{i.path}`, which is declared before it, at line {i.line}"
  -- An item of a chapter that is in a module named as one of the chapter's
  -- constructs, and each of its clauses, has a rule of its name, where the
  -- name is shaped as a rule identifier is.
  let ruleIds := rules.map (·.2.1.id)
  for (md, rs) in chapters do
    let constructs := (rs.map fun (r, _) => (r.id.splitOn ".").head!).toList.eraseDups
    for i in items do
      unless i.file == md && constructs.contains ((i.path.splitOn "::").head!) do continue
      let names := if i.clauses.isEmpty then #[i.path] else i.clauses.map (s!"{i.path}::{·}")
      for n in names do
        if (n.splitOn "::").all ruleShaped && !ruleIds.any (reqPathOf · == n) then
          failures := failures.push s!"{i.file}:{i.line}: `{n}` is named as a rule, but no rule is named `{(n.replace "::" ".").replace "_" "-"}`"
  -- Every rule that a test cites exists.
  let mut tests := #[]
  let cite (here id : String) : StateT (Array (String × String) × Array String) IO Unit := modify fun (ts, fs) =>
    if ruleIds.contains id then (ts.push (here, id), fs)
    else (ts, fs.push s!"{here}: `{id}` is no rule: a test cites one with a line `--@ reference: ID`")
  let ((), (ts, fs)) ← (do
      for f in (← sortedFiles "test" "fren") ++ (← sortedFiles "examples" "fren") do
        for (line, id) in citedRules (← IO.FS.readFile f) do cite s!"{f}:{line}" id
      for (md, text) in texts do
        for (start, src) in exampleBlocks text do
          for (line, id) in citedRules src do cite s!"{md}:{start + line}" id
    : StateT _ IO Unit).run (tests, failures)
  tests := ts.map fun (here, id) => ((here.splitOn ":").head!, id)
  return (chapters, tests, fs)

/-- The text of the page of the book that reports, for each rule, its
requirements, the `impl`s bound to them and the tests that cite it,
`dev/Rules.md`, which `scripts/rules_report.py` writes when the book is
built. -/
def rulesReportText (chapters : Array (String × Array (Rule × Array (ReqItem × Array String))))
    (impls : Array (String × String × String)) (tests : Array (String × String)) (partly : Array String) : String := Id.run do
  let rel (md : String) := "../" ++ ((md.dropPrefix? "src/Reqs/").map (·.toString)).getD md
  let mut out := "# Rules and their requirements\n\n"
    ++ "For each rule of a chapter of the reference that has rule identifiers:\n"
    ++ "the requirements that formalize it, the `impl`s bound to them, and the\n"
    ++ "tests that cite it (see [Writing the reference](Style.md#rules-and-requirements)).\n"
    ++ "A rule of **Legality rules** or **Dynamic semantics** with no\n"
    ++ "requirement, or any rule with no test, says **none**, and one whose\n"
    ++ "requirements formalize only part of it says *partly*. This page is\n"
    ++ "written when the book is built.\n"
  for (md, rules) in chapters do
    let formal := rules.filter (formalLabels.contains ·.1.label)
    let untested := rules.filter fun (r, _) => !tests.any (·.2 == r.id)
    out := out ++ s!"\n## [{md}]({rel md})\n\n{rules.size} rules, {formal.size} of them of legality or dynamic semantics, "
      ++ s!"{(formal.filter fun (r, reqs) => reqs.isEmpty || partly.contains r.id).size} of which have no requirement "
      ++ s!"or only part of one; {untested.size} rules have no test.\n\n"
      ++ "| Rule | Label | Requirements | `impl`s | Tests |\n|---|---|---|---|---|\n"
    for (r, reqs) in rules do
      let reqCell := if reqs.isEmpty then (if formalLabels.contains r.label then "**none**" else "")
        else ", ".intercalate (reqs.map fun (i, cs) =>
          if cs.isEmpty then s!"`{i.path}`" else s!"`{i.path}` ({", ".intercalate (cs.map (s!"`{·}`")).toList})").toList
          ++ (if partly.contains r.id then ", *partly*" else "")
      let implCell := ", ".intercalate ((impls.filter fun (_, p, _) => reqs.any (·.1.path == p)).map
        fun (n, _, f) => s!"`{n}` ({f})").toList
      let cited := (tests.filter (·.2 == r.id)).map (·.1)
      let testCell := if cited.isEmpty then "**none**" else ", ".intercalate (cited.toList.eraseDups.map (s!"`{·}`"))
      out := out ++ s!"| [`{r.id}`]({rel md}#r-{r.id}) | {r.label} | {reqCell} | {implCell} | {testCell} |\n"
  return out

/-- The rules of the reference and their requirements and tests
(`Reqs/dev/Style#rules-and-requirements`): every rule of **Legality rules**
or **Dynamic semantics** has a requirement, or is listed in
`unformalizedFile`, and not both unless the line says `partlyMark`
(`isPartly`); a
listed rule is in its chapter's section, and says why it has none once
its chapter's Interlock step is done; the clauses that a marker names
alone are clauses of the item that they resolve to, and every item and
clause that a marker names exists; each requirement that
formalizes a rule and is declared in its chapter is declared after it;
each item of a module named as one of its chapter's constructs, whose
name is shaped as a rule identifier, is named as a rule, or, if it has
clauses, each of them whose name is so shaped is; and every rule that a
test cites exists. -/
def ruleReqs : IO (Array String) := return (← ruleLinks).2.2

/-- The text of the report of the rules (`rulesReportText`), for
`fren_test --rules-report`. -/
def rulesReport : IO String := do
  let (chapters, tests, _) ← ruleLinks
  let partly := (listedRules (← IO.FS.readFile unformalizedFile)).filterMap fun e =>
    if isPartly e.why then some e.id else none
  return rulesReportText chapters (← implBindings) tests partly

/-! ## Fren's own requirements -/

/-! ## Error codes -/

/-- The ```` ```fren ```` blocks of a Markdown text. -/
def frenBlocks (md : String) : Array String :=
  (Fren.Core.fencedBlocks md).filterMap fun b =>
    if b.info == Fren.Core.frenInfo then some ("\n".intercalate b.body.toList ++ "\n") else none

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
    "Lang/Traits",
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
    "Methods",
    "Models",
    "Evidence",
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
    "Lint/Pedantic/Booleans",
    "Lint/Restriction",
    "Lint/Decidability",
    "Lint/Printing",
    "Lint/Rewrites",
    "Eval",
    "Lang/Refinement",
    "Mutate",
    "Fmt",
    "Impl",
    "Generated",
    "Trace",
    "Markdown",
    "dev/Testing",
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
def frenBlockLines (md : String) : Array String :=
  (Fren.Core.fencedBlocks md).foldl (init := #[]) fun acc b =>
    if b.info == Fren.Core.frenInfo then acc ++ b.body else acc

/-- The procedures and global expectations that the `fren` block lines
`ls` declare, which a `#fren_check` checks: each by its name. -/
def checkedItems (ls : Array String) : Array String :=
  ls.filterMap fun l =>
    let l := ((l.dropPrefix? "pub ").map (·.toString)).getD l
    let word (pre : String) : Option String := (l.dropPrefix? pre).map fun r =>
      (r.toString.takeWhile fun c => c.isAlphanum || c == '_' || c == '?').toString
    (word "proc ").orElse fun _ => word "expect "

/-- The `#fren_check`s of the Markdown text `md`, in its `fren` blocks: a
line in prose is prose, which `#fren_md` does not read (`Reqs/Markdown`). -/
def chapterChecks (md : String) : Array String :=
  (frenBlockLines md).filter (·.trimAscii.toString.startsWith "#fren_check")

#guard chapterChecks "```fren\nproc p() {}\n#fren_check p\n```\n\n#fren_check\n" == #["#fren_check p"]

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
    let checks := texts.map chapterChecks
    for c in chapters.toArray, t in texts, k in [0:texts.size] do
      let items := checkedItems (frenBlockLines t)
      if items.isEmpty then continue
      let bare := (checks.extract k checks.size).any (·.any (·.trimAscii.toString == "#fren_check"))
      let named := checks[k]!.filterMap fun l => (l.trimAscii.toString.dropPrefix? "#fren_check ").map (·.toString.trimAscii.toString)
      for i in items do
        unless bare || named.contains i do
          failures := failures.push s!"src/Reqs/{c}: `{i}` is checked by no `#fren_check` in Lean, as the chapter comes after its file's last `#fren_check` in a `fren` block: name it, as `#fren_check {i}`"
  return failures

/-- `fren check --query-cache` gives the same output cold, in a fresh
directory, as warm, from it, and the warm run answers every query from the
cache, writing no entry; a third run, cold into another fresh directory
and compared with the first's, compares answers and finds no
contradiction, and writes the same entries. Comparing with a copy of the
first's entries whose answers are flipped gives one contradiction for
each, an internal error with no position; and a `sat` entry without a
model answers a query that wants none, but not one that wants one
(`Reqs/Cli#query-cache`). -/
def queryCache : IO (Array String) := do
  let file := "test/fixtures/query_cache.fren"
  let root : FilePath := ".lake" / "query-cache-test" / s!"{← IO.monoNanosNow}"
  let first := (root / "first").toString
  let second := (root / "second").toString
  let run (args : List String) := runFren (["check"] ++ args ++ [file])
  let files (d : String) : IO (Array FilePath) := do
    let fs ← (FilePath.mk d).walkDir
    let fs ← fs.filterM fun f => return !(← f.isDir)
    return fs.qsort (·.toString < ·.toString)
  let entries (d : String) : IO (Array String) := do (← files d).mapM IO.FS.readFile
  -- Each entry with when it was last written: an entry written again,
  -- renamed into place, is a new file.
  let written (d : String) : IO (Array (String × IO.FS.SystemTime)) := do
    (← files d).mapM fun f => return (f.toString, (← f.metadata).modified)
  let (plain, plainCode) ← run []
  let (cold, coldCode) ← run ["--query-cache", first]
  let afterCold ← written first
  let (warm, warmCode) ← run ["--query-cache", first]
  let (verified, verifiedCode) ← run ["--query-cache", second, "--verify-query-cache", first]
  let mut failures := #[]
  for (name, out, code) in [("cold", cold, coldCode), ("warm", warm, warmCode)] do
    unless out == plain && code == plainCode do
      failures := failures.push s!"{name}, the output differs from that without the cache:\n{out}\n---\n{plain}"
  if (← entries first).isEmpty then failures := failures.push "the cold run kept no answers"
  -- The warm run answered every query from the cache: it wrote no entry.
  unless (← written first) == afterCold do
    failures := failures.push "the warm run wrote to the cache, so it did not answer every query from it"
  unless (← entries first) == (← entries second) do
    failures := failures.push "two cold runs kept different answers"
  let (counts, rest) := (verified.splitOn "\n").partition (·.startsWith "fren: compared ")
  unless "\n".intercalate rest == plain && verifiedCode == plainCode
      && counts.length == 1 && !counts.any (·.startsWith "fren: compared 0 ") do
    failures := failures.push s!"the verified run differs or compared nothing:\n{verified}"
  let (_, missingCode) ← run ["--verify-query-cache", (root / "missing").toString]
  unless missingCode == 2 do failures := failures.push "a missing directory to compare with is not an error"
  -- An entry whose answer is flipped contradicts the solver's: an internal
  -- error, which names the entry, with no position.
  let flipped := (root / "flipped").toString
  let mut flips := 0
  for (f, text) in (← files first).zip (← entries first) do
    let rel := (f.toString.dropPrefix (first ++ "/")).toString
    let text' := if text.endsWith "\nunsat\n" then some ((text.dropEnd 6).toString ++ "sat\n")
      else if text.endsWith "\nsat\n" then some ((text.dropEnd 4).toString ++ "unsat\n") else none
    let target := FilePath.mk flipped / rel
    if let some p := target.parent then IO.FS.createDirAll p
    IO.FS.writeFile target (text'.getD text)
    if text'.isSome then flips := flips + 1
  let (contradicted, contradictedCode) ← run ["--verify-query-cache", flipped]
  let lines := (contradicted.splitOn "\n").toArray
  let errorLines := (List.range lines.size).filter fun i =>
    lines[i]!.startsWith "error: internal error: the solver's answer contradicts the query cache's entry"
  -- A position would be the next line, as `--> file:line:col`.
  let positioned := errorLines.any fun i => (lines[i + 1]?.getD "").trimAscii.startsWith "-->"
  unless flips > 0 && errorLines.length == flips && contradictedCode == 1 && !positioned do
    failures := failures.push s!"flipping {flips} answers did not give as many contradictions, each with no position (exit {contradictedCode}):\n{contradicted}"
  -- A `sat` entry without a model answers a query that does not want one,
  -- and not one that does, which the solver answers.
  let k : FrenCli.CacheKey := FrenCli.CacheKey.of "(check-sat)" [] (← FrenCli.cvc5Version)
  let modelless := root / "modelless"
  FrenCli.writeEntry modelless k (.sat #[]) false 0
  unless (← FrenCli.lookupEntry? modelless k false).isSome && (← FrenCli.lookupEntry? modelless k true).isNone do
    failures := failures.push "a `sat` entry without a model answers a query that wants one, or not one that does not"
  -- The observations of a model, guarded or not, survive a key's lines
  -- (`cli::query_key`), and one whose name has a numeric component has no
  -- key.
  let observations : List FrenCli.ModelObservation :=
    [{ key := `a.b, formula := "(f x)" }, { key := `c, formula := "(g\ny)", guard? := some `d.e }]
  match observations.mapM FrenCli.KeyObservation.of? with
  | none => failures := failures.push "an observation whose names have no numeric component has no key"
  | some os =>
    let k := FrenCli.CacheKey.of "(check-sat)" os (← FrenCli.cvc5Version)
    unless os.map (·.name) == [["a", "b"], ["c"]] && os.map (·.guard?) == [none, some ["d", "e"]]
        && (FrenCli.CacheKey.read? (k.lines.splitOn "\n")).map (·.1) == some k do
      failures := failures.push s!"a key's observations do not survive its lines:\n{k.lines}"
  if (FrenCli.KeyObservation.of? { key := .num `a 1, formula := "x" }).isSome then
    failures := failures.push "an observation whose name has a numeric component has a key"
  -- A cache with an entry of this version and solver can be compared
  -- with; an empty one, or one of another solver, cannot.
  let solver ← FrenCli.cvc5Version
  unless (← FrenCli.comparableEntries (FilePath.mk first) solver) && !(← FrenCli.comparableEntries (FilePath.mk first) "another solver")
      && !(← FrenCli.comparableEntries (root / "missing") solver) do
    failures := failures.push "`comparableEntries` misjudges a cache that a run could compare with"
  IO.FS.removeDirAll root
  return failures

/-- A satisfiable query whose solver initializes its theories at a
definition: in `ALL`, a logic with nonlinear arithmetic, whose solvers
take `FrenCli.Cvc5.solverLock`, or, if `linear`, in `QF_UFDTLIA`, whose
solvers do not. -/
def lifetimeScript (k : Nat) (linear : Bool := false) : String :=
  if linear then
    s!"(set-logic QF_UFDTLIA)\n(set-option :produce-models true)\n(declare-const x Int)\n" ++
      s!"(define-fun dbl ((y Int)) Int (+ y y))\n(assert (> (dbl x) {k}))\n"
  else
    s!"(set-logic ALL)\n(set-option :produce-models true)\n(declare-const x Int)\n" ++
      s!"(define-fun sq ((y Int)) Int (* y y))\n(assert (> (sq x) {k}))\n"

/-- This process's resident memory, in kB, as `ps` reports it. -/
def residentKb : IO Nat := do
  let out ← IO.Process.output { cmd := "ps", args := #["-o", "rss=", "-p", toString (← IO.Process.getPID)] }
  return out.stdout.trimAscii.toString.toNat!

/-- Each query's solver is freed once it is answered, so that the memory
of `fren check` does not grow with the number of its queries; and solvers
of a logic with nonlinear arithmetic answer correctly on several threads
at once, which they share libpoly's state for (`FrenCli.Cvc5`). -/
def solverLifetime : IO (Array String) := do
  let mut failures := #[]
  let solve (k : Nat) (linear : Bool := false) : IO Bool := do
    return (← FrenCli.solveScript (lifetimeScript k linear) #[] false) matches .sat _
  -- Warm up the allocator first, so that what it keeps does not count.
  for k in [0:100] do discard <| solve k
  let before ← residentKb
  let mut wrong := 0
  for k in [0:500] do
    unless ← solve k do wrong := wrong + 1
  let grown := (← residentKb) - before
  -- A solver held about 1.5 MB, so 500 of them about 750 MB.
  if grown > 100 * 1024 then
    failures := failures.push s!"500 queries grew the memory by {grown / 1024} MB: their solvers are not freed"
  -- Sixteen threads at once, each initializing and freeing its solvers:
  -- without `FrenCli.Cvc5.exclusively`, this crashed one run in three.
  -- After every third, each thread asks one in a linear logic, whose
  -- solvers take no lock and must answer correctly beside those that do.
  let tasks ← (List.range 16).mapM fun t => IO.asTask (prio := .dedicated) do
    let mut n := 0
    for k in [0:300] do
      if ← solve (1000 * t + k) then n := n + 1
      if k % 3 == 0 then if ← solve (1000 * t + k) (linear := true) then n := n + 1
    return n
  for t in tasks do
    match ← IO.wait t with
    | .ok n => wrong := wrong + (400 - n)
    | .error e => failures := failures.push s!"a thread of queries failed: {e}"
  if wrong > 0 then failures := failures.push s!"{wrong} satisfiable queries were not answered `sat`"
  return failures

/-- The query caches of `ownSpec` (`Reqs/dev/Testing#query-cache`): the
directory `FREN_QUERY_CACHE`, by default `.lake/query-cache`, or none if it
is empty; and the one to compare with, `FREN_VERIFY_QUERY_CACHE`, if set. -/
def ownSpecCaches : IO (Option String × Option String) := do
  let dir? := match ← IO.getEnv "FREN_QUERY_CACHE" with
    | none => some ".lake/query-cache"
    | some "" => none
    | some d => some d
  let verify? := (← IO.getEnv "FREN_VERIFY_QUERY_CACHE").filter (· != "")
  return (dir?, verify?)

/-- Fren's own requirements pass under the binary, and it checks every
chapter that the Lean front end does; and Lean checks every chapter too
(`hostedChecks`). -/
def ownSpec : IO (Array String) := do
  let missing := (← hostedSpecFiles).filter (!ownSpecFiles.contains ·)
  let (queryCache?, verifyQueryCache?) ← ownSpecCaches
  let (out, code) ← IO.FS.withIsolatedStreams
    (FrenCli.check { files := ownSpecFiles, queryCache?, verifyQueryCache? })
  -- A contradiction leaves a mark next to the cache, so that CI does not
  -- save it (`Reqs/dev/Testing#query-cache`).
  if let some dir := queryCache? then
    if out.contains "contradicts the query cache's entry".toSlice then
      IO.FS.writeFile (dir ++ ".contradicted") out
  -- A comparison that compared nothing checks nothing, unless there was
  -- nothing to compare with: after a change to `queryCacheVersion` or to
  -- cvc5, which alters every key, the previous cache has no entry that
  -- this run could compare with (`Reqs/dev/Testing#query-cache`).
  let compared ← if verifyQueryCache?.isSome && !out.contains "fren: compared ".toSlice then
      pure #["the binary did not report how many answers it compared with the query cache"]
    else if let (some dir, true) := (verifyQueryCache?, out.contains "fren: compared 0 answers".toSlice) then
      if ← FrenCli.comparableEntries dir (← FrenCli.cvc5Version) then
        pure #[s!"the binary compared no answers with the query cache `{dir}`, which has entries of this " ++
          "`queryCacheVersion` and cvc5: if this change alters every query's key, such as the scripts' " ++
          "header, bump `FrenCli.queryCacheVersion`"]
      else pure #[]
    else pure #[]
  return (missing.map (s!"{·} is read by `#fren_md` but not in `ownSpecFiles`, so the binary does not check it"))
    ++ (if code == 0 then #[] else #[s!"src/Reqs failed under the binary:\n{out}"])
    ++ compared
    ++ (← hostedChecks)

/-- A message that Lake kept in a module's trace, `src/Reqs/M.lean:L:C: text`
or `src/Reqs/M.lean:L:C: warning: text`, about a Markdown spec that the
module reads: the spec, as a path from the repository's root, and the
message, at its position in the spec (`Fren.elabMd` places it at the
`#fren_md` and starts its text with `NAME.md:LINE:COL: `, the column from
0). A message about the Lean file's own item, or Lean's summary of a
`#fren_check` (`fren: …`), is none. -/
def ownSpecMessage? (level : String) (message : String) : Option (String × Diagnostic) := do
  let severity ← match level with
    | "info" => some "info"
    | "warning" => some "warning"
    | "error" => some "error"
    | _ => none
  -- After the Lean file's position, `src/Reqs/M.lean:L:C: `.
  let rest := match message.splitOn ".lean:" with
    | _ :: after@(_ :: _) => ".lean:".intercalate after
    | _ => ""
  let rest := match rest.splitOn ": " with
    | _ :: after@(_ :: _) => ": ".intercalate after
    | _ => ""
  let rest := ["warning: ", "error: "].foldl (fun r p => ((r.dropPrefix? p).map (·.toString)).getD r) rest
  match rest.splitOn ": " with
  | loc :: text@(_ :: _) =>
    match loc.splitOn ":" with
    | [name, line, col] =>
      guard (name.endsWith ".md")
      let text := ": ".intercalate text
      guard (!text.startsWith "fren: ")
      return (s!"src/Reqs/{name}", { line := ← line.toNat?, col := ← col.toNat?, severity, text })
    | _ => none
  | _ => none

#guard (ownSpecMessage? "info" "src/Reqs/Lang.lean:33:0: Lang/Types.md:1041:10: cover goal `t` is met\n\nwitness: x = 1").map
  (fun (f, d) => (f, d.line, d.col, d.severity, d.text)) ==
  some ("src/Reqs/Lang/Types.md", 1041, 10, "info", "cover goal `t` is met\n\nwitness: x = 1")
#guard (ownSpecMessage? "warning" "src/Reqs/Check.lean:15:0: warning: Check.md:3:4: could not decide").map
  (fun (f, d) => (f, d.line, d.severity)) == some ("src/Reqs/Check.md", 3, "warning")
#guard (ownSpecMessage? "info" "src/Reqs/Fmt.lean:9:0: Fmt.md:461:0: fren: 100 passed, 0 failed").isNone
#guard (ownSpecMessage? "trace" "src/Reqs/Fmt.lean:9:0: Fmt.md:461:0: x").isNone
#guard (ownSpecMessage? "info" "stderr:\nCould not evaluate").isNone

/-- The level and text of each message in the log of the Lake trace `text`. -/
def traceEntries (text : String) : Array (String × String) :=
  let log : Array Json := match Json.parse text >>= (·.getObjValAs? (Array Json) "log") with
    | .ok l => l
    | .error _ => #[]
  log.filterMap fun e =>
    match e.getObjValAs? String "level", e.getObjValAs? String "message" with
    | .ok level, .ok message => some (level, message)
    | _, _ => none

/-- Why the trace `trace` of `Reqs.stem`, of log `entries`, cannot show
Lean's checks of it: it was built without them, or its log has no command,
which Lake logs first, as when the module was taken from the artifact cache
(`Reqs/dev/Testing#shared-builds`). -/
def traceProblem (trace stem : String) (entries : Array (String × String)) : Option String :=
  match entries.find? (·.1 == "trace") with
  | some (_, cmd) =>
    if cmd.contains "fren.runChecks=false".toSlice then
      some s!"{trace}: `Reqs.{stem}` was built without its checks; run `lake -R -Kcheck_reqs=1 build Reqs` first"
    else none
  | none => some s!"{trace}: no command in its log, so whether its checks ran is unknown"

#guard (traceProblem "t" "Lang" (traceEntries "{\"log\": [{\"level\": \"trace\", \"message\": \"lean -Dweak.fren.runChecks=false x.lean\"}]}")).isSome
#guard (traceProblem "t" "Lang" (traceEntries "{\"log\": [{\"level\": \"trace\", \"message\": \"lean x.lean\"}, {\"level\": \"info\", \"message\": \"m\"}]}")).isNone
#guard (traceProblem "t" "Lang" (traceEntries "{\"log\": [{\"level\": \"info\", \"message\": \"m\"}]}")).isSome
#guard (traceProblem "t" "Lang" (traceEntries "{}")).isSome

/-- The Lean front end's messages about the Markdown specs of Fren's own
requirements, from the logs that Lake kept in the traces of the modules of
`src/Reqs` (`ownSpecMessage?`), with the problems: a module without a trace,
or built without its checks (`fren.runChecks`), as `lake build` builds it
unless `-Kcheck_reqs` is set. -/
def hostedOwnSpec : IO (Array (String × Diagnostic) × Array String) := do
  let mut msgs := #[]
  let mut problems := #[]
  let modules := (← System.FilePath.readDir "src/Reqs").filter (·.path.extension == some "lean")
  for entry in modules.qsort (·.fileName < ·.fileName) do
    let some stem := entry.path.fileStem | continue
    let trace : FilePath := ".lake" / "build" / "lib" / "lean" / "Reqs" / s!"{stem}.trace"
    let text ← match ← (IO.FS.readFile trace).toBaseIO with
      | .ok t => pure t
      | .error _ =>
        problems := problems.push s!"{trace}: no trace; run `lake -R -Kcheck_reqs=1 build Reqs` first"
        continue
    let entries := traceEntries text
    if let some p := traceProblem trace.toString stem entries then problems := problems.push p
    msgs := msgs ++ entries.filterMap fun (level, message) => ownSpecMessage? level message
  return (msgs, problems)

/-- Lean's note that it leaves checks to `fren check`: those set to random
testing, or that rest on them (`Reqs/Evidence#lean`). -/
def leavesToBinary (d : Diagnostic) : Bool :=
  d.severity == "info" && ((FrenTest.Frontends.headOf d).splitOn " set to random testing are run by `fren check`").length > 1

/-- The reports to compare on a spec of Fren's own requirements, of text
`text`, from the binary's messages `cli` and Lean's `hosted`, without what
only the binary runs (`ownSpecAgreement`): the checks set to random
testing and those that rest on them, which Lean leaves to it and does not
report (`Reqs/Evidence#lean`). So Lean's notes that it leaves them
(`leavesToBinary`) are dropped, and so is a message of the binary's that
Lean does not report alike: a caveat about them (`F0654`, `F0663`), or
any message in an item that Lean notes. Lean reports a check once for each
`#fren_check` of its Lean file that runs it, so its messages are counted
once. -/
def ownSpecReports (text : String) (cli hosted : Array Diagnostic) : FrenTest.Frontends.Report × FrenTest.Frontends.Report :=
  let items := FrenTest.Frontends.itemOf text
  let itemAt (n : Nat) := items[n]?.getD 0
  let same (a b : Diagnostic) := a.line == b.line && a.col == b.col && a.severity == b.severity && a.text == b.text
  let hosted := hosted.foldl (init := #[]) fun acc d => if acc.any (same d) then acc else acc.push d
  let left := (hosted.filter leavesToBinary).map (itemAt ·.line)
  let alike (c : Diagnostic) := hosted.any fun h => h.line == c.line && h.col == c.col && h.severity == c.severity
    && FrenTest.Frontends.normHead h.text == FrenTest.Frontends.normHead c.text
  let cli := cli.filter fun c => alike c || !(c.code?.any (["F0654", "F0663"].contains ·) || left.contains (itemAt c.line))
  ({ diags := cli }, { diags := hosted.filter (!leavesToBinary ·) })

/-- The binary's messages, and Lean's, on a procedure `p` whose checks of
`b` Lean leaves to the binary: for `ownSpecReports`. -/
def ownSpecExample : Array Diagnostic × Array Diagnostic :=
  (#[{ line := 2, col := 4, severity := "info", text := "cover goal `a` is met" },
     { line := 3, col := 4, severity := "info", text := "cover goal `b` is met" },
     { line := 1, col := 0, severity := "info", text := "x", code? := some "F0663" }],
   #[{ line := 2, col := 4, severity := "info", text := "cover goal `a` is met" },
     { line := 2, col := 4, severity := "info", text := "cover goal `a` is met" },
     { line := 1, col := 0, severity := "info",
       text := "the checks of `p` that rest on checks set to random testing are run by `fren check`, not in Lean" }])

#guard
  let r := ownSpecReports "proc p() {\n    cover a: true\n    cover b: true\n}\n" ownSpecExample.1 ownSpecExample.2
  (r.1.diags.map (·.line), r.2.diags.map (·.line)) == (#[2], #[2])

/-- Both front ends report the same messages about Fren's own requirements
(`cli::agreement`): Lean's, from a build of `Reqs` with its checks
(`lake -R -Kcheck_reqs=1 build Reqs`, `hostedOwnSpec`), and the binary's,
from `fren check` over `ownSpecFiles`, compared spec by spec as the
front-end fuzzer compares them (`FrenTest.Frontends.comparison`), without
the summaries, which Lean gives for each `#fren_check`, and without what
only the binary runs (`ownSpecReports`): its messages in an item that Lean
notes it leaves checks of to `fren check`, all of them. Run on `main` only,
by the `lean ci` workflow: `lake build` does not check `Reqs`, and `lake
test`'s `ownSpec` job checks them with the binary. -/
def ownSpecAgreement : IO (Array String) := do
  let (hosted, problems) ← hostedOwnSpec
  unless problems.isEmpty do return problems
  let (queryCache?, _) ← ownSpecCaches
  let (out, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files := ownSpecFiles, queryCache? })
  let mut failures := if code == 0 then #[] else #[s!"src/Reqs failed under the binary:\n{out}"]
  for f in ownSpecFiles do
    let text := Fren.Core.unwrapMarkdown (← IO.FS.readFile f)
    let (cli, lean) := ownSpecReports text (cliDiagnostics f out).1
      (hosted.filterMap fun (g, d) => if g == f then some d else none)
    for d in (FrenTest.Frontends.comparison text cli lean).found do
      failures := failures.push s!"{f}: {d}"
  -- Lean's messages about a spec that the binary does not check.
  for (g, d) in hosted do
    unless ownSpecFiles.contains g do
      failures := failures.push s!"{g}:{d.line}: Lean reports about a spec that `ownSpecFiles` lacks: {FrenTest.Frontends.headOf d}"
  return failures

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
   "test/cli/fmt/cover.fren", "test/cli/fmt/blocks.fren", "test/cli/fmt/comments.fren",
   "test/cli/fmt/generics.fren", "test/cli/fmt/generic_functions.fren", "test/cli/fmt/closures.fren",
   "test/cli/fmt/newtypes.fren",
   "test/cli/fmt/table.fren", "test/cli/fmt/subset_types.fren", "test/cli/fmt/subset_shorthand.fren",
   "test/cli/fmt/contract.fren",
   "test/cli/fmt/guards.fren", "test/cli/fmt/table_scrutinee.fren", "test/cli/fmt/lists.fren", "test/cli/fmt/commas.fren",
   "test/cli/fmt/independent.fren", "test/cli/fmt/right_sides.fren", "test/cli/fmt/blank_items.fren",
   "test/cli/commands/mutate_unformatted.fren", "test/ui/lints/unary_formatting.fren",
   "test/cli/lints/suspicious/f0762_suspicious_unary_op_formatting.fren", "test/ui/syntax/*.fren", "test/ui/lean/*.fren",
   "test/ui/checks/trace.fren",
   -- Markdown specs whose fences are deliberately wrong (`F0167`, `F0168`).
   "src/FrenTestFiles/LiterateUnclosed.md", "src/FrenTestFiles/LiterateNearFren.md",
   "src/FrenTestFiles/LiterateUnclosedProse.md", "src/FrenTestFiles/LiterateProseOuter.md",
   -- The explanations of the codes, whose first examples are erroneous.
   "src/FrenCore/Codes/*.md",
   -- The README's example keeps its hand-aligned continuation lines.
   "README.md",
   -- `#fren_md` in a block, which only the Lean front end reads.
   "src/FrenTestFiles/chapters/LiterateOuter.md", "src/FrenTestFiles/chapters/LiterateReader.md",
   "src/FrenTestFiles/chapters/deep/LiterateDeep.md", "src/FrenTestFiles/chapters/LiterateReplacing.md",
   -- Lean code in a block, likewise.
   "src/FrenTestFiles/chapters/LiterateNoPosition.md",
   -- Trailing commas that `unnecessary_trailing_comma` reports.
   "test/cli/lints/pedantic/f0801_unnecessary_trailing_comma.fren", "test/ui/lints/ranges_literals_commas.fren"]

/-- Test fixtures that `fren fmt` would lay out anew, as `--ignore` globs.
Their expected outputs and `--~` annotations name their lines, so
formatting them means updating those too. They are formatted a group at a
time, each only where the new layout reads better than the old, and this
list is then removed (#509). -/
def fmtPending : List String :=
  ["test/cli/commands/counterexample_newtype.fren",
   "test/ui/checks/recursion.fren", "test/ui/checks/recursion_bool_payload.fren",
   "test/ui/checks/subset_obligations.fren",
   "test/ui/lang/bool_members.fren", "test/ui/lang/cardinality.fren",
   "test/ui/lang/cardinality_static.fren", "test/ui/lang/chained_comparisons.fren",
   "test/ui/lang/checking_static.fren", "test/ui/lang/constants.fren",
   "test/ui/lang/constants_imported.fren", "test/ui/lang/constants_static.fren",
   "test/ui/lang/datatypes.fren", "test/ui/lang/datatypes_static.fren",
   "test/ui/lang/declared_types_static.fren", "test/ui/lang/defined_functions.fren",
   "test/ui/lang/defined_functions_static.fren", "test/ui/lang/defined_outputs.fren",
   "test/ui/lang/distinct_names_static.fren", "test/ui/lang/div_mod_static.fren",
   "test/ui/lang/empty_literals_static.fren", "test/ui/lang/functions_static.fren",
   "test/ui/lang/generic_functions.fren", "test/ui/lang/generic_functions_contracts.fren",
   "test/ui/lang/generic_functions_static.fren", "test/ui/lang/generics.fren",
   "test/ui/lang/generics_guards_contracts.fren", "test/ui/lang/generics_pattern_elements.fren",
   "test/ui/lang/generics_recursive_within.fren", "test/ui/lang/generics_static.fren",
   "test/ui/lang/generics_subset_types.fren", "test/ui/lang/global_static.fren",
   "test/ui/lang/guards.fren", "test/ui/lang/guards_static.fren",
   "test/ui/lang/higher_order_obligations.fren", "test/ui/lang/instances_static.fren",
   "test/ui/lang/lambda_match.fren", "test/ui/lang/lean_names.fren",
   "test/ui/lang/let.fren", "test/ui/lang/let_static.fren",
   "test/ui/lang/membership_static.fren", "test/ui/lang/mentions_static.fren",
   "test/ui/lang/multi_match_errors.fren", "test/ui/lang/nat.fren",
   "test/ui/lang/nat_fields.fren", "test/ui/lang/nat_static.fren",
   "test/ui/lang/nested_patterns.fren", "test/ui/lang/nested_patterns_static.fren",
   "test/ui/lang/newtypes.fren", "test/ui/lang/newtypes_static.fren",
   "test/ui/lang/or_patterns.fren", "test/ui/lang/or_patterns_static.fren",
   "test/ui/lang/ordered_enums_static.fren", "test/ui/lang/ordered_structs.fren",
   "test/ui/lang/ordered_structs_static.fren", "test/ui/lang/parameter_named_det.fren",
   "test/ui/lang/pattern_binders.fren", "test/ui/lang/pattern_binders_generic.fren",
   "test/ui/lang/pattern_binders_static.fren", "test/ui/lang/pattern_tests.fren",
   "test/ui/lang/pattern_tests_static.fren", "test/ui/lang/patterns_static.fren",
   "test/ui/lang/prelude.fren", "test/ui/lang/prelude_shadowing.fren",
   "test/ui/lang/quantifiers.fren", "test/ui/lang/quantifiers_elements.fren",
   "test/ui/lang/quantifiers_let.fren", "test/ui/lang/quantifiers_places.fren",
   "test/ui/lang/quantifiers_static.fren", "test/ui/lang/range_patterns.fren",
   "test/ui/lang/record_updates.fren", "test/ui/lang/record_updates_static.fren",
   "test/ui/lang/refines.fren", "test/ui/lang/refines_pattern.fren",
   "test/ui/lang/relations_static.fren", "test/ui/lang/scoping.fren",
   "test/ui/lang/sequences.fren", "test/ui/lang/sequences_static.fren",
   "test/ui/lang/shadowing.fren", "test/ui/lang/shadowing_static.fren",
   "test/ui/lang/strings_static.fren", "test/ui/lang/structural_recursion_static.fren",
   "test/ui/lang/subset_types.fren", "test/ui/lang/subset_types_meaning.fren",
   "test/ui/lang/tables.fren", "test/ui/lang/tables_scrutinee.fren",
   "test/ui/lang/tables_scrutinee_static.fren", "test/ui/lang/tables_static.fren",
   "test/ui/lang/type_facts.fren", "test/ui/lang/types.fren",
   "test/ui/lints/closures.fren", "test/ui/lints/methods.fren",
   "test/ui/lints/records.fren", "test/ui/lints/updates_covers.fren"]

/-- A file's pieces (`fmt::Piece`), each comment with whether it starts
its line, and the paths the `use` items import, sorted. With `all`, every
piece; otherwise, but for the trailing commas of lists and claims and for
`use` items. -/
def fmtPieces (path src : String) (all := false) : Option (List (FrenCli.Fmt.PieceKind × String) × Array (Array String)) := do
  let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
  let chars := src.toList.toArray
  let (toks, comments) ← (FrenCli.lexWithComments chars).toOption
  let lay ← (FrenCli.parseLayout toks chars).toOption
  let inUse (k : Nat) : Bool := lay.uses.any fun (f, l) => f ≤ k && k ≤ l
  let isStr (k : Nat) : Bool := toks[k]?.any (·.tok matches .str _)
  let startsLine (c : FrenCli.Span) : Bool := Id.run do
    let mut i := c.start
    while i > 0 && chars[i - 1]! != '\n' do
      if !chars[i - 1]!.isWhitespace then return false
      i := i - 1
    return true
  -- The tokens and comments, each with where it is and what it is.
  let mut pieces : Array (FrenCli.Span × FrenCli.Fmt.PieceKind × String) := #[]
  for h : k in [0:toks.size] do
    if inUse k && !all then continue
    let t := toks[k]
    let trailing := t.tok == .kw "," &&
      (toks[k + 1]?.any (fun n => n.tok == .kw "}" || n.tok == .kw ")" || n.tok == .kw "]") || (k > 0 && isStr (k - 1) && !isStr (k + 1)))
    if all || !trailing then
      pieces := pieces.push (t.span, if t.tok == .kw "," then .separator else .token, reprStr t.tok)
  for c in comments do
    let text := (FrenCli.Fmt.text chars c).trimAsciiEnd.toString
    let kind := FrenCli.Fmt.commentPiece (FrenCli.Fmt.isLineComment text) (startsLine c)
    pieces := pieces.push (c, kind, s!"{startsLine c} {text}")
  pieces := pieces.qsort fun a b => a.1.start < b.1.start
  -- With the line breaks between them.
  let mut stream : List (FrenCli.Fmt.PieceKind × String) := []
  let mut prev := 0
  for (span, kind, text) in pieces do
    if (chars.extract prev span.start).contains '\n' then stream := (.lineBreak, "") :: stream
    stream := (kind, text) :: stream
    prev := span.stop
  let paths := (lay.uses.flatMap fun (f, l) =>
    let (ps, glob) := FrenCli.Fmt.usePaths toks f l
    if glob then ps.map (·.push "*") else ps).qsort FrenCli.Fmt.pathLt
  return (stream.reverse, paths)

/-- What formatting keeps (`fmt::safe`): the order of the file's pieces
(`fmt::ordering`), in which a comma before a line break or a line comment
counts as one after it, and the paths the `use` items import. -/
def fmtKept (path src : String) : Option (Array String × Array (Array String)) := do
  let (stream, paths) ← fmtPieces path src
  return ((FrenCli.Fmt.keptOrder Prod.fst stream).toArray.map Prod.snd, paths)

/-- Whether no comma follows a line break or a line comment, of all the
file's pieces, trailing commas and `use` items included: whether placing
its commas (`fmt::separators`) changes nothing. That this is whether the
pieces are not `fmt::misplaced?` follows from `fmt::separators`'
`none_misplaced` and `placed_already`, which are tested at random. -/
def fmtCommasPlaced (path src : String) : Bool :=
  (fmtPieces path src (all := true)).any fun (stream, _) =>
    FrenCli.Fmt.placeSeparators Prod.fst stream == stream

/-- A token or comment of a file, for comparing blank lines: the token's
index, if it is one, its text, its first and last lines, whether it starts
its line, the blank lines between it and the piece kept before it, whether
a `use` item comes between them, and the piece just before it, kept or not. -/
structure BlankPiece where
  tok? : Option Nat
  text : String
  line : Nat
  endLine : Nat
  startsLine : Bool
  blank : Nat
  afterUse : Bool
  prev? : Option (Option Nat)
  deriving Inhabited

/-- The tokens and comments of Fren source, but its commas and the tokens
of its `use` items, which formatting moves or rewrites, with its tokens and
layout. -/
def blankPieces (src : String) : Option (Array BlankPiece × Array FrenCli.Token × FrenCli.Layout) := do
  let chars := src.toList.toArray
  let (toks, comments) ← (FrenCli.lexWithComments chars).toOption
  let lay ← (FrenCli.parseLayout toks chars).toOption
  let (lineOf, starts) := FrenCli.Fmt.lineTable chars
  let blankLine (l : Nat) : Bool :=
    (chars.extract starts[l]! ((starts[l + 1]?.map (· - 1)).getD chars.size)).all Char.isWhitespace
  let inUse (k : Nat) : Bool := lay.uses.any fun (f, l) => f ≤ k && k ≤ l
  let mut all : Array (FrenCli.Span × Option Nat) := #[]
  for k in [0:toks.size - 1] do all := all.push (toks[k]!.span, some k)
  for c in comments do all := all.push (c, none)
  all := all.qsort fun a b => a.1.start < b.1.start
  let mut out := #[]
  let mut lastKept : Option Nat := none
  let mut sawUse := false
  for h : i in [0:all.size] do
    let (s, tok?) := all[i]
    if tok?.any (fun k => inUse k || toks[k]!.tok == .kw ",") then
      if tok?.any inUse then sawUse := true
      continue
    let line := lineOf[s.start]!
    let blank := match lastKept with
      | some e => ((List.range (line - e - 1)).filter fun d => blankLine (e + 1 + d)).length
      | none => 0
    let startsLine := (chars.extract starts[line]! s.start).all Char.isWhitespace
    out := out.push { tok?, text := FrenCli.Fmt.text chars s, line, endLine := lineOf[s.stop - 1]!, startsLine, blank,
                      afterUse := sawUse, prev? := if i == 0 then none else some all[i - 1]!.2 }
    lastKept := some lineOf[s.stop - 1]!
    sawUse := false
  return (out, toks, lay)

/-- The blank lines before each line of `out`, formatted from `src`, in
`src`: before the token or comment that starts the line, as `blankPieces`
reads them, each by its line in `out`. -/
def sourceBlanks (src out : String) : Std.HashMap Nat Nat := Id.run do
  let some (ps, _, _) := blankPieces src | return {}
  let some (qs, _, _) := blankPieces out | return {}
  if ps.size != qs.size then return {}
  let mut m : Std.HashMap Nat Nat := {}
  for h : i in [0:qs.size] do
    if qs[i].startsLine then m := m.insert qs[i].line ps[i]!.blank
  return m

/-- The lines of Fren source `out`, as formatted, that `fmt::apart` sets
apart from the top-level item before them, computed from `out` and from
`blanks`, the blank lines before each of its lines in the source
(`sourceBlanks`): from the lines of each item's first and last tokens, the
lines between two items, each a `--~` annotation or not and with the
blank lines after it in the source, and the annotations on or below an
item's first line, before the next item, each with how many lines it is
below that line and how far it reaches. -/
def apartLines (out : String) (blanks : Std.HashMap Nat Nat) : Std.HashSet Nat := Id.run do
  let chars := out.toList.toArray
  let .ok (toks, comments) := FrenCli.lexWithComments chars | return {}
  let .ok lay := FrenCli.parseLayout toks chars | return {}
  let (lineOf, starts) := FrenCli.Fmt.lineTable chars
  let text (l : Nat) : String :=
    String.ofList (chars.extract starts[l]! ((starts[l + 1]?.map (· - 1)).getD chars.size)).toList
  let spans := lay.items.map fun (f, l) => (lineOf[toks[f]!.span.start]!, lineOf[toks[l]!.span.stop - 1]!)
  let annotations := comments.filterMap fun c =>
    (FrenCli.Fmt.annotationReach (FrenCli.Fmt.text chars c)).map (lineOf[c.start]!, ·)
  let mut apart : Std.HashSet Nat := {}
  for j in [1:spans.size] do
    let (pf, pl) := spans[j - 1]!
    let (f, l) := spans[j]!
    if pl ≥ f then continue
    -- The lines that are not blank between the two items, from the later
    -- one up, and what `fmt::apart` reads of each.
    let mut lines := #[f]
    let mut between := #[]
    let mut blankCount := 0
    for d in [1:f - pl] do
      let t := (text (f - d)).trimAscii
      if t.isEmpty then blankCount := blankCount + 1
      else
        between := between.push (t.startsWith "--~", blanks.getD lines.back! blankCount)
        lines := lines.push (f - d)
        blankCount := 0
    let stop? := spans[j + 1]?.map (·.1)
    let below := annotations.toList.filterMap fun (line, r) =>
      if line ≥ f && stop?.all (line < ·) then some (line - f, r) else none
    for h : a in [0:lines.size] do
      if FrenCli.Fmt.apart a between.toList below pf pl f l then apart := apart.insert lines[a]
  return apart

/-- Where formatting `src` as `out` loses or adds a blank line: before each
token or comment that starts a line of `out`, the blank lines are those
that `fmt::blank_lines` keeps of `src`'s, with whether `fmt::apart` sets
the line apart, computed from the lines of `out` and the blank lines of
`src` (`apartLines`); and a token or comment after a
blank line of `src` that does not start a line of `out` is after a gap
whose line break a list or block decides and whose blank lines go
(`fmt::line_break`): after an opening bracket, a record update's `{` or
`with`, before a closing bracket, before a block's `{`, or before the right
side of a `:=` or `=>` (`fmt::right_side`). Pieces after a
`use` item are left out, as imports are merged and sorted. -/
def fmtBlanksKept (src out : String) : Array String := Id.run do
  let some (ps, _, lay) := blankPieces src | return #[]
  let some (qs, toks', lay') := blankPieces out | return #[]
  if ps.size != qs.size then return #["formatting changes its tokens and comments"]
  -- Gaps of `src` whose blank lines go where a list or block joins them.
  let mut joinable : Std.HashSet Nat := {}
  for b in lay.bracketed do
    if b.kind == .members then joinable := joinable.insert b.opening
    joinable := (joinable.insert (b.lead + 1)).insert b.closing
    if b.lead != b.opening then joinable := joinable.insert (b.opening + 1)
  -- And the gap before each right side of a `:=` or `=>` (`fmt::right_side`).
  for (_, first, _, _) in lay.rightSides do joinable := joinable.insert first
  -- Tokens of `out` after which a line has no blank line after it, and
  -- the closing brackets of those that indent.
  let mut opens : Std.HashSet Nat := {}
  for b in lay'.bracketed do opens := (opens.insert b.opening).insert b.lead
  -- A `:=` or `=>` that ends a line is followed by its right side.
  for (op, _, _, _) in lay'.rightSides do opens := opens.insert op
  for h : k in [0:toks'.size] do
    if toks'[k].tok == .kw "{" || toks'[k].tok == .kw "::{" then opens := opens.insert k
  let mut closes : Std.HashSet Nat := {}
  let mut unclosed : Array Nat := #[]
  for h : k in [0:toks'.size] do
    match toks'[k].tok with
    | .kw "(" | .kw "[" | .kw "{" | .kw "::{" => unclosed := unclosed.push k
    | .kw ")" | .kw "]" | .kw "}" =>
      if let some o := unclosed.back? then
        if toks'[o]!.tok == .kw "{" || toks'[o]!.tok == .kw "::{" || lay'.bracketed.any (·.opening == o) then
          closes := closes.insert k
        unclosed := unclosed.pop
    | _ => pure ()
  let apart := apartLines out (sourceBlanks src out)
  let mut failures := #[]
  for h : i in [1:ps.size] do
    let p := ps[i]!
    let q := qs[i]!
    if p.text != q.text then return #["formatting changes its tokens and comments"]
    if p.afterUse || q.afterUse then continue
    if q.startsLine then
      let afterOpen := q.prev?.any (·.any opens.contains)
      let beforeClose := q.tok?.any closes.contains
      let kept := FrenCli.Fmt.blankLines p.blank false afterOpen beforeClose (apart.contains q.line)
      if q.blank != kept then
        failures := failures.push s!"{q.blank} blank lines before `{q.text}` (line {q.endLine + 1}), where `fmt::blank_lines` keeps {kept} of {p.blank}"
    else if p.blank > 0 && !p.tok?.any joinable.contains then
      failures := failures.push s!"a blank line before `{p.text}` (line {p.endLine + 1}) is lost, as its line is joined"
  return failures

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
inconclusive but a pass that rests on a check that did not pass, such as
an expectation of a procedure whose assumptions contradict each other
(`F0664`, `Reqs/Evidence`). -/
def conformance (name : String) (corpus : Nat → String) : IO (Array String) := do
  IO.FS.createDirAll (".lake" / "corpus")
  let file := s!".lake/corpus/{name}.fren"
  IO.FS.writeFile file (corpus 40)
  let (out, _) ← runFren ["check", file]
  let resting := (out.splitOn "warning[F0664]").length - 1
  if out.contains "could not check".toSlice || !out.contains s!" {resting} inconclusive".toSlice then
    return #[s!"the {name} corpus ({file}) is not decided:\n{out}"]
  return #[]

/-- `src` laid out again at random, from `seed`, as `fmt::layout_free`
allows: each gap whose line break a list or block decides, or that before
the right side of a `:=` or `=>` (`fmt::right_side`) but a chain broken by
hand, with no comment in it and none on its lines, is laid out again. One whose blank lines go
(`fmt::line_break`, `fmt::blank_lines`: after an opening bracket, a record
update's `{` or `with`, before a closing bracket, before a block's `{`, or
before a right side)
gets a space, a line break or a blank line, whatever it had; one between
two elements or members gets a space or a line break if it has no blank
line, and otherwise keeps its blank lines, with spaces on them at random.
The trailing comma of a list that may end with one, on a line without a
comment, is dropped or added; a comma that a line comment follows on its
line may move to a line of its own after the comment, a space taking its
place, and one in a list, on a line without a comment, may start the next
line, as the line break before a comma is not content (`fmt::separators`);
each gap of one or more spaces between two tokens on a line without a
comment gets 1 to 3 spaces; and then each line without a comment, and not
inside a token, is indented by 0 to 12 spaces. `none` if `src` does not
parse.

The gap before each token of `apart`, which starts a line that
`fmt::apart` sets apart from the top-level item before it, so that its
blank lines are not content, with no comment in it and none on its lines,
gets a line break or a blank line, whatever it had.

It leaves alone what is content (`fmt::safe`), and some of what is not:
the gaps and indentation of lines with comments, and gaps with no space,
where one could change what the parser reads, as in `f(x)` or `0..=9`. -/
def relaid (src : String) (seed : Nat) (apart : Std.HashSet Nat := {}) : Option String := do
  let chars := src.toList.toArray
  let (toks, comments) ← (FrenCli.lexWithComments chars).toOption
  let lay ← (FrenCli.parseLayout toks chars).toOption
  let (lineOf, _) := FrenCli.Fmt.lineTable chars
  let mut commented : Std.HashSet Nat := {}
  for c in comments do
    for l in [lineOf[c.start]!:lineOf[c.stop - 1]! + 1] do commented := commented.insert l
  let mut rng := seed
  -- Edits: a span of `chars` and its replacement, an insertion first.
  let mut edits : Array (Nat × Nat × String) := #[]
  let mut seen : Std.HashSet Nat := {}
  for b in lay.bracketed do
    -- The gaps, each with whether its blank lines go.
    let mut gaps : Array (Nat × Nat × Bool) := #[]
    if b.kind == .members && b.opening > 0 then gaps := gaps.push (b.opening - 1, b.opening, true)
    if b.closing != b.opening + 1 then
      gaps := gaps ++ #[(b.lead, b.lead + 1, true), (b.closing - 1, b.closing, true)]
      if b.lead != b.opening then gaps := gaps.push (b.opening, b.opening + 1, true)
      for k in b.commas do
        if k + 1 != b.closing then gaps := gaps.push (k, k + 1, false)
    for (a, c, goes) in gaps do
      let start := toks[a]!.span.stop
      let stop := toks[c]!.span.start
      let between := chars.extract start stop
      if seen.contains start || !between.all Char.isWhitespace then continue
      if commented.contains lineOf[start]! || commented.contains lineOf[stop]! then continue
      seen := seen.insert start
      rng := (rng * 1103515245 + 12345) % 2147483648
      let pick := (rng / 65536) % 3
      let breaks := between.count '\n'
      let gap := if goes then (if pick == 0 then " " else if pick == 1 then "\n" else "\n\n")
        else if breaks > 1 then
          (List.range (breaks - 1)).foldl (fun acc d => acc.pushn ' ' ((pick + d) % 3) ++ "\n") "\n"
        else if pick == 0 then " " else "\n"
      edits := edits.push (start, stop, gap)
    if b.closing == b.opening + 1 then continue
    -- The trailing comma, where the syntax allows one.
    if FrenCli.Fmt.endsWithComma b.kind && !commented.contains lineOf[toks[b.closing - 1]!.span.start]! then
      rng := (rng * 1103515245 + 12345) % 2147483648
      if (rng / 65536) % 2 == 0 then
        let last := b.closing - 1
        if b.commas.back? == some last then edits := edits.push (toks[last]!.span.start, toks[last]!.span.stop, "")
        else edits := edits.push (toks[last]!.span.stop, toks[last]!.span.stop, ",")
  -- The gap before the right side of each `:=` and `=>`, whose blank lines
  -- go (`fmt::right_side`): a space, a line break or a blank line. But for
  -- a chain broken by hand, with a line break outside its brackets, whose
  -- gap is content.
  let firsts : Std.HashSet Nat := lay.rightSides.foldl (fun acc (_, f, _, _) => acc.insert f) {}
  for (op, first, last, _) in lay.rightSides do
    let mut depth : Int := 0
    let mut chained := false
    for k in [first:last + 1] do
      if depth == 0 && k > first && !firsts.contains k
          && lineOf[toks[k]!.span.start]! > lineOf[toks[k - 1]!.span.stop - 1]! then
        chained := true
      match toks[k]!.tok with
      | .kw "(" | .kw "[" | .kw "{" | .kw "::{" => depth := depth + 1
      | .kw ")" | .kw "]" | .kw "}" => depth := depth - 1
      | _ => pure ()
    if chained then continue
    let start := toks[op]!.span.stop
    let stop := toks[first]!.span.start
    if seen.contains start || !(chars.extract start stop).all Char.isWhitespace then continue
    if commented.contains lineOf[start]! || commented.contains lineOf[stop]! then continue
    seen := seen.insert start
    rng := (rng * 1103515245 + 12345) % 2147483648
    let pick := (rng / 65536) % 3
    edits := edits.push (start, stop, if pick == 0 then " " else if pick == 1 then "\n" else "\n\n")
  -- The gap before a line that `fmt::apart` sets apart: a line break or a
  -- blank line.
  for k in apart.toArray.qsort (· < ·) do
    if k == 0 then continue
    let start := toks[k - 1]!.span.stop
    let stop := toks[k]!.span.start
    if seen.contains start || !(chars.extract start stop).all Char.isWhitespace then continue
    if commented.contains lineOf[start]! || commented.contains lineOf[stop]! then continue
    seen := seen.insert start
    rng := (rng * 1103515245 + 12345) % 2147483648
    edits := edits.push (start, stop, if (rng / 65536) % 2 == 0 then "\n" else "\n\n")
  -- Commas, on the next line (`fmt::separators`).
  let mut listCommas : Std.HashSet Nat := {}
  for b in lay.bracketed do
    for k in b.commas do listCommas := listCommas.insert k
  for h : k in [1:toks.size] do
    if toks[k].tok != .kw "," then continue
    let start := toks[k - 1]!.span.stop
    let stop := toks[k].span.start
    if !(chars.extract start stop).all (· == ' ') then continue
    rng := (rng * 1103515245 + 12345) % 2147483648
    if (rng / 65536) % 2 != 0 then continue
    -- The comment after it on its line, if any.
    let after := toks[k].span.stop
    match comments.find? fun c => c.start ≥ after && lineOf[c.start]! == lineOf[after - 1]! with
    | some c =>
      -- A line comment, with only spaces before it: the comma goes on a
      -- line of its own after it.
      if (chars.extract after c.start).all (· == ' ') && FrenCli.Fmt.isLineComment (FrenCli.Fmt.text chars c) then
        edits := edits.push (stop, after, " ")
        edits := edits.push (c.stop, c.stop, "\n,")
    | none =>
      -- Where a list decides the line break that follows the comma.
      if listCommas.contains k && !commented.contains lineOf[start]! then edits := edits.push (start, stop, "\n")
  let sortedEdits := edits.qsort fun (a, b, _) (c, d, _) => a < c || (a == c && b - a < d - c)
  let mut out := ""
  let mut pos := 0
  for (start, stop, r) in sortedEdits do
    out := out ++ String.ofList (chars.extract pos start).toList ++ r
    pos := stop
  out := out ++ String.ofList (chars.extract pos chars.size).toList
  -- Indentation, at random, on the lines that it cannot change.
  let chars' := out.toList.toArray
  let (toks', comments') ← (FrenCli.lexWithComments chars').toOption
  let (lineOf', starts) := FrenCli.Fmt.lineTable chars'
  let mut fixed : Std.HashSet Nat := {}
  for c in comments' do
    for l in [lineOf'[c.start]!:lineOf'[c.stop - 1]! + 1] do fixed := fixed.insert l
  for t in toks' do
    if t.span.stop > t.span.start then
      for l in [lineOf'[t.span.start]! + 1:lineOf'[t.span.stop - 1]! + 1] do fixed := fixed.insert l
  -- Spaces between tokens, at random, where there are some, on a line without a comment.
  let mut spaced := ""
  let mut upTo := 0
  for k in [1:toks'.size] do
    let start := toks'[k - 1]!.span.stop
    let stop := toks'[k]!.span.start
    if start >= stop || fixed.contains lineOf'[start]! then continue
    if !(chars'.extract start stop).all (· == ' ') then continue
    rng := (rng * 1103515245 + 12345) % 2147483648
    spaced := spaced ++ String.ofList (chars'.extract upTo start).toList |>.pushn ' ' (1 + (rng / 65536) % 3)
    upTo := stop
  out := spaced ++ String.ofList (chars'.extract upTo chars'.size).toList
  let lines := (out.splitOn "\n").toArray
  let mut result := #[]
  for h : l in [0:lines.size] do
    let line := lines[l]
    if fixed.contains l || starts[l]?.isNone then result := result.push line; continue
    rng := (rng * 1103515245 + 12345) % 2147483648
    let body := line.trimAsciiStart.toString
    result := result.push (if body.isEmpty then line else "".pushn ' ' ((rng / 65536) % 13) ++ body)
  return "\n".intercalate result.toList

/-- The tokens of `src` that start a line that `fmt::apart` sets apart in
`formatted`, what formatting writes for it (`apartLines`). -/
def apartTokens (src formatted : String) : Std.HashSet Nat := Id.run do
  let some (ps, _, _) := blankPieces src | return {}
  let some (qs, _, _) := blankPieces formatted | return {}
  if ps.size != qs.size then return {}
  let apart := apartLines formatted (sourceBlanks src formatted)
  let mut toks : Std.HashSet Nat := {}
  for h : i in [0:qs.size] do
    if qs[i].startsLine && apart.contains qs[i].line then
      if let some k := ps[i]!.tok? then toks := toks.insert k
  return toks

/-- `fmt::safe` and `fmt::layout_free` over every spec in the repository,
and over each laid out again at random, twice: formatting keeps its
tokens and comments in order and its imports, leaves no comma after a
line break or a line comment, formatting it again changes nothing, and
laying it out again changes nothing that formatting writes. And every
spec that parses is formatted. -/
def formatting : IO (Array String) := do
  let mut failures := #[]
  let mut relaidSome := false
  for f in ← specFiles do
    let src ← IO.FS.readFile f
    let .ok new := FrenCli.Fmt.formatFile f src | continue
    if fmtKept f src != fmtKept f new then
      failures := failures.push s!"{f}: formatting changes its tokens and comments, their order, or its imports"
    if !fmtCommasPlaced f new then
      failures := failures.push s!"{f}: formatting leaves a comma after a line break or a line comment"
    if (FrenCli.Fmt.formatFile f new).toOption != some new then
      failures := failures.push s!"{f}: formatting it twice changes it again"
    -- Its Fren source, laid out again.
    let code := FrenCli.Fmt.parsedText f src
    let .ok formatted := FrenCli.Fmt.formatFren code | continue
    for d in fmtBlanksKept code formatted do failures := failures.push s!"{f}: {d}"
    let apart := apartTokens code formatted
    for seed in [1, 2] do
      let some other := relaid code (seed * 7919 + f.length) apart | failures := failures.push s!"{f}: laid out again, it does not parse"; continue
      if other != code then relaidSome := true
      match FrenCli.Fmt.formatFren other with
      | .error _ => failures := failures.push s!"{f}: laid out again, it does not parse"
      | .ok again =>
        for d in fmtBlanksKept other again do failures := failures.push s!"{f}: laid out again (seed {seed}), {d}"
        if fmtKept "x.fren" other != fmtKept "x.fren" again then
          failures := failures.push s!"{f}: laid out again, formatting changes its tokens and comments, their order, or its imports"
        if !fmtCommasPlaced "x.fren" again then
          failures := failures.push s!"{f}: laid out again, formatting leaves a comma after a line break or a line comment"
        if again != formatted then
          failures := failures.push s!"{f}: laid out again (seed {seed}), it formats differently:\n{FrenCli.Fmt.diff {} f formatted again}"
        if (FrenCli.Fmt.formatFren again).toOption != some again then
          failures := failures.push s!"{f}: laid out again, formatting it twice changes it again"
  if !relaidSome then failures := failures.push "laying out the specs again at random changes none of them"
  -- The check of blank lines catches one between a comment and the item it
  -- documents, which `fmt::apart` puts above the comment.
  let tall := "proc tall(m: Mode): (on?) {\n    ensure r: on? iff m = Mode::Heat\n    ensure s: on?\n}\n"
  let documented (before after : String) := s!"enum Mode \{ Heat, Cool }\n{before}-- doc\n{after}{tall}"
  if !(fmtBlanksKept (documented "" "") (documented "\n" "")).isEmpty then
    failures := failures.push "the check of blank lines rejects a blank line above a doc comment"
  if (fmtBlanksKept (documented "" "") (documented "" "\n")).isEmpty then
    failures := failures.push "the check of blank lines misses a blank line between a doc comment and its item"
  -- Every other spec is formatted, as `fren fmt --check` says.
  let ignore := (fmtIgnore ++ fmtPending).flatMap (["--ignore", ·])
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
    (["Reqs.Lint"], fun p => p == "Lint.md" || p.startsWith "Lint/"),
    (["Reqs.Testing"], (·.startsWith "dev/"))]

/-- The modules of Impls whose library needs the tests, `ImplsTested` in
`lakefile.lean` (`libraryModules`). -/
def testReaders : List String := ["src/Impls/Evidence.lean", "src/Impls/Lint.lean", "src/Impls/Trace.lean"]

/-- The relative path `p` without its `.` and `..` components, where it can
drop them. -/
def normalPath (p : String) : String :=
  let parts := (p.splitOn "/").foldl (init := (#[] : Array String)) fun acc c =>
    if c == "." || c.isEmpty then acc
    else if c == ".." && !acc.isEmpty && acc.back! != ".." then acc.pop
    else acc.push c
  "/".intercalate parts.toList

#guard normalPath "src/FrenTestFiles/./chapters/../../../test/ui/x.fren" == "test/ui/x.fren"
#guard normalPath "src/../../x.md" == "../x.md"

/-- The source file of module `m`. -/
def sourceOf (m : String) : System.FilePath := "src" / ((m.replace "." "/") ++ ".lean")

/-- The declarations of kind `kind` in `lakefile.lean` (`lean_lib`,
`input_dir`, `input_file`), each as its name and its text: its line and
the indented lines after it. -/
def lakeDecls (kind : String) : IO (Array (String × String)) := do
  let mut out := #[]
  let mut cur : Option (String × String) := none
  for line in (← IO.FS.readFile "lakefile.lean").splitOn "\n" do
    if line.startsWith " " then
      cur := cur.map fun (n, t) => (n, t ++ "\n" ++ line)
      continue
    if let some c := cur then out := out.push c
    let decl := ((line.dropPrefix? "@[default_target] ").map (·.toString)).getD line
    cur := (decl.dropPrefix? s!"{kind} ").map fun rest => ((rest.toString.splitOn " ").headD "", decl)
  if let some c := cur then out := out.push c
  return out

/-- The items of the field `field := #[…]` of the declaration text `decl`,
each trimmed. -/
def lakeArray (decl field : String) : Option (List String) := do
  let after ← (decl.splitOn s!"{field} := #[")[1]?
  return ((after.splitOn "]").headD "").splitOn "," |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- The string of the field `field := "…"` of the declaration text `decl`. -/
def lakeString (decl field : String) : Option String := do
  (← (decl.splitOn s!"{field} := \"")[1]?).splitOn "\"" |>.head?

/-- A glob of a `lean_lib`, as the module, and whether it selects the
module itself and its submodules. -/
def parseGlob (g : String) : Option (String × Bool × Bool) :=
  let name (s : String) : String := (s.dropPrefix "`").toString
  if let some m := g.dropPrefix? ".one " then some (name m.toString, true, false)
  else if let some m := g.dropPrefix? ".submodules " then some (name m.toString, false, true)
  else if let some m := g.dropPrefix? ".andSubmodules " then some (name m.toString, true, true)
  else if !g.startsWith "`" then none
  else if let some m := g.dropSuffix? ".+" then some (name m.toString, false, true)
  else if let some m := g.dropSuffix? ".*" then some (name m.toString, true, true)
  else some (name g, true, false)

#guard parseGlob "`FrenTestFiles.+" == some ("FrenTestFiles", false, true)
#guard parseGlob ".andSubmodules `FrenCore" == some ("FrenCore", true, true)
#guard parseGlob "`Impls.Lint" == some ("Impls.Lint", true, false)

/-- The modules in the globs of the library `lib`, whose declaration in
`lakefile.lean` is `decl`, each as its name and source file: those it
builds with its own configuration, whatever imports them. Without
`globs`, its roots, which are by default `lib`. -/
def libraryModules (lib decl : String) : IO (Except String (Array (String × String))) := do
  let dir : System.FilePath := match lakeString decl "srcDir" with
    | some d => "src" / d
    | none => "src"
  let globs := (lakeArray decl "globs").getD (((lakeArray decl "roots").getD [s!"`{lib}"]).map (".one " ++ ·))
  let mut mods := #[]
  for g in globs do
    let some (m, self, subs) := parseGlob g
      | return .error s!"lakefile.lean: `{lib}` has the glob `{g}`, which `lake test`'s `libraries` job cannot read"
    let path := m.replace "." "/"
    if self then mods := mods.push (m, (dir / (path ++ ".lean")).toString)
    if subs && (← (dir / path).isDir) then
      for f in ← (dir / path).walkDir do
        if f.extension != some "lean" then continue
        let some rel := (f.withExtension "").toString.dropPrefix? (dir.toString ++ "/") | continue
        mods := mods.push (rel.toString.replace "/" ".", f.toString)
  return .ok mods

/-- Whether the library declaration `decl` of `lakefile.lean` needs the
file `p`, a path from the repository's root, by its `needs`: an
`input_file` of `p`, or an `input_dir` that holds `p` and whose filter
takes it. -/
def lakeNeeds (decl : String) : IO (Except String (String → Bool)) := do
  let files ← lakeDecls "input_file"
  let dirs ← lakeDecls "input_dir"
  let mut needed : Array (String → Bool) := #[]
  for n in (lakeArray decl "needs").getD [] do
    let name := (n.dropPrefix "`@/").toString
    let cannot := s!"lakefile.lean: `lake test`'s `libraries` job cannot read the input `{name}`"
    if let some (_, d) := files.find? (·.1 == name) then
      let some path := lakeString d "path" | return .error cannot
      needed := needed.push (· == path)
    else if let some (_, d) := dirs.find? (·.1 == name) then
      let some path := lakeString d "path" | return .error cannot
      let filter := (((d.splitOn "filter := ")[1]?.bind (·.splitOn "\n" |>.head?)).getD "").trimAscii.toString
      let inDir (p : String) := p.startsWith (path ++ "/")
      if filter == ".star" then needed := needed.push inDir
      else if let some exts := filter.dropPrefix? ".extension #[" then
        let exts := ((exts.toString.splitOn "]").headD "").splitOn "," |>.map fun e =>
          ((e.trimAscii.toString.dropPrefix "\"").dropSuffix "\"").toString
        needed := needed.push fun p => inDir p && exts.any (some · == (System.FilePath.mk p).extension)
      else return .error cannot
    else return .error cannot
  return .ok fun p => needed.any (· p)

/-- The modules that `m` imports. -/
def importsOf (m : String) : IO (Array String) := do
  let path := sourceOf m
  let header ← Lean.parseImports' (← IO.FS.readFile path) path.toString
  return header.imports.map (·.module.toString)

/-- The files that the `#fren_md` commands of the source `src` read,
wherever the command is on its line. -/
def specsOf (src : String) : Array String :=
  (src.splitOn "#fren_md \"").toArray.extract 1 |>.map fun rest => (rest.splitOn "\"").headD ""

#guard specsOf "#fren_md \"a.md\"\n#guard_msgs in #fren_md \"b.md\"\n  #fren_md \"c/d.md\"\n" == #["a.md", "b.md", "c/d.md"]
#guard specsOf "-- `#fren_md` with no file\n" == #[]

/-- The default targets of the lakefile `lakefile`: the names of its
`lean_lib`s and `lean_exe`s marked `@[default_target]`, the attribute on
the declaration's line or on a line of its own before it; or, as an
error, the first `@[default_target]` that it cannot read, so that no
default target is missed. -/
def defaultTargets (lakefile : String) : Except String (Array String) := do
  let lines := (lakefile.splitOn "\n").toArray
  let mut out := #[]
  for i in [0:lines.size] do
    let line := lines[i]!.trimAscii.toString
    unless line.startsWith "@[default_target]" do continue
    let after := (line.drop "@[default_target]".length).trimAscii.toString
    let decl := if after.isEmpty then ((lines[i + 1]?).getD "").trimAscii.toString else after
    let rest := (decl.dropPrefix? "lean_lib ").orElse fun _ => decl.dropPrefix? "lean_exe "
    let name := (rest.bind fun r => (r.toString.splitOn " ").head?).getD ""
    unless !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') do
      throw s!"lakefile.lean:{i + 1}: `lake test`'s `libraries` job cannot read the default target `{line}`"
    out := out.push name
  return out

#guard defaultTargets "@[default_target] lean_lib A where\n  x := 1\nlean_lib B\n@[default_target] lean_exe c where\n" == .ok #["A", "c"]
#guard defaultTargets "@[default_target]\nlean_lib A where\n" == .ok #["A"]
#guard (defaultTargets "@[default_target] lean_lib «a b» where\n" matches .error _)
#guard (defaultTargets "@[default_target] target x where\n" matches .error _)

/-- The targets that the job `build` of the workflow `workflow` builds in
its matrix: the names after each `targets:` from the job's line to the
next job's (a line indented by two spaces). -/
def matrixTargets (workflow : String) : Array String := Id.run do
  let mut out := #[]
  let mut inBuild := false
  for line in workflow.splitOn "\n" do
    if line.startsWith "  " && !line.startsWith "   " && !line.startsWith "  #" then
      inBuild := line == "  build:"
    else if inBuild then
      if let some rest := line.trimAscii.toString.dropPrefix? "targets: " then
        out := out ++ (rest.toString.splitOn " ").toArray.filter (!·.isEmpty)
  return out

#guard matrixTargets "jobs:\n  build:\n    strategy:\n      matrix:\n        - part: a\n          targets: A B\n        - part: b\n          targets: c\n  test:\n    targets: D\n" == #["A", "B", "c"]

/-- Each copy of a root's imports is the root's; no module is in the globs
of two libraries; each module of Reqs reads only the specs that its
library needs; only modules whose library needs the tests make `tested`
claims; and only the tests whose library needs the files that they read,
`FrenTestFiles`, read files with `#fren_md`; and `pre-merge`'s build
jobs together build exactly the default targets. -/
def libraries : IO (Array String) := do
  let mut failures := #[]
  -- `lake build --wfail` runs on two machines, each building some of the
  -- default targets, so that a new one would otherwise go unbuilt.
  let built := ((matrixTargets (← IO.FS.readFile ".github/workflows/pre-merge.yml")).qsort (· < ·)).toList.eraseDups.toArray
  match defaultTargets (← IO.FS.readFile "lakefile.lean") with
  | .error e => failures := failures.push e
  | .ok ts =>
    let want := ts.qsort (· < ·)
    if want != built then
      failures := failures.push s!".github/workflows/pre-merge.yml: its build jobs build {built.toList}, but the default targets of `lakefile.lean` are {want.toList}"
  for (root, copies) in rootCopies do
    let ofRoot (ms : Array String) := (ms.filter (·.startsWith s!"{root}.")).qsort (· < ·)
    let want := ofRoot (← importsOf root)
    for m in copies do
      let got := ofRoot (← importsOf m)
      if got != want then
        failures := failures.push s!"{sourceOf m}: imports {got.toList} of `{root}`'s modules, not `{root}`'s {want.toList}"
  -- A library builds each module of its globs with its own `needs`, even if
  -- another library has it too; only a module that a build reaches by an
  -- import alone is built in the last library that has it. So a module in
  -- the globs of two libraries is built with either's `needs`, by which
  -- library the build reaches it through first, and editing a file that
  -- the other needs may not rebuild it.
  let libs ← lakeDecls "lean_lib"
  let mut owners : Array (String × String) := #[]
  let mut modulesOf : Array (String × Array String) := #[]
  for (lib, decl) in libs do
    match ← libraryModules lib decl with
    | .error e => failures := failures.push e
    | .ok mods =>
      modulesOf := modulesOf.push (lib, mods.map (·.2))
      for (m, _) in mods do
        if let some (_, other) := owners.find? (·.1 == m) then
          failures := failures.push s!"lakefile.lean: `{m}` is in the globs of both `{other}` and `{lib}`, which build it with their own `needs`"
        else owners := owners.push (m, lib)
  let modulesOfLib (lib : String) : Array String := ((modulesOf.find? (·.1 == lib)).map (·.2)).getD #[]
  for (mods, ok) in specsRead do
    for m in mods do
      for spec in specsOf (← IO.FS.readFile (sourceOf m)) do
        unless ok spec do
          failures := failures.push s!"{sourceOf m}: reads `{spec}`, which its library in `lakefile.lean` does not need"
  let tested := modulesOfLib "ImplsTested"
  unless tested.qsort (· < ·) == testReaders.toArray.qsort (· < ·) do
    failures := failures.push s!"lakefile.lean: `ImplsTested` holds {tested}, but `testReaders` in src/FrenTestMain.lean is {testReaders}"
  for f in (← System.FilePath.walkDir "src/Impls").push "src/Impls.lean" do
    if f.extension != some "lean" || testReaders.contains f.toString then continue
    if (← IO.FS.readFile f).splitOn "\n" |>.any (·.startsWith "tested ") then
      failures := failures.push s!"{f}: makes a `tested` claim, but its library in `lakefile.lean` does not need the tests"
  -- A test outside `FrenTestFiles` is in `FrenTest`, which needs no file,
  -- so that editing one that it read would not rebuild it.
  let readers := modulesOfLib "FrenTestFiles"
  for f in (← System.FilePath.walkDir "src/FrenTest") ++ (← System.FilePath.walkDir "src/FrenTestFiles") do
    if f.extension != some "lean" || readers.contains f.toString then continue
    for file in specsOf (← IO.FS.readFile f) do
      failures := failures.push s!"{f}: reads `{file}`, but its library in `lakefile.lean` is not `FrenTestFiles`, which needs the files that tests read"
  -- The files that `FrenTestFiles` reads, and those that they read with
  -- their own `#fren_md`, relative to themselves, must be ones that it needs.
  match ← lakeNeeds (((libs.find? (·.1 == "FrenTestFiles")).map (·.2)).getD "") with
  | .error e => failures := failures.push e
  | .ok needed =>
    let mut todo := readers
    let mut seen := readers
    while !todo.isEmpty do
      let f := todo.back!
      todo := todo.pop
      for file in specsOf (← IO.FS.readFile f) do
        let path := if file.startsWith "/" then file else normalPath (((System.FilePath.mk f).parent.getD "" / file).toString)
        unless needed path do
          failures := failures.push s!"{f}: reads `{file}`, which `FrenTestFiles` in `lakefile.lean` does not need"
        if !seen.contains path && (← System.FilePath.pathExists path) then
          seen := seen.push path
          todo := todo.push path
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
def mutationSlices : Nat := 64

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
    -- One mutant in 16: `mutantState`, which elaborates again only the
    -- files after it that it must, reads as elaborating all of them again.
    -- Slice `s` takes the `s % 16`th of each 16 of its mutants, so that
    -- those taken are spread over the files, not in blocks of neighbours.
    if (i / slices) % 16 == slice % 16 then
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
    fun m (k, r, _) => m.insert k ((m.getD k #[]).push r)
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
changes a type alias or a subset type that it uses (`FrenCli.skipFile?`):
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
  let .ok sp := FrenCli.specOf files st.callTargs | return (#[], 0)
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
        -- As `methodsAgree` compares them, with no verdict of random testing.
        if Fren.Core.methodsContradict r.kind s.verdict r.verdict r.bounded?.isSome .inconclusive then
          let bounded := if r.bounded?.isSome then " up to the bound" else ""
          failures := failures.push s!"{f}: `{item}` {k}: enumeration {repr r.verdict}{bounded}, but the solver {repr s.verdict}"
    -- A value given where a subset type is declared stays the solver's
    -- (`check::by_evidence`): its result is not dropped.
    for (item, ss) in solver do
      for (k, s) in ss do
        unless s.kind == .definedness && s.subsetTy?.isSome do continue
        let same := ((enumerated.getD item #[]).find? (·.1 == k)).any (·.2.verdict == s.verdict)
        unless same do failures := failures.push s!"{f}: `{item}` {k}: the solver's obligation is missing with enumeration"
  return if compared < 500 then failures.push s!"enumeration: only {compared} checks compared" else failures

/-! ## Methods agree

Every check of Fren's own requirements, of the ui tests and of the
front-end fuzzer's corpus runs under each method that applies, the solver,
enumeration up to the size and random testing, each set by `fren check
--evidence`, in place of the specs' own settings; and no two methods'
verdicts on a check contradict each other (`check::methods_agree`). Model
confirmation checks every counterexample and witness that the solver
reports (`Reqs/Models`); this checks the other direction, a pass that rests
on the solver's `unsat` alone, which a wrong encoding can make of a false
claim. On `main` only (`methods-agree` in `ci.yml`). -/

/-- The methods that `methodsAgree` compares, each with the value of
`fren check --evidence` that sets it. -/
def comparedMethods : Array (Fren.Core.ProofMethod × String) :=
  #[(.solver, "solver"), (.enumerated, "enumerated"), (.random, "random")]

/-- A check's key across runs of the same files: its item's, and every
field that tells it from the item's other checks. -/
def methodKey (item : String) (r : Fren.Core.CheckResult) : String :=
  let goal := match r.goal? with | some g => s!"{repr g}" | none => "-"
  s!"{item}|{repr r.kind}|{r.prop?}|{r.target?}|{r.index?}|{r.site?}|{r.rows?}|{goal}|{r.subsetTy?}"

/-- What a method reached on a check: its verdict, whether a pass holds
only up to the size, and what it reported, as text. -/
structure MethodFound where
  kind : Fren.Core.CheckKind
  verdict : Fren.Core.Verdict
  bounded : Bool := false
  detail : String := ""
  deriving Inhabited

/-- What a check's detail shows: its counterexample, witness, or core. -/
def detailText : Fren.Core.Detail → String
  | .counterexample vals => s!"counterexample {Fren.Core.showAssignment vals}"
  | .witness vals => s!"witness {Fren.Core.showAssignment vals}"
  | .conflict input core => s!"no outputs for {Fren.Core.showAssignment input}, by {Fren.Core.showNames core}"
  | .nondeterministic input a b => s!"for {Fren.Core.showAssignment input}, `{a}` or `{b}`"
  | .vacuous core => s!"ruled out by {Fren.Core.showNames core}"
  | .redundant core => s!"follows from {Fren.Core.showNames core}"
  | .vacuousAssumptions core => s!"contradictory assumptions {Fren.Core.showNames core}"
  | .refuted _ vals => s!"refuted model {Fren.Core.showAssignment vals}"
  | .unknown reason => reason
  | .outOfRange => "an index out of range"
  | .undecidedQuantifier n => s!"a quantifier undecided up to {n}"
  | .none => ""

/-- The checks of `files` that `method` runs itself under `fren check
--evidence value`, by `methodKey`, and the run's exit code. A check that
the method does not run, such as one that it skips (`check::method_run`),
or one of a function, which only the solver runs, is not among them. -/
def methodResults (files : Array String) (method : Fren.Core.ProofMethod) (value : String) (jobs? : Option Nat) :
    IO (Std.HashMap String MethodFound × UInt32) := do
  let record ← IO.mkRef #[]
  let args : FrenCli.Args := { files, evidence? := Fren.Core.evidenceOf? value, jobs? }
  let (_, code) ← IO.FS.withIsolatedStreams (FrenCli.check args (some record))
  let found := (← record.get).foldl (init := ({} : Std.HashMap String MethodFound)) fun acc (item, r, m) =>
    if m != method then acc else
    acc.insert (methodKey item r) { kind := r.kind, verdict := r.verdict, bounded := r.bounded?.isSome, detail := detailText r.detail }
  return (found, code)

/-- The contradictions that `methodsAgree` expects, each a check by its file
and `methodKey`, with why: a known bug, by its issue, or a difference that
is not one. Each is narrow: a single check. -/
def methodExceptions : Array (String × String × String) := #[]

/-- What `methodsAgree` counted. -/
structure MethodCounts where
  checks : Nat := 0
  /-- Checks on which at least two methods contributed a verdict. -/
  compared : Nat := 0
  /-- By method: checks it ran and decided, ran and left inconclusive, and
  did not run. -/
  decided : Array Nat := #[0, 0, 0]
  inconclusive : Array Nat := #[0, 0, 0]
  notRun : Array Nat := #[0, 0, 0]
  /-- A counterexample beside a pass of enumeration's that holds only up to
  the size: no contradiction, as the counterexample may be larger. -/
  beyondSize : Nat := 0
  excepted : Nat := 0
  /-- Specs with a static error, which no method checks. -/
  static : Nat := 0
  /-- Runs that reported an error under their method alone (exit 2), as
  `name: method`, such as `F0639` under random testing or `F0645` under
  enumeration: the checks of the procedures that the error names are
  missing from that run, and counted under "not run", while its other
  checks are compared. -/
  errored : Array String := #[]
  /-- Checks on which both the solver and enumeration, and both the solver
  and random testing, contributed a verdict (`methodFloors`). -/
  solverEnumerated : Nat := 0
  solverRandom : Nat := 0
  deriving Inhabited

/-- Compares the methods on `files`, checked together as `name`, `jobs?`
procedures at once, adding to `counts`; returns the contradictions. -/
def methodsAgreeOn (name : String) (files : Array String) (counts : IO.Ref MethodCounts)
    (jobs? : Option Nat := none) : IO (Array String) := do
  let mut runs := #[]
  for (m, value) in comparedMethods do
    let (found, code) ← methodResults files m value jobs?
    runs := runs.push (found, code)
  if runs[0]!.2 == 2 then counts.modify fun c => { c with static := c.static + 1 }
  else
    for (_, code) in runs, (_, value) in comparedMethods do
      if code == 2 then counts.modify fun c => { c with errored := c.errored.push s!"{name}: {value}" }
  -- Every check that some method ran, by its key, in order.
  let keys := (runs.foldl (init := (#[] : Array String)) fun acc (found, _) =>
    acc ++ found.toArray.map (·.1)).qsort (· < ·) |>.toList.eraseDups
  let mut failures := #[]
  for key in keys do
    let found := runs.map fun (f, _) => f.get? key
    let verdictOf (i : Nat) := ((found[i]!).map (·.verdict)).getD .inconclusive
    let bounded := ((found[1]!).map (·.bounded)).getD false
    let some kind := (found.findSome? id).map (·.kind) | continue
    let contributions := (List.range comparedMethods.size).map fun i =>
      Fren.Core.contributionOf kind comparedMethods[i]!.1 (verdictOf i) (i == 1 && bounded)
    counts.modify fun c => Id.run do
      let mut c := { c with checks := c.checks + 1 }
      for i in [0:comparedMethods.size] do
        match found[i]! with
        | none => c := { c with notRun := c.notRun.modify i (· + 1) }
        | some f =>
          if f.verdict == .inconclusive then c := { c with inconclusive := c.inconclusive.modify i (· + 1) }
          else c := { c with decided := c.decided.modify i (· + 1) }
      if (contributions.filter (· != .nothing)).length ≥ 2 then c := { c with compared := c.compared + 1 }
      let said (i : Nat) := contributions[i]! != .nothing
      if said 0 && said 1 then c := { c with solverEnumerated := c.solverEnumerated + 1 }
      if said 0 && said 2 then c := { c with solverRandom := c.solverRandom + 1 }
      if contributions.contains .refuted && contributions.contains .bounded then
        c := { c with beyondSize := c.beyondSize + 1 }
      return c
    unless Fren.Core.methodsContradict kind (verdictOf 0) (verdictOf 1) bounded (verdictOf 2) do continue
    if methodExceptions.any fun (f, k, _) => f == name && k == key then
      counts.modify fun c => { c with excepted := c.excepted + 1 }
      continue
    let said := (List.range comparedMethods.size).map fun i =>
      let m := comparedMethods[i]!.2
      match found[i]! with
      | none => s!"{m}: not run"
      | some f =>
        let up := if f.bounded then " up to the size" else ""
        let d := if f.detail.isEmpty then "" else s!" ({f.detail})"
        s!"{m}: {repr f.verdict}{up}{d}"
    failures := failures.push s!"{name}: `{key}`: the methods contradict each other: {"; ".intercalate said}"
  return failures

/-- The fewest checks that each part of `methodsAgree` compares, between
the solver and enumeration and between the solver and random testing, so
that a change that silently stops a method, or makes its checks' keys
differ from the solver's, fails the job rather than comparing nothing: some
nine tenths of what each part compared when they were set (own 3314 and
34, ui 3175 and 218, fuzz 575 and 184). Random testing compares few, as
"no counterexample found" on a check that passes on a proof contributes
nothing (`check::methods_agree`). -/
def methodFloors : List (String × Nat × Nat) := [("own", (2982, 30)), ("ui", (2857, 196)), ("fuzz", (517, 165))]

/-- The ui tests whose checks the methods are compared on: those that the
binary checks, without a static error, as for `enumerationAgrees`. -/
def methodsCorpus : IO (Array FilePath) := enumerationCorpus

/-- The parts of `methodsAgree`'s corpus: `own`, Fren's own requirements;
`ui K N`, the `K`th of `N` shards of the ui tests; `fuzz`, the front-end
fuzzer's corpus (`FrenTest.FuzzFrontends.corpus`). -/
def methodsAgree (part : List String) : IO (Array String) := do
  let counts ← IO.mkRef ({} : MethodCounts)
  let mut failures := #[]
  let all := part.isEmpty
  if all || part == ["own"] then
    -- Two at a time: the solver, asked the checks that the requirements set
    -- to other methods, took 9.4 GB at two, and 13.8 GB at four, on macOS.
    failures := failures ++ (← methodsAgreeOn "src/Reqs" ownSpecFiles counts (jobs? := some 2))
  let (k, n) := match part with
    | ["ui", k, n] => (k.toNat?.getD 0, n.toNat?.getD 1)
    | _ => (0, 1)
  if all || part.head? == some "ui" then
    let ui ← methodsCorpus
    for f in ui, i in [0:ui.size] do
      if i % n != k then continue
      failures := failures ++ (← methodsAgreeOn f.toString #[f.toString] counts)
  if all || part == ["fuzz"] then
    for (mode, start, count) in FrenTest.FuzzFrontends.corpus do
      for s in [start:start + count] do
        let name := s!"fuzz seed {s}{FrenTest.FuzzFrontends.flags mode}"
        failures := failures ++ (← withText "spec.fren" (mode.spec s).toList.toArray fun p =>
          methodsAgreeOn name #[p] counts)
  let c ← counts.get
  let byMethod := (List.range comparedMethods.size).map fun i =>
    s!"{comparedMethods[i]!.2} decided {c.decided[i]!}, inconclusive {c.inconclusive[i]!}, not run {c.notRun[i]!}"
  IO.println s!"methodsAgree: {c.checks} checks, {c.compared} compared by at least two methods; {"; ".intercalate byMethod}; \
    {c.beyondSize} counterexamples beside a pass up to the size; {c.excepted} excepted; {failures.size} contradictions"
  IO.println s!"methodsAgree: {c.solverEnumerated} checks compared between the solver and enumeration, \
    {c.solverRandom} between the solver and random testing"
  IO.println s!"methodsAgree: {c.static} specs with static errors; {c.errored.size} runs reported an error under their \
    method alone, whose named procedures' checks are not run\
    {if c.errored.isEmpty then "" else s!": {", ".intercalate c.errored.toList}"}"
  -- The floors of the parts run, added up.
  let parts := if all then ["own", "ui", "fuzz"] else part.take 1
  let (leastE, leastR) := parts.foldl (init := (0, 0)) fun (e, r) p =>
    match methodFloors.lookup p with
    -- A shard of the ui tests has about its share of them.
    | some (e', r') => if p == "ui" then (e + e' / n, r + r' / n) else (e + e', r + r')
    | none => (e, r)
  if c.solverEnumerated < leastE then
    failures := failures.push
      s!"methodsAgree: only {c.solverEnumerated} checks compared between the solver and enumeration, fewer than {leastE}"
  if c.solverRandom < leastR then
    failures := failures.push
      s!"methodsAgree: only {c.solverRandom} checks compared between the solver and random testing, fewer than {leastR}"
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

/-- Runs `fren_test --job outOfFuel` with `env`, returning its exit code, its
failures, if it printed them, and its stderr. -/
def spawnOutOfFuel (env : Array (String × Option String)) : IO (UInt32 × Option (Array String) × String) := do
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--job", "outOfFuel"], env }
  let last := ((out.stdout.splitOn "\n").filter (!·.isEmpty)).getLast?.getD ""
  return (out.exitCode, (Json.parse last >>= fromJson?).toOption, out.stderr)

/-- A job's `panic!` fails it (`spawnJob`): `outOfFuel`, whose evaluation
runs out of fuel, aborts with `LEAN_ABORT_ON_PANIC`, and without it says
so on stderr and finds that the test counts for nothing
(`FrenTest.OutOfFuel.tinyFuel`). -/
def panicGuard : IO (Array String) := do
  let mut failures := #[]
  let (code, _, err) ← spawnOutOfFuel #[("LEAN_ABORT_ON_PANIC", some "1")]
  unless code != 0 && (err.splitOn "Ex.eval ran out of fuel").length > 1 do
    failures := failures.push s!"running out of fuel with `LEAN_ABORT_ON_PANIC` did not abort (exit {code}):\n{err}"
  let (code, found?, err) ← spawnOutOfFuel #[("LEAN_ABORT_ON_PANIC", none)]
  unless (err.splitOn "Ex.eval ran out of fuel").length > 1 do
    failures := failures.push s!"running out of fuel did not panic:\n{err}"
  match code, found? with
  | 0, some found => failures := failures ++ found
  | _, _ => failures := failures.push s!"`outOfFuel` crashed without `LEAN_ABORT_ON_PANIC` (exit {code}):\n{err}"
  return failures

/-- The jobs, as the arguments of `--job`, the slowest first. -/
def jobs : IO (Array (List String)) := do
  -- The ui tests of `misreadDir` run with the readers' injected bug.
  let (misread, ui) := (← uiFiles).partition (·.toString.startsWith misreadDir.toString)
  let n := (ui.size + uiBatch - 1) / uiBatch
  -- Every `n`th file, so that the slow ones spread over the batches.
  let batches := (List.range n).toArray.map fun k =>
    "ui" :: ((List.range ui.size).filter (· % n == k)).map (ui[·]!.toString)
  return #[["ownSpec"]] ++ (List.range mutationSlices).toArray.map (["mutation", "0", toString ·, toString mutationSlices])
    ++ batches ++ #["uiMisread" :: misread.toList.map toString] ++ (corpora.map (["conformance", ·.1])).toArray
    ++ #[["snapshots"], ["queryCache"], ["solverLifetime"], ["formatting"], ["errorCodes"], ["manualExamples"], ["ruleIds"], ["ruleReqs"], ["markdownFences"], ["printing"], ["fixing"], ["libraries"], ["leanTokens"], ["laterFiles"], ["backjumping", "reqs"], ["backjumping", "ui"],
      ["enumeration"], ["smtAgreement"], ["panicGuard"], ["smallValues"]]
    ++ FrenTest.FuzzFrontends.corpusJobs.toArray
    ++ ((List.range (← mutationCorpus).size).drop 1).toArray.map (["mutation", toString ·, "0", "1"])
    ++ (← decisionExamples).map (["decisions", ·.toString])

/-- Runs a job in this process. -/
unsafe def runJob (bless : Bool) : List String → IO (Array String)
  | "ui" :: files => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Fren }] {} (loadExts := true)
    uiTests env (files.toArray.map FilePath.mk)
  -- Spawned with `FREN_MISREAD_MODELS` set (`spawnJob`).
  | "uiMisread" :: files => runJob bless ("ui" :: files)
  | ["leanTokens"] => leanTokens
  | ["panicGuard"] => panicGuard
  -- Spawned by `panicGuard` only: it panics.
  | ["outOfFuel"] => Fren.Test.OutOfFuel.tinyFuel
  | ["snapshots"] => snapshots bless
  | ["errorCodes"] => errorCodes
  | ["manualExamples"] => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    manualExamples (← importModules #[{ module := `Fren }] {} (loadExts := true))
  | ["ruleIds"] => ruleIds
  | ["ruleReqs"] => ruleReqs
  | ["markdownFences"] => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    markdownFences (← importModules #[{ module := `Fren }] {} (loadExts := true))
  -- fren-covers: lint::printing, lint::parenthesization
  | ["printing"] => pure (FrenTest.Quote.roundTrips 5000)
  | ["smallValues"] => pure (Fren.Test.SmallValues.differences 300)
  | ["ownSpec"] => ownSpec
  -- Not among `jobs`: on `main` only, after a build of `Reqs` with its
  -- checks (`ownSpecAgreement`).
  | ["ownSpecAgreement"] => ownSpecAgreement
  | ["queryCache"] => queryCache
  | ["solverLifetime"] => solverLifetime
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
  -- Not among `jobs`: on `main` only (`methods-agree` in `ci.yml`).
  | "methodsAgree" :: part => methodsAgree part
  | ["smtAgreement"] => do
    enableInitializersExecution
    initSearchPath (← findSysroot)
    smtAgreement (← importModules #[{ module := `Fren }] {} (loadExts := true))
  | "frontendFuzz" :: args => match FrenTest.FuzzFrontends.corpusSpecs? args with
    | some specs => do
      FrenTest.FuzzFrontends.corpusFailures (← FrenTest.FuzzFrontends.loadFren) (".lake" / "fuzz") specs
    | none => throw (IO.userError s!"unknown front-end corpus `{" ".intercalate args}`")
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

/-- Runs `job` in a process of its own, returning its failures. If `timed`,
prints how long it took (`--timings`). -/
def spawnJob (bless timed : Bool) (job : List String) : IO (Array String) := do
  let args := #["--job"] ++ job.toArray ++ (if bless then #["--bless"] else #[])
  let start ← IO.monoMsNow
  -- A `panic!` aborts the job, so that it fails however its output is
  -- read: one in a `fren` run within it, such as `Ex.eval`'s when it runs
  -- out of fuel (`outOfFuel`), prints into that run's captured output,
  -- which a ui test reads only for its messages.
  let env := #[("LEAN_ABORT_ON_PANIC", some "1")]
  -- Both front ends' readers of solver models misread them (`Fren.Core.misreadModels`).
  let env := if job.head? == some "uiMisread" then env.push ("FREN_MISREAD_MODELS", some "1") else env
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args, env }
  let name ← jobName job
  if timed then IO.println s!"fren_test: {(← IO.monoMsNow) - start} ms: {name}"
  let last := ((out.stdout.splitOn "\n").filter (!·.isEmpty)).getLast?.getD ""
  match Json.parse last >>= fromJson? with
  | .ok failures =>
    if out.exitCode == 0 then
      -- What a job writes to stderr outside a captured run fails it too.
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

/-- Runs `jobs`, at most `jobCount` at once, printing how long each took if
`timed`. -/
def runJobs (bless timed : Bool) (jobs : Array (List String)) : IO (Array String) := do
  let next ← IO.mkRef 0
  let worker : IO (Array String) := do
    let mut failures := #[]
    repeat
      let k ← next.modifyGet fun k => (k, k + 1)
      let some job := jobs[k]? | break
      failures := failures ++ (← spawnJob bless timed job)
    return failures
  let tasks ← (List.range (← jobCount)).mapM fun _ => IO.asTask worker .dedicated
  tasks.foldlM (init := #[]) fun acc t => return acc ++ (← IO.ofExcept t.get)

unsafe def main (args : List String) : IO UInt32 := do
  let bless := args.contains "--bless" || (← IO.getEnv "FREN_BLESS").isSome
  if args == ["--rules-report"] then
    IO.print (← rulesReport)
    return 0
  if let "--job" :: job := args then
    IO.println (toJson (← runJob bless (job.filter (· != "--bless")))).compress
    return 0
  let selected ← IO.ofExcept ((selectJobs args (← jobs)).mapError IO.userError)
  let (first, rest) := selected.partition (bless && · == ["snapshots"])
  let timed := args.contains "--timings"
  let failures := ((← runJobs bless timed first) ++ (← runJobs bless timed rest)).qsort (· < ·)
  for f in failures do IO.eprintln s!"FAIL {f}"
  if failures.isEmpty then
    IO.println "fren_test: all passed"
    return 0
  IO.eprintln s!"fren_test: {failures.size} failure(s); `lake test -- --bless` accepts new snapshots"
  return 1
