-- keep-sorted start
import FrenCli.Color
import FrenCli.Exit
import FrenCli.Fmt
import FrenCli.Quick
import FrenCli.Smt
import FrenCore.Codes
import FrenCore.Literate
-- keep-sorted end

/-!
# Running `fren`

```
fren check [--timeout SECONDS] [--dump-smt] [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren trace [--tests GLOB]... [--require LEVEL] [-A|-W|-D|-F LINT]... FILE...
fren fmt [--check] [--ignore GLOB]... FILE...
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
fren eval --comp PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren --explain CODE
```

`-A`, `-W`, `-D` and `-F` (or `--allow`, `--warn`, `--deny` and
`--forbid`) set the level of a lint (`Reqs/Lint`), as in rustc.

Every form also takes `--color WHEN`, as rustc does: `always`, `never`, or
`auto` (the default), which colours output written to a terminal unless the
environment variable `NO_COLOR` is set or `TERM` is `dumb`.

Files are processed in order, sharing one set of modules. `check` then
checks every component and global expectation; `trace` reports the
evidence for every component (`Reqs/Trace`). Messages are rendered as rustc
renders its own (`Fren.Core.Diagnostic`), with the text shared with the
Lean-hosted front end, on stderr. Exit codes are `cli::exit` and
`trace::trace_exit`. `fmt` formats the files (`FrenCli.Fmt`), and `fix`
applies the edits that the elaborator finds for lints (`State.fixes`).
`eval` and `quickcheck` evaluate the spec without the solver
(`Reqs/Eval`, `FrenCli.Quick`).

Standard output holds only what was asked for: `trace`'s evidence report,
and the solver queries of `check --dump-smt`, as SMT-LIB separated by
`(reset)`, so that the whole stream can be replayed.
-/

namespace FrenCli

open Fren.Core (Msg Paint)

def usage : String :=
  "usage: fren check [--timeout SECONDS] [--dump-smt] [--tests N] [--seed N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren trace [--tests GLOB]... [--require LEVEL] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren fmt [--check] [--ignore GLOB]... [--color WHEN] FILE...\n       \
  fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren eval --comp PATH [--set VAR=VALUE]... [--seed N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren quickcheck [--tests N] [--seed N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren --explain CODE\n\n\
  `check` checks Fren specs. Exit status: 0 all checks passed, 1 some check\n\
  failed, 2 the checks could not run, 3 no failures but some check was\n\
  inconclusive, some constraint redundant or some lint warned. `--dump-smt` writes each solver\n\
  query to stdout, as SMT-LIB; diagnostics go to stderr. `--tests N` and\n\
  `--seed N` are as for `quickcheck`, for checks set to testing.\n\n\
  `trace` reports the evidence for every component, and scans the tests for\n\
  `fren-covers:` markers. LEVEL is trusted, tested, solver or proved. Exit\n\
  status: 0 nothing below LEVEL and no stray markers, 1 otherwise, 2 the\n\
  report could not run.\n\n\
  `fmt` formats the files in place; `--check` instead writes what it would\n\
  change to stdout, as a diff. `--ignore GLOB` skips the matching files.\n\
  Exit status: 0 formatted, 1 with `--check`\n\
  some file is not formatted, 2 some file could not be read or parsed.\n\n\
  `fix` fixes the lints that it can: unused_imports, glob_imports,\n\
  nonminimal_bool, unfulfilled_lint_expectations, length_zero, card_zero,\n\
  singleton_membership, membership_chain and index_after_use. `--only LINT` fixes\n\
  only the lints given, `--skip LINT` all but them. `--fmt` then formats the\n\
  files. `--check` and `--ignore` are as for `fmt`.\n\
  Exit status: 0 fixed, 1 with `--check` some file would change, 2 some\n\
  file could not be read or has a static error other than a denied lint.\n\n\
  LINT OPTIONS set the level of a lint, such as unused_imports: -A (--allow)\n\
  LINT allows it, -W (--warn) warns, -D (--deny) denies, and -F (--forbid)\n\
  forbids.\n\n\
  `eval` evaluates the component PATH on one behaviour, without the\n\
  solver: `--set VAR=VALUE` gives a variable a value, and the others are\n\
  searched for. Exit status: 0 the behaviour meets the component and its\n\
  expectations, 1 it does not, 2 it could not run, 3 no behaviour was found.\n\n\
  `quickcheck` tests every component and global expectation on `--tests`\n\
  random behaviours (default 100), without the solver. Exit status as for\n\
  `check`. `--seed N` sets where the random search starts (default 0).\n\n\
  `--explain` explains an error code, such as F0105.\n\n\
  `--color WHEN` colours the output: auto (the default: if it is a terminal),\n\
  always or never."

def version : String := "fren 0.1.0"

/-- Prints a message about a file to stderr, then a blank line, as rustc
does. -/
def printAt (p : Paint) (path : String) (src : Array Char) (severity : Fren.Core.Severity) (msg : Msg)
    (range : Fren.Core.Range) : IO Unit :=
  IO.eprintln ({ level := severity, msg, range : Fren.Core.Diagnostic }.render path src p)

def printDiag (p : Paint) (files : Array (String × Array Char)) (d : Diag) : IO Unit := do
  let (path, src) := files[d.file]!
  printAt p path src d.severity d.msg { start := d.span.start, stop := d.span.stop }

/-- Prints rustc's pointer to `--explain` for the codes of `msgs`, if any. -/
def printExplainHint (msgs : Array Msg) : IO Unit := do
  if let some h := Fren.Core.explainHint (msgs.filterMap (·.code?)) then IO.eprintln h

/-- An error about the command line, with no position. -/
def argError (p : Paint) (msg : Msg) : String :=
  -- Suggestions first, then the pointer to `--help`.
  let notes := msg.notes ++ msg.fixes.map ("help: " ++ ·.msg) |>.push "help: run `fren --help` for usage"
  Fren.Core.renderPlain .error { msg with notes, fixes := #[] } p

inductive Command where
  | check
  | trace
  | fmt
  | fix
  | eval
  | quickcheck
  deriving BEq

structure Args where
  command : Command := .check
  timeout : Nat := 10
  dumpSmt : Bool := false
  /-- `fmt --check` and `fix --check`. -/
  diffOnly : Bool := false
  /-- `fmt --ignore` and `fix --ignore`. -/
  ignore : Array String := #[]
  /-- `fix --fmt`. -/
  fmtAfter : Bool := false
  /-- `fix --only` and `fix --skip`. -/
  onlyLints : Array Fren.Core.Lint := #[]
  skipLints : Array Fren.Core.Lint := #[]
  tests : Array String := #[]
  require : Option Fren.Core.Level := none
  /-- `-A`, `-W`, `-D` and `-F`, in order. -/
  lints : Array (Fren.Core.Lint × Fren.Core.LintLevel) := #[]
  files : Array String := #[]
  paint : Paint := {}
  /-- `eval --comp`. -/
  comp? : Option String := none
  /-- `eval --set`, as written. -/
  sets : Array String := #[]
  /-- `eval --seed` and `quickcheck --seed`. -/
  seed : Nat := 0
  /-- `quickcheck --tests`. -/
  nTests : Nat := 100

def commands : Array String := #["check", "eval", "fix", "fmt", "quickcheck", "trace"]

def options : Array String :=
  #["--timeout", "--dump-smt", "--check", "--ignore", "--tests", "--require", "--color", "--explain", "--help", "--version", "-A", "-W", "-D", "-F",
    "--allow", "--warn", "--deny", "--forbid", "--only", "--skip", "--fmt", "--comp", "--set", "--seed", "--tests"]

def unknownLint (n : String) : Msg :=
  { code? := none, headline := s!"unknown lint `{n}`"
    notes := #[Fren.Core.lintsNote]
    fixes := (Fren.Core.similarStr n (Fren.Core.Lint.all.map (·.name))).toArray.map fun s =>
      { msg := s!"a lint with a similar name exists: `{s}`", replacement := s } }

def unknownOption (o : String) : Msg :=
  { code? := none, headline := s!"unknown option `{o}`"
    fixes := (Fren.Core.similarStr o options).toArray.map fun s =>
      { msg := s!"an option with a similar name exists: `{s}`", replacement := s } }

/-- Parses the arguments other than `--color`, whose errors are painted
with `p`. -/
def parseArgs (p : Paint := {}) : List String → Except String Args
  | "check" :: rest => go rest { paint := p }
  | "trace" :: rest => go rest { command := .trace, paint := p }
  | "fmt" :: rest => go rest { command := .fmt, paint := p }
  | "fix" :: rest => go rest { command := .fix, paint := p }
  | "eval" :: rest => go rest { command := .eval, paint := p }
  | "quickcheck" :: rest => go rest { command := .quickcheck, paint := p }
  | [] => .error usage
  | c :: _ =>
    if c.startsWith "-" then .error (argError p (unknownOption c))
    else .error (argError p {
      code? := none, headline := s!"unknown command `{c}`",
      notes := #["note: the commands are `check`, `eval`, `fix`, `fmt`, `quickcheck` and `trace`"],
      fixes := (Fren.Core.similarStr c commands).toArray.map fun s => { msg := s!"a command with a similar name exists: `{s}`", replacement := s } })
where
  only (opt : String) (cmd : String) : Except String Args :=
    .error (argError p { code? := none, headline := s!"`{opt}` is an option of `fren {cmd}`" })
  go : List String → Args → Except String Args
    | [], a =>
      if a.files.isEmpty then .error (argError p { code? := none, headline := "no input files" })
      else .ok a
    | "--timeout" :: n :: rest, a =>
      if a.command != .check then only "--timeout" "check" else
      match n.toNat? with
      | some t => go rest { a with timeout := t }
      | none => .error (argError p {
          code? := none, headline := s!"invalid timeout `{n}`",
          notes := #["note: the timeout is a whole number of seconds, such as `--timeout 30`"] })
    | "--comp" :: c :: rest, a =>
      if a.command == .eval then go rest { a with comp? := some c } else only "--comp" "eval"
    | "--set" :: x :: rest, a =>
      if a.command != .eval then only "--set" "eval"
      else if x.contains '=' then go rest { a with sets := a.sets.push x }
      else .error (argError p {
        code? := none, headline := s!"invalid `--set` value `{x}`"
        notes := #["note: a variable is set as `VAR=VALUE`, such as `--set x=3` or `--set w.ready?=true`"] })
    | "--seed" :: n :: rest, a =>
      if a.command != .eval && a.command != .quickcheck && a.command != .check then only "--seed" "check`, `fren eval` and `fren quickcheck" else
      match n.toNat? with
      | some k => go rest { a with seed := k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid seed `{n}`",
          notes := #["note: the seed is a whole number, such as `--seed 7`"] })
    | "--tests" :: n :: rest, a =>
      if a.command == .trace then go rest { a with tests := a.tests.push n }
      else if a.command != .quickcheck && a.command != .check then only "--tests" "check`, `fren trace` and `fren quickcheck" else
      match n.toNat? with
      | some k => go rest { a with nTests := k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid number of tests `{n}`",
          notes := #["note: the number of tests is a whole number, such as `--tests 1000`"] })
    | "--dump-smt" :: rest, a =>
      if a.command == .check then go rest { a with dumpSmt := true }
      else only "--dump-smt" "check"
    | "--check" :: rest, a =>
      if a.command == .fmt || a.command == .fix then go rest { a with diffOnly := true }
      else only "--check" "fmt` and `fren fix"
    | "--ignore" :: g :: rest, a =>
      if a.command == .fmt || a.command == .fix then go rest { a with ignore := a.ignore.push g }
      else only "--ignore" "fmt` and `fren fix"
    | "--fmt" :: rest, a =>
      if a.command == .fix then go rest { a with fmtAfter := true }
      else only "--fmt" "fix"
    | "--only" :: n :: rest, a =>
      if a.command != .fix then only "--only" "fix" else
      match Fren.Core.Lint.ofName? n with
      | some l => go rest { a with onlyLints := a.onlyLints.push l }
      | none => .error (argError p (unknownLint n))
    | "--skip" :: n :: rest, a =>
      if a.command != .fix then only "--skip" "fix" else
      match Fren.Core.Lint.ofName? n with
      | some l => go rest { a with skipLints := a.skipLints.push l }
      | none => .error (argError p (unknownLint n))
    | "--require" :: l :: rest, a =>
      if a.command != .trace then only "--require" "trace"
      else match Fren.Core.Level.ofName? l with
        | some lv => go rest { a with require := some lv }
        | none => .error (argError p (Fren.Core.unknownLevelMsg l))
    | opt@"-A" :: n :: rest, a | opt@"--allow" :: n :: rest, a => do go rest (← addLint opt .allow n a)
    | opt@"-W" :: n :: rest, a | opt@"--warn" :: n :: rest, a => do go rest (← addLint opt .warn n a)
    | opt@"-D" :: n :: rest, a | opt@"--deny" :: n :: rest, a => do go rest (← addLint opt .deny n a)
    | opt@"-F" :: n :: rest, a | opt@"--forbid" :: n :: rest, a => do go rest (← addLint opt .forbid n a)
    | [opt@"--timeout"], _ | [opt@"--tests"], _ | [opt@"--ignore"], _ | [opt@"--require"], _
    | [opt@"--only"], _ | [opt@"--skip"], _
    | [opt@"--comp"], _ | [opt@"--set"], _ | [opt@"--seed"], _
    | [opt@"-A"], _ | [opt@"-W"], _ | [opt@"-D"], _ | [opt@"-F"], _
    | [opt@"--allow"], _ | [opt@"--warn"], _ | [opt@"--deny"], _ | [opt@"--forbid"], _ =>
      .error (argError p { code? := none, headline := s!"`{opt}` needs a value" })
    | f :: rest, a =>
      if f.startsWith "-" then .error (argError p (unknownOption f))
      else go rest { a with files := a.files.push f }
  addLint (opt : String) (lv : Fren.Core.LintLevel) (n : String) (a : Args) : Except String Args :=
    if a.command == .fmt then
      .error (argError p { code? := none, headline := s!"`{opt}` is an option of `fren check`, `fren trace` and `fren fix`" })
    else
    match Fren.Core.Lint.ofName? n with
    | some l => .ok { a with lints := a.lints.push (l, lv) }
    | none => .error (argError p (unknownLint n))

/-- `fren --explain CODE`: prints the explanation of `code`, or an error
painted with `p`. -/
def explain (p : Paint) (code : String) : IO UInt32 := do
  match Fren.Core.explain? code with
  | some c => IO.print c.explanation; return 0
  | none =>
    IO.eprint (argError p {
      code? := none, headline := s!"`{code}` is not an error code",
      notes := #["note: error codes are written like `F0105`, as they are in Fren's messages"] })
    return 2

/-- Checks the files of `tested` claims (`trace::tested_file`). -/
def checkClaims (st : State) : IO State := do
  let mut st := st
  for c in st.claims do
    if !c.tested then continue
    for (file, span) in c.texts do
      let src? ← match ← (IO.FS.readFile file).toBaseIO with
        | .ok src => pure (some src)
        | .error _ => pure none
      if let .error msg := Fren.Core.checkTestedFile (Fren.Core.showComp c.comp) file src? then
        st := { st with diags := st.diags.push { file := c.file, span, msg } }
  return st

/-- Reads a file, or prints why it could not. -/
def readSpec (p : Paint) (path : String) : IO (Option String) := do
  try return some (← IO.FS.readFile path) catch e =>
    let why := match e with
      | .noFileOrDirectory .. => "no such file or directory"
      | .permissionDenied .. => "permission denied"
      | .inappropriateType .. => "it is a directory"
      | e => toString e
    IO.eprint (Fren.Core.renderPlain .error { code? := none, headline := s!"could not read `{path}`: {why}" } p)
    return none

/-- Reads and elaborates the files; `none` if one cannot be read. `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborate (p : Paint) (paths : Array String) (lints : Array (Fren.Core.Lint × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Option (Array (String × Array Char) × State)) := do
  let mut files := #[]
  let mut st : State := { cliLevels := Fren.Core.Levels.ofFlags lints }
  for path in paths do
    let some src ← readSpec p path | return none
    let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
    let chars := src.toList.toArray
    let file := files.size
    files := files.push (path, chars)
    match lex chars with
    | .error e => st := { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
    | .ok toks =>
      match parse toks with
      | .error e => st := { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
      | .ok items => st := (elabFile file chars items (if ignored path then #[] else fixing) |>.run st).2
  return some (files, ← checkClaims st)

/-- Prints the count of static errors, and the pointer to `--explain` for
the codes of `diags`. -/
def printErrorCount (p : Paint) (errors : Nat) (diags : Array Diag) (what := "check") : IO Unit := do
  IO.eprintln (Fren.Core.header .error
    { code? := none, headline := s!"could not {what} due to {errors} previous error{if errors == 1 then "" else "s"}" } p)
  IO.eprintln ""
  printExplainHint (diags.map (·.msg))

/-- Reads and elaborates the files, printing any static errors. -/
def load (p : Paint) (paths : Array String) (lints : Array (Fren.Core.Lint × Fren.Core.LintLevel)) :
    IO (Option (Array (String × Array Char) × State)) := do
  let some (files, st) ← elaborate p paths lints | return none
  for d in st.diags do printDiag p files d
  let errors := st.diags.filter (·.severity == .error) |>.size
  if errors > 0 then
    printErrorCount p errors st.diags
    return none
  return some (files, st)

/-- Prints the messages of result `r` of `c`, at the positions of the items
they are about; returns them. -/
def printResult (p : Paint) (files : Array (String × Array Char)) (c : CComp) (r : Fren.Core.CheckResult) :
    IO (Array Msg) := do
  let mut shown := #[]
  for m in Fren.Core.messages (c.vars.any fun v => v.role == .output && !v.isPub) r c.decidable do
    let prop? := m.item?.bind fun n => c.props.find? (·.name == n)
    let index? := m.atIndex?.bind fun k => m.item?.bind fun n => (c.indexes.filter (·.1 == n))[k]?.map (·.2.2.1)
    let span := if let some sp := index? then sp else match prop?, m.item? with
      | some p, _ => if m.atTrigger then p.triggerSpan?.getD p.span else p.span
      | none, some n => (c.insts.find? (·.name == n)).map (·.span)
        |>.orElse (fun _ => (c.vars.find? (·.name == n)).map (·.span)) |>.getD c.span
      | none, none => c.span
    printDiag p files { file := c.file, span, severity := m.severity, msg := m.msg }
    shown := shown.push m.msg
  return shown

/-- Tests the comp or global expectation `c`, whose counterpart is `ec`
(`Reqs/Eval#fren-quickcheck`), and prints what testing found about the
checks that `keep` selects: their results, and those that are not run
are dropped. Returns the results and the messages printed. -/
def testComp (args : Args) (files : Array (String × Array Char)) (sp : Eval.Spec) (c : CComp) (ec : Eval.Comp)
    (global : Bool) (keep : Fren.Core.CheckResult → Bool) : IO (Array Fren.Core.CheckResult × Array Msg) := do
  -- Each comp has its own stream, so a run does not depend on the others.
  let rng : Eval.Rng := ⟨Eval.mix args.seed.toUInt64 (hash c.path)⟩
  let rep := (if global then sp.quickGlobal ec args.nTests else sp.quickComp ec args.nTests).run' rng
  let results := rep.results.filter keep
  let mut shown := #[]
  let subject := s!"`{Fren.Core.showComp (if global then c.path ++ (c.props[0]?.map (·.name)).getD .anonymous else c.path)}`"
  for r in results do
    -- Inconclusive results are reported below, once for the comp.
    if r.verdict == .fail then shown := shown ++ (← printResult args.paint files c r)
  let warn (msg : Msg) : IO Unit := printDiag args.paint files { file := c.file, span := c.span, severity := .warning, msg }
  if let some input := rep.noOutputs? then
    if results.any (·.kind == .realizable) then
      let msg := Fren.Core.noOutputsMsg subject input
      warn msg
      shown := shown.push msg
  else if rep.untested && !results.isEmpty then
    let msg := Fren.Core.untestedMsg subject args.nTests
    warn msg
    shown := shown.push msg
  -- At the trigger of each check that no test reached (`F0612`).
  for r in rep.untriggered.filter keep do
    let some n := r.prop? | continue
    let (what, span) := match r.kind, r.target? with
      | .inst, some (d, a) =>
        (s!"the assumption `{Fren.Core.showComp (d ++ a)}` of instance `{n}`", ((c.insts.find? (·.name == n)).map (·.span)).getD c.span)
      | _, _ =>
        let p? := c.props.find? (·.name == n)
        (if global then subject else s!"`{Fren.Core.showComp (c.path ++ n)}`", (p?.map fun p => p.triggerSpan?.getD p.span).getD c.span)
    let msg := Fren.Core.untriggeredMsg what args.nTests
    printDiag args.paint files { file := c.file, span, severity := .warning, msg }
    shown := shown.push msg
  return (results, shown)

/-- Runs `fren check`, printing diagnostics and the summary to stderr and
any solver queries to stdout; returns the exit code. -/
def check (args : Args) : IO UInt32 := do
  let some (files, st) ← load args.paint args.files args.lints | return exitCode false none
  let prelude := st.prelude
  let mut all := #[]
  -- Warnings from lints, already printed.
  let mut shown := st.diags.map (·.msg)
  let todo := st.comps.map (·, false) ++ st.globals.map (·, true)
  -- Each model is confirmed with the evaluator (`Reqs/Eval#confirming-models`).
  let spec? := specOf files
  let mut internal := #[]
  let mut byTesting := 0
  if let .error e := spec? then
    internal := internal.push (Msg.internal s!"the evaluator cannot read the spec: {e}")
    printDiag args.paint files { file := 0, span := default, msg := internal.back! }
  for (c, global) in todo do
    let kinds := Fren.Core.kindsFor global
    let n ← IO.mkRef 0
    let dump? := if args.dumpSmt then some fun script => do
        n.modify (· + 1)
        IO.print s!"; {c.path}: query {← n.get}\n{script}(check-sat)\n(reset)\n\n"
      else none
    let bk := backend prelude st.datatypes c args.timeout dump? (st.usesStrings || st.usesSeqs) (st.usesSets || st.usesSeqs) st.usesProjection
    let log ← IO.mkRef #[]
    let raw ← match spec? with
      | .ok sp => match sp.counterpart? c global with
        | some ec =>
          -- The checks set to testing are not asked of the solver (`check::by_testing`).
          let (core, ks) := (pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start))).untested c.tested kinds
          Fren.Core.checkComp (fun k => confirming sp ec k log (bk k)) core ks
        | none =>
          internal := internal.push (Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`")
          printDiag args.paint files { file := c.file, span := c.span, msg := internal.back! }
          let (core, ks) := (toCore c).untested c.tested kinds
          Fren.Core.checkComp bk core ks
      | .error _ =>
        let (core, ks) := (toCore c).untested c.tested kinds
        Fren.Core.checkComp bk core ks
    let (results, refuted) := applyRefutations raw (← log.get)
    for (r, msg) in refuted do
      let span := (r.prop?.bind fun n => c.props.find? (·.name == n)).map (·.span) |>.getD c.span
      printDiag args.paint files { file := c.file, span, msg }
      internal := internal.push msg
    for r in results do
      shown := shown ++ (← printResult args.paint files c r)
    all := all ++ results
    -- The checks set to testing, tested (`Reqs/Check#checking-by-testing`).
    if c.tested.any then
      match spec? with
      | .ok sp =>
        if let some ec := sp.counterpart? c global then
          let (tested, msgs) ← testComp args files sp c ec global fun r =>
            kinds.contains r.kind && c.tested.covers r && Fren.Core.runOf r.kind true == .byTesting
          shown := shown ++ msgs
          all := all ++ tested
          byTesting := byTesting + (tested.filter (·.verdict == .pass)).size
      | .error _ => pure ()
  IO.eprintln (Fren.Core.summary all byTesting)
  if shown.any (·.code?.isSome) then
    IO.eprintln ""
    printExplainHint shown
  let errors := internal.map fun _ => Fren.Core.Severity.error
  return exitCode true (Fren.Core.worst (all.filterMap (·.severity?) ++ st.diags.map (·.severity) ++ errors))

/-- Runs `fren quickcheck` (`Reqs/Eval#fren-quickcheck`), printing
diagnostics and the summary to stderr; returns the exit code. -/
def quickcheck (args : Args) : IO UInt32 := do
  let some (files, st) ← load args.paint args.files args.lints | return exitCode false none
  let sp ← match specOf files with
    | .ok sp => pure sp
    | .error e =>
      printDiag args.paint files { file := 0, span := default, msg := Msg.internal s!"the evaluator cannot read the spec: {e}" }
      return exitCode true (some .error)
  let mut all := #[]
  let mut shown := st.diags.map (·.msg)
  let mut sevs := st.diags.map (·.severity)
  for (c, global) in st.comps.map (·, false) ++ st.globals.map (·, true) do
    let some ec := sp.counterpart? c global
      | let msg := Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`"
        printDiag args.paint files { file := c.file, span := c.span, msg }
        sevs := sevs.push .error
    let (results, msgs) ← testComp args files sp c ec global fun _ => true
    shown := shown ++ msgs
    all := all ++ results
  let count v := (all.filter (·.verdict == v)).size
  IO.eprintln s!"fren: {count .pass} passed, {count .fail} failed, {count .inconclusive} inconclusive, in {args.nTests} tests each"
  if shown.any (·.code?.isSome) then
    IO.eprintln ""
    printExplainHint shown
  return exitCode true (Fren.Core.worst (all.filterMap (·.severity?) ++ sevs))

/-- Runs `fren eval` (`Reqs/Eval#fren-eval`), printing the behaviour to
stdout; returns the exit code (`eval::eval_exit`). -/
def evalCmd (args : Args) : IO UInt32 := do
  let fail (msg : Msg) : IO UInt32 := do IO.eprint (argError args.paint msg); return 2
  let some (files, _) ← load args.paint args.files args.lints | return 2
  let some compText := args.comp? | fail { code? := none, headline := "`fren eval` needs `--comp PATH`" }
  let lst ← match specStateOf files with
    | .ok s => pure s
    | .error e =>
      printDiag args.paint files { file := 0, span := default, msg := Msg.internal s!"the evaluator cannot read the spec: {e}" }
      return 2
  let sp := lst.spec
  let path := (compText.splitOn "::").foldl Lean.Name.mkStr .anonymous
  let some c := sp.comp? path
    | fail { code? := none, headline := s!"no component `{compText}`"
             notes := #[s!"note: the components are {Fren.Core.showNameList (sp.comps.map (·.path))}"] }
  let vars := sp.flatVars c
  let mut given : Eval.Env := {}
  for set in args.sets do
    let (x, text) := match set.splitOn "=" with
      | x :: rest => (x, "=".intercalate rest)
      | [] => ("", "")
    let n := (x.splitOn ".").foldl Lean.Name.mkStr .anonymous
    let some v := vars.find? (·.name == n)
      | return ← fail { code? := none, headline := s!"`{Fren.Core.showComp path}` has no variable `{x}`"
                        notes := #[s!"note: its variables are {Fren.Core.showNameList (vars.map (·.name))}"] }
    match Eval.parseValue lst path.getPrefix v.ty text with
    | .ok val => given := given.insert n val
    | .error e => return ← fail { code? := none, headline := s!"invalid value for `{x}`: {e}" }
  let (w, rng) := (Eval.World.random sp).run ⟨args.seed.toUInt64⟩
  let I := w.interp sp
  let atoms := sp.meaning c
  let (strs, rng) := (Eval.stringsOf atoms).run rng
  let p : Eval.Problem := { vars := Eval.remaining (sp.order c) given, atoms, ints := Eval.intsOf atoms, strs }
  let found := (p.solve sp w I given 100000).run' rng
  let env := found.getD given
  -- `env` is now fixed.
  if found.isNone && !vars.all (given.contains ·.name) then
    IO.eprintln (Fren.Core.renderPlain .warning
      { code? := none, headline := s!"no behaviour of `{Fren.Core.showComp path}` was found with the values given"
        notes := #["note: the variables not set have no value"] } args.paint)
  for v in vars do
    IO.println s!"{v.name} = {(env[v.name]?.map (·.show sp)).getD "unknown"}"
  let ev := sp.evaluate I c env
  for (what, b) in ev.lines do
    IO.println s!"{what}: {(b.map toString).getD "unknown"}"
  let status := match ev.status? with
    | some .Meets => "meets" | some .Violates => "violates" | some .Inadmissible => "inadmissible" | none => "unknown"
  IO.println s!"status: {status}"
  return Eval.evalExit true (vars.all (env.contains ·.name)) ev.status? ev.expectFalse

/-- Runs `fren trace`, printing diagnostics to stderr and the evidence
report to stdout; returns the exit code. -/
def trace (args : Args) : IO UInt32 := do
  let some (files, st) ← load args.paint args.files args.lints | return Fren.Core.traceExitCode false false false
  let claims : Fren.Core.Claims := st.claims.foldl (init := {}) fun cs c =>
    let texts := c.texts.map (·.1)
    if c.tested then { cs with tested := cs.tested.insert c.comp (cs.tested.getD c.comp #[] ++ texts) }
    else { cs with trusted := cs.trusted.insert c.comp (cs.trusted.getD c.comp #[] ++ texts) }
  let comps := st.comps.qsort (·.path.toString < ·.path.toString)
  -- The `fren` command cannot check `impl`s.
  let ls := Fren.Core.levels (comps.map fun c =>
    { path := c.path, hasOutputs := c.vars.any (·.role == .output), insts := c.insts.map (·.comp) }) claims
  let threshold := args.require.getD .missing
  let mut below := false
  -- Warnings from lints, already printed.
  let mut shown := st.diags.map (·.msg)
  for c in comps do
    let l := ls.getD c.path .missing
    if let some .warning := Fren.Core.traceSeverity l threshold args.require.isSome then
      below := true
      let msg := Fren.Core.belowMsg c.path l threshold "`--require`"
      printDiag args.paint files { file := c.file, span := c.span, severity := .warning, msg }
      shown := shown.push msg
  let tests ← Fren.Core.expandGlobs args.tests
  let srcs ← tests.filterMapM fun (f : String) => do
    match ← (IO.FS.readFile (System.FilePath.mk f)).toBaseIO with
    | .ok src => pure (some (f, src))
    | .error _ => pure none
  let strays := Fren.Core.strays (comps.map (·.path)) claims srcs
  for st in strays do
    let chars := ((srcs.find? (·.1 == st.file)).map (·.2) |>.getD "").toList.toArray
    let start := (Fren.Core.lines chars)[st.line - 1]!.1 + st.col
    printAt args.paint st.file chars .error st.msg { start, stop := start + st.len }
    shown := shown.push st.msg
  IO.println (Fren.Core.traceSummary (comps.map (·.path)) ls)
  if !shown.isEmpty then
    IO.eprintln ""
    printExplainHint shown
  return Fren.Core.traceExitCode true below !strays.isEmpty

/-- Runs `fren fmt`: rewrites the files, or with `--check`, prints their
diffs to stdout, painted with `out`; returns the exit code (`fmt::file`,
`fmt::exit`). -/
def fmt (args : Args) (out : Paint) : IO UInt32 := do
  let mut failed := 0
  let mut allFormatted := true
  let mut shown := #[]
  for path in args.files do
    if Fmt.ignored args.ignore path then continue
    let some src ← readSpec args.paint path | failed := failed + 1; continue
    match Fmt.formatFile path src with
    | .error (span, msg) =>
      printAt args.paint path (Fmt.parsedText path src).toList.toArray .error msg { start := span.start, stop := span.stop }
      shown := shown.push msg
      failed := failed + 1
    | .ok new =>
      let formatted := new == src
      allFormatted := allFormatted && formatted
      let (write, diff) := Fmt.fileAction args.diffOnly false true formatted
      if write then IO.FS.writeFile path new
      if diff then IO.print (Fmt.diff out path src new)
  if failed > 0 then
    IO.eprintln (Fren.Core.header .error
      { code? := none, headline := s!"could not format {failed} file{if failed == 1 then "" else "s"}" } args.paint)
    if !shown.isEmpty then
      IO.eprintln ""
      printExplainHint shown
  return Fmt.exitCode args.diffOnly (failed == 0) allFormatted

/-- `src`, the text of a file as read, with `edits` applied; their ranges
are in `text`, the text as elaborated, which for a Markdown spec has its
prose blanked but keeps its lines. -/
def applyFileEdits (src : String) (text : Array Char) (edits : Array (Fren.Core.Range × String)) : String :=
  let srcChars := src.toList.toArray
  let starts := (Fren.Core.lines srcChars).map (·.1)
  let move (off : Nat) :=
    let (n, lstart, _) := Fren.Core.lineAt text off
    starts[n - 1]! + (off - lstart)
  Fren.Core.applyEdits srcChars (edits.map fun (r, t) => ({ start := move r.start, stop := move r.stop }, t))

/-- Runs `fren fix`: rewrites the files to fix the lints that it can, or
with `--check`, prints the diffs to stdout, painted with `out`; prints the
lints that it does not fix to stderr; returns the exit code
(`lint::fix_exit`). -/
def fix (args : Args) (out : Paint) : IO UInt32 := do
  let fixing := Fren.Core.Lint.all.filter (Fren.Core.fixSelected args.onlyLints args.skipLints)
  let some (files, st) ← elaborate args.paint args.files args.lints fixing (Fmt.ignored args.ignore)
    | return Fren.Core.fixExit args.diffOnly false false
  let errors := st.diags.filter fun d => d.severity == .error && d.lint?.isNone
  if !errors.isEmpty then
    -- Nothing is fixed.
    for d in st.diags do printDiag args.paint files d
    printErrorCount args.paint (st.diags.filter (·.severity == .error)).size st.diags "fix"
    return Fren.Core.fixExit args.diffOnly false false
  let left := st.diags.filter (!·.fixed)
  for d in left do printDiag args.paint files d
  let mut unchanged := true
  for (path, text) in files, i in [0:files.size] do
    let edits := st.edits.filterMap fun (f, e) => if f == i then some e else none
    let format := args.fmtAfter && !Fmt.ignored args.ignore path
    if edits.isEmpty && !format then continue
    let some src ← readSpec args.paint path | return Fren.Core.fixExit args.diffOnly false false
    let fixed := applyFileEdits src text edits
    -- The file parsed, and fixing it keeps it parsing.
    let new := if format then (Fmt.formatFile path fixed).toOption.getD fixed else fixed
    if new == src then continue
    unchanged := false
    if args.diffOnly then IO.print (Fmt.diff out path src new)
    else
      IO.FS.writeFile path new
      let n := (st.diags.filter fun d => d.fixed && d.file == i).size
      IO.eprintln (if n == 0 then s!"formatted {path}" else s!"fixed {path} ({n} lint{if n == 1 then "" else "s"})")
  printExplainHint (left.map (·.msg))
  return Fren.Core.fixExit args.diffOnly true unchanged

/-- Parses the value of `--color`. -/
def colorValue (w : String) : Except Msg ColorChoice :=
  match ColorChoice.ofString? w with
  | some c => .ok c
  | none => .error {
      code? := none, headline := s!"invalid value `{w}` for `--color`",
      notes := #["note: `--color` is `auto`, `always` or `never`"],
      fixes := (Fren.Core.similarStr w #["auto", "always", "never"]).toArray.map fun c =>
        { msg := s!"a value with a similar name exists: `{c}`", replacement := c } }

/-- Removes `--color WHEN` and `--color=WHEN` from anywhere in `args`; the
last one wins. -/
def colorArg : List String → Except Msg (Option ColorChoice × List String)
  | [] => .ok (none, [])
  | ["--color"] => .error {
      code? := none, headline := "`--color` needs a value",
      notes := #["note: `--color` is `auto`, `always` or `never`"] }
  | "--color" :: w :: rest => do
    let c ← colorValue w
    let (later, rest) ← colorArg rest
    return (later <|> some c, rest)
  | a :: rest => do
    let (later, rest) ← colorArg rest
    match a.dropPrefix? "--color=" with
    | some w => return (later <|> some (← colorValue w.toString), rest)
    | none => return (later, a :: rest)

/-- The painter for a stream (`cli::color`). -/
def paintFor (choice : ColorChoice) (stream : IO.FS.Stream) : IO Paint := do
  let tty ← stream.isTty
  let noColor := (← IO.getEnv "NO_COLOR").any (!·.isEmpty)
  let dumb := (← IO.getEnv "TERM") == some "dumb"
  return { on := useColor choice tty noColor dumb }

/-- Runs `fren` with `args`, printing diagnostics and usage errors to
stderr; returns the exit code. -/
def run (args : List String) : IO UInt32 := do
  let (choice, args) ← match colorArg args with
    | .ok r => pure r
    | .error msg => IO.eprint (argError (← paintFor .auto (← IO.getStderr)) msg); return 2
  let choice := choice.getD .auto
  let err ← paintFor choice (← IO.getStderr)
  match args with
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | ["--version"] | ["-V"] => IO.println version; return 0
  | ["--explain", code] => explain err code
  | _ =>
    match parseArgs err args with
    | .ok a =>
      let a := { a with paint := err }
      match a.command with
      | .check => check a
      | .trace => trace a
      | .fmt => fmt a (← paintFor choice (← IO.getStdout))
      | .fix => fix a (← paintFor choice (← IO.getStdout))
      | .eval => evalCmd a
      | .quickcheck => quickcheck a
    | .error msg => IO.eprint (if msg.endsWith "\n" then msg else msg ++ "\n"); return 2

end FrenCli
