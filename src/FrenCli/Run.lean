-- keep-sorted start
import FrenCli.Color
import FrenCli.Exit
import FrenCli.Fmt
import FrenCli.MutateRun
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
fren mutate [--by solver|testing|both] [--comp PATH] [--mutant ID]... [--sample N] [--seed N] [--list]
    [--timeout SECONDS] [--tests N] [-A|-W|-D|-F LINT]... FILE...
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
(`Reqs/Eval`, `FrenCli.Quick`). `mutate` checks mutants of the spec
(`Reqs/Mutate`, `FrenCli.Mutate`).

Standard output holds only what was asked for: `trace`'s evidence report,
`mutate`'s kill rates, and the solver queries of `check --dump-smt`, as SMT-LIB separated by
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
  fren mutate [--by solver|testing|both] [--comp PATH] [--mutant ID]... [--sample N] [--seed N] [--list]\n              \
  [--timeout SECONDS] [--tests N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
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
  `fix` fixes the lints that it can, whose messages say `fren fix` can fix\n\
  them. `--only LINT` fixes only the lints given, `--skip LINT`\n\
  all but them; LINT may be a group. `--fmt` then formats the files.\n\
  `--check` and `--ignore` are as for `fmt`.\n\
  Exit status: 0 fixed, 1 with `--check` some file would change, 2 some\n\
  file could not be read or has a static error other than a denied lint.\n\n\
  LINT OPTIONS set the level of a lint, such as unused_imports, or of each\n\
  lint of a group, such as pedantic: -A (--allow) LINT allows it, -W\n\
  (--warn) warns, -D (--deny) denies, and -F (--forbid) forbids.\n\n\
  `eval` evaluates the component PATH on one behaviour, without the\n\
  solver: `--set VAR=VALUE` gives a variable a value, and the others are\n\
  searched for. Exit status: 0 the behaviour meets the component and its\n\
  expectations, 1 it does not, 2 it could not run, 3 no behaviour was found.\n\n\
  `quickcheck` tests every component and global expectation on `--tests`\n\
  random behaviours (default 100), without the solver. Exit status as for\n\
  `check`. `--seed N` sets where the random search starts (default 0).\n\n\
  `mutate` makes small changes to the spec's constraints and definitions,\n\
  checks each changed spec (a mutant), and reports the mutants that no check\n\
  rejects. `--by` checks them with the solver (the default), by testing, or\n\
  both. `--comp PATH` and `--mutant ID` select mutants, and `--sample N` takes\n\
  N of them, chosen by `--seed`. `--list` lists them without checking them.\n\
  Exit status as for `check`, where each surviving mutant is a warning.\n\n\
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
  | mutate
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
  lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel) := #[]
  files : Array String := #[]
  paint : Paint := {}
  /-- `eval --comp` and `mutate --comp`. -/
  comp? : Option String := none
  /-- `eval --set`, as written. -/
  sets : Array String := #[]
  /-- `eval --seed`, `quickcheck --seed` and `mutate --seed`. -/
  seed : Nat := 0
  /-- `quickcheck --tests` and `mutate --tests`. -/
  nTests : Nat := 100
  /-- `mutate --by`. -/
  checker : Mutate.By := .solver
  /-- `mutate --mutant`. -/
  mutantIds : Array String := #[]
  /-- `mutate --sample`. -/
  sample? : Option Nat := none
  /-- `mutate --list`. -/
  listOnly : Bool := false

def commands : Array String := #["check", "eval", "fix", "fmt", "mutate", "quickcheck", "trace"]

def options : Array String :=
  #["--timeout", "--dump-smt", "--check", "--ignore", "--tests", "--require", "--color", "--explain", "--help", "--version", "-A", "-W", "-D", "-F",
    "--allow", "--warn", "--deny", "--forbid", "--only", "--skip", "--fmt", "--comp", "--set", "--seed", "--tests",
    "--by", "--mutant", "--sample", "--list"]

def unknownLint (n : String) : Msg :=
  { code? := none, headline := s!"unknown lint `{n}`"
    notes := Fren.Core.removedLintNotes n ++ #[Fren.Core.lintsNote, Fren.Core.groupsNote]
    fixes := (Fren.Core.similarStr n Fren.Core.lintTargetNames).toArray.map fun s =>
      { msg := Fren.Core.similarLintMsg s, replacement := s } }

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
  | "mutate" :: rest => go rest { command := .mutate, paint := p }
  | [] => .error usage
  | c :: _ =>
    if c.startsWith "-" then .error (argError p (unknownOption c))
    else .error (argError p {
      code? := none, headline := s!"unknown command `{c}`",
      notes := #["note: the commands are `check`, `eval`, `fix`, `fmt`, `mutate`, `quickcheck` and `trace`"],
      fixes := (Fren.Core.similarStr c commands).toArray.map fun s => { msg := s!"a command with a similar name exists: `{s}`", replacement := s } })
where
  only (opt : String) (cmd : String) : Except String Args :=
    .error (argError p { code? := none, headline := s!"`{opt}` is an option of `fren {cmd}`" })
  go : List String → Args → Except String Args
    | [], a =>
      if a.files.isEmpty then .error (argError p { code? := none, headline := "no input files" })
      else .ok a
    | "--timeout" :: n :: rest, a =>
      if a.command != .check && a.command != .mutate then only "--timeout" "check` and `fren mutate" else
      match n.toNat? with
      | some t => go rest { a with timeout := t }
      | none => .error (argError p {
          code? := none, headline := s!"invalid timeout `{n}`",
          notes := #["note: the timeout is a whole number of seconds, such as `--timeout 30`"] })
    | "--comp" :: c :: rest, a =>
      if a.command == .eval || a.command == .mutate then go rest { a with comp? := some c } else only "--comp" "eval` and `fren mutate"
    | "--set" :: x :: rest, a =>
      if a.command != .eval then only "--set" "eval"
      else if x.contains '=' then go rest { a with sets := a.sets.push x }
      else .error (argError p {
        code? := none, headline := s!"invalid `--set` value `{x}`"
        notes := #["note: a variable is set as `VAR=VALUE`, such as `--set x=3` or `--set w.ready?=true`"] })
    | "--seed" :: n :: rest, a =>
      if a.command != .eval && a.command != .quickcheck && a.command != .check && a.command != .mutate then
        only "--seed" "check`, `fren eval`, `fren quickcheck` and `fren mutate" else
      match n.toNat? with
      | some k => go rest { a with seed := k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid seed `{n}`",
          notes := #["note: the seed is a whole number, such as `--seed 7`"] })
    | "--tests" :: n :: rest, a =>
      if a.command == .trace then go rest { a with tests := a.tests.push n }
      else if a.command != .quickcheck && a.command != .check && a.command != .mutate then
        only "--tests" "check`, `fren trace`, `fren quickcheck` and `fren mutate" else
      match n.toNat? with
      | some k => go rest { a with nTests := k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid number of tests `{n}`",
          notes := #["note: the number of tests is a whole number, such as `--tests 1000`"] })
    | "--by" :: b :: rest, a =>
      if a.command != .mutate then only "--by" "mutate" else
      match Mutate.By.ofName? b with
      | some k => go rest { a with checker := k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid value `{b}` for `--by`",
          notes := #["note: `--by` is `solver`, `testing` or `both`"]
          fixes := (Fren.Core.similarStr b #["solver", "testing", "both"]).toArray.map fun c =>
            { msg := s!"a value with a similar name exists: `{c}`", replacement := c } })
    | "--mutant" :: m :: rest, a =>
      if a.command == .mutate then go rest { a with mutantIds := a.mutantIds.push m } else only "--mutant" "mutate"
    | "--sample" :: n :: rest, a =>
      if a.command != .mutate then only "--sample" "mutate" else
      match n.toNat? with
      | some k => go rest { a with sample? := some k }
      | none => .error (argError p {
          code? := none, headline := s!"invalid sample size `{n}`",
          notes := #["note: the sample size is a whole number of mutants, such as `--sample 50`"] })
    | "--list" :: rest, a =>
      if a.command == .mutate then go rest { a with listOnly := true } else only "--list" "mutate"
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
      match Fren.Core.LintTarget.ofName? n with
      | some t => go rest { a with onlyLints := a.onlyLints ++ t.members }
      | none => .error (argError p (unknownLint n))
    | "--skip" :: n :: rest, a =>
      if a.command != .fix then only "--skip" "fix" else
      match Fren.Core.LintTarget.ofName? n with
      | some t => go rest { a with skipLints := a.skipLints ++ t.members }
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
    | [opt@"--by"], _ | [opt@"--mutant"], _ | [opt@"--sample"], _
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
    match Fren.Core.LintTarget.ofName? n with
    | some t => .ok { a with lints := a.lints.push (t, lv) }
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

/-- Elaborates the file `file`, with text `chars`, after the state `st` of
the files before it. -/
def elabText (st : State) (file : Nat) (chars : Array Char) (fixing : Array Fren.Core.Lint := #[]) : State :=
  match lex chars with
  | .error e => { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
  | .ok toks =>
    match parse toks with
    | .error e => { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
    | .ok items => (elabFile file chars items fixing |>.run st).2

/-- The state before any file, with the lint levels `lints`. -/
def initialState (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) : State :=
  { cliLevels := Fren.Core.Levels.ofFlags lints }

/-- Elaborates the files at `paths`, whose contents are `srcs`. `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborateSources (paths srcs : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Array (String × Array Char) × State) := do
  let mut files := #[]
  let mut st := initialState lints
  for path in paths, src in srcs do
    let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
    let chars := src.toList.toArray
    st := elabText st files.size chars (if ignored path then #[] else fixing)
    files := files.push (path, chars)
  return (files, ← checkClaims st)

/-- Reads and elaborates the files; `none` if one cannot be read. `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborate (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Option (Array (String × Array Char) × State)) := do
  let mut srcs := #[]
  for path in paths do
    let some src ← readSpec p path | return none
    srcs := srcs.push src
  return some (← elaborateSources paths srcs lints fixing ignored)

/-- Prints the count of static errors, and the pointer to `--explain` for
the codes of `diags`. -/
def printErrorCount (p : Paint) (errors : Nat) (diags : Array Diag) (what := "check") : IO Unit := do
  IO.eprintln (Fren.Core.header .error
    { code? := none, headline := s!"could not {what} due to {errors} previous error{if errors == 1 then "" else "s"}" } p)
  IO.eprintln ""
  printExplainHint (diags.map (·.msg))

/-- Reads and elaborates the files, printing any static errors. -/
def load (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) :
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

/-- Tests `c`, the evaluator's `ec`, on `n` random behaviours from `seed`
(`Reqs/Eval#fren-quickcheck`). -/
def testReport (sp : Eval.Spec) (ec : Eval.Comp) (c : CComp) (global : Bool) (seed n : Nat) : Eval.Report :=
  -- Each comp has its own stream, so a run does not depend on the others.
  let rng : Eval.Rng := ⟨Eval.mix seed.toUInt64 (hash c.path)⟩
  (if global then sp.quickGlobal ec n else sp.quickComp ec n).run' rng

/-- Tests the comp or global expectation `c`, whose counterpart is `ec`
(`Reqs/Eval#fren-quickcheck`), and prints what testing found about the
checks that `keep` selects: their results, and those that are not run
are dropped. Returns the results and the messages printed. -/
def testComp (args : Args) (files : Array (String × Array Char)) (sp : Eval.Spec) (c : CComp) (ec : Eval.Comp)
    (global : Bool) (keep : Fren.Core.CheckResult → Bool) (byCheck : Bool := false) :
    IO (Array Fren.Core.CheckResult × Array Msg) := do
  let rep := testReport sp ec c global args.seed args.nTests
  let results := rep.results.filter keep
  let mut shown := #[]
  let subject := s!"`{Fren.Core.showComp (if global then c.path ++ (c.props[0]?.map (·.name)).getD .anonymous else c.path)}`"
  for r in results do
    -- Inconclusive results are reported below, once for the comp.
    if r.verdict == .fail then shown := shown ++ (← printResult args.paint files c r)
  let warn (msg : Msg) : IO Unit := printDiag args.paint files { file := c.file, span := c.span, severity := .warning, msg }
  if let some input := rep.noOutputs? then
    -- It explains why the checks it selects were not reached, too.
    if !results.isEmpty then
      let msg := Fren.Core.noOutputsMsg subject input byCheck
      warn msg
      shown := shown.push msg
  else if rep.untested && !results.isEmpty then
    let msg := Fren.Core.untestedMsg subject args.nTests byCheck
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
    let msg := Fren.Core.untriggeredMsg what args.nTests byCheck
    printDiag args.paint files { file := c.file, span, severity := .warning, msg }
    shown := shown.push msg
  return (results, shown)

/-- Whether the result `r` of testing the refinement `c` is about its
obligation (`Reqs/Lang/Refinement#the-obligation`): of the instances, only
the instance of the concrete component, since the abstract component's
instances are hypotheses there. -/
def refinementKeeps (c : CComp) (r : Fren.Core.CheckResult) : Bool :=
  Fren.Core.refinementRuns r.kind && (r.kind != .inst || r.prop? == c.insts[0]?.map (·.name))

/-- The solver's results for `c`, a global expectation if `global`, with
each model confirmed by the evaluator's `spec?` (`Reqs/Eval#confirming-models`);
the results that a refuted model is about, with their internal errors; and
an internal error if the evaluator has no counterpart of `c`. `prelude` is
`st`'s, indexed (`Prelude.ofDecls`). -/
def solveComp (st : State) (prelude : Prelude) (spec? : Except String Eval.Spec) (c : CComp) (global : Bool) (kinds : Array Fren.Core.CheckKind)
    (timeout : Nat) (dump? : Option (String → IO Unit) := none) :
    IO (Array Fren.Core.CheckResult × Array (Fren.Core.CheckResult × Msg) × Option Msg) := do
  let bk := backend prelude st.datatypes c timeout dump? (st.usesStrings || st.usesSeqs) (st.usesSets || st.usesSeqs) st.usesProjection
  let log ← IO.mkRef #[]
  -- The checks set to testing are not asked of the solver (`check::by_testing`).
  let (raw, missing?) ← match spec? with
    | .ok sp => match sp.counterpart? c global with
      | some ec =>
        let (core, ks) := (pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start))).untested c.tested kinds
        pure (← Fren.Core.checkComp (fun k => confirming sp ec k log (bk k)) core ks, none)
      | none =>
        let (core, ks) := (toCore c).untested c.tested kinds
        pure (← Fren.Core.checkComp bk core ks,
          some (Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`"))
    | .error _ =>
      let (core, ks) := (toCore c).untested c.tested kinds
      pure (← Fren.Core.checkComp bk core ks, none)
  let (results, refuted) := applyRefutations raw (← log.get)
  return (results, refuted, missing?)

/-- Which results of testing `c` `fren check` keeps, for the checks of
kinds `kinds` set to testing (`Reqs/Check#checking-by-testing`); for a
refinement, only those about its obligation. -/
def testedKeeps (c : CComp) (kinds : Array Fren.Core.CheckKind) (refinement : Bool) (r : Fren.Core.CheckResult) : Bool :=
  kinds.contains r.kind && c.tested.covers r && Fren.Core.runOf r.kind true == .byTesting
    && (!refinement || refinementKeeps c r)

/-- Runs `fren check`, printing diagnostics and the summary to stderr and
any solver queries to stdout; returns the exit code. -/
def check (args : Args) : IO UInt32 := do
  let some (files, st) ← load args.paint args.files args.lints | return exitCode false none
  let mut all := #[]
  -- Warnings from lints, already printed.
  let mut shown := st.diags.map (·.msg)
  -- Each comp, global expectation and refinement (`Reqs/Lang/Refinement`),
  -- with the checks that run on it.
  let todo := (Mutate.todo st).map fun t => (t.comp, t.global, t.kinds, t.refinement)
  let prelude := Prelude.ofDecls st.prelude
  -- Each model is confirmed with the evaluator (`Reqs/Eval#confirming-models`).
  let spec? := specOf files
  let mut internal := #[]
  let mut byTesting := 0
  if let .error e := spec? then
    internal := internal.push (Msg.internal s!"the evaluator cannot read the spec: {e}")
    printDiag args.paint files { file := 0, span := default, msg := internal.back! }
  for (c, global, kinds, refinement) in todo do
    let n ← IO.mkRef 0
    let dump? := if args.dumpSmt then some fun script => do
        n.modify (· + 1)
        IO.print s!"; {c.path}: query {← n.get}\n{script}(check-sat)\n(reset)\n\n"
      else none
    let (results, refuted, missing?) ← solveComp st prelude spec? c global kinds args.timeout dump?
    if let some msg := missing? then
      internal := internal.push msg
      printDiag args.paint files { file := c.file, span := c.span, msg }
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
          let (tested, msgs) ← testComp args files sp c ec global (testedKeeps c kinds refinement) (byCheck := true)
          shown := shown ++ msgs
          all := all ++ tested
          byTesting := byTesting + (tested.filter (·.verdict == .pass)).size
      -- The evaluator's internal error, printed above, explains why the
      -- checks set to testing are missing from the summary.
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
  for (c, global, refinement) in st.comps.map (·, false, false) ++ st.globals.map (·, true, false)
      ++ st.refinements.map (·, false, true) do
    let some ec := sp.counterpart? c global
      | let msg := Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`"
        printDiag args.paint files { file := c.file, span := c.span, msg }
        sevs := sevs.push .error
    let keep (r : Fren.Core.CheckResult) := !refinement || refinementKeeps c r
    let (results, msgs) ← testComp args files sp c ec global keep
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

/-- The most passes `fren fix` makes, in case two fixes undo each other. -/
def maxFixPasses : Nat := 10

/-- Runs `fren fix`: rewrites the files to fix the lints that it can, or
with `--check`, prints the diffs to stdout, painted with `out`; prints the
lints that it does not fix to stderr; returns the exit code
(`lint::fix_exit`). -/
def fix (args : Args) (out : Paint) : IO UInt32 := do
  let fixing := Fren.Core.Lint.all.filter (Fren.Core.fixSelected args.onlyLints args.skipLints)
  let ignored := Fmt.ignored args.ignore
  let paths := args.files
  let mut srcs := #[]
  for path in paths do
    let some src ← readSpec args.paint path | return Fren.Core.fixExit args.diffOnly false false
    srcs := srcs.push src
  let original := srcs
  let (files, st) ← elaborateSources paths srcs args.lints fixing ignored
  let errors := st.diags.filter fun d => d.severity == .error && d.lint?.isNone
  if !errors.isEmpty then
    -- Nothing is fixed.
    for d in st.diags do printDiag args.paint files d
    printErrorCount args.paint (st.diags.filter (·.severity == .error)).size st.diags "fix"
    return Fren.Core.fixExit args.diffOnly false false
  -- One fix can overlap another, or leave something that another lint
  -- fixes, so the passes go on until no edit is left (`Reqs/Lint#fixing-lints`).
  let mut pass := (files, st)
  let mut nFixed := paths.map fun _ => 0
  -- Whether the first pass's fixes were kept.
  let mut firstKept := false
  for k in [0:maxFixPasses] do
    let (files, st) := pass
    if st.edits.isEmpty then break
    let next := (files.zip srcs).mapIdx fun i ((_, text), src) =>
      applyFileEdits src text (st.edits.filterMap fun (f, e) => if f == i then some e else none)
    let (files', st') ← elaborateSources paths next args.lints fixing ignored
    -- A fix that made a static error is not kept.
    if st'.diags.any fun d => d.severity == .error && d.lint?.isNone then break
    if k == 0 then firstKept := true
    nFixed := nFixed.mapIdx fun i n => n + (st.diags.filter fun d => d.fixed && d.file == i).size
    srcs := next
    pass := (files', st')
  -- What is left, in the files the user has afterwards: as fixed, or with
  -- `--check`, as given.
  -- If the first pass's fixes were not kept, nothing is fixed.
  let (files, left) ← if args.diffOnly then pure (files, st.diags.filter fun d => !(firstKept && d.fixed)) else do
    let (files, st) ← elaborateSources paths srcs args.lints #[] ignored
    pure (files, st.diags)
  for d in left do printDiag args.paint files d
  let mut unchanged := true
  for path in paths, src in original, fixed in srcs, n in nFixed do
    let format := args.fmtAfter && !ignored path
    -- The file parsed, and fixing it keeps it parsing.
    let new := if format then (Fmt.formatFile path fixed).toOption.getD fixed else fixed
    if new == src then continue
    unchanged := false
    if args.diffOnly then IO.print (Fmt.diff out path src new)
    else
      IO.FS.writeFile path new
      IO.eprintln (if n == 0 then s!"formatted {path}" else s!"fixed {path} ({n} lint{if n == 1 then "" else "s"})")
  printExplainHint (left.map (·.msg))
  return Fren.Core.fixExit args.diffOnly true unchanged

/-- The results of one way of checking (`--by`) the spec's components,
global expectations and refinements, by `Mutate.Todo.key`, as far as they
have been needed. -/
abbrev Baseline := IO.Ref (Std.HashMap String (Array Fren.Core.CheckResult))

/-- The mutants of the files, as elaborated, with the lint levels `lints`,
and the state before each file, from which a mutant of it is elaborated. -/
def mutantsOf (files : Array (String × Array Char)) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) :
    Array State × Array Mutate.Mutant := Id.run do
  let mut before := #[]
  let mut st := initialState lints
  let mut all := #[]
  for (path, chars) in files, i in [0:files.size] do
    before := before.push st
    st := elabText st i chars
    if let .ok toks := lex chars then
      if let .ok items := parse toks then all := all ++ Mutate.ofFile { file := i, path, chars, toks } items
  return (before, all)

/-- The state of the files with the mutant `m` applied, from the states
`before` each file. -/
def mutantState (files : Array (String × Array Char)) (before : Array State) (m : Mutate.Mutant) : State := Id.run do
  let mut st := before[m.file]?.getD {}
  for (_, chars) in files.extract m.file, j in [m.file:files.size] do
    st := elabText st j (if j == m.file then m.apply chars else chars)
  return st

/-- Runs `fren mutate` (`Reqs/Mutate`), printing each surviving mutant and
the summary to stderr and the kill rates to stdout, or with `--list`, the
mutants to stdout; returns the exit code. -/
def mutate (args : Args) : IO UInt32 := do
  let p := args.paint
  let fail (msg : Msg) : IO UInt32 := do IO.eprint (argError p msg); return 2
  let some (files, st) ← load p args.files args.lints | return exitCode false none
  let (before, all) := mutantsOf files args.lints
  let comp? := args.comp?.map fun t => (t.splitOn "::").foldl Lean.Name.mkStr .anonymous
  if let some c := comp? then
    unless st.comps.any (·.path == c) do
      return ← fail { code? := none, headline := s!"no component `{Fren.Core.showComp c}`"
                      notes := #[s!"note: the components are {Fren.Core.showNameList (st.comps.map (·.path))}"] }
  for id in args.mutantIds do
    unless all.any (·.id == id) do
      return ← fail { code? := none, headline := s!"no mutant `{id}`"
                      notes := #["note: `fren mutate --list` lists the mutants"]
                      fixes := (Fren.Core.similarStr id (all.map (·.id))).toArray.map fun s =>
                        { msg := s!"a mutant with a similar identifier exists: `{s}`", replacement := s } }
  let selected := Mutate.select all comp? args.mutantIds args.sample? args.seed
  if args.listOnly then
    for m in selected do
      let (path, chars) := files[m.file]!
      let (line, col) := Fren.Core.position chars m.span.start
      IO.println s!"{m.id} {path}:{line}:{col} {m.change}"
    return 0
  -- The results of testing `c`, kept by `keep`.
  let testing (spec? : Except String Eval.Spec) (c : CComp) (global : Bool) (keep : Fren.Core.CheckResult → Bool) :
      Array Fren.Core.CheckResult :=
    match spec? with
    | .ok sp => match sp.counterpart? c global with
      | some ec => (testReport sp ec c global args.seed args.nTests).results.filter keep
      | none => #[]
    | .error _ => #[]
  -- As `fren check` checks `c`: with the solver, and the checks set to
  -- testing by testing; with the internal errors, each at its place in `c`.
  let solve (s : State) (spec? : Except String Eval.Spec) (t : Mutate.Todo) :
      IO (Array Fren.Core.CheckResult × Array (Span × Msg)) := do
    let (rs, refuted, missing?) ← solveComp s (Prelude.ofDecls s.prelude) spec? t.comp t.global t.kinds args.timeout
    let tested := if t.comp.tested.any then testing spec? t.comp t.global (testedKeeps t.comp t.kinds t.refinement) else #[]
    let errors := refuted.map fun (r, msg) =>
      ((r.prop?.bind fun n => t.comp.props.find? (·.name == n)).map (·.span) |>.getD t.comp.span, msg)
    return (rs ++ tested, missing?.toArray.map (t.comp.span, ·) ++ errors)
  -- As `fren quickcheck` tests `c`.
  let test (_ : State) (spec? : Except String Eval.Spec) (t : Mutate.Todo) :
      IO (Array Fren.Core.CheckResult × Array (Span × Msg)) :=
    pure (testing spec? t.comp t.global fun r => !t.refinement || refinementKeeps t.comp r, #[])
  let spec? := specOf files
  if let .error e := spec? then
    printDiag p files { file := 0, span := default, msg := Msg.internal s!"the evaluator cannot read the spec: {e}" }
  -- What each component's checks read in the spec. The spec's own results
  -- are computed only for components that some mutant changes.
  let originals : Std.HashMap String (Mutate.Todo × String) :=
    (Mutate.todo st).foldl (init := {}) fun m t => m.insert t.key (t, Mutate.fingerprint st.preludeText t.comp)
  let solved : Baseline ← IO.mkRef {}
  let tested : Baseline ← IO.mkRef {}
  let shown ← IO.mkRef (#[] : Array Msg)
  let sevs ← IO.mkRef (if spec?.toOption.isNone then #[Fren.Core.Severity.error] else #[])
  -- Whether one way of checking kills the mutant `st'`, and whether some
  -- check was inconclusive on it, checking only the components it changes;
  -- `run s spec? t` checks `t` of the spec `s`. Internal errors about the
  -- spec are printed as `fren check` prints them, and those about the
  -- mutant given to `onMutant`.
  let killedBy (base : Baseline) (st' : State) (spec'? : Except String Eval.Spec)
      (run : State → Except String Eval.Spec → Mutate.Todo → IO (Array Fren.Core.CheckResult × Array (Span × Msg)))
      (onMutant : Msg → IO Unit) : IO (Bool × Bool) := do
    let mut inconclusive := false
    for t in Mutate.todo st' do
      let some (t₀, fp) := originals[t.key]? | continue
      if Mutate.fingerprint st'.preludeText t.comp == fp then continue
      let rs ← match (← base.get)[t.key]? with
        | some rs => pure rs
        | none =>
          let (rs, errors) ← run st spec? t₀
          for (span, msg) in errors do
            printDiag p files { file := t₀.comp.file, span, msg }
            shown.modify (·.push msg)
            sevs.modify (·.push .error)
          base.modify (·.insert t.key rs)
          pure rs
      let (rs', errors) ← run st' spec'? t
      for (_, msg) in errors do onMutant msg
      let rs := Mutate.keyed rs
      let rs' := Mutate.keyed rs'
      if Mutate.kills rs rs' then return (true, inconclusive)
      inconclusive := inconclusive || Mutate.inconclusive rs rs'
    return (false, inconclusive)
  let mut tallies : Std.HashMap Lean.Name Mutate.Tally := {}
  for m in selected do
    let files' := files.modify m.file fun (path, chars) => (path, m.apply chars)
    let st' := mutantState files before m
    -- What to report about the mutant, at its span.
    let reports ← IO.mkRef (#[] : Array (Msg × Fren.Core.Severity))
    let report (msg : Msg) (severity := Fren.Core.Severity.warning) : IO Unit := reports.modify (·.push (msg, severity))
    let group := m.comp?.getD m.item
    let mut tally := tallies.getD group {}
    let errors := st'.diags.filter (·.severity == .error)
    if !errors.isEmpty then
      -- A denied lint can reject a mutant; nothing else should.
      if let some e := errors.find? (·.lint?.isNone) then
        report (Msg.internal s!"the mutant `{m.id}` has a static error: {e.msg.headline}") .error
      tally := tally.add .unviable
    else
      let spec'? := specOf files'
      if let .error e := spec'? then
        report (Msg.internal s!"the evaluator cannot read the mutant `{m.id}`: {e}") .error
      let onMutant (msg : Msg) := report { msg with notes := msg.notes.push s!"note: on the mutant `{m.id}`" } .error
      let (bySolver, inconclusive₁) ← if args.checker.solves then killedBy solved st' spec'? solve onMutant
        else pure (false, false)
      let (byTesting, inconclusive₂) ← if args.checker.tests then killedBy tested st' spec'? test onMutant
        else pure (false, false)
      let killed := bySolver || byTesting
      -- Short, whatever `--timeout` is, even 0, which means none.
      let equivalent? ← if killed then pure (some false) else Mutate.equivalent st st' Mutate.equivalenceTimeout
      let outcome := Mutate.outcome true killed (equivalent? == some true)
      tally := tally.add outcome
      if outcome == .survived then report (Mutate.survivedMsg m equivalent?.isNone (inconclusive₁ || inconclusive₂))
      if args.checker == .both && Mutate.missed bySolver byTesting then
        tally := { tally with missed := tally.missed + 1 }
        report (Mutate.missedMsg m args.nTests)
    tallies := tallies.insert group tally
    let (path, chars) := files[m.file]!
    for (msg, severity) in ← reports.get do
      printAt p path chars severity msg { start := m.span.start, stop := m.span.stop }
      shown.modify (·.push msg)
      sevs.modify (·.push severity)
  -- Each check once, though both ways of checking ran it.
  let notPassing := ((← solved.get).toArray ++ (← tested.get).toArray).foldl (init := ({} : Std.HashSet String)) fun acc (k, rs) =>
    (Mutate.keyed rs).foldl (init := acc) fun acc (rk, r) =>
      if r.verdict != .pass then acc.insert s!"{k}|{rk}" else acc
  let notPassing := notPassing.size
  if notPassing > 0 then
    IO.eprint (Fren.Core.renderPlain .info
      { code? := none, headline := s!"{Mutate.plural notPassing "check"} of the spec {if notPassing == 1 then "does" else "do"} not pass, \
          and so {if notPassing == 1 then "kills" else "kill"} no mutant"
        notes := #["help: run `fren check` or `fren quickcheck` to see them"] } p)
  let groups := tallies.toArray.qsort (Fren.Core.showComp ·.1 < Fren.Core.showComp ·.1)
  for (g, t) in groups do IO.println (t.line (Fren.Core.showComp g) (args.checker == .both))
  let total : Mutate.Tally := groups.foldl (fun acc (_, t) => acc.merge t) {}
  IO.eprintln s!"fren: {Mutate.plural selected.size "mutant"}: {total.killed} killed, {total.survived} survived, \
    {total.equivalent} equivalent, {total.unviable} unviable{if args.checker == .both then s!", {total.missed} missed by testing" else ""}"
  let shown ← shown.get
  let sevs ← sevs.get
  if shown.any (·.code?.isSome) then
    IO.eprintln ""
    printExplainHint shown
  return Mutate.exitCode true (sevs.contains .warning) (sevs.contains .error)

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
      | .mutate => mutate a
    | .error msg => IO.eprint (if msg.endsWith "\n" then msg else msg ++ "\n"); return 2

end FrenCli
