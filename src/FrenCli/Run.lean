-- keep-sorted start
import FrenCli.Color
import FrenCli.Enumerate
import FrenCli.Exit
import FrenCli.Fmt
import FrenCli.MutateRun
import FrenCli.Quick
import FrenCli.Same
import FrenCli.Smt
import FrenCore.Literate
import FrenCoreCodes
-- keep-sorted end

/-!
# Running `fren`

```
fren check [--timeout SECONDS] [--resource-limit N] [--examples N] [--jobs N] [--dump-smt] [--timings] [--tests N]
    [--seed N] [--query-cache DIR] [--verify-query-cache DIR] [-A|-W|-D|-F LINT]... FILE...
fren trace [--tests GLOB]... [--require LEVEL] [-A|-W|-D|-F LINT]... FILE...
fren fmt [--check] [--ignore GLOB]... FILE...
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
fren eval --proc PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [--jobs N] [-A|-W|-D|-F LINT]... FILE...
fren mutate [--by solver|testing|both] [--proc PATH] [--mutant ID]... [--diff PATCH] [--sample N] [--seed N]
    [--shard K/N] [--list] [--timeout SECONDS] [--resource-limit N] [--examples N] [--tests N]
    [-A|-W|-D|-F LINT]... FILE...
fren --explain CODE
```

`-A`, `-W`, `-D` and `-F` (or `--allow`, `--warn`, `--deny` and
`--forbid`) set the level of a lint (`Reqs/Lint`), as in rustc.

Every form also takes `--color WHEN`, as rustc does: `always`, `never`, or
`auto` (the default), which colours output written to a terminal unless the
environment variable `NO_COLOR` is set or `TERM` is `dumb`.

Files are processed in order, sharing one set of modules. `check` then
checks every procedure and global expectation; `trace` reports the
evidence for every procedure (`Reqs/Trace`). Messages are rendered as rustc
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
  "usage: fren check [--timeout SECONDS] [--resource-limit N] [--examples N] [--jobs N] [--dump-smt] [--timings] [--tests N]\n              \
  [--seed N] [--query-cache DIR] [--verify-query-cache DIR] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren trace [--tests GLOB]... [--require LEVEL] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren fmt [--check] [--ignore GLOB]... [--color WHEN] FILE...\n       \
  fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren eval --proc PATH [--set VAR=VALUE]... [--seed N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren quickcheck [--tests N] [--seed N] [--jobs N] [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren mutate [--by solver|testing|both] [--proc PATH] [--mutant ID]... [--diff PATCH] [--sample N] [--seed N]\n              \
  [--shard K/N] [--list] [--timeout SECONDS] [--resource-limit N] [--examples N] [--tests N]\n              \
  [LINT OPTIONS] [--color WHEN] FILE...\n       \
  fren --explain CODE\n\n\
  `check` checks Fren specs. Exit status: 0 all checks passed, 1 some check\n\
  failed, 2 the checks could not run, 3 no failures but some check was\n\
  inconclusive, some constraint redundant or some lint warned. `--dump-smt` writes each solver\n\
  query to stdout, as SMT-LIB; diagnostics go to stderr. `--tests N` and\n\
  `--seed N` are as for `quickcheck`, for checks set to testing.\n\
  `--timeout` limits each solver query's wall-clock time (default 10), and\n\
  `--resource-limit` its work, in cvc5's resource units, which unlike time\n\
  does not depend on the machine's load (default none); 0 is no limit.\n\
  `--examples N` shows at most N notes of guarantees that force an output\n\
  to different values, for each unrealizable component (default 1), or\n\
  all of them with `all`.\n\
  `--jobs N` checks N procedures at once (default: the number of cores),\n\
  with the same output as one at a time. `--timings` then reports how long\n\
  each procedure's checks took, slowest first, on stderr.\n\
  `--query-cache DIR` keeps the solver's answers in DIR, and answers a\n\
  query asked before from it; `--verify-query-cache DIR` instead fails if\n\
  the solver's answer contradicts DIR's.\n\n\
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
  `check`. `--seed N` sets where the random search starts (default 0).\n\
  `--jobs N` tests N procedures at once, as for `check`.\n\n\
  `mutate` makes small changes to the spec's constraints and definitions,\n\
  checks each changed spec (a mutant), and reports the mutants that no check\n\
  rejects. `--by` checks them with the solver (the default), by testing, or\n\
  both. `--proc PATH` and `--mutant ID` select mutants, and `--diff PATCH`\n\
  those of the items whose lines a unified diff (`-` for stdin), such as\n\
  `git diff -U0`, adds or changes. `--sample N` takes N of them, chosen by\n\
  `--seed`, and `--shard K/N` the Kth of N parts of those, from 0.\n\
  `--list` lists them without checking them.\n\
  Exit status as for `check`, where each surviving mutant is a warning.\n\n\
  `--explain` explains an error code, such as F0105.\n\n\
  `--color WHEN` colours the output: auto (the default: if it is a terminal),\n\
  always or never."

def version : String := "fren 0.1.0"

/-- Prints a message about a file to stderr, then a blank line, as rustc
does. `starts` is `Fren.Core.lineStarts src`. -/
def printAt (p : Paint) (path : String) (src : Array Char) (severity : Fren.Core.Severity) (msg : Msg)
    (range : Fren.Core.Range) (starts : Array Nat := Fren.Core.lineStarts src) : IO Unit :=
  IO.eprintln ({ level := severity, msg, range : Fren.Core.Diagnostic }.render path src p starts)

/-- Prints `d`, about one of `files`, whose line starts `starts?` gives, if
it is given (`linesOf`). -/
def printDiag (p : Paint) (files : Array (String × Array Char)) (d : Diag)
    (starts? : Option (Array (Thunk (Array Nat))) := none) : IO Unit := do
  let (path, src) := files[d.file]!
  let starts := match starts? with
    | some ss => ss[d.file]!.get
    | none => Fren.Core.lineStarts src
  printAt p path src d.severity d.msg { start := d.span.start, stop := d.span.stop } starts

/-- The line starts of each of `files`, each computed when first needed,
for printing many diagnostics about them (`printDiag`). -/
def linesOf (files : Array (String × Array Char)) : Array (Thunk (Array Nat)) :=
  files.map fun (_, src) => Thunk.mk fun _ => Fren.Core.lineStarts src

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
  /-- `--examples`: at most this many clash notes for each realizability
  conflict, `none` for `all` (`Reqs/Cli#forced-outputs`). -/
  examples : Option Nat := some 1
  /-- `--timeout` and `--resource-limit` (`Reqs/Cli#limits`). -/
  limits : Limits := {}
  /-- `check --jobs` and `quickcheck --jobs`; by default, the number of cores
  (`Reqs/Cli#parallel-checking`). -/
  jobs? : Option Nat := none
  dumpSmt : Bool := false
  /-- `check --timings` (`Reqs/Cli#timings`). -/
  timings : Bool := false
  /-- `check --query-cache` and `check --verify-query-cache` (`Reqs/Cli#query-cache`). -/
  queryCache? : Option String := none
  verifyQueryCache? : Option String := none
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
  /-- `eval --proc` and `mutate --proc`. -/
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
  /-- `mutate --diff`: the patch's path, or `-`. -/
  diff? : Option String := none
  /-- `mutate --shard K/N`, as `(K, N)`. -/
  shard? : Option (Nat × Nat) := none
  /-- `mutate --list`. -/
  listOnly : Bool := false

def commands : Array String := #["check", "eval", "fix", "fmt", "mutate", "quickcheck", "trace"]

def options : Array String :=
  #["--timeout", "--resource-limit", "--examples", "--jobs", "--dump-smt", "--timings", "--query-cache", "--verify-query-cache", "--check", "--ignore", "--tests", "--require", "--color", "--explain", "--help", "--version", "-A", "-W", "-D", "-F",
    "--allow", "--warn", "--deny", "--forbid", "--only", "--skip", "--fmt", "--proc", "--set", "--seed", "--tests",
    "--by", "--mutant", "--sample", "--list", "--diff", "--shard"]

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
      | some t => go rest { a with limits.timeoutSecs := t }
      | none => .error (argError p {
          code? := none, headline := s!"invalid timeout `{n}`",
          notes := #["note: the timeout is a whole number of seconds, such as `--timeout 30`"] })
    | "--resource-limit" :: n :: rest, a =>
      if a.command != .check && a.command != .mutate then only "--resource-limit" "check` and `fren mutate" else
      match n.toNat? with
      | some r => go rest { a with limits.resources := r }
      | none => .error (argError p {
          code? := none, headline := s!"invalid resource limit `{n}`",
          notes := #["note: the resource limit is a whole number of cvc5's resource units, such as `--resource-limit 100000`"] })
    | "--examples" :: n :: rest, a =>
      if a.command != .check && a.command != .mutate then only "--examples" "check` and `fren mutate" else
      match n, n.toNat? with
      | "all", _ => go rest { a with examples := none }
      | _, some k => go rest { a with examples := some k }
      | _, none => .error (argError p {
          code? := none, headline := s!"invalid number of examples `{n}`",
          notes := #["note: the number of examples is a whole number, such as `--examples 3`, or `all`"] })
    | "--jobs" :: n :: rest, a =>
      if a.command != .check && a.command != .quickcheck then only "--jobs" "check` and `fren quickcheck" else
      match n.toNat? with
      | some j@(_ + 1) => go rest { a with jobs? := some j }
      | _ => .error (argError p {
          code? := none, headline := s!"invalid number of jobs `{n}`",
          notes := #["note: the number of jobs is a whole number of at least 1, such as `--jobs 4`"] })
    | "--proc" :: c :: rest, a =>
      if a.command == .eval || a.command == .mutate then go rest { a with comp? := some c } else only "--proc" "eval` and `fren mutate"
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
    | "--diff" :: d :: rest, a =>
      if a.command == .mutate then go rest { a with diff? := some d } else only "--diff" "mutate"
    | "--shard" :: k :: rest, a =>
      if a.command != .mutate then only "--shard" "mutate" else
      match Mutate.shard? k with
      | some s => go rest { a with shard? := some s }
      | none => .error (argError p {
          code? := none, headline := s!"invalid shard `{k}`",
          notes := #["note: a shard is `K/N`, the `K`th of `N` from 0, with `K < N`, such as `--shard 0/4`"] })
    | "--dump-smt" :: rest, a =>
      if a.command == .check then go rest { a with dumpSmt := true }
      else only "--dump-smt" "check"
    | "--timings" :: rest, a =>
      if a.command == .check then go rest { a with timings := true }
      else only "--timings" "check"
    | "--query-cache" :: d :: rest, a =>
      if a.command == .check then go rest { a with queryCache? := some d }
      else only "--query-cache" "check"
    | "--verify-query-cache" :: d :: rest, a =>
      if a.command == .check then go rest { a with verifyQueryCache? := some d }
      else only "--verify-query-cache" "check"
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
    | [opt@"--timeout"], _ | [opt@"--resource-limit"], _ | [opt@"--examples"], _ | [opt@"--jobs"], _ | [opt@"--tests"], _ | [opt@"--ignore"], _ | [opt@"--require"], _
    | [opt@"--only"], _ | [opt@"--skip"], _
    | [opt@"--proc"], _ | [opt@"--set"], _ | [opt@"--seed"], _
    | [opt@"--by"], _ | [opt@"--mutant"], _ | [opt@"--sample"], _ | [opt@"--diff"], _ | [opt@"--shard"], _
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

/-- Why a file could not be read. -/
def readError : IO.Error → String
  | .noFileOrDirectory .. => "no such file or directory"
  | .permissionDenied .. => "permission denied"
  | .inappropriateType .. => "it is a directory"
  | e => toString e

/-- Reads a file, or prints why it could not. -/
def readSpec (p : Paint) (path : String) : IO (Option String) := do
  try return some (← IO.FS.readFile path) catch e =>
    let why := readError e
    IO.eprint (Fren.Core.renderPlain .error { code? := none, headline := s!"could not read `{path}`: {why}" } p)
    return none

/-- Elaborates the file `file`, with text `chars`, after the state `st` of
the files before it. -/
def elabText (st : State) (file : Nat) (chars : Array Char) (fixing : Array Fren.Core.Lint := #[]) : State :=
  match lexWithComments chars with
  | .error e => { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
  | .ok (toks, comments) =>
    match parseItems toks chars with
    | .error e => { st with diags := st.diags.push { file, span := e.span, msg := e.msg } }
    | .ok (items, starts) =>
      (elabFile file chars items starts (trailingCommas toks) (literalLints chars toks comments) fixing |>.run st).2

/-- A file's tokens, items, where each item starts, and the lints of its
literals and comments (`literalLints`), as `elabText` reads them, or the
error, at its span, of the lexer or else of the parser. -/
abbrev Parsed := Except (Span × Msg) (Array Token × Array Item × Array Nat × Array (Fren.Core.Lint × Span × Msg))

/-- The file with text `chars`, lexed and parsed. -/
def parseText (chars : Array Char) : Parsed :=
  match lexWithComments chars with
  | .error e => .error (e.span, e.msg)
  | .ok (toks, comments) => match parseItems toks chars with
    | .error e => .error (e.span, e.msg)
    | .ok (items, starts) => .ok (toks, items, starts, literalLints chars toks comments)

/-- `elabText st file chars`, where `p` is `parseText chars`: the same
cases, after the same lexing and parsing, so that a file parsed once can
be elaborated after several states. -/
def elabParsed (st : State) (file : Nat) (chars : Array Char) (p : Parsed) : State :=
  match p with
  | .error (span, msg) => { st with diags := st.diags.push { file, span, msg } }
  | .ok (toks, items, starts, found) => (elabFile file chars items starts (trailingCommas toks) found |>.run st).2

/-- The state before any file, with the lint levels `lints`. -/
def initialState (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) : State :=
  ({ cliLevels := Fren.Core.Levels.ofFlags lints } : State).withPrelude

/-- Elaborates the files at `paths`, whose contents are `srcs`, with the
state before each file and after the last, before the claims are checked,
from which `fren mutate` elaborates its mutants (`mutantsWith`). `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborateSourcesBefore (paths srcs : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Array (String × Array Char) × Array State × State) := do
  let mut files := #[]
  let mut states := #[]
  let mut st := initialState lints
  for path in paths, src in srcs do
    let src := if Fren.Core.isMarkdownFile path then Fren.Core.unwrapMarkdown src else src
    let chars := src.toList.toArray
    states := states.push st
    st := elabText st files.size chars (if ignored path then #[] else fixing)
    files := files.push (path, chars)
  return (files, states.push st, ← checkClaims st)

/-- Elaborates the files at `paths`, whose contents are `srcs`. `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborateSources (paths srcs : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Array (String × Array Char) × State) := do
  let (files, _, st) ← elaborateSourcesBefore paths srcs lints fixing ignored
  return (files, st)

/-- Reads and elaborates the files, with the states of
`elaborateSourcesBefore`; `none` if one cannot be read. `fren fix` fixes
the lints `fixing` in the files that `ignored` does not match. -/
def elaborateBefore (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Option (Array (String × Array Char) × Array State × State)) := do
  let mut srcs := #[]
  for path in paths do
    let some src ← readSpec p path | return none
    srcs := srcs.push src
  return some (← elaborateSourcesBefore paths srcs lints fixing ignored)

/-- Reads and elaborates the files; `none` if one cannot be read. `fren fix`
fixes the lints `fixing` in the files that `ignored` does not match. -/
def elaborate (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel))
    (fixing : Array Fren.Core.Lint := #[]) (ignored : String → Bool := fun _ => false) :
    IO (Option (Array (String × Array Char) × State)) := do
  return (← elaborateBefore p paths lints fixing ignored).map fun (files, _, st) => (files, st)

/-- Prints that the static errors stopped the command, and the pointer to
`--explain` for the codes of `diags`. -/
def printStopped (p : Paint) (diags : Array Diag) (what := "check") : IO Unit := do
  IO.eprintln (Fren.Core.header .error
    { code? := none, headline := Fren.Core.couldNotHeadline what } p)
  IO.eprintln ""
  printExplainHint (diags.map (·.msg))

/-- Reads and elaborates the files, printing any static errors, with the
states of `elaborateSourcesBefore`. -/
def loadBefore (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) :
    IO (Option (Array (String × Array Char) × Array State × State)) := do
  let some (files, states, st) ← elaborateBefore p paths lints | return none
  let starts := linesOf files
  for d in st.diags do printDiag p files d starts
  let errors := st.diags.filter (·.severity == .error) |>.size
  if errors > 0 then
    printStopped p st.diags
    return none
  return some (files, states, st)

/-- Reads and elaborates the files, printing any static errors. -/
def load (p : Paint) (paths : Array String) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) :
    IO (Option (Array (String × Array Char) × State)) := do
  return (← loadBefore p paths lints).map fun (files, _, st) => (files, st)

/-- Prints the messages of result `r` of `c`, at the positions of the items
they are about; returns them. -/
def printResult (p : Paint) (files : Array (String × Array Char)) (c : CComp) (r : Fren.Core.CheckResult)
    (vias : Array (Span × Lean.Name) := #[]) : IO (Array Msg) := do
  let mut shown := #[]
  for m in Fren.Core.messages (c.vars.any fun v => v.role == .output && !v.isPub) { r with global := c.global } c.decidable do
    let prop? := m.item?.bind fun n => c.props.find? (·.name == n)
    let index? := m.atIndex?.bind fun k => m.item?.bind fun n => (c.indexes.filter (·.1 == n))[k]?.map (·.2.2.1)
    let site? := m.atSite?.bind fun k => m.item?.bind fun n => (c.tables.filter (·.1 == n))[k]?.map (·.2.2.1)
    let explicit := m.atRange?.map fun sp => ({ start := sp.start, stop := sp.stop } : Span)
    let span := if let some sp := explicit.orElse (fun _ => index?.orElse fun _ => site?) then sp else match prop?, m.item? with
      | some p, _ => if m.atTrigger then p.triggerSpan?.getD p.span else p.span
      | none, some n => (c.insts.find? (·.name == n)).map (·.span)
        |>.orElse (fun _ => (c.vars.find? (·.name == n)).map (·.span)) |>.getD c.span
      | none, none => c.span
    -- A closure's obligation names the function that applies it.
    let msg := match (index?.orElse fun _ => site?).bind fun sp => vias.find? (·.1 == sp) with
      | some (_, f) => if m.severity == .error then m.msg.note (Fren.Core.viaNote f) else m.msg
      | none => m.msg
    let msg := if let some subset := c.subset? then
        if r.verdict == .fail && m.severity == .error then
          { msg with
            code? := some "F0660"
            headline := s!"subset type `{Fren.Core.showPath subset}` is empty"
            label? := some "no value satisfies its invariants"
            notes := (msg.notes.filter (!·.startsWith "help:")).map (·.replace "no outputs satisfy" "no value satisfies")
              |>.push "help: weaken the invariants or choose a base type with a satisfying value"
          }
        else msg
      else if let some invariant := c.subsetInvariant? then
        if r.verdict == .fail && m.severity == .error then
          { msg with
            code? := some "F0662"
            headline := s!"invariant `{Fren.Core.showPath invariant}` may not be defined"
            label? := some "not defined under the earlier invariants"
          }
        else msg
      else if let some label := r.subsetTy?.bind (·.dropPrefix? "@invariant:") then
        if m.severity == .error then
          { msg with
            code? := some "F0661"
            headline := s!"invariant `{label}` does not hold"
            label? := some "violates the invariant"
            notes := (msg.notes.filter (·.startsWith "counterexample:")).push
              "note: a value given for a subset type must satisfy each named invariant"
          }
        else msg
      else msg
    let file := prop?.bind fun prop => if prop.sourceRef || m.atRange?.isSome then prop.file? else none
    printDiag p files { file := file.getD c.file, span, severity := m.severity, msg }
    shown := shown.push msg
  return shown

/-- Tests `c`, the evaluator's `ec`, on `n` random behaviours from `seed`
(`Reqs/Eval#fren-quickcheck`). -/
def testReport (sp : Eval.Spec) (ec : Eval.Comp) (c : CComp) (global : Bool) (seed n : Nat) : Eval.Report :=
  -- Each procedure has its own stream, so a run does not depend on the others.
  let rng : Eval.Rng := ⟨Eval.mix seed.toUInt64 (hash c.path)⟩
  (if global then sp.quickGlobal ec n else sp.quickComp ec n).run' rng

/-- Tests the procedure or global expectation `c`, whose counterpart is `ec`
(`Reqs/Eval#fren-quickcheck`), and prints what testing found about the
checks that `keep` selects: their results, and those that are not run
are dropped. Returns the results and the messages printed, and whether
one is an error. `rep` is the report of testing it (`testReport`), if it
has been tested already. What testing it evaluates must have no quantifier
that the evaluator cannot evaluate: one is an error (`F0639`), at the
quantifier, and none of its checks is run (`Reqs/Eval#quantifiers`). -/
def testComp (args : Args) (files : Array (String × Array Char)) (sp : Eval.Spec) (c : CComp) (ec : Eval.Comp)
    (global : Bool) (keep : Fren.Core.CheckResult → Bool) (prelude : Prelude) (byCheck : Bool := false)
    (rep : Eval.Report := testReport sp ec c global args.seed args.nTests) (vias : Array (Span × Lean.Name) := #[]) :
    IO (Array Fren.Core.CheckResult × Array Msg × Bool) := do
  let subject := Fren.Core.subjectOf c.path global (c.props[0]?.map (·.name))
  if let some (file, pos) := sp.untestable? ec then
    let msg := Fren.Core.untestableMsg subject
    -- At its keyword, `forall` or `exists`.
    printDiag args.paint files { file, span := { start := pos, stop := pos + 6 }, msg }
    return (#[], #[msg], true)
  -- A call's binding of an input of a subset type, with that type, as
  -- the solver's check has it (`Fren.Core.Inst.typed`).
  let typedOf (r : Fren.Core.CheckResult) : Fren.Core.CheckResult :=
    match r.kind, r.prop?, r.target? with
    | .inst, some w, some (_, a) => { r with subsetTy? := (c.insts.find? (·.name == w)).bind fun i => (i.typed.find? (·.1 == a)).map (·.2) }
    | _, _, _ => r
  let results := markInterpreted prelude c ((rep.results.filter keep).map typedOf)
  let mut shown := #[]
  for r in results do
    -- Inconclusive results are reported below, once for the procedure; a
    -- cover goal's pass shows its witness.
    if r.verdict == .fail || (r.kind == .cover && r.verdict == .pass) then
      shown := shown ++ (← printResult args.paint files c r vias)
  let warn (msg : Msg) : IO Unit := printDiag args.paint files { file := c.file, span := c.span, severity := .warning, msg }
  -- Realizability refuted by an input whose outputs the search all saw
  -- (`eval::test_verdict`), which its failure reports.
  let refuted := results.any fun r => r.kind == .realizable && r.verdict == .fail
  if let some input := rep.noOutputs? then
    -- It explains why the checks it selects were not reached, too.
    if !results.isEmpty && !(refuted && results.all (·.verdict != .inconclusive)) then
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
        (s!"the assumption `{Fren.Core.showComp (d ++ a)}` of call `{n}`", ((c.insts.find? (·.name == n)).map (·.span)).getD c.span)
      | _, _ =>
        let p? := c.props.find? (·.name == n)
        (if global then subject else s!"`{Fren.Core.showComp (c.path ++ n)}`", (p?.map fun p => p.triggerSpan?.getD p.span).getD c.span)
    let msg := Fren.Core.untriggeredMsg what args.nTests byCheck
    printDiag args.paint files { file := c.file, span, severity := .warning, msg }
    shown := shown.push msg
  -- At each cover goal for which no test found a witness (`F0616`).
  for r in rep.unwitnessed.filter keep do
    let some n := r.prop? | continue
    let span := ((c.props.find? (·.name == n)).map (·.span)).getD c.span
    let msg := Fren.Core.unwitnessedMsg s!"`{Fren.Core.showComp (c.path ++ n)}`" args.nTests byCheck
    printDiag args.paint files { file := c.file, span, severity := .warning, msg }
    shown := shown.push msg
  return (results, shown, false)

/-- The SMT-LIB symbols of the evaluator's spec (`Symbols.of`), for
confirming models (`solveComp`); none if it has none. -/
def symbolsOf (spec? : Except String Eval.Spec) : Symbols :=
  match spec? with
  | .ok sp => Symbols.of sp
  | .error _ => {}

/-- The solver's results for `c`, a global expectation if `global`, with
each model confirmed by the evaluator's `spec?` (`Reqs/Eval#confirming-models`);
the results that a refuted model is about, with their internal errors; and
an internal error if the evaluator has no counterpart of `c`. `sy` is
`symbolsOf spec?`, built once for the spec. `prelude` is `st`'s, indexed
(`State.queryPrelude`), and `cache` holds the answers to the queries asked
before (`QueryCache`). -/
partial def solveComp (st : State) (prelude : Prelude) (spec? : Except String Eval.Spec) (sy : Symbols) (c : CComp) (global : Bool)
    (kinds : Array Fren.Core.CheckKind)
    (limits : Limits) (cache : QueryCache) (dump? : Option (String → IO Unit) := none) (body : Bool := false)
    (examples : Option Nat := some 1) (instances : Bool := true) :
    IO (Array Fren.Core.CheckResult × Array (Fren.Core.CheckResult × Msg) × Option Msg) := do
  -- The functions whose contracts each check's queries apply, recorded by
  -- the backend, and taken by `checkComp` after each check
  -- (`Fren.Core.withApplies`).
  let applied ← IO.mkRef (#[] : Array Lean.Name)
  let bk := backend prelude st.datatypes { c with funFacts := st.funFacts, bounded := st.bounded c } limits dump? (st.usesStrings || st.usesSeqs) (st.usesSets || st.usesSeqs) st.usesProjection cache st.quantified
    st.appFuns (contractFns := st.contractFns) (applied? := some applied)
  let take : IO (Array Lean.Name) := applied.modifyGet fun a => (a, #[])
  -- Whether a formula uses an abstract type or an uninterpreted function,
  -- for the values that a realizability conflict's notes may show
  -- (`Fren.Core.Comp.realizableInterpreted`), as `markInterpreted` decides.
  let interprets (f : String) : Bool := f.contains "(seq.nth (as seq.empty" || prelude.interprets (quotedSymbols f)
  let typesInterpreted := c.vars.any (fun v => interprets v.ty.sort || v.fact?.any interprets)
  let log ← IO.mkRef #[]
  -- The checks set to testing are not asked of the solver (`check::by_testing`).
  let (raw, missing?) ← match spec? with
    | .ok sp => match sp.counterpart? c global body with
      | some ec =>
        let core := pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start)) (c.tables.map (·.2.2.1.start))
        let (core, ks) := { core with typesInterpreted }.untested (c.tested.union c.enumerated) kinds
        pure (← Fren.Core.checkComp (fun k => confirming sp sy ec k log (bk k)) core ks examples (interprets ·.1) (some take), none)
      | none =>
        let (core, ks) := { toCore c with typesInterpreted }.untested (c.tested.union c.enumerated) kinds
        pure (← Fren.Core.checkComp bk core ks examples interprets (some take),
          some (Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`"))
    | .error _ =>
      let (core, ks) := { toCore c with typesInterpreted }.untested (c.tested.union c.enumerated) kinds
      pure (← Fren.Core.checkComp bk core ks examples interprets (some take), none)
  let (results, refuted) := applyRefutations raw (← log.get)
  let results := Fren.Core.recursiveResults c.recursive results
  -- The contract of a generic function without a body, where its check at
  -- its type parameters' sorts does not pass: its check at each instance
  -- that the spec applies, in order of their names (`lang::generic_contract`).
  if !instances then return (markInterpreted prelude c results, refuted, missing?)
  let sites := st.instanceSites
  -- The contract of the instance of `f` at `targs`, where `f`'s check at its
  -- type parameters' sorts, `r`'s, does not pass: its realizability check.
  let atInstance (f : Lean.Name) (targs : Array Fren.Core.Ty) : IO (Array Fren.Core.CheckResult × Array (Fren.Core.CheckResult × Msg)) := do
    let some (_, ic) := ((st.instContracts.find? f).getD #[]).find? (·.1 == targs) | return (#[], #[])
    let (rs, ref, _) ← solveComp st prelude spec? sy ic global #[.realizable] limits cache dump? body examples false
    return (rs.filter (·.kind == .realizable), ref)
  let mut results := results
  let mut refuted := refuted
  if let (true, some f, some r) := (c.generic, c.fn?, results.find? (·.kind == .realizable)) then
    if r.verdict != .pass then
      let mut instResults := #[]
      for (site, g, targs) in sites do
        unless site == .function && g == f do continue
        let (rs, ref) ← atInstance f targs
        instResults := instResults ++ rs
        refuted := refuted ++ ref
      let checked := Fren.Core.genericContract (·.verdict) r instResults
      results := results.foldl (init := #[]) fun acc x => if x.kind == .realizable then acc ++ checked else acc.push x
  -- The instances whose contracts this item's checks check, of functions
  -- declared in earlier files (`lang::instance_site`), where the
  -- function's check at its type parameters' sorts does not pass, reported
  -- at the item, without notes at the clauses, which another file has.
  let key := if body then c.path ++ c.bodyOf?.getD .anonymous
    else if global then c.path ++ ((c.props[0]?.map (·.name)).getD .anonymous) else c.path
  for (site, f, targs) in sites do
    unless site == .item c.file key do continue
    let some b := st.bodies.find? fun b => b.fn? == some f && b.generic | continue
    let (rs, _, _) ← solveComp st prelude spec? sy b false #[.realizable] limits cache dump? true examples false
    unless rs.any fun r => r.kind == .realizable && r.verdict != .pass do continue
    let (rs, ref) ← atInstance f targs
    results := results ++ rs.map fun r => { r with clashes := #[] }
    refuted := refuted ++ ref
  return (markInterpreted prelude c results, refuted, missing?)

/-- Which results of testing `c` `fren check` keeps, for the checks of
kinds `kinds` set to testing (`Reqs/Check#checking-by-testing`). -/
def testedKeeps (c : CComp) (kinds : Array Fren.Core.CheckKind) (r : Fren.Core.CheckResult) : Bool :=
  kinds.contains r.kind && c.tested.covers r && Fren.Core.runOf r.kind true == .byTesting
    && !(c.enumerated.covers r && Fren.Core.Enumeration.enumerable r.kind)

/-- The subject of the messages about `c`, as they show it. -/
def subjectOf (c : CComp) (global : Bool) : String :=
  Fren.Core.subjectOf c.path global (c.props[0]?.map (·.name))

/-- Whether two results are of the same check. -/
def sameCheck (a b : Fren.Core.CheckResult) : Bool :=
  a.kind == b.kind && a.prop? == b.prop? && a.target? == b.target?

/-- The checks of `c` set to enumeration, enumerated
(`Reqs/Check#checking-by-enumeration`), those also set to testing tested
beyond the bound too (`Reqs/Check#enumeration-then-testing`); or the error
that stopped it. Only the results of the kinds `kinds` are kept. -/
def enumerated (sp : Eval.Spec) (ec : Eval.Comp) (c : CComp) (global : Bool) (kinds : Array Fren.Core.CheckKind) :
    Except Msg Fren.Core.Enumeration.Enumerated := do
  let subject := subjectOf c global
  let alone := c.enumerated.minus c.tested
  let both := c.enumerated.inter c.tested
  let run (t : Fren.Core.Tested) (testing : Bool) : Except Msg (Option Fren.Core.Enumeration.Enumerated) :=
    if !t.any then pure none else some <$> enumerateComp sp ec c kinds subject t testing
  let a? ← run alone false
  let b? ← run both true
  let keep (r : Fren.Core.CheckResult) := c.enumerated.covers r
  return Fren.Core.Enumeration.Enumerated.merge c.enumSize a? b? keep

/-- `f` of each of `xs`, taken by at most `jobs` threads at once, those
that `first` selects before the others, and otherwise in order: for each,
in the order of `xs`, an action that waits for it. Which is started first
changes only when each finishes, not what it gives. With one job, each
action runs `f` itself, in the thread that runs it, so that nothing is
shared between threads.

Each thread first makes `own`, its own copy of what `f` reads, which it
gives `f`. Lean counts the references to an object
that two threads share atomically, and threads that read the same objects
contend for them: four tests of `lint::and_associates` at once, sharing
one `Eval.Spec`, took 11.6 s, and 3.1 s each with a spec of its own. So
`own` should build what `f` reads in the thread, not return an object
made before. The copies cost memory: when this was measured (November
2026), a reading of Fren's own spec took about 50 MB for each thread, and
`fren quickcheck` of it peaked at 964 MB with a reading for each thread,
against 248 MB with one shared. With one job, there is one thread, so
`f` is given `single?`, what the caller has already made, if it gives it,
rather than a copy of its own. -/
def inParallelWith [Nonempty β] (jobs : Nat) (xs : Array α) (own : IO σ) (f : σ → α → IO β)
    (first : α → Bool := fun _ => false) (single? : Option σ := none) : IO (Array (IO β)) := do
  if jobs ≤ 1 then
    let l ← match single? with
      | some l => pure l
      | none => own
    return xs.map (f l)
  let promises ← xs.mapM fun _ => IO.Promise.new
  let firsts := xs.map first
  let idxs := Array.range xs.size
  let order := idxs.filter (firsts[·]?.getD false) ++ idxs.filter (!firsts[·]?.getD false)
  let next ← IO.mkRef 0
  let worker : IO Unit := do
    let l ← own
    repeat
      let k ← next.modifyGet fun k => (k, k + 1)
      let some i := order[k]? | break
      let (some x, some p) := (xs[i]?, promises[i]?) | break
      p.resolve (← (f l x).toBaseIO)
  for _ in [0:min jobs xs.size] do
    discard <| IO.asTask worker .dedicated
  return promises.map fun p => IO.ofExcept p.result!.get

/-- A reading of the spec of `files` (`specOf`), made when it is first
needed. An action rather than a value, so that each thread that runs it
(`inParallelWith`) gets one of its own. -/
def ownSpecOf (files : Array (String × Array Char)) : IO (Thunk (Except String Eval.Spec)) :=
  pure (Thunk.mk fun _ => specOf files)

/-- `inParallelWith` without a copy of its own for each thread. -/
def inParallel [Nonempty β] (jobs : Nat) (xs : Array α) (f : α → IO β) (first : α → Bool := fun _ => false) :
    IO (Array (IO β)) :=
  inParallelWith jobs xs (pure ()) (fun _ => f) first

/-- The report of `--timings` (`Reqs/Cli#timings`): for each procedure
and global expectation, with its total time, the time of its solver's
checks and that of its checks by testing and enumeration, in nanoseconds,
its subject and its key, a line of its times in milliseconds, slowest
first, then their total. -/
def timingReport (ts : Array (Nat × Nat × Nat × String × String)) : String :=
  let ms (ns : Nat) : String :=
    let tenths := (ns + 50000) / 100000
    s!"{tenths / 10}.{tenths % 10}"
  let sorted := ts.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.2.2.2 < b.2.2.2.2)
  let lines := sorted.toList.map fun (t, s, r, subject, key) =>
    s!"timing: {ms t} ms (solver {ms s} ms, testing {ms r} ms): {subject} ({key})\n"
  let total := ts.foldl (· + ·.1) 0
  let solver := ts.foldl (· + ·.2.1) 0
  String.join lines ++ s!"timing: total {ms total} ms (solver {ms solver} ms, testing {ms (total - solver)} ms), of {ts.size} procedures and global expectations\n"

/-- How many procedures `fren check` checks at once without `--jobs`: as
many as the machine has cores (`Reqs/Cli#parallel-checking`). -/
def jobsDefault : BaseIO Nat :=
  return max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat

/-- Runs `fren check`, printing diagnostics and the summary to stderr and
any solver queries to stdout; returns the exit code. `record?` collects the
results of each item, by its key (`Mutate.Todo.key`), for the tests of
`fren mutate`'s decisions. -/
def check (args : Args) (record? : Option (IO.Ref (Array (String × Fren.Core.CheckResult))) := none) : IO UInt32 := do
  let some (files, st) ← load args.paint args.files args.lints | return exitCode false none
  let mut all := #[]
  -- Warnings from lints, already printed.
  let mut shown := st.diags.map (·.msg)
  -- Each procedure and global expectation,
  -- with the checks that run on it.
  let todo := (Mutate.todo st).map fun t => (t.comp, t.global, t.kinds, t.body, t.key)
  let prelude := st.queryPrelude
  -- A query asked again, as some checks of a procedure share one, is
  -- answered once (`Reqs/Cli#solver-queries`), and one asked by an earlier
  -- run, from `--query-cache` (`Reqs/Cli#query-cache`).
  let store? ← if args.queryCache?.isNone && args.verifyQueryCache?.isNone then pure none else
    some <$> QueryStore.new (args.queryCache?.map System.FilePath.mk) (args.verifyQueryCache?.map System.FilePath.mk)
  let cache ← QueryCache.new store?
  -- A directory to compare with that is not there would compare nothing.
  if let some dir := args.verifyQueryCache? then
    unless ← System.FilePath.isDir dir do
      IO.eprintln (argError args.paint { code? := none, headline := s!"no query cache `{dir}` to compare with" })
      return exitCode false none
  -- Each model is confirmed with the evaluator (`Reqs/Eval#confirming-models`).
  let spec? := specOf files
  let sy := symbolsOf spec?
  let mut internal := #[]
  let mut byTesting := 0
  let mut byBound := 0
  let mut enumErrors := 0
  -- The evidence of each procedure's realizability, by its path, which the
  -- checks of the items that call it rest on (`Reqs/Evidence`).
  let mut realizability : Std.HashMap Lean.Name Fren.Core.ExternalPremise := {}
  if let .error e := spec? then
    internal := internal.push (Msg.internal s!"the evaluator cannot read the spec: {e}")
    printDiag args.paint files { file := 0, span := default, msg := internal.back! }
  -- The solver's answers for each, `--jobs` at a time, each with the
  -- queries that it writes for `--dump-smt` and the report of testing its
  -- checks set to testing; reported below, in order
  -- (`Reqs/Cli#parallel-checking`). Only this thread prints, so that the
  -- output is the same as one at a time.
  let solve := fun (spec? : Thunk (Except String Eval.Spec))
      ((c, global, kinds, body, _) : CComp × Bool × Array Fren.Core.CheckKind × Bool × String) => do
    let spec? := spec?.get
    let n ← IO.mkRef 0
    let dumped ← IO.mkRef ""
    let dump? := if args.dumpSmt then some fun script => do
        n.modify (· + 1)
        let k ← n.get
        dumped.modify (· ++ s!"; {c.path}: query {k}\n{script}(check-sat)\n(reset)\n\n")
      else none
    let start ← IO.monoNanosNow
    let r ← solveComp st prelude spec? sy c global kinds args.limits cache dump? body args.examples
    let solved ← IO.monoNanosNow
    -- The checks set to testing, tested (`Reqs/Check#checking-by-testing`).
    let tested? := if !(c.tested.minus c.enumerated).any then none else match spec? with
      | .ok sp => (sp.counterpart? c global).map fun ec =>
        -- Not tested if it cannot be (`testComp`).
        (ec, if (sp.untestable? ec).isSome then {} else testReport sp ec c global args.seed args.nTests)
      | .error _ => none
    -- And those set to enumeration, enumerated (`Reqs/Check#checking-by-enumeration`).
    let enumerated? := if !c.enumerated.any then none else match spec? with
      | .ok sp => (sp.counterpart? c global).map fun ec => enumerated sp ec c global kinds
      | .error _ => none
    -- Forced here, in this thread, so that `--timings` counts them.
    let tested? ← IO.lazyPure fun _ => tested?
    let enumerated? ← IO.lazyPure fun _ => enumerated?
    let timing := (solved - start, (← IO.monoNanosNow) - solved)
    return (r, ← dumped.get, tested?, enumerated?, timing)
  let mut timings := #[]
  -- Those with checks by testing or enumeration first: they are the
  -- slowest, and starting them last would leave them running alone at
  -- the end.
  -- Each thread reads the spec itself, which gives the same `spec?`.
  let solving ← (← inParallelWith (args.jobs?.getD (← jobsDefault)) todo (ownSpecOf files) solve
    (first := fun (c, _) => c.tested.any || c.enumerated.any) (single? := some (Thunk.pure spec?))).mapM id
  -- The contracts of the uninterpreted functions first, though their items
  -- come last, since what applies them rests on them
  -- (`Fren.Core.contractsEvidence`).
  let contractFns := st.contractFns
  let bodies := (todo.zip solving).filterMap fun ((c, global, _, body, _), ((results, _, _), _)) =>
    c.fn?.map fun f => (c.path, f, Fren.Core.CheckedItem.of body (c.vars.any (·.role == .output)) (global || c.global) global, results)
  for (f, e) in Fren.Core.contractsEvidence realizability.get? bodies do
    realizability := realizability.insert f e
  for (c, global, kinds, body, key) in todo, solved in solving do
    let ((results, refuted, missing?), dumped, tested?, enumerated?, (solverNs, restNs)) := solved
    timings := timings.push (solverNs + restNs, solverNs, restNs, subjectOf c global, key)
    IO.print dumped
    if let some msg := missing? then
      internal := internal.push msg
      printDiag args.paint files { file := c.file, span := c.span, msg }
    for (r, msg) in refuted do
      let span := (r.prop?.bind fun n => c.props.find? (·.name == n)).map (·.span) |>.getD c.span
      printDiag args.paint files { file := c.file, span, msg }
      internal := internal.push msg
    for r in results do
      shown := shown ++ (← printResult args.paint files c r st.vias)
    -- Each of its results, with the caveats of the method that ran it.
    let mut item : Array (Fren.Core.CheckResult × List Fren.Core.Caveat) :=
      results.map fun r => (r, Fren.Core.ownCaveatsOf r false)
    -- The evaluator's internal error, printed above, explains why the
    -- checks set to testing are missing from the summary.
    if let (.ok sp, some (ec, rep)) := (spec?, tested?) then
      let (tested, msgs, failed) ← testComp args files sp c ec global (testedKeeps c kinds) prelude (byCheck := true) rep st.vias
      shown := shown ++ msgs
      if failed then internal := internal.push msgs[0]!
      -- A witness found by testing is a real witness: only a proof check's
      -- pass by testing has the caveat `Random` (`Reqs/Evidence`).
      item := item ++ tested.map fun r => (r, Fren.Core.ownCaveatsOf r true)
    -- The checks set to enumeration (`Reqs/Check#checking-by-enumeration`).
    match enumerated? with
    | some (.error msg) =>
      printDiag args.paint files { file := c.file, span := c.span, msg }
      shown := shown.push msg
      enumErrors := enumErrors + 1
    | some (.ok e) =>
      for r in e.results do
        shown := shown ++ (← printResult args.paint files c r st.vias)
      item := item ++ e.results.map fun r => (r, Fren.Core.ownCaveatsOf r false)
      if let some msg := e.boundedMsg? (subjectOf c global) c.tested then
        printDiag args.paint files { file := c.file, span := c.span, severity := .info, msg }
        shown := shown.push msg
    | none => pure ()
    -- The checks that the method their evidence sets does not run
    -- (`check::method_run`).
    for msg in (toCore c).skippedMsgs (subjectOf c global) c.tested c.enumerated kinds do
      printDiag args.paint files { file := c.file, span := c.span, severity := .info, msg }
      shown := shown.push msg
    -- What its checks rest on, the realizability of the procedures it calls
    -- and of its refinements' abstractions, weakens them or leaves them
    -- inconclusive (`Reqs/Evidence`).
    let refinements := Fren.Core.refinementsOf (c.props.map fun q => (q.name, q.abstraction?))
    let (calls, abstractions) := Fren.Core.externalPremises realizability.get?
      (c.insts.map fun i => (i.name, i.comp, i.assumes.map Prod.fst)) refinements
    let names := c.insts.map (·.name)
    let assumptions := (c.props.filter (·.kind == .assume)).map (·.name)
    let what := Fren.Core.CheckedItem.of body (c.vars.any (·.role == .output)) (global || c.global) global
    -- And the contracts of the functions that its checks' queries apply, or,
    -- for a check by random testing, that it applies (`Fren.Core.checkApplies`).
    -- Shared with Lean, which reads the placeholders that the item uses
    -- instead (`Fren.Core.itemContracts`).
    let itemApplies := Fren.Core.itemContracts c.natApps fun app =>
      contractFns.get? (((peelLets app).drop 1).takeWhile (· != ' ')).toString
    let functions := Fren.Core.functionPremises realizability.get? (Fren.Core.appliedOf item itemApplies) c.fn?
    let reported := Fren.Core.itemEvidence c.path what c.subsetInvariant?.isSome calls
      (item.map fun (r, own) => (r, r.site names assumptions c.fn?.isSome false (refinements.map (·.1)), own))
      abstractions functions c.fn? itemApplies
    let mut final := #[]
    for (r, _) in item, rc in reported do
      let rep := rc.rep
      let msg? := rc.msg?
      if let some msg := msg? then
        let span := (r.prop?.bind fun n => c.props.find? (·.name == n)).map (·.span)
          |>.orElse (fun _ => r.prop?.bind fun n => (c.insts.find? (·.name == n)).map (·.span)) |>.getD c.span
        printDiag args.paint files { file := c.file, span, severity := if rep.unsettled then .warning else .info, msg }
        shown := shown.push msg
      if rep.byTesting then byTesting := byTesting + 1
      if rep.byBound then byBound := byBound + 1
      final := final.push { r with verdict := rep.shown }
      if r.isOwnRealizability c.path && what == .component then
        realizability := realizability.insert c.path (rc.realizability c.path)
      if let (true, some f) := (r.isOwnRealizability c.path && what == .contract, c.fn?) then
        realizability := realizability.insert f (rc.contract f)
    all := all ++ final
    -- The tests compare each method's own verdicts, before the evidence of
    -- what they rest on changes how they are shown.
    if let some r := record? then r.modify (· ++ item.map fun (x, _) => (key, x))
  -- A fresh answer that contradicts `--verify-query-cache`'s
  -- (`cli::contradicts`).
  if let some store := store? then
    for path in ← store.mismatches.get do
      let msg := Msg.internal s!"the solver's answer contradicts the query cache's entry `{path}`"
      printDiag args.paint files { file := 0, span := default, msg }
      internal := internal.push msg
  IO.eprintln (Fren.Core.summary all byTesting byBound)
  -- How many answers it compared, so that a comparison with nothing does
  -- not look like a pass (`Reqs/Cli#query-cache`).
  if let (some store, some dir) := (store?, args.verifyQueryCache?) then
    IO.eprintln s!"fren: compared {← store.compared.get} answers with the query cache `{dir}`"
  if args.timings then IO.eprint (timingReport timings)
  if shown.any (·.code?.isSome) then
    IO.eprintln ""
    printExplainHint shown
  -- A result whose model Fren's semantics contradicts stays inconclusive,
  -- and its internal error, printed with it, is an error of the run, as a
  -- refuted model's is (`applyRefutations`, `Reqs/Models#reporting`).
  let refutedModels := all.filter (·.detail matches .refuted ..)
  let errors := (internal.map fun _ => Fren.Core.Severity.error) ++ Array.replicate enumErrors .error
    ++ refutedModels.map fun _ => Fren.Core.Severity.error
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
  let prelude := st.queryPrelude
  let items := st.comps.map (·, false) ++ st.globals.map (fun g => (g, g.short))
  -- The report of testing each, `--jobs` at a time, each from a random
  -- stream of its own (`testReport`); printed below, in order
  -- (`Reqs/Cli#parallel-checking`).
  let test := fun (own : Thunk (Except String Eval.Spec)) ((c, global) : CComp × Bool) => do
    let sp := own.get.toOption.getD sp
    let rep := match sp.counterpart? c global with
      | some ec => if (sp.untestable? ec).isSome then {} else testReport sp ec c global args.seed args.nTests
      | none => {}
    -- Forced here, in this thread.
    IO.lazyPure fun _ => some rep
  -- Each thread reads the spec itself, which gives the same `sp`.
  let testing ← inParallelWith (args.jobs?.getD (← jobsDefault)) items (ownSpecOf files) test
    (single? := some (Thunk.pure (.ok sp)))
  for (c, global) in items, tested in testing do
    let rep := (← tested).getD {}
    let some ec := sp.counterpart? c global
      | let msg := Msg.internal s!"the evaluator has no counterpart of `{Fren.Core.showComp c.path}`"
        printDiag args.paint files { file := c.file, span := c.span, msg }
        sevs := sevs.push .error
    let (results, msgs, failed) ← testComp args files sp c ec global (fun _ => true) prelude (rep := rep) (vias := st.vias)
    shown := shown ++ msgs
    if failed then sevs := sevs.push .error
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
  let some compText := args.comp? | fail { code? := none, headline := "`fren eval` needs `--proc PATH`" }
  let lst ← match specStateOf files with
    | .ok s => pure s
    | .error e =>
      printDiag args.paint files { file := 0, span := default, msg := Msg.internal s!"the evaluator cannot read the spec: {e}" }
      return 2
  let sp := lst.spec
  let path := (compText.splitOn "::").foldl Lean.Name.mkStr .anonymous
  let some c := sp.comp? path
    | fail { code? := none, headline := s!"no procedure `{compText}`"
             notes := #[s!"note: the procedures are {Fren.Core.showNameList (sp.comps.map (·.path))}"] }
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
  -- The literals of the expectations too, as when testing (`Reqs/Eval#searching-for-behaviours`).
  let lits := atoms ++ Eval.atomsOf .anonymous (c.ofKind .expect)
  let (strs, rng) := (Eval.stringsOf lits).run rng
  let p : Eval.Problem := { vars := Eval.remaining (sp.order c) given, atoms, ints := Eval.intsOf lits, strs }
  let found := (p.solve sp w I given 100000).run' rng
  let env := found.getD given
  -- `env` is now fixed.
  if found.isNone && !vars.all (given.contains ·.name) then
    IO.eprintln (Fren.Core.renderPlain .warning
      { code? := none, headline := s!"no behaviour of `{Fren.Core.showComp path}` was found with the values given"
        notes := #["note: the variables not set have no value"] } args.paint)
  for v in vars do
    IO.println s!"{v.name} = {(env[v.name]?.map (·.showAs sp v.ty)).getD "unknown"}"
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
  let comps := (st.comps.filter fun c => c.subset?.isNone && c.subsetInvariant?.isNone).qsort (·.path.toString < ·.path.toString)
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
  let textStarts := Fren.Core.lineStarts text
  let move (off : Nat) :=
    let (n, lstart, _) := Fren.Core.lineAtIn textStarts text off
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
    -- No lint is fixed.
    let starts := linesOf files
    for d in st.diags do printDiag args.paint files d starts
    printStopped args.paint st.diags "fix"
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
    -- A fix that made a static error is not kept, and is a bug.
    if st'.diags.any fun d => d.severity == .error && d.lint?.isNone then
      IO.eprint (Fren.Core.renderPlain .warning
        { code? := none, headline := "some fixes were not made, because they would have caused a static error"
          notes := #["note: this is a bug in `fren fix`; the lints they fix are reported below"] } args.paint)
      break
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
  let starts := linesOf files
  for d in left do printDiag args.paint files d starts
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
      IO.eprintln <| if n == 0 then s!"formatted {path}"
        else s!"fixed {path} ({n} lint{if n == 1 then "" else "s"})"
  printExplainHint (left.map (·.msg))
  return Fren.Core.fixExit args.diffOnly true unchanged

/-- The results of one way of checking (`--by`) the spec's procedures,
global expectations, by `Mutate.Todo.key`, as far as they
have been needed. -/
abbrev Baseline := IO.Ref (Std.HashMap String (Array Fren.Core.CheckResult))

/-- The mutants of the files, whose parses are `parsed` (`parseText`), as
elaborated in the states `states`: before each file, then after the last
(`elaborateSourcesBefore`). -/
def mutantsWith (files : Array (String × Array Char)) (parsed : Array Parsed) (states : Array State) :
    Array Mutate.Mutant := Id.run do
  let mut all := #[]
  let parsed := parsed.map (·.toOption)
  -- The constants that divisors name, in any of the files.
  let divisors := Mutate.divisorConstants (parsed.flatMap fun p => (p.map (·.2.1)).getD #[])
  let enums := Mutate.enumsOf (parsed.flatMap fun p => (p.map (·.2.1)).getD #[])
  for (path, chars) in files, i in [0:files.size] do
    if let some (toks, items, _) := parsed[i]! then
      -- The state after file `i`.
      let natSums := ((states[i + 1]?.map (·.natSums)).getD #[]).filterMap fun (f, sp) => if f == i then some sp else none
      all := all ++ Mutate.ofFile { file := i, path, chars, toks, natSums, enums } items divisors
  return all

/-- The mutants of the files, as elaborated, with the lint levels `lints`,
and the state before each file, from which a mutant of it is elaborated,
then after the last. -/
def mutantsOf (files : Array (String × Array Char)) (lints : Array (Fren.Core.LintTarget × Fren.Core.LintLevel)) :
    Array State × Array Mutate.Mutant := Id.run do
  let parsed := files.map (parseText ·.2)
  let mut states := #[initialState lints]
  for (_, chars) in files, i in [0:files.size] do
    states := states.push (elabParsed (states.back?.getD {}) i chars parsed[i]!)
  return (states, mutantsWith files parsed states)

deriving instance BEq for Fren.Core.Pat
deriving instance BEq for Fren.Core.PTy
deriving instance BEq for Fren.Core.DataShape
deriving instance BEq for Contract
deriving instance BEq for Fren.Core.Fix
deriving instance BEq for Fren.Core.Msg
deriving instance BEq for Diag
deriving instance BEq for Fren.Core.LevelInEffect
deriving instance BEq for Fren.Core.Levels
deriving instance BEq for Fren.Core.Item, Fren.Core.EnumDef, Fren.Core.UseDef, Fren.Core.Tested, DataDecl
deriving instance BEq for Ident, Bound, Pattern, Binder, Expr, Member
deriving instance BEq for CVar, CProp, CInst, CComp

instance : Same Fren.Core.Table := ⟨fun a b => same_fields% Fren.Core.Table a b except []⟩

/-- A generic function's: its declared result type by its type and its
text, which say what it is with its patterns. -/
instance : Same GenericFn := ⟨fun a b => same_fields% GenericFn a b except [resultP]
  && a.resultP.ty == b.resultP.ty && a.resultP.text == b.resultP.text⟩

/-- An instance's contract (`State.instContracts`), made of the function's
contract's comp: by its formulas, which say what its checks ask. -/
instance : Same CComp := ⟨fun a b => a.fn? == b.fn? && a.vars.map (·.ty) == b.vars.map (·.ty)
  && a.vars.map (·.fact?) == b.vars.map (·.fact?) && a.props.map (·.smt) == b.props.map (·.smt)
  && a.defs == b.defs && a.tables.map (·.2.2.2.2) == b.tables.map (·.2.2.2.2) && a.natApps == b.natApps⟩

/-- The names that the file whose parse is `p` writes, as identifiers or
keywords, with each part of a dotted identifier. A path resolves to an
item whose last name is the path's last segment (`Table.resolvePath`), so
a file that writes no item's name reads no item of that name
(`skipFile?`). -/
def writtenNames : Parsed → Std.HashSet String
  | .ok (toks, _) => toks.foldl (init := {}) fun s t => match t.tok with
    | .ident x | .kw x => (x.splitOn ".").foldl (·.insert ·) (s.insert x)
    | _ => s
  | .error _ => {}

/-- The keys at which `a` and `b` differ. -/
def changedKeys [BEq α] (a b : Lean.NameMap α) : Array Lean.Name :=
  let missing (x y : Lean.NameMap α) := x.foldl (init := #[]) fun acc k v => if y.find? k == some v then acc else acc.push k
  missing a b ++ missing b a

/-- `last`, with the entries at `keys` as in `mine`, if they are as in
`orig`: `last` is `orig`, extended by the files after it, which did not
change these entries. -/
def respliced? [BEq α] (orig mine last : Lean.NameMap α) (keys : Array Lean.Name) : Option (Lean.NameMap α) :=
  keys.foldlM (init := last) fun acc k => do
    unless last.find? k == orig.find? k do none
    return match mine.find? k with
      | some v => acc.insert k v
      | none => acc.erase k

/-- Whether a file elaborates the same after the states `a` and `b`, as
far as it reads them, but for the fields that `skipFile?` compares by name
or splices. Every field is compared (`same_fields%`), so a field added to
`State` is compared unless it is named here, but for:
- the fields that `elabFile` sets before it reads them: `file`, `src`,
  `fixing`, `module`, `scope`, `levels`, `useRecords`, `evidence?`, `used`,
  `expectations`, `lintReports`, `useLocs`, `expectationRemovals`,
  `items`, `usedItems`, `hofParams`, `fnArgs`, `lintFixes`, `globalTexts`, `settings`,
  `settingRemovals`, `seenSettings`, `assumptions`, `globalReads`,
  `trailingCommas`, `natReports` and `natKept`; and `itemStart`, `literals` and `itemSpan`, which it
  sets for each item before the item reads them. The `mutation` test job
  checks that they are not read, by elaborating files after states that
  differ in them (`FrenTestMain`);
- `comps`, `consts` and `constInts`, which `skipFile?` compares by name;
- the fields that `skipFile?` splices: `globals`, `bodies`,
  `diags`, `edits`, `natSums`, `claims` and `applied`, which elaboration
  only extends, or restores to an earlier value, and reads `applied` only
  after the size that it had when it was read; and `defs`, of which only
  each function's name, parameters and result type are read, never its
  body, so only they are compared;
- `bound`, which is empty between items, as `withBound` and the chains of
  `and` that hold pattern tests leave it, so only its size is compared.
A file is also elaborated again after a state with static errors of an
item in progress (`itemErrors`). -/
def sameForLater (a b : State) : Bool :=
  same_fields% State a b except [file, src, fixing, module, scope, levels, useRecords, evidence?, used, expectations,
    lintReports, useLocs, expectationRemovals, items, usedItems, hofParams, fnArgs, lintFixes, globalTexts, settings, settingRemovals,
    seenSettings, assumptions, globalReads, trailingCommas, natReports, natKept, itemStart, literals, itemSpan,
    comps, consts, constInts,
    globals, bodies, diags, edits, natSums, claims, applied, defs, bound]
    && a.bound.size == b.bound.size
    && a.defs.isEqv b.defs (fun (n, ps, r, _) (n', ps', r', _) => n == n' && ps == ps' && r == r')
    && a.itemErrors.isEmpty && b.itemErrors.isEmpty

/-- `s`, with the fields that `sameForLater` leaves out because `elabFile`
sets them before it reads them taken from `t`. Elaborating a file after
either gives the same state, which the `mutation` test job checks. -/
def State.withPerFileOf (s t : State) : State :=
  { s with file := t.file, src := t.src, fixing := t.fixing, module := t.module, scope := t.scope, levels := t.levels
           useRecords := t.useRecords, evidence? := t.evidence?, used := t.used, expectations := t.expectations
           lintReports := t.lintReports, useLocs := t.useLocs, expectationRemovals := t.expectationRemovals
           items := t.items, usedItems := t.usedItems, hofParams := t.hofParams, fnArgs := t.fnArgs
           lintFixes := t.lintFixes, globalTexts := t.globalTexts
           settings := t.settings, settingRemovals := t.settingRemovals, seenSettings := t.seenSettings
           assumptions := t.assumptions, globalReads := t.globalReads, trailingCommas := t.trailingCommas
           natReports := t.natReports, natKept := t.natKept
           itemStart := t.itemStart, literals := t.literals, itemSpan := t.itemSpan }

/-- How a mutant's state after a file differs from the original's
(`mutantState`): the paths of the procedures, and the constants, whose
entries differ, and whether both have as many procedures and agree on what
`sameForLater` compares. -/
structure Drift where
  comps : Array Lean.Name := #[]
  consts : Array Lean.Name := #[]
  constInts : Array Lean.Name := #[]
  aligned : Bool := true

/-- `d`, the drift of the state `mine` before a file from the original's,
`orig`, updated for the file: `mine'` and `orig'` are the states after it. -/
def Drift.next (d : Drift) (orig mine orig' mine' : State) : Drift :=
  let aligned := d.aligned && mine.comps.size == orig.comps.size && mine'.comps.size == orig'.comps.size
    && sameForLater orig' mine'
  -- The procedures that the file added; those before it are unchanged.
  let added := (orig'.comps.extract orig.comps.size).zip (mine'.comps.extract mine.comps.size)
  { comps := d.comps ++ added.filterMap fun (c, c') => if c == c' then none else some c.path
    consts := changedKeys orig'.consts mine'.consts, constInts := changedKeys orig'.constInts mine'.constInts, aligned }

/-- The state after file `j`, elaborated after `mine` rather than after
`orig`, the state before it as it is, if that can be told without
elaborating it: `orig'` is the state after file `j`, elaborated after
`orig`, `d` is how `mine` differs from `orig`, `written` are the names that
file `j` writes (`writtenNames`), and `items` whether it parses and has an
item.

Then `elabFile` and the first item set the fields that `sameForLater` does
not compare before they read them. If `mine` and `orig` agree on the
fields that it compares, and file `j` writes the name of no procedure or
constant whose entry differs, its elaboration reads the same values after
either, and so does the same:
- `comps` is read by a procedure's path, and `consts` and `constInts` by a
  constant's, each resolved from a path written in the file, which ends in
  the item's name (`Table.resolvePath`); the latter two are otherwise only
  extended;
- `globals`, `bodies`, `diags`, `edits`, `natSums`,
  `claims` and `applied` are only extended or restored to an earlier value,
  and `applied` is read after the size that it had when it was read;
- `defs` is read only as `sameForLater` compares it.
Those fields of the result are `mine`'s, changed as `orig`'s were, and
every other field is `orig'`'s. -/
def skipFile? (orig mine orig' : State) (d : Drift) (written : Std.HashSet String) (items : Bool) : Option State := do
  let named : Lean.Name → Bool
    | .str _ s => written.contains s
    | _ => true
  unless items && d.aligned && !(d.comps ++ d.consts ++ d.constInts).any named do none
  let splice {α} (f : State → Array α) : Array α := f mine ++ (f orig').extract (f orig).size
  return { orig' with consts := ← respliced? orig.consts mine.consts orig'.consts d.consts
                      constInts := ← respliced? orig.constInts mine.constInts orig'.constInts d.constInts
                      comps := splice (·.comps), globals := splice (·.globals)
                      bodies := splice (·.bodies), diags := splice (·.diags), edits := splice (·.edits)
                      natSums := splice (·.natSums), claims := splice (·.claims), applied := splice (·.applied)
                      defs := splice (·.defs) }

/-- The state of the files with the mutant `m` applied, from the states
`states` before each file and after the last. `parsed` are the files'
parses, `names` the names that each writes (`writtenNames`), and `chars'`
and `parsed'` the text of `m`'s file with `m` applied and its parse: the
files after it are elaborated again, from the parses they had, since a
mutant changes no file but its own, unless `skipFile?` tells the state
after one. -/
def mutantState (files : Array (String × Array Char)) (parsed : Array Parsed) (names : Array (Std.HashSet String))
    (states : Array State) (m : Mutate.Mutant) (chars' : Array Char) (parsed' : Parsed) : State := Id.run do
  let orig := states[m.file]?.getD {}
  let mut st := elabParsed orig m.file chars' parsed'
  let mut drift := ({} : Drift).next orig orig (states[m.file + 1]?.getD {}) st
  for (_, chars) in files.extract (m.file + 1), j in [m.file + 1:files.size] do
    let (orig, orig') := (states[j]?.getD {}, states[j + 1]?.getD {})
    let items := match parsed[j]! with
      | .ok (_, is, _) => !is.isEmpty
      | .error _ => false
    if let some st' := skipFile? orig st orig' drift (names[j]?.getD {}) items then
      st := st'
    else
      let st' := elabParsed st j chars parsed[j]!
      drift := drift.next orig st orig' st'
      st := st'
  return st

/-- The items of each file, as `specStateOf` reads them: the first file
that does not lex or parse gives the headline of its error. -/
def itemsOf (parsed : Array Parsed) : Except String (Array (Array Item)) :=
  parsed.mapM fun
    | .error (_, msg) => throw msg.headline
    | .ok (_, items, _) => pure items

/-- The evaluator's state before each file, lowering the files in turn
(`Eval.lowerFrom`), and after the last; past a file that does not parse,
an error that no mutant reads (`mutantSpec`). -/
def lowerPrefixes (parsed : Array Parsed) : Array (Except String Eval.LState) := Id.run do
  let mut out : Array (Except String Eval.LState) := #[Eval.preludeState]
  for p in parsed do
    out := out.push <| match out.back!, p with
      | .ok st, .ok (_, items, _) => Eval.lowerFrom st #[items]
      | .error e, _ => .error e
      | .ok _, .error (_, msg) => .error msg.headline
  return out

/-- `specOf` of the files, whose parses are `parsed`, from their
`lowerPrefixes`: an error if some file does not parse, as `specStateOf`
reads them (`itemsOf`), else the state after the last file. -/
def specOfParsed (parsed : Array Parsed) (prefixes : Array (Except String Eval.LState)) : Except String Eval.Spec := do
  let _ ← itemsOf parsed
  return (← prefixes.back!).spec

/-- `specOf` of the files with the mutant `m` applied, where `parsed'` is
the parse of `m`'s file with `m` applied: the same reading of the files'
items (`itemsOf`), and lowering from the state before `m`'s file
(`lowerPrefixes`), which is that of lowering the files before it, all of
which parse if every file does (`Eval.lowerAll`). -/
def mutantSpec (parsed : Array Parsed) (prefixes : Array (Except String Eval.LState)) (m : Mutate.Mutant)
    (parsed' : Parsed) : Except String Eval.Spec := do
  let items ← itemsOf (parsed.set! m.file parsed')
  let st ← prefixes[m.file]!
  return (← Eval.lowerFrom st (items.extract m.file)).spec

/-- The rest of `s`, as text. -/
partial def readAll (s : IO.FS.Stream) (acc : String := "") : IO String := do
  let line ← s.getLine
  if line.isEmpty then return acc else readAll s (acc ++ line)

/-- What `fren mutate` decided about a mutant, for the tests of its
decisions (`Reqs/dev/Testing`). -/
structure Decision where
  id : String
  outcome : Mutate.Outcome
  /-- The checks that kill it: the key of each one's item (`Mutate.Todo.key`),
  and its own (`Mutate.keyed`). -/
  killers : Array (String × String)

/-- What the tests of `fren mutate` see of a run. -/
structure Probe where
  /-- Checks every procedure and global expectation of a
  mutant, not only those whose fingerprint it changes, and every one of
  their checks, rather than stopping at the first that kills it. -/
  exhaustive : Bool := false
  decisions : IO.Ref (Array Decision)

/-- Runs `fren mutate` (`Reqs/Mutate`), printing each surviving mutant and
the summary to stderr and the kill rates to stdout, or with `--list`, the
mutants to stdout; returns the exit code. `probe?` records the decisions. -/
def mutate (args : Args) (probe? : Option Probe := none) : IO UInt32 := do
  let p := args.paint
  let fail (msg : Msg) : IO UInt32 := do IO.eprint (argError p msg); return 2
  let some (files, states, st) ← loadBefore p args.files args.lints | return exitCode false none
  -- Each file is lexed, parsed and elaborated once here; a mutant's
  -- files are elaborated from these states, and its spec read from these
  -- parses, as `mutantsOf`, `specOf` and `elabText` would.
  let parsed := files.map (parseText ·.2)
  let names := parsed.map writtenNames
  let all := mutantsWith files parsed states
  let comp? := args.comp?.map fun t => (t.splitOn "::").foldl Lean.Name.mkStr .anonymous
  if let some c := comp? then
    unless st.comps.any (·.path == c) do
      return ← fail { code? := none, headline := s!"no procedure `{Fren.Core.showComp c}`"
                      notes := #[s!"note: the procedures are {Fren.Core.showNameList (st.comps.map (·.path))}"] }
  for id in args.mutantIds do
    unless all.any (·.id == id) do
      return ← fail { code? := none, headline := s!"no mutant `{id}`"
                      notes := #["note: `fren mutate --list` lists the mutants"]
                      fixes := (Fren.Core.similarStr id (all.map (·.id))).toArray.map fun s =>
                        { msg := s!"a mutant with a similar identifier exists: `{s}`", replacement := s } }
  let touched : Mutate.Mutant → Bool ← match args.diff? with
    | none => pure fun _ => true
    | some patch => do
      let text ← try
          if patch == "-" then readAll (← IO.getStdin) else IO.FS.readFile patch
        catch e => return ← fail { code? := none, headline := s!"could not read `{patch}`: {readError e}" }
      match Mutate.parsePatch text with
      | .error (line, why) =>
        return ← fail { code? := none, headline := s!"`{patch}` is not a unified diff"
                        notes := #[s!"note: line {line}: {why}", "note: `--diff` reads a patch such as `git diff -U0` writes"] }
      | .ok changes =>
        -- Such as a patch with absolute paths, or made in another directory.
        unless changes.isEmpty || Mutate.namesAny changes (files.map (·.1)) do
          IO.eprint (Fren.Core.renderPlain .warning
            { code? := none, headline := s!"`{patch}` changes none of the files given"
              notes := #[s!"note: it changes {", ".intercalate (changes.toList.map (s!"`{·.1}`"))}",
                "note: a file is named as given, or without the `a/` or `b/` that `git diff` writes",
                "help: run `fren mutate` where `git diff` ran, with the paths it prints"] } p)
        let ofFile := files.mapIdx fun i (path, chars) =>
          let items := match parsed[i]! with
            | .ok (toks, _, starts, _) => Mutate.itemLines chars toks starts
            | .error _ => #[]
          (Mutate.changesOf changes path, items)
        pure fun (m : Mutate.Mutant) => let (c, items) := ofFile[m.file]!; Mutate.touchedAt c items m.span.start
  let selected := Mutate.select all comp? args.mutantIds args.sample? args.seed touched args.shard?
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
  -- The answers to the queries asked so far, shared by the spec and its
  -- mutants: a query of a mutant that only reads what it leaves alone, such
  -- as its assumptions' consistency, is often one of the spec's
  -- (`Reqs/Cli#solver-queries`).
  let cache ← QueryCache.new
  let prelude := st.queryPrelude
  -- As `fren check` checks `c`: with the solver, and the checks set to
  -- testing by testing; with the internal errors, each at its place in `c`.
  let solve (s : State) (prelude : Prelude) (spec? : Except String Eval.Spec) (t : Mutate.Todo) :
      IO (Array Fren.Core.CheckResult × Array (Span × Msg)) := do
    -- A procedure's checks share the symbols of its spec.
    let (rs, refuted, missing?) ← solveComp s prelude spec? (symbolsOf spec?) t.comp t.global t.kinds args.limits cache (body := t.body)
      (examples := args.examples)
    let tested := if t.comp.tested.any then testing spec? t.comp t.global (testedKeeps t.comp t.kinds) else #[]
    let errors := refuted.map fun (r, msg) =>
      ((r.prop?.bind fun n => t.comp.props.find? (·.name == n)).map (·.span) |>.getD t.comp.span, msg)
    return (rs ++ tested, missing?.toArray.map (t.comp.span, ·) ++ errors)
  -- As `fren quickcheck` tests `c`.
  let test (_ : State) (_ : Prelude) (spec? : Except String Eval.Spec) (t : Mutate.Todo) :
      IO (Array Fren.Core.CheckResult × Array (Span × Msg)) :=
    -- A body has no checks that testing runs.
    pure (if t.body then #[] else testing spec? t.comp t.global fun _ => true, #[])
  let prefixes := lowerPrefixes parsed
  let spec? := specOfParsed parsed prefixes
  if let .error e := spec? then
    printDiag p files { file := 0, span := default, msg := Msg.internal s!"the evaluator cannot read the spec: {e}" }
  -- What each procedure's checks read in the spec. The spec's own results
  -- are computed only for procedures that some mutant changes.
  let preludeText := st.preludeText
  let originals : Std.HashMap String (Mutate.Todo × String) :=
    (Mutate.todo st).foldl (init := {}) fun m t => m.insert t.key (t, Mutate.fingerprint preludeText t.comp)
  let solved : Baseline ← IO.mkRef {}
  let tested : Baseline ← IO.mkRef {}
  let shown ← IO.mkRef (#[] : Array Msg)
  let sevs ← IO.mkRef (if spec?.toOption.isNone then #[Fren.Core.Severity.error] else #[])
  -- The checks of one way of checking that kill the mutant `st'`, and
  -- whether some check was inconclusive on it, checking only the
  -- procedures it changes, and stopping at the first that kills it,
  -- unless `probe?` is exhaustive;
  -- `run s prelude spec? t` checks `t` of the spec `s`, whose prelude,
  -- indexed, is `prelude`, and whose prelude's text is `preludeText'`.
  -- Internal errors about the spec are printed as `fren check` prints
  -- them, and those about the mutant given to `onMutant`.
  let killedBy (base : Baseline) (st' : State) (prelude' : Prelude) (preludeText' : String) (spec'? : Except String Eval.Spec)
      (run : State → Prelude → Except String Eval.Spec → Mutate.Todo → IO (Array Fren.Core.CheckResult × Array (Span × Msg)))
      (onMutant : Msg → IO Unit) : IO (Array (String × String) × Bool) := do
    let exhaustive := probe?.any (·.exhaustive)
    let mut killers := #[]
    let mut inconclusive := false
    for t in Mutate.todo st' do
      let some (t₀, fp) := originals[t.key]? | continue
      unless exhaustive || Mutate.rechecks fp (Mutate.fingerprint preludeText' t.comp) do continue
      let rs ← match (← base.get)[t.key]? with
        | some rs => pure rs
        | none =>
          let (rs, errors) ← run st prelude spec? t₀
          for (span, msg) in errors do
            printDiag p files { file := t₀.comp.file, span, msg }
            shown.modify (·.push msg)
            sevs.modify (·.push .error)
          base.modify (·.insert t.key rs)
          pure rs
      let (rs', errors) ← run st' prelude' spec'? t
      for (_, msg) in errors do onMutant msg
      let rs := Mutate.keyed rs
      let rs' := Mutate.keyed rs'
      killers := killers ++ (Mutate.killers rs rs').map fun (k, _) => (t.key, k)
      if !killers.isEmpty && !exhaustive then return (killers, inconclusive)
      inconclusive := inconclusive || Mutate.inconclusive rs rs'
    return (killers, inconclusive)
  let mut tallies : Std.HashMap Lean.Name Mutate.Tally := {}
  for m in selected do
    let chars' := m.apply files[m.file]!.2
    let parsed' := parseText chars'
    let st' := mutantState files parsed names states m chars' parsed'
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
      if let some probe := probe? then probe.decisions.modify (·.push { id := m.id, outcome := .unviable, killers := #[] })
    else
      let spec'? := mutantSpec parsed prefixes m parsed'
      if let .error e := spec'? then
        report (Msg.internal s!"the evaluator cannot read the mutant `{m.id}`: {e}") .error
      let onMutant (msg : Msg) := report { msg with notes := msg.notes.push s!"note: on the mutant `{m.id}`" } .error
      let prelude' := st'.queryPrelude
      let preludeText' := st'.preludeText
      let (killers₁, inconclusive₁) ← if args.checker.solves then killedBy solved st' prelude' preludeText' spec'? solve onMutant
        else pure (#[], false)
      let (killers₂, inconclusive₂) ← if args.checker.tests then killedBy tested st' prelude' preludeText' spec'? test onMutant
        else pure (#[], false)
      let bySolver := !killers₁.isEmpty
      let byTesting := !killers₂.isEmpty
      let killed := bySolver || byTesting
      -- Short, whatever `--timeout` is, even 0, which means none.
      let equivalent? ← if killed then pure (some false) else Mutate.equivalent st prelude st' Mutate.equivalenceTimeout cache
      let outcome := Mutate.outcome true killed (equivalent? == some true)
      tally := tally.add outcome
      if let some probe := probe? then probe.decisions.modify (·.push { id := m.id, outcome, killers := killers₁ ++ killers₂ })
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
