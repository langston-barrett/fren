-- keep-sorted start
import Fren
import FrenCli.Run
import FrenTest.Messages
import Lean.Elab.Frontend
-- keep-sorted end

/-!
# Differential fuzzing of the front ends (`Reqs/dev/Testing`)

`lake exe fren_fuzz_frontends [--count N] [--seed N] [--out DIR]` generates
random specs and checks each with both front ends: `fren check`'s pipeline,
in-process, and the Lean front end, which elaborates the spec in an
environment that imports `Fren`, as the ui tests do. Their messages and
summaries must agree (`cli::agreement`); each spec where they differ is
written to `DIR` (default `.lake/fuzz`) with the difference and both
reports in comments.

Brute force is not needed, so the generator is wider than `fren_fuzz`'s,
and aims at the analyses that each front end implements on its own:
constants, defined outputs, defined and uninterpreted functions, `match`,
string methods with constant and non-constant arguments and `++`, products
of every kind of operand, and sets and relations with `card`, so that it
reaches `linear_product`, the decidable core and the lints.

What legitimately differs is normalized away (`compareFrontends`):

- Lean's own errors (`isLeanOwn`, such as `Type mismatch`) stand for any
  error that the binary reports on the same line, as `--~[hosted]` does in
  the ui tests. After a parse error (`F01xx`) the binary stops, but Lean
  recovers at the next command, so then Lean need only report an error.
- Messages are compared by line, severity and first line. The Lean front
  end shows no code, so the code itself is not compared. The values of a
  model (`for the input …`, `it can be …`, `when …`) are masked, since
  counterexample values may differ (`cli::agreement`), and so is the
  solver's reason for an undecided check, which is its own words. The
  names of a conflict's or a vacuity's constraints are compared.
- Checks whose evidence is testing, which Lean does not run, are left
  out: messages on such a member, testing's warnings, Lean's note that it
  does not run them, and the summary.
- A static error, including a denied lint, stops the binary's checks but
  not Lean's, so then the checks' results and the summary are not
  compared; and the binary drops the lints of an item with a static error
  other than a lint, so then Lean's are not compared either.
- A spec where they differ only in undecided checks (not solver errors)
  is counted apart, since the solvers' time limits may explain it.

`--avoid-known` keeps the generator clear of the differences already
known, to find others: it parenthesizes every method's receiver that is
not a name, and gives every component a set input.
-/

open Lean FrenCli FrenCli.Eval

namespace FrenFuzzFrontends

def pick (xs : Array α) [Inhabited α] : R α := do return xs[← below xs.size]!

def chance (pct : Nat) : R Bool := do return (← below 100) < pct

namespace Wide

inductive WTy where
  | int | bool | str | set | rel | enum
  deriving BEq, Inhabited

def WTy.name (relElem : String) : WTy → String
  | .int => "Int" | .bool => "Bool" | .str => "String" | .set => "Set(Int)"
  | .rel => s!"Rel({relElem}, {relElem})" | .enum => "E"

structure WScope where
  /-- A variable's text, type, and whether it is an input (so that an
  uninterpreted function may be applied to it). -/
  vars : Array (String × WTy × Bool) := #[]
  consts : Array (String × WTy) := #[]
  /-- Functions: name, parameter types, result type, and whether it has a
  body. -/
  fns : Array (String × Array WTy × WTy × Bool) := #[]
  nVariants : Nat := 0
  /-- The element type of relations: `E` or `Int`. -/
  relElem : String := "Int"
  /-- Only inputs and constants: an assumption, or an uninterpreted
  function's argument. -/
  onlyIns : Bool := false
  /-- Avoid the differences already known (`--avoid-known`). -/
  avoidKnown : Bool := false

def WScope.varsOf (sc : WScope) (t : WTy) : Array String :=
  sc.vars.filterMap fun (n, t', isIn) => if t' == t && (isIn || !sc.onlyIns) then some n else none

def WScope.constsOf (sc : WScope) (t : WTy) : Array String :=
  sc.consts.filterMap fun (n, t') => if t' == t then some n else none

def strLit : R String := pick #["\"\"", "\"a\"", "\"ab\"", "\"b\"", "\"ba\""]

def enumLit (sc : WScope) : R String := do return s!"E::V{← below sc.nVariants}"

mutual

/-- A leaf of type `t`: a variable, a constant or a literal. -/
partial def leaf (sc : WScope) (t : WTy) : R String := do
  let vs := sc.varsOf t
  let cs := sc.constsOf t
  let k ← below 10
  if k < 5 && !vs.isEmpty then return ← pick vs
  if k < 7 && !cs.isEmpty then return ← pick cs
  match t with
  | .int => return toString (← below 4)
  | .bool => pick #["true", "false"]
  | .str => strLit
  | .set => pick #["{1}", "{1, 2}", "{0, 3}"]
  | .rel => if sc.relElem == "E" then return s!"\{({← enumLit sc}, {← enumLit sc})}" else pick #["{(1, 2)}", "{(0, 0), (1, 2)}"]
  | .enum => enumLit sc

/-- An application of a function whose result has type `t`, if there is
one. The arguments of an uninterpreted one mention only inputs. -/
partial def app? (sc : WScope) (t : WTy) (d : Nat) : R (Option String) := do
  let fs := sc.fns.filter (·.2.2.1 == t)
  if fs.isEmpty then return none
  let (f, ps, _, hasBody) ← pick fs
  let asc := if hasBody then sc else { sc with onlyIns := true }
  let args ← ps.mapM (gen asc · (d - 1))
  return some s!"{f}({", ".intercalate args.toList})"

/-- A `match` on an enumeration, with arms of type `t`. -/
partial def matchOn (sc : WScope) (t : WTy) (d : Nat) : R String := do
  let scrut ← gen sc .enum 0
  let mut arms := #[]
  let n := sc.nVariants
  let covered ← below (n + 1)
  for k in [0:covered] do arms := arms.push s!"E::V{k} => {← gen sc t (d - 1)}"
  if covered < n || (← chance 5) then arms := arms.push s!"_ => {← gen sc t (d - 1)}"
  return s!"match {scrut} \{ {", ".intercalate arms.toList} }"

/-- An expression of type `t`, of depth at most `d`. -/
partial def gen (sc : WScope) (t : WTy) (d : Nat) : R String := do
  if d == 0 || (← chance 25) then return ← leaf sc t
  let sub (t : WTy) := gen sc t (d - 1)
  -- A method's receiver, in parentheses to avoid a known difference.
  let rsub (t : WTy) : R String := do
    let e ← sub t
    let plain := e.all fun c => c.isAlphanum || c == '_' || c == '?'
    return if sc.avoidKnown && !plain then s!"({e})" else e
  -- Mostly a constant, where only a constant is in the decidable core.
  let csub (t : WTy) : R String := do
    if ← chance 70 then gen { sc with vars := #[], fns := #[] } t (d - 1) else sub t
  -- Matches need an enumeration.
  let hasEnum := sc.nVariants > 0
  match t with
  | .int =>
    match ← below 14 with
    | 0 => return s!"({← sub .int} + {← sub .int})"
    | 1 => return s!"({← sub .int} - {← sub .int})"
    -- Products: mostly with a constant operand, which is linear.
    | 2 | 3 =>
      let k ← if ← chance 50 then pure (toString ((← below 3) + 2)) else
        let cs := sc.constsOf .int; if cs.isEmpty then pure "3" else pick cs
      if ← chance 50 then return s!"{k} * {← sub .int}" else return s!"{← sub .int} * {k}"
    | 4 => return s!"{← sub .int} * {← sub .int}"
    | 5 => return s!"{← rsub .str}.len"
    | 6 => return s!"{← rsub .set}.card"
    | 7 => if hasEnum then matchOn sc .int d else return s!"-({← sub .int})"
    | 8 => return s!"(if {← sub .bool} then {← sub .int} else {← sub .int})"
    | 9 | 10 => return (← app? sc .int d).getD (← leaf sc .int)
    | 11 => return s!"{← rsub .str}.index_of({← csub .str}, {← below 2})"
    | 12 => return s!"{← rsub .rel}.card"
    | _ => leaf sc .int
  | .bool =>
    match ← below 22 with
    | 0 => return s!"({← sub .bool} and {← sub .bool})"
    | 1 => return s!"({← sub .bool} or {← sub .bool})"
    | 2 => return s!"not {← sub .bool}"
    | 3 | 4 => return s!"{← sub .int} {← pick #["=", "!=", "<", "<=", ">", ">="]} {← sub .int}"
    | 5 => return s!"{← rsub .str}.{← pick #["starts_with?", "ends_with?", "contains?"]}({← csub .str})"
    | 6 => return s!"{← sub .str} {← pick #["=", "!=", "<", ">="]} {← csub .str}"
    | 7 => return s!"{← sub .str} ++ {← sub .str} {← pick #["=", "!="]} {← csub .str}"
    | 8 => return s!"{← rsub .str}.matches?({← pick #["\"a*\"", "r\"[ab]+\"", "\"\""]})"
    | 9 => return s!"{← sub .int} in {← sub .set}"
    | 10 => return s!"{← sub .set} {← pick #["subset", "=", "!="]} {← sub .set}"
    | 11 =>
      let x ← if sc.relElem == "E" then gen sc .enum 0 else sub .int
      let y ← if sc.relElem == "E" then gen sc .enum 0 else sub .int
      return s!"({x}, {y}) in {← sub .rel}"
    | 12 => return s!"{← sub .rel} {← pick #["subset", "="]} {← sub .rel}"
    | 13 => if hasEnum then return s!"{← sub .enum} {← pick #["=", "!="]} {← sub .enum}" else sub .bool
    | 14 => if hasEnum then matchOn sc .bool d else sub .bool
    | 15 | 16 => return (← app? sc .bool d).getD (← leaf sc .bool)
    | 17 => return s!"(when {← sub .bool}, {← sub .bool})"
    | 18 => return s!"({← sub .bool} iff {← sub .bool})"
    | 19 => return s!"{← rsub .set}.card {← pick #["=", ">", "<=", ">="]} {← below 3}"
    | 20 => return s!"{← sub .int} = {← sub .int} or {← sub .int} = {← sub .int} or {← sub .int} = {← sub .int}"
    | _ => leaf sc .bool
  | .str =>
    match ← below 7 with
    | 0 | 1 => return s!"({← sub .str} ++ {← sub .str})"
    | 2 => return s!"{← rsub .str}.at({← csub .int})"
    | 3 => return s!"{← rsub .str}.slice({← csub .int}, {← csub .int})"
    | 4 => return s!"{← rsub .str}.replace({← csub .str}, {← csub .str})"
    | 5 => return (← app? sc .str d).getD (← leaf sc .str)
    | _ => leaf sc .str
  | .set =>
    match ← below 6 with
    | 0 | 1 => return s!"({← sub .set} {← pick #["union", "inter", "minus"]} {← sub .set})"
    | 2 => return s!"\{{← sub .int}, {← sub .int}}"
    | 3 => if sc.relElem == "Int" then return s!"{← rsub .rel}.{← pick #["domain", "range"]}" else leaf sc .set
    | 4 => if sc.relElem == "Int" then return s!"{← rsub .rel}.image({← sub .set})" else leaf sc .set
    | _ => leaf sc .set
  | .rel =>
    match ← below 6 with
    | 0 => return s!"{← rsub .rel}.inverse"
    | 1 => return s!"{← rsub .rel}.closure"
    | 2 => return s!"({← sub .rel} join {← sub .rel})"
    | 3 => return s!"({← sub .rel} {← pick #["union", "inter", "minus"]} {← sub .rel})"
    | _ => leaf sc .rel
  | .enum =>
    match ← below 3 with
    | 0 => if hasEnum then matchOn sc .enum d else leaf sc .enum
    | 1 => return (← app? sc .enum d).getD (← leaf sc .enum)
    | _ => leaf sc .enum

end

def varName (t : WTy) (isIn : Bool) (k : Nat) : String :=
  let base := match t with
    | .int => "n" | .bool => "b" | .str => "s" | .set => "st" | .rel => "r" | .enum => "m"
  let base := if isIn then base else "o" ++ base
  if t == .bool then s!"{base}{k}?" else s!"{base}{k}"

/-- A spec with constants, functions, and components over them. -/
def genWide (avoidKnown : Bool := false) : R String := do
  let useEnum ← chance 60
  let nVariants ← if useEnum then pure ((← below 2) + 2) else pure 0
  let relElem := if useEnum && (← chance 50) then "E" else "Int"
  let mut out := "mod fz\n"
  if ← chance 40 then
    out := out ++ "set_option fren.lint.membership_chain \"warn\"\nset_option fren.lint.definable_output \"warn\"\n"
  out := out ++ "\n"
  if useEnum then
    out := out ++ s!"pub enum E \{ {", ".intercalate ((List.range nVariants).map (s!"V{·}"))} }\n"
  let mut sc : WScope := { nVariants, relElem, avoidKnown }
  -- Constants, each over the earlier ones.
  for k in [0:← below 4] do
    let t ← pick #[WTy.int, .int, .str, .bool, .set]
    let e ← gen sc t 2
    let n := s!"K{k}"
    out := out ++ s!"pub const {n}: {t.name relElem} := {e}\n"
    sc := { sc with consts := sc.consts.push (n, t) }
  -- Functions: defined ones over their parameters, and uninterpreted ones.
  for k in [0:← below 3] do
    let r ← pick #[WTy.int, .bool, .int, .str]
    let ps ← (List.range ((← below 2) + 1)).toArray.mapM fun _ => pick #[WTy.int, .int, .str, .bool]
    let name := if r == .bool then s!"f{k}?" else s!"f{k}"
    if ← chance 60 then
      let params := ps.mapIdx fun i t => (if t == .bool then s!"x{i}?" else s!"x{i}", t)
      -- The body sees only its parameters and the constants.
      let body ← gen { sc with vars := params.map fun (n, t) => (n, t, true) } r 2
      let ty := if r == .bool then "" else s!": {r.name relElem}"
      let ps := ", ".intercalate (params.toList.map fun (n, t) => if t == .bool then n else s!"{n}: {t.name relElem}")
      out := out ++ s!"pub fn {name}({ps}){ty} := {body}\n"
      sc := { sc with fns := sc.fns.push (name, params.map (·.2), r, true) }
    else
      let ty := if r == .bool then "" else s!": {r.name relElem}"
      out := out ++ s!"pub fn {name}({", ".intercalate (ps.toList.map (·.name relElem))}){ty}\n"
      sc := { sc with fns := sc.fns.push (name, ps, r, false) }
  -- Each earlier comp: its name, inputs, and visible variables.
  let mut comps : Array (String × Array (String × WTy) × Array (String × WTy)) := #[]
  for c in [0:(← below 2) + 1] do
    out := out ++ s!"\npub comp c{c} \{\n"
    let mut vars : Array (String × WTy × Bool) := #[]
    let mut shown : Array (String × WTy) := #[]
    for k in [0:(← below 4) + 1] do
      let t ← pick (#[WTy.int, .int, .bool, .str, .set, .rel] ++ (if useEnum then #[WTy.enum] else #[]))
      let n := varName t true k
      vars := vars.push (n, t, true)
      shown := shown.push (n, t)
      out := out ++ s!"    in {n}{if t == .bool then "" else s!": {t.name relElem}"}\n"
    -- The binary declares no sets for a `card` of a literal unless a
    -- variable is a set, a known difference.
    if avoidKnown then
      vars := vars.push ("st9", .set, true)
      out := out ++ "    in st9: Set(Int)\n    assume a9: not 7 in st9\n"
    -- An instance of an earlier comp, its inputs bound to expressions of
    -- this one's.
    if !comps.isEmpty && (← chance 50) then
      let (d, ins, vis) ← pick comps
      let isc := { sc with vars, onlyIns := true }
      let bs ← ins.mapM fun (x, t) => do return s!"{x} := {← gen isc t 1}"
      out := out ++ s!"    inst w: {d} \{ {", ".intercalate bs.toList} }\n"
      vars := vars ++ vis.map fun (x, t) => (s!"w.{x}", t, false)
    let outTys := #[WTy.int, .bool] ++ (if useEnum then #[WTy.enum] else #[])
    let mut defs : Array (String × WTy) := #[]
    for k in [0:(← below 3) + 1] do
      let isDef ← chance 40
      let t ← if isDef then pick #[WTy.int, .bool, .str, .set] else pick outTys
      let n := varName t false k
      if isDef then defs := defs.push (n, t)
      else
        let isPub ← chance 80
        if isPub then shown := shown.push (n, t)
        let mods := s!"{if isPub then "pub " else ""}{if ← chance 40 then "det " else ""}out"
        out := out ++ s!"    {mods} {n}{if t == .bool then "" else s!": {t.name relElem}"}\n"
      vars := vars.push (n, t, false)
    let csc := { sc with vars }
    -- A definition may mention any variable, so definitions may form a
    -- cycle (`F0411`), but seldom.
    for (n, t) in defs do
      let others := if ← chance 85 then vars.filter (fun v => v.2.2 || !defs.any (·.1 == v.1)) else vars.filter (·.1 != n)
      let e ← gen { csc with vars := others } t 2
      let isPub ← chance 60
      if isPub then shown := shown.push (n, t)
      out := out ++ s!"    {if isPub then "pub " else ""}out {n}{if t == .bool then "" else s!": {t.name relElem}"} := {e}\n"
    for k in [0:← below 2] do
      out := out ++ s!"    assume a{k}: {← gen { csc with onlyIns := true } .bool 2}\n"
    for k in [0:(← below 3) + 1] do
      out := out ++ s!"    req q{k}: {← gen csc .bool 3}\n"
    for k in [0:← below 3] do
      let tested := if ← chance 5 then "set_option fren.evidence \"tested\" in " else ""
      let e ← if ← chance 50 then pure s!"when {← gen csc .bool 1}, {← gen csc .bool 2}" else gen csc .bool 3
      out := out ++ s!"    {tested}expect x{k}: {e}\n"
    out := out ++ "}\n"
    comps := comps.push (s!"c{c}", vars.filterMap (fun (n, t, i) => if i then some (n, t) else none), shown)
  return out

end Wide

/-! ### Comparing the front ends -/

open FrenTest.Ui (Diagnostic)

/-- Replaces the text between `start` and the first `stop` after it (or
the end) with `…`. -/
def maskBetween (s start : String) (stops : List String) : String :=
  match s.splitOn start with
  | pre :: rest@(_ :: _) =>
    let after := start.intercalate rest
    let cut := stops.filterMap fun st => match after.splitOn st with
      | a :: b :: more => some (a.length, st ++ st.intercalate (b :: more))
      | _ => none
    let tail := ((cut.toArray.qsort (·.1 < ·.1))[0]?.map (·.2)).getD ""
    pre ++ start ++ "…" ++ tail
  | _ => s

/-- The first line of a message, with the values of a model masked:
counterexample values may differ (`cli::agreement`), and the Lean front end
may show none. Names, such as those of a conflict's constraints, are kept. -/
def normHead (text : String) : String :=
  let head := (text.splitOn "\n").head!
  -- Why a check is undecided is the solver's own words.
  let head := if head.startsWith "could not decide whether" then (head.splitOn ": ").head! else head
  let head := maskBetween head "for the input " [", no outputs", ", it can be"]
  let head := maskBetween head ", it can be " []
  maskBetween head " when " []

/-- A check's result, rather than a static error or a lint. -/
def isCheckResult (d : Diagnostic) : Bool :=
  d.code?.any (·.startsWith "F06") ||
  ["could not decide whether ", "the assumptions of ", " is not realizable: ", "an index of ",
   "the assumption `", "expectation `", " is vacuous: ", " is redundant: ", " is not determined by the inputs",
   "is false when ", "conflicts with ", "testing "].any fun p => (d.text.splitOn "\n").head!.contains p

/-- Lean's own errors, which the Lean front end reports for parse and type
errors that the binary reports with a Fren code (as `--~[hosted]` does in
the ui tests). -/
def leanOwn : List String :=
  ["Type mismatch", "type mismatch", "Application type mismatch", "failed to synthesize",
   "unexpected token", "unexpected identifier", "unknown identifier", "unknown constant",
   "Function expected", "function expected", "invalid", "ambiguous", "elaboration function",
   "typeclass instance problem", "don't know how to synthesize", "unterminated"]

def isLeanOwn (d : Diagnostic) : Bool := leanOwn.any (d.text.startsWith ·)

/-- The 1-based lines of each top-level item of `text`: an item starts at
a line that is neither indented, blank, a comment nor a closing brace. -/
def itemOf (text : String) : Array Nat := Id.run do
  let mut out := #[0]
  let mut item := 0
  for line in text.splitOn "\n", k in [1:text.length + 2] do
    if !line.isEmpty && !line.startsWith " " && !line.startsWith "}" && !line.startsWith "--" then item := k
    out := out.push item
  return out

/-- How the front ends' reports on a spec differ: each difference as a
line, and whether all of them are about inconclusive results, which the
solvers' time limits can explain. -/
def compareFrontends (text : String) (cli hosted : Array Diagnostic) (cliSum hostedSum : Option String) :
    Array String × Bool := Id.run do
  -- A parse error stops the binary, but Lean recovers at the next
  -- command: then Lean need only report an error too.
  if cli.any (·.code?.any (·.startsWith "F01")) then
    if hosted.any (·.severity == "error") then return (#[], false)
    return (#["fren reports a parse error, and Lean no error"], false)
  let lines := text.splitOn "\n"
  let lineText (n : Nat) := lines[n - 1]?.getD ""
  -- Checks whose evidence is testing, which Lean does not run.
  let tested (d : Diagnostic) := (lineText d.line).contains "fren.evidence \"tested\""
  let items := itemOf text
  let itemAt (n : Nat) := items[n]?.getD 0
  -- The binary drops the lints of an item with a static error other than
  -- a lint, as the ui tests say (`constants_static.fren`).
  let isLint (d : Diagnostic) := d.code?.any (·.startsWith "F07")
  let errorItems := (cli.filter fun d => d.severity == "error" && !isCheckResult d && !isLint d).map (itemAt ·.line)
    ++ (hosted.filter fun d => d.severity == "error" && isLeanOwn d).map (itemAt ·.line)
  -- A static error, including a denied lint, stops the binary's checks,
  -- but not Lean's.
  let staticError := cli.any fun d => d.severity == "error" && !isCheckResult d
  -- Testing's own messages, which Lean does not run, and Lean's note that
  -- it does not.
  let anyTested := text.contains "fren.evidence \"tested\""
  let testing (d : Diagnostic) := anyTested &&
    (d.code?.any (["F0609", "F0610", "F0612"].contains ·) || (d.severity == "info" && d.text.contains "set to testing"))
  let keep (d : Diagnostic) := !tested d && !testing d && !(staticError && isCheckResult d)
  let mut cs := cli.filter keep
  let mut hs := hosted.filter keep
  -- The same message: same line, severity and masked headline.
  let mut hostedOnly := #[]
  for h in hs do
    match cs.findIdx? fun c => c.line == h.line && c.severity == h.severity && normHead c.text == normHead h.text with
    | some i => cs := cs.eraseIdx! i
    | none => hostedOnly := hostedOnly.push h
  -- Lean's own errors for those of the binary on the same line.
  let leanLines := hostedOnly.filter isLeanOwn |>.map (·.line)
  hostedOnly := hostedOnly.filter fun h => !(isLeanOwn h && cs.any fun c => c.line == h.line && c.severity == "error")
  cs := cs.filter fun c => !(c.severity == "error" && leanLines.contains c.line)
  -- Lean's lints of an item with a static error, which the binary drops.
  hostedOnly := hostedOnly.filter fun h => !errorItems.contains (itemAt h.line)
  let mut out := #[]
  for c in cs do out := out.push s!"line {c.line}: only fren reports {c.severity}[{c.code?.getD "-"}]: {(c.text.splitOn "\n").head!}"
  for h in hostedOnly do out := out.push s!"line {h.line}: only Lean reports {h.severity}: {(h.text.splitOn "\n").head!}"
  -- Undecided for lack of time, not for a solver error.
  let inconclusive (d : Diagnostic) := d.text.startsWith "could not decide whether" && !d.text.contains "solver error"
  let allInconclusive := cs.all inconclusive && hostedOnly.all inconclusive
  -- The summary, unless a check is tested, or a static error stops the
  -- binary.
  let mut sumDiffers := false
  if !anyTested && !staticError && cliSum != hostedSum then
    sumDiffers := true
    out := out.push s!"summary: fren says `{cliSum.getD "(none)"}`, Lean says `{hostedSum.getD "(none)"}`"
  -- A summary that differs only in its inconclusive count is a matter of
  -- time too.
  let sumOk := !sumDiffers || (cliSum.getD "").contains "inconclusive" && allInconclusive && !cs.isEmpty || !hostedOnly.isEmpty
  return (out, allInconclusive && sumOk && !out.isEmpty)

/-- Checks `text` with both front ends; returns how they differ, whether
only in inconclusive results, and the two reports. -/
def runFrontends (env : Environment) (dir : System.FilePath) (text : String) :
    IO (Array String × Bool × String × Array String) := do
  let path := dir / "current.fren"
  IO.FS.writeFile path text
  let (out, _) ← IO.FS.withIsolatedStreams (FrenCli.check { files := #[path.toString] })
  let (cli, cliSum) := FrenTest.Ui.cliDiagnostics path.toString out
  let (hosted, hostedSum) ← FrenTest.Ui.hostedDiagnostics env path.toString text
  let (found, flaky) := compareFrontends text cli hosted cliSum hostedSum
  let render (ds : Array Diagnostic) (s : Option String) :=
    String.join (ds.toList.map fun d => s!"--   {d.line}: {d.severity}{(d.code?.map (s!"[{·}]")).getD ""}: {(d.text.splitOn "\n").head!}\n")
      ++ s!"--   summary: {s.getD "(none)"}\n"
  return (found, flaky, s!"-- fren:\n{render cli cliSum}-- Lean:\n{render hosted hostedSum}",
    cli.filterMap fun d => if d.severity == "error" then d.code? else none)

unsafe def loadFren : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  importModules #[{ module := `Fren }] {} (loadExts := true)

/-- Compares the front ends on the given files, to reproduce or minimize a
difference. -/
unsafe def mainFiles (files : List String) (dir : String) : IO UInt32 := do
  let env ← loadFren
  let mut bad := 0
  for f in files do
    let (found, _, reports, _) ← runFrontends env dir (← IO.FS.readFile f)
    IO.println s!"{f}: {if found.isEmpty then "the front ends agree" else "the front ends differ"}"
    for x in found do IO.println s!"  {x}"
    unless found.isEmpty do bad := bad + 1; IO.println reports
  return if bad == 0 then 0 else 1

def rngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0xf407⟩

/-- A difference without its line, names and values, to group the
specs that differ alike. -/
def signature (f : String) : String := Id.run do
  let f := match f.splitOn ": " with
    | l :: rest => if l.startsWith "line " then ": ".intercalate rest else f
    | [] => f
  let mut out := ""
  let mut inQuote := false
  for c in f.toList do
    if c == '`' then
      inQuote := !inQuote
      if inQuote then out := out ++ "`_`"
    else if !inQuote then out := out.push c
  let masked := maskBetween out "for the input " [", no outputs", ", it can be"]
  return maskBetween (maskBetween masked "fren says " [", Lean says"]) "Lean says " []

/-- What a worker found on one spec, one JSON object per line of
`DIR/results.jsonl`, so that a worker that crashes loses nothing. -/
structure Outcome where
  seed : Nat
  /-- `ok`, `differ`, `inconclusive` (differ only in undecided checks) or
  `crash`. -/
  status : String
  errors : Array String := #[]
  signatures : Array String := #[]
  deriving ToJson, FromJson

def resultsFile (dir : String) : System.FilePath := dir / "results.jsonl"

def progressFile (dir : String) : System.FilePath := dir / "current.seed"

def record (dir : String) (o : Outcome) : IO Unit := do
  let h ← IO.FS.Handle.mk (resultsFile dir) .append
  h.putStrLn (toJson o).compress
  h.flush

/-- Checks the specs of seeds `[seed, seed + count)` in this process,
writing each one's outcome to the results file. -/
unsafe def worker (count seed : Nat) (dir : String) (avoidKnown : Bool) : IO UInt32 := do
  let env ← loadFren
  for i in [0:count] do
    let s := seed + i
    IO.FS.writeFile (progressFile dir) (toString s)
    let text : String := Id.run ((Wide.genWide avoidKnown).run' (rngOf s))
    let t0 ← IO.monoMsNow
    let (found, flaky, reports, errs) ← runFrontends env dir text
    let elapsed := (← IO.monoMsNow) - t0
    if elapsed > 20000 then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s"
    let status := if found.isEmpty then "ok" else if flaky then "inconclusive" else "differ"
    unless found.isEmpty do
      let file : System.FilePath := dir / s!"{if flaky then "inconclusive-" else ""}fe-seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz_frontends{if avoidKnown then " --avoid-known" else ""} --seed {s}\n"
        ++ header ++ reports ++ text)
      IO.eprintln s!"seed {s}: front ends differ{if flaky then " (only in inconclusive results)" else ""}, written to {file}"
      for f in found.extract 0 4 do IO.eprintln s!"  {f}"
    record dir { seed := s, status, errors := errs.toList.eraseDups.toArray, signatures := found.map signature }
  return 0

/-- Counts `x` in a tally. -/
def tally (xs : Array (String × Nat × Nat)) (x : String) (seed : Nat) : Array (String × Nat × Nat) :=
  match xs.findIdx? (·.1 == x) with
  | some k => xs.modify k fun (x, n, first) => (x, n + 1, first)
  | none => xs.push (x, 1, seed)

/-- Runs workers until every seed is checked. The solver can abort the
process (a failed assertion in cvc5), so each spec runs in a worker,
and a crash is recorded as the outcome of the spec it was checking. -/
unsafe def mainFrontends (count seed : Nat) (dir : String) (avoidKnown : Bool) : IO UInt32 := do
  let start ← IO.monoMsNow
  IO.FS.writeFile (resultsFile dir) ""
  let mut next := seed
  while next < seed + count do
    let args := #["--worker", "--count", toString (seed + count - next), "--seed", toString next, "--out", dir]
      ++ (if avoidKnown then #["--avoid-known"] else #[])
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    if code == 0 then break
    let crashed := ((← IO.FS.readFile (progressFile dir)).trimAscii.toString.toNat?).getD next
    IO.eprintln s!"seed {crashed}: the worker crashed (exit {code})"
    let text : String := Id.run ((Wide.genWide avoidKnown).run' (rngOf crashed))
    IO.FS.writeFile (dir / s!"crash-seed{crashed}.fren")
      (s!"-- fren_fuzz_frontends{if avoidKnown then " --avoid-known" else ""} --seed {crashed}: crashed\n" ++ text)
    record dir { seed := crashed, status := "crash" }
    next := crashed + 1
  let outcomes : Array Outcome := ((← IO.FS.readFile (resultsFile dir)).splitOn "\n").toArray.filterMap fun l =>
    (Json.parse l >>= fromJson? : Except String Outcome).toOption
  let mut sigs := #[]
  let mut codes := #[]
  for o in outcomes do
    for g in o.signatures do sigs := tally sigs g o.seed
    for e in o.errors do codes := tally codes e o.seed
  unless sigs.isEmpty do
    IO.eprintln "differences, by kind (how many, and the first seed):"
    for (g, n, first) in sigs.qsort (·.2.1 > ·.2.1) do IO.eprintln s!"  {n} × seed {first}: {g}"
  let n (st : String) := (outcomes.filter (·.status == st)).size
  let codeList := ", ".intercalate ((codes.qsort (·.2.1 > ·.2.1)).toList.map fun (e, k, _) => s!"{e} ×{k}")
  IO.eprintln s!"specs with errors from `fren check`: {(outcomes.filter (!·.errors.isEmpty)).size} ({codeList})"
  IO.eprintln s!"fren_fuzz_frontends: {outcomes.size} specs in {((← IO.monoMsNow) - start) / 1000}s, {n "differ"} where \
    the front ends differ, {n "inconclusive"} more only in inconclusive results, {n "crash"} crashed"
  return if n "differ" + n "crash" == 0 then 0 else 1

def usage : String := "usage: fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--avoid-known] | --files FILE... | [--avoid-known] --print SEED"

unsafe def main (args : List String) : IO UInt32 := do
  if let "--files" :: files := args then
    IO.FS.createDirAll ".lake/fuzz"
    return ← mainFiles files ".lake/fuzz"
  let avoidKnown := args.contains "--avoid-known"
  let args := args.filter (· != "--avoid-known")
  if let ["--print", n] := args then
    let some s := n.toNat? | IO.eprintln usage; return 2
    IO.print (Id.run ((Wide.genWide avoidKnown).run' (rngOf s)))
    return 0
  let rec parse : List String → Nat × Nat × String → Option (Nat × Nat × String)
    | [], a => some a
    | "--count" :: n :: rest, (_, s, d) => n.toNat?.bind fun n => parse rest (n, s, d)
    | "--seed" :: n :: rest, (c, _, d) => n.toNat?.bind fun n => parse rest (c, n, d)
    | "--out" :: d :: rest, (c, s, _) => parse rest (c, s, d)
    | _, _ => none
  let isWorker := args.contains "--worker"
  let args := args.filter (· != "--worker")
  let some (count, seed, dir) := parse args (100, 0, ".lake/fuzz") | IO.eprintln usage; return 2
  IO.FS.createDirAll dir
  if isWorker then worker count seed dir avoidKnown else mainFrontends count seed dir avoidKnown

end FrenFuzzFrontends

unsafe def main (args : List String) : IO UInt32 := FrenFuzzFrontends.main args
