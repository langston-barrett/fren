-- keep-sorted start
import FrenTest.FuzzFrontends
-- keep-sorted end

/-! An independent stream for evaluator-copying regressions. It leaves
all seeds of the existing front-end corpus unchanged. Large deliberate
resource failures are checked separately from the ordinary constructs. -/

namespace FrenTest.ExpansionFuzz

/-- Local-definition expansion used both below and above the allowance. -/
def refinement (depth seed : Nat) : String := Id.run do
  let mut source := "pub proc abstract_value(n: Int): (answer: Int) {\n"
  let mut last := "n"
  for i in [0:depth] do
    let next := s!"hidden_{i}"
    source := source ++ s!"    let {next}: Int := {last} + {last}\n"
    last := next
  source := source ++ s!"    ensure value: answer = {last} + {seed}\n}\n"
  source := source ++ s!"pub proc concrete_value(n: Int): (answer: Int) \{ out answer := n * {2 ^ depth} + {seed} }\n"
  return source ++ "expect compares(n: Int) {\n    call c := concrete_value(n)\n    refines c abstract_value(n)\n}\n"

/-- Duplicated arguments of several types, generic and higher-order
applications, nested binders, matches, fields, and refinement locals. -/
def source (seed : Nat) : String := Id.run do
  if seed % 17 == 8 then return refinement (1 + seed % 4) seed
  let depth := 1 + (seed / 17) % 5
  let (decls, ty, leaf, apply, extra) : String × String × String × (String → String) × String := match seed % 17 with
    | 0 => (s!"pub fn duplicate(x: Int): Int := x + x + {seed}\n", "Int", "n", fun x => s!"duplicate({x})", "")
    | 1 => ("pub fn duplicate?(x?): Bool := x? and x?\n", "Bool", "n?", fun x => s!"duplicate?({x})", "")
    | 2 => ("pub fn duplicate(x: Seq<Int>): Seq<Int> := x ++ x\n", "Seq<Int>", "n", fun x => s!"duplicate({x})", "")
    | 3 => ("pub fn duplicate(x: Set<Int>): Set<Int> := x union x\n", "Set<Int>", "n", fun x => s!"duplicate({x})", "")
    | 4 => (s!"pub struct Pair \{ a: Int, b: Int }\npub fn duplicate(x: Pair): Pair := Pair \{ a := x.a + x.b, b := x.a + x.b + {seed} }\n", "Pair", "n", fun x => s!"duplicate({x})", "")
    | 5 => ("pub enum Choice { A, B }\npub fn duplicate(x: Choice): Choice := match x { Choice::A => x, Choice::B => x }\n", "Choice", "n", fun x => s!"duplicate({x})", "")
    | 6 => ("pub fn duplicate<T>(x: T, flag?): T := if flag? then x else x\n", "Int", "n", fun x => s!"duplicate({x}, flag?)", ", flag?")
    | 7 => (s!"pub fn duplicate(f: fn(Int) -> Int, x: Int): Int := f(x) + f(x + 1)\n", "Int", "n", fun x => s!"duplicate(|v| v + {seed}, {x})", "")
    | 9 => ("pub fn duplicate(x: String): String := x ++ x\n", "String", "n", fun x => s!"duplicate({x})", "")
    | 10 => ("pub fn duplicate(x: Nat): Nat := x + x\n", "Nat", "n", fun x => s!"duplicate({x})", "")
    | 11 => ("pub fn duplicate(x: Rel<Int, Bool>): Rel<Int, Bool> := x union x\n", "Rel<Int, Bool>", "n", fun x => s!"duplicate({x})", "")
    | 12 => ("pub struct Amount(Int)\npub fn duplicate(x: Amount): Amount := x + x\n", "Amount", "n", fun x => s!"duplicate({x})", "")
    | 13 => ("pub type Token\npub fn duplicate(x: Token, flag?): Token := if flag? then x else x\n", "Token", "n", fun x => s!"duplicate({x}, flag?)", ", flag?")
    | 14 => ("pub enum Tree { Leaf, Branch(Tree, Tree) }\npub fn duplicate(x: Tree): Tree := Tree::Branch(x, x)\n", "Tree", "n", fun x => s!"duplicate({x})", "")
    | 15 => ("pub type Positive = n: Int where invariant: n > 0\npub fn duplicate(x: Positive): Positive := x + x\n", "Positive", "n", fun x => s!"duplicate({x})", "")
    | 16 => ("pub fn duplicate(x: Int): Int := if forall (p?: Bool), p? or not p? then x + x else x\n", "Int", "n", fun x => s!"duplicate({x})", "")
    | _ => unreachable!
  let mut body := leaf
  for _ in [0:depth] do body := apply body
  let parameter := if ty == "Bool" then "n?" else "n"
  let name := if ty == "Bool" then "result?" else "result"
  return s!"-- independent copying seed {seed}\nset_option fren.lint.undecidable \"allow\"\n{decls}pub fn {name}({parameter}: {ty}{extra}): {ty} := {body}\n"

/-- Exercise real reports, including the explicit resource-limit
exception. An internal error, a wrong exit or a hosted static error stays
blocking under the comparison harness. -/
unsafe def run (count : Nat) (start := 0) : IO (Array String) := do
  let env ← FrenTest.FuzzFrontends.loadFren
  let dir : System.FilePath := ".lake/expansion-fuzz"
  IO.FS.createDirAll dir
  let mut failures := #[]
  for seed in [start:start + count] do
    let ran ← FrenTest.FuzzFrontends.runFrontends env (dir / "current.fren") (source seed)
    unless ran.comparison.found.isEmpty && !(ran.cli.any (·.severity == "error")) do
      failures := failures.push s!"copying seed {seed}: {ran.comparison.found}\n{ran.reports}"
  if start != 0 then return failures
  -- Error cases have their own specs, so they never stop the checks of
  -- the ordinary corpus. The same limit is also tested by CLI snapshots.
  for (name, text) in #[("functions", ← IO.FS.readFile "test/cli/commands/check_expansion_limit.fren")] do
    let ran ← FrenTest.FuzzFrontends.runFrontends env (dir / s!"{name}.fren") text
    unless ran.comparison.found.isEmpty do
      failures := failures.push s!"copying limit {name}: {ran.comparison.found}\n{ran.reports}"
    unless ran.cli.any FrenTest.Frontends.isExpansionLimit do
      failures := failures.push s!"copying limit {name}: no resource diagnostic\n{ran.reports}"
  -- The large refinement is a reader-resource probe. Its smaller forms
  -- above compare both front ends; constructing the hosted proof of the
  -- huge form is itself expensive and is not needed to check this limit.
  let (cli, summary, code, _) ← FrenTest.FuzzFrontends.runCli (dir / "refinement.fren") (refinement 25 0)
  unless code == 2 && summary.isNone && cli.any FrenTest.Frontends.isExpansionLimit do
    failures := failures.push s!"copying refinement limit: exit {code}, summary {summary}, diagnostics {repr cli}"
  return failures

end FrenTest.ExpansionFuzz
