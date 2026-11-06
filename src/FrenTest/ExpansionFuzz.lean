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
def baseSource (seed : Nat) : String := Id.run do
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

/-- Append consumers after the established stream. Its declarations and
draws stay unchanged; these depths come from a separate seed. -/
def source (seed : Nat) : String := Id.run do
  let original := baseSource seed
  let depth := 1 + Id.run ((FrenCli.Eval.below 5).run' (FrenTest.FuzzFrontends.rngOf (seed + 0x72656164)))
  let mut body := "n"
  for _ in [0:depth] do body := s!"copying_twice({body})"
  let mut more := "\nset_option fren.lint.undecidable \"allow\"\npub fn copying_twice(value: Int): Int := value + value\n"
  more := more ++ s!"pub proc copying_constraint(n: Int): (answer: Int) \{ ensure equation: answer = {body} }\n"
  more := more ++ "pub proc copying_sink(value: Int): (answer: Int) { out answer := value }\n"
  more := more ++ s!"pub proc copying_binding(n: Int): (answer: Int) \{ call c := copying_sink({body})\n out answer := c.answer }\n"
  more := more ++ s!"expect copying_global: forall (n: Int), {body} = {body}\n"
  more := more ++ "pub proc copying_locals(n: Int) {\n"
  let mut last := "n"
  for i in [0:depth + 1] do
    let next := s!"local_{i}"
    more := more ++ s!"let {next}: Int := {last} + {last}\n"
    last := next
  more := more ++ s!"require reads_locals: {last} = {last}\n}\n"
  if seed % 17 != 8 then
    let ty := match seed % 17 with
      | 1 => "Bool" | 2 => "Seq<Int>" | 3 => "Set<Int>" | 4 => "Pair" | 5 => "Choice"
      | 9 => "String" | 10 => "Nat" | 11 => "Rel<Int, Bool>" | 12 => "Amount"
      | 13 => "Token" | 14 => "Tree" | 15 => "Positive" | _ => "Int"
    let boolean := ty == "Bool"
    let input := if boolean then "n?" else "n"
    let output := if boolean then "answer?" else "answer"
    let functionName := if boolean then "result?" else "result"
    let flag := if seed % 17 == 6 || seed % 17 == 13 then ", flag?" else ""
    more := more ++ s!"pub proc copying_typed({input}: {ty}{flag}): (det {output}: {ty}) \{ out {output} := {functionName}({input}{flag})\n ensure equation: {output} = {functionName}({input}{flag}) }\n"
  let binder (i : Nat) := s!"copying_bound_{i}"
  let lastBinder := binder (depth - 1)
  let mut pureMatch := lastBinder
  let mut indexedMatch := s!"if 0 <= {lastBinder} < q.len then q[{lastBinder}] else 0"
  for i in (List.range depth).reverse do
    let input := if i == 0 then "n" else binder (i - 1)
    pureMatch := s!"match ({input} + {input}) \{ {binder i} => {pureMatch} }"
    indexedMatch := s!"match ({input} + {input}) \{ {binder i} => {indexedMatch} }"
  more := more ++ s!"pub fn copying_matches(n: Int): Int := {pureMatch}\n"
  more := more ++ s!"pub fn copying_match_index(q: Seq<Int>, n: Int): Int := {indexedMatch}\n"
  more := more ++ "pub enum CopyingList<T> { Nil, Cons(T, CopyingList<T>) }\n"
  more := more ++ "pub fn copying_clone<T>(xs: CopyingList<T>): CopyingList<T> := match xs { CopyingList::Nil => CopyingList::Nil, CopyingList::Cons(x, tail) => CopyingList::Cons(x, copying_clone(tail)) }\n"
  let mut recursive := "xs"
  for _ in [0:depth] do recursive := s!"copying_clone({recursive})"
  -- Nat, abstract types and subset types cannot be payload arguments of
  -- a recursive enumeration. Their ordinary typed consumers remain above.
  let element := match seed % 17 with
    | 1 => "Bool" | 2 => "Seq<Int>" | 3 => "Set<Int>" | 4 => "Pair" | 5 => "Choice"
    | 9 => "String" | 11 => "Rel<Int, Bool>" | 12 => "Amount"
    | 14 => "Tree" | _ => "Int"
  more := more ++ s!"pub fn copying_recursive(xs: CopyingList<{element}>): CopyingList<{element}> := {recursive}\n"
  return original ++ more

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
  -- above compare both front ends. Hosted `hasConcat` still follows these
  -- locals repeatedly and starts fresh mention analyses. That separate
  -- front-end cost is not bounded by the evaluator's reading allowance.
  let (cli, summary, code, _) ← FrenTest.FuzzFrontends.runCli (dir / "refinement.fren") (refinement 25 0)
  unless code == 2 && summary.isNone && cli.any FrenTest.Frontends.isExpansionLimit do
    failures := failures.push s!"copying refinement limit: exit {code}, summary {summary}, diagnostics {repr cli}"
  for file in ["check_constraint_expansion_limit", "check_locals_expansion_limit"] do
    let (cli, summary, code, _) ← FrenTest.FuzzFrontends.runCli (dir / s!"{file}.fren")
      (← IO.FS.readFile s!"test/cli/commands/{file}.fren")
    unless code == 2 && summary.isNone && cli.any FrenTest.Frontends.isExpansionLimit do
      failures := failures.push s!"copying {file}: exit {code}, summary {summary}, diagnostics {repr cli}"
  return failures

end FrenTest.ExpansionFuzz
