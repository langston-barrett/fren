-- keep-sorted start
import FrenTest.FuzzFrontends.Bodies
import FrenTest.FuzzFrontends.Claims
import FrenTest.FuzzFrontends.Contracts
import FrenTest.FuzzFrontends.Counts
import FrenTest.FuzzFrontends.EmptyArguments
import FrenTest.FuzzFrontends.FactChain
import FrenTest.FuzzFrontends.GenericElements
import FrenTest.FuzzFrontends.GoalHeads
import FrenTest.FuzzFrontends.Guards
import FrenTest.FuzzFrontends.Inductions
import FrenTest.FuzzFrontends.Patterns
import FrenTest.FuzzFrontends.PrimedNames
import FrenTest.FuzzFrontends.Recursion
import FrenTest.FuzzFrontends.Requires
import FrenTest.FuzzFrontends.Sites
import FrenTest.FuzzFrontends.Traits
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A spec with constants, functions, and components over them, and its
*cuts*: the spec as it stands before each group of items appended after
`bodyFns`, which must add no static error (`corpusFailures`). -/
def genWideCuts (avoidKnown : Bool := false) : R (String × Array String) := do
  let useEnum ← chance 60
  let nVariants ← if useEnum then pure ((← below 2) + 2) else pure 0
  let relElem := if useEnum && (← chance 50) then "E" else "Int"
  let ordered ← chance 50
  let mut out := "mod fz\n"
  if ← chance 40 then
    out := out ++ "set_option fren.lint.membership_chain \"warn\"\nset_option fren.lint.definable_output \"warn\"\n"
  out := out ++ "\n"
  if useEnum then
    out := out ++ s!"pub {if ordered then "ordered " else ""}enum E \{ {", ".intercalate ((List.range nVariants).map (s!"V{·}"))} }\n"
  let hasMs ← chance 40
  if hasMs then out := out ++ "pub ordered struct Ms(Int)\n"
  let ms := if hasMs then #[WTy.ms] else #[]
  let hasPay ← chance 40
  -- Sometimes generic, as `P<Int>`, whose variables' types are written so
  -- below.
  let genericPay ← chance 50
  if hasPay then
    out := out ++ (if genericPay then "pub enum P<X> { A, B(X), C(Bool) }\n" else "pub enum P { A, B(Int), C(Bool) }\n")
  let pays := if hasPay then #[WTy.pay] else #[]
  -- Sometimes sequences, whose indexes may be out of range, and a struct
  -- with one beside another field, its procedures often enumerated.
  let hasSeq ← chance 30
  if hasSeq then out := out ++ "pub struct Rq { q: Seq<Int>, n: Int }\npub struct Bx<T> { v: T }\n"
  let seqs := if hasSeq then #[WTy.seq, .rq, .bx] else #[]
  -- Sometimes counts written out, as `exactly_one?` and `at_most_one?` are
  -- defined, at `Int`, `Nat` and the newtype `Ms`, through functions and
  -- constants (`countSum`), which both front ends must read alike.
  let hasCounts ← chance 35
  let mut countNewtypes := #[]
  if hasCounts then
    let (decls, nts) ← countDecls
    out := out ++ decls
    countNewtypes := nts
    if hasMs then out := out ++ "pub fn indm(c?): Ms := if c? then Ms(1) else Ms(0)\n"
  let mut sc : WScope := { nVariants, ordered, relElem, avoidKnown, hasMs, hasPay, hasSeq }
  -- Constants, each over the earlier ones.
  for k in [0:← below 4] do
    let t ← pick (#[WTy.int, .int, .str, .bool, .set] ++ ms)
    let e ← gen sc t 2
    let n := s!"K{k}"
    out := out ++ s!"pub const {n}: {t.name relElem} := {e}\n"
    sc := { sc with consts := sc.consts.push (n, t) }
  -- Functions: defined ones over their parameters, and uninterpreted ones.
  for k in [0:← below 3] do
    let r ← pick (#[WTy.int, .bool, .int, .str] ++ ms)
    let ps ← (List.range ((← below 2) + 1)).toArray.mapM fun _ => pick (#[WTy.int, .int, .str, .bool] ++ ms)
    let name := if r == .bool then s!"f{k}?" else s!"f{k}"
    if ← chance 60 then
      let params := ps.mapIdx fun i t => (if t == .bool then s!"x{i}?" else s!"x{i}", t)
      -- The body sees only its parameters and the constants.
      let body ← gen { sc with vars := params.map fun (n, t) => (n, t, true) } r 2
      let ty := if r == .bool then "" else s!": {r.name relElem}"
      let ps := ", ".intercalate (params.toList.map fun (n, t) => if t == .bool then n else s!"{n}: {t.name relElem}")
      out := out ++ s!"pub fn {name}({ps}){ty} := {body}\n"
      sc := { sc with fns := sc.fns.push (name, params.map (·.2), r, true) }
    else if r != .bool && (← chance 50) then
      -- An uninterpreted function with a contract, whose postconditions
      -- may contradict each other, so that what applies it rests on its
      -- realizability (`ContractRealizability`, `Reqs/Evidence`).
      let params := ps.mapIdx fun i t => (if t == .bool then s!"x{i}?" else s!"x{i}", t)
      let csc := { sc with vars := params.map (fun (n, t) => (n, t, true)) |>.push ("r", r, false) }
      let decls := ", ".intercalate (params.toList.map fun (n, t) => if t == .bool then n else s!"{n}: {t.name relElem}")
      let mut clauses := ""
      -- Clause names now and then the names that the code gives facts
      -- itself, so that nothing reads a fact's sort from its name.
      let names := #["nat", "c", "post", "equation", "ok"]
      if ← chance 30 then
        let n := if ← chance 30 then "nat" else "p"
        clauses := clauses ++ s!"    require {n}0: {← gen { csc with vars := csc.vars.pop } .bool 2}\n"
      for j in [0:(← below 2) + 1] do
        let n ← pick names
        let n := if j == 0 && n == "nat" then n else s!"{n}{j}"
        clauses := clauses ++ s!"    ensure {n}: {← gen csc .bool 2}\n"
      out := out ++ s!"pub fn {name}({decls}): (r: {r.name relElem}) \{\n{clauses}}\n"
      sc := { sc with fns := sc.fns.push (name, ps, r, false) }
    else
      let ty := if r == .bool then "" else s!": {r.name relElem}"
      out := out ++ s!"pub fn {name}({", ".intercalate (ps.toList.map (·.name relElem))}){ty}\n"
      sc := { sc with fns := sc.fns.push (name, ps, r, false) }
  -- Each earlier comp: its name, inputs, and visible variables.
  let mut comps : Array (String × Array (String × WTy) × Array (String × WTy)) := #[]
  for c in [0:(← below 2) + 1] do
    -- Its parameters, results and block, one to a line.
    let mut params := ""
    let mut results := ""
    let mut body := ""
    let mut vars : Array (String × WTy × Bool) := #[]
    let mut shown : Array (String × WTy) := #[]
    for k in [0:(← below 4) + 1] do
      let t ← pick (#[WTy.int, .int, .bool, .str, .set, .rel] ++ (if useEnum then #[WTy.enum] else #[]) ++ ms ++ pays ++ seqs)
      let n := varName t true k
      vars := vars.push (n, t, true)
      shown := shown.push (n, t)
      params := params ++ s!"    {n}{if t == .bool then "" else s!": {t.name relElem}"},\n"
    -- A call of an earlier procedure, with expressions of this one's
    -- parameters as its arguments.
    if !comps.isEmpty && (← chance 50) then
      let (d, ins, vis) ← pick comps
      let isc := { sc with vars, onlyIns := true }
      let args ← ins.mapM fun (_, t) => gen isc t 1
      body := body ++ s!"    call w := {d}({", ".intercalate args.toList})\n"
      vars := vars ++ vis.map fun (x, t) => (s!"w.{x}", t, false)
    -- Outputs of `P` more often, for clashes of variants.
    let outTys := #[WTy.int, .bool] ++ (if useEnum then #[WTy.enum] else #[]) ++ ms ++ pays ++ pays
    let mut defs : Array (String × WTy) := #[]
    for k in [0:(← below 3) + 1] do
      let isDef ← chance 40
      let t ← if isDef then pick (#[WTy.int, .bool, .str, .set] ++ seqs) else pick outTys
      let n := varName t false k
      if isDef then defs := defs.push (n, t)
      else
        let isPub ← chance 80
        if isPub then shown := shown.push (n, t)
        let det := if ← chance 40 then "det " else ""
        let decl := s!"{n}{if t == .bool then "" else s!": {t.name relElem}"}"
        if isPub then results := results ++ s!"    {det}{decl},\n"
        else body := body ++ s!"    {det}exists {decl}\n"
      vars := vars.push (n, t, false)
    let csc := { sc with vars }
    -- A definition may mention any variable, so definitions may form a
    -- cycle (`F0411`), but seldom.
    for (n, t) in defs do
      let others := if ← chance 85 then vars.filter (fun v => v.2.2 || !defs.any (·.1 == v.1)) else vars.filter (·.1 != n)
      let e ← gen { csc with vars := others } t 2
      let isPub ← chance 60
      let decl := s!"{n}{if t == .bool then "" else s!": {t.name relElem}"}"
      if isPub then
        shown := shown.push (n, t)
        results := results ++ s!"    {decl},\n"
        body := body ++ s!"    out {n} := {e}\n"
      else body := body ++ s!"    let {decl} := {e}\n"
    -- Counts: defined outputs, `let`s and chains of them, each a sum of a
    -- type's count terms, and expectations comparing one with 1.
    let mut countExpects := #[]
    if hasCounts then
      let isc := { csc with onlyIns := true }
      let seqIns := vars.filterMap fun (n, t, i) => if i && t == .seq then some n else none
      let cond : R String := do
        if !seqIns.isEmpty && (← chance 60) then return s!"{← pick seqIns}[{← below 6}] > 0"
        gen isc .bool 1
      let tys := #["Int", "Nat"] ++ countNewtypes ++ (if hasMs then #["Ms"] else #[])
      let mut cvars : Array (String × String) := #[]
      for k in [0:← below 4] do
        let ty ← pick tys
        let e ← countSum ty (cvars.filterMap fun (n, t) => if t == ty then some n else none) cond
        let n := s!"cnt{k}"
        match ← below 3 with
        | 0 => body := body ++ s!"    let {n}: {ty} := {e}\n"
        | _ =>
          results := results ++ s!"    {n}: {ty},\n"
          body := body ++ s!"    out {n} := {e}\n"
        cvars := cvars.push (n, ty)
      for _ in [0:(← below 3) + 1] do
        let ty ← pick tys
        let own := cvars.filterMap fun (n, t) => if t == ty then some n else none
        let lhs ← if !own.isEmpty && (← chance 60) then pick own else countSum ty own cond
        countExpects := countExpects.push (← countCmp ty lhs)
    for e in countExpects, k in [0:countExpects.size] do
      body := body ++ s!"    expect cx{k}: {e}\n"
    for k in [0:← below 2] do
      body := body ++ s!"    require a{k}: {← gen { csc with onlyIns := true } .bool 2}\n"
    for k in [0:(← below 3) + 1] do
      body := body ++ s!"    ensure q{k}: {← gen csc .bool 3}\n"
    for k in [0:← below 3] do
      let tested := if ← chance 5 then "set_option fren.evidence \"random\" in " else ""
      let e ← if ← chance 50 then pure s!"when {← gen csc .bool 1}, {← gen csc .bool 2}" else gen csc .bool 3
      body := body ++ s!"    {tested}expect x{k}: {e}\n"
    for k in [0:← below 2] do
      let tested := if ← chance 5 then "set_option fren.evidence \"random\" in " else ""
      body := body ++ s!"    {tested}cover g{k}: {← gen csc .bool 3}\n"
    let resultList := if results.isEmpty then "" else s!": (\n{results})"
    -- With sequences, often enumerated, at a small size.
    -- Now and then at size 3, where a struct's slot has thousands of
    -- values; and other procedures too, sets among their outputs.
    let size := if ← chance 20 then 3 else 2
    let enumerated := if (hasSeq && (← chance 60)) || (hasCounts && (← chance 60)) || (← chance 15) then
      s!"set_option fren.enumeration.size {size} in\nset_option fren.evidence \"enumerated\" in\n" else ""
    out := out ++ s!"\n{enumerated}pub proc c{c}(\n{params}){resultList} \{\n{body}}\n"
    comps := comps.push (s!"c{c}", vars.filterMap (fun (n, t, i) => if i then some (n, t) else none), shown)
  if hasCounts then out := out ++ (← countsProc "counts" hasMs countNewtypes)
  if ← chance 25 then out := out ++ guardDecls ++ (← guardsProc "guards")
  -- Last, so that the specs of the seeds before them are as they were.
  -- It writes static errors, on purpose (a body of another type) and not
  -- (#589), as the procedures above do too, so many seeds' specs stop
  -- before the groups below.
  if ← chance 50 then out := out ++ "\n" ++ (← bodyFns sc genericPay)
  -- Each group appended from here on starts with a cut (`out` pushed to
  -- `cuts`), and must add no static error (`appendedErrors`).
  let mut cuts := #[out]
  -- Generic functions applied, last too.
  if ← chance 40 then out := out ++ "\n" ++ (← genericApps sc genericPay)
  -- Each kind of site, with expressions that do not synthesize their
  -- types, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ sitesDecls ++ (← sitesProc "sites")
  -- A contract whose postconditions are tables, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← contractTable sc "ft")
  -- Subset-typed outputs of solver-checked procedures, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← subsetOutputs)
  -- Contracts of each form under enumeration, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← enumContracts "kc")
  -- A trait, last too.
  cuts := cuts.push out
  if ← chance 30 then out := out ++ "\n" ++ (← traitGroup sc)
  -- Contracts whose facts mention applications with facts of their own,
  -- last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← factChain)
  -- Generic functions over sets, sequences and relations of their type
  -- parameters, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← genericElements sc)
  -- Pattern tests that match every value or bind a name, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← patternTests)
  -- Goals with leading binders of each form, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← goalHeads)
  -- Variables named as bound names' and copies' symbols were, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← primedNames)
  -- Generic structural recursions, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← genericRecursion sc)
  -- A recursive application found on several paths, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← guardPaths)
  -- `[]` and `{}` as methods' arguments, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← emptyArguments sc)
  -- Structural recursions with subset results, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← recursiveSubsets)
  -- Procedures that only claim, and contract clauses about other names,
  -- last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← claimProcs)
  -- Global expectations over recursive enumerations, which induction may
  -- prove, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← inductions)
  -- Preconditions written `require`, in each of its forms, last too.
  cuts := cuts.push out
  if ← chance 40 then out := out ++ "\n" ++ (← requireForms)
  -- Only variables have the type `P`, each declared on a line of its own.
  let types (s : String) := if genericPay then (s.replace ": P\n" ": P<Int>\n").replace ": P,\n" ": P<Int>,\n" else s
  return (types out, cuts.map types)

/-- A spec with constants, functions, and components over them. -/
def genWide (avoidKnown : Bool := false) : R String := return (← genWideCuts avoidKnown).1

end FrenTest.FuzzFrontends.Wide
