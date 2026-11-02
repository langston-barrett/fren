-- keep-sorted start
import Fren
import FrenCli.Run
import FrenTest.Frontends
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
constants, defined outputs, defined and uninterpreted functions, the
former of every kind of result, as functions with `:=` and as function
blocks, with bodies that take their type from it (`bodyFns`), the
latter sometimes with contracts whose postconditions may contradict each
other, so that what applies them rests on their realizability, and
chains of contracts whose facts mention applications with facts of their
own (`factChain`), `match`
and tables over a scrutinee,
string methods with constant and non-constant arguments and `++`, products
of every kind of operand, orderings and `min` and `max` of an ordered
enumeration, an enumeration with payloads, whose outputs' variants a
clash note may give, sets and relations with `card`, so that it
reaches `linear_product`, the decidable core and the lints,
expressions that do not synthesize their types at each kind of site
(`sitesProc`), and traits, with laws and expectations over their methods
(`traitGroup`).

What legitimately differs is normalized away by
`FrenTest.Frontends.compare`, whose documentation lists it, as does
`Reqs/dev/Testing`. Specs run in worker processes (`--worker`), so that a
solver that aborts, or a spec that runs too long (`--spec-timeout`), is
recorded against its spec and the run goes on.

`--avoid-known` keeps the generator clear of the differences already
known, to find others: it parenthesizes every method's receiver that is
not a name, and counts a spec whose every difference is of a kind that
`knownDifferences` lists for `--avoid-known` as known, not as a finding.
`lake test` checks a fixed corpus of seeds against `knownDifferences`
(`corpusFailures`), and that what `genWide` appends adds no static error
(`Wide.genWideCuts`); CI runs fresh seeds on `main`.
`--guards` generates guarded quantifiers alone
(`Wide.genGuards`), over every type that a guard may bound or not, with
their operands read through fields, so that many run fast; `genWide`
includes such a procedure now and then too. `--sites` generates
`Wide.sitesProc`s alone, the last of which may write an expression that
does not synthesize its type where it is not checked, an error that stops
the spec's other checks; `genWide` includes one without it now and then.
-/

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends

def pick (xs : Array α) [Inhabited α] : R α := do return xs[← below xs.size]!

def chance (pct : Nat) : R Bool := do return (← below 100) < pct

namespace Wide

inductive WTy where
  | int | bool | str | set | rel | enum
  /-- The newtype `Ms` of `Int`. -/
  | ms
  /-- The enumeration with payloads `P { A, B(Int), C(Bool) }`, whose
  variants a clash note may give (`Reqs/Check#forced-outputs`). -/
  | pay
  /-- `Seq<Int>`, whose indexes may be out of range. -/
  | seq
  /-- The struct `Rq { q: Seq<Int>, n: Int }`, a collection beside another
  field. -/
  | rq
  /-- `Bx<Bx<Rq>>`, of the struct `Bx<T> { v: T }`: a generic type at an
  instance of itself. -/
  | bx
  deriving BEq, Inhabited

def WTy.name (relElem : String) : WTy → String
  | .int => "Int" | .bool => "Bool" | .str => "String" | .set => "Set<Int>"
  | .rel => s!"Rel<{relElem}, {relElem}>" | .enum => "E" | .ms => "Ms" | .pay => "P"
  | .seq => "Seq<Int>" | .rq => "Rq" | .bx => "Bx<Bx<Rq>>"

structure WScope where
  /-- A variable's text, type, and whether it is an input (so that an
  uninterpreted function may be applied to it). -/
  vars : Array (String × WTy × Bool) := #[]
  consts : Array (String × WTy) := #[]
  /-- Functions: name, parameter types, result type, and whether it has a
  body. -/
  fns : Array (String × Array WTy × WTy × Bool) := #[]
  nVariants : Nat := 0
  /-- The enumeration is ordered, so its values are compared with orderings
  and have `min` and `max`. -/
  ordered : Bool := false
  /-- The element type of relations: `E` or `Int`. -/
  relElem : String := "Int"
  /-- Only inputs and constants: an assumption, or an uninterpreted
  function's argument. -/
  onlyIns : Bool := false
  /-- Avoid the differences already known (`--avoid-known`). -/
  avoidKnown : Bool := false
  /-- The spec declares the newtype `Ms` of `Int`. -/
  hasMs : Bool := false
  /-- The spec declares the enumeration `P`. -/
  hasPay : Bool := false
  /-- The spec has sequences, and declares the struct `Rq`. -/
  hasSeq : Bool := false

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
  | .ms => return s!"Ms({← below 4})"
  | .pay => pick #["P::A", "P::B(0)", "P::B(2)", "P::C(true)", "P::C(false)"]
  | .seq => pick #["[1]", "[0, 2]", "[3, 1, 2]"]
  | .rq => return s!"Rq \{ q := {← pick #["[1]", "[0, 2]"]}, n := {← below 3} }"
  | .bx => return s!"Bx \{ v := Bx \{ v := {← leaf sc .rq} } }"

/-- An application of a function whose result has type `t`, if there is
one. The arguments of an uninterpreted one mention only inputs. -/
partial def app? (sc : WScope) (t : WTy) (d : Nat) : R (Option String) := do
  let fs := sc.fns.filter (·.2.2.1 == t)
  if fs.isEmpty then return none
  let (f, ps, _, hasBody) ← pick fs
  let asc := if hasBody then sc else { sc with onlyIns := true }
  let args ← ps.mapM (gen asc · (d - 1))
  return some s!"{f}({", ".intercalate args.toList})"

/-- A `match` on an enumeration, with arms of type `t`, some of them
with guards, and an arm with a guard sometimes followed by its variant's
arm without one; or a table over the scrutinee with those arms, which
then overlap. -/
partial def matchOn (sc : WScope) (t : WTy) (d : Nat) : R String := do
  let scrut ← gen sc .enum 0
  let mut arms := #[]
  let n := sc.nVariants
  let covered ← below (n + 1)
  for k in [0:covered] do
    if ← chance 30 then
      arms := arms.push s!"E::V{k} if {← gen sc .bool (d - 1)} => {← gen sc t (d - 1)}"
      unless ← chance 50 do continue
    arms := arms.push s!"E::V{k} => {← gen sc t (d - 1)}"
  if covered < n || (← chance 5) then arms := arms.push s!"_ => {← gen sc t (d - 1)}"
  let kw ← if ← chance 25 then pure "table" else pure "match"
  return s!"{kw} {scrut} \{ {", ".intercalate arms.toList} }"

/-- A table with values of type `t`: one to three rows, and sometimes a
last `_` row; or a table over an integer,
whose ranges may overlap, which the static rules reject (`F0391`). -/
partial def tableOf (sc : WScope) (t : WTy) (d : Nat) : R String := do
  if ← chance 30 then
    let (a, b, c) := (← below 4, ← below 4, ← below 4)
    let guard ← if ← chance 50 then pure s!" if {← gen sc .bool (d - 1)}" else pure ""
    let arms := #[s!"{min a b}..={max a b} => {← gen sc t (d - 1)}", s!"{c}..{guard} => {← gen sc t (d - 1)}",
      s!"..=-1 => {← gen sc t (d - 1)}", s!"_ => {← gen sc t (d - 1)}"]
    return s!"table ({← gen sc .int 0}) \{ {", ".intercalate arms.toList} }"
  let mut rows := #[]
  for _ in [0:(← below 3) + 1] do rows := rows.push s!"{← gen sc .bool (d - 1)} => {← gen sc t (d - 1)}"
  if ← chance 40 then rows := rows.push s!"_ => {← gen sc t (d - 1)}"
  -- Drawn where a leading `|`, which no row has now (`F0166`), was, so
  -- that the spec of every seed stays as it was but for the `|`s.
  discard (chance 30)
  return s!"table \{ {", ".intercalate rows.toList} }"

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
    match ← below 15 with
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
    -- Half the time a count's term, `if c then 1 else 0`, which a sum
    -- compared with 1 reads as a cardinality operation, also through a
    -- defined output.
    | 8 =>
      if ← chance 50 then return s!"(if {← sub .bool} then 1 else 0)"
      return s!"(if {← sub .bool} then {← sub .int} else {← sub .int})"
    | 9 | 10 => return (← app? sc .int d).getD (← leaf sc .int)
    | 11 => return s!"{← rsub .str}.index_of({← csub .str}, {← below 2})"
    | 12 => return s!"{← rsub .rel}.card"
    | 13 => if sc.hasMs then return s!"{← sub .ms}.0" else leaf sc .int
    | 14 => tableOf sc .int d
    | 15 | 16 =>
      -- An index of a sequence, guarded or not, or its length.
      unless sc.hasSeq do return ← leaf sc .int
      let q ← rsub .seq
      match ← below 4 with
      | 0 => return s!"{q}[{← sub .int}]"
      | 1 => let i ← sub .int; return s!"(if 0 <= {i} < {q}.len then {q}[{i}] else {← sub .int})"
      | 2 => return s!"{q}.len"
      | _ => return s!"{← rsub .rq}.n"
    | _ => leaf sc .int
  | .bool =>
    match ← below 30 with
    | 0 => return s!"({← sub .bool} and {← sub .bool})"
    | 1 => return s!"({← sub .bool} or {← sub .bool})"
    | 2 => return s!"not {← sub .bool}"
    | 3 | 4 =>
      let rhs ← if ← chance 30 then pure "1" else sub .int
      return s!"{← sub .int} {← pick #["=", "!=", "<", "<=", ">", ">="]} {rhs}"
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
    | 13 =>
      unless hasEnum do return ← sub .bool
      -- Orderings, and chains of them, mostly of an ordered enumeration; of
      -- an unordered one, an error that both front ends must report alike.
      if (sc.ordered || (← chance 10)) && (← chance 50) then
        if ← chance 50 then return s!"{← sub .enum} {← pick #["<", "<=", ">", ">="]} {← sub .enum}"
        return s!"{← sub .enum} {← pick #["<", "<="]} {← sub .enum} {← pick #["<", "<="]} {← sub .enum}"
      return s!"{← sub .enum} {← pick #["=", "!="]} {← sub .enum}"
    | 14 => if hasEnum then matchOn sc .bool d else sub .bool
    | 15 | 16 => return (← app? sc .bool d).getD (← leaf sc .bool)
    | 17 => return s!"(when {← sub .bool}, {← sub .bool})"
    | 18 => return s!"({← sub .bool} iff {← sub .bool})"
    | 19 => return s!"{← rsub .set}.card {← pick #["=", ">", "<=", ">="]} {← below 3}"
    | 20 => return s!"{← sub .int} = {← sub .int} or {← sub .int} = {← sub .int} or {← sub .int} = {← sub .int}"
    | 21 =>
      -- A cardinality operator, of one to three arguments, rarely one that
      -- is not a `Bool`.
      let arg : R String := do if ← chance 5 then sub .int else sub .bool
      let mut args := #[← arg]
      for _ in [0:← below 3] do args := args.push (← arg)
      return s!"{← pick #["exactly_one?", "at_most_one?"]}({", ".intercalate args.toList})"
    | 22 | 23 =>
      unless sc.hasMs do return ← leaf sc .bool
      -- Seldom, a newtype compared with an `Int`, which both reject.
      let rhs ← if ← chance 5 then sub .int else sub .ms
      return s!"{← sub .ms} {← pick #["=", "!=", "<", "<=", ">", ">="]} {rhs}"
    | 24 => tableOf sc .bool d
    -- A pattern test of `P`, of a variant, or an equation, or a `match`
    -- that reads a payload.
    | 25 | 26 =>
      unless sc.hasPay do return ← leaf sc .bool
      let p ← pick #["P::A", "P::B(_)", "P::C(_)", "P::B(_) | P::C(true)", "P::B(1..)", "P::C(false)"]
      if ← chance 30 then return s!"{← sub .pay} {← pick #["=", "!="]} {← sub .pay}"
      return s!"{← sub .pay} is {p}"
    | 28 | 29 =>
      unless sc.hasSeq do return ← leaf sc .bool
      let q ← rsub .seq
      match ← below 3 with
      | 0 => return s!"({q} != [] and {q}[0] {← pick #["<", ">=", "="]} {← sub .int})"
      | 1 => return s!"{q} {← pick #["=", "!="]} {← sub .seq}"
      | _ => return s!"(when {← sub .int} < {q}.len, {q}[{← sub .int}] = {← sub .int})"
    | 27 =>
      unless sc.hasPay do return ← leaf sc .bool
      return s!"match {← sub .pay} \{ P::B(y) => y {← pick #["<", ">=", "="]} {← sub .int}, P::C(z?) => z?, _ => {← sub .bool} }"
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
    match ← below 4 with
    | 0 => if hasEnum then matchOn sc .enum d else leaf sc .enum
    | 1 => return (← app? sc .enum d).getD (← leaf sc .enum)
    | 2 => if sc.ordered then return s!"({← sub .enum}).{← pick #["min", "max"]}({← sub .enum})" else leaf sc .enum
    | _ => leaf sc .enum
  | .ms =>
    match ← below 7 with
    | 0 => return s!"({← sub .ms} + {← sub .ms})"
    | 1 => return s!"({← sub .ms} - {← sub .ms})"
    | 2 => return s!"Ms({← sub .int})"
    | 3 => return s!"(if {← sub .bool} then {← sub .ms} else {← sub .ms})"
    | 4 => if hasEnum then matchOn sc .ms d else leaf sc .ms
    | 5 => return (← app? sc .ms d).getD (← leaf sc .ms)
    | _ => leaf sc .ms
  | .pay =>
    match ← below 4 with
    | 0 => return s!"P::B({← sub .int})"
    | 1 => return s!"(if {← sub .bool} then {← sub .pay} else {← sub .pay})"
    | _ => leaf sc .pay
  | .seq =>
    match ← below 4 with
    | 0 => return s!"[{← sub .int}, {← sub .int}]"
    | 1 => return s!"{← rsub .rq}.q"
    | _ => leaf sc .seq
  | .rq =>
    match ← below 3 with
    | 0 => return s!"{← rsub .bx}.v.v"
    | _ => leaf sc .rq
  | .bx => leaf sc .bx

end

def varName (t : WTy) (isIn : Bool) (k : Nat) : String :=
  let base := match t with
    | .int => "n" | .bool => "b" | .str => "s" | .set => "st" | .rel => "r" | .enum => "m" | .ms => "d" | .pay => "p"
    | .seq => "q" | .rq => "rq" | .bx => "bx"
  let base := if isIn then base else "o" ++ base
  if t == .bool then s!"{base}{k}?" else s!"{base}{k}"

/-- The literal `k` at the count type `ty`: an integer, or wrapped in each
newtype that `ty` is over, as `Cm3(Cm2(Cm(k)))` (`countDecls`). -/
def wrapLit (ty : String) (k : Nat) : String :=
  if ty == "Ms" then s!"Ms({k})"
  else if ty.startsWith "Cm" || ty.startsWith "Cn" then
    let base := (ty.take 2).toString
    let d := ((ty.drop 2).toString.toNat?).getD 1
    (List.range d).foldl (init := toString k) fun acc i =>
      s!"{base}{if i == 0 then "" else toString (i + 1)}({acc})"
  else toString k

/-- The indicator function at the count type `ty`, which `countDecls`
declares. -/
def countFn : String → String
  | "Int" => "ind" | "Nat" => "indn" | "Ms" => "indm" | t => "ind" ++ t.toLower

/-- A sum of a count's terms at the type `ty`, `Int`, `Nat` or a newtype over them: an
`if c then 1 else 0`, a literal, a constant, an application of the
type's indicator function, or one of `defs`, defined variables of the
type, which makes chains of definitions; `cond` gives each condition. -/
def countSum (ty : String) (defs : Array String) (cond : R String) : R String := do
  let lit := wrapLit ty
  let mut terms := #[]
  for _ in [0:(← below 3) + 1] do
    let t ← match ← below 6 with
      | 0 | 1 => pure s!"(if {← cond} then {lit 1} else {lit 0})"
      | 2 => pure (lit (← below 3))
      | 3 => match ty with
        | "Int" => pick #["ONE_I", "TWO_I"]
        | "Nat" => pick #["ONE_N", "TWO_N"]
        | _ => pure (lit 2)
      | 4 => pure s!"{countFn ty}({← cond})"
      | _ => if defs.isEmpty then pure s!"(if {← cond} then {lit 1} else {lit 0})" else pick defs
    terms := terms.push t
  return " + ".intercalate terms.toList

/-- What a count of `ty` is compared with: 1, or a constant that is 1. -/
def countOne (ty : String) : R String := match ty with
  | "Int" => pick #["1", "1", "ONE_I"]
  | "Nat" => pick #["1", "1", "ONE_N"]
  | t => pure (wrapLit t 1)

/-- A comparison of `lhs`, a count of `ty`, with 1, each way, sometimes
negated. -/
def countCmp (ty lhs : String) : R String := do
  let one ← countOne ty
  let cmp ← match ← below 7 with
    | 0 | 1 => pure s!"{lhs} <= {one}"
    | 2 | 3 => pure s!"{lhs} = {one}"
    | 4 => pure s!"{one} >= {lhs}"
    | 5 => pure s!"{lhs} < {one}"
    | _ => pure s!"{lhs} != {one}"
  return if ← chance 40 then s!"not ({cmp})" else cmp

/-- The declarations that counts use, and the newtypes among the count
types: an indicator function at `Int` and `Nat`, constants, and newtypes
over `Int` and `Nat`, each of a newtype over the one before to a random
depth, `Cm`, `Cm2(Cm)`, `Cm3(Cm2)` over `Int` and `Cn`, `Cn2(Cn)` over
`Nat`, with an indicator function each. -/
def countDecls : R (String × Array String) := do
  let mut out := "pub fn ind(c?): Int := if c? then 1 else 0\npub fn indn(c?): Nat := if c? then 1 else 0\n" ++
    "pub const ONE_I: Int := 1\npub const TWO_I: Int := 2\npub const ONE_N: Nat := 1\npub const TWO_N: Nat := 2\n"
  let mut tys := #[]
  for (base, under, top) in [("Cm", "Int", 3), ("Cn", "Nat", 2)] do
    let depth := (← below top) + 1
    for i in [1:depth + 1] do
      let ty := if i == 1 then base else s!"{base}{i}"
      let inner := if i == 1 then under else if i == 2 then base else s!"{base}{i - 1}"
      out := out ++ s!"pub ordered struct {ty}({inner})\n"
      out := out ++ s!"pub fn {countFn ty}(c?): {ty} := if c? then {wrapLit ty 1} else {wrapLit ty 0}\n"
      tys := tys.push ty
  return (out, tys)

/-- A procedure of counts alone, always enumerated, so that nothing else
about it hides how a front end reads them: over sequences whose indexes
may be out of range, with counts at every numeric type (`Int`, `Nat`, the
newtypes `newtypes` over them, and `Ms` if `hasMs`), each through defined
outputs, `let`s, functions and chains of them, or inline. -/
def countsProc (name : String) (hasMs : Bool) (newtypes : Array String) : R String := do
  -- At size 3, one sequence only, so that the procedure stays within the
  -- limit of behaviours (two `Seq<Int>` there have 160,000 assignments).
  let size := if ← chance 30 then 3 else 2
  let cond : R String := do
    match ← below 5 with
    | 0 | 1 => return s!"q[{← below 6}] > 0"
    | 2 => if size == 2 then return s!"r[{← below 6}] = {← below 2}" else return s!"q[{← below 6}] = {← below 2}"
    | 3 => pick #["b?", "not b?", "n > 0"]
    | _ => pick #["true", "false"]
  let tys := #["Int", "Nat"] ++ newtypes ++ (if hasMs then #["Ms"] else #[])
  let mut results := ""
  let mut body := ""
  let mut cvars : Array (String × String) := #[]
  for k in [0:← below 5] do
    let ty ← pick tys
    let e ← countSum ty (cvars.filterMap fun (n, t) => if t == ty then some n else none) cond
    let n := s!"k{k}"
    if ← chance 30 then body := body ++ s!"    let {n}: {ty} := {e}\n"
    else
      results := results ++ s!"    {n}: {ty},\n"
      body := body ++ s!"    out {n} := {e}\n"
    cvars := cvars.push (n, ty)
  for k in [0:(← below 4) + 1] do
    let ty ← pick tys
    let own := cvars.filterMap fun (n, t) => if t == ty then some n else none
    let lhs ← if !own.isEmpty && (← chance 60) then pick own else countSum ty own cond
    body := body ++ s!"    expect e{k}: {← countCmp ty lhs}\n"
  let resultList := if results.isEmpty then "" else s!": (\n{results})"
  let params := if size == 2 then "q: Seq<Int>, r: Seq<Int>, b?, n: Int" else "q: Seq<Int>, b?, n: Int"
  return s!"\nset_option fren.lint.undecidable \"allow\" in\nset_option fren.enumeration.size {size} in\n" ++
    s!"set_option fren.evidence \"enumerated\" in\npub proc {name}({params}){resultList} \{\n{body}}\n"

/-! ### Guards of quantifiers -/

/-- The declarations that `guardsProc` quantifies over: newtypes over
`Int` and `Nat`, a newtype over a newtype, one that is not ordered, an
ordered record and an ordered enumeration. -/
def guardDecls : String :=
  "pub ordered struct Gm(Int)\npub ordered struct Gn(Nat)\npub ordered struct Go(Gm)\npub struct Gp(Int)\n" ++
  "pub ordered struct Gr { x: Int, y: Int }\npub ordered enum Ge { A, B, C }\n" ++
  "pub type Gb = b: Int where invariant: b is 0..=3\n"

/-- An operand of a guard: how it reads the bound name `x`, and a constant
of its type, which a bound or a member may be. -/
structure GuardForm where
  text : String
  lit : R String
  /-- A collection of the operand's type, for a membership. -/
  coll : R String
  /-- Whether `k`, an `Int`, may bound it. -/
  int : Bool := false

instance : Inhabited GuardForm := ⟨{ text := "x", lit := pure "0", coll := pure "s" }⟩

def intLit : R String := do
  let n ← below 6
  return if (← chance 15) then s!"-{n}" else toString n

/-- The ways a guard may read a bound name of the type `ty`, by its fields
and orderings, each with constants of its type. -/
def guardForms (ty : String) (x : String) : Array GuardForm :=
  let ints : R String := intLit
  let natLit : R String := do return toString (← below 6)
  let intColl (lit : R String) : R String := do
    match ← below 3 with
    | 0 => return "s"
    | 1 => return "q"
    | _ => return s!"\{{← lit}, {← lit}}"
  let wrapColl (lit : R String) : R String := do
    if ← chance 50 then return s!"\{{← lit}, {← lit}}" else return s!"[{← lit}, {← lit}]"
  let int (t : String) (lit : R String) : GuardForm := { text := t, lit, coll := intColl lit, int := true }
  match ty with
  | "Int" | "Gb" => #[int x ints]
  | "Nat" => #[int x natLit]
  | "Gm" =>
    let gm : R String := do return s!"Gm({← intLit})"
    #[{ text := x, lit := gm, coll := wrapColl gm }, int s!"{x}.0" ints]
  | "Gn" =>
    let gn : R String := do return s!"Gn({← natLit})"
    #[{ text := x, lit := gn, coll := wrapColl gn }, int s!"{x}.0" natLit]
  | "Go" =>
    let gm : R String := do return s!"Gm({← intLit})"
    let go : R String := do return s!"Go(Gm({← intLit}))"
    #[{ text := x, lit := go, coll := wrapColl go }, { text := s!"{x}.0", lit := gm, coll := wrapColl gm },
      int s!"{x}.0.0" ints, int s!"({x}).0.0" ints]
  | "Gp" => #[int s!"{x}.0" ints, int s!"({x}).0" ints]
  | "Gr" =>
    let gr : R String := do return s!"Gr \{ x := {← intLit}, y := {← intLit} }"
    #[{ text := x, lit := gr, coll := wrapColl gr }, int s!"{x}.x" ints]
  | "Ge" =>
    let ge : R String := do return s!"Ge::{← pick #["A", "B", "C"]}"
    #[{ text := x, lit := ge, coll := wrapColl ge }]
  | _ =>
    let str : R String := do pick #["\"\"", "\"a\"", "\"ab\"", "\"b\""]
    #[{ text := x, lit := str, coll := wrapColl str }]

/-- A conjunct of a guard of the bound name `x` of the type `ty`: a
comparison of one of its forms, on either side, with each operator, a
chain of two, a membership, or a conjunct about something else. -/
def guardConjunct (ty x : String) : R String := do
  let f ← pick (guardForms ty x)
  let bound : R String := do
    if f.int && (← chance 30) then pick #["k", "k + 1", "q.len"] else f.lit
  match ← below 6 with
  | 0 | 1 =>
    let op ← pick #["<", "<=", ">", ">="]
    if ← chance 50 then return s!"{f.text} {op} {← bound}" else return s!"{← bound} {op} {f.text}"
  | 2 => return s!"{← bound} {← pick #["<", "<="]} {f.text} {← pick #["<", "<="]} {← bound}"
  | 3 | 4 => return s!"{f.text} in {← f.coll}"
  | _ => pick #["k > 0", "true"]

/-- A procedure of guarded quantifiers alone, always enumerated, over
each type that a guard may bound or not (`lang::range_domain`), its
operands read through fields (`lang::name_alone`), with ranges with one
or both bounds, memberships in sets and sequences, and each comparison
operator. -/
def guardsProc (name : String) : R String := do
  let tys := #["Int", "Nat", "Gb", "Gm", "Gn", "Go", "Gp", "Gr", "Ge", "String"]
  let mut body := ""
  let n := (← below 3) + 1
  for j in [0:n] do
    let ty ← pick tys
    let x := "x"
    let guard := " and ".intercalate (← (List.range ((← below 3) + 1)).mapM fun _ => guardConjunct ty x)
    let f ← pick (guardForms ty x)
    let inst := s!"{f.text} != {← f.lit}"
    let q ← if ← chance 60 then pure s!"forall ({x}: {ty}), when {guard}, {inst}"
      else pure s!"exists ({x}: {ty}), {guard} and {inst}"
    body := body ++ s!"    ensure r{j}: b{j}? iff ({q})\n    expect e{j}: b{j}?\n"
  let outs := ", ".intercalate ((List.range n).map (s!"b{·}?"))
  let size := if ← chance 10 then 3 else 2
  return s!"\nset_option fren.lint.undecidable \"allow\" in\nset_option fren.lint.chainable_comparison \"allow\" in\n" ++
    s!"set_option fren.enumeration.size {size} in\nset_option fren.evidence \"enumerated\" in\n" ++
    s!"pub proc {name}(k: Int, s: Set<Int>, q: Seq<Int>): ({outs}) \{\n{body}}\n"

/-- A spec of guarded quantifiers alone (`--guards`). -/
def genGuards : R String := do
  let mut out := "mod fz\n\n" ++ guardDecls
  for i in [0:(← below 3) + 2] do
    out := out ++ (← guardsProc s!"g{i}")
  return out

/-- A body of type `t` where its type is expected, as a defined function's
body or a function block's `out` (`lang::checked`): the forms that take
their type from what is expected, `{}`, `[]` and a variant of the generic
`P<Int>` without a payload, within conditionals, `match`es, parentheses,
`union` and `++`, or any expression of the type. -/
partial def bodyOf (sc : WScope) (t : WTy) (genericPay : Bool) (d : Nat) : R String := do
  let sub := bodyOf sc t genericPay (d - 1)
  if d == 0 || (← chance 30) then
    match t with
    | .set => if ← chance 60 then return "{}" else return ← leaf sc .set
    | .rel => if ← chance 60 then return "{}" else return ← leaf sc .rel
    | .seq => if ← chance 60 then return "[]" else return ← leaf sc .seq
    | .pay => if genericPay && (← chance 60) then return "P::A" else return ← leaf sc .pay
    | _ => return ← gen sc t 1
  match ← below 6 with
  | 0 => return s!"if {← gen sc .bool 1} then {← sub} else {← sub}"
  | 1 =>
    if sc.nVariants == 0 then return s!"({← sub})"
    let arms ← (List.range sc.nVariants).toArray.mapM fun k => do return s!"E::V{k} => {← sub}"
    return s!"match {← gen sc .enum 0} \{ {", ".intercalate arms.toList} }"
  | 2 => return s!"({← sub})"
  | 3 => match t with
    | .set | .rel => return s!"{← sub} {← pick #["union", "inter", "minus"]} {← sub}"
    | .seq => return s!"{← sub} ++ {← sub}"
    | _ => sub
  | _ => gen sc t 2

/-- A body of type `Option<inner>`, where its type is expected:
`Option::None`, `Option::Some` of `inner`, or, seldom, of a `Bool`, a type
mismatch, within conditionals, `match`es and parentheses. -/
partial def optionBody (sc : WScope) (inner : R String) (d : Nat) : R String := do
  let sub := optionBody sc inner (d - 1)
  if d == 0 || (← chance 35) then
    match ← below 10 with
    -- A type mismatch, which `--avoid-known` leaves out: after it, the Lean
    -- front end may report a Lean error of its own too (#493).
    | 0 => return if sc.avoidKnown then "Option::None" else "Option::Some(true)"
    | 1 | 2 | 3 | 4 => return "Option::None"
    | _ => return s!"Option::Some({← inner})"
  match ← below 3 with
  | 0 => return s!"if {← gen sc .bool 1} then {← sub} else {← sub}"
  | 1 =>
    if sc.nVariants == 0 then return s!"({← sub})"
    let arms ← (List.range sc.nVariants).toArray.mapM fun k => do return s!"E::V{k} => {← sub}"
    return s!"match {← gen sc .enum 0} \{ {", ".intercalate arms.toList} }"
  | _ => return s!"({← sub})"

/-- A defined function `name` of the parameter `x0: Int` and result type
`ty` with the body `body`, written with `:=` or, sometimes, as a function
block whose `out` is the body. -/
def bodyFn (name ty body : String) (params := "x0: Int") (tps := "") : R String := do
  if ← chance 40 then return s!"pub fn {name}{tps}({params}): (r: {ty}) \{\n    out r := {body}\n}\n"
  return s!"pub fn {name}{tps}({params}): {ty} := {body}\n"

/-- Functions whose bodies are checked against their result types, of every
kind of result (`lang::checked`): collections, enumerations with payloads,
generic instances, aliases, subset types, a generic result, a structural
recursion, and now and then a body of another type. -/
def bodyFns (sc : WScope) (genericPay : Bool) : R String := do
  let sc := { sc with vars := #[("x0", WTy.int, true)] }
  let x : R String := gen sc .int 1
  let payTy := if genericPay then "P<Int>" else "P"
  let mut out := ""
  let mut aliases := false
  let mut subset := false
  let mut list := false
  for k in [0:(← below 4) + 1] do
    let name := s!"h{k}"
    match ← below 9 with
    | 0 | 1 | 2 =>
      let tys := #[(WTy.set, "Set<Int>"), (.seq, "Seq<Int>"), (.int, "Int"), (.rel, WTy.rel.name sc.relElem)] ++
        (if sc.hasPay then #[(WTy.pay, payTy)] else #[]) ++ (if sc.hasSeq then #[(WTy.bx, "Bx<Bx<Rq>>")] else #[])
      let (t, ty) ← pick tys
      -- Seldom a body of another type: a mismatch, reported alike.
      let bt ← if ← chance 8 then pick (tys.map (·.1)) else pure t
      out := out ++ (← bodyFn name ty (← bodyOf sc bt genericPay 3))
    | 3 => out := out ++ (← bodyFn name "Option<Int>" (← optionBody sc x 3))
    | 4 =>
      unless aliases do
        out := out ++ "pub type OptInt := Option<Int>\npub type IntSet := Set<Int>\n"
        aliases := true
      if ← chance 50 then out := out ++ (← bodyFn name "OptInt" (← optionBody sc x 3))
      else out := out ++ (← bodyFn name "IntSet" (← bodyOf sc .set genericPay 3))
    | 5 =>
      unless subset do
        out := out ++ "pub type Small = n: Int where small: n is 0..=5\n"
        subset := true
      if ← chance 50 then out := out ++ (← bodyFn name "Option<Small>" (← optionBody sc (pick #["0", "3", "9", "x0"]) 3))
      else out := out ++ (← bodyFn name "Small" (← pick #["3", "9", "x0", "if x0 > 0 then 1 else 7"]))
    | 6 | 7 =>
      -- A generic function, whose result mentions its type parameter.
      out := out ++ (← bodyFn s!"g{k}" "Option<T>" (← optionBody sc (pure "x") 3) (params := "x: T") (tps := "<T>"))
    | _ =>
      unless list do
        out := out ++ "pub enum L { Nil, Cons(Int, L) }\n"
        list := true
      let base ← pick #["Option::None", "Option::None", "Option::Some(0)"]
      out := out ++ s!"pub fn last{k}(l: L): Option<Int> := match l \{\n    L::Nil => {base},\n" ++
        s!"    L::Cons(h, t) => if t = L::Nil then Option::Some(h) else last{k}(t),\n}\n"
  return out

/-- Generic functions, and a procedure that applies them (`Reqs/Lang/GenericFunctions`):
`match`es that mention a value of the type parameter and that don't, a
generic enumeration's payload, and applications at `Int`, `Bool`, an
abstract type and a nested instance, with arguments whose type arguments
come from the expected type, as `Option::None`. -/
def genericApps (sc : WScope) (genericPay : Bool) : R String := do
  let mut out := "pub type Nm\n" ++
    "pub fn pick<T>(c?, a: T, b: T): T := if c? then a else b\n" ++
    "pub fn unwrap_or<T>(o: Option<T>, d: T): T := match o { Option::Some(x) => x, Option::None => d }\n" ++
    "pub fn some?<T>(o: Option<T>) := match o { Option::Some(_) => true, Option::None => false }\n" ++
    "pub fn wrap<T>(x: T): Option<T> := Option::Some(x)\n"
  if sc.hasPay && genericPay then
    out := out ++ "pub fn payload_or<X>(p: P<X>, d: X): X := match p { P::B(x) => x, _ => d }\n" ++
      "pub fn is_b?<X>(p: P<X>) := match p { P::B(_) => true, _ => false }\n"
  let isc : WScope := { sc with vars := #[("n", WTy.int, true), ("b?", .bool, true)], fns := #[] }
  -- Leaves, so that nothing here is an error of its own, such as a
  -- product of two variables, which would stop the spec's other checks.
  let int : R String := leaf isc .int
  let bool : R String := leaf isc .bool
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 10 with
      | 0 => pure s!"r = unwrap_or({← pick #["o", "Option::None", "wrap(n)", s!"Option::Some({← int})"]}, {← int})"
      | 1 => pure s!"s? = pick({← bool}, some?(o), {← bool})"
      | 2 => pure s!"t = pick({← bool}, m, m2)"
      | 3 => pure s!"u = unwrap_or(oo, {← pick #["Option::None", "o", "wrap(n)"]})"
      | 4 => pure s!"some?(oo) = some?({← pick #["o", "wrap(m)", "wrap(b?)", "wrap(oo)"]})"
      | 5 => pure s!"r = pick(some?(wrap({← bool})), {← int}, unwrap_or(unwrap_or(oo, o), n))"
      | 6 => pure s!"t = unwrap_or({← pick #["wrap(m)", "Option::None", "wrap(m2)"]}, m)"
      | 7 =>
        if sc.hasPay && genericPay then pure s!"r = payload_or({← pick #["P::A", "P::B(n)", "pp", "P::C(b?)"]}, {← int})"
        else pure s!"s? = some?(wrap({← bool}))"
      | 8 =>
        -- Not `P::A`, which leaves `X` unknown (`F0400`), an error.
        if sc.hasPay && genericPay then pure s!"s? = is_b?({← pick #["pp", "P::B(n)", "P::B(3)"]})"
        else pure s!"u = wrap({← int})"
      | _ => pure s!"t = pick({← bool}, m2, m)"
    body := body ++ s!"    ensure ga{k}: {e}\n"
  let pp := if sc.hasPay && genericPay then ", pp: P<Int>" else ""
  return out ++ s!"pub proc gapps(n: Int, b?, m: Nm, m2: Nm, o: Option<Int>, oo: Option<Option<Int>>{pp}): " ++
    s!"(r: Int, s?, t: Nm, u: Option<Int>) \{\n{body}}\n"

/-- An expression of the collection type `ty` (`"Set<Int>"`, `"Rel<Int, Int>"`,
`"Seq<Int>"` or `"Option<Int>"`) that does not synthesize its type: its
empty value, `{}`, `[]` or `Option::None`, within parentheses,
conditionals, `match`es, tables, the bodies of `let`s, definitions whose
type is written, and `union`, or, seldom, `other`, a variable of the type,
which synthesizes it (`lang::synthesizes`). -/
partial def unsynthesized (ty : String) (other : String) (d : Nat) : R String := do
  let empty := if ty == "Seq<Int>" then "[]" else if ty == "Option<Int>" then "Option::None" else "{}"
  let sub := unsynthesized ty other (d - 1)
  if d == 0 || (← chance 35) then return if ← chance 10 then other else empty
  match ← below 8 with
  | 0 => return s!"({← sub})"
  | 1 => return s!"(if c? then {← sub} else {← sub})"
  | 2 => return s!"match o \{ Option::Some(_) => {← sub}, Option::None => {← sub} }"
  | 3 => return s!"table \{ c? => {← sub}, _ => {← sub} }"
  -- Named by depth, so that nothing shadows them.
  | 4 => return s!"(let t{d}: {ty} := {← sub} in t{d})"
  | 5 => return s!"(let t{d} := {other} in {← sub})"
  | _ =>
    if ty == "Set<Int>" || ty.startsWith "Rel" then return s!"({← sub} {← pick #["union", "inter", "minus"]} {← sub})"
    return s!"({← sub})"

/-- The declarations that the procedures of `sitesProc` use. -/
def sitesDecls : String :=
  "pub struct SiteRec { m: Set<Int>, n: Int }\n" ++
  "pub fn site_card(t: Set<Int>): Int := t.card\n" ++
  "pub fn site_first(t: Seq<Int>): Int := if t.len > 0 then t[0] else 0\n"

/-- A procedure `name` that writes expressions that do not synthesize their
types at each kind of site that `ExprSite` lists where they are checked
(`lang::checked`): beside a part that synthesizes one or none, as an
argument, a payload, a field of a record literal or update, a written
definition, the right of `in`, and the branches, arms and rows beside a
variable. Each is well typed and in the decidable core, so that it stops
none of the spec's other checks. With `unchecked`, it ends with one where
they are not checked, an error, reported alike, which stops them all, as in
`--sites` mode. -/
def sitesProc (name : String) (unchecked : Bool := false) : R String := do
  let set : R String := unsynthesized "Set<Int>" "s" 2
  let rel : R String := unsynthesized "Rel<Int, Int>" "r" 2
  let seq : R String := unsynthesized "Seq<Int>" "q" 2
  let opt : R String := unsynthesized "Option<Int>" "o" 2
  let mut body := ""
  for k in [0:(← below 5) + 2] do
    let e ← match ← below 19 with
      | 0 => pure s!"s = {← set}"
      | 1 => pure s!"{← set} = s"
      | 2 => pure s!"{← set} subset s"
      | 3 => pure s!"x in {← set}"
      | 4 => pure s!"site_card({← set}) >= 0"
      | 5 => pure s!"os != Option::Some({← set})"
      | 6 => pure s!"sr = SiteRec \{ m := {← set}, n := x }"
      | 7 => pure s!"sr = \{ sr with m := {← set} }"
      | 8 => pure s!"(let u: Set<Int> := {← set} in u subset s)"
      | 9 => pure s!"s = (s {← pick #["union", "inter", "minus"]} {← set})"
      | 10 => pure s!"s = (if c? then {← set} else s)"
      | 11 => pure s!"s = match o \{ Option::Some(_) => {← set}, Option::None => s }"
      | 12 => pure s!"s = table \{ c? => {← set}, _ => s }"
      | 13 => pure s!"(table \{ c? => {← set}, _ => s }).card >= 0"
      | 14 => pure s!"site_first({← seq}) = 0"
      | 15 => pure s!"o = {← opt}"
      | 16 => pure s!"{← opt} != o"
      | 17 => pure s!"(1, 2) in {← rel}"
      | _ => pure s!"r = (r union {← rel})"
    body := body ++ s!"    expect st{k}: {e}\n"
  if unchecked then
    let e ← match ← below 6 with
      | 0 => pure s!"({← set}).card = 0"
      | 1 => pure s!"r.image({← set}) = s"
      | 2 => pure s!"(let u := {← set} in u) = s"
      | 3 => pure s!"r = r join {← rel}"
      | 4 => pure s!"({← seq}).len = 0"
      | _ => pure s!"{← set} = {← set}"
    body := body ++ s!"    expect unchecked: {e}\n"
  return s!"pub proc {name}(s: Set<Int>, q: Seq<Int>, x: Int, c?, o: Option<Int>, os: Option<Set<Int>>, " ++
    s!"r: Rel<Int, Int>, sr: SiteRec) \{\n{body}}\n"

/-- A spec of `sitesProc`s alone, the last of which may write an expression
that does not synthesize its type where it is not checked (`--sites`). -/
def genSites : R String := do
  let mut out := "mod fz\n\n" ++ sitesDecls
  let n := (← below 2) + 1
  for i in [0:n] do
    out := out ++ (← sitesProc s!"sites{i}" (unchecked := i + 1 == n && (← chance 60)))
  return out

/-- An uninterpreted function `name` whose postconditions are tables, each
row's condition a leaf (its parameter `x1?`, a `Bool` constant, `true` or
`false`), or a comparison of its value `r` or of `x0` with an `Int` leaf:
so that rows `K0` and `true` meet, and rows over `r` overlap where only
the clause that they are in rules it out (#559). The checks of its rows
ask about them without that clause, of `r`, not of the function's
application (`Reqs/Check#contracts-of-uninterpreted-functions`). It is
appended to specs of the corpus, so it is written from a grammar of its
own, every form of which is well-typed, whatever the spec declares: no
payload of a generic `P`, no ill-typed count, and no comparison of a name
with itself, which a lint reports. -/
def contractTable (sc : WScope) (name : String) : R String := do
  let bools := sc.constsOf .bool
  let ints := sc.constsOf .int
  -- An `Int` other than `r` and `x0`, which the comparisons have.
  let int : R String := do
    if !ints.isEmpty && (← chance 40) then pick ints else return toString (← below 4)
  let bool : R String := do
    match ← below 3 with
    | 0 => pure "x1?"
    | 1 => if bools.isEmpty then pick #["true", "false"] else pick bools
    | _ => pick #["true", "false"]
  let row : R String := do
    match ← below 3 with
    | 0 => bool
    | 1 => return s!"r {← pick #["=", "<", ">=", ">"]} {← if ← chance 30 then pure "x0" else int}"
    | _ => return s!"x0 {← pick #["=", "<", ">"]} {← int}"
  let value : R String := do
    if ← chance 50 then bool else return s!"r {← pick #["=", "<", ">"]} {← int}"
  let mut clauses := ""
  for j in [0:(← below 2) + 1] do
    let mut rows := #[]
    for _ in [0:(← below 3) + 2] do rows := rows.push s!"{← row} => {← value}"
    if ← chance 40 then rows := rows.push s!"_ => {← value}"
    clauses := clauses ++ s!"    ensure t{j}: table \{ {", ".intercalate rows.toList} }\n"
  return s!"pub fn {name}(x0: Int, x1?): (r: Int) \{\n{clauses}}\n"

/-- Uninterpreted functions with contracts of each form, applied by an
enumerated procedure (`check::contract_blocks_enumeration`): preconditions
alone, which do not keep it from being enumerated, postconditions alone,
both, or no contract. They are declared in an order of their own, and
applied in another, so that the function that `F0645` names, the first by
path of those with postconditions, is neither the first declared nor the
first applied. -/
def enumContracts (name : String) : R String := do
  let mut names := #["kca", "kcb", "kcc"]
  let mut decls := ""
  -- The names in a random order, each with a contract of a random form.
  for _ in [0:3] do
    let i ← below names.size
    let f := names[i]!
    names := names.eraseIdx! i
    let pre := s!"    assume p: x >= {← pick #["-2", "-1", "0"]}\n"
    let post := s!"    ensure q: r > {← pick #["x", "x - 1"]}\n"
    let decl ← match ← below 4 with
      | 0 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{pre}}\n"
      | 1 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{post}}\n"
      | 2 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{pre}{post}}\n"
      | _ => pure s!"pub fn {f}(Int): Int\n"
    decls := decls ++ decl
  let mut apps := #[]
  let mut left := #["kca", "kcb", "kcc"]
  for _ in [0:3] do
    let i ← below left.size
    apps := apps.push s!"{left[i]!}(x)"
    left := left.eraseIdx! i
  let sum := " + ".intercalate apps.toList
  let options := "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n"
  return decls ++ s!"\n{options}pub proc {name}(x: Int): (det y: Int) \{\n    assume a: x != 5\n    \
    out y := {sum}\n    expect e: y != {← below 3}\n}\n"

/-- Procedures checked by the solver whose outputs have subset types: of
`Int`, a subset of a subset, a record with a field of one, and a subset of
that record; each output `pub` or not (`exists`), `det` or not, with
guarantees that sometimes force a value outside its type, so that
realizability's `∃` over the outputs ranges over their types alone
(`Reqs/Models#what-is-not-confirmed`). It adds no static error. -/
def subsetOutputs : R String := do
  let bound := (← below 4) + 2
  let mut out := "pub type Sp = n: Int where pos: n > 0\n" ++
    s!"pub type Ss = s: Sp where small: s < {bound}\n" ++
    "pub struct Sbox { v: Ss, w: Int }\n" ++
    "pub type Sr = r: Sbox where ok: r.w >= 0\n"
  -- An integer from the inputs `x` and `y`.
  let int : R String := do
    match ← below 5 with
    | 0 => return "x"
    | 1 => return "y"
    | 2 => return s!"x + {← below 4}"
    | 3 => return s!"y - {← below 3}"
    | _ => return s!"{← below 5}"
  for c in [0:(← below 2) + 1] do
    let mut results := #[]
    let mut body := ""
    if ← chance 40 then body := body ++ s!"    assume a: x > {← below 4}\n"
    for k in [0:(← below 2) + 1] do
      let ty ← pick #["Sp", "Ss", "Sbox", "Sr", "Nat"]
      let n := s!"o{k}"
      let det := if ← chance 40 then "det " else ""
      if ← chance 75 then results := results.push s!"{det}{n}: {ty}"
      else body := body ++ s!"    {det}exists {n}: {ty}\n"
      let guard ← if ← chance 30 then pure s!"when x > {← below 4}, " else pure ""
      let isRec := ty == "Sbox" || ty == "Sr"
      let e ← if isRec then do
          if ← chance 70 then pure s!"{n}.v = {← int} and {n}.w = {← int}" else pure s!"{n}.w > {← int}"
        else do
          match ← below 3 with
          | 0 => pure s!"{n} = {← int}"
          | 1 => pure s!"{n} > {← int}"
          | _ => pure s!"{n} != {← int}"
      body := body ++ s!"    ensure e{k}: {guard}{e}\n"
      if ← chance 30 then
        let v := if isRec then s!"{n}.v" else n
        let b ← below 3
        body := body ++ s!"    expect x{k}: {v} >= {b}\n"
    let rs := if results.isEmpty then "" else s!": ({", ".intercalate results.toList})"
    out := out ++ s!"\npub proc so{c}(x: Int, y: Int){rs} \{\n{body}}\n"
  return out

mutual
/-- A term of a trait's carrier, over the carriers `ss` and the integers
`xs`, of depth at most `d` (`traitGroup`). -/
partial def traitSelf (sc : WScope) (ss xs : Array String) (d : Nat) : R String := do
  if d == 0 || (← chance 50) then pick ss
  else return s!"step({← traitSelf sc ss xs (d - 1)}, {← traitInt sc ss xs (d - 1)})"

/-- An integer term of a trait: a variable, a literal, an observation, a
sum, or an expression of the spec's constants and functions alone, which
multiplies no two variables, an error (`traitGroup`). -/
partial def traitInt (sc : WScope) (ss xs : Array String) (d : Nat) : R String := do
  match ← below (if d == 0 then 3 else 6) with
  | 0 => if xs.isEmpty then return toString (← below 4) else pick xs
  | 1 => return toString (← below 4)
  | 2 => return s!"obs({← traitSelf sc ss xs 0})"
  | 3 => return s!"obs({← traitSelf sc ss xs (d - 1)})"
  | 4 => return s!"{← traitInt sc ss xs (d - 1)} + {← traitInt sc ss xs (d - 1)}"
  | _ => gen { sc with vars := #[] } .int 1
end

/-- A `Bool` term of a trait, which applies `ok?` if `flag` (`traitGroup`). -/
def traitBool (sc : WScope) (flag : Bool) (ss xs : Array String) (d : Nat) : R String := do
  match ← below (if flag then 4 else 3) with
  | 0 => return s!"{← traitInt sc ss xs d} = {← traitInt sc ss xs d}"
  | 1 => return s!"{← traitInt sc ss xs d} <= {← traitInt sc ss xs d}"
  | 2 => return s!"{← traitSelf sc ss xs d} = {← traitSelf sc ss xs d}"
  | _ => return s!"ok?({← traitSelf sc ss xs d})"

/-- A trait (`Reqs/Lang/Traits`): methods in both of an uninterpreted
function's forms, one with a contract, laws over them, and expectations
in both of a global expectation's forms, whose terms apply the methods to
each other and to the spec's constants and functions. Its laws are
outside the decidable core, so `undecidable` is allowed on it, and
nothing in it is an error. -/
def traitGroup (sc : WScope) : R String := do
  let contract ← chance 50
  let flag ← chance 50
  let mut out := "set_option fren.lint.undecidable \"allow\" in\npub trait Tr {\n"
  out := out ++ (if contract then "    fn obs(s: Self): (r: Int) {\n        ensure low: r >= 0\n    }\n"
    else "    fn obs(Self): Int\n")
  out := out ++ "    fn step(Self, Int): Self\n"
  if flag then out := out ++ "    fn ok?(Self)\n"
  for k in [0:← below 3] do
    let law ← if ← chance 50 then
        pure s!"obs(step(s, x)) = {← traitInt sc #["s"] #["x"] 1}"
      else traitBool sc flag #["s"] #["x"] 1
    out := out ++ s!"\n    law l{k}(s: Self, x: Int): {law}\n"
  for k in [0:(← below 2) + 1] do
    -- Now and then under a lint setting, as a member may be.
    if ← chance 20 then out := out ++ "\n    set_option fren.lint.eq_op \"allow\" in"
    if ← chance 50 then
      let assume ← if ← chance 40 then pure s!"        assume a: {← traitBool sc flag #["s", "t"] #["x"] 0}\n" else pure ""
      let claim ← traitBool sc flag #["s", "t"] #["x"] 1
      out := out ++ s!"\n    expect e{k}(s: Self, t: Self, x: Int) \{\n{assume}        expect c: {claim}\n    }\n"
    else
      out := out ++ s!"\n    expect e{k}: forall (s: Self) (x: Int), {← traitBool sc flag #["s"] #["x"] 1}\n"
  -- The other forms, drawn after the members above, so that a trait drawn
  -- before them is as it was: a method that shadows a procedure's name,
  -- which only the trait's own law mentions; a contract over an earlier
  -- method; a law with no variables, one with a `Bool` variable written
  -- `x?`, and one after a lint setting; and a trait that is not `pub`.
  if ← chance 40 then
    out := out ++ "\n    fn c0(Self): Int\n    law shadowed(s: Self): c0(s) >= 0\n"
  if ← chance 40 then
    out := out ++ "\n    fn grown(s: Self): (r: Int) { ensure above: r >= obs(s) }\n"
  if ← chance 30 then
    out := out ++ s!"\n    law closed(): {← gen { sc with vars := #[] } .int 1} <= {← gen { sc with vars := #[] } .int 1}\n"
  if ← chance 30 then
    out := out ++ s!"\n    law flagged(s: Self, b?): when b?, {← traitBool sc flag #["s"] #[] 0}\n"
  if ← chance 30 then
    out := out ++ s!"\n    set_option fren.lint.eq_op \"allow\" in\n    law set(s: Self, x: Int): {← traitBool sc flag #["s"] #["x"] 0}\n"
  out := if ← chance 30 then out.replace "pub trait Tr" "trait Tr" else out
  return out ++ "}\n"

/-- A chain of uninterpreted functions with contracts, each of whose
postconditions applies the one before it, and checks over the last, so
that the facts of an application mention another, whose facts a query has
too, transitively (`check::fact_applications`, #619). Each link applies
the one before it in one of the forms that a fact's applications take: a
sum, a bound, a product, a conditional, a nested application of an
uninterpreted function without a contract, a quantifier whose body applies
a function into `Nat` at its bound name, an arm of a `match` that binds a
payload, a `where` clause, a table, a function into `Nat` or into a subset
type, without a contract, a generic function with a contract over the
first of the chain, and a recursive defined function with a
postcondition, whose one-step equations a query reflects from a fact
(`lang::recursion_formulas`); its results `Int` or `Nat`, sometimes under
a precondition. An expectation and a cover goal over the last then hold or
fail by the facts of all of them, as do the rows of a table over the last
in a contract of its own, whose own facts its checks never have; and an
input, an output and a call's output of a subset type whose invariant
applies the recursive function. It is
appended to specs of the corpus, so it is written from a grammar of its
own, every form of which is well-typed, whatever the spec declares. -/
def factChain : R String := do
  let mut out := "pub type Fc\npub fn fct(Fc): Fc\n"
  let n := (← below 3) + 1
  let bound ← below 3
  let nat0 ← chance 30
  out := out ++ s!"pub fn fc0(s: Fc): (r: {if nat0 then "Nat" else "Int"}) \{ ensure e: r >= {bound} }\n"
  -- What the links may apply besides the chain, each well-typed alone.
  out := out ++ "pub enum Fk { A, B(Int) }\npub fn fck(Fc): Fk\npub fn fcn(Fc): Nat\npub fn fci(Int): Nat\n" ++
    "pub type FcPos = p: Int where invariant: p > 0\npub fn fcp(Fc): FcPos\n" ++
    "pub fn fcg<T>(x: T, y: T, s: Fc): (r: Int) { ensure e: r >= (if x = y then fc0(s) else fc0(s) + 1) }\n" ++
    "pub enum Fl { Nil, Cons(Int, Fl) }\npub fn fcl(Fc): Fl\n" ++
    "pub fn fcsum(l: Fl): (r: Int) {\n    out r := match l { Fl::Nil => 0, Fl::Cons(m, rest) => m.abs + fcsum(rest) }\n" ++
    "    ensure e: r >= 0\n}\n"
  for k in [1:n + 1] do
    let prev := s!"fc{k - 1}"
    let arg ← pick #["s", "fct(s)", "fct(fct(s))"]
    let app := if k == 1 then s!"{prev}({arg})" else s!"{prev}({arg}, b?)"
    let c ← below 3
    let form ← below 13
    let (opt, post) ← match form with
      | 0 => pure ("", s!"ensure e: r = {app} + {c}")
      | 1 => pure ("", s!"ensure e: r >= {app}")
      | 2 => pure ("", s!"ensure e: r > 2 * {app}")
      | 3 => pure ("", s!"ensure e: r = if b? then {app} else {c}")
      | 4 => pure ("", s!"ensure e: r = {app} - {c}")
      | 5 => pure ("set_option fren.lint.undecidable \"allow\" in\n",
          s!"ensure e: forall (i: Int), when 0 <= i < {c + 1}, r >= {app} + fci(i)")
      | 6 => pure ("", s!"ensure e: r = match fck(s) \{ Fk::A => {app}, Fk::B(x) => {app} + x.abs }")
      | 7 => pure ("", s!"ensure e: r = y + {c} where y := {app}")
      | 8 => pure ("", s!"ensure e: table \{ b? => r >= {app}, _ => r = {app} + {c} }")
      | 9 => pure ("", s!"ensure e: r = {app} + fcn({arg})")
      | 10 => pure ("", s!"ensure e: r = {app} + fcp({arg})")
      | 11 => pure ("", s!"ensure e: r = fcg(b?, true, {arg}) + {app}")
      | _ => pure ("", s!"ensure e: r = fcsum(Fl::Cons({c}, fcl({arg}))) + {app}")
    let pre := if ← chance 30 then s!"    assume p: b?\n" else ""
    -- A `Nat` result only where the clause gives its value: where it only
    -- bounds it by an `Int`, Lean's realizability query often times out
    -- (#493).
    let ty := if k > 1 && [0, 7, 9, 10].contains form && (← chance 40) then "Nat" else "Int"
    out := out ++ s!"{opt}pub fn fc{k}(s: Fc, b?): (r: {ty}) \{\n{pre}    {post}\n}\n"
  -- Whatever its preconditions, `b?` is `true` at the checks, so that
  -- none fails at a call.
  let last := s!"fc{n}(s, true)"
  let c ← below 4
  out := out ++ s!"\nexpect fc_holds(s: Fc) \{ expect c: {last} >= {c} }\n"
  out := out ++ s!"\nproc fc_cover(s: Fc) \{\n    cover low: {last} < {c}\n}\n"
  if ← chance 40 then
    out := out ++ s!"\npub fn fc_table(s: Fc): (r: Int) \{\n    ensure t: table \{ fc{n}(s, true) >= {c} => r > 0, r < 0 => true, _ => true }\n}\n"
  -- An input, an output and a call's output of a subset type whose
  -- invariant applies the recursive `fcsum`, whose facts each query has
  -- (`lang::recursion_formulas`); its second row keeps the type inhabited
  -- without the opaque `fcsum`.
  if ← chance 50 then
    let b ← below 4
    let d ← below 4
    out := out ++ s!"\npub type FcBig = m: Int where invariant: fcsum(Fl::Cons(m, Fl::Nil)) >= {b} or m = {b}\n" ++
      "proc fc_in(x: FcBig): (det z: Int) { out z := x + 1 }\n" ++
      s!"proc fc_out(): (y: FcBig) \{\n    cover w: y = {d}\n}\n" ++
      s!"proc fc_call(u: Int) \{\n    call w := fc_out()\n    cover v: w.y = {d} + u\n}\n" ++
      s!"proc fc_in2(x: FcBig) \{\n    cover v: x > {d}\n}\n"
  return out

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
        clauses := clauses ++ s!"    assume {n}0: {← gen { csc with vars := csc.vars.pop } .bool 2}\n"
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
      body := body ++ s!"    assume a{k}: {← gen { csc with onlyIns := true } .bool 2}\n"
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
  -- Only variables have the type `P`, each declared on a line of its own.
  let types (s : String) := if genericPay then (s.replace ": P\n" ": P<Int>\n").replace ": P,\n" ": P<Int>,\n" else s
  return (types out, cuts.map types)

/-- A spec with constants, functions, and components over them. -/
def genWide (avoidKnown : Bool := false) : R String := return (← genWideCuts avoidKnown).1

end Wide

/-! ### Running the front ends -/

open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends (Report maskBetween headOf)

/-- What both front ends said on a spec. -/
structure Ran where
  /-- How they differ. -/
  comparison : FrenTest.Frontends.Comparison
  /-- Both reports, as comments. -/
  reports : String
  /-- The binary's error codes. -/
  errors : Array String
  /-- The binary's diagnostics. -/
  cli : Array Diagnostic

/-- The `fren` command's diagnostics and summary on `text`, and its exit
code. -/
def runCli (path : System.FilePath) (text : String) : IO (Array Diagnostic × Option String × UInt32) := do
  IO.FS.writeFile path text
  let (out, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files := #[path.toString] })
  let (cli, cliSum) := FrenTest.Ui.cliDiagnostics path.toString out (keepUnlocated := true)
  return (cli, cliSum, code)

/-- Checks `text` with both front ends. -/
def runFrontends (env : Environment) (path : System.FilePath) (text : String) : IO Ran := do
  let (cli, cliSum, code) ← runCli path text
  let (hosted, hostedSum) ← FrenTest.Ui.hostedDiagnostics env path.toString text
  let comparison := FrenTest.Frontends.comparison text
    { diags := cli, summary? := cliSum, exit? := some code.toNat } { diags := hosted, summary? := hostedSum }
  let render (ds : Array Diagnostic) (s : Option String) :=
    String.join (ds.toList.map fun d => s!"--   {d.line}:{d.col + 1}: {d.severity}{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}\n")
      ++ s!"--   summary: {s.getD "(none)"}\n"
  return { comparison, reports := s!"-- fren (exit {code}):\n{render cli cliSum}-- Lean:\n{render hosted hostedSum}",
           errors := cli.filterMap fun d => if d.severity == "error" then d.code? else none,
           cli }

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
    let ran ← runFrontends env (dir / s!"current-files-{← IO.Process.getPID}.fren") (← IO.FS.readFile f)
    let (found, reports) := (ran.comparison.found, ran.reports)
    IO.println s!"{f}: {if found.isEmpty then "the front ends agree" else "the front ends differ"}"
    for x in found do IO.println s!"  {x}"
    unless found.isEmpty do bad := bad + 1; IO.println reports
  return if bad == 0 then 0 else 1

def rngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0xf407⟩

/-- How specs are generated: `--avoid-known`, and `--guards`, which
generates guarded quantifiers alone (`Wide.genGuards`), many to a spec. -/
structure Mode where
  avoidKnown : Bool := false
  guards : Bool := false
  /-- Specs of `Wide.sitesProc`s alone (`Wide.genSites`). -/
  sites : Bool := false
  deriving BEq

def Mode.spec (m : Mode) (seed : Nat) : String :=
  Id.run ((if m.sites then Wide.genSites else if m.guards then Wide.genGuards else Wide.genWide m.avoidKnown).run' (rngOf seed))

/-- The cuts of the spec of `seed` (`Wide.genWideCuts`), each shorter than
the next; none for `--guards` and `--sites`, whose generators append
nothing. -/
def Mode.cuts (m : Mode) (seed : Nat) : Array String :=
  if m.guards || m.sites then #[] else
    (Id.run ((Wide.genWideCuts m.avoidKnown).run' (rngOf seed))).2

def Mode.args (m : Mode) : Array String :=
  (if m.avoidKnown then #["--avoid-known"] else #[]) ++ (if m.guards then #["--guards"] else #[]) ++
    (if m.sites then #["--sites"] else #[])

def flags (m : Mode) : String := String.join (m.args.toList.map (" " ++ ·))

/-- The mode of the flags `args`, if they are only flags of a mode. -/
def Mode.ofArgs? (args : List String) : Option Mode :=
  if args.all (· ∈ ["--avoid-known", "--guards", "--sites"]) then
    some { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards", sites := args.contains "--sites" }
  else none

/-- The mode as Lean writes it in `knownDifferences`. -/
def Mode.lean (m : Mode) : String :=
  let fields := (if m.avoidKnown then ["avoidKnown := true"] else []) ++ (if m.guards then ["guards := true"] else []) ++
    (if m.sites then ["sites := true"] else [])
  if fields.isEmpty then "{}" else "{ " ++ ", ".intercalate fields ++ " }"

/-- `s` with each number written right after `pre`, and followed by
`post`, as `N`. -/
def maskNumberAfter (s pre : String) (post : String := "") : String :=
  match s.splitOn pre with
  | [] => s
  | first :: rest => first ++ String.join (rest.map fun piece =>
    let digits := piece.toList.takeWhile Char.isDigit
    let after := String.ofList (piece.toList.drop digits.length)
    pre ++ if !digits.isEmpty && after.startsWith post then "N" ++ after else piece)

#guard maskNumberAfter "rows 1 and 2 of a table" "rows " == "rows N and 2 of a table"
#guard maskNumberAfter "has 12 behaviours, has 3 checks" "has " " behaviours" == "has N behaviours, has 3 checks"

/-- A difference without its line, names and values, to group the
specs that differ alike. Of the numbers, it masks, as `N`, only those that
name a place or count what a spec happens to have: a line (`line N`), a
row or an arm of a table or a `match` (`row N`, `rows N and N`, `arm N`,
`arms N and N`), and a count of behaviours (`has N behaviours`). Every
other number is part of the kind, so that two differences that it
tells apart stay apart: an exit code, a size bound, and the counts of
checks of a summary or a note. -/
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
  for pre in ["line ", "row ", "rows ", "arm ", "arms ", "rows N and ", "arms N and "] do
    out := maskNumberAfter out pre
  out := maskNumberAfter out "has " " behaviours"
  let masked := maskBetween out "for the input " [", no outputs", ", it can be"]
  return maskBetween (maskBetween masked "fren says " [", Lean says"]) "Lean says " []

/-! ### Known differences -/

/-- A difference that the front ends are known to make on a spec, until
its issue is fixed: the spec's mode and seed, the difference as `compare`
gives it, line and names included, and the issue that tracks it. -/
structure Known where
  mode : Mode
  seed : Nat
  difference : String
  issue : Nat
  /-- As a kind for `--avoid-known` (`knownKind`), it is known only after a
  static error: on a spec where the `fren` command reports one at or
  before the difference's line, which its recovery from the error
  explains. -/
  afterStaticError : Bool := false
  /-- As a kind, it is known only on a spec that also has a difference of
  this kind (a `signature`), which explains it. -/
  alongside? : Option String := none
  deriving BEq

/-- The kind of the `fren` command's internal error on a formula that its
evaluator cannot read (#493), which explains the differences listed
`alongside?` it. -/
def evaluatorUnread : String :=
  "only fren reports error[-]: internal error: the evaluator does not know the meaning of a formula of `_`"

/-- The differences that the front ends make on the specs of the corpus
(`corpusSpecs?`) on `main`, each with its issue: #493 and its sub-issues,
and #555. As with `knownColumnDifferences` in `FrenTestMain`, the corpus
fails on a difference that is not listed, on a listed one that no longer
occurs, and on one that occurs more often than it is listed, so that the
list only shrinks. A change to the generator leaves every seed's spec as
it was, up to what it appends (`Wide.genWideCuts`), so this list stays as
it is; never list a difference here to absorb a changed corpus. A
difference that the run of fresh seeds on `main` finds is listed with its
seed and mode, and the corpus then checks that seed too (`listedOutside`).
`--avoid-known` counts a spec whose every difference is of a kind (its
`signature`) listed here for `--avoid-known` as known. An entry holds the
whole difference: its line and column, the names that a front end gives
its own facts, as Lean's `f0.equation0.1`, and the message's wording. A
change to any of those, such as to where a front end places a message or
to the generated text before it on its line, makes an unlisted and a
vanished difference on the same line, which is relisted, not a
regression; on a spec with an undecided check, only the unlisted one
shows, since a vanished entry does not fail there. -/
def knownDifferences : List Known :=
  -- Lean reports `ob1?`, an output that a table in an expectation reads,
  -- as unknown, in a spec with other errors (F0391 in `c0`), once any
  -- later item with checks is declared after it, even a constant, as
  -- `sitesDecls` and `contractTable` declare (also on main's front ends,
  -- which agree on the spec without them).
  [{ mode := {}, seed := 28, issue := 493,
     difference := "line 21:35: only Lean reports error: Unknown identifier `ob1?`" },
   { mode := {}, seed := 153, issue := 478,
     difference := "line 37:28: only fren reports error[F0714]: this is outside the decidable core: \
       a relational operator over a type that is not finite quantifies over its values" },
   -- Lean reports `F0743` twice on `((({(1, 2)}).inverse).domain).card`.
   { mode := { avoidKnown := true }, seed := 41, issue := 493,
     difference := "line 23:16: only Lean reports warning: this chain of methods has a shorter form" },
   -- Kinds of #493 and #295 that `--avoid-known` found on fresh seeds:
   -- those below 2000000 in runs on `main` (`fuzz-frontends`), the others in
   -- a run of 13,800 seeds from 3000000, at 8a0c3978.
   -- After a static error, the front ends recover differently: only `fren`
   -- reports the lints of what follows it, and only Lean reports an error
   -- of its own (`Type mismatch`, `Application type mismatch`, `cannot
   -- find`, or a lint).
   { mode := { avoidKnown := true }, seed := 1156065, issue := 493, afterStaticError := true,
     difference := "line 49:16: only fren reports warning[F0712]: this `Bool` expression can be simpler" },
   { mode := { avoidKnown := true }, seed := 1156065, issue := 493, afterStaticError := true,
     difference := "line 48:34: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 102:33: only fren reports warning[F0739]: parentheses directly around parentheses" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 102:11: only fren reports warning[F0710]: unused parameter `x0`" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 100:37: only Lean reports error: Type mismatch" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:36: only fren reports warning[F0737]: both branches of `if` are written the \
       same" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:34: only fren reports warning[F0739]: parentheses directly around parentheses" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:14: only fren reports warning[F0710]: unused parameter `x`" },
   { mode := { avoidKnown := true }, seed := 3102696, issue := 493, afterStaticError := true,
     difference := "line 58:41: only Lean reports error: Type mismatch" },
   { mode := { avoidKnown := true }, seed := 3102696, issue := 493, afterStaticError := true,
     difference := "line 60:28: only Lean reports error: cannot find `Small` in this scope" },
   { mode := { avoidKnown := true }, seed := 3103202, issue := 493, afterStaticError := true,
     difference := "line 28:103: only Lean reports error: Application type mismatch: The argument" },
   { mode := { avoidKnown := true }, seed := 3100624, issue := 493, afterStaticError := true,
     difference := "line 41:17: only Lean reports warning: `n1` is never negative, so it can be a `Nat`" },
   -- After a static error, only Lean reports a name as an `Unknown
   -- identifier`.
   { mode := { avoidKnown := true }, seed := 1159002, issue := 295, afterStaticError := true,
     difference := "line 17:61: only Lean reports error: Unknown identifier `b0?`" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 25:18: only fren reports warning[F0736]: the condition and the body of `when` are \
       written the same" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 25:18: only fren reports warning[F0712]: this `Bool` expression can be simpler" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 21:35: only Lean reports error: Unknown identifier `on2`" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 49:16: only fren reports warning[F0761]: this expectation mentions no variable" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 43:34: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 37:24: only Lean reports error: Unknown identifier `b1?`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 50:5: only fren reports warning[F0719]: defined output `k1` is the same in every \
       behaviour" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 48:43: only fren reports warning[F0710]: unused variable `b?`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 48:47: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 42:59: only Lean reports error: Unknown identifier `s1`" },
   -- Only Lean notes that two clauses force an output both ways.
   { mode := { avoidKnown := true }, seed := 1157147, issue := 493,
     difference := "line 11: for the same input, fren notes #[], Lean notes #[line 18: `q1` forces ob1? = \
       false, but `q2` forces ob1? = true]" },
   { mode := { avoidKnown := true }, seed := 1158050, issue := 493,
     difference := "line 9: for the same input, fren notes #[], Lean notes #[line 20: `q0` forces ob1? = \
       true, but `q1` forces ob1? = false]" },
   { mode := { avoidKnown := true }, seed := 3000892, issue := 493,
     difference := "line 10: for the same input, fren notes #[], Lean notes #[line 19: `q1` forces ob0? = \
       false, but `q2` forces ob0? = true]" },
   { mode := { avoidKnown := true }, seed := 3102156, issue := 493,
     difference := "line 4: for the same input, fren notes #[], Lean notes #[line 13: `q1` forces ob0? = \
       true, but `q2` forces ob0? = false]" },
   -- Only `fren` reports F0111 on `K0.card` in a guard of a `match` arm.
   { mode := { avoidKnown := true }, seed := 1157298, issue := 493,
     difference := "line 34:45: only fren reports error[F0111]: `K0.card` is not a single name (and Lean \
       reports no parse error at or just before that line, in its item)" },
   -- Only Lean notes why unsatisfiable assumptions cannot hold.
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 21:12: only Lean reports info: `a0` cannot hold." },
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 10:88: only Lean reports info: Both operands of `a0` cannot be true: the stated \
       premises require `a0.fz::f1?@1.2` to be false." },
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 10:33: only Lean reports info: Both operands of `a0` cannot be false: the stated \
       premises require `a0.fz::f1?@1.1` to be true." },
   -- The CLI's evaluator cannot read a formula that Lean counts the
   -- behaviours of.
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493,
     difference := "line 28:10: only fren reports error[-]: internal error: the evaluator does not know the \
       meaning of a formula of `fz::c1`" },
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493, alongside? := some evaluatorUnread,
     difference := "line 28:10: only Lean reports error: `fz::c1` has 442137500 behaviours up to size 2, too \
       many to enumerate" },
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493, alongside? := some evaluatorUnread,
     difference := "exit: fren exits 1, and Lean's messages call for 2" },
   { mode := { avoidKnown := true }, seed := 1160230, issue := 493,
     difference := "line 13:10: only fren reports error[-]: internal error: the evaluator does not know the \
       meaning of a formula of `fz::c0`" },
   { mode := { avoidKnown := true }, seed := 1160230, issue := 493, alongside? := some evaluatorUnread,
     difference := "line 13:10: only Lean reports error: `fz::c0` has 36238786560 behaviours up to size 2, \
       too many to enumerate" },
   { mode := { avoidKnown := true }, seed := 1160230, issue := 493, alongside? := some evaluatorUnread,
     difference := "exit: fren exits 1, and Lean's messages call for 2" }]

/-- The line of the difference `f`, if it has one: `line N:` or `line
N:COL:` at its start. -/
def differenceLine? (f : String) : Option Nat := do
  let first ← (f.splitOn ": ").head?
  let rest ← first.dropPrefix? "line "
  (rest.toString.splitOn ":").head?.bind String.toNat?

#guard differenceLine? "line 48:34: only fren reports warning[F0710]: unused variable `n`" == some 48
#guard differenceLine? "line 11: for the same input, fren notes #[]" == some 11
#guard differenceLine? "exit: fren exits 1, and Lean's messages call for 2" == none

/-- The difference `f`, on a spec whose differences are `found` and where
the `fren` command reports static errors at the lines `staticLines`, is of
a kind that `knownDifferences` lists for a seed of `--avoid-known`, of
either generator, and `mode` is of `--avoid-known` too: on the fresh seeds
that CI checks with it, those kinds go unchecked. An entry that holds only
after a static error (`afterStaticError`) matches only where one is at or
before `f`'s line, and one that holds only alongside another kind
(`alongside?`) only where `found` has that kind. -/
def knownKind (mode : Mode) (staticLines : Array Nat) (found : Array String) (f : String) : Bool :=
  mode.avoidKnown && knownDifferences.any fun k =>
    k.mode.avoidKnown && signature k.difference == signature f
      && (!k.afterStaticError || (differenceLine? f).any fun l => staticLines.any (· ≤ l))
      && k.alongside?.all fun a => found.any (signature · == a)

section
private def known (f : String) (staticLines : Array Nat := #[]) (found : Array String := #[f])
    (mode : Mode := { avoidKnown := true }) : Bool :=
  knownKind mode staticLines found f
#guard known "line 23:16: only Lean reports warning: this chain of methods has a shorter form"
#guard known "line 23:16: only Lean reports warning: this chain of methods has a shorter form"
  (mode := { avoidKnown := true, guards := true })
#guard !known "line 23:16: only Lean reports warning: this chain of methods has a shorter form" (mode := {})
-- A kind listed only for the default generator is not known to
-- `--avoid-known`.
#guard !known "line 37:28: only fren reports error[F0714]: this is outside the decidable core: \
  a relational operator over a type that is not finite quantifies over its values"
-- A lint that only `fren` reports is known after a static error, which
-- explains it, and not on a spec without one, or with one only after it.
#guard known "line 48:34: only fren reports warning[F0710]: unused variable `n`" #[12]
#guard !known "line 48:34: only fren reports warning[F0710]: unused variable `n`"
#guard !known "line 48:34: only fren reports warning[F0710]: unused variable `n`" #[50]
-- An exit code that the evaluator's internal error explains is known only
-- alongside that error.
#guard !known "exit: fren exits 1, and Lean's messages call for 2"
#guard known "exit: fren exits 1, and Lean's messages call for 2"
  (found := #["exit: fren exits 1, and Lean's messages call for 2", "line 13:10: only fren reports error[-]: \
    internal error: the evaluator does not know the meaning of a formula of `fz::c0`"])
-- A verdict count, a core and another exit code are no known kind, so a
-- spec that has one is a finding.
#guard !known "summary: fren says `15 passed, 19 failed, 1 inconclusive, 0 redundant`, Lean says `14 passed, \
  20 failed, 1 inconclusive, 0 redundant`" #[1]
#guard !known "line 23: for the same input, fren says `no outputs satisfy `q2``, Lean says `no outputs \
  satisfy `q0`, `q1` and `q2``" #[1]
#guard !known "exit: fren exits 0, and Lean's messages call for 1" #[1]
end

-- The numbers that place a difference or count what the spec has are
-- masked; a code's digits and a name's are not.
#guard signature "line 28:10: only Lean reports error: `fz::c1` has 442137500 behaviours up to size 2, \
    too many to enumerate"
  == "only Lean reports error: `_` has N behaviours up to size 2, too many to enumerate"
#guard signature "line 11: for the same input, fren notes #[], Lean notes #[line 18: `q1` forces ob1? = false, \
    but `q2` forces ob1? = true]"
  == "for the same input, fren notes #[], Lean notes #[line N: `_` forces ob1? = false, but `_` forces ob1? = true]"
#guard signature "line 48:34: only fren reports warning[F0710]: unused variable `n`"
  == "only fren reports warning[F0710]: unused variable `_`"
#guard signature "line 3:1: only Lean reports error: rows 1 and 2 of a table in `f` may both hold"
  == signature "line 9:4: only Lean reports error: rows 2 and 3 of a table in `g` may both hold"
-- Every other number stays, so that differences that it tells apart stay
-- apart: exit codes, size bounds and counts of checks.
#guard signature "exit: fren exits 0, and Lean's messages call for 1"
  != signature "exit: fren exits 1, and Lean's messages call for 2"
#guard signature "line 1:1: only Lean reports info: 4 checks of `c` hold for every behaviour up to size 2"
  != signature "line 1:1: only Lean reports info: 3 checks of `c` hold for every behaviour up to size 2"
#guard signature "line 2:5: only Lean reports warning: could not decide whether `q` is vacuous: no witness up to size 2, \
    but a larger one may exist"
  != signature "line 2:5: only Lean reports warning: could not decide whether `q` is vacuous: no witness up to size 3, \
    but a larger one may exist"
/-- The ranges of seeds of the corpus that `lake test` checks: the seeds
`[SEED, SEED + COUNT)` of each mode, a few dozen to a job of `fren_test`
(`frontendFuzz SEED COUNT FLAGS...`), so that they spread over the
shards. Sized so that the whole corpus takes about 2 minutes of one CI
machine. -/
def corpus : List (Mode × Nat × Nat) :=
  [({}, 0, 30), ({}, 30, 30), ({ guards := true }, 0, 20), ({ guards := true }, 20, 20), ({ sites := true }, 0, 20)]

/-- The specs that `knownDifferences` lists outside `corpus`, which the job
`frontendFuzz listed` checks. -/
def listedOutside : List (Mode × Nat) :=
  let inCorpus (m : Mode) (s : Nat) := corpus.any fun (m', a, n) => m' == m && a ≤ s && s < a + n
  (knownDifferences.filterMap fun k => if inCorpus k.mode k.seed then none else some (k.mode, k.seed)).eraseDups

/-- The arguments of the corpus's jobs of `fren_test`. -/
def corpusJobs : List (List String) :=
  corpus.map (fun (m, a, n) => ["frontendFuzz", toString a, toString n] ++ m.args.toList)
    ++ if listedOutside.isEmpty then [] else [["frontendFuzz", "listed"]]

/-- The specs of a job of the corpus, from its arguments after
`frontendFuzz`. -/
def corpusSpecs? : List String → Option (List (Mode × Nat))
  | ["listed"] => some listedOutside
  | seed :: count :: args => do
    let a ← seed.toNat?
    let n ← count.toNat?
    let m ← Mode.ofArgs? args
    return (List.range n).map fun i => (m, a + i)
  | _ => none

#guard corpusSpecs? ["listed"] == some listedOutside
#guard corpusSpecs? ["5", "2", "--guards"] == some [({ guards := true }, 5), ({ guards := true }, 6)]
#guard corpusSpecs? ["5", "2", "--other"] == none
#guard corpusSpecs? ["5"] == none
-- The seeds of `knownDifferences` outside the corpus's ranges, the
-- `--avoid-known` ones among them, and every job's specs are the corpus's
-- or those.
#guard listedOutside == ({}, 153) :: ([41, 1156065, 1160095, 3000319, 3102696, 3103202, 3100624, 1159002, 3102505,
  3101311, 3104511, 1157147, 1158050, 3000892, 3102156, 1157298, 1160124, 1160173, 1160230].map
    fun s => ({ avoidKnown := true }, s))
#guard corpusJobs.all fun j => (corpusSpecs? (j.drop 1)).isSome

/-- How the differences `found` on the spec of `mode` and `seed`, those
that the solvers' time limits do not explain, fail to match `known`: those
that it does not list, each as often as it occurs beyond the times it is
listed, and the listed ones that do not occur as often as listed. A
listed one that does not occur on a spec where either front end left a
check undecided (`undecided`) may be hidden by it, and does not fail. -/
def unmatched (known : List Known) (mode : Mode) (seed : Nat) (found : Array String) (undecided : Bool) :
    Array String × List Known := Id.run do
  let mut unlisted := found
  let mut vanished := []
  for k in known do
    unless k.mode == mode && k.seed == seed do continue
    match unlisted.idxOf? k.difference with
    | some i => unlisted := unlisted.eraseIdx! i
    | none => unless undecided do vanished := vanished ++ [k]
  return (unlisted, vanished)

section
private def kd (mode : Mode := {}) (seed := 1) (difference := "d") : Known := { mode, seed, difference, issue := 0 }
-- A listed difference passes, and an unlisted one fails.
#guard unmatched [kd] {} 1 #["d"] false == (#[], [])
#guard (unmatched [kd] {} 1 #["d", "e"] false).1 == #["e"]
-- A listed one that no longer occurs fails, unless a check was undecided.
#guard ((unmatched [kd] {} 1 #[] false).2.map (·.difference)) == ["d"]
#guard (unmatched [kd] {} 1 #[] true).2.isEmpty
-- Another mode's or seed's entry does not match.
#guard (unmatched [kd (mode := { avoidKnown := true })] {} 1 #["d"] false).1 == #["d"]
#guard (unmatched [kd (seed := 2)] {} 1 #["d"] false).1 == #["d"]
-- Each entry matches one occurrence: an extra copy fails.
#guard (unmatched [kd] {} 1 #["d", "d"] false).1 == #["d"]
#guard unmatched [kd, kd] {} 1 #["d", "d"] false == (#[], [])
#guard ((unmatched [kd, kd] {} 1 #["d"] false).2.map (·.difference)) == ["d"]
end

/-- The static errors that the groups appended after the cuts of a spec
(`Mode.cuts`) add, given each cut's number of lines, each with the line
after which its group starts: each error of the `fren` command that is
not a check's result, located past the first cut's lines. Errors before
them, which may stop the checks already, are no group's. A static error
without a location, which the generator should never cause, is blamed on
the first group, when there are cuts. -/
def appendedErrors (cutLines : Array Nat) (diags : Array Diagnostic) : Array (Nat × Diagnostic) :=
  diags.filterMap fun d => do
    guard (d.severity == "error" && !FrenTest.Frontends.isCheckResult d && !FrenTest.Frontends.isStoppedTrailer d)
    if d.line == 0 then return (← cutLines[0]?, d)
    let start ← (cutLines.toList.filter (· < d.line)).max?
    return (start, d)

/-- The lines of the static errors of the `fren` command, those that are
not a check's result nor the trailer that says that they stopped the
checks (`knownKind`). -/
def staticErrorLines (diags : Array Diagnostic) : Array Nat :=
  diags.filterMap fun d =>
    if d.severity == "error" && !FrenTest.Frontends.isCheckResult d && !FrenTest.Frontends.isStoppedTrailer d
      && d.line > 0 then some d.line else none

section
private def errAt (line : Nat) (code : String := "F0304") : Diagnostic :=
  { line, severity := "error", text := "type mismatch", code? := some code }
-- An error before the first cut is no group's, even where the spec stops.
#guard (appendedErrors #[10, 20] #[errAt 3, { line := 0, severity := "error", text := Fren.Core.couldNotHeadline }]).isEmpty
-- An error in a group is caught, with the line its group starts after,
-- though an earlier one already stops the checks.
#guard (appendedErrors #[10, 20] #[errAt 3, errAt 12, errAt 25]).map (·.1) == #[10, 20]
-- A check's result and a warning are not static errors.
#guard (appendedErrors #[10] #[errAt 12 "F0603", { line := 12, severity := "warning", text := "w" }]).isEmpty
-- A static error without a location is blamed on the first group.
#guard (appendedErrors #[10, 20] #[{ line := 0, severity := "error", text := "unreadable", code? := some "F0001" }]).map (·.1) == #[10]
-- No cuts, as in `--guards`: nothing is a group's.
#guard (appendedErrors #[] #[errAt 12]).isEmpty
end

/-- Checks the specs of the corpus with both front ends, in this process.
Each failure is a difference that `knownDifferences` does not list, or a
listed one that no longer occurs (`unmatched`), leaving out those that
the solvers' time limits explain; or a static error in a group that the
generator appends after a cut (`appendedErrors`), which it must not
append, whether or not the spec stops before it. -/
def corpusFailures (env : Environment) (dir : System.FilePath) (specs : List (Mode × Nat)) :
    IO (Array String) := do
  IO.FS.createDirAll dir
  let path := dir / s!"corpus-{← IO.Process.getPID}.fren"
  let mut failures := #[]
  for (mode, s) in specs do
    let ran ← runFrontends env path (mode.spec s)
    let c := ran.comparison
    let again := s!"`lake exe fren_fuzz_frontends{flags mode} --count 1 --seed {s}`"
    let (unlisted, vanished) := unmatched knownDifferences mode s c.decided c.undecided
    for f in unlisted do
      failures := failures.push s!"seed {s}{flags mode}: the front ends differ: {f.replace "\n" " "}\n  \
        reproduce it with {again}; if its issue is known, list it in `knownDifferences` as\n  \
        \{ mode := {mode.lean}, seed := {s}, difference := {(toJson f).compress}, issue := ISSUE }"
    for k in vanished do
      failures := failures.push s!"seed {s}{flags mode}: the front ends no longer differ by `{k.difference}` (#{k.issue}); \
        remove it from `knownDifferences`, or, if a change to the generator removed it, leave every seed's spec as it was"
    let cutLines := (mode.cuts s).map fun c => (c.splitOn "\n").length - 1
    for (start, d) in appendedErrors cutLines ran.cli do
      failures := failures.push s!"seed {s}{flags mode}: what the generator appends after line {start} adds a static \
        error at line {d.line}, error{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}; an error stops \
        every check of the spec, so put deliberate errors in a mode of their own \
        (print the spec with {again.replace "--count 1 --seed" "--print"})"
  try IO.FS.removeFile path catch _ => pure ()
  return failures

/-- What a worker found on one spec, one JSON object per line of the run's
results file, so that a worker that crashes loses nothing. -/
structure Outcome where
  seed : Nat
  /-- `ok`, `differ`, `inconclusive` (differ only in undecided checks),
  `known` (with `--avoid-known`, differ only in kinds that
  `knownDifferences` lists), `crash` or `timeout`. -/
  status : String
  errors : Array String := #[]
  signatures : Array String := #[]
  deriving ToJson, FromJson

/-- A run's work files, named after the driver's process, so that runs
sharing `--out` do not mix them. -/
structure Run where
  dir : String
  id : String

def Run.results (r : Run) : System.FilePath := r.dir / s!"results-{r.id}.jsonl"
def Run.progress (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.seed"
def Run.spec (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.fren"

def record (r : Run) (o : Outcome) : IO Unit := do
  let h ← IO.FS.Handle.mk r.results .append
  h.putStrLn (toJson o).compress
  h.flush

/-- Checks the specs of seeds `[seed, seed + count)` in this process,
writing each one's outcome to the results file. -/
unsafe def worker (count seed : Nat) (run : Run) (mode : Mode) : IO UInt32 := do
  let env ← loadFren
  for i in [0:count] do
    let s := seed + i
    IO.FS.writeFile run.progress (toString s)
    let text : String := mode.spec s
    let t0 ← IO.monoMsNow
    let ran ← runFrontends env run.spec text
    let (found, flaky, reports, errs) := (ran.comparison.found, ran.comparison.flaky, ran.reports, ran.errors)
    let elapsed := (← IO.monoMsNow) - t0
    if elapsed > 20000 then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s"
    let status := if found.isEmpty then "ok" else if flaky then "inconclusive"
      else if mode.avoidKnown && found.all (knownKind mode (staticErrorLines ran.cli) found) then "known" else "differ"
    unless found.isEmpty do
      let pre := if status == "differ" then "" else s!"{status}-"
      let file : System.FilePath := run.dir / s!"{pre}fe-seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz_frontends{flags mode} --seed {s}\n" ++ header ++ reports ++ text)
      let why := match status with
        | "inconclusive" => " (only in inconclusive results)"
        | "known" => " (only in known kinds)"
        | _ => ""
      IO.eprintln s!"seed {s}: front ends differ{why}, written to {file}"
      for f in found.extract 0 4 do IO.eprintln s!"  {f}"
    record run { seed := s, status, errors := errs.toList.eraseDups.toArray, signatures := found.map signature }
    -- Between specs, a crash is no spec's.
    IO.FS.writeFile run.progress ""
  return 0

/-- Counts `x` in a tally. -/
def tally (xs : Array (String × Nat × Nat)) (x : String) (seed : Nat) : Array (String × Nat × Nat) :=
  match xs.findIdx? (·.1 == x) with
  | some k => xs.modify k fun (x, n, first) => (x, n + 1, first)
  | none => xs.push (x, 1, seed)

/-- The outcomes recorded so far in a run. -/
def outcomesOf (run : Run) : IO (Array Outcome) := do
  return ((← IO.FS.readFile run.results).splitOn "\n").toArray.filterMap fun l =>
    (Json.parse l >>= fromJson? : Except String Outcome).toOption

/-- Runs workers until every seed is checked. The solver can abort the
process (a failed assertion in cvc5), so specs run in a worker, and a
crash is recorded as the outcome of the spec it was checking. A spec that
takes longer than `limit` seconds is stopped and recorded as a timeout.
Crashes and timeouts are findings: the run then exits nonzero. A worker
that dies while checking no spec, before its first or between two, is
blamed on none: the run resumes after the last spec recorded, or stops if
the worker recorded none. -/
unsafe def mainFrontends (count seed : Nat) (dir : String) (mode : Mode) (limit : Nat) : IO UInt32 := do
  let start ← IO.monoMsNow
  let run : Run := { dir, id := toString (← IO.Process.getPID) }
  IO.FS.writeFile run.results ""
  let mut next := seed
  while next < seed + count do
    IO.FS.writeFile run.progress ""
    let args := #["--worker", run.id, "--count", toString (seed + count - next), "--seed", toString next, "--out", dir]
      ++ mode.args
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .inherit }
    -- Wait, and stop the worker if one spec takes too long.
    let mut current := ""
    let mut since ← IO.monoMsNow
    let mut code? : Option UInt32 := none
    let mut timedOut := false
    repeat
      if let some c ← child.tryWait then code? := some c; break
      let now ← IO.monoMsNow
      let cur := (← (IO.FS.readFile run.progress).toBaseIO).toOption.getD current
      if cur != current then current := cur; since := now
      else if now - since > limit * 1000 && !current.isEmpty then
        child.kill
        let _ ← child.wait
        timedOut := true
        break
      IO.sleep 200
    if code? == some 0 then break
    let some failed := (← IO.FS.readFile run.progress).trimAscii.toString.toNat?
      | let done := (← outcomesOf run).filter (fun o => next ≤ o.seed && o.seed < seed + count)
        let last? := done.foldl (fun m o => some (max (m.getD o.seed) o.seed)) none
        let some last := last?
          | IO.eprintln s!"fren_fuzz_frontends: the worker for seed {next} exited ({code?.getD 0}) before checking any spec"
            return 2
        IO.eprintln s!"seed {last + 1}: the worker exited ({code?.getD 0}) between specs; resuming"
        next := last + 1
        continue
    let what := if timedOut then s!"took more than {limit}s" else s!"crashed (exit {code?.getD 0})"
    IO.eprintln s!"seed {failed}: the worker {what}"
    let text : String := mode.spec failed
    let kind := if timedOut then "timeout" else "crash"
    IO.FS.writeFile (dir / s!"{kind}-seed{failed}.fren") (s!"-- fren_fuzz_frontends{flags mode} --seed {failed}: {what}\n" ++ text)
    record run { seed := failed, status := kind }
    next := failed + 1
  let outcomes ← outcomesOf run
  for f in [run.progress, run.spec] do
    try IO.FS.removeFile f catch _ => pure ()
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
    the front ends differ, {n "inconclusive"} more only in inconclusive results, \
    {n "known"} more only in known kinds, {n "crash"} crashed, \
    {n "timeout"} took more than {limit}s (results in {run.results})"
  return if n "differ" + n "crash" + n "timeout" == 0 then 0 else 1

def usage : String :=
  "usage: fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--avoid-known] [--guards] [--sites] [--spec-timeout SECONDS]\n" ++
  "       fren_fuzz_frontends --files FILE...\n" ++
  "       fren_fuzz_frontends [--avoid-known] [--guards] [--sites] --print SEED"

structure Opts where
  count : Nat := 100
  seed : Nat := 0
  dir : String := ".lake/fuzz"
  limit : Nat := 30
  worker? : Option String := none

unsafe def main (args : List String) : IO UInt32 := do
  if let "--files" :: files := args then
    IO.FS.createDirAll ".lake/fuzz"
    return ← mainFiles files ".lake/fuzz"
  let mode : Mode := { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards"
                       sites := args.contains "--sites" }
  let args := args.filter (fun a => a != "--avoid-known" && a != "--guards" && a != "--sites")
  if let ["--print", n] := args then
    let some s := n.toNat? | IO.eprintln usage; return 2
    IO.print (mode.spec s)
    return 0
  let rec parse : List String → Opts → Option Opts
    | [], o => some o
    | "--count" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with count := n }
    | "--seed" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with seed := n }
    | "--out" :: d :: rest, o => parse rest { o with dir := d }
    | "--spec-timeout" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with limit := n }
    | "--worker" :: id :: rest, o => parse rest { o with worker? := some id }
    | _, _ => none
  let some o := parse args {} | IO.eprintln usage; return 2
  IO.FS.createDirAll o.dir
  match o.worker? with
  | some id => worker o.count o.seed { dir := o.dir, id } mode
  | none => mainFrontends o.count o.seed o.dir mode o.limit

end FrenTest.FuzzFrontends
