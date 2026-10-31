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
latter sometimes with contracts whose postconditions may contradict each
other, so that what applies them rests on their realizability, `match`
and tables over a scrutinee,
string methods with constant and non-constant arguments and `++`, products
of every kind of operand, orderings and `min` and `max` of an ordered
enumeration, an enumeration with payloads, whose outputs' variants a
clash note may give, and sets and relations with `card`, so that it
reaches `linear_product`, the decidable core and the lints.

What legitimately differs is normalized away by
`FrenTest.Frontends.compare`, whose documentation lists it, as does
`Reqs/dev/Testing`. Specs run in worker processes (`--worker`), so that a
solver that aborts, or a spec that runs too long (`--spec-timeout`), is
recorded against its spec and the run goes on.

`--avoid-known` keeps the generator clear of the differences already
known, to find others: it parenthesizes every method's receiver that is
not a name. `--guards` generates guarded quantifiers alone
(`Wide.genGuards`), over every type that a guard may bound or not, with
their operands read through fields, so that many run fast; `genWide`
includes such a procedure now and then too.
-/

open Lean FrenCli FrenCli.Eval

namespace FrenFuzzFrontends

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

/-- A table with values of type `t`: one to three rows, sometimes after
a leading `|`, and sometimes a last `_` row; or a table over an integer,
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
  let bar := if ← chance 30 then "| " else ""
  return s!"table \{ {", ".intercalate (rows.toList.map (bar ++ ·))} }"

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

/-- A spec with constants, functions, and components over them. -/
def genWide (avoidKnown : Bool := false) : R String := do
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
  -- Only variables have the type `P`, each declared on a line of its own.
  return if genericPay then (out.replace ": P\n" ": P<Int>\n").replace ": P,\n" ": P<Int>,\n" else out

end Wide

/-! ### Running the front ends -/

open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends (Report maskBetween headOf)

/-- Checks `text` with both front ends; returns how they differ, whether
only in undecided checks, both reports, and the binary's error codes. -/
def runFrontends (env : Environment) (path : System.FilePath) (text : String) :
    IO (Array String × Bool × String × Array String) := do
  IO.FS.writeFile path text
  let (out, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files := #[path.toString] })
  let (cli, cliSum) := FrenTest.Ui.cliDiagnostics path.toString out (keepUnlocated := true)
  let (hosted, hostedSum) ← FrenTest.Ui.hostedDiagnostics env path.toString text
  let (found, flaky) := FrenTest.Frontends.compare text
    { diags := cli, summary? := cliSum, exit? := some code.toNat } { diags := hosted, summary? := hostedSum }
  let render (ds : Array Diagnostic) (s : Option String) :=
    String.join (ds.toList.map fun d => s!"--   {d.line}: {d.severity}{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}\n")
      ++ s!"--   summary: {s.getD "(none)"}\n"
  return (found, flaky, s!"-- fren (exit {code}):\n{render cli cliSum}-- Lean:\n{render hosted hostedSum}",
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
    let (found, _, reports, _) ← runFrontends env (dir / s!"current-files-{← IO.Process.getPID}.fren") (← IO.FS.readFile f)
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

def Mode.spec (m : Mode) (seed : Nat) : String :=
  Id.run ((if m.guards then Wide.genGuards else Wide.genWide m.avoidKnown).run' (rngOf seed))

def Mode.args (m : Mode) : Array String :=
  (if m.avoidKnown then #["--avoid-known"] else #[]) ++ (if m.guards then #["--guards"] else #[])

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

/-- What a worker found on one spec, one JSON object per line of the run's
results file, so that a worker that crashes loses nothing. -/
structure Outcome where
  seed : Nat
  /-- `ok`, `differ`, `inconclusive` (differ only in undecided checks),
  `crash` or `timeout`. -/
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

def flags (m : Mode) : String := String.join (m.args.toList.map (" " ++ ·))

/-- Checks the specs of seeds `[seed, seed + count)` in this process,
writing each one's outcome to the results file. -/
unsafe def worker (count seed : Nat) (run : Run) (mode : Mode) : IO UInt32 := do
  let env ← loadFren
  for i in [0:count] do
    let s := seed + i
    IO.FS.writeFile run.progress (toString s)
    let text : String := mode.spec s
    let t0 ← IO.monoMsNow
    let (found, flaky, reports, errs) ← runFrontends env run.spec text
    let elapsed := (← IO.monoMsNow) - t0
    if elapsed > 20000 then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s"
    let status := if found.isEmpty then "ok" else if flaky then "inconclusive" else "differ"
    unless found.isEmpty do
      let file : System.FilePath := run.dir / s!"{if flaky then "inconclusive-" else ""}fe-seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz_frontends{flags mode} --seed {s}\n" ++ header ++ reports ++ text)
      IO.eprintln s!"seed {s}: front ends differ{if flaky then " (only in inconclusive results)" else ""}, written to {file}"
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
    the front ends differ, {n "inconclusive"} more only in inconclusive results, {n "crash"} crashed, \
    {n "timeout"} took more than {limit}s (results in {run.results})"
  return if n "differ" + n "crash" + n "timeout" == 0 then 0 else 1

def usage : String :=
  "usage: fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--avoid-known] [--guards] [--spec-timeout SECONDS]\n" ++
  "       fren_fuzz_frontends --files FILE...\n" ++
  "       fren_fuzz_frontends [--avoid-known] [--guards] --print SEED"

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
  let mode : Mode := { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards" }
  let args := args.filter (fun a => a != "--avoid-known" && a != "--guards")
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

end FrenFuzzFrontends

unsafe def main (args : List String) : IO UInt32 := FrenFuzzFrontends.main args
