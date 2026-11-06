-- keep-sorted start
import Fren
import FrenCli.Run
import FrenTest.Frontends
import FrenTest.FuzzDatatypeElements
import FrenTest.Messages
import FrenTest.SpecTimeout
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
(`sitesProc`), traits, with laws and expectations over their methods
(`traitGroup`), a recursive function applied on several paths of one
expectation (`guardPaths`), and global expectations over recursive
enumerations that induction on a parameter may prove (`inductions`).

What legitimately differs is normalized away by
`FrenTest.Frontends.compare`, whose documentation lists it, as does
`Reqs/dev/Testing`. Specs run in worker processes (`--worker`), so that a
solver that aborts, or a spec that runs too long (`--spec-timeout`), is
recorded against its spec and the run goes on.

`--avoid-known` keeps the generator clear of the differences already
known, to find others: it parenthesizes every method's receiver that is
not a name, and counts a spec whose every difference is of a kind that
`knownDifferences` lists for `--avoid-known`, or that `knownKinds` lists,
as known, not as a finding (`knownIssue?`). `lake test` checks a fixed
corpus of seeds against `knownDifferences` (`corpusFailures`), and that
what `genWide` appends adds no static error (`Wide.genWideCuts`); CI runs
fresh seeds on `main`, and fails only on a difference of a kind that is
not known, a crash or a timeout. `--report DIR` gives the results of the
runs in `DIR` as Markdown (`report`), for CI's job summary.
`--guards` generates guarded quantifiers alone
(`Wide.genGuards`), over every type that a guard may bound or not, with
their operands read through fields, so that many run fast; `genWide`
includes such a procedure now and then too. `--sites` generates
`Wide.sitesProc`s alone, the last of which may write an expression that
does not synthesize its type where it is not checked, an error that stops
the spec's other checks; `genWide` includes one without it now and then.
`--inductions` generates global expectations over recursive enumerations
alone (`Wide.inductions`), which induction on a parameter may prove, and
`--induction-forms` the forms in which the front ends read a candidate
for it (`Wide.inductionForms`); `--induction-candidates` generates declared
type, comparison and binder forms (`Wide.inductionCandidates`).
`--datatype-elements` generates generic enumerations and records with
collection payloads and fields (`FuzzDatatypeElements.spec`).
`--confirm` generates what the confirmation of models evaluates
(`Wide.genConfirmed`): `div` and `mod`, an index in an argument that a
function's body never reads, and the formulas whose value confirmation
knows where an index is out of range; and it checks them with both front
ends misreading models (`Fren.Core.misreadSet`), so that what one knows
and the other does not is a message that differs.
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
    let pre := s!"    require p: x >= {← pick #["-2", "-1", "0"]}\n"
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
  return decls ++ s!"\n{options}pub proc {name}(x: Int): (det y: Int) \{\n    require a: x != 5\n    \
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
    if ← chance 40 then body := body ++ s!"    require a: x > {← below 4}\n"
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
    let pre := if ← chance 30 then s!"    require p: b?\n" else ""
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

/-- A recursive defined function with a postcondition, applied on several
paths of one expectation, each with its own guards, whose facts a query
asserts once, under its weakest paths (`lang::merged_facts`): on a path
whose guards include another's, on two neither of whose guards are among
the other's, or on one without guards first; and at a larger argument,
whose one-step equation applies it again. Each expectation holds, by the
postcondition or by one unfolding, so no result depends on a model. It is
written from a grammar of its own, as `factChain` is. -/
def guardPaths : R String := do
  let k ← below 3
  let shape ← below 3
  let (params, goal) := match shape with
    | 0 => ("a?", "(not a? or gpsum(l) >= 0) and (not a? or gpsum(l) > -1)")
    | 1 => ("a?, b?", s!"(not a? or gpsum(l) >= 0) and (not b? or gpsum(GuardList::Cons({k}, l)) >= {k})")
    | _ => ("a?", s!"gpsum(l) > -1 and (not a? or gpsum(GuardList::Cons({k}, l)) >= {k})")
  return "pub enum GuardList { Nil, Cons(Int, GuardList) }\n" ++
    "pub fn gpsum(l: GuardList): (r: Int) {\n    out r := match l { GuardList::Nil => 0, GuardList::Cons(m, rest) => m.abs + gpsum(rest) }\n" ++
    "    ensure e: r >= 0\n}\n" ++
    s!"\nproc gp_paths(l: GuardList, {params}) \{\n    expect c: {goal}\n}\n"

/-- Global expectations over recursive enumerations, whose claims their
checks leave Inconclusive and induction on a parameter may prove
(`Reqs/Lang/Recursion#induction`): over a list, a tree with two children
and a `Bool` payload, and an instance of a generic enumeration; with
parameters of those types, of `Int`, of `Bool` and of a payload's type,
in either order; under an assumption or not; claims that one step of each
function proves, that need more (which the deeper unfolding of an
induction's check may prove), and in a Boolean block; and the forms that
rule induction out: a call, an uninterpreted function, a parameter of a
subset type. Each claim holds, so no result depends on a model, but for
one false claim now and then, which fails under its function's contract
with a counterexample that evaluation does not confirm, not the internal
error of a model that contradicts Fren's semantics: so it stays
Inconclusive, with no model shown, induction is tried on it, and induction
must not pass it. It is written from a grammar of its own, as `factChain`
is. -/
def inductions : R String := do
  let mut out := "pub enum IdList { Nil, Cons(Int, IdList) }\n" ++
    "pub enum IdTree { Leaf(Bool), Node(IdTree, Int, IdTree) }\n" ++
    "pub enum IdGen<A> { Z, S(A, IdGen<A>) }\n" ++
    "pub fn idlen(l: IdList): Int := match l { IdList::Nil => 0, IdList::Cons(_, r) => 1 + idlen(r) }\n" ++
    "pub fn idapp(a: IdList, b: IdList): IdList := match a {\n" ++
    "    IdList::Nil => b,\n    IdList::Cons(h, t) => IdList::Cons(h, idapp(t, b)),\n}\n" ++
    "pub fn idsize(t: IdTree): Int := match t { IdTree::Leaf(_) => 1, IdTree::Node(l, _, r) => idsize(l) + 1 + idsize(r) }\n" ++
    "pub fn idmirror(t: IdTree): IdTree := match t {\n" ++
    "    IdTree::Leaf(x?) => IdTree::Leaf(x?),\n    IdTree::Node(l, n, r) => IdTree::Node(idmirror(r), n, idmirror(l)),\n}\n" ++
    "pub fn idcount<A>(g: IdGen<A>): Int := match g { IdGen::Z => 0, IdGen::S(_, r) => 1 + idcount(r) }\n"
  -- Each claim, with its parameters, which come in either order.
  let swap ← chance 50
  let two (x y : String) : String := if swap then s!"{y}, {x}" else s!"{x}, {y}"
  let claims : Array (String × String × String) := #[
    ("adds", two "a: IdList" "b: IdList", "expect c: idlen(idapp(a, b)) = idlen(a) + idlen(b)"),
    ("nil_right", "a: IdList", "expect c: idapp(a, IdList::Nil) = a"),
    ("assoc", "a: IdList, b: IdList, c: IdList", "expect holds: idapp(idapp(a, b), c) = idapp(a, idapp(b, c))"),
    ("mirror_size", "t: IdTree", "expect c: idsize(idmirror(t)) = idsize(t)"),
    ("mirror_twice", "t: IdTree", "expect c: idmirror(idmirror(t)) = t"),
    ("count", "g: IdGen<Int>", "expect c: idcount(g) >= 0"),
    ("suffix", two "a: IdList" "b: IdList", "assume e: b = IdList::Nil\n    expect c: idlen(idapp(a, b)) = idlen(a)"),
    ("one_more", two "a: IdList" "k: Int", "expect c: idlen(idapp(a, IdList::Cons(k, IdList::Nil))) = idlen(a) + 1"),
    ("flagged", two "a: IdList" "x?", "expect c: when x?, idapp(a, IdList::Nil) = a"),
    ("both", two "a: IdList" "b: IdList",
      "expect c: and {\n        n: idapp(a, IdList::Nil) = a,\n        s: idlen(idapp(a, b)) = idlen(a) + idlen(b),\n    }")]
  for (n, params, body) in claims do
    if ← chance 50 then out := out ++ s!"\nexpect id_{n}({params}) \{\n    {body}\n}\n"
  -- The forms that rule induction out.
  if ← chance 40 then
    out := out ++ "\npub proc idmeasure(l: IdList): (det n: Int) {\n    ensure value: n = idlen(l)\n}\n" ++
      "\nexpect id_called(a: IdList, b: IdList) {\n    call m := idmeasure(idapp(a, b))\n" ++
      "    expect c: m.n = idlen(a) + idlen(b)\n}\n"
  if ← chance 40 then
    out := out ++ "\npub fn idweight(IdList): Int\n" ++
      "\nexpect id_weighed(a: IdList, b: IdList) {\n    expect c: idlen(idapp(a, b)) + idweight(a) = idlen(a) + idlen(b) + idweight(a)\n}\n"
  if ← chance 40 then
    out := out ++ "\npub type IdCons = l: IdList where invariant: l is IdList::Cons(_, _)\n" ++
      s!"\nexpect id_subset({two "a: IdList" "b: IdCons"}) \{\n    expect c: idlen(idapp(a, b)) = idlen(a) + idlen(b)\n}\n"
  -- A false claim that its own check leaves Inconclusive, which induction
  -- must not pass, last.
  if ← chance 30 then
    out := out ++ "\nexpect id_off(a: IdList) {\n    expect c: idlen(a) != 5\n}\n"
  return out

/-- Global expectations in the forms where the two front ends read a
candidate for induction with code of their own (`lang::induction_candidate`,
`--induction-forms`): a decreasing argument in parentheses or nested in
another application; one hidden by a `match` arm's binder that shadows the
parameter; a recursion applied only to another expression; the other members
of a block (`let`, `use`, a call, a `cover`, a claim under an evidence
setting, an assumption that is a Boolean block); an uninterpreted
function, generic or not; a parameter of a type alias, of a nested instance
of a generic enumeration, and of an enumeration with a payload of a subset
type; and an enumeration of another module, which is not tried
(`Reqs/Lang/Recursion#induction`). Each claim holds, so no result depends
on a model. A mode of its own, so that no other seed's spec changes. -/
def inductionForms : R String := do
  let mut out := "mod jforms\n\npub enum JL { Nil, Cons(Int, JL) }\n" ++
    "pub enum JG<A> { Z, S(A, JG<A>) }\n" ++
    "pub type JList := JL\n" ++
    "pub type JPos = n: Int where positive: n >= 1\n" ++
    "set_option fren.lint.undecidable \"allow\" in\npub enum JP { Nil, Cons(JPos, JP) }\n" ++
    "pub fn jlen(l: JL): Int := match l { JL::Nil => 0, JL::Cons(_, r) => 1 + jlen(r) }\n" ++
    "pub fn japp(a: JL, b: JL): JL := match a {\n" ++
    "    JL::Nil => b,\n    JL::Cons(h, t) => JL::Cons(h, japp(t, b)),\n}\n" ++
    "pub fn jcount<A>(g: JG<A>): Int := match g { JG::Z => 0, JG::S(_, r) => 1 + jcount(r) }\n" ++
    "pub fn jplen(l: JP): Int := match l { JP::Nil => 0, JP::Cons(_, r) => 1 + jplen(r) }\n" ++
    "pub fn jw(JL): Int\n" ++
    "pub fn jgw<T>(T): Int\n" ++
    "pub proc jmeasure(l: JL): (det n: Int) {\n    ensure value: n = jlen(l)\n}\n"
  let adds (a b : String) := s!"jlen(japp({a}, {b})) = jlen({a}) + jlen({b})"
  -- Each form, with the parameters it is over and its block, drawn or not.
  let forms : Array (String × String × String) := #[
    ("parens", "a: JL, b: JL", s!"expect c: {adds "(a)" "b"}"),
    ("nested", "a: JL, b: JL, c: JL",
      "expect holds: jlen(japp(japp(a, b), c)) = jlen(a) + jlen(b) + jlen(c)"),
    ("shadowed", "a: JL, b: JL",
      "expect c: match b {\n        JL::Nil => jlen(a) >= 0,\n        JL::Cons(_, a!) => jlen(a) >= 0,\n    }"),
    ("other_arg", "a: JL", "expect c: jlen(JL::Cons(1, a)) >= 1"),
    ("let_member", "a: JL, b: JL", s!"let n: Int := jlen(a)\n    expect c: n + jlen(b) = jlen(a) + jlen(b)"),
    ("use_member", "a: JL", "use self::JL::{Nil}\n    expect c: japp(a, Nil) = a"),
    ("call_member", "a: JL, b: JL", "call m := jmeasure(japp(a, b))\n    expect c: m.n = jlen(a) + jlen(b)"),
    ("cover_member", "a: JL, b: JL", s!"cover nonempty: a != JL::Nil\n    expect c: {adds "a" "b"}"),
    ("evidence", "a: JL, b: JL", s!"set_option fren.evidence \"solver\" in\n    expect c: {adds "a" "b"}"),
    ("block_assume", "a: JL, b: JL",
      "assume e: and {\n        empty: b = JL::Nil,\n        zero: jlen(b) = 0,\n    }\n    expect c: jlen(japp(a, b)) = jlen(a)"),
    ("abstract", "a: JL, b: JL", s!"expect c: {adds "a" "b"} + jw(a) - jw(a)"),
    ("generic_abstract", "a: JL, b: JL", s!"expect c: {adds "a" "b"} + jgw(a) - jgw(a)"),
    ("alias", "a: JList, b: JL", s!"expect c: {adds "a" "b"}"),
    ("nested_instance", "g: JG<JG<Int>>", "expect c: jcount(g) >= 0"),
    ("subset_payload", "l: JP", "expect c: jplen(l) >= 0")]
  for (n, params, body) in forms do
    if ← chance 50 then out := out ++ s!"\nexpect jf_{n}({params}) \{\n    {body}\n}\n"
  -- An enumeration of another module, last, as its module's `use` ends
  -- the spec.
  if ← chance 30 then
    out := out ++ "\nmod jother\n\nuse jforms::{JL, japp, jlen}\n" ++
      s!"\nexpect jf_module(a: JL, b: JL) \{\n    expect c: {adds "a" "b"}\n}\n"
  return out

/-- Global expectations whose claims induction proves only by unfolding
more than one step of each function's equations, as the check of a function
generated for induction does (`Reqs/Lang/Recursion#unfolding-in-an-induction`):
over a list and a tree with two children and a `Bool` payload, claims whose
base case needs the equations at a depth that grows with a constant's size,
of 1 to 4 elements or levels, so that both sides of the bound are reached;
with another parameter now and then, in either order; and a claim with no
parameter, which no induction checks, and whose constant arguments need
the equations at depth 1. Appended forms use generic lists, assumptions
and Boolean blocks, and a binary recursion whose deeper equations bring
another function's contract. Each claim holds, so no result depends on a
model. Its generator is split off the seed, and appended forms draw last,
so the other modes and every existing spec's prefix stay unchanged. -/
def unfoldings : R String := do
  let mut out := "mod uunfold\n\n" ++
    "pub enum UL { Nil, Cons(Int, UL) }\n" ++
    "pub enum UT { Leaf(Bool), Node(UT, Int, UT) }\n" ++
    "pub fn ulen(l: UL): Int := match l { UL::Nil => 0, UL::Cons(_, r) => 1 + ulen(r) }\n" ++
    "pub fn uapp(a: UL, b: UL): UL := match a {\n" ++
    "    UL::Nil => b,\n    UL::Cons(h, t) => UL::Cons(h, uapp(t, b)),\n}\n" ++
    "pub fn uleaves(t: UT): Int := match t { UT::Leaf(_) => 1, UT::Node(l, _, r) => uleaves(l) + uleaves(r) }\n" ++
    "pub fn ugraft(t: UT, s: UT): UT := match t {\n" ++
    "    UT::Leaf(_) => s,\n    UT::Node(l, n, r) => UT::Node(ugraft(l, s), n, r),\n}\n"
  -- A list of `n` elements, and a tree of height `n` with `n + 1` leaves.
  let mut i := 0
  for n in [1, 2, 3, 4] do
    if ← chance 60 then
      let mut l := "UL::Nil"
      for _ in [0:n] do l := s!"UL::Cons({← below 10}, {l})"
      let mut t := s!"UT::Leaf({← pick #["true", "false"]})"
      for _ in [0:n] do t := s!"UT::Node(UT::Leaf({← pick #["true", "false"]}), {← below 10}, {t})"
      let extra ← chance 30
      let swap ← chance 50
      let ps (p : String) := if !extra then p else if swap then s!"k: Int, {p}" else s!"{p}, k: Int"
      let more := if extra then " + k - k" else ""
      if ← chance 70 then
        out := out ++ s!"\nexpect ul_{i}({ps "a: UL"}) \{\n    expect c: ulen(uapp(a, {l})) = ulen(a) + {n}{more}\n}\n"
      if ← chance 70 then
        out := out ++ s!"\nexpect ut_{i}({ps "t: UT"}) \{\n    expect c: uleaves(ugraft(t, {t})) = uleaves(t) + {n}{more}\n}\n"
    i := i + 1
  if ← chance 40 then
    out := out ++ s!"\nset_option fren.lint.assertions_on_constants \"allow\" in\nexpect uconst: ulen(uapp(UL::Nil, UL::Cons({← below 10}, UL::Nil))) = 1\n"
  -- Draw only after the original generator, preserving every old prefix.
  out := out ++ "\npub enum UG<T> { Nil, Cons(T, UG<T>) }\n" ++
    "pub fn uglen<T>(l: UG<T>): Int := match l { UG::Nil => 0, UG::Cons(_, r) => 1 + uglen(r) }\n" ++
    "pub fn ugapp<T>(a: UG<T>, b: UG<T>): UG<T> := match a {\n" ++
    "    UG::Nil => b,\n    UG::Cons(h, t) => UG::Cons(h, ugapp(t, b)),\n}\n"
  let ty ← pick #["Int", "Bool"]
  let n := (← below 4) + 1
  let mut suffix := "UG::Nil"
  for _ in [0:n] do
    let value ← if ty == "Int" then toString <$> below 10 else pick #["true", "false"]
    suffix := s!"UG::Cons({value}, {suffix})"
  out := out ++ s!"\nexpect ug_assume(a: UG<{ty}>, b: UG<{ty}>) \{\n" ++
    s!"    assume fixed: b = {suffix}\n    expect c: uglen(ugapp(a, b)) = uglen(a) + {n}\n}\n" ++
    s!"\nexpect ug_block(a: UG<{ty}>) \{\n    expect c: and \{\n" ++
    s!"        length: uglen(ugapp(a, {suffix})) = uglen(a) + {n},\n" ++
    "        identity: ugapp(a, UG::Nil) = a,\n    }\n}\n"
  -- The two leaf applications are at depth 2; their equations introduce
  -- `uweight` at depth 3, where its contract still brings facts.
  out := out ++ "\npub fn uweight(t: UT): (n: Int) {\n    out n := match t {\n" ++
    "        UT::Leaf(_) => 1,\n        UT::Node(l, _, r) => uweight(l) + uweight(r),\n    }\n" ++
    "    ensure positive: n >= 1\n}\n" ++
    "pub fn ubranch(t: UT): Int := match t {\n" ++
    "    UT::Leaf(b?) => uweight(UT::Leaf(b?)),\n    UT::Node(l, _, r) => ubranch(l) + ubranch(r),\n}\n" ++
    "\nexpect ubinary(t: UT) {\n    expect c: ubranch(UT::Node(\n" ++
    s!"        UT::Node(UT::Leaf(true), {← below 10}, UT::Leaf(false)), {← below 10}, t\n" ++
    "    )) >= ubranch(t) + 2\n}\n"
  return out

/-- Specs of induction candidacy and function construction: each samples a
companion parameter type, an argument form and a comparison. Its generator
is split off the seed, leaving the other modes' draws unchanged. All claims
hold; no form adds a static error that suppresses the checks. -/
def inductionCandidates : R String := do
  let mut out := "mod kcandidates\n\nset_option fren.lint.undecidable \"allow\"\n\n" ++
    "pub enum KL { Nil, Cons(Int, KL) }\n" ++
    "pub enum KG<A> { Z, S(A, KG<A>) }\n" ++
    "pub enum KLeaf { A, B }\n" ++
    "pub enum KBox<A> { Box(A) }\n" ++
    "set_option fren.lint.non_camel_case_types \"allow\" in\npub enum KCollision { fren_induction_p0, C(Int, KCollision) }\n" ++
    "set_option fren.lint.non_camel_case_types \"allow\" in\npub enum fren_induction_p0 { Z, S(Int, fren_induction_p0) }\n" ++
    "pub type KAlias := fren_induction_p0\n" ++
    "pub struct KRecord { list: KL }\n" ++
    "pub struct KInt(Int)\n" ++
    "pub type KOpaque\n" ++
    "pub type KPos = n: Int where positive: n >= 1\n" ++
    "pub type KNonempty = l: KL where nonempty: l is KL::Cons(_, _)\n" ++
    "pub fn klen(l: KL): Int := match l { KL::Nil => 0, KL::Cons(_, r) => 1 + klen(r) }\n" ++
    "pub fn kapp(a: KL, b: KL): KL := match a {\n" ++
    "    KL::Nil => b,\n    KL::Cons(h, t) => KL::Cons(h, kapp(t, b)),\n}\n" ++
    "pub fn ksecond(k: Int, a: KL): KL := match a {\n" ++
    "    KL::Nil => KL::Nil,\n    KL::Cons(h, t) => KL::Cons(h, ksecond(k, t)),\n}\n" ++
    "pub fn kcount<A>(g: KG<A>): Int := match g { KG::Z => 0, KG::S(_, r) => 1 + kcount(r) }\n" ++
    "pub fn kkeep<A>(x: A, a: KL): A := match a { KL::Nil => x, KL::Cons(_, r) => kkeep(x, r) }\n" ++
    "pub fn kcollision(a: KCollision): Int := match a { KCollision::fren_induction_p0 => 0, KCollision::C(_, r) => 1 + kcollision(r) }\n" ++
    "pub fn kalias(a: KAlias): Int := match a { fren_induction_p0::Z => 0, fren_induction_p0::S(_, r) => 1 + kalias(r) }\n"
  let right := "kapp(a, KL::Nil) = a"
  -- Every unrestricted companion type must leave `a` a candidate; every
  -- restricted companion must exclude all parameters, even if unused.
  let types := #["Int", "Nat", "Bool", "String", "Set<Int>", "Seq<Int>", "Rel<Int, Bool>",
    "KLeaf", "KRecord", "KInt", "KOpaque", "KG<KG<Bool>>", "KNonempty", "KPos", "Set<KPos>",
    "Seq<KPos>", "Rel<KPos, Int>", "Rel<Int, KPos>", "KBox<KPos>", "KBox<Seq<KPos>>", "Seq<KBox<KPos>>"]
  let t ← pick types
  let x := if t == "Bool" then "x?" else "x"
  let ps := if ← chance 50 then s!"a: KL, {x}: {t}" else s!"{x}: {t}, a: KL"
  let same := if ← chance 50 then s!"kkeep({x}, a) = {x}" else s!"not (kkeep({x}, a) != {x})"
  out := out ++ s!"\nexpect kc_type({ps}) \{ expect c: ({right}) and ({same}) }\n"
  let forms : Array (String × String × String) := #[
    ("second", "k: Int, a: KL", "expect c: ksecond(k, a) = a"),
    ("second_parens", "a: KL, k: Int", "expect c: ksecond(k, ((a))) = a"),
    ("two", "b: KL, a: KL", "expect c: klen(kapp(a, b)) = klen(a) + klen(b)"),
    ("field", "r: KRecord", "expect c: klen(r.list) >= 0"),
    ("constructed", "a: KL", "expect c: klen(KL::Cons(0, a)) >= 1"),
    ("where", "a: KL", "expect c: kapp(t, KL::Nil) = t where t := a"),
    ("let_expr", "a: KL", "expect c: let t := a in kapp(t, KL::Nil) = t"),
    ("shadow_only", "a: KL, b: KL", "expect c: match b { KL::Nil => true, KL::Cons(_, a!) => klen(a) >= 0 }"),
    ("shadow_then_free", "a: KL, b: KL", s!"expect c: (match b \{ KL::Nil => true, KL::Cons(_, a!) => klen(a) >= 0 }) and ({right})"),
    ("nested_generic", "g: KG<KG<Bool>>", "expect c: kcount(g) >= 0"),
    ("nested_restricted", "a: KL, g: KBox<KBox<KPos>>", s!"expect c: {right}"),
    ("assumptions", "a: KL, b: KL", "assume one: b = KL::Nil\n    assume two: klen(b) = 0\n    expect c: klen(kapp(a, b)) = klen(a)"),
    ("bool_claims", "a: KL", s!"expect c: and \{ right: {right}, nonnegative: klen(a) >= 0 }"),
    ("conditional", "a: KL, b?", s!"expect c: if b? then {right} else klen(a) >= 0"),
    ("variant_placeholder", "a: KCollision", "expect c: kcollision(a) >= 0"),
    ("alias_placeholder", "a: KAlias", "expect c: kalias(a) >= 0")]
  let (n, ps, body) ← pick forms
  out := out ++ s!"\nexpect kc_{n}({ps}) \{\n    {body}\n}\n"
  -- Every comparison, with a recursive application nested in arithmetic.
  let op ← pick #["=", "!=", "<", "<=", ">", ">="]
  let rhs := if op == "!=" || op == "<" then "1" else if op == ">" then "-1" else "0"
  out := out ++ s!"\nexpect kc_compare(a: KL) \{ expect c: klen(a) - klen(a) {op} {rhs} }\n"
  return out

/-- Preconditions in each form that a clause about the inputs takes
(`lang::precondition_word`): `require` in a procedure's block, labelled,
with a `where` clause, as a labelled `and` block, as an unlabelled one and
under a leading `when`, in a function's block, labelled or as an unlabelled
`and` block, alone, under a leading `when` or `let` or before a `where`, a
generic function's and a trait method's; and the
`assume` of a global expectation that calls the procedure, where the
preconditions hold. Its checks pass, and nothing here is a static error.
The procedure is checked by the solver: a global expectation over one
checked by random testing is a difference of its own (only the `fren`
command says what rests on it, `F0663`).
It is appended to specs of the corpus, so it is written from a grammar of
its own. -/
def requireForms : R String := do
  let low ← pick #["-3", "-1", "0"]
  let mut body := s!"    require n0: x > {low}\n"
  if ← chance 50 then body := body ++ "    require n1: y >= x - k where k := 2\n"
  if ← chance 50 then body := body ++ s!"    require n2: and \{ a: x > {low} - 1, b: y > -9 }\n"
  if ← chance 50 then body := body ++ "    require and { c: x != 3, d: b? or y > 0 }\n"
  if ← chance 50 then body := body ++ "    require when b?, and { e: y > 0 }\n"
  body := body ++ "    out r := x\n    ensure q: r = x\n"
  let mut out := s!"pub proc pw_proc(x: Int, y: Int, b?): (det r: Int) \{\n{body}}\n"
  if ← chance 60 then
    out := out ++ s!"\npub fn pw_fn(x: Int): (r: Int) \{\n    require p: x > {low}\n    out r := x + 1\n    ensure s: r > {low}\n}\n"
  if ← chance 50 then
    out := out ++ "\npub fn pw_generic<T>(q: Seq<T>, d: T): (r: T) {\n    require first: q != [] and q[0] = d\n    out r := d\n}\n"
  if ← chance 40 then
    out := out ++ "\npub trait PwTrait {\n    fn pw_method(s: Self, x: Int): (r: Int) {\n        require p: x > 0\n        ensure q: r >= 0\n    }\n}\n"
  if ← chance 60 then
    out := out ++ "\nexpect pw_global(x: Int, y: Int) {\n    assume big: x > 5 and y > x\n    call c := pw_proc(x, y, true)\n" ++
      "    expect e: c.r = x\n}\n"
  -- After every earlier draw, so that what the seed gave before stays: a
  -- function's preconditions without a label, a Boolean block, alone,
  -- under a leading `when` or `let`, or before a `where`, and an
  -- application that meets them.
  if ← chance 50 then
    let pre ← pick #[s!"require and \{ p: x > {low} }", s!"require when x > 0, and \{ p: x > {low} }",
      s!"require and \{ p: x > {low}, q: x > {low} - 1 }", s!"require and \{ p: x > k } where k := {low}",
      s!"require let m := {low} in and \{ p: x > m }"]
    out := out ++ s!"\npub fn pw_bare(x: Int): (r: Int) \{\n    {pre}\n    out r := x + 1\n}\n" ++
      "\nproc pw_bare_use(x: Int): (y: Int) {\n    require big: x > 5\n    ensure e: y = pw_bare(x)\n}\n"
  return out

/-- Generic functions whose type parameters are element types
(`lang::element_parameter`): sets, sequences and relations of them, nested
and within an instance, in signatures, bodies and contracts, defined and
not, one applied within another at its own type parameter, one whose type
argument only what is expected gives, one with a function parameter,
preconditions and postconditions over an element of a `Seq<T>`, and a
procedure that applies them at one element type: `Int`, `Bool`, `String`, an
abstract type, `E` if the spec has it, or `Option<Int>`, with arguments that
are empty literals, nested or not, in either order. Now and then, at `Bool`
or `E`, the procedure is enumerated, with only inputs of that type and small
sets and sequences of it, so that it is enumerated indeed. A postcondition
may fail, a check's result, but nothing here is a static error: no
relational operator or quantifier over a set's members, which are outside
the decidable core, and the function without a body only at `Int`, since one
of sets of a type that may be finite is too (#437). -/
def genericElements (sc : WScope) : R String := do
  let mut out := "pub type Atom\n" ++
    "pub fn ge_grow<T>(s: Set<T>, x: T): Set<T> := s union {x}\n" ++
    "pub fn ge_twice<T>(s: Set<T>, x: T): Set<T> := ge_grow(ge_grow(s, x), x)\n" ++
    "pub fn ge_has?<T>(s: Set<T>, x: T) := x in s\n" ++
    "pub fn ge_first<T>(q: Seq<T>, d: T): T := if q != [] then q[0] else d\n" ++
    "pub fn ge_at<T>(q: Seq<T>): T := q[0]\n" ++
    "pub fn ge_apply?<T>(q: Seq<T>, f: fn(T) -> Bool) := f(q[0])\n" ++
    "pub fn ge_pick<T>(q: Seq<T>, d: T): (r: T) {\n    require first: q[0] = d\n    out r := d\n    ensure same: r = q[0]\n}\n" ++
    "pub fn ge_head<T>(q: Seq<T>): (r: T) {\n    ensure m: r = q[0]\n}\n" ++
    "pub fn ge_len<T>(q: Seq<T>): Int := q.len\n" ++
    "pub fn ge_all?<T>(q: Seq<T>, s: Set<T>) := forall (x: T), when x in q, x in s\n" ++
    "pub fn ge_nest<T>(s: Set<Set<T>>, x: T): Set<Set<T>> := s union {{x}}\n" ++
    "pub fn ge_sets?<T>(q: Seq<Set<T>>, s: Set<T>) := q = [s]\n" ++
    "pub fn ge_deep<T>(q: Seq<Seq<T>>, d: T): T := if q = [] then d else q[0][0]\n" ++
    "pub fn ge_deep2<T>(d: T, q: Seq<Seq<T>>): T := if q = [] then d else q[0][0]\n" ++
    "pub fn ge_opt<T>(s: Set<T>): Option<Set<T>> := if s = {} then Option::None else Option::Some(s)\n" ++
    "pub fn ge_put<T>(q: Seq<Option<T>>, x: T): Seq<Option<T>> := q.update(0, Option::Some(x))\n" ++
    "pub fn ge_pair<A, B>(a: A, b: B): Rel<A, B> := {(a, b)}\n" ++
    "pub fn ge_in?<A, B>(r: Rel<A, B>, a: A, b: B) := (a, b) in r\n" ++
    "pub fn ge_parts<T>(s: Set<T>, t: Set<T>): Int := (s inter t).card + (s minus t).card\n"
  -- A contract over a set of the parameter, which holds or fails.
  let post ← pick #["not x in r", "r subset s", "r = s", "r.card < s.card"]
  out := out ++ s!"pub fn ge_drop<T>(s: Set<T>, x: T): (r: Set<T>) \{\n    out r := s minus \{x}\n    ensure q: {post}\n}\n"
  if ← chance 50 then
    out := out ++ "pub fn ge_choose<T>(s: Set<T>): (r: T) {\n    require ne: s != {}\n    ensure m: r in s\n}\n"
  -- The element type, and two of its values, distinct where it has two.
  let tys := #[("Int", "1", "2"), ("Bool", "true", "false"), ("String", "\"a\"", "\"b\""), ("Atom", "", ""),
    ("Option<Int>", "Option::None", "Option::Some(0)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0", "E::V1")] else #[])
  let (ty, a, b) ← pick tys
  -- Enumerated now and then, at a finite element type: then its inputs are
  -- only of that type, and the function without a body, whose
  -- postcondition blocks enumeration, is not applied.
  let enumerated := (ty == "Bool" || ty == "E") && (← chance 50)
  -- Its variables, named with `?` if they are `Bool`s.
  let x := if ty == "Bool" then "x?" else "x"
  let y := if ty == "Bool" then "y?" else "y"
  let lit (v : String) : R String := do if v.isEmpty then pure x else pick #[v, x, y]
  let n := if enumerated then "0" else "n"
  -- A value to compare with: not `q[0]` of a `Seq<String>`, which with an
  -- application is a comparison of two strings neither of which is a
  -- variable, outside the decidable core.
  let other : R String := if ty == "String" then pure x else pick #[x, "q[0]"]
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 19 with
      | 0 => pure s!"{x} in ge_grow(s, {x})"
      | 1 => pure s!"ge_has?(ge_grow(s, {← lit a}), {← lit b})"
      | 2 => pure s!"ge_first(q, {y}) = {← pick #[x, y]}"
      | 3 => pure s!"ge_all?(q, ge_grow(s, {← lit a}))"
      | 4 => pure s!"\{{x}} in ge_nest(\{s}, {← lit b})"
      | 5 => pure s!"(ge_opt(s) = Option::None) iff s = \{}"
      | 6 => pure s!"ge_put([Option::None], {x}) = [Option::Some({← lit a})]"
      | 7 => pure s!"ge_in?(ge_pair({x}, {← pick #["0", n]}), {← lit b}, {n})"
      | 8 => pure s!"ge_parts(s, \{{x}}) {← pick #["=", ">=", "<"]} s.card"
      | 9 => pure s!"not {x} in ge_drop(s, {← lit b})"
      | 10 => pure s!"ge_twice(s, {← lit a}) = ge_grow(s, {← lit b})"
      | 11 => pure s!"ge_len({← pick #["q", s!"[{x}]", s!"[{x}, {y}]"]}) > 1"
      | 12 =>
        -- Not both empty, which would leave `T` unknown (`F0400`).
        let q ← pick #["[s]", s!"[\{{x}}]", "[{}]"]
        pure s!"ge_sets?({q}, {← pick (if q == "[{}]" then #["s"] else #["s", "{}"])})"
      | 13 =>
        let q ← pick #["[[]]", s!"[[{x}]]", "[]", "[q]"]
        let call ← pick #[s!"ge_deep({q}, {y})", s!"ge_deep2({y}, {q})"]
        pure s!"{call} = {← if ← chance 33 then other else pick #[x, y]}"
      -- An instance whose type argument only what is expected gives.
      | 14 => pure s!"{← other} {← pick #["=", "!="]} ge_at([])"
      -- A generic function with a function parameter, given a closure or,
      -- at a type with a literal, a named function (`ge_is?`).
      | 15 =>
        let v := if ty == "Bool" then "v?" else "v"
        let f ← if a.isEmpty || (← chance 50) then pure s!"|{v}| {v} = {y}" else pure "ge_is?"
        pure s!"ge_apply?({← pick #["q", s!"[{x}]"]}, {f})"
      -- A precondition and a postcondition over an element of a `Seq<T>`,
      -- read at the instance, the function without a body's only where the
      -- procedure is not enumerated, as its postcondition blocks it.
      | 16 => pure s!"ge_pick({← pick #["q", s!"[{x}]", "[]"]}, {← pick #[y, "q[0]"]}) = {← other}"
      | 17 =>
        if enumerated then pure s!"{x} in ge_grow(s, {x})"
        else pure s!"ge_head({← pick #["q", s!"[{x}]"]}) {← pick #["=", "!="]} {← other}"
      | _ => pure s!"ge_first([{← lit a}], {y}) = {← lit b}"
    let e := if ← chance 30 then s!"when {x} != {y}, {e}" else e
    body := body ++ s!"    expect ge{k}: {e}\n"
  if out.contains "ge_choose" && !enumerated then
    body := body ++ s!"    expect gc: when ks != \{}, ge_choose(ks) in ks\n"
  let xs := if ty == "Bool" then s!"{x}, {y}" else s!"{x}: {ty}, {y}: {ty}"
  if body.contains "ge_is?" then
    out := out ++ (if ty == "Bool" then s!"pub fn ge_is?(v?) := v? = {a}\n" else s!"pub fn ge_is?(v: {ty}) := v = {a}\n")
  if enumerated then
    return out ++ "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc ge_apps({xs}, s: Set<{ty}>, q: Seq<{ty}>) \{\n{body}}\n"
  return out ++ s!"pub proc ge_apps({xs}, s: Set<{ty}>, q: Seq<{ty}>, n: Int, ks: Set<Int>) \{\n{body}}\n"

/-- Pattern tests that match every value of their scrutinee's type, or
bind a name that what follows reads: `_`, alternatives that cover an
enumeration, a variant of an enumeration of one variant, a binder, and
payload binders of one-variant enumerations, nested or not, each where
the binding is visible, so that none is an error (`F0334`). Both front
ends decide `irrefutable_is` and `is_equality` on them with
`Core.irrefutableIsAt` (`lint::irrefutable_is`). -/
def patternTests : R String := do
  let decls := "pub enum Zt { A, B(Int), C(Bool) }\npub enum Zo { Only }\npub enum Zw { W(Int) }\n" ++
    "pub enum Zn { N(Zw) }\npub enum Zq { Q(Int, Bool) }\n"
  let forms : Array (String × String) := #[
    ("Bool", "t is _"),
    ("Bool", "t is Zt::A | Zt::B(_) | Zt::C(_)"),
    ("Bool", "t is Zt::C(true) | Zt::C(false) | Zt::A | Zt::B(_)"),
    ("Bool", "o is Zo::Only"),
    ("Bool", "not (o is _)"),
    ("Bool", "w is Zw::W(_)"),
    ("Int", "if n is zm then zm else 0"),
    ("Bool", "(when t is Zt::B(zy), zy > 0)"),
    ("Bool", "t is Zt::B(zy) and zy > 0"),
    ("Int", "if w is Zw::W(zx) then zx else 0"),
    ("Int", "if v is Zn::N(Zw::W(zz)) then zz else 0"),
    ("Bool", "q is Zq::Q(zk, zb?) and (zb? or zk > 0)"),
    ("Int", "if q is Zq::Q(_, zb?) then (if zb? then 1 else 0) else 2")
  ]
  let mut results := #[]
  let mut body := ""
  for (ty, e) in forms, k in [0:forms.size] do
    unless ← chance 60 do continue
    let name := if ty == "Bool" then s!"zr{k}?" else s!"zr{k}"
    results := results.push (if ty == "Bool" then name else s!"{name}: {ty}")
    body := body ++ (if ty == "Bool" then s!"    ensure zk{k}: {name} iff {e}\n" else s!"    ensure zk{k}: {name} = {e}\n")
  if results.isEmpty then return ""
  return decls ++ s!"pub proc zpt(t: Zt, o: Zo, w: Zw, v: Zn, q: Zq, n: Int): ({", ".intercalate results.toList}) \{\n{body}}\n"

/-- Private procedures that only claim (`lint::proc_without_outputs`), and
functions whose contract clauses mention their own names, another
function's, a constant's, or nothing (`lint::contract_mentions_nothing`).

Each procedure has members of every kind that a global expectation's block
accepts, and now and then one that it does not: a result, a guarantee, an
`exists` or a `det` `let`. A later call, refinement or claim names some of
them. No member has an evidence setting: only `fren check` runs random
testing, so the two front ends would report such a member's checks
differently. -/
def claimProcs : R String := do
  -- The lint is allowed by default, so warn of it from here on.
  let mut out := "set_option fren.lint.proc_without_outputs \"warn\"\npub const ZK: Int := 3\npub fn zg(Int): Int\npub proc zb(x: Int): (y?) { ensure r: y? iff x > ZK }\n"
  let mut procs : Array (String × Nat × Bool) := #[]
  for k in [0:(← below 3) + 1] do
    let nIn ← below 3
    let ins := (List.range nIn).map (s!"zx{·}")
    let int (d : Nat) : R String := do
      let a ← if ins.isEmpty || (← chance 30) then pure (toString (← below 5)) else pick ins.toArray
      if d > 0 && (← chance 40) then return s!"{a} + {← below 3}"
      return a
    let mut body := ""
    let mut results := ""
    if !ins.isEmpty && (← chance 40) then body := body ++ s!"    require za: {← int 1} >= 0\n"
    let hasLet ← chance 40
    if hasLet then body := body ++ s!"    {if ← chance 15 then "det " else ""}let zl: Int := {← int 1}\n"
    let hasCall ← chance 40
    if hasCall then body := body ++ s!"    call zw := zb({← int 1})\n"
    -- A refinement cannot name a procedure with an `exists`.
    let kind ← below 8
    match kind with
    | 0 =>
      results := s!": (zo: Int)"
      body := body ++ s!"    out zo := {← int 1}\n"
    | 1 => body := body ++ s!"    ensure zq: {← int 1} > zg({← int 0})\n"
    | 2 => body := body ++ "    exists zv?\n    expect zu: zv? or not zv?\n"
    | _ => pure ()
    let atom : R String := do
      match ← below 4 with
      | 0 => if hasLet then return s!"zl > {← int 0}" else return s!"{← int 1} > 0"
      | 1 => if hasCall then return "zw.y?" else return s!"{← int 0} < ZK"
      | 2 => return s!"zg({← int 0}) >= {← int 1}"
      | _ => return s!"{← int 1} != {← int 0}"
    -- No evidence setting: only `fren check` tests an expectation set to
    -- random testing, so the front ends would differ in its result. The ui
    -- test `lints/procedures.fren` has one.
    body := body ++ s!"    expect ze: {← atom} or {← atom}\n"
    if ← chance 40 then body := body ++ s!"    cover zc: {← atom}\n"
    let params := ", ".intercalate (ins.map (s!"{·}: Int"))
    out := out ++ s!"proc zp{k}({params}){results} \{\n{body}}\n"
    procs := procs.push (s!"zp{k}", nIn, kind != 2)
  -- A later item that names one of them, now and then.
  if ← chance 50 then
    let (p, nIn, refinable) ← pick procs
    let args := ", ".intercalate ((List.range nIn).map fun _ => "zy")
    match ← below 3 with
    | 0 => out := out ++ s!"pub proc zcaller(zy: Int): (zr: Int) \{\n    call zc := {p}({args})\n    out zr := zy\n}\n"
    | 1 => if refinable then out := out ++ s!"expect zrefines(zy: Int) \{\n    call zc := {p}({args})\n    refines zc {p}({args})\n}\n"
    | _ => out := out ++ s!"trusted {p}: \"a claim\"\n"
  -- Contract clauses, each mentioning its own, another's, or nothing.
  for k in [0:(← below 2) + 1] do
    let clause : R String := do
      match ← below 7 with
      | 0 => return "zn > 0"
      | 1 => return "zr >= zn"
      | 2 => return s!"zg({← below 3}) > 0"
      | 3 => return "ZK > 0"
      | 4 => return "zh > ZK"
      | 5 => return s!"zf{k}(zn) = zr"
      | _ => return "true"
    let pre ← clause
    let pre := if pre.startsWith "zr" || pre.startsWith s!"zf{k}" then "zn > ZK" else pre
    out := out ++ s!"pub fn zf{k}(zn: Int): (zr: Int) \{\n    let zh: Int := zg(1)\n    require zpre: {pre}\n" ++
      s!"    ensure zpost: {← clause}\n}\n"
  -- Drawn after the above, so that a spec the group wrote before keeps it:
  -- clauses that read a field of a parameter, of a sequence or a record,
  -- that mention only the value, that are a labelled conjunction, or a
  -- quantifier over another function; and a higher-order function's
  -- precondition, which reads or applies its function parameter. A
  -- procedure's `out` member always defines a result, which the block
  -- rejects anyway, so the results above stand for it.
  out := out ++ "pub struct Zs { za: Int }\n"
  let fieldClause (post : Bool) : R String := do
    match ← below (if post then 7 else 5) with
    | 0 => return "zq.len > 1"
    | 1 => return "zs.za > ZK"
    | 2 => return s!"zg({← below 3}) > zs.za"
    | 3 => return "and { zl1: zq.len > 1, zl2: zg(0) > 0 }"
    | 4 => return "forall (zb?: Bool), zg(if zb? then 1 else 0) > 0"
    | 5 => return "zr > 0"
    | _ => return "and { zl1: zr > ZK, zl2: zg(1) > 0 }"
  out := out ++ s!"pub fn zfs(zq: Seq<Int>, zs: Zs): (zr: Int) \{\n    require zpre: {← fieldClause false}\n" ++
    s!"    ensure zpost: {← fieldClause true}\n}\n"
  let hoClause ← pick #["zk(0) > ZK", "zk(zn) >= zn", "zn > 0", "zg(0) > 0", "and { zl1: zk(1) > 0, zl2: zg(1) > 0 }"]
  out := out ++ s!"pub fn zho(zk: fn(Int) -> Int, zn: Int): (zr: Int) \{\n    require zpre: {hoClause}\n    out zr := zk(zn)\n}\n"
  -- Drawn after the above too: procedures whose members are unlabelled
  -- Boolean blocks, of each kind, which are members of their keywords'
  -- kinds, so that a guarantee among them keeps the lint quiet.
  for k in [0:(← below 2) + 1] do
    let mut body := ""
    if ← chance 50 then body := body ++ "    require and { zua: zx > 0, zub: zx < 9 }\n"
    if ← chance 30 then body := body ++ "    ensure and { zuc: zx + 1 > zx, zud: zx - 1 < zx }\n"
    body := body ++ s!"    expect and \{ zue: zx >= {← below 3}, zuf: zg(zx) != zx }\n"
    out := out ++ s!"proc zu{k}(zx: Int) \{\n{body}}\n"
  -- And last, a clause about two other functions, whose note lists both,
  -- in an order that both front ends must agree on.
  if ← chance 60 then
    let two ← pick #["zg(0) > zg2(1)", "zg2(0) > 0 or zg(1) > ZK", "zg2(zg(0)) > 0"]
    out := out ++ s!"pub fn zg2(Int): Int\npub fn zf2(zn: Int): (zr: Int) \{\n    ensure zgrows: zr >= zn\n" ++
      s!"    ensure ztwo: {two}\n}\n"
  return out

/-- A goal with leading binders (`cli::goal_introduction`), whose terms
mention `outer`, its body the first of them: one to three heads, each a universal quantifier over one
or two bound names, of an infinite type, `Nat`, an abstract type, or a
listed type, or a premise, in any order, then a body, and now and then a
guard within the last quantifier. -/
def goalWithHeads (outer : Array String) (tys : Array String := #["Int", "Nat", "Zgt", "Zgt", "Zge", "Bool"]) :
    R String := do
  let mut bound : Array (String × String) := #[]
  let mut heads : Array String := #[]
  -- An `Int` term of one of the names in scope.
  let intOf (scope : Array (String × String)) : R String := do
    if scope.isEmpty || (← chance 20) then return ← pick (outer.push "1")
    let (x, t) ← pick scope
    return match t with
      | "Zgt" => s!"zgw({x})"
      | "Self" => s!"zgo({x})"
      | "Zge" => s!"(if {x} = Zge::A then 1 else 0)"
      | "Bool" => s!"(if {x} then 1 else 0)"
      | _ => x
  let cond (scope : Array (String × String)) : R String := do
    match ← below 3 with
    | 0 =>
      match scope.find? (·.2 == "Zgt") with
      | some (x, _) => return s!"zgh?({x})"
      | none => match scope.find? (·.2 == "Self") with
        | some (x, _) => return s!"zgo({x}) > 0"
        | none => return s!"{← intOf scope} > 0"
    | 1 => return s!"{← intOf scope} {← pick #["<", "<=", "="]} {← intOf scope}"
    | _ => return s!"{← intOf scope} >= {← below 3}"
  for _ in [0:(← below 3) + 1] do
    if ← chance 60 then
      let mut names := #[]
      for _ in [0:(← below 2) + 1] do
        let t ← pick tys
        let x := if t == "Bool" then s!"zb{bound.size}?" else s!"zx{bound.size}"
        bound := bound.push (x, t)
        names := names.push s!"({x}: {t})"
      heads := heads.push s!"forall {" ".intercalate names.toList}, "
    else heads := heads.push s!"when {← cond bound}, "
  let guard ← if ← chance 30 then pure s!"when {← cond bound}, " else pure ""
  -- The right operand is the first of `outer`, if any, so that the
  -- goal mentions it, and an assumption over it is used (F0792).
  let rhs ← match outer[0]? with
    | some o => pure o
    | none => intOf bound
  let body := s!"{guard}{← intOf bound} {← pick #["<", "<=", ">=", "!="]} {rhs} + {← below 3}"
  -- Each head wraps the rest; a quantifier after a premise in parentheses.
  return heads.foldr (init := body) fun h rest =>
    if h.startsWith "when" && rest.startsWith "forall" then s!"{h}({rest})" else h ++ rest

/-- Goals with leading binders (`goalWithHeads`), as each item poses
them: a global expectation of each form, one with a quantified assumption
that only instances at the goal's bound names decide, as a trait's laws
are, a procedure with a defined output, which the binary's goal binds
with a `let`, a `let` and a `where` in front of a goal, and a trait's
expectations over `Self` under its laws (`Reqs/Cli#goal-introduction`). -/
def goalHeads : R String := do
  let mut out := "pub type Zgt\npub enum Zge { A, B }\npub fn zgw(Zgt): Int\npub fn zgh?(Zgt)\n"
  let undecidable := "set_option fren.lint.undecidable \"allow\" in\n"
  for k in [0:← below 2] do
    out := out ++ s!"\n{undecidable}expect zgs{k}: {← goalWithHeads #[]}\n"
  if ← chance 70 then
    let law ← pick #["zgw(zy) >= n", "zgw(zy) = n", "when zgh?(zy), zgw(zy) > n", "zgh?(zy)"]
    out := out ++ s!"\n{undecidable}expect zgl(n: Int) \{\n    assume a: forall (zy: Zgt), {law}\n" ++
      s!"    expect c: {← goalWithHeads #["n"]}\n}\n"
  if ← chance 70 then
    let mut body := "    out zd := n + 1\n"
    for k in [0:(← below 2) + 1] do
      body := body ++ s!"    expect c{k}: {← goalWithHeads #["n", "zd"]}\n"
    out := out ++ s!"\n{undecidable}pub proc zgp(n: Int): (zd: Int) \{\n{body}}\n"
  -- Drawn after the items above, so that they are as they were: a `let`
  -- or `where` in front of a goal, and a trait whose expectations
  -- quantify over `Self` under its laws, two of which may contradict each
  -- other, as at #543.
  if ← chance 60 then
    let goal ← goalWithHeads #["zl", "n"]
    let d ← below 3
    let e := if ← chance 50 then s!"let zl := n + {d} in {goal}" else s!"{goal} where zl := n + {d}"
    out := out ++ s!"\n{undecidable}pub proc zgq(n: Int) \{\n    expect c: {e}\n}\n"
  if ← chance 60 then
    let mut body := "    fn zgo(Self): Int\n"
    body := body ++ s!"    law zl0(s: Self): zgo(s) {← pick #["=", ">=", "<="]} {← below 4}\n"
    if ← chance 50 then body := body ++ s!"    law zl1(s: Self): zgo(s) = {← below 4}\n"
    for k in [0:(← below 2) + 1] do
      body := body ++ s!"    expect ze{k}: {← goalWithHeads #[] #["Self", "Self", "Int", "Nat"]}\n"
    out := out ++ s!"\n{undecidable}pub trait Zgr \{\n{body}}\n"
  return out

/-- The bound names of a quantifier of `primedNames`, from position `k`:
one or two, each with its position and type, `zi` or `zj` at position 0
and the other at 1, as a list of binders and as written. -/
def primedBinders (tys : Array String) (first : String) (k : Nat) : R (Array (String × Nat × String)) := do
  let other := if first == "zi" then "zj" else "zi"
  let names := if k == 0 then #[first, other] else #[other]
  let n := if names.size == 2 && (← chance 50) then 2 else 1
  return (names.extract 0 n).mapIdx fun i x => (x, k + i, tys[k + i]!)

/-- A comparison of the bound name `x`, of type `t`, with a variable of
`primedNames` of a type it compares with, or another bound name of
`bound`, or a literal. -/
def primedAtom (tys : Array String) (bound : Array (String × Nat × String)) (x : String) (t : String) : R String := do
  let numeric (u : String) := u != "String"
  let fits (u : String) := if t == "String" then u == "String" else numeric u
  let vars := (#["zi", "zj"].flatMap fun n => #[0, 1].map fun k => (s!"{n}'{k}", tys[k]!)).filter (fits ·.2)
  let others := (bound.filter fun (y, _, u) => y != x && fits u).map (·.1)
  let rhs ← match ← below 4 with
    | 0 | 1 => pure (← pick vars).1
    | 2 => if others.isEmpty then pure (← pick vars).1 else pick others
    | _ => if t == "String" then pure "\"a\"" else do pure (toString (← below 3))
  let op ← if t == "String" then pick #["=", "!="] else pick #["=", "!=", "<", ">=", ">"]
  return s!"{x} {op} {rhs}"

/-- A quantifier of `primedNames` from position `k`, over bound names
whose symbols were those of its variables: one or two bound names, under
`forall` or `exists`, with or without a guard, and a quantifier within it
at the next position, now and then. -/
partial def primedQuant (tys : Array String) (first : String) (k : Nat) (outer : Array (String × Nat × String)) :
    R String := do
  let bs ← primedBinders tys first k
  let all ← chance 50
  let bound := outer ++ bs
  let binders := " ".intercalate (bs.toList.map fun (x, _, t) => s!"({x}: {t})")
  let atom : R String := do
    let (x, _, t) ← pick bound
    primedAtom tys bound x t
  let inner ← if bs.size == 1 && k == 0 && (← chance 40) then primedQuant tys first 1 bound else atom
  let body ← if ← chance 50 then pure s!"{← atom} {← pick #["and", "or"]} ({inner})" else pure inner
  let guard ← if all && (← chance 50) then pure s!"when {← atom}, " else pure ""
  return s!"{if all then "forall" else "exists"} {binders}, {guard}{body}"

/-- Variables named as the symbols of bound names and of second copies
were, `x'k` and `x'`, beside quantifiers whose bound names are `x` at
position `k`, of each type that is not listed, in expectations,
guarantees and a defined output, and a `det` output beside a variable
named as its copy was; and an enumerated procedure, whose variable `zm'`
was read as the copy of its `zm` (`cli::query_symbols`). -/
def primedNames : R String := do
  let tys ← #[0, 1].mapM fun _ => pick #["Int", "Nat", "String"]
  let first ← pick #["zi", "zj"]
  let params := ", ".intercalate ((#["zi", "zj"].flatMap fun n => #[0, 1].map fun k => s!"{n}'{k}: {tys[k]!}").toList)
  let mut body := ""
  for k in [0:(← below 3) + 1] do
    body := body ++ s!"    expect zpe{k}: {← primedQuant tys first 0 #[]}\n"
  if ← chance 50 then body := body ++ s!"    ensure zpq: {← primedQuant tys first 0 #[]}\n"
  let mut results := #[]
  if ← chance 50 then
    results := results.push "zd?"
    body := body ++ s!"    out zd? := {← primedQuant tys first 0 #[]}\n"
  if ← chance 60 then
    results := results ++ #["det zy: Int", "zy': Int"]
    let num := (#["zi'0", "zi'1", "zj'0", "zj'1"].zip (tys ++ tys)).filterMap fun (v, t) => if t != "String" then some v else none
    let e ← if num.isEmpty then do pure (toString (← below 3)) else pick num
    body := body ++ (← pick #[s!"    ensure zya: zy = zy' + {e}\n",
      s!"    ensure zya: zy' = {e}\n    ensure zyb: zy = zy'\n", s!"    ensure zya: zy = {e}\n"])
  let resultList := if results.isEmpty then "" else s!": ({", ".intercalate results.toList})"
  let mut out := s!"set_option fren.lint.undecidable \"allow\" in\npub proc zpn({params}){resultList} \{\n{body}}\n"
  if ← chance 50 then
    let rel ← pick #["zm' = Zpe::A", "zm' != Zpe::B", "zm = Zpf::C"]
    let exp ← pick #["when zo?, zm' = Zpe::A", "when zo?, zm' = Zpe::B", "zo? or zm = Zpf::D"]
    out := out ++ "\npub enum Zpe { A, B }\npub enum Zpf { C, D, F }\n\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc zpk(zm': Zpe, zm: Zpf): (det zo?) \{\n    ensure r: zo? iff {rel}\n    expect e: {exp}\n}\n"
  return out

/-- Generic structural recursions (`Reqs/Lang/Recursion#generic-recursion`):
over a generic list and a tree with two type parameters, with an `Int`, a
`Nat`, a `Bool` and a `Set<T>` result, with a contract that holds by
induction or fails, nested (one applying another at its own type parameter
and at a list of it), applied in a closure given to a generic higher-order
function and in a generic function that is not recursive, and a procedure
that applies them at two instances, of `Int`, `Bool`, `String`, `E` if the
spec has it, or `Option<Int>`, at constant arguments too. Now and then, at
`Bool` or `E`, the procedure is enumerated, with one list of that type as
its only input. A check may fail or be inconclusive, but nothing here is a
static error. -/
def genericRecursion (sc : WScope) : R String := do
  let post ← pick #["r >= 0", "r >= 1", "r = gr_len(l)", "r <= gr_len(l)"]
  let mut out := "pub enum Gl<T> { Nil, Cons(T, Gl<T>) }\n" ++
    "pub enum Gt<A, B> { Leaf(A), Node(B, Gt<A, B>, Gt<A, B>) }\n" ++
    "pub fn gr_len<T>(l: Gl<T>): Int := match l { Gl::Nil => 0, Gl::Cons(_, r) => 1 + gr_len(r) }\n" ++
    "pub fn gr_nlen<T>(l: Gl<T>): Nat := match l { Gl::Nil => 0, Gl::Cons(_, r) => 1 + gr_nlen(r) }\n" ++
    "pub fn gr_has?<T>(l: Gl<T>, x: T) := match l { Gl::Nil => false, Gl::Cons(y, r) => y = x or gr_has?(r, x) }\n" ++
    "pub fn gr_elems<T>(l: Gl<T>): Set<T> := match l { Gl::Nil => {}, Gl::Cons(y, r) => {y} union gr_elems(r) }\n" ++
    "pub fn gr_count<T>(l: Gl<T>): (r: Int) {\n    out r := match l { Gl::Nil => 0, Gl::Cons(_, t) => 1 + gr_count(t) }\n" ++
    s!"    ensure e: {post}\n}\n" ++
    "pub fn gr_total<T>(ls: Gl<Gl<T>>): Int := match ls { Gl::Nil => 0, Gl::Cons(l, r) => gr_len(l) + gr_total(r) }\n" ++
    "pub fn gr_size<A, B>(t: Gt<A, B>): (r: Int) {\n" ++
    "    out r := match t { Gt::Leaf(_) => 1, Gt::Node(_, a, b) => 1 + gr_size(a) + gr_size(b) }\n    ensure pos: r >= 1\n}\n" ++
    "pub fn gr_leaves<A, B>(t: Gt<A, B>): Set<A> := match t {\n" ++
    "    Gt::Leaf(x) => {x},\n    Gt::Node(_, a, b) => gr_leaves(a) union gr_leaves(b),\n}\n" ++
    "pub fn gr_holds?<T>(l: Gl<T>, p: fn(Gl<T>) -> Bool) := p(l)\n" ++
    "pub fn gr_nonempty?<T>(l: Gl<T>) := gr_len(l) > 0\n"
  let tys := #[("Int", "1", "2"), ("Bool", "true", "false"), ("String", "\"a\"", "\"b\""),
    ("Option<Int>", "Option::Some(1)", "Option::Some(0)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0", "E::V1")] else #[])
  let (ty, a, b) ← pick tys
  let (ty2, _, _) ← pick tys
  let enumerated := (ty == "Bool" || ty == "E") && (← chance 40)
  let cons (v : String) (l : String) := s!"Gl::Cons({v}, {l})"
  let lst : R String := do
    if enumerated then pick #["l", cons a "l", cons a "Gl::Nil"]
    else pick #["l", "m", cons a "l", cons b (cons a "Gl::Nil"), cons b "Gl::Nil"]
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 14 with
      | 0 => pure s!"gr_len({← lst}) >= 0"
      | 1 => pure s!"when l is Gl::Cons(_, r), gr_len(l) = 1 + gr_len(r)"
      | 2 => pure s!"gr_nlen({← lst}) {← pick #[">=", "<", "="]} {← below 3}"
      | 3 => pure s!"gr_has?({cons a "l"}, {a})"
      | 4 => pure s!"gr_has?({← lst}, {b}) {← pick #["iff", "or"]} {b} in gr_elems({← lst})"
      | 5 => pure s!"gr_count({← lst}) {← pick #[">=", ">", "="]} {← pick #["0", "gr_len(l)"]}"
      -- The same list on both sides: a check that holds, whatever model
      -- the solver gives where it needs more than one step (#634).
      | 6 =>
        let x ← lst
        pure s!"gr_total({cons x "Gl::Nil"}) = gr_len({x})"
      | 7 => pure s!"gr_holds?({← lst}, |z| gr_len(z) >= {← below 2})"
      | 8 => pure s!"when l is Gl::Cons(_, _), gr_nonempty?(l)"
      | 9 => pure s!"gr_len({cons a "Gl::Nil"}) = 1 or l = Gl::Nil"
      | 10 =>
        if enumerated then pure s!"gr_elems(l) subset gr_elems({cons a "l"})"
        else pure s!"gr_size(t) >= {← pick #["1", "2"]}"
      | 11 =>
        if enumerated then pure s!"gr_len(l) = gr_count(l)"
        else
          let x := if ty == "Bool" then "x?" else "x"
          pure s!"when t is Gt::Leaf({x}), gr_leaves(t) = \{{x}}"
      | 12 =>
        if enumerated then pure s!"not gr_has?(Gl::Nil, {a})"
        else pure s!"gr_len(w) >= 0 and gr_count(w) {← pick #[">=", "<"]} 0"
      | _ => pure s!"gr_elems({← lst}) = gr_elems({← lst})"
    body := body ++ s!"    expect gr{k}: {e}\n"
  -- Every input mentioned, so that none is unused.
  body := body ++ (if enumerated then "    expect grm: gr_len(l) >= 0\n"
    else "    expect grm: gr_len(l) + gr_len(m) + gr_len(w) >= 0 and gr_size(t) >= 1\n")
  if enumerated then
    return out ++ "set_option fren.enumeration.size 3 in\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc gr_apps(l: Gl<{ty}>) \{\n{body}}\n"
  return out ++ s!"pub proc gr_apps(l: Gl<{ty}>, m: Gl<{ty}>, t: Gt<{ty}, {ty2}>, w: Gl<{ty2}>) \{\n{body}}\n"

/-- A spec for `--keywords`: one block, a procedure's, a function's, a
trait method's or a global expectation's, with one clause written with the
other block's keyword (`assume` in a procedure's or a function's, `require`
in a global expectation's), alone or among parts that the block rejects,
before or after it: a modifier or a second result of a function's, an
`out` of another name or of the result again, `refines`, a claim, a call
or an `exists` in a function's block, a dotted name, a foreign operator,
or a clause without a label that is not a Boolean block; or, no error, one
that is, with a `where` or under a `let`.
No part is an error of Lean's grammar, which Lean would report instead
of any error of the block's: a `det` claim, or an evidence setting before
the `}`. Its static errors are on purpose, so it is a mode of its own, which
`lake test`'s corpus does not check; both front ends must report the same
first error of the block (`lang::block_errors`). `genKeywordsItem` now
and then writes an item of another kind before it, `genKeywordsGrammar`
puts an error of Lean's grammar in its item, and `genKeywordsTail` writes
the item after it. -/
def genKeywords : R String := do
  let block ← below 4
  let global := block == 3
  let wrong := if global then "require" else "assume"
  let clause ← match ← below 5 with
    | 0 => pure s!"{wrong} a: x > 0"
    | 1 => pure s!"{wrong} a: x > k where k := 1"
    | 2 => pure s!"{wrong} a: and \{ b: x > 0, c: x < 9 }"
    | 3 => pure s!"{wrong} and \{ b: x > 0 }"
    | _ => pure s!"{wrong} when x > 0, and \{ b: x < 9 }"
  -- Parts that the block rejects, or that are errors of their own syntax.
  let fnParts := #["out s := x", "out r := x\nout r := x", "refines c spec(x)", "expect e: x > 0",
    "cover g: x > 0", "call w := cb(x)", "exists z: Int", "det let z: Int := x", "ensure q: r == 1",
    "set_option fren.evidence \"random\" in", "let d.e: Int := x"]
  let procParts := #["out z := x", "ensure q: y == 1", "let d.e: Int := x",
    "set_option fren.evidence \"random\" in", "set_option fren.foo \"x\" in"]
  let globalParts := #["ensure q: x > 0", "out y := x", "expect q: x == 1", "let d.e: Int := x",
    "set_option fren.evidence \"random\" in"]
  let pool := if block == 3 then globalParts else if block == 0 then procParts else fnParts
  let mut before := #[]
  for _ in [0:← below 3] do before := before.push (← pick pool)
  -- After the clause, no evidence setting, which Lean's grammar would
  -- reject before the `}` and so before any check of the block.
  let mut after := #[]
  for _ in [0:← below 2] do
    let part ← pick pool
    unless part.startsWith "set_option" do after := after.push part
  -- A function's results: one, or with a modifier, a second, or a dotted
  -- name, the first's own error.
  let result ← match ← below 6 with
    | 0 => pure "det r: Int"
    | 1 => pure "r: Int, s: Int"
    | 2 => pure "r.a: Int, s: Int"
    | 3 => pure "set_option fren.evidence \"random\" in r: Int"
    | _ => pure "r: Int"
  -- Drawn after every other draw, so that a spec that has none is the one
  -- that the seed gave before: now and then, a clause without a label that
  -- is not a Boolean block, an error of its own syntax
  -- (`lang::clause_errors`), somewhere before the clause, with the block's
  -- keyword or the other's, under a leading `when` or with a `where`; or
  -- one that is a Boolean block with a `where` or under a `let`, no error.
  if ← chance 50 then
    let bareParts := if global then #["expect x > 0", "assume x > 0", "require x > 0", "ensure x > 0",
        "expect when x > 0, x < 9", "assume x > k where k := 1", "assume and { u: x > k } where k := 1"]
      else if block == 0 then #["ensure y = x", "require x > 0", "assume x > 0", "expect when x > 0, y = x",
        "ensure y = k where k := x", "require let m := 1 in and { u: x > m }"]
      else #["require x > 0", "assume x > 0", "ensure r = x", "require when x > 0, x < 9", "expect x > 0",
        "require and { u: x > k } where k := 1"]
    let bare ← pick bareParts
    let at_ ← below (before.size + 1)
    before := before.insertIdxIfInBounds at_ bare
  let members := before ++ #[clause] ++ after
  -- Each line of each member, at the indentation `ind`.
  let bodyAt (ind : String) := String.join (members.toList.flatMap fun m =>
    (m.splitOn "\n").map (ind ++ · ++ "\n"))
  let body := bodyAt "    "
  let decls := "pub proc cb(x: Int): (v: Int) { ensure e: v = x }\n" ++
    "pub proc spec(x: Int): (v: Int) { ensure e: v = x }\n"
  return decls ++ match block with
    | 0 => s!"\npub proc kw(x: Int): (y: Int) \{\n{body}    ensure r: y = x\n}\n"
    | 1 => s!"\npub fn kw(x: Int): ({result}) \{\n{body}}\n"
    | 2 => s!"\npub trait KwTrait \{\n    fn kw(s: Self, x: Int): ({result}) \{\n{bodyAt "        "}    }\n}\n"
    | _ => s!"\nexpect kw(x: Int) \{\n    call c := cb(x)\n{body}    expect z: c.v = x\n}\n"

/-- The item after `genKeywords`' block (`--keywords`), with messages of
its own, which neither front end may lose to the block's keyword error
(`lang::item_error`): now and then, a procedure with a name that
nothing declares (`F0201`), one with an unused parameter, one whose
expectation fails (`F0603`), or an application that may not meet a
function's precondition (`F0629`). It is drawn from a generator of its own
(`Mode.spec`), so that the block before it is the one that the seed gave
before. -/
def genKeywordsTail (block : String) : R String := do
  if !(← chance 75) then return ""
  -- An item that names the block's own, a procedure's or a function's,
  -- which its keyword error breaks.
  let names := if (block.splitOn "\npub proc kw(").length > 1 then
      #["\nproc kw_after(x: Int): (y: Int) {\n    call c := kw(x)\n    ensure r: y = c.y\n}\n"]
    else if (block.splitOn "\npub fn kw(").length > 1 then
      #["\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = kw(x)\n}\n"]
    else #[]
  pick (#["\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = x + missing\n}\n",
    "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = 1\n}\n",
    "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = x\n    expect e: y > 0\n}\n",
    "\nfn kw_pre(x: Int): (r: Int) {\n    require p: x > 0\n    out r := x\n}\n" ++
      "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = kw_pre(x)\n}\n"] ++ names)

/-- An item of each kind that can hold clauses, with a clause written with
the other block's keyword in one of its members (`--keywords`,
`lang::item_error`): a procedure, a function, a global expectation, a
trait's method, procedure or expectation (a procedure being a member that
the trait does not take), a trait inside a trait, and a procedure under a
`set_option ... in`. The clause is labelled, a Boolean block without a
label, or under a leading `when`. It is drawn from a generator of its own
(`Mode.spec`), and goes before `genKeywords`' block. -/
def genKeywordsItem : R String := do
  if !(← chance 60) then return ""
  let kind ← below 8
  let global := kind == 2 || kind == 5
  let wrong := if global then "require" else "assume"
  let form ← pick #[s!"{wrong} ka: x > 0", s!"{wrong} and \{ ka: x > 0 }", s!"{wrong} when x > 0, and \{ kb: x < 9 }"]
  -- Each line of the item's member, at the indentation `ind`.
  let at_ (ind : String) := ind ++ form ++ "\n"
  return match kind with
    | 0 => s!"\npub proc kx(x: Int): (y: Int) \{\n{at_ "    "}    ensure r: y = x\n}\n"
    | 1 => s!"\npub fn kx(x: Int): (r: Int) \{\n{at_ "    "}    out r := x\n}\n"
    | 2 => s!"\nexpect kx(x: Int) \{\n{at_ "    "}    expect e: x >= 0\n}\n"
    | 3 => s!"\npub trait KxTrait \{\n    fn kx(s: Self, x: Int): (r: Int) \{\n{at_ "        "}        out r := x\n    }\n}\n"
    | 4 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    proc kx(x: Int): (y: Int) \{\n{at_ "        "}" ++
        "        ensure r: y = x\n    }\n}\n"
    | 5 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    expect kx(s: Self, x: Int) \{\n{at_ "        "}" ++
        "        expect e: kc(s) = kc(s)\n    }\n}\n"
    | 6 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    trait KxInner \{\n        fn kx(s: Self, x: Int): (r: Int) \{\n" ++
        s!"{at_ "            "}            out r := x\n        }\n    }\n}\n"
    | _ => s!"\nset_option fren.lint.unused_variables \"allow\" in\npub proc kx(x: Int): (y: Int) \{\n{at_ "    "}" ++
        "    ensure r: y = x\n}\n"

/-- An error of Lean's grammar later in `genKeywords`' item (`--keywords`),
which both front ends must report instead of any error of a clause's
keyword (`lang::item_error`): now and then, a member on a line of its own
before the block's `}`, or a clause written with the other block's keyword
whose Boolean block spans lines, with the grammar error inside. It is
drawn from a generator of its own (`Mode.spec`). `block` is the spec that
`genKeywords` gave. -/
def genKeywordsGrammar (block : String) : R String := do
  if !(← chance 30) then return block
  let global := (block.splitOn "\nexpect kw(").length > 1
  let trait := block.endsWith "    }\n}\n"
  let ind := if trait then "        " else "    "
  let wrong := if global then "require" else "assume"
  let lines ← pick #[s!"{ind}expect zz: x +\n",
    s!"{ind}{wrong} zz: and \{\n{ind}    zb: x +\n{ind}}\n",
    s!"{ind}{wrong} zz: and \{\n{ind}    zb: x > 0,\n{ind}    zc: x < (1\n{ind}}\n"]
  -- Before the `}` that closes the block: a method's, before the trait's.
  let close := if trait then "    }\n}\n" else "}\n"
  return (block.dropEnd close.length).toString ++ lines ++ close

/-- A spec of what the confirmation of models evaluates (`--confirm`,
`Reqs/Models#known-values`): `div` and `mod` by a literal, positive or
negative; an index in an argument that a function's body never reads,
which leaves the application unknown out of range
(`model::known_application`); tables that may take no
row, or whose last row is a condition or `true`; `match`es over an integer
and over enumerations, exhaustive or not, by or-patterns and over one
variant, with binders read in a body or a guard, and in a function's body;
`match`es of several scrutinees and tables over one, a binder as the
whole arm, an or-pattern with a `_` alternative, `let` and `is`;
and the rules that know more than `lang::eval`: a count with an argument
that may be unknown, spelled out too, through a function and against a
constant, and an `if`, a `match` and a table whose condition or scrutinee
may be, with branches, arms or rows equal or not. A mode of its own, so
that the specs of the other modes' seeds are as they were. No value of an
abstract type or of a type parameter, which the Lean-hosted front end does
not evaluate. -/
def genConfirmed : R String := do
  let k : R String := do return toString (← below 4)
  let divisor : R String := pick #["2", "3", "-2", "(-3)"]
  let int : R String := do
    match ← below 12 with
    | 0 => return s!"(a {← pick #["div", "mod"]} {← divisor})"
    | 1 => return s!"(b {← pick #["div", "mod"]} {← divisor})"
    | 2 => return s!"cf_ind({← pick #["a", "b"]})"
    | 3 => return s!"(a {← pick #["div", "mod"]} {← divisor} + b)"
    | 4 => return "CF_ONE"
    | 5 => return s!"(if q != [] then q[0] else {← pick #["a", "b"]})"
    | 6 => return "(a + b)"
    -- A table that may take no row, whose value there is unspecified: by
    -- its conditions, since one over a range that leaves out values is a
    -- static error (F0317), which would stop the spec's checks.
    | 7 => return s!"table \{ a > {← k} => 1, b > {← k} => 2 }"
    | 8 => return s!"table \{ q != [] => q[0], a = {← k} => {← pick #["a", "b", "2"]} }"
    -- An `if` whose condition may be unknown, an index out of range.
    | 9 => return s!"(if q[{← k}] > {← k} then {← pick #["a", "b", "1"]} else {← pick #["a", "b", "1"]})"
    -- A `match` that may take no arm, by its guards.
    | 10 => return s!"match a \{ n if n > {← k} => 1, n if n < {← k} => b }"
    | _ => pick #["a", "b"]
  let op : R String := pick #["=", "!=", "<", "<=", ">", ">="]
  let bool : R String := do
    match ← below 31 with
    | 0 => return s!"a {← pick #["=", "!="]} b"
    | 1 | 2 => return s!"{← int} {← op} {← int}"
    -- An index in an argument that a body never reads only where nothing
    -- guards it: the `fren` command gives such an index no definedness goal
    -- (#493).
    | 3 => return s!"(q != [] and (q[0] {← op} {← int} or q[{← k}] = {← k}))"
    | 4 => return s!"(when {← k} < q.len, q[{← k}] {← op} {← int})"
    | 5 => return s!"(cf_ign?(q[{← k}]) or a {← op} {← k})"
    | 6 => return s!"(cf_ign?(a + b) or a {← op} {← k})"
    -- A count with an argument that may be unknown, which the others may decide.
    | 7 => return s!"{← pick #["at_most_one?", "exactly_one?"]}({← pick #["true", "false", "a > 1"]}, " ++
        s!"{← pick #["true", "false", "b > 1"]}, q[{← k}] = {← k})"
    -- An `if` whose condition may be unknown, with branches equal or not.
    | 8 =>
      let t ← pick #["a > 1", "true", "b = a"]
      return s!"(if q[{← k}] = {← k} then {t} else {← if ← chance 50 then pure t else pick #["a > 1", "false"]})"
    -- A `match` and a table whose scrutinee or condition may be unknown,
    -- with arms or rows equal or not.
    | 9 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match q[{← k}] \{ {← k} => {t}, _ => {u} })"
    | 10 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table \{ q[{← k}] = {← k} => {t}, _ => {u} }"
    -- A count spelled out, with a condition that may be unknown.
    | 11 =>
      return s!"((if q[{← k}] = {← k} then 1 else 0) + {← pick #["0", "1", "2", "(if a > 1 then 1 else 0)"]} " ++
        s!"{← pick #["<=", "="]} 1)"
    -- Through a function, and against a constant.
    | 12 => return s!"(cf_ind(q[{← k}]) + {← pick #["0", "1", "2"]} {← pick #["<=", "="]} 1)"
    | 13 =>
      return s!"((if q[{← k}] = {← k} then 1 else 0) + {← pick #["0", "1", "CF_ONE"]} {← pick #["<=", "="]} CF_ONE)"
    -- A `match` on a value of an enumeration that may be unknown: its arms
    -- exhaustive or not, by an or-pattern, with binders read in a body or a
    -- guard, and over an enumeration of one variant.
    | 14 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}] \{ Ce::P({← pick #["_", "n"]}) => {t}, Ce::Q => {u} })"
    | 15 =>
      let t ← pick #["a > 1", "true"]
      return s!"(match s[{← k}] \{ Ce::P(n) => n > {← k} or {t}, Ce::Q => {t} })"
    | 16 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}] \{ Ce::P(n) if n > {← k} => {t}, _ => {u} })"
    | 17 => return s!"(match s[{← k}] \{ Ce::P(_) | Ce::Q => {← pick #["a > 1", "true", "b = a"]} })"
    | 18 => return s!"(match o[{← k}] \{ Co::A({← pick #["_", "n"]}) => {← pick #["a > 1", "true", "b = a"]} })"
    -- In a function's body.
    | 19 => return s!"cf_pick?(s, a)"
    -- A table whose last row is a condition, or `true`.
    | 20 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table \{ q[{← k}] = {← k} => {t}, {← pick #["true", "a > 1"]} => {u} }"
    -- A `match` of several scrutinees, one of which may be unknown, which
    -- each pattern tests on its own (`model::arm_test_of`), with `_`s.
    | 21 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match q[{← k}], a \{ {← k}, _ => {t}, _, _ => {u} })"
    | 22 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match a, q[{← k}] \{ {← k}, _ => {t}, _, {← pick #["_", "n"]} => {u} })"
    | 23 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}], (a > 1) \{ Ce::P(_), _ => {t}, Ce::Q, true => {u}, Ce::Q, false => {t} })"
    -- A table over a scrutinee that may be unknown.
    | 24 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table (q[{← k}]) \{ {← k} => {t}, _ => {u} }"
    -- A binder of a scrutinee that may be unknown, as the whole arm.
    | 25 => return s!"(match q[{← k}] \{ n => {← pick #["n > 1 or a > 1", "a > 1", "n = n"]} })"
    -- An or-pattern with a `_` alternative, which tests nothing.
    | 26 =>
      let t ← pick #["a > 1", "true", "b = a"]
      -- The alternative's literal is none of the first arm's (`k`), which
      -- would leave it unreachable, a static error (F0318).
      return s!"(match q[{← k}] \{ {← k} => {t}, {← pick #["4", "5"]} | _ => {← pick #["a > 1", "false", "true"]} })"
    -- A `let`, whose definition the body reads or not.
    | 27 => return s!"(let z := {← pick #["q[1]", "a + 1"]} in {← pick #["z > 1", "a > 1"]})"
    -- A pattern test of a scrutinee that may be unknown.
    | 28 => return s!"(q[{← k}] is {← k} or a {← op} {← k})"
    -- A count spelled out with a negated literal, and as `1 >= sum`.
    | 29 =>
      let sum := s!"(if q[{← k}] = {← k} then 1 else 0) + {← pick #["-0", "0", "1", "-(-1)", "(if a > 1 then 1 else 0)"]}"
      let rel ← pick #["<=", "="]
      return if ← chance 50 then s!"(1 >= {sum})" else s!"({sum} {rel} 1)"
    | _ => return s!"(if a = b then a {← op} {← k} else b {← op} {← k})"
  let mut out := "mod fz\n\n" ++
    "pub fn cf_ign?(a: Int) := false\n" ++
    "pub enum Ce { P(Int), Q }\npub enum Co { A(Int) }\npub const CF_ONE: Int := 1\n" ++
    "pub fn cf_ind(n: Int): Int := if n = 0 then 1 else 0\n" ++
    "pub fn cf_pick?(s: Seq<Ce>, a: Int) := match s[1] { Ce::P(_) => a > 1, Ce::Q => a > 1 }\n"
  for i in [0:(← below 3) + 1] do
    let mut body := s!"    out r := {← int}\n"
    for j in [0:← below 2] do body := body ++ s!"    require ca{j}: {← bool}\n"
    for j in [0:(← below 3) + 1] do body := body ++ s!"    expect cx{j}: {← bool}\n"
    if ← chance 50 then body := body ++ s!"    cover cg0: {← bool}\n"
    let enumerated ← chance 30
    -- The sequences of enumerations only where the body reads them, and then
    -- not enumerated: the Lean-hosted front end does not count the scrutinee
    -- of a complete `match` among a check's variables (#493).
    let ce := if (body.splitOn "s[").length > 1 || (body.splitOn "cf_pick?(s").length > 1 then ", s: Seq<Ce>" else ""
    let co := if (body.splitOn "o[").length > 1 then ", o: Seq<Co>" else ""
    let enumerated := if enumerated && ce.isEmpty && co.isEmpty then
      "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n" else ""
    out := out ++ s!"\n{enumerated}pub proc cfm{i}(a: Int, b: Int, q: Seq<Int>{ce}{co}): (r: Int) \{\n{body}}\n"
  -- Binders of a scrutinee that may be unknown, each read where the arm
  -- binds it: in its body, its guard or both, for a binder as a column of a
  -- `match` of several scrutinees, as the whole arm, and in a variant's
  -- payload. Drawn after every other draw, so that each earlier seed's spec
  -- only grows (`Reqs/dev/Testing`, front-end corpus).
  let binderBool : R String := do
    let u ← pick #["a > 1", "false", "true"]
    let t ← pick #["a > 1", "true", "b = a"]
    let (g?, body) ← match ← below 3 with
      | 0 => pure (none, s!"n > {← k} or {t}")
      | 1 => pure (some s!"n > {← k}", t)
      | _ => pure (some s!"n > {← k}", s!"n < {← k} or {t}")
    let guard := (g?.map (s!" if " ++ ·)).getD ""
    -- After a binder's arm without a guard, which matches whatever is left,
    -- no arm, which would be unreachable (F0318), a static error.
    let rest (r : String) := if g?.isSome then s!", {r} => {u}" else ""
    match ← below 5 with
    | 0 => return s!"(match a, q[{← k}] \{ {← k}, _ => {u}, _, n{guard} => {body}{rest "_, _"} })"
    | 1 => return s!"(match q[{← k}], a \{ n, {← k}{guard} => {body}, _, _ => {u} })"
    | 2 => return s!"(match q[{← k}] \{ n{guard} => {body}{rest "_"} })"
    | 3 => return s!"(match s[{← k}] \{ Ce::P(n){guard} => {body}, _ => {u} })"
    | _ => return s!"(match o[{← k}] \{ Co::A(n){guard} => {body}{rest "_"} })"
  let mut binders := ""
  for j in [0:(← below 3) + 1] do binders := binders ++ s!"    expect cb{j}: {← binderBool}\n"
  out := out ++ s!"\npub proc cfb(a: Int, b: Int, q: Seq<Int>, s: Seq<Ce>, o: Seq<Co>): (r: Int) \{\n    out r := a\n{binders}}\n"
  return out

/-- `[]` and `{}` as methods' arguments, which take their element types
from their receivers (`Reqs/Lang/Expressions`): in one procedure, over
two to four sequences of `Int`, `Bool`, `String`, `Option<Int>` or `E` if
the spec has it, of sequences of them and of sets of them, each read
alone and then all of them in one expectation, so that the same `[]` is
typed against several element types in one check, as the hosted front
end's cache of the types of terms must not confuse (`typeOf`). A check
may fail, but nothing here is a static error. -/
def emptyArguments (sc : WScope) : R String := do
  let tys := #[("Int", "1"), ("Bool", "true"), ("String", "\"a\""), ("Option<Int>", "Option::Some(1)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0")] else #[])
  let mut params := #[]
  let mut atoms := #[]
  for k in [0:(← below 3) + 2] do
    let (t, v) ← pick tys
    let q := s!"ea{k}"
    let (ty, atom) ← match ← below 3 with
      | 0 => do
        let i ← below 2
        let a ← pick #[s!"{q}.starts_with?([])", s!"{q}.ends_with?([])", s!"{q}.contains?([])",
          s!"{q}.index_of([], {i}) >= 0", s!"{q}.replace([], [{v}]).len > {i}", s!"[] = {q}"]
        pure (s!"Seq<{t}>", a)
      | 1 => do
        let a ← pick #[s!"{q}.contains?([[]])", s!"{q}.starts_with?([[]])", s!"{q}.update(0, []) = {q}",
          s!"{q}.update(1, [{v}]).len = {q}.len", s!"{q}.ends_with?([[], [{v}]])"]
        pure (s!"Seq<Seq<{t}>>", a)
      | _ => do
        let a ← pick #[s!"{q}.update(0, \{}) = {q}", s!"{q}.update(1, \{}).len = {q}.len", s!"{q}.contains?([\{}])",
          s!"{q}.starts_with?([\{{v}}, \{}])"]
        pure (s!"Seq<Set<{t}>>", a)
    params := params.push s!"{q}: {ty}"
    atoms := atoms.push atom
  let body := String.join (atoms.toList.zipIdx.map fun (a, k) => s!"    expect xa{k}: {a}\n")
  return s!"pub proc empty_args({", ".intercalate params.toList}) \{\n{body}    expect xa_all: {" and ".intercalate atoms.toList}\n}\n"

/-- Structural recursions whose results have subset types (#693): of
`Int` or `Nat`, named or through an alias, over a list and a tree, with
each recursive application direct, under an `if`'s guard, under a `match`
on a payload, within arithmetic, or several of them, with a postcondition
or without, one generic at a result type that is not its type parameter,
and a procedure whose expectations apply each. Each application's result
type is a fact, in the function's own body too, beside its postconditions
(`lang::recursive_facts`), and a model that evaluation refutes is
Inconclusive (`lang::counterexample_confirmed`). A check may fail or be
inconclusive, but nothing here is a static error. -/
def recursiveSubsets : R String := do
  -- The subset type's base and its invariant, of a value.
  let (base, inv) ← pick #[("Int", fun (e : String) => s!"{e} >= 1"), ("Int", fun e => s!"{e} != 0"),
    ("Nat", fun e => s!"{e} >= 2"), ("Int", fun e => s!"{e} >= 1 and {e} <= 100")]
  let alias ← chance 50
  let ty := if alias then "Rsq" else "Rsp"
  let mut out := "pub enum Rsl { Nil, Cons(Int, Rsl) }\npub enum Rst { Leaf, Node(Rst, Rst) }\n" ++
    s!"pub type Rsp = n: {base} where inv: {inv "n"}\n" ++ (if alias then "pub type Rsq := Rsp\n" else "")
  -- The arm of a `Cons`, with the recursive application `f(p, ·)`, and
  -- whether it reads the element `x`.
  let arm (f : String) : R (String × String) := do
    match ← below 6 with
    | 0 => pure ("_", s!"{f}(p, r)")
    | 1 => pure ("x", s!"if x > 0 then {f}(p, r) else p")
    | 2 => pure ("_", s!"match r \{ Rsl::Nil => p, Rsl::Cons(_, s) => {f}(p, s) }")
    | 3 => pure ("_", s!"if {f}(p, r) = p then p else {f}(p, r)")
    -- Each arm meets the result type where the recursive applications
    -- do, so that a caller's check, which assumes it, holds in fact and
    -- the methods agree (`methodsAgree fuzz`).
    | 4 => pure ("_", s!"{f}(p, r) + 0")
    | _ => pure ("x", s!"if x = 0 then p else {f}(p, r)")
  let fns := #["rs_keep", "rs_post"]
  let (x, a) ← arm "rs_keep"
  out := out ++ s!"pub fn rs_keep(p: {ty}, l: Rsl): {ty} := match l \{\n" ++
    s!"    Rsl::Nil => p,\n    Rsl::Cons({x}, r) => {a},\n}\n"
  -- With a postcondition, which holds or fails by induction.
  let post ← pick #["o >= p", "o = p", "o > p", "o >= 1"]
  let (x, a) ← arm "rs_post"
  out := out ++ s!"pub fn rs_post(p: {ty}, l: Rsl): (o: {ty}) \{\n    out o := match l \{\n" ++
    s!"        Rsl::Nil => p,\n        Rsl::Cons({x}, r) => {a},\n    }\n    ensure e: {post}\n}\n"
  -- Two applications, over a tree.
  let (pat, a) ← pick #[("Rst::Node(a, b)", "if rs_tree(p, a) > rs_tree(p, b) then rs_tree(p, a) else rs_tree(p, b)"),
    ("Rst::Node(a, _)", "rs_tree(p, a)"), ("Rst::Node(a, b)", "if a = b then rs_tree(p, b) else p")]
  out := out ++ s!"pub fn rs_tree(p: {ty}, t: Rst): {ty} := match t \{\n    Rst::Leaf => p,\n    {pat} => {a},\n}\n"
  let generic ← chance 50
  if generic then
    out := out ++ s!"pub fn rs_gen<T>(p: {ty}, y: T, l: Rsl): {ty} := match l \{\n" ++
      s!"    Rsl::Nil => p,\n    Rsl::Cons(_, r) => rs_gen(p, y, r),\n}\n"
  -- Every input mentioned, so that none is unused: `l` first, `t` second.
  let mut body := ""
  for k in [0:(← below 3) + 2] do
    let app ← match k, ← below (if generic then 5 else 4) with
      | 0, _ => pure s!"{← pick fns}(p, l)"
      | 1, _ | _, 2 => pure "rs_tree(p, t)"
      | _, 0 => pure s!"{← pick fns}(p, l)"
      | _, 1 => pure s!"{← pick fns}(p, Rsl::Cons({← pick #["0", "1", "-1"]}, l))"
      | _, 3 => pure s!"{← pick fns}(p, Rsl::Nil)"
      | _, _ => pure s!"rs_gen(p, {← pick #["true", "1", "l"]}, l)"
    body := body ++ s!"    expect rs{k}: {← pick #[inv app, s!"{app} = p or ({inv app})"]}\n"
  out := out ++ s!"pub proc rs_apps(p: {ty}, l: Rsl, t: Rst) \{\n{body}}\n"
  -- A generic one whose result is its type parameter, at an enumeration
  -- whose payload has the subset type: its instance's result brings no
  -- fact, in both front ends.
  if ← chance 50 then
    out := out ++ s!"pub enum Rsb \{ B({ty}) }\n" ++
      "pub fn rs_rep<T>(x: T, l: Rsl): T := match l {\n    Rsl::Nil => x,\n    Rsl::Cons(_, r) => rs_rep(x, r),\n}\n" ++
      s!"pub proc rs_reps(b: Rsb, l: Rsl) \{\n    expect rr: match rs_rep(b, l) \{\n        Rsb::B(n) => {inv "n"},\n    }\n}\n"
  -- Result types that bring the subset type's constraint through data,
  -- each now and then: a record's field, a newtype's, an enumeration's
  -- payload, an option's, and every element of a set or a sequence, which
  -- quantifies over them. Each body meets its type, and a caller reads the
  -- constraint.
  let forms : Array (String × String × String × String) := #[
    ("rs_rec", "Rsr", s!"pub struct Rsr \{ v: {ty}, k: Int }\n", inv "rs_rec(v, l).v"),
    ("rs_nt", "Rsn", s!"pub struct Rsn({ty})\n", inv "rs_nt(v, l).0"),
    ("rs_ch", "Rse", s!"pub enum Rse \{ A({ty}), Z }\n",
      s!"match rs_ch(v, l) \{ Rse::A(n) => {inv "n"}, Rse::Z => true }"),
    ("rs_opt", s!"Option<{ty}>", "",
      s!"match rs_opt(v, l) \{ Option::Some(n) => {inv "n"}, Option::None => true }"),
    ("rs_set", s!"Set<{ty}>", "", s!"forall (n: {base}), when n in rs_set(v, l), {inv "n"}"),
    ("rs_seq", s!"Seq<{ty}>", "", s!"forall (n: {base}), when n in rs_seq(v, l), {inv "n"}")]
  for (f, rt, decl, read) in forms do
    unless ← chance 30 do continue
    -- A `Nat`, or a subset type of one, is no type argument or element type.
    if base == "Nat" && rt.contains '<' then continue
    -- A collection's constraint quantifies over its elements.
    let opt := if rt.startsWith "Set" || rt.startsWith "Seq" then "set_option fren.lint.undecidable \"allow\" in\n" else ""
    let (x, a) ← pick #[("_", s!"{f}(v, r)"), ("x", s!"if x > 0 then {f}(v, r) else v")]
    out := out ++ decl ++ opt ++ s!"pub fn {f}(v: {rt}, l: Rsl): {rt} := match l \{\n" ++
      s!"    Rsl::Nil => v,\n    Rsl::Cons({x}, r) => {a},\n}\n" ++
      opt ++ s!"pub proc {f}_apps(v: {rt}, l: Rsl) \{\n    expect c: {read}\n}\n"
  -- A body wrong only at its induction step, which no caller applies: its
  -- obligation's model, at a recursive application, is never confirmed,
  -- so it is Inconclusive in both front ends, never `F0661`.
  if base != "Nat" && (← chance 30) then
    out := out ++ s!"pub fn rs_bad(p: {ty}, l: Rsl): {ty} := match l \{\n" ++
      "    Rsl::Nil => p,\n    Rsl::Cons(x, r) => if x > 0 then rs_bad(p, r) - 1 else p,\n}\n"
  return out

/-- Several scrutinees of every matchable kind, repeated or distinct,
with parentheses, comments, calls (uninterpreted too), methods, fields,
indexes, definitions and nested matches. The result is also used in a
comparison, a definition, a closure and an outer match. This group adds
no static error. A mode of its own (`--scrutinees`) leaves every older
mode's seed unchanged, including diagnostics after an earlier error. -/
def duplicateScrutineeGroup : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum Ds { A, B, C(Int), D(Bool) }\n" ++
    "pub ordered enum Dso { A, B, C }\n" ++
    "pub enum Dsr { End, Next(Dsr) }\n" ++
    "pub struct Dsp { left: Int, right: Int }\n" ++
    "pub fn ds_unknown(Int): Int\n" ++
    "pub fn ds_apply(f: fn(Int) -> Int, x: Int): Int := f(x)\n" ++
    "pub fn ds_id<T>(x: T): T := x\n" ++
    "pub fn ds_implicit(Bool, Bool): Int := match { true, false => 1, _, _ => 0 }\n"
  let params := "n: Int, m: Int, u: Nat, v: Nat, a?, b?, s: String, t: String, r: Ds, z: Ds, " ++
    "o: Dso, h: Dso, opt: Option<Int>, other: Option<Int>, tree: Dsr, branch: Dsr, p: Dsp"
  for k in [:2] do
    let (ty, pairs, pat, otherPat) ← pick #[
      ("Int", #[("n", "m"), ("p.left", "p.right"), ("[n, m][0]", "[n, m][1]"),
        ("ds_unknown(n)", "ds_unknown(m)"), ("n + 1", "1 + n"),
        ("let x := n + 1 in x", "let x := m + 1 in x"),
        ("let x := n + 1 in x + 1", "let x := m + 1 in x + 1"),
        ("match r { Ds::C(x) => x, _ => n }", "match z { Ds::C(x) => x, _ => n }")], "0..=2", "3..=5"),
      ("Nat", #[("u", "v"), ("u + 1", "v + 1"), ("if a? then u else v", "if b? then u else v")], "0", "1"),
      ("Bool", #[("a?", "b?"), ("n > 0", "m > 0"), ("o < h", "o <= h"),
        ("not a?", "not b?"), ("a? and b?", "a? or b?"),
        ("when a?, b?", "unless a?, b?"),
        ("forall (ds_flag?: Bool), ds_flag? or a?", "exists (ds_flag?: Bool), ds_flag? and b?"),
        ("at_most_one?(a?, b?)", "exactly_one?(a?, b?)"),
        ("if r is Ds::C(x) then x > n else a?", "if z is Ds::C(x) then x > n else a?")], "true", "false"),
      ("String", #[("s", "t"), ("s.at(0)", "t.at(0)"), ("s ++ \"a\"", "t ++ \"a\"")], "\"a\"", "\"b\""),
      ("Ds", #[("r", "z"), ("Ds::C(n)", "Ds::C(m)"), ("if a? then r else z", "if b? then r else z")], "Ds::A", "Ds::C(_)"),
      ("Dso", #[("o", "h")], "Dso::A", "Dso::B"),
      ("Option<Int>", #[("opt", "other"), ("Option::Some(n)", "Option::Some(m)")], "Option::Some(_)", "Option::None"),
      ("Dsr", #[("tree", "branch"), ("Dsr::Next(tree)", "Dsr::Next(branch)")], "Dsr::End", "Dsr::Next(_)")]
    let (pat, otherPat) ← if pat == "Ds::A" then
      pick #[(pat, otherPat), ("Ds::A | Ds::B", "Ds::C(_)"),
        ("Ds::C(0..=2)", "Ds::C(3..=5)"), ("Ds::C(_)", "Ds::C(1)")]
    else if pat == "Dsr::End" then
      pick #[(pat, otherPat), ("Dsr::Next(Dsr::End)", "Dsr::Next(Dsr::Next(_))")]
    else if pat == "0..=2" then
      pick #[(pat, otherPat), ("0 | 2", "1 | 3"), ("0..=2", "2..=4")]
    else pure (pat, otherPat)
    let (x, y) ← pick pairs
    -- The same enclosing forms at every type, including generic and
    -- recursive enumerations. Parentheses keep open-ended operands local.
    let wrap ← below 6
    let localName := if ty == "Bool" then "ds_value?" else "ds_value"
    let otherLocal := if ty == "Bool" then "ds_other?" else "ds_other"
    -- `where` follows a whole body or constraint, never a scrutinee.
    let defs := if wrap == 3 then s!" where {localName} := ({x}), {otherLocal} := ({y})" else ""
    let enclose (x y : String) : String := match wrap with
      | 0 => x
      | 1 => s!"ds_id(({x}))"
      | 2 => s!"let {localName} := ({x}) in {localName}"
      | 3 => x
      | 4 => s!"if a? then ({x}) else ({y})"
      | _ => s!"match a? \{ true => ({x}), false => ({y}) }"
    let (x, y) := if wrap == 3 then (localName, otherLocal) else (enclose x y, enclose y x)
    let repeated ← chance 70
    let second := if repeated then x else y
    let bare := if second.all (fun c => c.isAlphanum || c == '_' || c == '?') then second else s!"({second})"
    let decorated ← pick #[bare, s!"({second})", s!"(/- column -/ {second})"]
    let third ← chance 40
    let scrs := s!"({x}), {decorated}" ++ (if third then s!", ({x})" else "")
    let tail := if third then ", _" else ""
    let guarded ← chance 40
    let guard := if guarded then " if a?" else ""
    let kw ← pick #["match", "table"]
    let e := s!"{kw} {scrs} \{ {pat}, {otherPat}{tail}{guard} => n + 1, _, _{tail} => m }"
    let bodies := #[e, s!"let result := {e} in result + 1", s!"({e}) + 1",
      s!"if ({e}) > n then n else m", s!"match ({e}) \{ 0 => n, _ => m }"]
    if (e ++ defs).contains "ds_unknown" then
      -- Uninterpreted applications belong in procedures, never in a
      -- defined function or a closure.
      let body ← pick bodies
      out := out ++ s!"pub proc ds_p{k}({params}): (value: Int) \{ ensure result: value = ({body}){defs} }\n"
    else
      let body ← pick (bodies.push s!"ds_apply(|arg| ({e}) + arg, n)")
      out := out ++ s!"pub fn ds_f{k}({params}): Int := {body}{defs}\n"
  -- Append after every existing draw, keeping each seed's earlier text.
  let (a, b) ← pick #[("n", "m"), ("m", "n")]
  let kw ← pick #["match", "table"]
  return out ++ s!"pub fn ds_groups(n: Int, m: Int): Int := {kw} {a}, {b}, {a}, {b} \{ 0, 0, 0, 1 => 1, 0, 1, 1, 1 => 2, _, _, _, _ => 0 }\n" ++
    s!"pub fn ds_generic<T>(o: Option<T>): Int := {kw} o, o \{ Option::Some(_), Option::None => 1, _, _ => 0 }\n"

/-- Compare reports on separate queries of one item that mention disjoint
contracts, or no function at all (#766). These exercise transitive contract
chains over scalar, collection and compound results, sometimes nested in a
generic record, a defined identity, a `let`, a `where`, a quantifier, a
conditional, a match or a table. The mode checks agreement on the chain,
separate contract and plain cover goal; the UI fixture pins their expected
results. Its independent mode leaves existing seeds and draws unchanged. -/
def factScopes : R String := do
  let k ← below 4
  let (decls, ty, value) ← pick #[
    ("", "Int", toString k), ("", "Nat", toString k),
    ("", "Bool", "true"), ("", "String", "\"scope\""),
    ("", "Set<Int>", s!"\{{k}}"), ("", "Rel<Int, Int>", s!"\{({k}, {k + 1})}"),
    ("", "Seq<Int>", s!"[{k}, {k + 1}]"),
    ("pub enum ScE { A, B }\n", "ScE", "ScE::A"),
    ("pub enum ScP { A, B(Int) }\n", "ScP", s!"ScP::B({k})"),
    ("pub struct ScN(Int)\n", "ScN", s!"ScN({k})"),
    ("pub struct ScBox<T> { v: T }\n", "ScBox<Seq<Int>>", s!"ScBox \{ v := [{k}] }")]
  let r := if ty == "Bool" then "r?" else "r"
  let name (i : Nat) := s!"sc{i}{if ty == "Bool" then "?" else ""}"
  let mut out := "set_option fren.lint.undecidable \"allow\"\n" ++ decls ++
    s!"pub fn {name 0}(x: Int): ({r}: {ty}) \{ ensure e: {r} = {value} }\n"
  let n := (← below 3) + 1
  for i in [1:n + 1] do
    out := out ++ s!"pub fn {name i}(x: Int): ({r}: {ty}) \{ ensure e: {r} = {name (i - 1)}(x) }\n"
  let app := s!"{name n}(x)"
  let (extra, goal) ← match ← below 9 with
    | 0 => pure ("", s!"{app} = {value}")
    | 1 => pure ("", s!"(({app})) = {value}")
    | 2 => pure ("pub fn sc_id<T>(v: T): T := v\n", s!"sc_id({app}) = {value}")
    | 3 => pure ("", s!"(let {r} := {app} in {r}) = {value}")
    | 4 => pure ("", s!"{r} = {value} where {r} := {app}")
    | 5 => pure ("", s!"(if x > {k} then {app} else {name n}(x + 1)) = {value}")
    | 6 => pure ("", s!"(match (x > {k}) \{ true => {app}, false => {name n}(x + 1) }) = {value}")
    | 7 => pure ("", s!"(table \{ x > {k} => {app}, _ => {name n}(x + 1) }) = {value}")
    | _ => pure ("", s!"forall (j: Int), when {k} <= j < {k + 2}, {name n}(j) = {value}")
  -- Other comparisons of ordered results exercise closure at those sites.
  let goal ← if ty == "Int" || ty == "Nat" then
    pick #[goal, s!"{app} >= {k}", s!"{app} <= {k}", s!"{app} < {k + 1}", s!"{app} > {k} - 1",
      s!"{app} != {k + 1}"]
    else pure goal
  return out ++ extra ++ "pub fn sc_other(x: Int): (r: Int) { ensure e: r < 0 }\n" ++
    s!"proc sc_queries(x: Int) \{\n    expect chain: {goal}\n    expect separate: sc_other(x) < 0\n" ++
    s!"    cover plain: x = {k}\n}\n"

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

/-- Relation obligations below fields, payloads and collection quantifiers,
at calls and in the procedure's own inputs and defined outputs.
Drawn after `enumerationObligations`' original cases. `natural` appends
Nat-based subset types without changing the original draws. -/
def enumerationRelations (natural : Bool := false) : R String := do
  let (base, good, bad) ← if natural then pure ("Nat", "0", "1") else pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("String", "\"\"", "\"a\""),
    ("E", "E::A", "E::B"), ("N", "N(0)", "N(1)"),
    ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let valueName := if base == "Bool" then "value?" else "value"
  let left ← pick #[good, bad]
  let right ← pick #[good, bad]
  let otherLeft ← pick #[good, bad]
  let otherRight ← pick #[good, bad]
  -- Nat may occur in fields and non-recursive payloads, but not directly
  -- as an element or type argument. Put the Nat-based subset in a field
  -- before using it inside relations and their surrounding types.
  let wrap (v : String) := if natural then s!"NatBox \{ value := {v} }" else v
  let (left, right, otherLeft, otherRight) := (wrap left, wrap right, wrap otherLeft, wrap otherRight)
  let (relation, first, second) ← pick #[
    ("Rel<Narrow, Narrow>", s!"\{({left}, {right})}", s!"\{({otherLeft}, {otherRight})}"),
    ("Rel<Narrow, Bool>", s!"\{({left}, true)}", s!"\{({otherLeft}, false)}"),
    ("Rel<Bool, Narrow>", s!"\{(false, {right})}", s!"\{(true, {otherRight})}")]
  let (ty, arg, other) ← pick #[
    (relation, first, second),
    (s!"Pair<{relation}, Narrow>", s!"Pair \{ first := {first}, second := {left} }", s!"Pair \{ first := {second}, second := {otherLeft} }"),
    (s!"Pair<Narrow, {relation}>", s!"Pair \{ first := {left}, second := {first} }", s!"Pair \{ first := {otherLeft}, second := {second} }"),
    (s!"Option<{relation}>", s!"Option::Some({first})", "Option::None"),
    (s!"Choice<{relation}>", s!"Choice::Two({first}, {second})", "Choice::Empty"),
    (s!"Set<{relation}>", s!"\{{first}}", "{}"),
    (s!"Seq<{relation}>", s!"[{first}]", s!"[{second}]"),
    (s!"Rel<{relation}, Narrow>", s!"\{({first}, {left})}", s!"\{({second}, {otherLeft})}"),
    (s!"Rel<Narrow, {relation}>", s!"\{({left}, {first})}", s!"\{({otherLeft}, {second})}"),
    (s!"Rel<{relation}, {relation}>", s!"\{({first}, {second})}", s!"\{({second}, {first})}"),
    (s!"Option<Pair<{relation}, {relation}>>", s!"Option::Some(Pair \{ first := {first}, second := {second} })", "Option::None"),
    (s!"Pair<Option<{relation}>, Choice<{relation}>>", s!"Pair \{ first := Option::Some({first}), second := Choice::One({second}) }", "Pair { first := Option::None, second := Choice::Empty }"),
    (s!"Set<Option<{relation}>>", s!"\{Option::Some({first})}", "{Option::None}"),
    (s!"Seq<Set<{relation}>>", s!"[\{{first}}]", "[{}]"),
    ("RelBox", first, second)]
  let relation := if natural then relation.replace "Narrow" "NatBox" else relation
  let ty := if natural then ty.replace "Narrow" "NatBox" else ty
  -- Newtypes have no type parameters. Keep the function's result erased
  -- and construct the constrained newtype at its giving site instead.
  let erased := (if ty == "RelBox" then relation else ty).replace "Narrow" base
  let definition ← pick #[arg, s!"if flag? then {arg} else {other}",
    s!"let saved: {erased} := {arg} in saved"]
  let options := "set_option fren.enumeration.size 1 in\nset_option fren.evidence \"enumerated\" in\n"
  let given := if ty == "RelBox" then "RelBox(nested_value(flag?))" else "nested_value(flag?)"
  -- Copying the input exercises both type facts. The call separately
  -- checks its named parts; output type-giving checks use the solver.
  let moduleName := if natural then "enum_natural_relation_obligations" else "enum_relation_obligations"
  return s!"\nmod {moduleName}\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n" ++
    "pub struct Pair<A, B> { first: A, second: B }\npub enum Choice<T> { Empty, One(T), Two(T, T) }\n" ++
    s!"pub type Narrow = {valueName}: {base} where first: {valueName} != {bad} and second: {valueName} = {good}\n" ++
    (if natural then "pub struct NatBox { value: Narrow }\n" else "") ++
    s!"pub struct RelBox({relation})\n" ++
    s!"pub proc accept_nested(arg: {ty}) \{}\n" ++
    s!"pub fn nested_value(flag?): {erased} := {definition}\n" ++ options ++
    s!"pub proc caller(flag?) \{ call c := accept_nested({given}) }\n" ++ options ++
    s!"pub proc own_membership(value: {ty}): (copy: {ty}) \{\n" ++
    "    call c := accept_nested(value)\n    out copy := value\n    expect same: copy = value\n}\n"

/-- Call-input obligations with two named parts, and predicate leaves with
inherited evidence (#813). `natural` generates additional Nat-based cases
and `guardOrders` further wrapper orders over every base type, drawn after
both modes' original cases. -/
def enumerationObligationCases (natural : Bool := false) (guardOrders : Bool := false) : R String := do
  let (base, good, bad) ← if natural then pure ("Nat", "0", "1") else pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "0", "1"),
    ("String", "\"\"", "\"a\""), ("E", "E::A", "E::B"),
    ("N", "N(0)", "N(1)"), ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let valueName := if base == "Bool" then "value?" else "value"
  let localName := if base == "Bool" then "saved?" else "saved"
  let moduleName := if natural then "enum_natural_obligations" else if guardOrders then "enum_guard_obligations" else "enum_obligations"
  let declarations := s!"mod {moduleName}\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n" ++
    "pub struct Pair<A, B> { first: A, second: B }\npub enum Choice<T> { Empty, One(T), Two(T, T) }\n" ++
    s!"pub type Narrow = {valueName}: {base} where first: {valueName} != {bad} and second: {valueName} = {good}\n" ++
    (if natural then "pub struct NatField { value: Narrow }\npub struct NatNewtype(Narrow)\n" ++
      "pub enum NatPayload { Empty, One(Narrow), Two(Narrow, Narrow) }\n" else "")
  let value ← pick #[good, bad]
  -- Every giving site, including nested generic payloads and fields.
  let field := s!"NatField \{ value := {value} }"
  let payload := s!"NatPayload::Two({value}, {good})"
  let (ty, arg) ← if natural then pick #[
    ("Narrow", value), ("NatField", field), ("NatNewtype", s!"NatNewtype({value})"),
    ("NatPayload", payload), ("Set<NatField>", s!"\{{field}}"), ("Seq<NatPayload>", s!"[{payload}]"),
    ("Rel<NatField, NatPayload>", s!"\{({field}, {payload})}"),
    ("Option<NatField>", s!"Option::Some({field})"),
    ("Pair<NatField, NatPayload>", s!"Pair \{ first := {field}, second := {payload} }"),
    ("Option<Pair<NatField, NatPayload>>", s!"Option::Some(Pair \{ first := {field}, second := {payload} })"),
    ("Pair<Option<NatField>, Choice<NatPayload>>", s!"Pair \{ first := Option::Some({field}), second := Choice::One({payload}) }")]
    else if base == "Nat" then pure ("Narrow", value) else pick #[
    ("Narrow", value), ("Pair<Narrow, Narrow>", s!"Pair \{ first := {value}, second := {good} }"),
    ("Option<Narrow>", s!"Option::Some({value})"),
    ("Choice<Narrow>", s!"Choice::Two({value}, {good})"),
    ("Set<Narrow>", s!"\{{value}}"), ("Seq<Narrow>", s!"[{value}]"),
    ("Rel<Narrow, Narrow>", s!"\{({value}, {good})}"),
    ("Option<Pair<Narrow, Narrow>>", s!"Option::Some(Pair \{ first := {good}, second := {value} })"),
    ("Pair<Option<Narrow>, Choice<Narrow>>", s!"Pair \{ first := Option::Some({value}), second := Choice::One({good}) }")]
  let argument := if base == "Bool" && ty == "Narrow" then "arg?" else "arg"
  let copy := if base == "Bool" && ty == "Narrow" then "copy?" else "copy"
  let definition ← pick #[arg, s!"if flag? then {arg} else {arg}", s!"let {copy}: {ty.replace "Narrow" base} := {arg} in {copy}"]
  let option ← pick #["enumerated", "enumerated+random"]
  let wrapper ← if natural || guardOrders then pick #[
    "let saved := value in when flag?, p?(saved)",
    "let saved := value in unless flag?, p?(saved)",
    "(when flag?, p?(saved)) where saved := value",
    "(unless flag?, p?(saved)) where saved := value",
    "let saved := value in when gate?, p?(saved) where gate? := flag?",
    "let saved := value in unless gate?, p?(saved) where gate? := flag?",
    "when flag?, let saved := value in p?(saved)",
    "unless flag?, let saved := value in p?(saved)"] else pick #[
    "p?(value)", "when flag?, p?(value)", "unless flag?, p?(value)",
    "let saved := value in p?(saved)", "not p?(value)",
    "p?(saved) where saved := value", "when flag?, let saved := value in p?(saved)",
    "let saved := value in not p?(saved)", "not (when flag?, p?(value))"]
  let wrapper := (wrapper.replace "value" valueName).replace "saved" localName
  let member ← pick #["", "set_option fren.evidence \"solver\" in ", "set_option fren.evidence \"enumerated\" in "]
  return declarations ++ s!"pub proc accept({argument}: {ty}) \{}\n" ++
    s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
    s!"pub proc caller(flag?) \{ call c := accept({definition}) }\n" ++
    s!"pub fn p?({valueName}: {base}) := and \{ first: {valueName} != {bad}, second: {valueName} = {good} }\n" ++
    s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
    s!"pub proc predicates({valueName}: {base}, flag?) \{ {member}expect property: {wrapper} }\n"

/-- Whole and split predicate checks under guards, negation and bindings.
These draws follow all existing enumeration cases. -/
def predicateCheckLocations : R String := do
  let (base, good, bad) ← pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "0", "1"),
    ("String", "\"\"", "\"a\""), ("E", "E::A", "E::B"),
    ("N", "N(0)", "N(1)"), ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let value := if base == "Bool" then "value?" else "value"
  let saved := if base == "Bool" then "saved?" else "saved"
  let option ← pick #["solver", "enumerated", "enumerated+random"]
  let guard ← pick #["when", "unless"]
  let order ← below 8
  let wrap (representative expression : String) : String :=
    let bound := expression.replace "VALUE" saved
    let expression := expression.replace "VALUE" representative
    match order with
    | 0 => s!"{guard} active?, {expression}"
    | 1 => s!"let {saved}: {base} := {representative} in {guard} active?, {bound}"
    | 2 => s!"{guard} active?, let {saved}: {base} := {representative} in {bound}"
    | 3 => s!"({guard} active?, {bound}) where {saved}: {base} := {representative}"
    | 4 => s!"{guard} active?, ({bound}) where {saved}: {base} := {representative}"
    | 5 => s!"let {saved}: {base} := {representative} in {guard} gate?, {bound} where gate? := active?"
    | 6 => s!"when active?, unless other?, {expression}"
    | _ => s!"unless active?, when other?, {expression}"
  -- A separate lint gap under `where` is outside these placement cases.
  -- Keep cover goals, but do not compare the unrelated trigger lint.
  let mut out := "\nmod enum_predicate_locations\nset_option fren.lint.trivial_cover \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n"
  for op in #["and", "or", "iff", "one"] do
    out := out ++ s!"pub fn p_{op}?({value}: {base}, other?) := {op} \{ first: {value} != {bad}, second: other? }\n"
  for op in #["and", "or", "iff", "one"] do
    -- Closed typed representatives make member notes comparable without
    -- relying on which valid data model each backend chooses.
    let representative := if op == "and" then good else bad
    out := out ++ s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
      s!"pub proc {op}_checks(active?, other?) \{\n" ++
      s!"    expect positive: {wrap representative s!"p_{op}?(VALUE, other?)"}\n" ++
      s!"    expect negative: {wrap representative s!"not p_{op}?(VALUE, other?)"}\n" ++
      s!"    cover witness: {wrap representative s!"p_{op}?(VALUE, other?)"}\n}\n"
  -- Contracts use the same source policy as procedure constraints.
  let op ← pick #["and", "or", "iff", "one"]
  out := out ++ s!"pub fn contracted?(active?): (result?) \{\n" ++
    "    out result? := true\n" ++
    s!"    ensure post: {guard} active?, not p_{op}?({good}, result?)\n}\n"
  return out

/-- The original enumeration cases, optionally followed by relation cases,
then Nat-based subset types, further `let`/`where` guard orders and whole
predicate check locations. All new draws follow both modes' existing
draws, preserving their original specs as prefixes. -/
def enumerationObligations (relations : Bool := false) : R String := do
  let original ← enumerationObligationCases
  let originalRelations ← if relations then enumerationRelations else pure ""
  let natural ← enumerationObligationCases true
  let naturalRelations ← if relations then enumerationRelations true else pure ""
  let guardOrders ← enumerationObligationCases (guardOrders := true)
  let locations ← predicateCheckLocations
  return original ++ originalRelations ++ "\n" ++ natural ++ naturalRelations ++ "\n" ++ guardOrders ++ locations

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
  /-- The Lean front end's diagnostics. -/
  hosted : Array Diagnostic := #[]
  /-- With `obligations`, both front ends' obligations dumps, the `fren`
  command's first (`Fren.Core.dump`). -/
  obligations? : Option (String × String) := none

/-- `out` without its obligations dump, and the dump, if it has one
(`Fren.Core.dumpStart`). -/
def splitDump (out : String) : String × Option String := Id.run do
  let lines := out.splitOn "\n"
  let some i := lines.idxOf? Fren.Core.dumpStart | return (out, none)
  let some j := (lines.drop i).idxOf? Fren.Core.dumpEnd | return (out, none)
  let dump := "\n".intercalate ((lines.drop i).take (j + 1))
  return ("\n".intercalate (lines.take i ++ lines.drop (i + j + 1)), some dump)

/-- The `fren` command's diagnostics and summary on `text`, and its exit
code, and with `obligations`, its obligations dump. -/
def runCli (path : System.FilePath) (text : String) (obligations := false) :
    IO (Array Diagnostic × Option String × UInt32 × Option String) := do
  IO.FS.writeFile path text
  let (out, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files := #[path.toString], dumpObligations := obligations })
  let (out, dump?) := splitDump out
  let (cli, cliSum) := FrenTest.Ui.cliDiagnostics path.toString out (keepUnlocated := true)
  return (cli, cliSum, code, dump?)

/-- Checks `text` with both front ends, both misreading models if
`misread`, as `--confirm` has them (`Fren.Core.misreadSet`), or if
`FREN_MISREAD_MODELS` is set; with `obligations`, with their obligations
dumps, which are not among their diagnostics. -/
def runFrontends (env : Environment) (path : System.FilePath) (text : String) (misread := false) (obligations := false) :
    IO Ran := do
  Fren.Core.misreadSet.set misread
  let misread ← Fren.Core.misreadModels
  let (cli, cliSum, code, cliDump?) ← runCli path text obligations
  let opts : Options := if obligations then Fren.fren.dump.set {} "obligations" else {}
  let (hosted, hostedSum) ← FrenTest.Ui.hostedDiagnostics env path.toString text opts
  let (dumps, hosted) := hosted.partition (·.text.startsWith Fren.Core.dumpStart)
  let obligations? := if obligations then some (cliDump?.getD "", (dumps[0]?.map (·.text)).getD "") else none
  let comparison := FrenTest.Frontends.comparison text
    { diags := cli, summary? := cliSum, exit? := some code.toNat } { diags := hosted, summary? := hostedSum } misread
  let render (ds : Array Diagnostic) (s : Option String) :=
    String.join (ds.toList.map fun d => s!"--   {d.line}:{d.col + 1}: {d.severity}{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}\n")
      ++ s!"--   summary: {s.getD "(none)"}\n"
  return { comparison, reports := s!"-- fren (exit {code}):\n{render cli cliSum}-- Lean:\n{render hosted hostedSum}",
           errors := cli.filterMap fun d => if d.severity == "error" then d.code? else none,
           cli, hosted, obligations? }

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

/-- The generator of `--keywords`' following item (`Wide.genKeywordsTail`),
split off the seed, so that its draws leave `genKeywords`' unchanged. -/
def tailRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6b77⟩

/-- The generator of `--keywords`' grammar errors (`Wide.genKeywordsGrammar`),
split off the seed too. -/
def grammarRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6772⟩

/-- The generator of `--keywords`' item of each kind (`Wide.genKeywordsItem`),
split off the seed too. -/
def itemRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6974⟩

/-- The generator of `--induction-candidates` (`Wide.inductionCandidates`),
split off the seed so that its draws leave the other modes unchanged. -/
def inductionRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6963⟩

/-- The generator of `--unfoldings` (`Wide.unfoldings`), split off the
seed so that its draws leave the other modes unchanged. -/
def unfoldingRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x756e⟩

/-- The generator modes selected by command-line flags. Each specialized
mode generates specs of the constructs described by its field; otherwise
`Wide.genWide` generates a mix, optionally avoiding known differences. -/
structure Mode where
  avoidKnown : Bool := false
  guards : Bool := false
  /-- Specs of `Wide.sitesProc`s alone (`Wide.genSites`). -/
  sites : Bool := false
  /-- Specs of what the confirmation of models evaluates
  (`Wide.genConfirmed`). -/
  confirm : Bool := false
  /-- Multi-scrutinee lints alone (`Wide.duplicateScrutineeGroup`). -/
  scrutinees : Bool := false
  /-- Specs of global expectations over recursive enumerations alone
  (`Wide.inductions`). -/
  inductions : Bool := false
  /-- Specs of the forms in which the front ends read a candidate for
  induction (`Wide.inductionForms`). -/
  inductionForms : Bool := false
  /-- Specs of a clause written with the other block's keyword
  (`Wide.genKeywords`). -/
  keywords : Bool := false
  /-- Query-local transitive fact closure (`Wide.factScopes`). -/
  factScopes : Bool := false
  /-- Specs of induction-candidate types, argument forms and comparisons
  (`Wide.inductionCandidates`). -/
  inductionCandidates : Bool := false
  /-- Specs of call-input obligations with two named parts, predicate leaves
  with inherited evidence and whole-predicate check locations
  (`Wide.enumerationObligations`). -/
  enumerationObligations : Bool := false
  /-- Append nested relation cases after the original enumeration cases. -/
  enumerationRelations : Bool := false
  /-- Specs of claims that induction proves only by unfolding more than
  one step (`Wide.unfoldings`). -/
  unfoldings : Bool := false
  /-- Collection payloads and fields of generic datatypes. -/
  datatypeElements : Bool := false
  deriving BEq

def Mode.spec (m : Mode) (seed : Nat) : String :=
  if m.enumerationObligations || m.enumerationRelations then
    Id.run ((Wide.enumerationObligations m.enumerationRelations).run' (rngOf seed))
  else if m.keywords then
    let block := Id.run (Wide.genKeywords.run' (rngOf seed))
    let spec := Id.run ((Wide.genKeywordsGrammar block).run' (grammarRngOf seed)) ++
      Id.run ((Wide.genKeywordsTail block).run' (tailRngOf seed))
    -- The item of `Wide.genKeywordsItem` after the declarations that
    -- `genKeywords` writes first.
    let decls := "pub proc spec(x: Int): (v: Int) { ensure e: v = x }\n"
    match spec.splitOn decls with
    | [before, after] => before ++ decls ++ Id.run (Wide.genKeywordsItem.run' (itemRngOf seed)) ++ after
    | _ => spec
  else if m.inductionCandidates then Id.run (Wide.inductionCandidates.run' (inductionRngOf seed))
  else if m.unfoldings then Id.run (Wide.unfoldings.run' (unfoldingRngOf seed))
  else
    Id.run ((if m.inductionForms then Wide.inductionForms else if m.inductions then Wide.inductions
      else if m.scrutinees then Wide.duplicateScrutineeGroup
      else if m.factScopes then Wide.factScopes else if m.confirm then Wide.genConfirmed
      else if m.sites then Wide.genSites else if m.guards then Wide.genGuards
      else if m.datatypeElements then FuzzDatatypeElements.spec
      else Wide.genWide m.avoidKnown).run' (rngOf seed))

/-- The cuts of the spec of `seed` (`Wide.genWideCuts`), each shorter than
the next; none for `--guards`, `--sites`, `--confirm`, `--inductions`,
`--induction-forms` and `--keywords`. The empty prefix of `--scrutinees`,
`--fact-scopes`, `--induction-candidates`, `--enumeration-obligations`,
`--unfoldings` and `--datatype-elements` makes any static error a group
error: these generators, like appended groups, promise to add none.
`--enumeration-relations` keeps the original enumeration spec as its
prefix, so its additional cases must add no static error either. -/
def Mode.cuts (m : Mode) (seed : Nat) : Array String :=
  if m.enumerationRelations then #[Id.run ((Wide.enumerationObligationCases false).run' (rngOf seed))] else
  if m.scrutinees || m.factScopes || m.inductionCandidates || m.enumerationObligations || m.unfoldings || m.datatypeElements then #[""] else if m.guards || m.sites || m.confirm || m.inductions || m.inductionForms || m.keywords then #[] else
    (Id.run ((Wide.genWideCuts m.avoidKnown).run' (rngOf seed))).2

def Mode.args (m : Mode) : Array String :=
  (if m.avoidKnown then #["--avoid-known"] else #[]) ++ (if m.guards then #["--guards"] else #[]) ++
    (if m.sites then #["--sites"] else #[]) ++ (if m.confirm then #["--confirm"] else #[]) ++
    (if m.scrutinees then #["--scrutinees"] else #[]) ++
    (if m.inductions then #["--inductions"] else #[]) ++ (if m.inductionForms then #["--induction-forms"] else #[]) ++
    (if m.keywords then #["--keywords"] else #[]) ++
    (if m.factScopes then #["--fact-scopes"] else #[]) ++
    (if m.inductionCandidates then #["--induction-candidates"] else #[]) ++
    (if m.enumerationObligations then #["--enumeration-obligations"] else #[]) ++
    (if m.enumerationRelations then #["--enumeration-relations"] else #[]) ++
    (if m.unfoldings then #["--unfoldings"] else #[]) ++
    (if m.datatypeElements then #["--datatype-elements"] else #[])

def flags (m : Mode) : String := String.join (m.args.toList.map (" " ++ ·))

/-- The mode of the flags `args`, if they are only flags of a mode. -/
def Mode.ofArgs? (args : List String) : Option Mode :=
  if args.all (· ∈ ["--avoid-known", "--guards", "--sites", "--confirm", "--scrutinees", "--inductions", "--induction-forms",
      "--keywords", "--fact-scopes", "--induction-candidates", "--enumeration-obligations", "--enumeration-relations", "--unfoldings", "--datatype-elements"]) then
    some { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards", sites := args.contains "--sites",
           confirm := args.contains "--confirm", scrutinees := args.contains "--scrutinees"
           inductions := args.contains "--inductions", inductionForms := args.contains "--induction-forms"
           keywords := args.contains "--keywords", factScopes := args.contains "--fact-scopes"
           inductionCandidates := args.contains "--induction-candidates"
           enumerationObligations := args.contains "--enumeration-obligations"
           enumerationRelations := args.contains "--enumeration-relations"
           unfoldings := args.contains "--unfoldings", datatypeElements := args.contains "--datatype-elements" }
  else none

/-- The mode as Lean writes it in `knownDifferences`. -/
def Mode.lean (m : Mode) : String :=
  let fields := (if m.avoidKnown then ["avoidKnown := true"] else []) ++ (if m.guards then ["guards := true"] else []) ++
    (if m.sites then ["sites := true"] else []) ++ (if m.confirm then ["confirm := true"] else []) ++
    (if m.scrutinees then ["scrutinees := true"] else []) ++
    (if m.inductions then ["inductions := true"] else []) ++ (if m.inductionForms then ["inductionForms := true"] else []) ++
    (if m.keywords then ["keywords := true"] else []) ++
    (if m.factScopes then ["factScopes := true"] else []) ++
    (if m.inductionCandidates then ["inductionCandidates := true"] else []) ++
    (if m.enumerationObligations then ["enumerationObligations := true"] else []) ++
    (if m.enumerationRelations then ["enumerationRelations := true"] else []) ++
    (if m.unfoldings then ["unfoldings := true"] else []) ++
    (if m.datatypeElements then ["datatypeElements := true"] else [])
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
  static error: on a spec where both front ends report one, at the same
  line and column (`sharedStaticErrorLines`), at or before the
  difference's line, which their recovery from the error explains. -/
  afterStaticError : Bool := false
  /-- As a kind, it is known only on a spec that also has a difference of
  this kind (a `signature`), which explains it. -/
  alongside? : Option String := none
  /-- Whether the kind of `alongside?` must be at the same line, so that it
  explains the difference at that check only. -/
  onItsLine : Bool := false
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
`signature`) listed here for `--avoid-known`, or in `knownKinds`, as
known. An entry holds the
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
     difference := "line 41:18: only Lean reports warning: `n1` is never negative, so it can be a `Nat`" },
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
     difference := "line 21:13: only Lean reports info: `a0` cannot hold." },
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
   -- Run 267 found these on main; both seeds reproduce at dd28d924,
   -- before #817. Lean cannot decide the expectation, while `fren`
   -- reports its dependency or failure (#493).
   { mode := { avoidKnown := true }, seed := 1267162, issue := 493, onItsLine := true,
     alongside? := some "only Lean reports warning: could not decide whether `_` holds: INCOMPLETE",
     difference := "line 141:12: only fren reports warning[F0664]: `fz::zpn::zpe1` rests on the realizability of \
       `fz::zpn`, which did not pass" },
   { mode := { avoidKnown := true }, seed := 1267162, issue := 493, onItsLine := true,
     alongside? := some "only fren reports warning[F0664]: `_` rests on the realizability of `_`, which did not pass",
     difference := "line 141:12: only Lean reports warning: could not decide whether `fz::zpn::zpe1` holds: INCOMPLETE" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493, onItsLine := true,
     alongside? := some "only Lean reports warning: could not decide whether `_` holds",
     difference := "line 167:12: only fren reports error[F0603]: expectation `fz::gr_apps::gr1` does not hold" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493, onItsLine := true,
     alongside? := some "only fren reports error[F0603]: expectation `_` does not hold",
     difference := "line 167:12: only Lean reports warning: could not decide whether `fz::gr_apps::gr1` holds" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493,
     alongside? := some "only fren reports error[F0603]: expectation `_` does not hold",
     difference := "summary: fren says `57 passed (1 by bounded enumeration), 17 failed, 18 inconclusive, 0 redundant`, \
       Lean says `57 passed (1 by bounded enumeration), 16 failed, 19 inconclusive, 0 redundant`" }]

/-- Whether the kind `s` (a `signature`) is of the pattern `p`, where each
`*` stands for any text, and every other character for itself. -/
partial def kindMatches (p s : String) : Bool :=
  go p.toList s.toList
where
  go : List Char → List Char → Bool
    | [], s => s.isEmpty
    | '*' :: p, s => go p s || match s with
      | [] => false
      | _ :: s => go ('*' :: p) s
    | c :: p, d :: s => c == d && go p s
    | _ :: _, [] => false

#guard kindMatches "only fren reports warning[F07*"
  "only fren reports warning[F0712]: this `_` expression can be simpler"
#guard !kindMatches "only fren reports warning[F07*" "only fren reports warning[F0608]: could not decide"
#guard kindMatches "a * b * c" "a x b y b z c"
#guard !kindMatches "a * c" "a x c d"
#guard kindMatches "exit" "exit" && !kindMatches "exit" "exits"

/-- A kind of difference that an issue tracks, which runs of fresh seeds
find, but that no spec of the corpus has, so that `knownDifferences` does
not list it: `--avoid-known` counts it as known, like the kinds that
`knownDifferences` lists, and `lake test` does not check it. -/
structure KnownKind where
  /-- The kind, as a `signature`, where `*` stands for any text
  (`kindMatches`). -/
  kind : String
  issue : Nat
  /-- The spec where a run found it first, to reproduce it with. -/
  mode : Mode := { avoidKnown := true }
  seed : Nat
  /-- As `Known.afterStaticError`. -/
  afterStaticError : Bool := false
  /-- As `Known.alongside?`, a kind that may have `*`s too. -/
  alongside? : Option String := none
  /-- Whether the kind of `alongside?` must be at the same line, so that it
  explains the difference at that check only. -/
  onItsLine : Bool := false
  /-- A condition on the difference itself, given the spec's differences,
  for what its kind masks: the names, as which clauses a conflict core
  has (`leanCoreHasMore`), or which procedure a message is about
  (`aboutUnreadProcedure`). -/
  test? : Option (Array String → String → Bool) := none

/-- The kind of Lean's failure, through lean-smt, on a query that has the
same closed application twice under different binders (#493), whatever
it could not decide. -/
def leanSmtArrow : String :=
  "only Lean reports warning: could not decide whether * cvc5.Error.error \
    \"Symbol '->' not declared as a variable\""

/-- The kind of Lean's failure to enumerate a procedure that the `fren`
command enumerates (#485), which explains the inconclusive results and
the summary that only `fren` gives there. -/
def leanEnumerationFails : String :=
  "only Lean reports error: internal error: enumerating `_` in Lean failed: failed to synthesize"

/-- The kind of the `fren` command's warning that a trait's expectation
rests on an uninterpreted function's contract whose realizability did not
pass, which Lean does not give (#493). -/
def traitRestsOnContract : String :=
  "only fren reports warning[F0664]: `_` rests on the realizability of the contract of `_`, which did not pass"

/-- The clauses of one side of a conflict core, as `compare` writes it
after `no outputs satisfy`: `` `q2` `` or `` `q0`, `q1` and `q2` ``, each
name in backticks, separated by `, ` or ` and `. -/
def coreClauses? (side : String) : Option (List String) := do
  let parts := side.splitOn "`"
  guard (parts.length ≥ 3 && parts.length % 2 == 1 && parts.head? == some "" && parts.getLast? == some "")
  let inner := (parts.drop 1).dropLast
  let names := inner.zipIdx.filterMap fun (p, i) => if i % 2 == 0 then some p else none
  let seps := inner.zipIdx.filterMap fun (p, i) => if i % 2 == 1 then some p else none
  guard (names.all (!·.isEmpty) && seps.all (· ∈ [", ", " and "]))
  return names

#guard coreClauses? "`q2`" == some ["q2"]
#guard coreClauses? "`q0`, `q1` and `q2`" == some ["q0", "q1", "q2"]
#guard coreClauses? "`q0` or `q1`" == none
#guard coreClauses? "q0" == none

/-- The difference `f` is a conflict core where `fren`'s clauses are a
proper subset of Lean's: for the same input, `fren` says `no outputs
satisfy` some clauses, and Lean says it of those and more (#493). -/
def leanCoreHasMore (_ : Array String) (f : String) : Bool := Id.run do
  let pre := "for the same input, fren says `no outputs satisfy "
  let mid := "`, Lean says `no outputs satisfy "
  let some rest := (f.splitOn pre)[1]? | return false
  let [frenSide, leanSide] := rest.splitOn mid | return false
  let some leanSide := leanSide.dropSuffix? "`" | return false
  let (some fren, some lean) := (coreClauses? frenSide, coreClauses? leanSide.toString) | return false
  return fren.all (· ∈ lean) && lean.any (· ∉ fren)

section
private def core (fren lean : String) : String :=
  s!"line 43: for the same input, fren says `no outputs satisfy {fren}`, Lean says `no outputs satisfy {lean}`"
#guard leanCoreHasMore #[] (core "`q2`" "`q0`, `q1` and `q2`")
#guard leanCoreHasMore #[] (core "`q0` and `q2`" "`q0`, `q1` and `q2`")
-- Not where the cores are disjoint, equal, or `fren`'s is the larger.
#guard !leanCoreHasMore #[] (core "`q0` and `q2`" "`q1` and `q3`")
#guard !leanCoreHasMore #[] (core "`q0`, `q1` and `q2`" "`q3` and `q4`")
#guard !leanCoreHasMore #[] (core "`q0` and `q1`" "`q1` and `q0`")
#guard !leanCoreHasMore #[] (core "`q0`, `q1` and `q2`" "`q2`")
#guard !leanCoreHasMore #[] (core "`q2`" "`q0` and `q3`")
end

/-- The procedure that the `fren` command's evaluator cannot read a
formula of, in a difference of the kind `evaluatorUnread`. -/
def unreadProcedure? (g : String) : Option String := do
  guard (signature g == evaluatorUnread)
  let name ← (g.splitOn "a formula of `")[1]?
  (name.dropSuffix? "`").map (·.toString)

/-- The subject of the message of the difference `f`: its first name in
backticks. -/
def subject? (f : String) : Option String := (f.splitOn "`")[1]?

/-- The difference `f` is about the procedure `p`, or one of its items: its
subject is `p` or a name in `p`. -/
def isAbout (p f : String) : Bool := (subject? f).any fun n => n == p || n.startsWith s!"{p}::"

/-- The difference `f` is about a procedure that the `fren` command's
evaluator cannot read a formula of, by a difference among `found`: what
Lean reports of that procedure (#484). -/
def aboutUnreadProcedure (found : Array String) (f : String) : Bool :=
  found.any fun g => (unreadProcedure? g).any (isAbout · f)

/-- The procedure that Lean fails to enumerate, in a difference of the
kind `leanEnumerationFails`. -/
def enumerationFailedProcedure? (g : String) : Option String := do
  guard (signature g == leanEnumerationFails)
  let name ← (g.splitOn "enumerating `")[1]?
  return (name.splitOn "`")[0]!

/-- The difference `f` is about a procedure that Lean fails to enumerate,
by a difference among `found`: what only `fren` reports of it (#485). -/
def aboutUnenumeratedProcedure (found : Array String) (f : String) : Bool :=
  found.any fun g => (enumerationFailedProcedure? g).any (isAbout · f)

/-- The difference `f` is a check's result, of an `F06xx` code. -/
def checkResult (_ : Array String) (f : String) : Bool := (f.splitOn "reports warning[F06").length > 1
  || (f.splitOn "reports error[F06").length > 1 || (f.splitOn "reports info[F06").length > 1

section
private def unread : String :=
  "line 13:10: only fren reports error[-]: internal error: the evaluator does not know the meaning of a formula of `fz::c0`"
#guard unreadProcedure? unread == some "fz::c0"
#guard aboutUnreadProcedure #[unread] "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of \
  `fz::c0`, which did not pass"
#guard aboutUnreadProcedure #[unread] "line 13:10: only Lean reports error: `fz::c0` is not realizable"
-- Not what Lean reports of another procedure, nor of one whose name only
-- starts the same, nor of one that only mentions it.
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c1` is not realizable"
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c1` calls `fz::c0`, so x"
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c01` is not realizable"
#guard !aboutUnreadProcedure #[] "line 13:10: only Lean reports error: `fz::c0` is not realizable"
end

/-- The difference `f` is no check's result: a static error's, not one of
the `F06xx` codes of checks. -/
def notCheckResult (_ : Array String) (f : String) : Bool := (f.splitOn "reports error[F06").length == 1

/-- The kinds of the issues that runs of `--avoid-known` on fresh seeds
found, beyond those that `knownDifferences` lists: `fuzz-frontends` in
`lean ci` fails on a difference of any other kind. Each entry gives the
first seed where a run found it. A kind is listed here once its issue
records it, with the seed, under the most specific issue that tracks it,
#493 only where none does; when the issue is fixed, its kinds are
removed. -/
def knownKinds : List KnownKind :=
  -- After a static error, only `fren` reports the lints of what follows
  -- it (#493): any lint, as `knownDifferences` lists a few.
  [{ kind := "only fren reports warning[F07*", issue := 493, seed := 1175152, afterStaticError := true },
   { kind := "only fren reports warning[F08*", issue := 493, seed := 6000809, afterStaticError := true },
   -- and its static errors after one that both report, as the decidable
   -- core's: not a check's result.
   { kind := "only fren reports error[F0*", issue := 493, seed := 6000809, afterStaticError := true,
     test? := some notCheckResult },
   -- Only Lean notes why an assumption's operands cannot both hold, in
   -- any wording (#493; `knownDifferences` lists two at seed 1160124).
   { kind := "only Lean reports info: Both operands of `_` cannot be *", issue := 493, seed := 1190787 },
   -- For the same input, Lean gives a realizability conflict core that
   -- has `fren`'s clauses and more (#493).
   { kind := "for the same input, fren says …, Lean says …", issue := 493, seed := 6001014,
     test? := some leanCoreHasMore },
   -- Only `fren` reports that an assumption constrains only parameters
   -- that nothing uses (F0792, #493).
   { kind := "only fren reports warning[F0792]: the assumption `_` constrains only parameters that nothing uses",
     issue := 493, seed := 1175274 },
   -- and on other specs, only Lean does.
   { kind := "only Lean reports warning: the assumption `_` constrains only parameters that nothing uses",
     issue := 493, seed := 1182701 },
   -- The CLI's evaluator cannot read a formula of a procedure that Lean
   -- enumerates (#484), so only Lean reports what enumerating that
   -- procedure found, and what rests on it, at any size bound; and the
   -- summaries differ.
   { kind := "only Lean reports *", issue := 484, seed := 1187360, alongside? := some evaluatorUnread,
     test? := some aboutUnreadProcedure },
   { kind := "summary: fren says …, Lean says …", issue := 484, seed := 1187360, alongside? := some evaluatorUnread },
   -- A trait's check that Lean cannot decide (`leanSmtArrow`): what only
   -- `fren` reports of the check at its line, as that it rests on the
   -- trait's laws (F0665), on its assumptions and calls (F0664), that its
   -- assumptions contradict each other (F0602), or that an arm is never
   -- taken (F0626), and so the summaries' counts (#493).
   { kind := leanSmtArrow, issue := 493, seed := 1179170 },
   { kind := "only fren reports *", issue := 493, seed := 1179170, alongside? := some leanSmtArrow, onItsLine := true,
     test? := some checkResult },
   { kind := "summary: fren says …, Lean says …", issue := 493, seed := 1179061, alongside? := some leanSmtArrow },
   -- A trait's expectation rests on a contract whose realizability did
   -- not pass: only `fren` warns, and counts it inconclusive (#493).
   { kind := traitRestsOnContract, issue := 493, seed := 1179203 },
   { kind := "summary: fren says …, Lean says …", issue := 493, seed := 1179203,
     alongside? := some traitRestsOnContract },
   -- Lean fails to enumerate a procedure (#485), so only `fren` reports
   -- what enumerating it found, and what rests on it.
   { kind := leanEnumerationFails, issue := 485, seed := 1175253 },
   { kind := "only fren reports warning[F0608]: could not decide whether *", issue := 485, seed := 1175253,
     alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "only fren reports info[F0646]: * checks of `_` hold for every behaviour up to size *", issue := 485,
     seed := 1175253, alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "only fren reports warning[F0664]: * rests on the realizability of `_`, which did not pass",
     issue := 485, seed := 1175253, alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "summary: fren says …, Lean says …", issue := 485, seed := 1175253,
     alongside? := some leanEnumerationFails }]

/-- The line of the difference `f`, if it has one: `line N:` or `line
N:COL:` at its start. -/
def differenceLine? (f : String) : Option Nat := do
  let first ← (f.splitOn ": ").head?
  let rest ← first.dropPrefix? "line "
  (rest.toString.splitOn ":").head?.bind String.toNat?

#guard differenceLine? "line 48:34: only fren reports warning[F0710]: unused variable `n`" == some 48
#guard differenceLine? "line 11: for the same input, fren notes #[]" == some 11
#guard differenceLine? "exit: fren exits 1, and Lean's messages call for 2" == none

/-- The issue of the known kind of the difference `f`, on a spec whose
differences are `found` and where both front ends report static errors
at the lines `staticLines` (`sharedStaticErrorLines`): a kind that `knownDifferences` lists for a seed
of `--avoid-known`, of either generator, or one of `knownKinds`, where
`mode` is of `--avoid-known` too: on the fresh seeds that CI checks with
it, those kinds go unchecked. An entry that holds only after a static
error (`afterStaticError`) matches only where one is at or before `f`'s
line, and one that holds only alongside another kind (`alongside?`) only
where `found` has that kind, on the same line when `onItsLine` is set;
one with a `test?`, only where the
difference passes it. -/
def knownIssue? (mode : Mode) (staticLines : Array Nat) (found : Array String) (f : String) : Option Nat :=
  let sig := signature f
  let holds (afterStaticError : Bool) (alongside? : Option String) (onItsLine := false) :=
    (!afterStaticError || (differenceLine? f).any fun l => staticLines.any (· ≤ l))
      && alongside?.all fun a => found.any fun g =>
        kindMatches a (signature g) && (!onItsLine || (differenceLine? f).isSome && differenceLine? g == differenceLine? f)
  if !mode.avoidKnown then none
  else match knownDifferences.find? (fun k =>
      k.mode.avoidKnown && signature k.difference == sig && holds k.afterStaticError k.alongside? k.onItsLine) with
    | some k => some k.issue
    | none =>
      (knownKinds.find? fun k =>
        kindMatches k.kind sig && holds k.afterStaticError k.alongside? k.onItsLine && k.test?.all (· found f)).map
        (·.issue)

/-- Whether the difference `f` is of a known kind (`knownIssue?`). -/
def knownKind (mode : Mode) (staticLines : Array Nat) (found : Array String) (f : String) : Bool :=
  (knownIssue? mode staticLines found f).isSome

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
-- A verdict count on its own, and another exit code, are no known kind, so
-- a spec that has one is a finding.
#guard !known "summary: fren says `15 passed, 19 failed, 1 inconclusive, 0 redundant`, Lean says `14 passed, \
  20 failed, 1 inconclusive, 0 redundant`" #[1]
-- A conflict core is known only where Lean's has more clauses than `fren`'s.
#guard known "line 23: for the same input, fren says `no outputs satisfy `q2``, Lean says `no outputs \
  satisfy `q0`, `q1` and `q2``"
#guard !known "line 23: for the same input, fren says `no outputs satisfy `q0` and `q2``, Lean says `no outputs \
  satisfy `q2``"
#guard !known "exit: fren exits 0, and Lean's messages call for 1" #[1]
-- Of `knownKinds`: any lint that only `fren` reports after a static error,
-- of a code that `knownDifferences` does not list, but no other warning.
#guard known "line 21:25: only fren reports warning[F0736]: both operands of `=` are written the same" #[11]
-- A static error that only `fren` reports, with no earlier one that both
-- report, is a finding; and a check's result is none of this kind.
#guard known "line 53:21: only fren reports error[F0307]: nonlinear arithmetic is not supported" #[42]
#guard !known "line 53:21: only fren reports error[F0307]: nonlinear arithmetic is not supported"
#guard !known "line 53:21: only fren reports error[F0603]: expectation `fz::c0::e` does not hold" #[42]
-- The pairs from seeds 1267162 and 1267186 excuse only their own line:
-- an inconclusive expectation elsewhere cannot hide a decided result.
section
private def failed : String :=
  "line 53:21: only fren reports error[F0603]: expectation `fz::c0::e` does not hold"
private def rests : String :=
  "line 53:21: only fren reports warning[F0664]: `fz::c0::e` rests on the realizability of `fz::c0`, which did not pass"
private def unknown : String :=
  "line 53:21: only Lean reports warning: could not decide whether `fz::c0::e` holds"
private def incomplete : String := unknown ++ ": INCOMPLETE"
#guard known failed (found := #[failed, unknown]) && known unknown (found := #[failed, unknown])
#guard known rests (found := #[rests, incomplete]) && known incomplete (found := #[rests, incomplete])
#guard !known failed (found := #[failed, unknown.replace "line 53:" "line 54:"])
#guard !known rests (found := #[rests, incomplete.replace "line 53:" "line 54:"])
#guard !known unknown (found := #[failed.replace "line 53:" "line 54:", unknown])
#guard !known incomplete (found := #[rests.replace "line 53:" "line 54:", incomplete])
end
#guard !known "line 21:25: only fren reports warning[F0736]: both operands of `=` are written the same"
#guard known "line 10:33: only Lean reports info: Both operands of `a0` cannot be false: this would require `b0?` to \
  equal false, while `a1` requires `b0?` to equal true."
#guard !known "line 65:72: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
#guard known "line 65:72: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
  #[46]
#guard known "line 22:12: only fren reports warning[F0792]: the assumption `a0` constrains only parameters that \
  nothing uses"
#guard !known "line 31:10: only fren reports warning[F0608]: could not decide whether `fz::c0` is realizable: no \
  outputs up to size 2, but larger ones may exist" #[1]
-- A trait's expectation that Lean cannot decide: the warning that only
-- `fren` gives, and the summary, are known only alongside Lean's failure.
section
private def arrow : String := "line 95:12: only Lean reports warning: could not decide whether `fz::Tr::e0` holds: \
  cvc5.Error.error \"Symbol '->' not declared as a variable\""
private def laws : String :=
  "line 95:12: only fren reports warning[F0665]: `fz::Tr::e0` rests on the laws of `fz::Tr`, whose consistency is \
    not checked"
private def summary : String := "summary: fren says `12 passed, 2 failed, 2 inconclusive, 0 redundant`, Lean says \
  `11 passed, 2 failed, 3 inconclusive, 0 redundant`"
#guard known arrow
#guard known laws (found := #[laws, arrow]) && known summary (found := #[laws, arrow, summary])
#guard !known laws && !known summary (found := #[laws, summary])
-- only at the line of Lean's failure.
#guard !known laws (found := #[laws, arrow.replace "line 95:12" "line 96:12"])
-- and only a check's result: not a static error nor a lint at its line.
#guard !known "line 95:40: only fren reports error[F0307]: nonlinear arithmetic is not supported"
  (found := #["line 95:40: only fren reports error[F0307]: nonlinear arithmetic is not supported", arrow])
#guard !known "line 95:40: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
  (found := #["line 95:40: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken",
    arrow])
#guard knownIssue? { avoidKnown := true } #[] #[laws, arrow] laws == some 493
#guard knownIssue? {} #[] #[laws, arrow] laws == none
-- Lean's failure is known whatever it could not decide.
#guard known "line 61:12: only Lean reports warning: could not decide whether the assumptions and calls of \
  `fz::Tr::e1` can hold together with its trait's laws: cvc5.Error.error \"Symbol '->' not declared as a variable\""
end
-- The evaluator's failure explains what only Lean's enumeration reports,
-- and nothing else.
#guard known "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, which did \
  not pass" (found := #["line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, \
  which did not pass", "line 13:10: only fren reports error[-]: internal error: the evaluator does not know the \
  meaning of a formula of `fz::c0`"])
-- of that procedure only.
#guard !known "line 50:12: only Lean reports error: `fz::c1` is not realizable" (found := #["line 50:12: only Lean \
  reports error: `fz::c1` is not realizable", "line 13:10: only fren reports error[-]: internal error: the evaluator \
  does not know the meaning of a formula of `fz::c0`"])
#guard !known "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, which did \
  not pass"
-- Lean's failure to enumerate explains what only `fren` reports of that
-- procedure, at any size bound, and is #485's; but not of another.
section
private def enumFails : String :=
  "line 31:10: only Lean reports error: internal error: enumerating `fz::c0` in Lean failed: failed to synthesize"
private def ofEnum (f : String) : Option Nat := knownIssue? { avoidKnown := true } #[] #[enumFails, f] f
#guard enumerationFailedProcedure? enumFails == some "fz::c0"
#guard ofEnum "line 31:10: only fren reports info[F0646]: 7 checks of `fz::c0` hold for every behaviour up to size 3"
  == some 485
#guard ofEnum "line 31:10: only fren reports info[F0646]: 7 checks of `fz::c9` hold for every behaviour up to size 3"
  == none
#guard ofEnum "line 43:12: only fren reports warning[F0608]: could not decide whether `fz::c0::x0` is vacuous: no \
  witness up to size 2, but a larger one may exist" == some 485
#guard ofEnum "line 43:12: only fren reports warning[F0608]: could not decide whether `fz::c9` holds: INCOMPLETE" == none
#guard ofEnum "line 41:12: only fren reports warning[F0664]: `fz::c0::cx0` rests on the realizability of `fz::c0`, \
  which did not pass" == some 485
#guard ofEnum "line 41:12: only fren reports warning[F0664]: `fz::c9::cx0` rests on the realizability of `fz::c9`, \
  which did not pass" == none
end
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
`[SEED, SEED + COUNT)` of each mode, split into jobs by `corpusJobs`.
Sized so that the whole corpus takes about 2 minutes of one CI machine. -/
def corpus : List (Mode × Nat × Nat) :=
  [({}, 0, 30), ({}, 30, 30), ({ guards := true }, 0, 20), ({ guards := true }, 20, 20), ({ sites := true }, 0, 20),
    ({ confirm := true }, 0, 20), ({ scrutinees := true }, 0, 20), ({ scrutinees := true }, 840434, 1),
    ({ inductions := true }, 0, 20),
    ({ inductionForms := true }, 0, 20), ({ factScopes := true }, 0, 20),
    ({ inductionCandidates := true }, 0, 20),
    ({ enumerationObligations := true }, 0, 20), ({ enumerationObligations := true }, 438, 1),
    ({ enumerationObligations := true }, 555, 1), ({ enumerationRelations := true }, 0, 20),
    ({ unfoldings := true }, 0, 10), ({ datatypeElements := true }, 0, 20)]

/-- The specs that `knownDifferences` lists outside `corpus`, checked in
the batches that `corpusJobs` lists as `frontendFuzz listed START COUNT`. -/
def listedOutside : List (Mode × Nat) :=
  let inCorpus (m : Mode) (s : Nat) := corpus.any fun (m', a, n) => m' == m && a ≤ s && s < a + n
  (knownDifferences.filterMap fun k => if inCorpus k.mode k.seed then none else some (k.mode, k.seed)).eraseDups

/-- At most this many specs per corpus job, so that no large batch holds
up a shard after its other jobs finish. Each job imports `Fren` once. -/
def corpusBatch : Nat := 5

/-- The arguments of the corpus's jobs of `fren_test`, with every range
and the seeds listed outside them split into batches of `corpusBatch`. -/
def corpusJobs : List (List String) :=
  let batches (n : Nat) := (List.range ((n + corpusBatch - 1) / corpusBatch)).map fun i =>
    (i * corpusBatch, min corpusBatch (n - i * corpusBatch))
  corpus.flatMap (fun (m, a, n) => (batches n).map fun (offset, count) =>
    ["frontendFuzz", toString (a + offset), toString count] ++ m.args.toList)
    ++ (batches listedOutside.length).map fun (offset, count) =>
      ["frontendFuzz", "listed", toString offset, toString count]

/-- The specs of a job of the corpus, from its arguments after
`frontendFuzz`. -/
def corpusSpecs? : List String → Option (List (Mode × Nat))
  | ["listed"] => some listedOutside
  | ["listed", start, count] => do
    let a ← start.toNat?
    let n ← count.toNat?
    return (listedOutside.drop a).take n
  | seed :: count :: args => do
    let a ← seed.toNat?
    let n ← count.toNat?
    let m ← Mode.ofArgs? args
    return (List.range n).map fun i => (m, a + i)
  | _ => none

#guard corpusSpecs? ["listed"] == some listedOutside
#guard corpusSpecs? ["listed", "5", "2"] == some ((listedOutside.drop 5).take 2)
#guard corpusSpecs? ["listed", "x", "2"] == none
#guard corpusSpecs? ["5", "2", "--guards"] == some [({ guards := true }, 5), ({ guards := true }, 6)]
#guard corpusSpecs? ["5", "2", "--other"] == none
#guard corpusSpecs? ["5"] == none
-- The seeds of `knownDifferences` outside the corpus's ranges, the
-- `--avoid-known` ones among them, and every job's specs are the corpus's
-- or those.
#guard listedOutside == ({}, 153) :: ([41, 1156065, 1160095, 3000319, 3102696, 3103202, 3100624, 1159002, 3102505,
  3101311, 3104511, 1157147, 1158050, 3000892, 3102156, 1157298, 1160124, 1160173, 1267162, 1267186].map
    fun s => ({ avoidKnown := true }, s))
#guard corpusJobs.all fun j => (corpusSpecs? (j.drop 1)).isSome
-- The jobs keep every original mode and seed, in order, exactly once,
-- including the final partial batch of seeds outside the ranges.
#guard (corpusJobs.flatMap fun j => (corpusSpecs? (j.drop 1)).getD []) ==
  corpus.flatMap (fun (m, a, n) => (List.range n).map fun i => (m, a + i)) ++ listedOutside
#guard corpusJobs.all fun j =>
  let specs := (corpusSpecs? (j.drop 1)).getD []
  !specs.isEmpty && specs.length ≤ corpusBatch

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
not a check's result, the trailer that says that they stopped the checks,
nor an internal error, as the evaluator's that cannot read a formula
(`evaluatorUnread`), which is no error of the spec's and from which no
front end recovers (`knownKind`). -/
def staticErrorLines (diags : Array Diagnostic) : Array Nat :=
  diags.filterMap fun d =>
    if d.severity == "error" && !FrenTest.Frontends.isCheckResult d && !FrenTest.Frontends.isStoppedTrailer d
      && !d.text.startsWith "internal error" && d.line > 0 then some d.line else none

/-- The lines of the static errors that both front ends report, at the
same line and column (`staticErrorLines`): those that explain a
difference after them, which a static error that only one front end
reports does not, since it is a difference itself. -/
def sharedStaticErrorLines (cli hosted : Array Diagnostic) : Array Nat :=
  let isStatic (d : Diagnostic) := !(staticErrorLines #[d]).isEmpty
  (cli.filter fun d => isStatic d && hosted.any fun h => isStatic h && h.line == d.line && h.col == d.col).map
    (·.line)

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
-- Only the static errors that both front ends report, at the same place.
#guard sharedStaticErrorLines #[errAt 3, errAt 7, errAt 9 "F0603"] #[{ errAt 3 with code? := none }, errAt 5,
  errAt 9] == #[3]
-- An internal error is no static error of the spec's.
#guard staticErrorLines #[errAt 3, { line := 25, severity := "error", text := "internal error: the evaluator does \
  not know the meaning of a formula of `fz::c0`" }] == #[3]
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
    let ran ← runFrontends env path (mode.spec s) mode.confirm
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

/-- How long a spec runs, in milliseconds, before it is reported as slow. -/
def slowMs : Nat := 20000

/-- What a worker found on one spec, one JSON object per line of the run's
results file, so that a worker that crashes loses nothing. -/
structure Outcome where
  seed : Nat
  /-- `ok`, `differ`, `inconclusive` (differ only in undecided checks),
  `known` (with `--avoid-known`, differ only in kinds that
  `knownDifferences` or `knownKinds` lists), `crash` or `timeout`. -/
  status : String
  /-- The mode's flags, as `flags` gives them. -/
  flags : String := ""
  errors : Array String := #[]
  signatures : Array String := #[]
  /-- For each of `signatures`, the issue of its known kind
  (`knownIssue?`), or 0 if it is of none. -/
  issues : Array Nat := #[]
  /-- How long the spec took, in milliseconds, and how much of that was in
  solver queries that ended at their time limit (`Fren.Core.solverTimeoutMs`). -/
  ms : Nat := 0
  solverTimeoutMs : Nat := 0
  /-- Whether the front ends' obligations dumps differ, without their
  metadata (`Fren.Core.withoutMetadata`): reported, but not a failure
  (`obligationsDiffer`). -/
  obligations : Bool := false
  /-- And whether they differ other than in the names of their constants
  (`obligationsDifferBeyondNames`). -/
  obligationsBeyondNames : Bool := false
  deriving ToJson, FromJson

/-- A run's work files, named after the driver's process, so that runs
sharing `--out` do not mix them. -/
structure Run where
  dir : String
  id : String

def Run.results (r : Run) : System.FilePath := r.dir / s!"results-{r.id}.jsonl"
def Run.progress (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.seed"
def Run.spec (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.fren"
/-- The worker's `Fren.Core.solverTimeoutMs`, which it writes as it grows. -/
def Run.solver (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.solver"

/-- Writes the worker's `Fren.Core.solverTimeoutMs` to `Run.solver` whenever
it grows, until cancelled, on a thread of its own, so that it is written
while a spec's check runs, or hangs. The file is replaced whole, so that
the driver never reads half of it. -/
def reportSolverTime (r : Run) : IO Unit := do
  let mut last := 0
  let tmp := r.solver.addExtension "tmp"
  while !(← IO.checkCanceled) do
    let ms ← Fren.Core.solverTimeoutMs
    if ms != last then
      IO.FS.writeFile tmp (toString ms)
      IO.FS.rename tmp r.solver
      last := ms
    IO.sleep 100

def record (r : Run) (o : Outcome) : IO Unit := do
  let h ← IO.FS.Handle.mk r.results .append
  h.putStrLn (toJson o).compress
  h.flush

/-- Whether two front ends' obligations dumps of a spec differ, but for
their metadata (`Fren.Core.withoutMetadata`): an early signal of a
difference between their queries (`Reqs/Cli#obligations`), which a run
reports, but which fails nothing yet, since many dumps differ in what
predates the dump, such as the names that lean-smt's embeddings give
`Nat` and `Bool` variables (#493). -/
def obligationsDiffer (cli hosted : String) : Bool :=
  Fren.Core.withoutMetadata cli != Fren.Core.withoutMetadata hosted

/-- `line` with each of its symbols that `names` has written `_`. -/
def collapseNames (names : Array String) (line : String) : String := Id.run do
  let mut out := ""
  let mut tok := ""
  for c in line.toList do
    if c == ' ' || c == '(' || c == ')' then
      out := out ++ (if names.contains tok then "_" else tok) |>.push c
      tok := ""
    else tok := tok.push c
  return out ++ (if names.contains tok then "_" else tok)

/-- A dump's obligations, each as its lines, sorted, with the names of the
constants and functions that it declares written `_` (`collapseNames`): two dumps whose
obligations are the same so differ only in the names of their constants,
as where lean-smt's embeddings rename a `Nat` or `Bool` variable. -/
def namelessObligations (dump : String) : Array (Array String) := Id.run do
  let mut blocks : Array (Array String) := #[]
  for l in (Fren.Core.withoutMetadata dump).splitOn "\n" do
    if l == "(obligation" then blocks := blocks.push #[]
    else if let some b := blocks.back? then blocks := blocks.pop.push (b.push l)
  return blocks.map fun b =>
    let names := b.filterMap fun l =>
      let l := l.trimAscii.toString
      ((l.dropPrefix? "(declare-const ").orElse fun _ => l.dropPrefix? "(declare-fun ").map
        fun r => ((r.toString.splitOn " ")[0]?).getD ""
    (b.map (collapseNames names)).qsort (· < ·)

/-- Whether two front ends' obligations dumps differ other than in the
names of their constants (`namelessObligations`). -/
def obligationsDifferBeyondNames (cli hosted : String) : Bool :=
  namelessObligations cli != namelessObligations hosted

#guard !obligationsDifferBeyondNames
  "(obligation\n  (signature\n    (declare-const n Int)\n  )\n  (context\n    (>= n 0)\n  )\n  (goal (> n 1))\n)"
  "(obligation\n  (signature\n    (declare-const f Int)\n  )\n  (context\n    (>= f 0)\n  )\n  (goal (> f 1))\n)"
#guard obligationsDifferBeyondNames
  "(obligation\n  (signature\n    (declare-const n Int)\n  )\n  (goal (> n 1))\n)"
  "(obligation\n  (signature\n    (declare-const f Int)\n  )\n  (goal (> f 2))\n)"

/-- Checks the specs of seeds `[seed, seed + count)` in this process,
writing each one's outcome to the results file. With `compareDumps`
(`--obligations`), it compares the front ends' obligations dumps too, from
runs with the dump on, whose messages it then compares: off by default, so
that a run compares the messages of what users run. -/
unsafe def worker (count seed : Nat) (run : Run) (mode : Mode) (compareDumps : Bool) : IO UInt32 := do
  let env ← loadFren
  let reporter ← IO.asTask (prio := .dedicated) (reportSolverTime run)
  for i in [0:count] do
    let s := seed + i
    -- The spec, and the time in queries that timed out before it.
    let solver0 ← Fren.Core.solverTimeoutMs
    IO.FS.writeFile run.progress s!"{s}\n{solver0}"
    let text : String := mode.spec s
    let t0 ← IO.monoMsNow
    let ran ← runFrontends env run.spec text mode.confirm compareDumps
    let (found, flaky, reports, errs) := (ran.comparison.found, ran.comparison.flaky, ran.reports, ran.errors)
    -- The obligations dumps, compared without their metadata, and both
    -- written where they differ.
    let obligations := match ran.obligations? with
      | some (a, b) => obligationsDiffer a b
      | none => false
    let obligationsBeyondNames := match ran.obligations? with
      | some (a, b) => obligations && obligationsDifferBeyondNames a b
      | none => false
    if let (true, some (a, b)) := (obligations, ran.obligations?) then
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.fren")
        (s!"-- fren_fuzz_frontends{flags mode} --obligations --seed {s}\n" ++ text)
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.cli") a
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.lean") b
    let elapsed := (← IO.monoMsNow) - t0
    let timedOut := (← Fren.Core.solverTimeoutMs) - solver0
    if elapsed > slowMs then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s, {timedOut / 1000}s of it in queries that timed out"
    let issues := found.map fun f => (knownIssue? mode (sharedStaticErrorLines ran.cli ran.hosted) found f).getD 0
    let status := if found.isEmpty then "ok" else if flaky then "inconclusive"
      else if mode.avoidKnown && issues.all (· != 0) then "known" else "differ"
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
    record run { seed := s, status, flags := flags mode, errors := errs.toList.eraseDups.toArray,
                 signatures := found.map signature, issues, ms := elapsed, solverTimeoutMs := timedOut, obligations,
                 obligationsBeyondNames }
    -- Between specs, a crash is no spec's.
    IO.FS.writeFile run.progress ""
  IO.cancel reporter
  let _ ← IO.wait reporter
  return 0

/-- Counts `x` in a tally. -/
def tally (xs : Array (String × Nat × Nat)) (x : String) (seed : Nat) : Array (String × Nat × Nat) :=
  match xs.findIdx? (·.1 == x) with
  | some k => xs.modify k fun (x, n, first) => (x, n + 1, first)
  | none => xs.push (x, 1, seed)

/-- The outcomes of a results file's text, one to a line. -/
def parseOutcomes (text : String) : Array Outcome :=
  (text.splitOn "\n").toArray.filterMap fun l => (Json.parse l >>= fromJson? : Except String Outcome).toOption

/-- The outcomes recorded so far in a run. -/
def outcomesOf (run : Run) : IO (Array Outcome) := do
  return parseOutcomes (← IO.FS.readFile run.results)

/-! ### The report of a run -/

/-- The file where a run writes the spec of an outcome, if it writes one. -/
def Outcome.file? (o : Outcome) : Option String :=
  match o.status with
  | "differ" => some s!"fe-seed{o.seed}.fren"
  | "known" | "inconclusive" => some s!"{o.status}-fe-seed{o.seed}.fren"
  | "crash" | "timeout" => some s!"{o.status}-seed{o.seed}.fren"
  | _ => none

/-- Whether an outcome fails the run: a difference of a kind that is not
known, a crash or a timeout. -/
def Outcome.fails (o : Outcome) : Bool := o.status ∈ ["differ", "crash", "timeout"]

/-- `s` in a cell of a Markdown table. -/
def mdCell (s : String) : String := (s.replace "\n" " ").replace "|" "\\|" |>.replace "<" "&lt;"

/-- The kinds of an outcome's differences, each with its issue, or as new
if it is of no known kind. -/
def Outcome.kinds (o : Outcome) : String :=
  "<br>".intercalate (o.signatures.toList.zipIdx.map fun (g, i) =>
    let issue := o.issues[i]?.getD 0
    (if issue == 0 then "**new**: " else s!"#{issue}: ") ++ mdCell g)

/-- A Markdown report of a run's outcomes, for the job's summary: how many
specs of each outcome; each one that fails it, with its kinds; each
known kind, with its issue, how many specs had it, and their seeds; and
each slow spec (`slowMs`), with how long it took in queries that timed
out. The specs are named as the run writes them. -/
def report (outcomes : Array Outcome) : String := Id.run do
  let n (st : String) := (outcomes.filter (·.status == st)).size
  let mut out := s!"{outcomes.size} specs: {n "differ"} differ in a kind that is not known, {n "crash"} crashed and \
    {n "timeout"} took too long, which fail the job; {n "known"} differ only in known kinds, and \
    {n "inconclusive"} only in inconclusive results.\n"
  let dumps := outcomes.filter (·.obligations)
  unless dumps.isEmpty do
    out := out ++ s!"\n{dumps.size} specs' obligations dumps differ, {(dumps.filter (·.status == "ok")).size} of them \
      where the messages agree, and {(dumps.filter (·.obligationsBeyondNames)).size} other than in the names of their \
      constants, which fails nothing (`obligations-seed*`).\n"
  let failed := outcomes.filter (·.fails) |>.qsort (·.seed < ·.seed)
  unless failed.isEmpty do
    out := out ++ "\n#### Failures\n\n| Seed | Flags | Outcome | Spec | Kinds |\n|---|---|---|---|---|\n"
    for o in failed do
      let fl := o.flags.trimAscii.toString
      let fl := if fl.isEmpty then "" else s!"`{fl}`"
      out := out ++ s!"| {o.seed} | {fl} | {o.status} | `{(o.file?).getD ""}` | {o.kinds} |\n"
  -- Each known kind, with its issue, and the seeds of the specs that have it.
  let mut kinds : Array (String × Nat × Array Nat) := #[]
  for o in outcomes.qsort (·.seed < ·.seed) do
    for (g, i) in o.signatures.toList.zipIdx do
      let issue := o.issues[i]?.getD 0
      if issue == 0 then continue
      kinds := match kinds.findIdx? fun (g', j, _) => g' == g && j == issue with
        | some k => kinds.modify k fun (g, j, seeds) =>
          (g, j, if seeds.contains o.seed then seeds else seeds.push o.seed)
        | none => kinds.push (g, issue, #[o.seed])
  unless kinds.isEmpty do
    out := out ++ "\n#### Known kinds\n\n| Kind | Issue | Specs | Seeds |\n|---|---|---|---|\n"
    for (g, issue, seeds) in kinds.qsort (·.2.2.size > ·.2.2.size) do
      let shown := ", ".intercalate ((seeds.extract 0 5).toList.map toString) ++ if seeds.size > 5 then ", …" else ""
      out := out ++ s!"| {mdCell g} | #{issue} | {seeds.size} | {shown} |\n"
  let inconclusive := outcomes.filter (·.status == "inconclusive")
  unless inconclusive.isEmpty do
    let seeds := ", ".intercalate (inconclusive.toList.map (toString ·.seed))
    out := out ++ s!"\nOnly in inconclusive results: seeds {seeds}.\n"
  -- The slow specs, slowest first, with the time in queries that timed out,
  -- which the time limit leaves out (`SpecTimeout.overdue`).
  let slow := outcomes.filter (·.ms > slowMs) |>.qsort (·.ms > ·.ms)
  unless slow.isEmpty do
    out := out ++ "\n#### Slow specs\n\n| Seed | Flags | Outcome | Time | In queries that timed out |\n|---|---|---|---|---|\n"
    for o in slow do
      let fl := o.flags.trimAscii.toString
      let fl := if fl.isEmpty then "" else s!"`{fl}`"
      out := out ++ s!"| {o.seed} | {fl} | {o.status} | {o.ms / 1000} s | {o.solverTimeoutMs / 1000} s |\n"
  return out

section
private def kn : Outcome :=
  { seed := 7, status := "known", flags := " --avoid-known", signatures := #["k"], issues := #[493] }
private def df : Outcome :=
  { seed := 5, status := "differ", flags := " --avoid-known", signatures := #["a|b", "k"], issues := #[0, 493] }
-- A clean run reports only its counts.
#guard report #[{ seed := 1, status := "ok" }] == "1 specs: 0 differ in a kind that is not known, 0 crashed and \
  0 took too long, which fail the job; 0 differ only in known kinds, and 0 only in inconclusive results.\n"
-- Specs whose obligations dumps differ are counted, but fail nothing.
#guard report #[{ seed := 1, status := "ok", obligations := true }, { seed := 2, status := "known", obligations := true }] ==
  "2 specs: 0 differ in a kind that is not known, 0 crashed and 0 took too long, which fail the job; 1 differ only in \
  known kinds, and 0 only in inconclusive results.\n\n2 specs' obligations dumps differ, 1 of them where the messages \
  agree, and 0 other than in the names of their constants, which fails nothing (`obligations-seed*`).\n"
-- A failing spec is listed with its kinds, new or known, and every known
-- kind with its issue and seeds, of the failing specs too.
#guard ((report #[kn, df, { seed := 9, status := "crash" }]).splitOn "\n").drop 6 == [
  "| 5 | `--avoid-known` | differ | `fe-seed5.fren` | **new**: a\\|b<br>#493: k |",
  "| 9 |  | crash | `crash-seed9.fren` |  |",
  "", "#### Known kinds", "", "| Kind | Issue | Specs | Seeds |", "|---|---|---|---|",
  "| k | #493 | 2 | 5, 7 |", ""]
#guard !kn.fails && df.fails
-- A slow spec is listed, with the time in queries that timed out.
#guard ((report #[{ seed := 3, status := "ok", ms := 41000, solverTimeoutMs := 40000 },
  { seed := 4, status := "ok", ms := 19000 }]).splitOn "\n").drop 2 == [
  "#### Slow specs", "", "| Seed | Flags | Outcome | Time | In queries that timed out |", "|---|---|---|---|---|",
  "| 3 |  | ok | 41 s | 40 s |", ""]
end

/-- The outcomes of every run whose results are in `dir`. -/
def outcomesIn (dir : System.FilePath) : IO (Array Outcome) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if e.fileName.startsWith "results-" && e.fileName.endsWith ".jsonl" then
      out := out ++ parseOutcomes (← IO.FS.readFile e.path)
  return out

/-- The most specs that one worker checks, a workaround for #650: a
worker slows down as it checks more, since the hosted front end's memory
grows by some 90 MB a spec (on macOS; the binary's stays level), so that
four workers of 100 specs would need more than a CI runner's 16 GB. On
CI, a worker's 97th and 98th specs, which take under a second on their
own, took 22 s and more than 30 s (seeds 1202247 and 1202248). A fresh
worker, which takes a few seconds to start, takes over after these. Once
#650 is fixed, this is to be raised, or the replacement dropped. -/
def workerSpecs : Nat := 25

/-- Runs workers until every seed is checked. The solver can abort the
process (a failed assertion in cvc5), so specs run in a worker, and a
crash is recorded as the outcome of the spec it was checking. A spec that
takes longer than `limit` seconds is stopped and recorded as a timeout.
Crashes and timeouts are findings: the run then exits nonzero. A worker
that dies while checking no spec, before its first or between two, is
blamed on none: the run resumes after the last spec recorded, or stops if
the worker recorded none. With `compareDumps`, the workers compare the
obligations dumps too (`worker`). -/
unsafe def mainFrontends (count seed : Nat) (dir : String) (mode : Mode) (limit : Nat) (compareDumps : Bool) :
    IO UInt32 := do
  let start ← IO.monoMsNow
  let run : Run := { dir, id := toString (← IO.Process.getPID) }
  IO.FS.writeFile run.results ""
  let mut next := seed
  -- The appended enumeration groups put more declarations in each spec;
  -- restart their workers sooner to keep the retained environments small.
  let perWorker := if mode.enumerationObligations || mode.enumerationRelations then workerSpecs / 2 else workerSpecs
  while next < seed + count do
    IO.FS.writeFile run.progress ""
    let batch := min (seed + count - next) perWorker
    let args := #["--worker", run.id, "--count", toString batch, "--seed", toString next, "--out", dir]
      ++ mode.args ++ (if compareDumps then #["--obligations"] else #[])
    for f in [run.solver, run.solver.addExtension "tmp"] do
      try IO.FS.removeFile f catch _ => pure ()
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .inherit }
    -- Wait, and stop the worker if one spec takes too long, leaving out its
    -- queries that timed out (`SpecTimeout.overdue`).
    let mut current := ""
    let mut since ← IO.monoMsNow
    let mut solver := 0
    let mut code? : Option UInt32 := none
    let mut timedOut := false
    let mut spent := (0, 0)
    repeat
      if let some c ← child.tryWait then code? := some c; break
      let now ← IO.monoMsNow
      let cur := (← (IO.FS.readFile run.progress).toBaseIO).toOption.getD current
      solver := (← (IO.FS.readFile run.solver).toBaseIO).toOption.bind (·.trimAscii.toString.toNat?) |>.getD solver
      let atStart := (((current.splitOn "\n")[1]?).bind (·.toNat?)).getD 0
      if cur != current then current := cur; since := now
      else if FrenTest.SpecTimeout.overdue limit (now - since) (solver - atStart) && !current.isEmpty then
        child.kill
        let _ ← child.wait
        timedOut := true
        spent := (now - since, solver - atStart)
        break
      IO.sleep 200
    if code? == some 0 then next := next + batch; continue
    let some failed := ((← IO.FS.readFile run.progress).splitOn "\n").head!.trimAscii.toString.toNat?
      | let done := (← outcomesOf run).filter (fun o => next ≤ o.seed && o.seed < seed + count)
        let last? := done.foldl (fun m o => some (max (m.getD o.seed) o.seed)) none
        let some last := last?
          | IO.eprintln s!"fren_fuzz_frontends: the worker for seed {next} exited ({code?.getD 0}) before checking any spec"
            return 2
        IO.eprintln s!"seed {last + 1}: the worker exited ({code?.getD 0}) between specs; resuming"
        next := last + 1
        continue
    let what := if timedOut then s!"took more than {limit}s, leaving out {spent.2 / 1000}s in queries that timed out"
      else s!"crashed (exit {code?.getD 0})"
    IO.eprintln s!"seed {failed}: the worker {what}"
    let text : String := mode.spec failed
    let kind := if timedOut then "timeout" else "crash"
    IO.FS.writeFile (dir / s!"{kind}-seed{failed}.fren") (s!"-- fren_fuzz_frontends{flags mode} --seed {failed}: {what}\n" ++ text)
    record run { seed := failed, status := kind, flags := flags mode, ms := spent.1, solverTimeoutMs := spent.2 }
    next := failed + 1
  let outcomes ← outcomesOf run
  for f in [run.progress, run.spec, run.solver, run.solver.addExtension "tmp"] do
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
  let dumps := outcomes.filter (·.obligations)
  if compareDumps then
    IO.eprintln s!"specs whose obligations dumps differ, which fails nothing: {dumps.size}, \
      {(dumps.filter (·.status == "ok")).size} of them where the messages agree, \
      {(dumps.filter (·.obligationsBeyondNames)).size} other than in the names of their constants \
      (`obligations-seed*` in {dir})"
  IO.eprintln s!"fren_fuzz_frontends: {outcomes.size} specs in {((← IO.monoMsNow) - start) / 1000}s, {n "differ"} where \
    the front ends differ, {n "inconclusive"} more only in inconclusive results, \
    {n "known"} more only in known kinds, {n "crash"} crashed, \
    {n "timeout"} took more than {limit}s outside queries that timed out (results in {run.results})"
  return if n "differ" + n "crash" + n "timeout" == 0 then 0 else 1

def usage : String :=
  "usage: fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--avoid-known] [--guards] [--sites] [--confirm] [--obligations] [--scrutinees] [--inductions] [--induction-forms] [--keywords] [--fact-scopes] [--induction-candidates] [--enumeration-obligations] [--enumeration-relations] [--unfoldings] [--datatype-elements] [--spec-timeout SECONDS]\n" ++
  "       fren_fuzz_frontends --files FILE...\n" ++
  "       fren_fuzz_frontends --report DIR\n" ++
  "       fren_fuzz_frontends [--avoid-known] [--guards] [--sites] [--confirm] [--scrutinees] [--inductions] [--induction-forms] [--keywords] [--fact-scopes] [--induction-candidates] [--enumeration-obligations] [--enumeration-relations] [--unfoldings] [--datatype-elements] --print SEED"

structure Opts where
  count : Nat := 100
  seed : Nat := 0
  dir : String := ".lake/fuzz"
  limit : Nat := 30
  worker? : Option String := none
  /-- Compare the obligations dumps too (`--obligations`, `worker`). -/
  compareDumps : Bool := false

unsafe def main (args : List String) : IO UInt32 := do
  if let "--files" :: files := args then
    IO.FS.createDirAll ".lake/fuzz"
    return ← mainFiles files ".lake/fuzz"
  let mode : Mode := { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards"
                       sites := args.contains "--sites", confirm := args.contains "--confirm", scrutinees := args.contains "--scrutinees"
                       inductions := args.contains "--inductions", inductionForms := args.contains "--induction-forms"
                       keywords := args.contains "--keywords", factScopes := args.contains "--fact-scopes"
                       inductionCandidates := args.contains "--induction-candidates"
                       enumerationObligations := args.contains "--enumeration-obligations"
                       enumerationRelations := args.contains "--enumeration-relations"
                       unfoldings := args.contains "--unfoldings", datatypeElements := args.contains "--datatype-elements" }
  let args := args.filter (fun a => a != "--avoid-known" && a != "--guards" && a != "--sites" && a != "--confirm" && a != "--scrutinees"
    && a != "--inductions" && a != "--induction-forms" && a != "--keywords" && a != "--fact-scopes" && a != "--induction-candidates"
    && a != "--enumeration-obligations" && a != "--enumeration-relations" && a != "--unfoldings" && a != "--datatype-elements")
  if let ["--report", dir] := args then
    IO.print (report (← outcomesIn dir))
    return 0
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
    | "--obligations" :: rest, o => parse rest { o with compareDumps := true }
    | _, _ => none
  let some o := parse args {} | IO.eprintln usage; return 2
  IO.FS.createDirAll o.dir
  match o.worker? with
  | some id => worker o.count o.seed { dir := o.dir, id } mode o.compareDumps
  | none => mainFrontends o.count o.seed o.dir mode o.limit o.compareDumps

end FrenTest.FuzzFrontends
