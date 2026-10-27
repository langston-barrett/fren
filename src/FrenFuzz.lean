-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-!
# Differential fuzzing (`Reqs/dev/Testing`)

`lake exe fren_fuzz [--count N] [--seed N] [--out DIR]` generates random
specs, checks each with `fren check`'s pipeline (cvc5, with its models
confirmed), and compares every result with one computed by brute force
from the evaluator (`FrenCli.Eval`), from the definitions of
`Reqs/Check`.

The specs stay in a fragment where brute force is exact: `Bool`s,
enumerations without payloads, ordered or not, the enumeration `P` with `Bool`
payloads, `Int`s that constraints named `range_*`
bound to `0..2`, an abstract type and a function from it to `Bool`, with
instances, `det out`s and global expectations. Every query's hypotheses
then bound every `Int` that matters, except the comparison sets of the
`range_*` constraints' own redundancy, which are not compared. Abstract
types need as many values as the variables of that type, and the
function's interpretations are enumerated over them.

Inputs may also be sets, relations and sequences of one element type, the
enumeration or `Bool`, which has finitely many values, so that brute force
enumerates every set and relation; `range_*` constraints bound sequences
to two elements. Each index is guarded, before or after it, so that the
evaluator knows every constraint's value, as the solver does whatever the
interpretation of an index out of range.
-/

open Lean FrenCli FrenCli.Eval

namespace FrenFuzz

open Fren.Core (CheckKind Verdict CheckResult)

/-! ## Generating specs -/

inductive GTy where
  | bool | int | enum | abs
  /-- The newtype `W` of `Int`. -/
  | wrap
  /-- The enumeration with payloads `P { A, B(Bool), C(Bool) }`, whose
  values' variants a clash note may give (`Reqs/Check#forced-outputs`). -/
  | pay
  /-- Of the spec's element type. -/
  | set | rel | seq
  deriving BEq, Inhabited

structure GVar where
  name : String
  ty : GTy
  isIn : Bool
  isPub : Bool := true
  isDet : Bool := false
  deriving Inhabited

structure GInst where
  name : String
  comp : Nat
  bindings : Array (String × String)
  deriving Inhabited

structure GComp where
  name : String
  vars : Array GVar
  inst? : Option GInst := none
  assumes : Array (String × String) := #[]
  reqs : Array (String × String) := #[]
  expects : Array (String × String) := #[]
  covers : Array (String × String) := #[]
  deriving Inhabited

def pick (xs : Array α) [Inhabited α] : R α := do return xs[← below xs.size]!

def chance (pct : Nat) : R Bool := do return (← below 100) < pct

/-- The element type of sets, relations and sequences: the enumeration
if there is one, else `Bool`. -/
def elemTy (useEnum : Bool) : GTy := if useEnum then .enum else .bool

def tyName (elem : GTy) (t : GTy) : String :=
  let base : GTy → String
    | .int => "Int" | .enum => "E" | .abs => "T" | .wrap => "W" | .pay => "P" | _ => "Bool"
  match t with
  | .set => s!"Set<{base elem}>"
  | .rel => s!"Rel<{base elem}, {base elem}>"
  | .seq => s!"Seq<{base elem}>"
  | t => base t

/-- A variable in scope: its text, type, and whether it may be a
function's argument. -/
structure Scope where
  vars : Array (String × GTy × Bool)
  nVariants : Nat
  /-- The enumeration is ordered, so its values are compared with orderings
  and have `min` and `max`. -/
  ordered : Bool := false
  hasFn : Bool
  elem : GTy := .bool
  /-- No `card`: the spec has a relation, and the solver does not combine
  counting with relational operators (`Reqs/Lang/Decidability#relations`). -/
  noCard : Bool := false

def Scope.of (sc : Scope) (t : GTy) : Array String := sc.vars.filterMap fun (n, t', _) => if t' == t then some n else none

def intTerm (sc : Scope) : R String := do
  let ns := sc.of .int
  if ns.isEmpty then return toString (← below 3)
  match ← below 5 with
  | 0 => return s!"({← pick ns} + {← pick ns})"
  | 1 => return s!"({← pick ns} - 1)"
  | 2 => return s!"2 * {← pick ns}"
  | 3 => return toString (← below 4)
  | _ => pick ns

/-- A value of the newtype `W` of `Int`, of its variables, `W(e)`, or a
sum or difference of two. -/
def wrapTerm (sc : Scope) : R String := do
  let ws := sc.of .wrap
  if ws.isEmpty then return s!"W({← below 3})"
  match ← below 5 with
  | 0 => return s!"({← pick ws} + {← pick ws})"
  | 1 => return s!"({← pick ws} - W(1))"
  | 2 => return s!"W({← intTerm sc})"
  | 3 => return s!"W({← below 3})"
  | _ => pick ws

/-- A value of `P`: a variable, or a literal, whose payload may be an
expression. -/
def payTerm (sc : Scope) (b : String) : R String := do
  let ps := sc.of .pay
  if !ps.isEmpty && (← chance 50) then return ← pick ps
  match ← below 3 with
  | 0 => return "P::A"
  | 1 => return s!"P::B({b})"
  | _ => return s!"P::C({b})"

/-- A pattern of `P`: of one variant, or two, with `_` or a literal for
its payload. -/
def payPattern : R String := do
  let one : R String := do
    match ← below 5 with
    | 0 => return "P::A"
    | 1 => return "P::B(_)"
    | 2 => return "P::C(_)"
    | _ => return s!"P::{← pick #["B", "C"]}({← pick #["true", "false"]})"
  -- Of two variants, so that neither alternative is unreachable.
  if ← chance 30 then
    let (a, b) ← pick #[("P::A", "P::B(_)"), ("P::B(true)", "P::C(_)"), ("P::C(false)", "P::A")]
    return s!"{a} | {b}"
  one

/-- A value of the element type. -/
def elemTerm (sc : Scope) : R String := do
  let vs := sc.of sc.elem
  if vs.isEmpty || (← chance 50) then
    if sc.elem == .enum then return s!"E::V{← below sc.nVariants}"
    return ← pick #["true", "false"]
  pick vs

/-- A set: a variable, or a literal of zero to two elements. -/
def setTerm (sc : Scope) : R String := do
  let vs := sc.of .set
  if !vs.isEmpty && (← chance 60) then return ← pick vs
  match ← below 3 with
  | 0 => return "{}"
  | 1 => return s!"\{{← elemTerm sc}}"
  | _ => return s!"\{{← elemTerm sc}, {← elemTerm sc}}"

/-- A relation: a variable, a literal, or a relational operator on one. -/
def relTerm (sc : Scope) : R String := do
  let vs := sc.of .rel
  let pair : R String := do return s!"({← elemTerm sc}, {← elemTerm sc})"
  if vs.isEmpty || (← chance 20) then
    if ← chance 30 then return "{}"
    return s!"\{{← pair}}"
  let r ← pick vs
  match ← below 6 with
  | 0 => return s!"{r}.inverse"
  | 1 => return s!"{r}.closure"
  | 2 => return s!"({r} join {← pick vs})"
  | _ => return r

/-- A sequence: a variable, or a literal of zero to two elements. -/
def seqTerm (sc : Scope) : R String := do
  let vs := sc.of .seq
  if !vs.isEmpty && (← chance 70) then return ← pick vs
  match ← below 3 with
  | 0 => return "[]"
  | 1 => return s!"[{← elemTerm sc}]"
  | _ => return s!"[{← elemTerm sc}, {← elemTerm sc}]"

/-- A constraint on sets, relations or sequences. -/
def collectionAtom (sc : Scope) (t : GTy) : R String := do
  match t with
  | .set =>
    let s ← pick (sc.of .set)
    match ← below 6 with
    | 0 => return s!"{← elemTerm sc} in {s}"
    | 1 => return s!"{s} subset {← setTerm sc}"
    | 2 => return s!"{s} {← pick #["=", "!="]} {← setTerm sc}"
    | 3 => return s!"{← elemTerm sc} in ({s} {← pick #["union", "inter", "minus"]} {← setTerm sc})"
    | _ =>
      if sc.noCard then return s!"{← elemTerm sc} in {s}"
      return s!"{s}.card {← pick #["=", "<=", ">="]} {← below 3}"
  | .rel =>
    let r ← pick (sc.of .rel)
    match ← below 6 with
    | 0 => return s!"{← elemTerm sc} in {r}.{← pick #["domain", "range"]}"
    | 1 => return s!"{r}.image(\{{← elemTerm sc}}) subset {← setTerm sc}"
    | 2 => return s!"{r} {← pick #["=", "subset"]} {← relTerm sc}"
    | _ => return s!"({← elemTerm sc}, {← elemTerm sc}) in {← relTerm sc}"
  | _ =>
    let q ← pick (sc.of .seq)
    let k ← below 2
    match ← below 8 with
    | 0 => return s!"{q}.len {← pick #["=", "<", ">="]} {← below 3}"
    | 1 => return s!"{q} {← pick #["=", "!="]} {← seqTerm sc}"
    | 2 => return s!"{q}.{← pick #["starts_with?", "ends_with?"]}([{← elemTerm sc}])"
    | 3 => return s!"{q}.update({k}, {← elemTerm sc}) = {← seqTerm sc}"
    -- Guarded indexes, whose definedness holds, and a bound after the
    -- index, whose definedness fails.
    | 4 => return s!"({k} < {q}.len and {q}[{k}] = {← elemTerm sc})"
    | 5 => return s!"({q}.len <= {k} or {q}[{k}] != {← elemTerm sc})"
    | 6 => return s!"({q}[{k}] = {← elemTerm sc} and {k} < {q}.len)"
    | _ => return s!"(when {q}.len > {k}, {q}[{k}] = {← elemTerm sc})"

partial def genBool (sc : Scope) (depth : Nat) : R String := do
  let atom : R String := do
    let mut kinds := #[0]
    unless (sc.of .bool).isEmpty do kinds := kinds ++ #[1, 1, 1]
    unless (sc.of .int).isEmpty do kinds := kinds ++ #[2, 2]
    unless (sc.of .enum).isEmpty do kinds := kinds ++ #[3, 3]
    unless (sc.of .abs).isEmpty do kinds := kinds.push 4
    let args := sc.vars.filterMap fun (n, t, a) => if t == .abs && a then some n else none
    if sc.hasFn && !args.isEmpty then kinds := kinds ++ #[5, 5]
    unless (sc.of .set).isEmpty do kinds := kinds ++ #[6, 6]
    unless (sc.of .rel).isEmpty do kinds := kinds ++ #[7, 7]
    unless (sc.of .seq).isEmpty do kinds := kinds ++ #[8, 8]
    unless (sc.of .wrap).isEmpty do kinds := kinds ++ #[9, 9]
    unless (sc.of .pay).isEmpty do kinds := kinds ++ #[10, 10, 10]
    match ← pick kinds with
    | 1 =>
      -- A `match` on a `Bool`, with literal patterns, sometimes with a
      -- guard on `true` that falls through to its arm without one, or
      -- with only guarded arms, which the completeness check asks about.
      if depth > 0 && (← chance 15) then
        let b ← pick (sc.of .bool)
        if ← chance 40 then
          let g ← genBool sc (depth - 1)
          if ← chance 50 then
            return s!"(match {b} \{ true if {g} => {← genBool sc (depth - 1)}, true => {← genBool sc (depth - 1)}, false => {← genBool sc (depth - 1)} })"
          return s!"(match {b} \{ true if {g} => {← genBool sc (depth - 1)}, false if {← genBool sc (depth - 1)} => {← genBool sc (depth - 1)}, _ => {← genBool sc (depth - 1)} })"
        return s!"(match {b} \{ true => {← genBool sc (depth - 1)}, false => {← genBool sc (depth - 1)} })"
      -- A table over a `Bool`, whose arms of `true` have guards that may
      -- overlap, which the disjointness check asks about, or leave a case,
      -- which the completeness check asks about.
      if depth > 0 && (← chance 10) then
        let b ← pick (sc.of .bool)
        let g ← genBool sc (depth - 1)
        let h ← if ← chance 50 then pure s!"not ({g})" else genBool sc (depth - 1)
        return s!"(table {b} \{ true if {g} => {← genBool sc (depth - 1)}, true if {h} => {← genBool sc (depth - 1)}, false => {← genBool sc (depth - 1)} })"
      -- A table, whose rows are guarded arms, sometimes without `_`.
      if depth > 0 && (← chance 10) then
        let rows := #[s!"{← genBool sc (depth - 1)} => {← genBool sc (depth - 1)}",
          s!"{← genBool sc (depth - 1)} => {← genBool sc (depth - 1)}"]
        let wild ← if ← chance 50 then pure #[s!"_ => {← genBool sc (depth - 1)}"] else pure #[]
        let rows := rows ++ wild
        return s!"table \{ {", ".intercalate rows.toList} }"
      pick (sc.of .bool)
    | 2 =>
      -- A pattern test of a literal or a range, or a `match` on an `Int`.
      if ← chance 20 then
        let (a, b) := (← below 4, ← below 4)
        let (lo, hi) : Int × Int := ((min a b : Nat) - 1, max a b)
        let p ← pick #[toString lo, s!"{lo}..={hi}", s!"{lo}..{hi + 1}", s!"{lo}..", s!"..={hi}"]
        return s!"{← pick (sc.of .int)} is {p}"
      if depth > 0 && (← chance 10) then
        let k ← below 3
        return s!"(match {← pick (sc.of .int)} \{ {k} => {← genBool sc (depth - 1)}, {k + 1} | -1 => {← genBool sc (depth - 1)}, _ => {← genBool sc (depth - 1)} })"
      -- A table over an `Int`, whose ranges do not overlap, and whose arms
      -- of one range have guards, which the disjointness check asks about.
      if depth > 0 && (← chance 10) then
        let k ← below 3
        let g ← genBool sc (depth - 1)
        let h ← if ← chance 50 then pure s!"not ({g})" else genBool sc (depth - 1)
        return s!"(table {← pick (sc.of .int)} \{ ..={k} => {← genBool sc (depth - 1)}, {k + 1}..={k + 2} if {g} => {← genBool sc (depth - 1)}, {k + 1}..={k + 2} if {h} => {← genBool sc (depth - 1)}, {k + 3}.. => {← genBool sc (depth - 1)} })"
      return s!"{← intTerm sc} {← pick #["=", "!=", "<", "<=", ">", ">="]} {← intTerm sc}"
    | 3 =>
      let es := sc.of .enum
      -- A pattern test, of one or two distinct variants.
      if ← chance 25 then
        let (a, b) := (← below sc.nVariants, ← below sc.nVariants)
        let alts := if a == b then [a] else [a, b]
        return s!"{← pick es} is {" | ".intercalate (alts.map (s!"E::V{·}"))}"
      let rhs ← if ← chance 60 then pure s!"E::V{← below sc.nVariants}" else pick es
      if sc.ordered && (← chance 50) then
        -- An ordering, a chained comparison, or `min` or `max`.
        match ← below 3 with
        | 0 => return s!"{← pick es} {← pick #["<", "<=", ">", ">="]} {rhs}"
        | 1 => return s!"E::V0 {← pick #["<", "<="]} {← pick es} {← pick #["<", "<="]} {rhs}"
        | _ => return s!"{← pick es}.{← pick #["min", "max"]}({rhs}) = E::V{← below sc.nVariants}"
      return s!"{← pick es} {← pick #["=", "!="]} {rhs}"
    | 4 => let ts := sc.of .abs; return s!"{← pick ts} {← pick #["=", "!="]} {← pick ts}"
    | 5 => return s!"p?({← pick args})"
    | 6 => collectionAtom sc .set
    | 7 => collectionAtom sc .rel
    | 8 => collectionAtom sc .seq
    | 9 =>
      if ← chance 30 then return s!"{← pick (sc.of .wrap)}.0 {← pick #["=", "<", ">="]} {← intTerm sc}"
      return s!"{← wrapTerm sc} {← pick #["=", "!=", "<", "<=", ">", ">="]} {← wrapTerm sc}"
    | 10 =>
      let x ← pick (sc.of .pay)
      -- A pattern test, an equation, or a `match` that reads a payload.
      match ← below 4 with
      | 0 | 1 => return s!"{x} is {← payPattern}"
      | 2 =>
        let b ← if depth > 0 then genBool sc (depth - 1) else pick #["true", "false"]
        return s!"{x} {← pick #["=", "!="]} {← payTerm sc b}"
      | _ =>
        let rest ← if depth > 0 then genBool sc (depth - 1) else pick #["true", "false"]
        return s!"(match {x} \{ P::B(y?) => y?, P::C(y?) => not y?, _ => {rest} })"
    | _ => pick #["true", "false"]
  if depth == 0 then return ← atom
  match ← below 10 with
  | 0 => return s!"({← genBool sc (depth - 1)} and {← genBool sc (depth - 1)})"
  | 1 => return s!"({← genBool sc (depth - 1)} or {← genBool sc (depth - 1)})"
  | 2 => return s!"not ({← genBool sc (depth - 1)})"
  | 3 => return s!"({← genBool sc (depth - 1)} iff {← genBool sc (depth - 1)})"
  | 4 => return s!"(if {← genBool sc (depth - 1)} then {← genBool sc (depth - 1)} else {← genBool sc (depth - 1)})"
  | 5 =>
    -- A cardinality operator, of one to three arguments.
    let mut args := #[← genBool sc (depth - 1)]
    for _ in [0:← below 3] do args := args.push (← genBool sc (depth - 1))
    return s!"{← pick #["exactly_one?", "at_most_one?"]}({", ".intercalate args.toList})"
  -- A quantifier over the enumeration, or over `Bool`, whose bound name is
  -- named after the depth, so that nested ones do not shadow each other.
  | 6 =>
    let enum := sc.elem == .enum && (← chance 70)
    let (x, t) := if enum then (s!"x{depth}", GTy.enum) else (s!"x{depth}?", GTy.bool)
    let body ← genBool { sc with vars := sc.vars.push (x, t, false) } (depth - 1)
    return s!"({← pick #["forall", "exists"]} ({x}: {if enum then "E" else "Bool"}), {body})"
  -- A table: complete by its last row's being the negation of the first,
  -- with a `_` row after rows that may overlap, or with rows that may
  -- leave a case, where its value is the interpretation's, which brute
  -- force enumerates.
  | 7 =>
    let c ← genBool sc (depth - 1)
    match ← below 3 with
    | 0 => return s!"table \{ {c} => {← genBool sc (depth - 1)}, not ({c}) => {← genBool sc (depth - 1)} }"
    | 1 => return s!"table \{ {c} => {← genBool sc (depth - 1)}, {← genBool sc (depth - 1)} => {← genBool sc (depth - 1)}, _ => {← genBool sc (depth - 1)} }"
    | _ => return s!"table \{ {c} => {← genBool sc (depth - 1)}, {← genBool sc (depth - 1)} => {← genBool sc (depth - 1)} }"
  | _ => atom

/-- A constraint, often with a trigger. -/
def genConstraint (sc : Scope) (trig : Scope) : R String := do
  match ← below 10 with
  | 0 | 1 | 2 | 3 | 4 => return s!"when {← genBool trig 1}, {← genBool sc 1}"
  | 5 => return s!"unless {← genBool trig 1}, {← genBool sc 1}"
  | 6 => return s!"when {← genBool trig 0}, when {← genBool trig 0}, {← genBool sc 1}"
  | _ => genBool sc 2

def varName (t : GTy) (isIn : Bool) (k : Nat) : String :=
  match t, isIn with
  | .bool, true => s!"a{k}?" | .bool, false => s!"b{k}?"
  | .int, true => s!"n{k}" | .int, false => s!"k{k}"
  | .enum, true => s!"m{k}" | .enum, false => s!"e{k}"
  | .abs, _ => s!"t{k}"
  | .wrap, true => s!"u{k}" | .wrap, false => s!"v{k}"
  | .pay, true => s!"i{k}" | .pay, false => s!"o{k}"
  | .set, _ => s!"s{k}" | .rel, _ => s!"rel{k}" | .seq, _ => s!"q{k}"

def genComp (idx : Nat) (prev : Array GComp) (useEnum useAbs useWrap usePay : Bool) (nVariants : Nat) (ordered : Bool)
    (collections : Array GTy) : R GComp := do
  let wraps := if useWrap then #[GTy.wrap] else #[]
  let pays := if usePay then #[GTy.pay] else #[]
  let tys := #[GTy.bool, .bool, .int] ++ (if useEnum then #[GTy.enum] else #[]) ++ (if useAbs then #[GTy.abs] else #[])
    ++ wraps ++ pays ++ collections
  -- Outputs of `P` more often, for clashes of variants.
  let outTys := #[GTy.bool, .int] ++ (if useEnum then #[GTy.enum] else #[]) ++ wraps ++ pays ++ pays
  let mut vars : Array GVar := #[]
  for k in [0:(← below 3) + 1] do
    let t ← pick tys
    -- At most one of each collection, whose domains are large.
    if collections.contains t && vars.any (·.ty == t) then continue
    vars := vars.push { name := varName t true k, ty := t, isIn := true }
  for k in [0:(← below 2) + 1] do
    let t ← pick outTys
    vars := vars.push { name := varName t false k, ty := t, isIn := false, isPub := ← chance 80, isDet := ← chance 40 }
  -- An instance of an earlier comp, with every input bound.
  let mut inst? := none
  if !prev.isEmpty && (← chance 60) then
    let ci ← below prev.size
    let d := prev[ci]!
    for v in d.vars do
      if v.isIn && v.ty == .abs && !vars.any (fun u => u.isIn && u.ty == .abs) then
        vars := vars.push { name := varName .abs true 9, ty := .abs, isIn := true }
    let insc : Scope := { vars := vars.filter (·.isIn) |>.map (fun v => (v.name, v.ty, true)), nVariants, ordered, hasFn := useAbs
                          elem := elemTy useEnum, noCard := collections.contains .rel }
    let mut bs := #[]
    for v in d.vars do
      unless v.isIn do continue
      let e ← match v.ty with
        | .bool => genBool insc 1
        | .int => if (insc.of .int).isEmpty || (← chance 30) then (toString <$> below 3) else pick (insc.of .int)
        | .enum => if (insc.of .enum).isEmpty || (← chance 30) then pure s!"E::V{← below nVariants}" else pick (insc.of .enum)
        | .abs => pick (insc.of .abs)
        | .wrap => if (insc.of .wrap).isEmpty || (← chance 30) then pure s!"W({← below 3})" else pick (insc.of .wrap)
        | .pay => payTerm insc (← pick #["true", "false"])
        | .set => setTerm insc
        | .rel => relTerm insc
        | .seq => seqTerm insc
      bs := bs.push (v.name, e)
    inst? := some { name := "w", comp := ci, bindings := bs }
  let own := vars.map fun v => (v.name, v.ty, v.isIn)
  let instVars := match inst? with
    | some i => prev[i.comp]!.vars.filter (fun v => v.isIn || v.isPub) |>.map fun v => (s!"w.{v.name}", v.ty, true)
    | none => #[]
  let elem := elemTy useEnum
  let noCard := collections.contains .rel
  let inputs : Scope := { vars := own.filter (·.2.2), nVariants, ordered, hasFn := useAbs, elem, noCard }
  let all : Scope := { vars := own ++ instVars, nVariants, ordered, hasFn := useAbs, elem, noCard }
  let mut assumes := #[]
  let mut reqs := #[]
  for v in vars do
    if v.ty == .int then
      if v.isIn then assumes := assumes.push (s!"range_{v.name}", s!"0 <= {v.name} and {v.name} <= 2")
      else reqs := reqs.push (s!"range_{v.name}", s!"0 <= {v.name} and {v.name} <= 2")
    if v.ty == .wrap then
      if v.isIn then assumes := assumes.push (s!"range_{v.name}", s!"W(0) <= {v.name} <= W(2)")
      else reqs := reqs.push (s!"range_{v.name}", s!"W(0) <= {v.name} <= W(2)")
    if v.ty == .seq then assumes := assumes.push (s!"range_{v.name}", s!"{v.name}.len <= 2")
  for k in [0:← below 2] do assumes := assumes.push (s!"as{k}", ← genBool inputs 1)
  for k in [0:(← below 3) + 1] do reqs := reqs.push (s!"r{k}", ← genConstraint all all)
  let mut expects := #[]
  for k in [0:← below 3] do expects := expects.push (s!"x{k}", ← genConstraint all all)
  let mut covers := #[]
  for k in [0:← below 3] do covers := covers.push (s!"g{k}", ← genBool all 1)
  return { name := s!"c{idx}", vars, inst?, assumes, reqs, expects, covers }

structure GSpec where
  text : String

def genSpec : R GSpec := do
  let useEnum ← chance 60
  let useAbs ← chance 35
  let useWrap ← chance 35
  let usePay ← chance 35
  let genericPay ← chance 50
  let nVariants := (← below 2) + 2
  let ordered ← chance 50
  let mut collections := #[]
  for t in #[GTy.set, .rel, .seq] do
    -- A relation over three values has 512 values, too many to evaluate
    -- `closure` and `join` on for every behaviour.
    if t == .rel && useEnum && nVariants > 2 then continue
    if ← chance 40 then collections := collections.push t
  let mut out := "mod fz\n\n"
  if useEnum then
    out := out ++ s!"pub {if ordered then "ordered " else ""}enum E \{ {", ".intercalate ((List.range nVariants).map (s!"V{·}"))} }\n"
  if useAbs then out := out ++ "pub type T\npub fn p?(T)\n"
  if useWrap then out := out ++ "pub ordered struct W(Int)\n"
  -- Sometimes generic, declared as `P<Bool>`, whose values are the same.
  if usePay then
    out := out ++ (if genericPay then "pub enum P<X> { A, B(X), C(Bool) }\n" else "pub enum P { A, B(Bool), C(Bool) }\n")
  let mut comps : Array GComp := #[]
  for i in [0:(← below 2) + 1] do
    comps := comps.push (← genComp i comps useEnum useAbs useWrap usePay nVariants ordered collections)
  for c in comps do
    out := out ++ s!"\npub comp {c.name} \{\n"
    for v in c.vars do
      let ty := if v.ty == .bool then "" else if v.ty == .pay && genericPay then ": P<Bool>"
        else s!": {tyName (elemTy useEnum) v.ty}"
      let mods := if v.isIn then "in" else s!"{if v.isPub then "pub " else ""}{if v.isDet then "det " else ""}out"
      out := out ++ s!"    {mods} {v.name}{ty}\n"
    if let some i := c.inst? then
      let bs := ", ".intercalate (i.bindings.toList.map fun (x, e) => s!"{x} := {e}")
      out := out ++ s!"    inst {i.name}: {comps[i.comp]!.name} \{ {bs} }\n"
    for (n, e) in c.assumes do out := out ++ s!"    assume {n}: {e}\n"
    for (n, e) in c.reqs do out := out ++ s!"    ensure {n}: {e}\n"
    for (n, e) in c.expects do out := out ++ s!"    expect {n}: {e}\n"
    for (n, e) in c.covers do out := out ++ s!"    cover {n}: {e}\n"
    out := out ++ "}\n"
  -- A global expectation over two behaviours of one comp.
  if ← chance 40 then
    let c ← pick comps
    let shown := c.vars.filter (fun v => v.isIn || v.isPub)
    let sc : Scope := { vars := shown.flatMap (fun v => #[(s!"x.{v.name}", v.ty, v.isIn), (s!"y.{v.name}", v.ty, v.isIn)])
                        nVariants, ordered, hasFn := useAbs, elem := elemTy useEnum, noCard := collections.contains .rel }
    let ins := shown.filter (·.isIn)
    let same := " and ".intercalate (ins.toList.map fun v => s!"x.{v.name} = y.{v.name}")
    let body ← if (← chance 50) && !ins.isEmpty then
        let o := shown.filter (!·.isIn)
        if o.isEmpty then pure s!"when {same}, {← genBool sc 1}"
        else do let v ← pick o; pure s!"when {same}, x.{v.name} = y.{v.name}"
      else genConstraint sc sc
    out := out ++ s!"\nexpect g: forall (x y: {c.name}), {body}\n"
  return { text := out }

/-! ## Brute force -/

/-- Every subset of `xs`. -/
def subsets (xs : Array Val) : Array Val :=
  (xs.foldl (fun acc x => acc ++ acc.map (·.push x)) #[#[]]).map Val.setOf

partial def domain (sp : Spec) (size : Nat) : VTy → Array Val
  | .bool => #[.bool false, .bool true]
  | .int => #[.int 0, .int 1, .int 2]
  -- The generator emits no `Nat`s, but a `Nat` is an `Int` of at least 0.
  | .nat => #[.int 0, .int 1, .int 2]
  -- The generator emits no strings.
  | .string => #[]
  -- A newtype's values are its underlying type's.
  | .newtype _ u => domain sp size u
  | .set t => subsets (domain sp size t)
  | .rel a b => subsets ((domain sp size a).flatMap fun x => (domain sp size b).map (.pair x ·))
  -- Up to two elements, as the `range_*` constraints bound them.
  | .seq t =>
    let xs := domain sp size t
    #[.seq #[]] ++ xs.map (.seq #[·]) ++ xs.flatMap fun x => xs.map fun y => .seq #[x, y]
  | .abstract s => (Array.range size).map (.abs s)
  -- Each variant with each value of its payload, which the generator
  -- makes of finite types (`P`'s `Bool`s), with a generic type's
  -- arguments for its parameters.
  | .data p args => match sp.data.find? p with
    | some d => (d.ctors.zipIdx).flatMap fun (c, i) =>
      (c.fields.foldl (init := #[#[]]) fun pre (_, t) =>
        pre.flatMap fun xs => (domain sp size (t.subst args)).map xs.push).map (.ctor p i ·)
    | none => #[]
  -- Substituted by the type's arguments, above.
  | .param _ => #[]

/-- Every interpretation of the functions, whose parameters are abstract
types of `size` values. -/
def interps (sp : Spec) (size : Nat) : Array Interp := Id.run do
  let fs := sp.funs.toList.toArray
  let mut tables : Array (Std.HashMap (Name × Array Val) Val) := #[{}]
  for (f, ps, r) in fs do
    let mut points : Array (Array Val) := #[#[]]
    for t in ps do points := points.flatMap fun pre => (domain sp size t).map pre.push
    for pt in points do
      tables := tables.flatMap fun tb => (domain sp size r).map fun v => tb.insert (f, pt) v
  return tables.map fun tb => { fn := fun f args => tb[(f, args)]? }

/-- Every assignment of `vars` that makes `atoms` true. -/
partial def models (sp : Spec) (size : Nat) (I : Interp) (vars : Array (Name × VTy)) (atoms : Array Atom)
    (env : Env := {}) : Array Env :=
  let rec go (i : Nat) (env : Env) : Array Env :=
    if atoms.any (·.eval I env.look == some false) then #[]
    else if h : i < vars.size then
      let (x, t) := vars[i]
      if env.contains x then go (i + 1) env
      else (domain sp size t).flatMap fun v => go (i + 1) (env.insert x v)
    else if allHold I env.look atoms == some true then #[env] else #[]
  go 0 env

def holds (I : Interp) (env : Env) (a : Atom) : Bool := a.eval I env.look == some true

/-- How many assignments and interpretations brute force tries, at most. -/
def space (sp : Spec) (c : Comp) : Nat :=
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  -- Evaluating an assignment costs about as much as its collections have
  -- members.
  let members (t : VTy) : Nat := match t with
    | .set e => (domain sp size e).size
    | .rel a b => (domain sp size a).size * (domain sp size b).size
    | .seq _ => 2
    | _ => 0
  (interps sp size).size * flat.foldl (fun n v => n * (domain sp size v.ty).size) 1
    * (1 + flat.foldl (fun n v => n + members v.ty) 0)

def maxSpace : Nat := 3000000

structure Oracle where
  /-- The verdict of each result that brute force decides, by key. -/
  verdicts : Array ((CheckKind × Option Name × Option (Name × Name)) × Verdict) := #[]
  /-- Results that the checks must not report: redundancy that is not asked. -/
  notAsked : Array Name := #[]

def isRange (n : Name) : Bool := n.toString.startsWith "range_"

/-- The key of a question about a table's rows in the item `p`: where it is
reported, and for disjointness, the earlier row. -/
def tableKey (p : Name) (pos : Nat) (rows? : Option (Nat × Nat)) : Name :=
  .num (.num p pos) ((rows?.map (·.1)).getD 0)

def oracle (sp : Spec) (c : Comp) : Oracle := Id.run do
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  let Is := interps sp size
  let order := sp.order c
  let ownIns := c.vars.filter (·.role == .input) |>.map fun v => (v.name, v.ty)
  let atom (p : Constraint) (e := p.e) : Atom := { label := p.name, pfx := .anonymous, e }
  let as := c.ofKind .assume
  let rs := c.ofKind .ensure
  let es := c.ofKind .expect
  let gs := c.ofKind .cover
  let A := as.map (atom ·)
  let R := rs.map (atom ·)
  let Iw := sp.insts c
  let full := A ++ Iw ++ R
  let mut out : Oracle := {}
  let put (o : Oracle) (k : CheckKind) (p : Option Name) (v : Verdict) (t : Option (Name × Name) := none) :=
    { o with verdicts := o.verdicts.push ((k, p, t), v) }
  let pass (b : Bool) : Verdict := if b then .pass else .fail
  let MF := Is.map fun I => (I, models sp size I order full)
  let constraintsWithTrig := (c.constraints.filter fun p => p.kind == .ensure || p.kind == .expect).filterMap fun p =>
    p.e.trigger?.map (p, ·)
  -- Definedness, of each index by its position, and the completeness and
  -- disjointness of each table and `match`, by where it is reported and the
  -- earlier row (`tableKey`): in every model of `ms`, its goal holds, or of
  -- `rms` for disjointness. The reachability of an arm or a row: in some
  -- model of `rms`, the models without the constraint itself
  -- (`Comp.reachHyps`), its goal fails.
  let defined (o : Oracle) (p : Name) (e : Ex) (ms : Array (Interp × Array Env))
      (rms : Array (Interp × Array Env) := ms) : Oracle :=
    let always (ms : Array (Interp × Array Env)) (g : Ex) :=
      ms.all fun (I, ms) => ms.all (holds I · { label := p, pfx := .anonymous, e := g })
    let o := e.indexGoals.foldl (init := o) fun o (pos, g) => put o .definedness (some (.num p pos)) (pass (always ms g))
    -- Disjointness, as reachability, without the constraint itself
    -- (`Comp.caseHyps`): in every model of `rms`, its goal holds.
    let o := e.tableGoals.foldl (init := o) fun o (pos, q, g) =>
      if q.kind == .reachability then o
      else put o q.kind (some (tableKey p pos q.rows?)) (pass (always (if q.kind == .disjointness then rms else ms) g))
    -- A case is reachable where some mention of a `let` or `where` name
    -- reaches it (`Fren.Core.mergeReach`): one verdict for all its goals.
    let reach := e.tableGoals.filter (·.2.1.kind == .reachability)
    let keys := reach.foldl (init := (#[] : Array (Nat × Fren.Core.TableGoal))) fun ks (pos, q, _) =>
      if ks.contains (pos, q) then ks else ks.push (pos, q)
    keys.foldl (init := o) fun o (pos, q) =>
      let gs := reach.filter (fun (p', q', _) => p' == pos && q' == q)
      put o .reachability (some (tableKey p pos q.rows?)) (pass (gs.any fun (_, _, g) => !always rms g))
  if c.isGlobal then
    let MG := Is.map fun I => (I, models sp size I order (sp.insts c))
    for e in es do out := put out .expect (some e.name) (pass (MG.all fun (I, ms) => ms.all (holds I · (atom e))))
    for e in es do out := defined out e.name e.e MG
    for (p, t) in constraintsWithTrig do
      out := put out .vacuity (some p.name) (pass (MG.any fun (I, ms) => ms.any (holds I · (atom p t))))
    return out
  -- Realizability.
  let assumeSat := Is.any fun I => !(models sp size I ownIns A).isEmpty
  let realizable := assumeSat && Is.all fun I =>
    let noOut := order.filter fun (x, _) => !(c.vars.any fun v => v.role == .output && v.name == x)
    let ms := (MF.find? (fun _ => true)).map (·.2) |>.getD #[]
    let _ := ms
    let full := (models sp size I order full)
    (models sp size I noOut (A ++ Iw)).all fun m =>
      full.any fun f => noOut.all fun (x, _) => f[x]? == m[x]?
  out := put out .realizable none (pass realizable)
  -- Instance assumptions.
  for i in c.insts, k in [0:c.insts.size] do
    let some d := sp.comp? i.comp | continue
    let before := (c.insts.extract 0 k).flatMap fun j => (sp.comp? j.comp).map (sp.order · j.name) |>.getD #[]
    let ins := d.vars.filter (·.role == .input) |>.map fun v => (i.name ++ v.name, v.ty)
    let vars := ownIns ++ before ++ ins
    let hyps := A ++ sp.insts c k ++ bindingAtoms .anonymous i
    for a in d.ofKind .assume do
      let goal : Atom := { label := a.name, pfx := i.name, e := a.e }
      let ok := Is.all fun I => (models sp size I vars hyps).all (holds I · goal)
      out := put out .inst (some i.name) (pass ok) (some (d.path, a.name))
    let ms := Is.map fun I => (I, models sp size I (ownIns ++ before) (A ++ sp.insts c k))
    for (_, e) in i.bindings do out := defined out i.name e ms
  for a in as, k in [0:as.size] do
    let others := (A.extract 0 k) ++ A.extract (k + 1)
    out := defined out a.name a.e (Is.map fun I => (I, models sp size I ownIns others))
  for p in es ++ gs do out := defined out p.name p.e MF
  for p in rs do
    let others := A ++ Iw ++ R.filter (·.label != p.name)
    out := defined out p.name p.e MF (Is.map fun I => (I, models sp size I order others))
  for e in es do
    out := put out .expect (some e.name) (pass (MF.all fun (I, ms) => ms.all (holds I · (atom e))))
  -- A cover goal: some behaviour satisfies it (`check::cover_goal`).
  for g in gs do
    out := put out .cover (some g.name) (pass (MF.any fun (I, ms) => ms.any (holds I · (atom g))))
  let mut vacuous : Array Name := #[]
  for (p, t) in constraintsWithTrig do
    let ok := MF.any fun (I, ms) => ms.any (holds I · (atom p t))
    unless ok do vacuous := vacuous.push p.name
    out := put out .vacuity (some p.name) (pass ok)
  -- Redundancy, but not of `range_*` constraints.
  for a in as, k in [0:as.size] do
    if !assumeSat then out := { out with notAsked := out.notAsked.push a.name }; continue
    if isRange a.name then continue
    let others := (A.extract 0 k) ++ A.extract (k + 1)
    let ok := Is.any fun I => (models sp size I ownIns others).any (!holds I · (atom a))
    out := put out .redundancy (some a.name) (pass ok)
  let consistent := MF.any fun (_, ms) => !ms.isEmpty
  for r in rs, k in [0:rs.size] do
    if !consistent || vacuous.contains r.name then out := { out with notAsked := out.notAsked.push r.name }; continue
    if isRange r.name then continue
    let others := A ++ Iw ++ (R.extract 0 k) ++ R.extract (k + 1)
    let ok := Is.any fun I => (models sp size I order others).any (!holds I · (atom r))
    out := put out .redundancy (some r.name) (pass ok)
  -- Determinism.
  for x in c.vars.filter (·.isDet) do
    let ok := MF.all fun (_, ms) => ms.all fun m₁ => ms.all fun m₂ =>
      !(ownIns.all fun (n, _) => m₁[n]? == m₂[n]?) || m₁[x.name]? == m₂[x.name]?
    out := put out .determinism (some x.name) (pass ok)
  return out

/-! ## Details -/

/-- The atoms named `names` among the hypotheses of `c`: assumptions,
requirements and instances. -/
def named (sp : Spec) (c : Comp) (names : Array Name) : Array Atom :=
  (c.constraints.filter (fun p => (p.kind == .assume || p.kind == .ensure) && names.contains p.name)).map
    (fun p => { label := p.name, pfx := .anonymous, e := p.e })
  ++ (c.insts.filter (names.contains ·.name)).flatMap (sp.instAtoms .anonymous)

/-- The values `shown` as an environment. Abstract values keep their
pattern of equalities: the `k`th distinct one shown is value `k`. -/
def pinned (st : LState) (c : Comp) (vars : Array Var) (shown : Fren.Core.Assignment) : Option Env := do
  let module := if c.isGlobal then c.path else c.path.getPrefix
  let mut env : Env := {}
  let mut abstracts : Array String := #[]
  for (n, text) in shown do
    let v ← vars.find? (·.name == n)
    if let .abstract s := v.ty then
      let k := (abstracts.idxOf? text).getD abstracts.size
      if k == abstracts.size then abstracts := abstracts.push text
      env := env.insert n (.abs s k)
    else
      match parseValue st module v.ty text with
      | .ok val => env := env.insert n val
      | .error _ => none
  return env

/-- What is wrong with the details of a failing result, by brute force. -/
def checkDetail (st : LState) (c : Comp) (r : CheckResult) : Option String := Id.run do
  let sp := st.spec
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  let Is := interps sp size
  let order := sp.order c
  let some_ (atoms : Array Atom) (env : Env := {}) := Is.any fun I => !(models sp size I order atoms env).isEmpty
  let prop? := r.prop?.bind fun n => c.constraints.find? (·.name == n)
  let atomOf (p : Constraint) (e := p.e) : Atom := { label := p.name, pfx := .anonymous, e }
  match r.detail with
  | .vacuousAssumptions core =>
    if some_ (named sp c core) then return some s!"the assumptions {core} are satisfiable"
  | .conflict input core =>
    -- Under the model's interpretation, which is not shown: wrong only if
    -- outputs satisfy the core under every interpretation.
    let some env := pinned st c flat input | return some s!"cannot read the input {input}"
    let context := sp.meaning c |>.filter fun a => !(c.ofKind .ensure).any (·.name == a.label)
    if Is.all fun I => !(models sp size I order (context ++ named sp c core) env).isEmpty then
      return some s!"on the input {input}, outputs satisfy {core}"
    -- Each clash: its guarantee, and the rest of the core, force the
    -- output to the values shown. They are shown only where they depend on
    -- no interpretation; the context, which the clash's queries do not
    -- have, can only force more.
    for cl in r.clashes do
      let some v := flat.find? (·.name == cl.output) | return some s!"a clash names {cl.output}, which is not an output"
      -- A value's variant, as a clash note names it.
      let variantOf (val : Val) : Option String := match val with
        | .ctor ty idx _ => do
          let d ← sp.data.find? ty
          if d.isRecord then none
          return s!"{ty.getString!}::{(← d.ctors[idx]?).name}"
        | _ => none
      let models' (names : Array Name) (I : Interp) := models sp size I order (context ++ named sp c names) env
      -- Every assignment that satisfies them has the value, or a value of
      -- the variant, and some does.
      let forced (names : Array Name) : Fren.Core.Forced → Bool
        | .value text => match parseValue st c.path.getPrefix v.ty text with
          | .ok val => Is.all fun I => (models' names I).all (·[cl.output]? == some val)
          | .error _ => false
        | .variant k => Is.all fun I => (models' names I).all fun m => (m[cl.output]?.bind variantOf) == some k.name
      -- Different values, or values of different variants.
      let variant : Fren.Core.Forced → Option String
        | .value text => (parseValue st c.path.getPrefix v.ty text).toOption.bind variantOf
        | .variant k => some k.name
      let differ := match cl.forced, cl.restForced with
        | .value a, .value b => a != b
        | f, f' => (variant f).isSome && variant f != variant f'
      -- A side shows its variant only where it does not force its value.
      let onlyVariant (names : Array Name) : Fren.Core.Forced → Bool
        | .variant _ => Is.any fun I => !(models' names I).isEmpty && !((models' names I).all fun m =>
            (models' names I).all fun m' => m[cl.output]? == m'[cl.output]?)
        | .value _ => true
      unless forced #[cl.guarantee] cl.forced && forced cl.rest cl.restForced && differ do
        return some s!"on the input {input}, {cl.guarantee} and {cl.rest} do not force {cl.output} to {repr cl.forced} and {repr cl.restForced}"
      unless onlyVariant #[cl.guarantee] cl.forced && onlyVariant cl.rest cl.restForced do
        return some s!"on the input {input}, {cl.guarantee} or {cl.rest} force a whole value of {cl.output}, but only a variant is shown"
  | .vacuous core =>
    let some p := prop? | return none
    -- A cover goal's core rules out the goal itself.
    let some t := if r.kind == .cover then some p.e else p.e.trigger? | return none
    if some_ (named sp c core |>.push (atomOf p t)) then return some s!"{core} do not rule out the trigger"
  | .redundant core =>
    let some p := prop? | return none
    if some_ (named sp c core |>.push (atomOf p (.not p.e))) then return some s!"{p.name} does not follow from {core}"
  | .counterexample shown =>
    let some env := pinned st c flat shown | return some s!"cannot read the counterexample {shown}"
    if r.kind == .expect then
      let some p := prop? | return none
      let hyps := if c.isGlobal then sp.insts c else sp.meaning c
      unless some_ (hyps.push (atomOf p (.not p.e))) env do
        return some s!"the counterexample {shown} is not a behaviour in which it is false"
  | .witness shown =>
    let some env := pinned st c flat shown | return some s!"cannot read the witness {shown}"
    let some p := prop? | return none
    unless some_ (sp.meaning c |>.push (atomOf p)) env do
      return some s!"the witness {shown} is not a behaviour in which the goal holds"
  | .nondeterministic input v₁ v₂ =>
    let some env := pinned st c flat input | return some s!"cannot read the input {input}"
    let some x := r.prop? | return none
    let some v := flat.find? (·.name == x) | return none
    let (.ok a, .ok b) := (parseValue st c.path.getPrefix v.ty v₁, parseValue st c.path.getPrefix v.ty v₂)
      | return none
    if a == b then return some s!"the two values {v₁} and {v₂} are equal"
    let has (I : Interp) (val : Val) :=
      !(models sp size I order (sp.meaning c |>.push { label := x, pfx := .anonymous, e := .bin .eq (.var x) (.lit val) }) env).isEmpty
    unless Is.any fun I => has I a && has I b do return some s!"on the input {input}, {x} cannot be both {v₁} and {v₂}"
  | _ => pure ()
  return none

/-! ## Comparing -/

structure Finding where
  what : String

def keyOf (r : CheckResult) : CheckKind × Option Name × Option (Name × Name) := (r.kind, r.prop?, r.target?)

def showKey (k : CheckKind × Option Name × Option (Name × Name)) : String :=
  let (kind, p, t) := k
  s!"{kindName kind}{(p.map (s!" {·}")).getD ""}{(t.map fun (d, a) => s!" ({d}::{a})").getD ""}"

/-- Checks one spec, and returns what differs from brute force. -/
def runOne (dir : System.FilePath) (text : String) (timeout : Nat) :
    IO (Array String × Nat × Nat × Nat) := do
  let path := dir / "current.fren"
  IO.FS.writeFile path text
  let lints := Fren.Core.Lint.all.map (.lint ·, Fren.Core.LintLevel.allow)
  let some (files, st) ← elaborate {} #[path.toString] lints | return (#["cannot read the spec"], 0, 0, 0)
  let errors := st.diags.filter (·.severity == .error)
  unless errors.isEmpty do return (#[s!"generator: static error: {(errors[0]?.map (·.msg.headline)).getD ""}"], 0, 0, 0)
  let lst ← match specStateOf files with
    | .ok s => pure s
    | .error e => return (#[s!"the evaluator cannot read the spec: {e}"], 0, 0, 0)
  let sp := lst.spec
  let mut found := #[]
  let mut compared := 0
  let mut inconclusive := 0
  let mut skipped := 0
  let prelude := Prelude.ofDecls st.prelude
  let sy := Symbols.of sp
  for (c, global) in st.comps.map (·, false) ++ st.globals.map (·, true) do
    let some ec := sp.counterpart? c global | found := found.push s!"no counterpart of {c.path}"; continue
    let log ← IO.mkRef #[]
    let bk := backend prelude st.datatypes { c with funFacts := st.funFacts, bounded := st.bounded c } { timeoutSecs := timeout } none (st.usesStrings || st.usesSeqs) (st.usesSets || st.usesSeqs)
      st.usesProjection (funs := st.appFuns)
    let core := pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start)) (c.tables.map (·.2.2.1.start))
    -- Every clash of a conflict, where it depends on no interpretation
    -- (`Fren.Core.Comp.realizableInterpreted`), as `fren check` decides.
    let interprets (f : String) : Bool := prelude.interprets (quotedSymbols f)
    let core := { core with typesInterpreted := c.vars.any (interprets ·.ty.sort) }
    let results ← Fren.Core.checkComp (fun k => confirming sp sy ec k log (bk k)) core (Fren.Core.kindsFor global)
      (examples := none) (interprets := (interprets ·.1))
    -- A definedness result, by its index's position, and a table's, by
    -- where it is reported and its rows, as brute force keys them.
    let keyOf (r : CheckResult) :=
      if r.kind == .completeness || r.kind == .disjointness || r.kind == .reachability then
        let pos? := r.prop?.bind fun p => (c.tables.filter (·.1 == p))[r.site?.getD 0]?.map (·.2.2.1.start)
        (r.kind, r.prop?.map fun p => tableKey p (pos?.getD 0) r.rows?, r.target?)
      else if r.kind != .definedness then keyOf r else
      let pos? := r.prop?.bind fun p => (c.indexes.filter (·.1 == p))[r.index?.getD 0]?.map (·.2.2.1.start)
      (r.kind, r.prop?.map fun p => Name.num p (pos?.getD 0), r.target?)
    for x in ← log.get do
      found := found.push s!"{c.path}: refuted model ({kindName x.kind} {x.subject?}, hypothesis {x.hyp?}): {x.model}"
    if space sp ec > maxSpace then skipped := skipped + 1; continue
    let o := oracle sp ec
    for r in results do
      if r.kind == .redundancy && o.notAsked.contains (r.prop?.getD .anonymous) then
        found := found.push s!"{c.path}: {showKey (keyOf r)} was checked, but brute force says it is not asked"
      if r.verdict == .inconclusive then inconclusive := inconclusive + 1; continue
      match o.verdicts.find? (·.1 == keyOf r) with
      | some (_, v) =>
        compared := compared + 1
        if v != r.verdict then
          found := found.push s!"{c.path}: {showKey (keyOf r)}: fren says {repr r.verdict}, brute force says {repr v}"
      | none =>
        let ignored := r.kind == .redundancy && (r.prop?.any isRange || o.notAsked.contains (r.prop?.getD .anonymous))
        unless ignored do found := found.push s!"{c.path}: {showKey (keyOf r)}: no such check by brute force"
      -- A failure's details, and a cover goal's witness.
      if r.verdict == .fail || (r.kind == .cover && r.verdict == .pass) then
        if let some why := checkDetail lst ec r then
          found := found.push s!"{c.path}: {showKey (keyOf r)}: wrong details: {why}"
    for (k, _) in o.verdicts do
      unless results.any (keyOf · == k) do
        found := found.push s!"{c.path}: {showKey k}: brute force checks it, but fren does not"
  return (found, compared, inconclusive, skipped)

def usage : String := "usage: fren_fuzz [--count N] [--seed N] [--out DIR] [--timeout SECONDS]"

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Nat × Nat × String × Nat → Option (Nat × Nat × String × Nat)
    | [], a => some a
    | "--count" :: n :: rest, (_, s, d, t) => n.toNat?.bind fun n => parse rest (n, s, d, t)
    | "--seed" :: n :: rest, (c, _, d, t) => n.toNat?.bind fun n => parse rest (c, n, d, t)
    | "--out" :: d :: rest, (c, s, _, t) => parse rest (c, s, d, t)
    | "--timeout" :: n :: rest, (c, s, d, _) => n.toNat?.bind fun n => parse rest (c, s, d, n)
    | _, _ => none
  let some (count, seed, dir, timeout) := parse args (100, 0, ".lake/fuzz", 10) | IO.eprintln usage; return 2
  IO.FS.createDirAll dir
  let mut bad := 0
  let mut compared := 0
  let mut inconclusive := 0
  let mut skipped := 0
  for i in [0:count] do
    let s := seed + i
    let g := genSpec.run' ⟨mix s.toUInt64 0x5eed⟩
    let start ← IO.monoMsNow
    let (found, n, u, k) ← runOne dir g.text timeout
    let elapsed := (← IO.monoMsNow) - start
    if elapsed > 5000 then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s"
    skipped := skipped + k
    compared := compared + n
    inconclusive := inconclusive + u
    unless found.isEmpty do
      bad := bad + 1
      let file : System.FilePath := dir / s!"seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz --seed {s}\n" ++ header ++ g.text)
      IO.eprintln s!"seed {s}: {found.size} difference(s), written to {file}"
      for f in found.extract 0 3 do IO.eprintln s!"  {f}"
  IO.eprintln s!"fren_fuzz: {count} specs, {compared} results compared, {inconclusive} inconclusive, \
    {skipped} components too large for brute force, {bad} with differences"
  return if bad == 0 then 0 else 1

end FrenFuzz

def main (args : List String) : IO UInt32 := FrenFuzz.main args
