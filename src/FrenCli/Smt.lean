-- keep-sorted start
import FrenCli.Elab
import FrenCore.Check
import cvc5
-- keep-sorted end

/-!
# The cvc5 backend

Runs the shared check algorithms (`FrenCore.Check`) with cvc5, linked into the
binary. Formulas are SMT-LIB text over the comp's variables; each query is a
fresh solver.
-/

namespace FrenCli

open Fren.Core (Outcome)

/-- The SMT-LIB script that asserts `hyps` and the negation of `goal`, each
hypothesis followed by a comment with its name; without `(check-sat)`. -/
def queryScript (logic prelude : String) (vars : Array CVar) (timeoutSecs : Nat)
    (hyps : Array (Lean.Name × String)) (goal : String) : String :=
  let decls := String.join (vars.toList.map fun v => s!"(declare-const {quote v.name.toString} {v.ty.sort})\n")
  let asserts := String.join (hyps.toList.map fun (n, h) => s!"(assert {h}) ; {n}\n")
  s!"(set-logic {logic})\n(set-option :produce-models true)\n\
    (set-option :tlimit-per {timeoutSecs * 1000})\n{prelude}{decls}{asserts}(assert (not {goal}))\n"

/-- Asserts `hyps` and the negation of `goal` and checks satisfiability,
first passing the script to `dump?`, if any. -/
def runQuery (logic prelude : String) (vars : Array CVar) (timeoutSecs : Nat) (dump? : Option (String → IO Unit))
    (hyps : Array (Lean.Name × String)) (goal : String) (wantModel : Bool) : IO (Outcome String) := do
  let script := queryScript logic prelude vars timeoutSecs hyps goal
  if let some dump := dump? then dump script
  let r ← cvc5.Env.run do
    let tm ← cvc5.TermManager.new
    let solver ← cvc5.Solver.new tm
    let parser ← cvc5.InputParser.new solver
    let sm ← parser.getSymbolManager
    parser.setStringInput script .SMT_LIB_2_6
    repeat
      let cmd ← parser.nextCommand
      if cmd.isNull then break
      -- A command that fails reports an error as its output, rather than
      -- throwing; ignoring it could let a dropped assertion give `sat`.
      let out ← cmd.invoke solver sm
      if out.trimAscii.toString.startsWith "(error" then
        throw (.error out)
    let res ← solver.checkSat
    if res.isUnsat then return Outcome.unsat
    if !res.isSat then return .unknown s!"the solver returned unknown ({res.getUnknownExplanation})"
    if !wantModel then return .sat #[]
    let mut model := #[]
    for t in ← sm.getDeclaredTerms do
      let n := (toString t).replace "|" ""
      if let some v := vars.find? (·.name.toString == n) then
        model := model.push (v.name, toString (← solver.getValue t))
    return .sat model
  match r with
  | .ok o => return o
  | .error e => return .unknown s!"solver error: {e}"

/-- A value of an abstract type, as cvc5 writes it, such as
`(as @|::lang::Name|_0 |::lang::Name|)`, as Fren writes it: `Name#0`. -/
def renderAbstract? (v : String) : Option String := do
  let v := v.replace "|" ""
  let v := if v.startsWith "(as " then (v.drop 4).toString else v
  guard (v.startsWith "@")
  let tok := ((v.drop 1).takeWhile (· != ' ')).toString
  let digits := (tok.toList.reverse.takeWhile Char.isDigit).reverse
  guard !digits.isEmpty
  let sort := ((tok.dropEnd digits.length).dropEndWhile (· == '_')).toString
  let name := (sort.splitOn "::").getLast?.getD sort
  return s!"{name}#{String.ofList digits}"

/-- A value as cvc5 writes it: an atom, with any `|` quotes removed, or a
list. -/
inductive Term where
  | atom (s : String)
  | list (ts : Array Term)
  deriving Inhabited

/-- The terms of `cs` from `i`, up to an unmatched `)`, and where they end. -/
partial def parseTerms (cs : Array Char) (i : Nat) : Array Term × Nat := Id.run do
  let mut i := i
  let mut out := #[]
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then i := i + 1
    else if c == ')' then return (out, i + 1)
    else if c == '(' then
      let (ts, j) := parseTerms cs (i + 1)
      out := out.push (.list ts)
      i := j
    else if c == '"' then
      -- A string literal, in which `""` is a `"`.
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      out := out.push (.atom (String.ofList (cs.extract i (j + 1)).toList))
      i := j + 1
    else if c == '|' then
      let j := ((cs.extract (i + 1) cs.size).findIdx? (· == '|')).map (· + i + 1) |>.getD cs.size
      out := out.push (.atom (String.ofList (cs.extract (i + 1) j).toList))
      i := j + 1
    else
      let j := ((cs.extract i cs.size).findIdx? fun c => c.isWhitespace || c == '(' || c == ')').map (· + i) |>.getD cs.size
      out := out.push (.atom (String.ofList (cs.extract i j).toList))
      i := j
  return (out, i)

/-- `check::Verdict::Pass` ↦ `Verdict::Pass`: a variant or record by its
type's name, without its module. -/
def lastTwo (s : String) : String :=
  let segs := s.splitOn "::"
  if segs.length > 2 then "::".intercalate (segs.drop (segs.length - 2)) else s

/-- The member of a set that the tuple `t` is: a set's 1-tuple is its
member, and a relation's 2-tuple, a pair, stays a tuple. -/
def tupleMember? : Term → Option Term
  | .list #[.atom "tuple", x] => some x
  | t@(.list #[.atom "tuple", _, _]) => some t
  | _ => none

/-- The members of a set or relation as cvc5 writes it, a union of
singletons of tuples, or `none` if it is not one. -/
partial def setMembers? : Term → Option (Array Term)
  | .list #[.atom "as", .atom "set.empty", _] => some #[]
  | .list #[.atom "set.singleton", t] => do return #[← tupleMember? t]
  | .list #[.atom "set.union", a, b] => do return (← setMembers? a) ++ (← setMembers? b)
  | .list ts => do
    guard (ts[0]? matches some (Term.atom "set.insert") && ts.size ≥ 3)
    let xs ← (ts.extract 1 (ts.size - 1)).mapM tupleMember?
    return xs ++ (← setMembers? ts.back!)
  | _ => none

/-- A value as Fren builds it (`Reqs/View`), where `dts` are the
enumerations and records: `(- 3)` ↦ `-3`, `|check::Verdict::Pass|` ↦
`Verdict::Pass`, `(|Shape::Circle| 2)` ↦ `Shape::Circle(2)` and
`(|geo::Point\{}| 1 2)` ↦ `Point \{ x := 1, y := 2 }`. -/
partial def renderTerm (dts : Array DataDecl) : Term → String
  -- A string, as a Lean literal, so that it can be pasted into a spec.
  | .atom a => match Fren.Core.parseSmtString? a with
    | some s => s.quote
    | none => lastTwo a

  | .list #[.atom "-", .atom n] => "-" ++ n
  -- A pair, a member of a relation.
  | .list #[.atom "tuple", x, y] => s!"({renderTerm dts x}, {renderTerm dts y})"
  -- A sequence, as a literal.
  | .list #[.atom "as", .atom "seq.empty", _] => "[]"
  | .list #[.atom "seq.unit", x] => s!"[{renderTerm dts x}]"
  | .list ts =>
    -- An abstract value within another value.
    let abs? := match ts with | #[.atom "as", .atom a, _] => renderAbstract? a | _ => none
    if let some r := abs? then r else
    -- A concatenation of sequences, as one literal: each part is one.
    if ts[0]? matches some (Term.atom "seq.++") then
      let parts := (ts.extract 1).map (renderTerm dts) |>.map fun p => ((p.drop 1).dropEnd 1).toString
      "[" ++ ", ".intercalate (parts.toList.filter (!·.isEmpty)) ++ "]"
    else
    -- A set, as a literal, with its members sorted, so that it is stable.
    if let some ms := setMembers? (.list ts) then
      let shown := ms.map (renderTerm dts) |>.toList.eraseDups.toArray.qsort (· < ·)
      "{" ++ ", ".intercalate shown.toList ++ "}"
    else
    let args := (ts.extract 1 ts.size).map (renderTerm dts)
    match ts[0]? with
    | some (Term.atom c) =>
      if c.endsWith "{}" then
        let r := (c.dropEnd 2).toString
        match dts.find? (Fren.Core.showPath ·.path == r) with
        | some d =>
          let fs := (d.ctors[0]!.2.zip args).toList.map fun ((f, _), v) => s!"{f} := {v}"
          s!"{(r.splitOn "::").getLast!} \{ {", ".intercalate fs} }"
        | none => s!"({c} {" ".intercalate args.toList})"
      else s!"{lastTwo c}({", ".intercalate args.toList})"
    | _ => s!"({" ".intercalate args.toList})"

def renderValue (dts : Array DataDecl) (v : String) : String :=
  if let some a := renderAbstract? v then a else
  match (parseTerms v.toList.toArray 0).1 with
  | #[t] => renderTerm dts t
  | _ => v.replace "|" ""

/-- The variables of `c` other than its `in`s, renamed to their second
copies (`Fren.Core.primed`). -/
def primes (c : CComp) : Array CVar :=
  c.vars.filter (fun v => (Fren.Core.Symbol.ofRole v.role).copied) |>.map fun v =>
    { v with name := Fren.Core.primed v.name }

/-- Renames each variable of `c` other than its `in`s to its second copy.
Like `rename`, relies on variables being quoted symbols. -/
def prime (c : CComp) (smt : String) : String :=
  -- Functions are not variables, so they are never renamed.
  let names := (c.vars.filter fun v => (Fren.Core.Symbol.ofRole v.role).copied).map (·.name.toString)
  mapQuoted (fun p => if names.contains p then p ++ "'" else p) smt

/-- The backend for `c`, where `strings` and `sets` say whether the spec uses
strings and sets, and `projection` whether it projects a relation over a
type that is not finite (`cli::logic`). -/
def backend (prelude : String) (dts : Array DataDecl) (c : CComp) (timeoutSecs : Nat) (dump? : Option (String → IO Unit) := none)
    (strings sets : Bool := false) (projection : Bool := false) (kind : Fren.Core.CheckKind) :
    Fren.Core.Backend IO String String where
  -- cvc5 refuses some string operations without `strings-exp`.
  query := runQuery (Fren.Core.logic kind (strings || sets) projection)
    (String.join ((Fren.Core.solverOptions strings sets).map fun (o, v) => s!"(set-option :{o} {v})\n") ++ prelude)
    (c.vars ++ primes c) timeoutSecs dump?
  falseF := "false"
  notF f := s!"(not {f})"
  conj := conj
  existsOutputs f := do
    -- Defined outputs are substituted, never searched for.
    let outs := c.vars.filter fun v => v.role == .output && v.defn?.isNone
    if outs.isEmpty then return f
    let binders := " ".intercalate (outs.toList.map fun v => s!"({quote v.name.toString} {v.ty.sort})")
    return s!"(exists ({binders}) {f})"
  -- A value of an abstract type names a solver-internal constant, such as
  -- `@U_0`, which a fresh query cannot parse.
  pin n v := return if v.contains '@' then none else some s!"(= {quote n.toString} {v})"
  render _ v := return renderValue dts v
  prime := prime c
  samePrimed n := s!"(= {quote n.toString} {quote (Fren.Core.primed n).toString})"
  -- Each definition sees the earlier ones.
  subst ds f := ds.foldr (init := f) fun (d, e) f => s!"(let (({quote d.toString} {e})) {f})"

def toCore (c : CComp) : Fren.Core.Comp String :=
  let props (k : PropKind) := c.props.filter (·.kind == k) |>.map fun p => (p.name, p.smt)
  { path := c.path
    vars := c.vars.map fun v =>
      { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
    assumes := props .assume
    reqs := props .req
    expects := props .expect
    insts := c.insts.map fun i =>
      { name := i.name, comp := i.comp, bindings := i.bindings, behaviour := i.behaviour, assumes := i.assumes }
    triggers := (c.props.filter (·.kind != .assume)).filterMap fun p => p.trigger?.map (p.name, ·)
    defs := c.defs.map fun (d, e) => (d, s!"(= {quote d.toString} {e})", e)
    -- Numbered in order within each item.
    indexes := c.indexes.mapIdx fun j (n, place, _, goal) =>
      { prop := n, k := (c.indexes.extract 0 j).filter (·.1 == n) |>.size, place, goal } }

end FrenCli
