-- keep-sorted start
import FrenCli.Elab
import FrenCore.Check
import cvc5
-- keep-sorted end

/-!
# The cvc5 backend

Runs the shared check algorithms (`FrenCore.Check`) with cvc5, linked into the
binary. Formulas are SMT-LIB text over the procedure's variables; each query is a
fresh solver, and a query asked again is answered from a cache
(`QueryCache`).
-/

namespace FrenCli

open Fren.Core (Outcome)

/-- The prelude (`State.prelude`), with the declarations that each one
mentions. -/
structure Prelude where
  decls : Array PreludeDecl
  /-- The declaration of each symbol. -/
  owner : Std.HashMap String Nat
  /-- The declarations that each declaration mentions. -/
  deps : Array (Array Nat)
  deriving Inhabited

def Prelude.ofDecls (decls : Array PreludeDecl) : Prelude :=
  let owner := decls.zipIdx.foldl (init := {}) fun m (d, i) => d.syms.foldl (·.insert · i) m
  { decls, owner, deps := decls.map fun d => (quotedSymbols d.text).filterMap owner.get? }

/-- The declarations that a script whose quoted symbols are `syms` needs:
those of its symbols, and of theirs in turn, in the order of the prelude.
The others cannot change its answer, and declaring them is most of the
work of a small query. -/
def Prelude.needed (p : Prelude) (syms : Array String) : String := Id.run do
  let mut keep := Array.replicate p.decls.size false
  let mut work := syms.filterMap p.owner.get?
  while h : work.size > 0 do
    let i := work[work.size - 1]
    work := work.pop
    if keep[i]! then continue
    keep := keep.set! i true
    work := work ++ p.deps[i]!
  return String.join (p.decls.zipIdx.toList.filterMap fun (d, i) => if keep[i]! then some d.text else none)

/-- Whether a script whose quoted symbols are `syms` needs an abstract type
or an uninterpreted function, directly or through another declaration. -/
def Prelude.interprets (p : Prelude) (syms : Array String) : Bool := Id.run do
  let mut seen := Array.replicate p.decls.size false
  let mut work := syms.filterMap p.owner.get?
  while h : work.size > 0 do
    let i := work[work.size - 1]
    work := work.pop
    if seen[i]! then continue
    seen := seen.set! i true
    let text := p.decls[i]!.text
    if text.startsWith "(declare-sort" || text.startsWith "(declare-fun" then return true
    work := work ++ p.deps[i]!
  return false

/-- The limits of each solver query (`Reqs/Cli#limits`): `timeoutSecs`
seconds of wall-clock time (`--timeout`), and `resources` of cvc5's
resource units (`--resource-limit`), which do not depend on the machine's
load. Either is none when 0. -/
structure Limits where
  timeoutSecs : Nat := 10
  resources : Nat := 0
  deriving Inhabited

/-- The options that set `limits`. A script without a resource limit sets
none, so that it is the script that `fren` wrote before the limit
existed. -/
def Limits.options (limits : Limits) : String :=
  s!"(set-option :tlimit-per {limits.timeoutSecs * 1000})\n" ++
    if limits.resources == 0 then "" else s!"(set-option :rlimit-per {limits.resources})\n"

/-- The SMT-LIB script that asserts `hyps` and the negation of `goal`, each
hypothesis followed by a comment with its name; without `(check-sat)`. It
declares only what the prelude needs to (`Prelude.needed`). -/
def queryScript (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (hyps : Array (Lean.Name × String)) (goal : String) : String :=
  let decls := String.join (vars.toList.map fun v => s!"(declare-const {quote v.name.toString} {v.ty.sort})\n")
  let asserts := String.join (hyps.toList.map fun (n, h) => s!"(assert {h}) ; {n}\n")
  let body := s!"{decls}{asserts}(assert (not {goal}))\n"
  let script := s!"(set-logic {logic})\n(set-option :produce-models true)\n\
    {limits.options}{options}{prelude.needed (quotedSymbols body)}{body}"
  mapQuoted Fren.Core.smtName script

/-- The answers to the queries asked so far, by script, each with whether
it has a model: a script asked again gets the same answer without the
solver (`Reqs/Cli#solver-queries`). The script is the whole query, with its
logic, options and limits, so the same script means the same question. The
checks of several procedures may share it at once (`Reqs/Cli#parallel-checking`). -/
abbrev QueryCache := IO.Ref (Std.HashMap String (Outcome String × Bool))

/-- Checks the satisfiability of `script`, a query over `vars`, with values
of `vars` if `wantModel`. -/
def solveScript (script : String) (vars : Array CVar) (wantModel : Bool) : IO (Outcome String) := do
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
      if let some v := vars.find? (Fren.Core.smtName ·.name.toString == n) then
        model := model.push (v.name, toString (← solver.getValue t))
    return .sat model
  match r with
  | .ok o => return o
  | .error e => return .unknown s!"solver error: {e}"

/-- Asserts `hyps` and the negation of `goal` and checks satisfiability,
first passing the script to `dump?`, if any, and answering from `cache?`,
if any, a script asked before. -/
def runQuery (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (dump? : Option (String → IO Unit)) (hyps : Array (Lean.Name × String)) (goal : String) (wantModel : Bool)
    (cache? : Option QueryCache := none) : IO (Outcome String) := do
  let script := queryScript logic options prelude vars limits hyps goal
  if let some dump := dump? then dump script
  let some cache := cache? | solveScript script vars wantModel
  -- A model's variables are those that the script declares, which are `vars`.
  match (← cache.get)[script]? with
  | some (o@(.sat _), hasModel) =>
    if !wantModel then return .sat #[]
    if hasModel then return o
  | some (o, _) => return o
  | none => pure ()
  let o ← solveScript script vars wantModel
  cache.modify (·.insert script (o, wantModel))
  return o

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

/-- The first position from `i` of a character of `cs` that satisfies `p`,
or the end of `cs`: without copying the rest of `cs`, so that reading a
model is linear in its length. -/
def findFrom (cs : Array Char) (i : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut j := i
  while h : j < cs.size do
    if p cs[j] then return j
    j := j + 1
  return cs.size

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
      let j := findFrom cs (i + 1) (· == '|')
      out := out.push (.atom (String.ofList (cs.extract (i + 1) j).toList))
      i := j + 1
    else
      let j := findFrom cs i fun c => c.isWhitespace || c == '(' || c == ')'
      out := out.push (.atom (String.ofList (cs.extract i j).toList))
      i := j
  return (out, i)

/-- The atoms that `t` mentions as the solver sees it, once its
`define-fun`s are unfolded and its `let`s substituted, as the Lean-hosted
front end gives them to lean-smt (`Fren.unfoldDefined`): an argument of a
function in `used` whose parameter its body does not mention, and a `let`'s
definition of a name that its body does not mention, are not mentioned. -/
partial def termMentions (used : Std.HashMap String (Array Bool)) : Term → Array String
  | .atom a => #[a]
  | .list ts => match ts.toList with
    | [.atom "let", .list binds, body] =>
      let inBody := termMentions used body
      binds.foldl (init := inBody) fun acc b => match b with
        | Term.list #[Term.atom x, e] => if inBody.contains x then acc ++ termMentions used e else acc
        | b => acc ++ termMentions used b
    | .atom f :: args => match used[f]? with
      | some u => (args.toArray.zipIdx.filter fun (_, i) => u[i]?.getD true).flatMap (termMentions used ·.1)
      | none => ts.flatMap (termMentions used)
    | _ => ts.flatMap (termMentions used)

/-- Of each `define-fun` of `decls`, by its symbol, which of its parameters
its body mentions (`termMentions`), in order, so that each sees those
before it. -/
def usedParams (decls : Array PreludeDecl) : Std.HashMap String (Array Bool) := Id.run do
  let mut used : Std.HashMap String (Array Bool) := {}
  for d in decls do
    unless d.text.startsWith "(define-fun" do continue
    let (ts, _) := parseTerms d.text.toList.toArray 0
    let some (Term.list #[_, Term.atom f, Term.list ps, _, body]) := ts[0]? | continue
    let inBody := termMentions used body
    used := used.insert f (ps.map fun
      | Term.list #[Term.atom x, _] => inBody.contains x
      | _ => true)
  return used

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

/-- The types of the fields of the constructor `c` of one of `dts`, as the
solver writes `c`. -/
def fieldTys (dts : Array DataDecl) (c : String) : Option (Array Fren.Core.Ty) := do
  let named (d : DataDecl) (v : Lean.Name) := s!"{Fren.Core.showPath d.path}::{v}" == c
  let d ← dts.find? fun d => if d.isRecord then s!"{Fren.Core.showPath d.path}\{}" == c else d.ctors.any (named d ·.1)
  let (_, fs) ← if d.isRecord then d.ctors[0]? else d.ctors.find? (named d ·.1)
  return fs.map (·.2)

/-- The symbol that a non-generic type's constructor would have, for a
generic type's constructor `c`, which is a simple symbol with `~` for `::`
(`DataDecl.ctorSym`): `Option~Some` ↦ `Option::Some`, `Pair~` ↦ `Pair{}`. -/
def genericCtor (c : String) : String :=
  if c.endsWith "~" then ((c.dropEnd 1).toString.replace "~" "::") ++ "{}" else c.replace "~" "::"

/-- `t`, with a generic type's constructor, which cvc5 writes qualified by
its sort, `(as C (D Int))`, as a constructor of any other type. -/
def unqualify : Term → Term
  | .atom c => if !c.startsWith "\"" && c.contains '~' then .atom (genericCtor c) else .atom c
  | .list ts => match ts[0]? with
    | some (Term.atom "as") => match ts[1]? with
      | some (Term.atom c) => if c.contains '~' then .atom (genericCtor c) else .list ts
      | _ => .list ts
    | some (Term.list #[.atom "as", .atom c, _]) =>
      if c.contains '~' then .list (#[.atom (genericCtor c)] ++ ts.extract 1) else .list ts
    | _ => .list ts

/-- A value as Fren builds it (`Reqs/View`), where `dts` are the
enumerations and records: `(- 3)` ↦ `-3`, `|check::Verdict::Pass|` ↦
`Verdict::Pass`, `(|Shape::Circle| 2)` ↦ `Shape::Circle(2)` and
`(|geo::Point\{}| 1 2)` ↦ `Point \{ x := 1, y := 2 }`. A value of type
`ty?`, if it is known, is shown with its newtypes, which the solver does
not see: `5` of the newtype `Ms` ↦ `Ms(5)`. -/
partial def renderTerm (dts : Array DataDecl) (ty? : Option Fren.Core.Ty) (t : Term) : String :=
  if let some (.newtype p u) := ty? then s!"{p.getString!}({renderTerm dts (some u) t})" else
  let t := unqualify t
  let elemTy? : Option Fren.Core.Ty := match ty? with
    | some (.set e) | some (.seq e) => some e
    | _ => none
  let (fstTy?, sndTy?) : Option Fren.Core.Ty × Option Fren.Core.Ty := match ty? with
    | some (.rel a b) => (some a, some b)
    | _ => (none, none)
  match t with
  -- A string, as a Lean literal, so that it can be pasted into a spec.
  | .atom a => match Fren.Core.parseSmtString? a with
    | some s => s.quote
    | none => lastTwo a
  | .list #[.atom "-", .atom n] => "-" ++ n
  -- A pair, a member of a relation.
  | .list #[.atom "tuple", x, y] => s!"({renderTerm dts fstTy? x}, {renderTerm dts sndTy? y})"
  -- A sequence, as a literal.
  | .list #[.atom "as", .atom "seq.empty", _] => "[]"
  | .list #[.atom "seq.unit", x] => s!"[{renderTerm dts elemTy? x}]"
  | .list ts =>
    -- An abstract value within another value.
    let abs? := match ts with | #[.atom "as", .atom a, _] => renderAbstract? a | _ => none
    if let some r := abs? then r else
    -- A concatenation of sequences, as one literal: each part is one.
    if ts[0]? matches some (Term.atom "seq.++") then
      let parts := (ts.extract 1).map (renderTerm dts ty?) |>.map fun p => ((p.drop 1).dropEnd 1).toString
      "[" ++ ", ".intercalate (parts.toList.filter (!·.isEmpty)) ++ "]"
    else
    -- A set, as a literal, with its members sorted, so that it is stable.
    -- A relation's members are tuples, which are typed by the relation.
    if let some ms := setMembers? (.list ts) then
      let memberTy? := if fstTy?.isSome then ty? else elemTy?
      let shown := ms.map (renderTerm dts memberTy?) |>.toList.eraseDups.toArray.qsort (· < ·)
      "{" ++ ", ".intercalate shown.toList ++ "}"
    else
    -- A generic type's fields, with the instance's arguments for its
    -- parameters, so that a newtype among them is shown.
    let instArgs : Array Fren.Core.Ty := match ty? with
      | some (.enum _ as) | some (.record _ as) => as.toArray
      | _ => #[]
    let tys := match ts[0]? with
      | some (Term.atom c) => ((fieldTys dts c).getD #[]).map (Fren.Core.Ty.subst instArgs)
      | _ => #[]
    let args := (ts.extract 1 ts.size).mapIdx fun k a => renderTerm dts tys[k]? a
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

/-- A value as cvc5 writes it, as Fren builds it, of the type `ty?` if it
is known. -/
def renderValue (dts : Array DataDecl) (v : String) (ty? : Option Fren.Core.Ty := none) : String :=
  let wrap (s : String) : String := match ty? with
    | some (.newtype p _) => s!"{p.getString!}({s})"
    | _ => s
  if let some a := renderAbstract? v then wrap a else
  match (parseTerms v.toList.toArray 0).1 with
  | #[t] => renderTerm dts ty? t
  | _ => wrap (v.replace "|" "")

/-- The variant of `v`, a value as cvc5 writes it, of the type `ty`, an
enumeration: the variant as Fren names it (`Decision::RetryAfter`, as
`renderTerm` shows its constructor), its index among the enumeration's, the
enumeration and its type arguments. Not of a newtype of one, whose values
no pattern matches (`Reqs/Check#forced-outputs`). -/
def variantOfValue (dts : Array DataDecl) (ty : Fren.Core.Ty) (v : String) :
    Option (Fren.Core.Variant × Nat × DataDecl × List Fren.Core.Ty) := do
  match ty with
  | .enum path args =>
    let d ← dts.find? fun d => d.path == path && !d.isRecord
    -- A value of an abstract type within it cannot be written back.
    if v.contains '@' then none
    let #[t] := (parseTerms v.toList.toArray 0).1 | none
    let head ← match unqualify t with
      | Term.atom a => some a
      | Term.list ts => match ts[0]? with
        | some (Term.atom a) => some a
        | _ => none
    let idx ← d.ctors.findIdx? fun (c, _) => s!"{Fren.Core.showPath d.path}::{c}" == head
    return ({ name := lastTwo head, arity := d.ctors[idx]!.2.size }, idx, d, args)
  | _ => none

/-- The variables of `c` other than its parameters, renamed to their second
copies (`Fren.Core.primed`). -/
def primes (c : CComp) : Array CVar :=
  c.vars.filter (fun v => (Fren.Core.Symbol.ofRole v.role).copied) |>.map fun v =>
    { v with name := Fren.Core.primed v.name }

/-- Renames each variable of `c` other than its parameters to its second copy.
Like `rename`, relies on variables being quoted symbols. -/
def prime (c : CComp) (smt : String) : String :=
  -- Functions are not variables, so they are never renamed.
  let names := (c.vars.filter fun v => (Fren.Core.Symbol.ofRole v.role).copied).map (·.name.toString)
  mapQuoted (fun p => if names.contains p then p ++ "'" else p) smt

/-- Those of `terms` that occur in the SMT-LIB text `f`, outside its string
literals, in the order in which they start: an enclosing term before the
terms within it, and otherwise from left to right, as the Lean front end's
`natApps` walks a term. Each of `terms` is a whole term, an application in
parentheses, so its text occurs in `f` just where `f` mentions it. -/
def termsIn (terms : Array String) (f : String) : Array String := Id.run do
  if terms.isEmpty then return #[]
  let cs := f.toList.toArray
  let pats := terms.map fun t => (t, t.toList.toArray)
  let mut out := #[]
  let mut i := 0
  let mut inString := false
  while h : i < cs.size do
    let c := cs[i]
    -- In a string literal, where `""` is a `"`; a term never starts there.
    if c == '"' then
      inString := !inString
    else if !inString && c == '(' then
      for (t, p) in pats do
        let here := i + p.size ≤ cs.size && Id.run do
          for k in [0:p.size] do
            if cs[i + k]! != p[k]! then return false
          return true
        if here && !out.contains t then out := out.push t
    i := i + 1
  return out

/-- The term that starts at `i` in `cs`, an application in parentheses, to
its closing parenthesis, outside string literals and quoted symbols. -/
def balancedAt (cs : Array Char) (i : Nat) : String := Id.run do
  let mut depth := 0
  let mut j := i
  let mut inString := false
  let mut inSym := false
  while h : j < cs.size do
    let c := cs[j]
    if inString then
      if c == '"' then inString := false
    else if inSym then
      if c == '|' then inSym := false
    else if c == '"' then inString := true
    else if c == '|' then inSym := true
    else if c == '(' then depth := depth + 1
    else if c == ')' then
      depth := depth - 1
      if depth == 0 then return String.ofList (cs.extract i (j + 1)).toList
    j := j + 1
  return String.ofList (cs.extract i cs.size).toList

/-- The terms of the SMT-LIB text `f` that bring facts, in the order in
which they start, as `termsIn` finds them: those of `terms`, and the
applications of the selectors `heads`, whatever their arguments, as the
Lean front end's `natApps` walks a term. -/
def factTermsIn (terms heads : Array String) (f : String) : Array String := Id.run do
  let cs := f.toList.toArray
  let pats := terms.map fun t => (t, t.toList.toArray)
  let hpats := heads.map fun h => ("(" ++ h ++ " ").toList.toArray
  let mut out := #[]
  let mut i := 0
  let mut inString := false
  while h : i < cs.size do
    let c := cs[i]
    if c == '"' then
      inString := !inString
    else if !inString && c == '(' then
      for (t, p) in pats do
        let here := i + p.size ≤ cs.size && (List.range p.size).all fun k => cs[i + k]! == p[k]!
        if here && !out.contains t then out := out.push t
      for p in hpats do
        if i + p.size ≤ cs.size && (List.range p.size).all fun k => cs[i + k]! == p[k]! then
          let t := balancedAt cs i
          if !out.contains t then out := out.push t
    i := i + 1
  return out

/-- `t`, the SMT-LIB text that `wrapLets` makes of a term, as the `let`s
around the term, the term, and the parentheses that close them. -/
partial def splitLets (t : String) : String × String × String :=
  let inner := peelLets t
  if inner.length == t.length then ("", t, "") else
  let n := t.length - inner.length
  -- `(let BINDINGS ` before, and `)` after, for each `let`.
  let closes := (t.toList.reverse.takeWhile (· == ')')).length - (inner.toList.reverse.takeWhile (· == ')')).length
  ((t.take (n - closes)).toString, inner, (t.takeEnd closes).toString)

/-- The facts that the application `app`, of an uninterpreted function into
`Nat`, into a pattern type or with postconditions, or a read of a
recursive enumeration's payload of a pattern type, brings
(`Fren.Core.appFacts`), from what `funs` says of its function
(`State.appFuns`) and `types` of its head symbol (`State.funFacts`): that
it is at least 0, if its result is a `Nat`, that it matches its type, and
that it meets each postcondition where its arguments meet the
preconditions, named by the postcondition, within the `let`s and
`forall`s around it, as the Lean front end's are. -/
def appFactsOf (funs : Std.HashMap String (Bool × Contract)) (types : Std.HashMap String String) (app : String) :
    Array (Lean.Name × String) :=
  let (pre, inner, post) := splitLets app
  -- `(SYM ARGS)`.
  let head := ((inner.drop 1).takeWhile (· != ' ')).toString
  let args := ((inner.drop (head.length + 2)).dropEnd 1).toString
  let (nat, k) := funs.getD head (false, {})
  let implies (ps : Array String) (q : String) := if ps.isEmpty then q else s!"(=> {conj ps} {q})"
  let posts := Fren.Core.postconditionFacts implies (k.pres.map fun (_, p) => s!"({p} {args})")
    (k.posts.map fun (n, sym) => (n, s!"({sym} {args})"))
  let typed := (types.get? head).map fun t => (`type, pre ++ t.replace factHole inner ++ post)
  (if nat then #[(`nat, pre ++ s!"(>= {inner} 0)" ++ post)] else #[]) ++ typed.toArray ++ posts.map fun (n, f) => (n, pre ++ f ++ post)

/-- The backend for `c`, where `strings` and `sets` say whether the spec uses
strings and sets, and `projection` whether it projects a relation over a
type that is not finite (`cli::logic`); answering from `cache?`, if any,
the scripts asked before (`runQuery`). -/
def backend (prelude : Prelude) (dts : Array DataDecl) (c : CComp) (limits : Limits) (dump? : Option (String → IO Unit) := none)
    (strings sets : Bool := false) (projection : Bool := false) (cache? : Option QueryCache := none) (quantified : Bool := false)
    (funs : Std.HashMap String (Bool × Contract) := {}) (kind : Fren.Core.CheckKind) :
    Fren.Core.Backend IO String String where
  -- cvc5 refuses some string operations without `strings-exp`. Every query
  -- has what the `Nat` variables bring, of both copies, and what the
  -- applications that it mentions bring (`Reqs/Check`).
  -- The query declares only the variables that its formulas mention, a
  -- `Nat`'s fact among them, so a model, and so a counterexample, has only
  -- those, as in Lean (`Reqs/View#check-results`).
  query hyps goal wantModel := do
    let facts := c.natFacts false ++ c.natFacts true
    let facts := facts ++ (facts.map fun (n, f) => (n, prime c f)).filter (!facts.contains ·)
    let formulas := facts.map (·.2) ++ hyps.map (·.2) |>.push goal
    let mentioned : Std.HashSet String := .ofArray (formulas.flatMap quotedSymbols)
    let vars := (c.vars ++ primes c).filter (mentioned.contains ·.name.toString)
    -- A model shows those that the formulas mention once their definitions
    -- are unfolded, as Lean's does (`termMentions`).
    let used := usedParams prelude.decls
    let shown : Std.HashSet String :=
      .ofArray (formulas.flatMap fun f => (parseTerms f.toList.toArray 0).1.flatMap (termMentions used))
    let apps := c.natApps ++ (c.natApps.map (prime c)).filter (!c.natApps.contains ·)
    -- An application within a `let` or `where` is found as it is written
    -- there, and its fact is within the clause's `let`s.
    let peeled := apps.map peelLets
    -- And each read of a recursive enumeration's payload whose type brings
    -- a constraint, by its selector (`State.funFacts`).
    let heads := c.funFacts.toArray.filterMap fun (h, _) => if h.startsWith "|::" then none else some h
    let appsOf (f : String) := (factTermsIn peeled heads f).map fun t => ((peeled.idxOf? t).map (apps[·]!)).getD t
    let appFacts ← Fren.Core.appFacts (m := Id) appsOf (appFactsOf funs c.funFacts) hyps goal
    -- A procedure whose queries may quantify sets `fmf-bound`
    -- (`State.bounded`).
    let options := Fren.Core.solverOptions strings sets ++ (if c.bounded then Fren.Core.boundedOptions else [])
    let o ← runQuery (Fren.Core.logic kind (strings || sets) projection quantified)
      (String.join (options.map fun (o, v) => s!"(set-option :{o} {v})\n"))
      prelude vars limits dump? (facts ++ appFacts ++ hyps) goal wantModel cache?
    return match o with
      | .sat m => .sat (m.filter fun (n, _) => shown.contains n.toString)
      | o => o
  falseF := "false"
  notF f := s!"(not {f})"
  conj := conj
  existsOutputs f := do
    -- Defined outputs are substituted, never searched for.
    let outs := c.vars.filter fun v => v.role == .output && v.defn?.isNone
    if outs.isEmpty then return f
    let binders := " ".intercalate (outs.toList.map fun v => s!"({quote v.name.toString} {v.ty.sort})")
    -- The outputs' `Nat`s are at least 0, with the requirements.
    return s!"(exists ({binders}) {conj ((c.natFacts true).map (·.2) ++ #[f])})"
  -- A value of an abstract type names a solver-internal constant, such as
  -- `@U_0`, which a fresh query cannot parse.
  pin n v := return if v.contains '@' then none else some s!"(= {quote n.toString} {v})"
  -- The tester of its variant (`DataDecl.tester`), by the variable's type.
  pinVariant n v := return do
    let ty ← (c.vars ++ primes c).find? (·.name == n) |>.map (·.ty)
    let (k, idx, d, args) ← variantOfValue dts ty v
    return (k, d.tester idx (quote n.toString) args)
  -- By the variable's type, for its newtypes.
  render n v := return renderValue dts v ((c.vars ++ primes c).find? (·.name == n) |>.map (·.ty))
  prime := prime c
  samePrimed n := s!"(= {quote n.toString} {quote (Fren.Core.primed n).toString})"
  -- Each definition sees the earlier ones.
  subst ds f := ds.foldr (init := f) fun (d, e) f => s!"(let (({quote d.toString} {e})) {f})"

def toCore (c : CComp) : Fren.Core.Comp String :=
  let props (k : PropKind) := c.props.filter (·.kind == k) |>.map fun p => (p.name, p.smt)
  -- The contract of an uninterpreted function, whose value is an output.
  let contract := c.fn?.isSome && c.vars.any (·.role == .output)
  let core : Fren.Core.Comp String :=
    { path := c.path
      vars := c.vars.map fun v =>
        { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
      assumes := props .assume
      -- A function's postconditions are claims of its own
      -- (`check::postcondition`), and the hypotheses of nothing.
      reqs := if c.fn?.isNone || contract then props .ensure else #[]
      posts := if c.fn?.isSome && !contract then props .ensure else #[]
      fn? := c.fn?
      expects := props .expect
      covers := props .cover
      insts := c.insts.map fun i =>
        { name := i.name, comp := i.comp, bindings := i.bindings, behaviour := i.behaviour, assumes := i.assumes
          typed := i.typed }
      triggers := (c.props.filter fun p => p.kind == .ensure || p.kind == .expect).filterMap fun p =>
        p.trigger?.map (p.name, ·)
      defs := c.defs.map fun (d, e) => (d, s!"(= {quote d.toString} {e})", e)
      -- Numbered in order within each item.
      indexes := c.indexes.mapIdx fun j (n, place, _, goal, t) =>
        { prop := n, k := (c.indexes.extract 0 j).filter (·.1 == n) |>.size, place, goal, patTy? := t.map (·.1) }
      tables := c.tables.mapIdx fun j (n, place, _, q, goal) =>
        { site := { prop := n, k := (c.tables.extract 0 j).filter (·.1 == n) |>.size, place, goal }, goal := q } }
  -- An uninterpreted function's contract, as both front ends build it
  -- (`Fren.Core.contractComp`).
  match contract, c.fn?, c.vars.back? with
  | true, some f, some v => Fren.Core.contractComp core.path f (c.vars.pop.map (·.name)) v.name core.assumes core.reqs core.tables
  | _, _, _ => core

/-- `rs`, results of `c`, with each cover goal's marked if its query uses
an abstract type or an uninterpreted function, as the prelude declarations
that a formula needs say (`Fren.Core.coverInterpreted`). -/
def markInterpreted (p : Prelude) (c : CComp) (rs : Array Fren.Core.CheckResult) : Array Fren.Core.CheckResult :=
  let interprets (f : String) : Bool := p.interprets (quotedSymbols f)
  Fren.Core.withInterpreted { toCore c with typesInterpreted := c.vars.any (interprets ·.ty.sort) } interprets rs

end FrenCli
