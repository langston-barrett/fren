-- keep-sorted start
import FrenCli.Elab
import FrenCli.QueryStore
import FrenCli.SeqElems
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

/-- The prelude (`State.prelude`), with the declarations that each one
mentions. -/
structure Prelude where
  decls : Array PreludeDecl
  /-- The declaration of each symbol. -/
  owner : Std.HashMap String Nat
  /-- The declarations that each declaration mentions. -/
  deps : Array (Array Nat)
  /-- `usedParams decls`, computed once, when first needed, rather than at
  each query. -/
  used : Thunk (Std.HashMap String (Array Bool))
  /-- Each declaration's text as a query has it, with each quoted symbol
  in the solver's name (`queryScript`), computed once, when first needed. -/
  smtTexts : Array (Thunk String)
  /-- The `define-fun`s with quantifiers over elements, which each query
  unfolds (`SeqElems.markedDefs`). -/
  marked : Std.HashMap String (Array String × SeqElems.SExpr) := {}
  /-- The `define-fun`s that a query of a spec with recursion unfolds
  (`queryDefinitions`), computed once, when first needed. -/
  unfolds : Thunk (Std.HashMap String (Array String × SeqElems.SExpr)) := Thunk.pure {}
  /-- Each recursive function's quoted symbol, parameters and parsed body
  (`recursiveQueryFacts`), computed once, when first needed, rather than at
  each query. -/
  recs : Thunk (Array (String × Array String × SeqElems.SExpr)) := Thunk.pure #[]
  /-- The first declaration of each quoted symbol (`quote`), computed once,
  when first needed. -/
  byQuoted : Thunk (Std.HashMap String Nat) := Thunk.pure {}
  /-- The symbols of the recursive functions, and of the definitions of
  `unfolds` whose bodies apply one, directly or through another of them:
  a formula that mentions none of them has no application of a recursive
  function once unfolded (`recursiveQueryFacts`). Computed once, when
  first needed. -/
  recReach : Thunk (Array String) := Thunk.pure #[]
  deriving Inhabited

/-- The `define-fun`s of `decls`, by symbol, with their parameters and
bodies, that a query unfolds before it scans for applications
(`Reqs/Lang/Recursion#solver-encoding`): those whose bodies apply, directly
or through another of them, a recursive or uninterpreted function, or a
selector of `factHeads` (`State.funFacts`), which bring facts. Unfolding the
others finds nothing, and writes each of their bodies once at every
application, which can make a query hundreds of times larger. One of
`marked` is unfolded to its body with its quantifiers over elements still
marked, so that they are expanded where it is applied, as they are where
it is left to the expansion (`solveExpanded`). -/
def queryDefinitions (decls : Array PreludeDecl) (factHeads : Array String)
    (marked : Std.HashMap String (Array String × SeqElems.SExpr)) :
    Std.HashMap String (Array String × SeqElems.SExpr) := Id.run do
  let defs := decls.filterMap fun d => match SeqElems.parse d.text with
    | .list #[.atom "define-fun", .atom f, .list ps, _, body] =>
      some (f, marked[f]?.getD (ps.filterMap (fun | .list #[.atom p, _] => some p | _ => none), body))
    | _ => none
  let mut wanted : Std.HashSet String := .ofArray factHeads
  for d in decls do
    if d.text.startsWith "(declare-fun" then wanted := d.syms.foldl (·.insert <| quote ·) wanted
  let mut out := {}
  -- A definition applies only those before it, but a clause may apply any.
  let mut changed := true
  while changed do
    changed := false
    for (f, ps, body) in defs do
      if !out.contains f && body.mentionsAny wanted then
        out := out.insert f (ps, body)
        wanted := wanted.insert f
        changed := true
  return out

/-- The symbols of the recursive functions of `decls`, and of the
definitions of `defs` whose bodies apply one, directly or through another
of them: the symbols that unfolding with `defs` can turn into an
application of a recursive function. -/
def recursionReach (decls : Array PreludeDecl) (defs : Std.HashMap String (Array String × SeqElems.SExpr)) :
    Array String := Id.run do
  let mut reach : Std.HashSet String := .ofArray (decls.filterMap fun d => d.recursion?.map fun _ => quote d.syms[0]!)
  let mut changed := true
  while changed do
    changed := false
    for (f, _, body) in defs do
      if !reach.contains f && body.mentionsAny reach then
        reach := reach.insert f
        changed := true
  return reach.toArray

def Prelude.ofDecls (decls : Array PreludeDecl) (factHeads : Array String) : Prelude :=
  let marked := SeqElems.markedDefs (decls.map (·.text))
  let decls := if marked.isEmpty then decls else decls.map fun d => { d with text := SeqElems.plainText d.text }
  let owner := decls.zipIdx.foldl (init := {}) fun m (d, i) => d.syms.foldl (·.insert · i) m
  let unfolds := Thunk.mk fun _ => queryDefinitions decls factHeads marked
  { decls, owner, deps := decls.map fun d => (quotedSymbols d.text).filterMap owner.get?
    used := Thunk.mk fun _ => usedParams decls
    smtTexts := decls.map fun d => Thunk.mk fun _ => solverText d.text, marked
    unfolds
    recReach := Thunk.mk fun _ => recursionReach decls unfolds.get
    recs := Thunk.mk fun _ => decls.filterMap fun d => d.recursion?.map fun b => (quote d.syms[0]!, b.1, SeqElems.parse b.2)
    byQuoted := Thunk.mk fun _ => decls.zipIdx.foldl (init := {}) fun m (d, i) =>
      d.syms.foldl (fun m s => if m.contains (quote s) then m else m.insert (quote s) i) m }

/-- The prelude of the queries of `st`'s spec, with the selectors whose
payloads bring facts, which every front end of the CLI asks with. -/
def State.queryPrelude (st : State) : Prelude :=
  Prelude.ofDecls st.prelude (st.funFacts.toArray.map (·.1))

/-- The positions of the declarations that a script whose quoted symbols
are `syms` needs: those of its symbols, and of theirs in turn, in the
order of the prelude.
The others cannot change its answer, and declaring them is most of the
work of a small query. -/
def Prelude.neededDecls (p : Prelude) (syms : Array String) : Array Nat := Id.run do
  let mut keep := Array.replicate p.decls.size false
  let mut work := syms.filterMap p.owner.get?
  while h : work.size > 0 do
    let i := work[work.size - 1]
    work := work.pop
    if keep[i]! then continue
    keep := keep.set! i true
    work := work ++ p.deps[i]!
  return (Array.range p.decls.size).filter (keep[·]!)

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
    if text.startsWith "(declare-sort" || text.startsWith "(declare-fun" || text.contains "(seq.nth (as seq.empty" then return true
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
declares only what the prelude needs to (`Prelude.neededDecls`), and is in
`logic`, but for `ALL` instead of `HO_ALL` if it projects no relation
(`Fren.Core.queryLogic`). -/
def queryScript (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (hyps : Array (Lean.Name × String)) (goal : String) : String :=
  let decls := String.join (vars.toList.map fun v => s!"(declare-const {quote v.name.toString} {v.ty.sort})\n")
  let asserts := String.join (hyps.toList.map fun (n, h) => s!"(assert {h}) ; {n}\n")
  let body := s!"{decls}{asserts}(assert (not {goal}))\n"
  -- `mapQuoted` of the whole script, piece by piece: each piece is whole
  -- commands, which close their quoted symbols and string literals, so
  -- the pieces' are the script's, and the prelude's are computed once.
  let defs := String.join ((prelude.neededDecls (quotedSymbols body)).toList.map (prelude.smtTexts[·]!.get))
  -- Higher-order only if the script, including the definitions that it
  -- includes, projects a relation (`cli::logic`).
  let logic := Fren.Core.queryLogic logic (Fren.Core.projectsRelation defs || Fren.Core.projectsRelation body)
  let head := s!"(set-logic {logic})\n(set-option :produce-models true)\n{limits.options}{options}"
  solverText head ++ defs ++ solverText body

/-- The answers to the queries asked so far, by script, each with whether
it has a model: a script asked again gets the same answer without the
solver (`Reqs/Cli#solver-queries`). The script is the whole query, with its
logic, options and limits, so the same script means the same question. The
checks of several components may share it at once (`Reqs/Cli#parallel-checking`). -/
structure QueryCache where
  /-- By the script and the observations of its model, which are every
  input of `solveScript` but its variables, which the script declares. -/
  answers : IO.Ref (Std.HashMap (String × Array ModelObservation) (Outcome String × Bool))
  /-- The answers kept across runs, if any (`Reqs/Cli#query-cache`). -/
  store? : Option QueryStore := none

/-- A cache with no answers yet, over the persistent `store?`, if any. -/
def QueryCache.new (store? : Option QueryStore := none) : IO QueryCache := do
  return { answers := ← IO.mkRef {}, store? }

def observationsOf (c : CComp) : Array ModelObservation := Id.run do
  let mut out := #[]
  for group in c.memberGroups, g in [0:c.memberGroups.size] do
    for member in group.members, k in [0:group.members.size] do
      let guard := Lean.Name.mkSimple s!"#member_observation_{g}_{k}_guard"
      let value := Lean.Name.mkSimple s!"#member_observation_{g}_{k}_value"
      out := out.push { key := guard, formula := member.evaluationGuard?.getD "true" }
      out := out.push { key := value, formula := member.valueFormula?.getD member.formula, guard? := some guard }
  return out

/-- Checks the satisfiability of `script`, a query over `vars`, with values
of `vars` if `wantModel`. -/
def solveScript (script : String) (vars : Array CVar) (wantModel : Bool) (observations : Array ModelObservation := #[]) : IO (Outcome String) := do
  let r ← cvc5.Env.run do
    let tm ← cvc5.TermManager.new
    let solver ← cvc5.Solver.new tm
    -- cvc5 warns on stderr when a model's value of a quantified formula
    -- cannot be evaluated (`Could not evaluate ... in getValue.`), which the
    -- model then holds as that formula: the warning is not an outcome, and
    -- only cvc5's own diagnostics are silenced.
    solver.setOption "verbosity" "-1"
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
        let value := toString (← solver.getValue t)
        -- cvc5 shares values and qualified constructor symbols with lets.
        -- Expand them before confirmation, rendering, or pinning a model.
        let value := toString ((SeqElems.parse value).unfold {})
        model := model.push (v.name, value)
    for observation in observations do
      let reached := observation.guard?.all fun guard => model.any (fun (name, value) => name == guard && value == "true")
      let value ← if !reached then pure "unknown" else do
        try
          parser.setStringInput observation.formula .SMT_LIB_2_6
          let term ← parser.nextTerm
          pure (toString (← solver.getValue term))
        catch _ => pure "unknown"
      model := model.push (observation.key, value)
    return .sat model
  match r with
  | .ok o => return o
  | .error e => return .unknown s!"solver error: {e}"

/-- Asserts `hyps` and the negation of `goal` and checks satisfiability,
first passing the script to `dump?`, if any, and answering from `cache?`,
if any, a script asked before. -/
def runQuery (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (dump? : Option (String → IO Unit)) (hyps : Array (Lean.Name × String)) (goal : String) (wantModel : Bool)
    (cache? : Option QueryCache := none) (observations : Array ModelObservation := #[]) : IO (Outcome String) := do
  let script := queryScript logic options prelude vars limits hyps goal
  -- Read from the script that would be asked, the definitions that it
  -- includes, its hypotheses and its goal, not from the spec: a query with a
  -- quantifier is never asked in a quantifier-free logic, whatever set it
  -- (`cli::query_logic`).
  unless Fren.Core.queryAsked logic (Fren.Core.hasQuantifier script) do
    return .unknown (Fren.Core.quantifiedQueryReason logic)
  if let some dump := dump? then dump script
  let key := (script, observations)
  let some cache := cache? | solveScript script vars wantModel observations
  -- A model's variables are those that the script declares, which are `vars`.
  match (← cache.answers.get)[key]? with
  | some (o@(.sat _), hasModel) =>
    if !wantModel then return .sat #[]
    if hasModel then return o
  | some (o, _) => return o
  | none => pure ()
  -- Then from the answers kept across runs (`cli::query_cache`).
  if let some store := cache.store? then
    if let some (o, hasModel) ← store.lookup? script observations wantModel then
      cache.answers.modify (·.insert key (o, hasModel))
      return if wantModel then o else match o with | .sat _ => .sat #[] | _ => o
  let o ← solveScript script vars wantModel observations
  cache.answers.modify (·.insert key (o, wantModel))
  if let some store := cache.store? then store.record script observations o wantModel
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

/-- The symbol that a variant of one of the prelude's types would have if it
were a user's, `Option::Some`, for lean-smt's constructor `c` of the Lean
type that it is, `Option.some` (`Reqs/Lang/Prelude#smt`). -/
def preludeCtor? (c : String) : Option String :=
  Fren.Core.leanTypes.findSome? fun l =>
    (l.ctors.idxOf? c.toName).map fun i => s!"{l.name}::{l.variants[i]!}"

/-- `t`, with a generic type's constructor, which cvc5 writes qualified by
its sort, `(as C (D Int))`, as a constructor of any other type, and a
prelude type's, which is a Lean constructor, as Fren names it. -/
def unqualify : Term → Term
  | .atom c => if let some f := preludeCtor? c then .atom f
    else if !c.startsWith "\"" && c.contains '~' then .atom (genericCtor c) else .atom c
  | .list ts => match ts[0]? with
    | some (Term.atom "as") => match ts[1]? with
      | some (Term.atom c) => if let some f := preludeCtor? c then .atom f
        else if c.contains '~' then .atom (genericCtor c) else .list ts
      | _ => .list ts
    | some (Term.list #[.atom "as", .atom c, _]) =>
      if let some f := preludeCtor? c then .list (#[.atom f] ++ ts.extract 1)
      else if c.contains '~' then .list (#[.atom (genericCtor c)] ++ ts.extract 1) else .list ts
    | some (Term.atom c) => if let some f := preludeCtor? c then .list (#[.atom f] ++ ts.extract 1) else .list ts
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

/-- Whether the SMT-LIB text `t` mentions the symbol `x`, as written, quoted
or not, as a whole token. -/
def mentionsSymbol (t x : String) : Bool :=
  let parts := t.splitOn x
  parts.length > 1 && (List.range (parts.length - 1)).any fun k =>
    let before := (parts[k]!.toList.getLast?).getD ' '
    let after := (parts[k + 1]!.toList.head?).getD ' '
    let delim (c : Char) := c == ' ' || c == '(' || c == ')' || c == '\n'
    (x.startsWith "|" || delim before) && (x.endsWith "|" || delim after)

/-- `f` without the bindings of its `let`s whose names their bodies do not
mention, as the Lean front end's `zetaReduce` drops them: an application
in such a binding is not one of the query's, so it brings no facts
(`Fren.Core.appFactsWith`), in both front ends. A `let` with no binding
left is its body. -/
partial def dropUnusedLets (f : String) : String := Id.run do
  let cs := f.toList.toArray
  let pat := "(let (".toList.toArray
  let mut i := 0
  let mut inString := false
  while h : i < cs.size do
    let c := cs[i]
    if c == '"' then inString := !inString
    else if !inString && c == '(' && i + pat.size ≤ cs.size && (List.range pat.size).all (fun k => cs[i + k]! == pat[k]!) then
      let whole := balancedAt cs i
      let j := i + 5
      let list := balancedAt cs j
      -- Its bindings, each `(name value)`.
      let mut bindings : Array (String × String) := #[]
      let mut k := j + 1
      while k < j + list.length - 1 do
        if cs[k]! == '(' then
          let b := balancedAt cs k
          let inner := ((b.drop 1).dropEnd 1).toString
          let name := (inner.takeWhile (· != ' ')).toString
          bindings := bindings.push (name, b)
          k := k + b.length
        else k := k + 1
      let bodyStart := j + list.length + 1
      let bodyEnd := i + whole.length - 1
      if bodyStart ≤ bodyEnd then
        let body := String.ofList (cs.extract bodyStart bodyEnd).toList
        let kept := bindings.filter fun (x, _) => mentionsSymbol body x
        if kept.size < bindings.size then
          let replaced := if kept.isEmpty then body else s!"(let ({" ".intercalate (kept.toList.map (·.2))}) {body})"
          let before := String.ofList (cs.extract 0 i).toList
          let after := String.ofList (cs.extract (i + whole.length) cs.size).toList
          return dropUnusedLets (before ++ replaced ++ after)
    i := i + 1
  return f

-- A dead binding, one that is dead only once the binding within it is
-- dropped, one dead binding of two, a quoted symbol that is used, and a
-- name mentioned only in a string literal, which is kept, conservatively.
#guard dropUnusedLets "(let ((|x| (f 1))) true)" == "true"
#guard dropUnusedLets "(and (let ((|z| (f 1))) (let ((|w| |z|)) true)) b)" == "(and true b)"
#guard dropUnusedLets "(let ((|x| 1) (|y| (f 2))) (> |x| 0))" == "(let ((|x| 1)) (> |x| 0))"
#guard dropUnusedLets "(let ((|x| 1)) (|f| |x|))" == "(let ((|x| 1)) (|f| |x|))"
#guard dropUnusedLets "(let ((|x| (f 1))) (= s \"|x|\"))" == "(let ((|x| (f 1))) (= s \"|x|\"))"

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
`Nat`, into a subset type or with postconditions, or a read of a
recursive enumeration's payload of a subset type, brings
(`Fren.Core.appFactsWith`), from what `funs` says of its function
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

/-- Whether a query of the formulas `fs` has a quantifier over elements to
expand, directly or in a `define-fun` of `marked` that it applies. -/
def needsExpansion (marked : Std.HashMap String (Array String × SeqElems.SExpr)) (fs : Array String) : Bool :=
  fs.any fun f => SeqElems.hasMarker f || marked.keys.any fun g => (f.splitOn g).length > 1

/-- The answer to the query of `hyps` and `goal`, with its quantifiers over
elements expanded (`SeqElems.expandQuery`), asked by `ask` of its
variables, hypotheses and goal: at the index set, with the fresh constants
and length constants as variables of their own; and, if that has a model,
again at every position, with the sequences' lengths pinned to the
model's, whose model is real. That second query is unsatisfiable only if a
model of the first is not one of the quantified query at its lengths
(`Fren.Core.elementUnconfirmedReason`), and either may have more instances
than `Fren.Core.maxElementInstances` (`Fren.Core.elementLimitReason`): the
check is then inconclusive (`Reqs/Lang/ElementQuantifiers#expansion`). -/
def solveExpanded (marked : Std.HashMap String (Array String × SeqElems.SExpr))
    (ask : Array CVar → Array (Lean.Name × String) → String → Bool → IO (Outcome String)) (vars : Array CVar)
    (hyps : Array (Lean.Name × String)) (goal : String) (wantModel : Bool) : IO (Outcome String) := do
  let unquote (c : String) : String := ((c.drop 1).dropEnd 1).toString
  let fresh (c : String) : CVar := { name := .mkSimple (unquote c), role := .input, isPub := false, ty := .int, span := default }
  match SeqElems.expandQuery marked hyps goal with
  | .error n => return .unknown (Fren.Core.elementLimitReason n)
  | .ok ex =>
    let o ← ask (vars ++ ex.consts.map fresh) ex.hyps ex.goal (wantModel || !ex.lengths.isEmpty)
    let .sat m := o | return o
    let consts := ex.consts.map unquote
    let model := m.filter fun (n, _) => !consts.contains n.toString
    if ex.lengths.isEmpty then return .sat model
    let pins := ex.lengths.filterMap fun (l, q) => do
      let (_, v) ← m.find? (·.1.toString == unquote l)
      let k ← (v.replace " " "").toNat?
      pure (q, k)
    unless pins.size == ex.lengths.size do return .unknown Fren.Core.elementUnconfirmedReason
    match SeqElems.expandQuery marked hyps goal (some pins) with
    | .error n => return .unknown (Fren.Core.elementLimitReason n)
    | .ok ex =>
      match ← ask vars ex.hyps ex.goal wantModel with
      | .unsat => return .unknown Fren.Core.elementUnconfirmedReason
      | o => return o

/-- A recursive contract's own result stands for its body, once. -/
partial def contractBody (own : SeqElems.SExpr) (body : SeqElems.SExpr) (e : SeqElems.SExpr) : SeqElems.SExpr :=
  if e == own then body else match e with
  | .list xs => .list (xs.map (contractBody own body))
  | _ => e

/-- Finite one-step reflection. Nonrecursive definitions and clauses are
expanded before finding applications; equation-introduced applications receive
only contract facts. Guards follow the original conditional branches. -/
partial def recursiveQueryFacts (prelude : Prelude) (funs : Std.HashMap String (Bool × Contract))
    (types : Std.HashMap String String) (hyps : Array (Lean.Name × String)) (goal : String)
    (mentioned : Std.HashSet String) : Array (Lean.Name × String) := Id.run do
  let recs := prelude.recs.get
  if recs.isEmpty then return #[]
  -- Unfolding brings an application of a recursive function only into a
  -- formula that mentions one, or a definition that applies one.
  -- `mentioned` has the names of the formulas' quoted symbols
  -- (`quotedSymbols`); a symbol that is not quoted is taken to be
  -- mentioned.
  let mentions (r : String) : Bool :=
    if r.length ≥ 2 && r.startsWith "|" && r.endsWith "|" then mentioned.contains ((r.drop 1).dropEnd 1).toString
    else true
  unless prelude.recReach.get.any mentions do return #[]
  let defs := prelude.unfolds.get
  let expand (s : String) := (SeqElems.parse s).unfold defs
  let mut work := #[]
  for f in hyps.map (·.2) |>.push goal do
    work := work ++ scan recs (expand f) #[] false #[]
  let mut out := #[]
  let mut seen : Std.HashSet (SeqElems.SExpr × Array String × Bool) := {}
  let mut done := 0
  while done < work.size do
    let (app, gs, introduced, ancestors) := work[done]!
    done := done + 1
    let key := (app, gs, introduced)
    if seen.contains key then continue
    seen := seen.insert key
    let .list xs := app | continue
    let .atom head := xs[0]! | continue
    let args := xs.extract 1
    let text := toString app
    if ancestors.contains text then continue
    let ancestors := ancestors.push text
    let guarded (f : String) := if gs.isEmpty then f else s!"(=> {conj gs} {f})"
    let domain := ((prelude.byQuoted.get[head]?.bind (prelude.decls[·]?)).map fun d =>
      let ps := (d.recursion?.map (·.1)).getD #[]
      d.domain.map fun f => toString ((SeqElems.parse f).subst (ps.zip args))).getD #[]
    for (n, f) in appFactsOf funs types text do
      let f := expand f
      out := out.push (n, guarded (if domain.isEmpty then toString f else s!"(=> {conj domain} {f})"))
      work := work ++ scan recs f gs introduced ancestors
    if (Fren.Core.recursiveFacts introduced).2 then
      if let some (_, ps, body) := recs.find? (·.1 == head) then
        let body := (body.subst (ps.zip args)).unfold defs
        out := out.push (`equation, guarded s!"(= {text} {body})")
        work := work ++ scan recs body gs true ancestors
  -- Each fact once, where it first occurs.
  let mut kept : Std.HashSet (Lean.Name × String) := {}
  let mut facts := #[]
  for f in out do
    unless kept.contains f do
      kept := kept.insert f
      facts := facts.push f
  return facts
where
  scan (recs : Array (String × Array String × SeqElems.SExpr)) (e : SeqElems.SExpr)
      (gs : Array String) (introduced : Bool) (ancestors : Array String) (bound : Array String := #[]) :
      Array (SeqElems.SExpr × Array String × Bool × Array String) :=
    match e with
    | .atom _ => #[]
    | .list xs => Id.run do
      let own := match xs[0]? with
        | some (SeqElems.SExpr.atom h) => if recs.any (·.1 == h) && (Fren.Core.recursiveFacts introduced (e.mentions bound)).1 then
          -- With nothing bound, no guard mentions a bound name.
          let gs := if bound.isEmpty then gs else gs.filter fun g => !(SeqElems.parse g).mentions bound
          #[(e, gs, introduced, ancestors)] else #[]
        | _ => #[]
      if let some (names, body) := SeqElems.binderOf? e then
        return scan recs body gs introduced ancestors (bound ++ names)
      if xs[0]? == some (SeqElems.SExpr.atom "and") || xs[0]? == some (SeqElems.SExpr.atom "or") then
        let mut result := own
        let mut guards := gs
        for x in xs.extract 1 do
          result := result ++ scan recs x guards introduced ancestors bound
          guards := guards.push (if xs[0]? == some (SeqElems.SExpr.atom "and") then toString x else s!"(not {x})")
        return result
      match xs with
      | #[.atom "ite", c, a, b] =>
        return own ++ scan recs c gs introduced ancestors bound
          ++ scan recs a (gs.push (toString c)) introduced ancestors bound
          ++ scan recs b (gs.push s!"(not {c})") introduced ancestors bound
      | #[.atom "=>", c, b] =>
        return own ++ scan recs c gs introduced ancestors bound ++ scan recs b (gs.push (toString c)) introduced ancestors bound
      | _ => return own ++ xs.flatMap fun x => scan recs x gs introduced ancestors bound

/-- The backend for `c`, where `strings` and `sets` say whether the spec uses
strings and sets, and `projection` whether it projects a relation over a
type that is not finite, which puts in `HO_ALL` those of its queries that
do (`cli::logic`, `queryScript`); answering from `cache?`, if any,
the scripts asked before (`runQuery`). -/
def backend (prelude : Prelude) (dts : Array DataDecl) (c : CComp) (limits : Limits) (dump? : Option (String → IO Unit) := none)
    (strings sets : Bool := false) (projection : Bool := false) (cache? : Option QueryCache := none) (quantified : Bool := false)
    (funs : Std.HashMap String (Bool × Contract) := {}) (kind : Fren.Core.CheckKind)
    (contractFns : Std.HashMap String Lean.Name := {}) (applied? : Option (IO.Ref (Array Lean.Name)) := none) :
    Fren.Core.Backend IO String String where
  -- cvc5 refuses some string operations without `strings-exp`. Every query
  -- has what the `Nat` variables bring, of both copies, and what the
  -- applications that it mentions bring (`Reqs/Check`).
  -- The query declares only the variables that its formulas mention, a
  -- `Nat`'s fact among them, so a model, and so a counterexample, has only
  -- those, as in Lean (`Reqs/View#check-results`).
  modelBool? := some fun model formula => pure <|
    (observationsOf c).findSome? fun observation =>
      if observation.formula != formula then none else
      match model.find? (·.1 == observation.key) |>.map (·.2) with
      | some "true" => some true
      | some "false" => some false
      | _ => none
  query hyps goal wantModel := do
    let hasRecursion := prelude.decls.any (·.recursion?.isSome)
    let expand (f : String) : String := Id.run do
      if !hasRecursion then return f
      let e := (SeqElems.parse f).unfold prelude.unfolds.get
      let some fn := c.fn? | return toString e
      let some d := prelude.decls.find? (·.syms.contains ((itemSym fn).drop 1 |>.dropEnd 1 |>.toString)) | return toString e
      let some (ps, body) := d.recursion? | return toString e
      let own := SeqElems.SExpr.list (#[.atom (itemSym fn)] ++ ps.map SeqElems.SExpr.atom)
      return toString (contractBody own (SeqElems.parse body) e)
    let hyps := hyps.map fun (n, f) => (n, expand f)
    let goal := expand goal
    -- Observe the same unfolded terms in the primary model. Keys retain
    -- their source identity for modelBool? above.
    let observations := (observationsOf c).map fun observation =>
      { observation with formula := expand observation.formula }
    let facts := c.natFacts false ++ c.natFacts true
    let facts := facts ++ (facts.map fun (n, f) => (n, prime c f)).filter (!facts.contains ·)
    let formulas := facts.map (·.2) ++ hyps.map (·.2) |>.push goal
    let mentioned : Std.HashSet String := .ofArray (formulas.flatMap quotedSymbols)
    let vars := (c.vars ++ primes c).filter (mentioned.contains ·.name.toString)
    -- A model shows those that the formulas mention once their definitions
    -- are unfolded, as Lean's does (`termMentions`).
    let used := prelude.used.get
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
    -- And the functions whose contracts those facts have, which its check
    -- rests on, but its own function's, in its own contract
    -- (`Fren.Core.appFactsWith`).
    let fnOf (app : String) : Option Lean.Name :=
      let inner := (splitLets app).2.1
      contractFns.get? ((inner.drop 1).takeWhile (· != ' ')).toString
    let (appFacts, fns) := Fren.Core.appFactsWith (m := Id) appsOf (appFactsOf funs c.funFacts) fnOf
      (hyps.map fun (n, f) => (n, dropUnusedLets f)) (dropUnusedLets goal) c.fn?
    if let some r := applied? then
      r.modify fun acc => fns.foldl (init := acc) fun acc f => if acc.contains f then acc else acc.push f
    -- A procedure whose queries may quantify sets `fmf-bound`
    -- (`State.bounded`).
    let hyps := facts ++ appFacts ++ recursiveQueryFacts prelude funs c.funFacts hyps goal mentioned ++ hyps
    let options := Fren.Core.solverOptions strings sets ++ (if c.bounded then Fren.Core.boundedOptions else [])
      -- The contract of a generic function without a body, at its type
      -- parameters' sorts, with finite-model finding.
      ++ (if c.generic || c.finiteModel then Fren.Core.finiteModelOptions else [])
    -- A recursive definition needs a logic with quantifiers.
    let logic := Fren.Core.logic kind (strings || sets) projection quantified
    let options := String.join ((options ++ Fren.Core.quantifierOptions logic).map fun (o, v) => s!"(set-option :{o} {v})\n")
    let o ← if needsExpansion prelude.marked (hyps.map (·.2) |>.push goal) then
        solveExpanded prelude.marked (runQuery logic options prelude · limits dump? · · · cache? observations) vars hyps goal
          wantModel
      else runQuery logic options prelude vars limits dump? hyps goal wantModel cache? observations
    return match o with
      | .sat m => .sat (m.filter fun (n, _) => shown.contains n.toString || n.toString.startsWith "#member_observation_")
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
      inhabitation := c.subset?.isSome
      branchGroups := c.branchGroups
      memberGroups := c.memberGroups
      vars := c.vars.map fun v =>
        { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
      assumes := props .assume
      laws := c.laws
      lawsOf := c.lawsOf
      -- A function's postconditions are claims of its own
      -- (`check::postcondition`), and the hypotheses of nothing.
      reqs := if c.fn?.isNone || contract then props .ensure else #[]
      posts := if c.fn?.isSome && !contract then props .ensure else #[]
      recursive := c.recursive
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
        { prop := n, k := (c.indexes.extract 0 j).filter (·.1 == n) |>.size, place, goal, subsetTy? := t.map (·.1), excludeSelf := c.distributed.contains n }
      tables := c.tables.mapIdx fun j (n, place, _, q, goal) =>
        { site := { prop := n, k := (c.tables.extract 0 j).filter (·.1 == n) |>.size, place, goal, excludeSelf := c.distributed.contains n }, goal := q } }
  -- An uninterpreted function's contract, as both front ends build it
  -- (`Fren.Core.contractComp`).
  match contract, c.fn?, c.vars.back? with
  | true, some f, some v =>
    Fren.Core.contractComp core.path f (c.vars.pop.map (·.name)) v.name core.assumes core.reqs core.tables c.generic
      core.branchGroups core.memberGroups
  | _, _, _ => core

/-- `rs`, results of `c`, with each cover goal's marked if its query uses
an abstract type or an uninterpreted function, as the prelude declarations
that a formula needs say (`Fren.Core.coverInterpreted`). -/
def markInterpreted (p : Prelude) (c : CComp) (rs : Array Fren.Core.CheckResult) : Array Fren.Core.CheckResult :=
  let interprets (f : String) : Bool := f.contains "(seq.nth (as seq.empty" || p.interprets (quotedSymbols f)
  Fren.Core.withInterpreted { toCore c with typesInterpreted := c.vars.any (interprets ·.ty.sort) } interprets rs

end FrenCli
