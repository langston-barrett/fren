-- keep-sorted start
import FrenCli.Cvc5
import FrenCli.Elab
import FrenCli.QueryStore
import FrenCli.SeqElems
import FrenCli.SolverSorts
import FrenCli.SolverStats
import FrenCore.Check
import FrenCore.Goals
import FrenCore.SolverTime
import FrenCore.Symbols
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
  /-- Payload and field types, for initializing tuples at instances. -/
  datatypes : Array DataDecl := #[]
  /-- No per-query traversal when the declarations have no implicit tuple. -/
  tupleSortsNeeded : Bool := false
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

def Prelude.ofDecls (decls : Array PreludeDecl) (factHeads : Array String) (datatypes : Array DataDecl := #[]) : Prelude :=
  let marked := SeqElems.markedDefs (decls.map (·.text))
  let decls := if marked.isEmpty then decls else decls.map fun d => { d with text := SeqElems.plainText d.text }
  let owner := decls.zipIdx.foldl (init := {}) fun m (d, i) => d.syms.foldl (·.insert · i) m
  let unfolds := Thunk.mk fun _ => queryDefinitions decls factHeads marked
  { decls, datatypes, tupleSortsNeeded := SolverSorts.needed datatypes, owner, deps := decls.map fun d => (quotedSymbols d.text).filterMap owner.get?
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
  Prelude.ofDecls st.prelude (st.funFacts.toArray.map (·.1)) st.datatypes

/-- A `State`, `st`, with what checking each of its items reads of it that
is the same for every item (`FrenCli.solveComp`), built once for all of
them (`State.forSolving`) rather than for each. Each field is, by its
proof, what the `State` function of its name gives of `st`, and
`prelude` what `State.queryPrelude` gives, so none can be another
`State`'s, such as a mutant's. -/
structure Solving where
  st : State
  appFuns : Std.HashMap String (Bool × Contract)
  contractFns : Std.HashMap String Lean.Name
  recursiveSyms : Std.HashMap String Lean.Name
  instanceSites : Array (Fren.Core.InstanceSite × Lean.Name × Array Fren.Core.Ty)
  prelude : Prelude
  appFuns_eq : appFuns = st.appFuns
  contractFns_eq : contractFns = st.contractFns
  recursiveSyms_eq : recursiveSyms = st.recursiveSyms
  instanceSites_eq : instanceSites = st.instanceSites
  prelude_eq : prelude = st.queryPrelude

/-- `s`, with its maps and prelude for checking its items, each computed
once. -/
def State.forSolving (s : State) : Solving :=
  { st := s, appFuns := s.appFuns, contractFns := s.contractFns, recursiveSyms := s.recursiveSyms
    instanceSites := s.instanceSites, prelude := s.queryPrelude, appFuns_eq := rfl, contractFns_eq := rfl
    recursiveSyms_eq := rfl, instanceSites_eq := rfl, prelude_eq := rfl }

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

-- cvc5 checks both limits only where it spends resources, and cvc5 1.3.x's
-- strings solver (which also decides sequences) can loop in
-- `TheoryStrings::postCheck` → `BaseSolver::checkInit` without spending
-- any, so that neither `--timeout` nor `--resource-limit` stops the
-- query, and `fren check` hangs (#297; cvc5 1.3.2 and 1.3.4, recorded on
-- #549, not reported). The query that found it, minimized to 88 commands,
-- had a datatype with `String` fields (`Val`), a `Seq` of it built with
-- `seq.++` of `seq.unit`s and read with `seq.nth` under a bounds `ite`,
-- string-valued selectors compared with string literals, and sets of
-- `String` and `Int` tuples (`set.member`, `set.subset`), from two
-- `lang::node` instances at 527d4ee. No encoding choice is known to avoid
-- the loop, and no current spec reaches it: on 7bf7cc0, none of the
-- 14,002 distinct queries of `src/Reqs`, `test/` and `examples/` ran past
-- a 1 s `tlimit-per` (the slowest took 0.85 s).
/-- The options that set `limits`. A script without a resource limit sets
none, so that it is the script that `fren` wrote before the limit
existed. -/
def Limits.options (limits : Limits) : String :=
  s!"(set-option :tlimit-per {limits.timeoutSecs * 1000})\n" ++
    if limits.resources == 0 then "" else s!"(set-option :rlimit-per {limits.resources})\n"

open SeqElems (SExpr) in
/-- The head of a goal of `fren check`, as `Fren.Core.introduceGoal` reads
it (`Reqs/Cli#goal-introduction`): `(forall ((x S) ...) body)`,
`(=> p q ...)` and `(let (...) body)`, the last with its definitions
substituted. A bound name becomes the constant `(x', S)`, where `x'` is
`Fren.Core.goalConstantName` of the symbols that the state has, the
query's, and the prelude's declarations; the state gets `x'`. The state
is computed only when a bound name needs it. -/
def smtGoalHead (prelude : Prelude) (e : SExpr) :
    StateM (Thunk (Std.HashSet String)) (Fren.Core.GoalHead (String × String) SExpr) := do
  match e with
  | .list #[.atom "forall", .list decls, body] =>
    let some (SExpr.list #[.atom x, sort]) := decls[0]? | return .other
    let rest := if decls.size == 1 then body else .list #[.atom "forall", .list (decls.extract 1), body]
    let taken := (← get).get
    let base := SeqElems.unquoted x
    let name := Fren.Core.goalConstantName (fun s => taken.contains s || prelude.owner.contains s) base
      (taken.size + prelude.owner.size + 1)
    set (Thunk.pure (taken.insert name))
    if name == base then return .universal (x, sort.toString) rest
    return .universal (quote name, sort.toString) (rest.subst #[(x, .atom (quote name))])
  | .list ts =>
    match ts[0]? with
    | some (SExpr.atom "=>") =>
      if ts.size < 3 then return .other
      return .premise ts[1]! (if ts.size == 3 then ts[2]! else .list (#[SExpr.atom "=>"] ++ ts.extract 2))
    | some (SExpr.atom "let") =>
      let #[_, .list binds, body] := ts | return .other
      let σ := binds.filterMap fun | SExpr.list #[.atom x, d] => some (x, d) | _ => none
      if σ.size != binds.size then return .other
      return .definition (body.subst σ)
    | _ => return .other
  | _ => return .other

/-- `goal`, a goal over `vars` with the hypotheses `hyps`, with its leading
heads introduced (`Fren.Core.introduceGoal`, `smtGoalHead`): its constants,
each with its sort, its premises, and the goal left. The hypotheses are
read only if a bound name is introduced. A goal with nothing to introduce
is left as it is written. -/
def introduceSmtGoal (prelude : Prelude) (vars : Array CVar) (hyps : Array (Lean.Name × String)) (goal : String) :
    Array (String × String) × Array String × String :=
  let parsed := SeqElems.parse goal
  let taken : Thunk (Std.HashSet String) := Thunk.mk fun _ => .ofArray (vars.map (·.name.toString (escape := false)) ++
    (hyps.flatMap fun (_, h) => (SeqElems.parse h).freeAtoms) ++ parsed.freeAtoms)
  let r := (Fren.Core.introduceGoal (smtGoalHead prelude) parsed).run' taken
  if r.steps.isEmpty then (#[], #[], goal)
  else (r.constants, r.premises.map toString, toString r.goal)

-- Bound names and premises in any order, through a `let`; a bound name
-- that the hypotheses have free, or an earlier constant has, is renamed.
#guard introduceSmtGoal default #[] #[] "(forall ((|x| Int) (|y| Int)) (=> (> |x| 0) (> |y| |x|)))" ==
  (#[("|x|", "Int"), ("|y|", "Int")], #["(> |x| 0)"], "(> |y| |x|)")
#guard introduceSmtGoal default #[] #[(`h, "(> |x| 1)")] "(forall ((|x| Int)) (> |x| 0))" ==
  (#[("|x#goal0|", "Int")], #[], "(> |x#goal0| 0)")
#guard introduceSmtGoal default #[] #[] "(forall ((|x| Int)) (=> (> |x| 0) (forall ((|x| Int)) (> |x| 1))))" ==
  (#[("|x|", "Int"), ("|x#goal0|", "Int")], #["(> |x| 0)"], "(> |x#goal0| 1)")
#guard introduceSmtGoal default #[] #[] "(let ((|d| 1)) (forall ((|x| Int)) (=> a b c)))" ==
  (#[("|x|", "Int")], #["a", "b"], "c")
-- A goal with nothing to introduce is left as it is written.
#guard introduceSmtGoal default #[] #[] "(and  a b)" == (#[], #[], "(and  a b)")

/-- The SMT-LIB script that asserts `hyps` and the negation of `goal`, each
hypothesis followed by a comment with its name; without `(check-sat)`. The
goal's leading heads are introduced first (`introduceSmtGoal`): its
constants are declared after the variables, and its premises asserted
after the hypotheses, each followed by the comment `; premise`. It
declares only what the prelude needs to (`Prelude.neededDecls`), and is in
`logic`, but for `ALL` instead of `HO_ALL` if it projects no relation
(`Fren.Core.queryLogic`). -/
def queryScript (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (hyps : Array (Lean.Name × String)) (goal : String) : String :=
  let (constants, premises, goal) := introduceSmtGoal prelude vars hyps goal
  let decls := String.join (vars.toList.map fun v => s!"(declare-const {quote (v.name.toString (escape := false))} {v.ty.sort})\n")
  let decls := decls ++ String.join (constants.toList.map fun (x, s) => s!"(declare-const {x} {s})\n")
  let asserts := String.join (hyps.toList.map fun (n, h) => s!"(assert {h}) ; {n.toString (escape := false)}\n")
  let asserts := asserts ++ String.join (premises.toList.map fun p => s!"(assert {p}) ; premise\n")
  let body := s!"{decls}{asserts}(assert (not {goal}))\n"
  -- `mapQuoted` of the whole script, piece by piece: each piece is whole
  -- commands, which close their quoted symbols and string literals, so
  -- the pieces' are the script's, and the prelude's are computed once.
  let needed := prelude.neededDecls (quotedSymbols body)
  let tuples := if prelude.tupleSortsNeeded then
      SolverSorts.tupleSorts prelude.datatypes (String.join (needed.toList.map (prelude.decls[·]!.text)) ++ body)
    else #[]
  -- cvc5's implicit substitution into a datatype does not initialize its
  -- concrete tuple encodings. Register them after their last sort
  -- dependency, before a definition or assertion can use the instance.
  let aliases := tuples.mapIdx fun i sort =>
    let deps := (quotedSymbols sort).filterMap prelude.owner.get?
    let after := deps.foldl (fun acc k => some (max (acc.getD k) k)) none
    (after, solverText s!"(define-sort |#fren.tuple.{i}| () {sort})\n")
  let defs := if aliases.isEmpty then String.join (needed.toList.map (prelude.smtTexts[·]!.get)) else
    needed.foldl (init := String.join ((aliases.filter (·.1.isNone)).toList.map (·.2))) fun acc k =>
      acc ++ prelude.smtTexts[k]!.get ++ String.join ((aliases.filter (·.1 == some k)).toList.map (·.2))
  -- Higher-order only if the script, including the definitions that it
  -- includes, projects a relation (`cli::logic`).
  let logic := Fren.Core.queryLogic logic (Fren.Core.projectsRelation defs || Fren.Core.projectsRelation body)
  let head := s!"(set-logic {logic})\n(set-option :produce-models true)\n{limits.options}{options}"
  solverText head ++ defs ++ solverText body

/-- How many maps `QueryCache` splits its answers into. The threads of
`fren check` share the cache, and so each map is multi-threaded: reading
one takes it from its reference with an atomic exchange, and a map that
another thread can reach is never updated in place, so adding an answer
copies the map's buckets and marks the copy multi-threaded. With one
map, a warm `fren check` of Fren's own spec at 8 jobs spent about 8 % of
its cycles there: 5.7 % in reading and taking it, where threads wait for
each other, and the rest in copying and marking it (#701). With 64, two
threads seldom want the same map at once, and each copy is of about a
64th of the answers. -/
def answerShards : Nat := 64

/-- Which of the `answerShards` maps holds `k`: by its hash, as a map
picks a bucket, so that keys that are equal are in the same one. -/
def answerShard [Hashable α] (k : α) : Fin answerShards :=
  ⟨(hash k).toNat % answerShards, Nat.mod_lt _ (by decide)⟩

/-- Maps split by `answerShard`, as values: what `QueryCache.answers`
holds. `QueryCache.find?` and `QueryCache.insert` mirror `get?` and
`insert`, on the reference of the same map, rather than call them: no
theorem is about `QueryCache` itself. `get?` and `insert` behave as one
map does (`Shards.get?_insert`, `Shards.get?_empty`, `Shards.get?_foldl`),
and over keys with their hashes, as one map of the plain keys does
(`Shards.get?_foldl_of`). -/
abbrev Shards (α β : Type) [BEq α] [Hashable α] := Vector (Std.HashMap α β) answerShards

/-- No key, in any map. -/
def Shards.empty [BEq α] [Hashable α] : Shards α β := Vector.replicate answerShards {}

/-- What `k` maps to, from its map. -/
def Shards.get? [BEq α] [Hashable α] (s : Shards α β) (k : α) : Option β :=
  s[answerShard k][k]?

/-- `k` mapped to `v`, in its map. -/
def Shards.insert [BEq α] [Hashable α] (s : Shards α β) (k : α) (v : β) : Shards α β :=
  s.set (answerShard k) (s[answerShard k].insert k v)

/-- As in one map (`Std.HashMap.getElem?_insert`): a key gets the last
value inserted for an equal key. -/
theorem Shards.get?_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (s : Shards α β) (k k' : α)
    (v : β) : (s.insert k v).get? k' = if k == k' then some v else s.get? k' := by
  simp only [Shards.get?, Shards.insert, Fin.getElem_fin, Vector.getElem_set]
  split
  · next h => rw [Std.HashMap.getElem?_insert]; simp only [h]
  · next h =>
    have hne : (k == k') = false := by
      cases hb : k == k'
      · rfl
      · exact absurd (by simp [answerShard, hash_eq hb]) h
    simp [hne]

/-- As in one map (`Std.HashMap.getElem?_empty`). -/
theorem Shards.get?_empty [BEq α] [Hashable α] (k : α) : (Shards.empty : Shards α β).get? k = none := by
  simp [Shards.get?, Shards.empty]

/-- The same answers as one map of the same keys that is given the same
insertions. -/
theorem Shards.get?_foldl [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (kvs : List (α × β)) (k : α) :
    (kvs.foldl (fun s (k, v) => s.insert k v) Shards.empty).get? k
      = (kvs.foldl (fun m (k, v) => m.insert k v) ({} : Std.HashMap α β))[k]? := by
  suffices h : ∀ (s : Shards α β) (m : Std.HashMap α β), (∀ k, s.get? k = m[k]?) →
      ∀ k, (kvs.foldl (fun s (k, v) => s.insert k v) s).get? k = (kvs.foldl (fun m (k, v) => m.insert k v) m)[k]? from
    h _ _ (fun k => by simp [Shards.get?_empty]) k
  induction kvs with
  | nil => intro s m h; exact h
  | cons kv kvs ih =>
    intro s m h
    apply ih
    intro k'
    rw [Shards.get?_insert, Std.HashMap.getElem?_insert, h]

/-- A key with its hash, computed once (`Hashed.of`): a map that holds it
neither hashes it again to look it up, to add it nor to grow, which for a
query's script is a pass over the whole text each time. Two are equal only
if their hashes are, so the hash is lawful whatever `α`'s is. `code_eq`,
which is erased at runtime, keeps the hash from going stale: a key built
with another hash would miss its equal and land in another map. -/
structure Hashed (α : Type) [Hashable α] where
  key : α
  code : UInt64
  code_eq : code = hash key

/-- `k`, with its hash. -/
def Hashed.of [Hashable α] (k : α) : Hashed α := ⟨k, hash k, rfl⟩

instance [Hashable α] : Hashable (Hashed α) := ⟨Hashed.code⟩

instance [Hashable α] [BEq α] : BEq (Hashed α) := ⟨fun a b => a.code == b.code && a.key == b.key⟩

theorem Hashed.beq_iff [Hashable α] [BEq α] (a b : Hashed α) : (a == b) = true ↔ a.code = b.code ∧ (a.key == b.key) = true := by
  show (a.code == b.code && a.key == b.key) = true ↔ _
  simp

instance [Hashable α] [BEq α] : LawfulHashable (Hashed α) where
  hash_eq a b h := ((Hashed.beq_iff a b).1 h).1

instance [Hashable α] [BEq α] [EquivBEq α] : EquivBEq (Hashed α) where
  rfl := (Hashed.beq_iff _ _).2 ⟨rfl, BEq.rfl⟩
  symm h := by
    have ⟨h₁, h₂⟩ := (Hashed.beq_iff _ _).1 h
    exact (Hashed.beq_iff _ _).2 ⟨h₁.symm, BEq.symm h₂⟩
  trans h h' := by
    have ⟨h₁, h₂⟩ := (Hashed.beq_iff _ _).1 h
    have ⟨h₁', h₂'⟩ := (Hashed.beq_iff _ _).1 h'
    exact (Hashed.beq_iff _ _).2 ⟨h₁.trans h₁', BEq.trans h₂ h₂'⟩

/-- Keys with their hashes are equal as the keys are, when equal keys
have equal hashes. -/
theorem Hashed.of_beq [Hashable α] [BEq α] [LawfulHashable α] (a b : α) :
    (Hashed.of a == Hashed.of b) = (a == b) := by
  cases h : a == b
  · exact Bool.eq_false_iff.2 fun h' => by
      have : (a == b) = true := ((Hashed.beq_iff _ _).1 h').2
      simp [this] at h
  · exact (Hashed.beq_iff _ _).2 ⟨hash_eq h, h⟩

/-- A map of keys with their hashes answers `Hashed.of k` as the map of
the plain keys, given the same insertions, answers `k`. -/
theorem Hashed.getElem?_foldl [Hashable α] [BEq α] [EquivBEq α] [LawfulHashable α] (kvs : List (α × β)) (k : α) :
    (kvs.foldl (fun m (k, v) => m.insert (Hashed.of k) v) ({} : Std.HashMap (Hashed α) β))[Hashed.of k]?
      = (kvs.foldl (fun m (k, v) => m.insert k v) ({} : Std.HashMap α β))[k]? := by
  suffices h : ∀ (m₁ : Std.HashMap (Hashed α) β) (m₂ : Std.HashMap α β), (∀ k : α, m₁[Hashed.of k]? = m₂[k]?) →
      ∀ k, (kvs.foldl (fun m (k, v) => m.insert (Hashed.of k) v) m₁)[Hashed.of k]?
        = (kvs.foldl (fun m (k, v) => m.insert k v) m₂)[k]? from
    h _ _ (fun k => by simp) k
  induction kvs with
  | nil => intro m₁ m₂ h; exact h
  | cons kv kvs ih =>
    intro m₁ m₂ h
    apply ih
    intro k'
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert, Hashed.of_beq, h]

/-- What `QueryCache.answers` holds, given the insertions of `runQuery`,
which keys each answer by `Hashed.of`, answers a key as the one map of
plain keys that it was before it was split, given the same insertions. -/
theorem Shards.get?_foldl_of [Hashable α] [BEq α] [EquivBEq α] [LawfulHashable α] (kvs : List (α × β)) (k : α) :
    (kvs.foldl (fun s (k, v) => s.insert (Hashed.of k) v) (Shards.empty : Shards (Hashed α) β)).get? (Hashed.of k)
      = (kvs.foldl (fun m (k, v) => m.insert k v) ({} : Std.HashMap α β))[k]? := by
  have h := Shards.get?_foldl (kvs.map fun (k, v) => (Hashed.of k, v)) (Hashed.of k)
  simp only [List.foldl_map] at h
  rw [h, Hashed.getElem?_foldl]

/-- The key of a query's answer: the script and the observations of its
model, which are every input of `solveScript` but its variables, which
the script declares. -/
abbrev QueryKey := String × Array ModelObservation

/-- The answers to the queries asked so far, by script, each with whether
it has a model: a script asked again gets the same answer without the
solver (`Reqs/Cli#solver-queries`). The script is the whole query, with its
logic, options and limits, so the same script means the same question. The
checks of several components may share it at once (`Reqs/Cli#parallel-checking`). -/
structure QueryCache where
  /-- By `QueryKey`, hashed once, in the map of `answerShard` (`Shards`):
  each map is updated atomically, as the one map was. -/
  answers : Vector (IO.Ref (Std.HashMap (Hashed QueryKey) (Outcome String × Bool))) answerShards
  /-- The answers kept across runs, if any (`Reqs/Cli#query-cache`). -/
  store? : Option QueryStore := none
  /-- With `fren check --solver-stats`, where the time of each query asked
  of the solver went (`FrenCli.SolverStats`); without it, `none`,
  and nothing is measured. -/
  stats? : Option (IO.Ref (Array SolverStats.QueryStats)) := none

/-- A cache with no answers yet, over the persistent `store?`, if any,
that records the solver's statistics of each query if `stats`. -/
def QueryCache.new (store? : Option QueryStore := none) (stats : Bool := false) : IO QueryCache := do
  let stats? ← if stats then some <$> IO.mkRef #[] else pure none
  return { answers := ← (Shards.empty : Shards (Hashed QueryKey) _).mapM fun m => IO.mkRef m, store?, stats? }

/-- The answer to `k`, if it was asked: as `Shards.get?`, on the
reference of `k`'s map. -/
def QueryCache.find? (c : QueryCache) (k : Hashed QueryKey) : BaseIO (Option (Outcome String × Bool)) :=
  return (← c.answers[answerShard k].get)[k]?

/-- Keeps `a` as the answer to `k`: as `Shards.insert`, on the reference
of `k`'s map, atomically. -/
def QueryCache.insert (c : QueryCache) (k : Hashed QueryKey) (a : Outcome String × Bool) : BaseIO Unit :=
  c.answers[answerShard k].modify (·.insert k a)

def observationsOf (c : CComp) : Array ModelObservation := Id.run do
  let mut out := #[]
  for group in c.memberGroups, g in [0:c.memberGroups.size] do
    for member in group.members, k in [0:group.members.size] do
      let guard := Lean.Name.mkSimple s!"#member_observation_{g}_{k}_guard"
      let value := Lean.Name.mkSimple s!"#member_observation_{g}_{k}_value"
      out := out.push { key := guard, formula := member.evaluationGuard?.getD "true" }
      out := out.push { key := value, formula := member.valueFormula?.getD member.formula, guard? := some guard }
  return out

/-- `solveScript`'s work, on `solver`, which it borrows: what it makes
from the solver, it drops before it returns, and so before the solver is
freed (`FrenCli.Cvc5`). With `probe?`, it marks when each phase begins and
ends, and then reads cvc5's statistics (`FrenCli.SolverStats.Probe`);
without it, it reads no clock of its own, only `Fren.Core.timeQuery`'s. -/
def solveOn (solver : @& cvc5.Solver) (script : String) (vars : Array CVar) (wantModel : Bool)
    (observations : Array ModelObservation) (limitSecs : Nat) (shared : Bool)
    (probe? : Option (IO.Ref SolverStats.Probe) := none) : cvc5.Env (Outcome String) := do
  let mark (set : SolverStats.Probe → Nat → SolverStats.Probe) : cvc5.Env Unit := do
    if let some probe := probe? then
      let t ← IO.monoNanosNow
      probe.modify (set · t)
  -- cvc5 warns on stderr when a model's value of a quantified formula
  -- cannot be evaluated (`Could not evaluate ... in getValue.`), which the
  -- model then holds as that formula: the warning is not an outcome, and
  -- only cvc5's own diagnostics are silenced.
  Cvc5.setOption solver "verbosity" "-1"
  let parser ← Cvc5.parserNew solver
  let sm ← Cvc5.getSymbolManager parser
  Cvc5.setStringInput parser script .SMT_LIB_2_6 "lean-cvc5"
  -- Every command up to and including the first that initializes the
  -- solver's theories runs exclusively if its logic shares libpoly's
  -- state, and so does `checkSat` if none did
  -- (`FrenCli.Cvc5.exclusively`). So a command that initializes the
  -- solver without being one that `Cvc5.initializes` lists still runs
  -- under the lock: the list only decides when the lock is let go
  -- (`released`), after a command that always initializes the solver.
  let mut released := false
  repeat
    let cmd ← Cvc5.nextCommand parser
    if Cvc5.isNull cmd then break
    let initializes := Cvc5.initializes (Cvc5.commandName cmd)
    let first := !released && initializes
    if first then mark fun p t => { p with initStart := t }
    -- A command that fails reports an error as its output, rather than
    -- throwing; ignoring it could let a dropped assertion give `sat`.
    let out ← if released then Cvc5.invoke cmd solver sm
      else Cvc5.exclusively shared (Cvc5.invoke cmd solver sm)
    if first then mark fun p t => { p with initEnd := t }
    released := released || initializes
    if out.trimAscii.toString.startsWith "(error" then
      -- Its time up to here is in the phases it reached, and none in
      -- the later ones (`FrenCli.SolverStats.Probe`).
      mark fun p t => { p with initStart := if p.initStart == 0 then t else p.initStart,
                                initEnd := if p.initEnd == 0 then t else p.initEnd,
                                checkStart := t, checkEnd := t, modelEnd := t, statsEnd := t }
      throw (.error out)
  -- With no command that initializes the solver, `checkSat` does.
  if !released then mark fun p t => { p with initStart := t, initEnd := t }
  mark fun p t => { p with checkStart := t }
  -- The time of a query that reaches its time limit is recorded
  -- (`Fren.Core.solverCredit`).
  let res ← Fren.Core.timeQuery limitSecs (fun (res : cvc5.Result) => Cvc5.isUnknown res &&
    Fren.Core.timedOutExplanation (toString (Cvc5.unknownExplanation res)))
    (if released then Cvc5.checkSat solver else Cvc5.exclusively shared (Cvc5.checkSat solver))
  mark fun p t => { p with checkEnd := t }
  let o ← (do
    if Cvc5.isUnsat res then return Outcome.unsat
    if !Cvc5.isSat res then return .unknown s!"the solver returned unknown ({Cvc5.unknownExplanation res})"
    if !wantModel then return .sat #[]
    let mut model := #[]
    for t in ← Cvc5.getDeclaredTerms sm do
      let n := (Cvc5.termText t).replace "|" ""
      if let some v := vars.find? (fun v => Fren.Core.smtName (v.name.toString (escape := false)) == n) then
        let value := Cvc5.termText (← Cvc5.getValue solver t)
        -- cvc5 shares values and qualified constructor symbols with lets.
        -- Expand them before confirmation, rendering, or pinning a model.
        let value := toString ((SeqElems.parse value).unfold {})
        model := model.push (v.name, value)
    for observation in observations do
      let reached := observation.guard?.all fun guard => model.any (fun (name, value) => name == guard && value == "true")
      let value ← if !reached then pure "unknown" else do
        try
          Cvc5.setStringInput parser observation.formula .SMT_LIB_2_6 "lean-cvc5"
          let term ← Cvc5.nextTerm parser
          pure (Cvc5.termText (← Cvc5.getValue solver term))
        catch _ => pure "unknown"
      model := model.push (observation.key, value)
    return .sat model : cvc5.Env (Outcome String))
  if let some probe := probe? then
    let t ← IO.monoNanosNow
    -- Read last, so that it changes nothing that the query answered; and
    -- a failure to read it is no answer's.
    let stats ← try Cvc5.getInfo solver "all-statistics" catch _ => pure ""
    let t' ← IO.monoNanosNow
    probe.modify fun p => { p with modelEnd := t, statsEnd := t', stats }
  return o

/-- `solveOn` on a solver of the term manager `tm`, which it borrows: it
frees the solver before it returns, and so before the term manager is
(`FrenCli.Cvc5`). -/
@[noinline] def solveWith (tm : @& cvc5.TermManager) (script : String) (vars : Array CVar) (wantModel : Bool)
    (observations : Array ModelObservation) (limitSecs : Nat) (probe? : Option (IO.Ref SolverStats.Probe) := none) :
    cvc5.Env (Outcome String) := do
  let shared := Cvc5.sharesLibpoly (Cvc5.scriptLogic script)
  -- Only `cell` holds the solver once `solveOn` returns, so that emptying
  -- it frees the solver, exclusively if its logic shares libpoly's state
  -- (`FrenCli.Cvc5.exclusively`), even after an error.
  let cell ← IO.mkRef (some (← Cvc5.solverNew tm))
  ExceptT.mk do
    let r ← match ← cell.get with
      | some solver => (solveOn solver script vars wantModel observations limitSecs shared probe?).run
      -- Not reached: `cell` was just set to the solver.
      | none => pure (.error (.error "the solver was freed before its query"))
    let _ ← (Cvc5.exclusively shared (cell.set none)).run
    return r

/-- Checks the satisfiability of `script`, a query over `vars`, with values
of `vars` if `wantModel`, with a solver of its own, which is freed once
it is answered (`FrenCli.Cvc5`); with `probe?`, marking when each phase
begins and ends (`FrenCli.SolverStats.Probe`). -/
def solveScript (script : String) (vars : Array CVar) (wantModel : Bool) (observations : Array ModelObservation := #[])
    (limitSecs : Nat := 0) (probe? : Option (IO.Ref SolverStats.Probe) := none) : IO (Outcome String) := do
  if let some probe := probe? then
    let t ← IO.monoNanosNow
    probe.modify ({ · with start := t })
  let r ← cvc5.Env.run do
    solveWith (← cvc5.TermManager.new) script vars wantModel observations limitSecs probe?
  if let some probe := probe? then
    let t ← IO.monoNanosNow
    probe.modify ({ · with stop := t, failed := r matches .error _ })
  match r with
  | .ok o => return o
  | .error e => return .unknown s!"solver error: {e}"

/-- `solveScript`, recording in `sink` where its time went, as a query of
the check of kind `kind` of `item` (`FrenCli.SolverStats`). -/
def solveRecorded (sink : IO.Ref (Array SolverStats.QueryStats)) (item : Lean.Name) (kind : Fren.Core.CheckKind)
    (script : String) (vars : Array CVar) (wantModel : Bool) (observations : Array ModelObservation)
    (limitSecs : Nat) : IO (Outcome String) := do
  let probe ← IO.mkRef ({} : SolverStats.Probe)
  let o ← solveScript script vars wantModel observations limitSecs (some probe)
  let p ← probe.get
  let outcome := match o with
    | .sat _ => "sat"
    | .unsat => "unsat"
    | .unknown _ => if p.failed then "error" else "unknown"
  let stats : SolverStats.QueryStats :=
    { item, kind, logic := Cvc5.scriptLogic script, bytes := script.utf8ByteSize, outcome, phases := p.phases, cvc5 := SolverStats.parse p.stats }
  sink.modify (·.push stats)
  return o

/-- Asserts `hyps` and the negation of `goal` and checks satisfiability,
first passing the script to `dump?`, if any, and answering from `cache?`,
if any, a script asked before. It is a query of the check of kind `kind`
of `item`, for `fren check --solver-stats` (`QueryCache.stats?`). -/
def runQuery (logic options : String) (prelude : Prelude) (vars : Array CVar) (limits : Limits)
    (dump? : Option (String → IO Unit)) (hyps : Array (Lean.Name × String)) (goal : String) (wantModel : Bool)
    (cache? : Option QueryCache := none) (observations : Array ModelObservation := #[])
    (item : Lean.Name) (kind : Fren.Core.CheckKind) : IO (Outcome String) := do
  let script := queryScript logic options prelude vars limits hyps goal
  -- Read from the script that would be asked, the definitions that it
  -- includes, its hypotheses and its goal, not from the spec: a query with a
  -- quantifier is never asked in a quantifier-free logic, whatever set it
  -- (`cli::query_logic`).
  unless Fren.Core.queryAsked logic (Fren.Core.hasQuantifier script) do
    return .unknown (Fren.Core.quantifiedQueryReason logic)
  if let some dump := dump? then dump script
  let some cache := cache? | solveScript script vars wantModel observations limits.timeoutSecs
  let key := Hashed.of (script, observations)
  -- A model's variables are those that the script declares, which are `vars`.
  match ← cache.find? key with
  | some (o@(.sat _), hasModel) =>
    if !wantModel then return .sat #[]
    if hasModel then return o
  | some (o, _) => return o
  | none => pure ()
  -- Then from the answers kept across runs (`cli::query_cache`).
  if let some store := cache.store? then
    if let some (o, hasModel) ← store.lookup? script observations wantModel then
      cache.insert key (o, hasModel)
      return if wantModel then o else match o with | .sat _ => .sat #[] | _ => o
  let o ← match cache.stats? with
    | none => solveScript script vars wantModel observations limits.timeoutSecs
    | some sink => solveRecorded sink item kind script vars wantModel observations limits.timeoutSecs
  cache.insert key (o, wantModel)
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
  let names := (c.vars.filter fun v => (Fren.Core.Symbol.ofRole v.role).copied).map (·.name.toString (escape := false))
  mapQuoted (fun p => if names.contains p then Fren.Core.copySymbol p else p) smt

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

/-- The symbol at the start of `s`, the inside of an SMT-LIB application:
a quoted one whole, which may have spaces, as an instance of a generic
function with two type arguments, `|::f<Int, Bool>|`, does. -/
def headSymbol (s : String) : String :=
  if s.startsWith "|" then "|" ++ ((s.drop 1).takeWhile (· != '|')).toString ++ "|"
  else (s.takeWhile (· != ' ')).toString

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
  let head := headSymbol (inner.drop 1).toString
  let args := ((inner.drop (head.length + 2)).dropEnd 1).toString
  let (nat, k) := funs.getD head (false, {})
  let implies (ps : Array String) (q : String) := if ps.isEmpty then q else s!"(=> {conj ps} {q})"
  let posts := Fren.Core.postconditionFacts implies (k.pres.map fun (_, p) => s!"({p} {args})")
    (k.posts.map fun (n, sym) => (n, s!"({sym} {args})"))
  let typed := (types.get? head).map fun t => (`type, pre ++ t.replace factHole inner ++ post)
  (if nat then #[(`nat, pre ++ s!"(>= {inner} 0)" ++ post)] else #[]) ++ typed.toArray ++ posts.map fun (n, f) => (n, pre ++ f ++ post)

/-- The atoms of the SMT-LIB term `e`, each once, in order. -/
partial def atomsOf (e : SeqElems.SExpr) (acc : Array String := #[]) : Array String :=
  match e with
  | .atom a => if acc.contains a then acc else acc.push a
  | .list xs => xs.foldl (fun acc x => atomsOf x acc) acc

/-- The applications of the symbols `heads` in the SMT-LIB term `e`, each
once, after `acc`, as the Lean front end's `natApps` finds them: an
application before its arguments, and they from left to right. One that
mentions a name that a quantifier around it within `e` binds, of those
`bound`, is closed over those names with a `forall`, outermost first, as
an unbounded quantifier's applications are (`peelLets`): its facts hold
for every value of them. -/
partial def factAppsIn (heads : Std.HashSet String) (e : SeqElems.SExpr) (bound : Array (String × String) := #[])
    (acc : Array String := #[]) : Array String :=
  match e with
  | .atom _ => acc
  | .list xs =>
    match SeqElems.binderOf? e, xs with
    | some _, #[_, .list decls, body] =>
      -- A `let`'s definitions are outside its scope; `unfold` leaves none.
      let acc := decls.foldl (init := acc) fun acc d => match d with
        | .list #[_, v] => if xs[0]! == .atom "let" then factAppsIn heads v bound acc else acc
        | _ => acc
      let names := decls.filterMap fun
        | SeqElems.SExpr.list #[.atom x, t] => some (x, toString t)
        | _ => none
      factAppsIn heads body ((bound.filter fun (x, _) => !names.any (·.1 == x)) ++ names) acc
    | _, _ =>
      let acc := match xs[0]? with
        | some (SeqElems.SExpr.atom h) =>
          if !heads.contains h then acc else
          let used := bound.filter fun (x, _) => e.mentions #[x]
          let t := if used.isEmpty then toString e
            else s!"(forall ({" ".intercalate (used.toList.map fun (x, t) => s!"({x} {t})")}) {e})"
          if acc.contains t then acc else acc.push t
        | _ => acc
      xs.foldl (fun acc x => factAppsIn heads x bound acc) acc

/-- Whether a query of the formulas `fs` has a quantifier over elements to
expand, directly or in a `define-fun` of `marked` that it applies. -/
def needsExpansion (marked : Std.HashMap String (Array String × SeqElems.SExpr)) (fs : Array String) : Bool :=
  fs.any fun f => SeqElems.hasMarker f || marked.keys.any (Fren.Core.occursIn · f)

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

/-- Finite reflection. Nonrecursive definitions and clauses are expanded
before finding applications. Each application keeps its depth, how many
equations away from the query it is, through contracts, and brings an
equation only where its depth is less than `unfoldings`
(`Fren.Core.recursiveFacts`); the others receive only contract facts.
Guards follow the original conditional branches. -/
partial def recursiveQueryFacts (prelude : Prelude) (funs : Std.HashMap String (Bool × Contract))
    (types : Std.HashMap String String) (hyps : Array (Lean.Name × String)) (goal : String)
    (mentioned : Std.HashSet String) (unfoldings : Nat := 1) : Array (Lean.Name × String) := Id.run do
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
    work := work ++ scan recs (expand f) #[] 0 #[]
  let mut out := #[]
  let mut seen : Std.HashSet (SeqElems.SExpr × Array String × Nat) := {}
  let mut done := 0
  while done < work.size do
    let (app, gs, depth, ancestors) := work[done]!
    done := done + 1
    let key := (app, gs, depth)
    if seen.contains key then continue
    seen := seen.insert key
    let .list xs := app | continue
    let .atom head := xs[0]! | continue
    let args := xs.extract 1
    let text := toString app
    if ancestors.contains text then continue
    let ancestors := ancestors.push text
    let domain := ((prelude.byQuoted.get[head]?.bind (prelude.decls[·]?)).map fun d =>
      let ps := (d.recursion?.map (·.1)).getD #[]
      d.domain.map fun f => toString ((SeqElems.parse f).subst (ps.zip args))).getD #[]
    for (n, f) in appFactsOf funs types text do
      let f := expand f
      out := out.push ((n, if domain.isEmpty then toString f else s!"(=> {conj domain} {f})"), gs)
      work := work ++ scan recs f gs depth ancestors
    if (Fren.Core.recursiveFacts depth (unfoldings := unfoldings)).2 then
      if let some (_, ps, body) := recs.find? (·.1 == head) then
        let body := (body.subst (ps.zip args)).unfold defs
        out := out.push ((`equation, s!"(= {text} {body})"), gs)
        work := work ++ scan recs body gs (depth + 1) ancestors
  -- Each fact once, where it is first found, under its weakest paths.
  let implies (gs : Array String) (f : String) := if gs.isEmpty then f else s!"(=> {conj gs} {f})"
  let disj (ps : List (Array String)) := s!"(or {" ".intercalate (ps.map conj)})"
  return (Fren.Core.mergeGuarded Fren.Core.guardsWithin out.toList).toArray.map fun ((n, f), ps) =>
    (n, Fren.Core.guardedFact implies disj f ps)
where
  scan (recs : Array (String × Array String × SeqElems.SExpr)) (e : SeqElems.SExpr)
      (gs : Array String) (depth : Nat) (ancestors : Array String) (bound : Array String := #[]) :
      Array (SeqElems.SExpr × Array String × Nat × Array String) :=
    match e with
    | .atom _ => #[]
    | .list xs => Id.run do
      let own := match xs[0]? with
        | some (SeqElems.SExpr.atom h) => if recs.any (·.1 == h) && (Fren.Core.recursiveFacts depth (e.mentions bound)).1 then
          -- With nothing bound, no guard mentions a bound name.
          let gs := if bound.isEmpty then gs else gs.filter fun g => !(SeqElems.parse g).mentions bound
          #[(e, gs, depth, ancestors)] else #[]
        | _ => #[]
      if let some (names, body) := SeqElems.binderOf? e then
        return scan recs body gs depth ancestors (bound ++ names)
      if xs[0]? == some (SeqElems.SExpr.atom "and") || xs[0]? == some (SeqElems.SExpr.atom "or") then
        let mut result := own
        let mut guards := gs
        for x in xs.extract 1 do
          result := result ++ scan recs x guards depth ancestors bound
          guards := guards.push (if xs[0]? == some (SeqElems.SExpr.atom "and") then toString x else s!"(not {x})")
        return result
      match xs with
      | #[.atom "ite", c, a, b] =>
        return own ++ scan recs c gs depth ancestors bound
          ++ scan recs a (gs.push (toString c)) depth ancestors bound
          ++ scan recs b (gs.push s!"(not {c})") depth ancestors bound
      | #[.atom "=>", c, b] =>
        return own ++ scan recs c gs depth ancestors bound ++ scan recs b (gs.push (toString c)) depth ancestors bound
      | _ => return own ++ xs.flatMap fun x => scan recs x gs depth ancestors bound

/-- The recursive functions, by path, that the SMT-LIB formula `f` applies
once the definitions of `prelude` are unfolded, of those whose symbols are
`recursiveSyms` (`State.recursiveSyms`), each once, in order. -/
def recursiveIn (prelude : Prelude) (recursiveSyms : Std.HashMap String Lean.Name) (f : String) : Array Lean.Name :=
  if recursiveSyms.isEmpty then #[] else
  (atomsOf ((SeqElems.parse f).unfold prelude.unfolds.get)).foldl (init := #[]) fun acc a =>
    match recursiveSyms.get? a with
    | some p => if acc.contains p then acc else acc.push p
    | none => acc

/-- A query as `backend` asks it, once its hypotheses have the facts that
its formulas bring: its variables, hypotheses, goal, logic and options,
the observations of its model, the symbols that the model shows, and the
recursive functions that its facts apply (`prepare`). -/
structure Prepared where
  vars : Array CVar
  hyps : Array (Lean.Name × String)
  goal : String
  logic : String
  options : String
  observations : Array ModelObservation
  shown : Std.HashSet String
  factRecs : Array Lean.Name

/-- The query of `hyps` and `goal` that `backend` asks, as it asks it
(`Prepared`), but for its quantifiers over elements, which it expands as
it asks it (`solveExpanded`). -/
def prepare (prelude : Prelude) (c : CComp) (strings sets : Bool) (projection : Bool) (quantified : Bool)
    (funs : Std.HashMap String (Bool × Contract)) (kind : Fren.Core.CheckKind)
    (contractFns : Std.HashMap String Lean.Name) (applied? : Option (IO.Ref (Array Lean.Name)))
    (recursiveSyms : Std.HashMap String Lean.Name) (hyps : Array (Lean.Name × String)) (goal : String)
    (requery : Bool := false) : IO Prepared := do
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
  -- their source identity for `backend`'s `modelBool?`.
  let observations := (observationsOf c).map fun observation =>
    { observation with formula := expand observation.formula }
  let facts := c.natFacts false ++ c.natFacts true
  let facts := facts ++ (facts.map fun (n, f) => (n, prime c f)).filter (!facts.contains ·)
  let formulas := facts.map (·.2) ++ hyps.map (·.2) |>.push goal
  let mentioned : Std.HashSet String := .ofArray (formulas.flatMap quotedSymbols)
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
    contractFns.get? (headSymbol (inner.drop 1).toString)
  -- And those of the applications in those facts, once their clauses
  -- are unfolded, of the functions whose applications bring facts
  -- (`Fren.Core.closeApps`).
  let factHeads : Std.HashSet String := funs.fold (init := .ofList (c.funFacts.toList.map (·.1)))
    fun acc h (nat, k) => if nat || !k.posts.isEmpty then acc.insert h else acc
  let factAppsOf (f : String) : Id (Array String) :=
    (factAppsIn factHeads ((SeqElems.parse f).unfold prelude.unfolds.get)).map fun t =>
      ((peeled.idxOf? t).map (apps[·]!)).getD t
  let some (appFacts, fns) := Fren.Core.appFactsWith (m := Id) appsOf (appFactsOf funs c.funFacts) fnOf factAppsOf
      (factHeads.size + 1) (hyps.map fun (n, f) => (n, dropUnusedLets f)) (dropUnusedLets goal) c.fn?
    | throw (IO.userError Fren.Core.factRoundsMsg)
  -- Without the `let`s of their applications that they do not use, as
  -- Lean's `zetaReduce` drops them; and the query declares the variables
  -- that they mention too, which a fact of an application in a `let` may
  -- where the formulas do not, as of a parameter that a contract does not
  -- mention.
  let appFacts := appFacts.map fun (n, f) => (n, dropUnusedLets f)
  let mentioned := appFacts.foldl (init := mentioned) fun m (_, f) => (quotedSymbols f).foldl (·.insert ·) m
  let vars := (c.vars ++ primes c).filter (fun v => mentioned.contains (v.name.toString (escape := false)))
  if let some r := applied? then
    r.modify fun acc => fns.foldl (init := acc) fun acc f => if acc.contains f then acc else acc.push f
  -- A procedure whose queries may quantify sets `fmf-bound`
  -- (`State.bounded`).
  -- The recursive functions that the facts of its applications apply,
  -- once their clauses are unfolded, by path, whose models are never
  -- confirmed (`Fren.Core.recursiveCounterexample`).
  let factRecs := appFacts.foldl (init := #[]) fun acc (_, f) =>
    (recursiveIn prelude recursiveSyms f).foldl (init := acc) fun acc p => if acc.contains p then acc else acc.push p
  -- Reflected with the hypotheses (`Fren.Core.recursionFormulas`).
  -- Deeper in the check of a function generated for induction
  -- (`lang::unfoldings`).
  let hyps := facts ++ appFacts ++ recursiveQueryFacts prelude funs c.funFacts (Fren.Core.recursionFormulas facts appFacts hyps) goal mentioned
    (Fren.Core.unfoldings (c.fn?.any Fren.Core.isInductionFn)) ++ hyps
  let options := Fren.Core.solverOptions strings sets ++ (if c.bounded then Fren.Core.boundedOptions else [])
    -- The contract of a generic function without a body, at its type
    -- parameters' sorts, with finite-model finding.
    ++ (if c.generic || c.finiteModel then Fren.Core.finiteModelOptions else [])
    -- Asked again, for a model that confirmation contradicts
    -- (`Fren.Core.askedAgain`).
    ++ (if requery then Fren.Core.requeryOptions else [])
  -- A recursive definition needs a logic with quantifiers.
  let logic := Fren.Core.logic kind (strings || sets) projection quantified
  let options := String.join ((options ++ Fren.Core.quantifierOptions logic).map fun (o, v) => s!"(set-option :{o} {v})\n")
  return { vars, hyps, goal, logic, options, observations, shown, factRecs }

/-- The script of the query of `hyps` and `goal` that `backend` would ask,
without asking it: what `--dump=obligations` prints (`Fren.Core.dump`). -/
def queryText (prelude : Prelude) (c : CComp) (limits : Limits) (strings sets : Bool := false) (projection : Bool := false)
    (quantified : Bool := false) (funs : Std.HashMap String (Bool × Contract) := {}) (kind : Fren.Core.CheckKind)
    (contractFns : Std.HashMap String Lean.Name := {}) (recursiveSyms : Std.HashMap String Lean.Name := {})
    (hyps : Array (Lean.Name × String)) (goal : String) : IO String := do
  let p ← prepare prelude c strings sets projection quantified funs kind contractFns none recursiveSyms hyps goal
  return queryScript p.logic p.options prelude p.vars limits p.hyps p.goal

/-- The variable symbols in each opaque application of an unfolded formula. -/
private partial def outputApplications (opaqueHeads vars : Std.HashSet String) (e : SeqElems.SExpr) : List (List String) :=
  match e with
  | .atom _ => []
  | .list ts =>
    let own := match ts[0]? with
      | some (SeqElems.SExpr.atom f) => if opaqueHeads.contains f then
          [(ts.extract 1 |>.flatMap fun a => (quotedSymbols (toString a)).filter vars.contains).toList]
        else []
      | _ => []
    own ++ ts.toList.flatMap (outputApplications opaqueHeads vars)

/-- The backend for `c`, where `strings` and `sets` say whether the spec uses
strings and sets, and `projection` whether it projects a relation over a
type that is not finite, which puts in `HO_ALL` those of its queries that
do (`cli::logic`, `queryScript`); answering from `cache?`, if any,
the scripts asked before (`runQuery`). -/
def backendWith (prelude : Prelude) (dts : Array DataDecl) (c : CComp) (limits : Limits) (dump? : Option (String → IO Unit) := none)
    (strings sets : Bool := false) (projection : Bool := false) (cache? : Option QueryCache := none) (quantified : Bool := false)
    (funs : Std.HashMap String (Bool × Contract) := {}) (kind : Fren.Core.CheckKind)
    (contractFns : Std.HashMap String Lean.Name := {}) (applied? : Option (IO.Ref (Array Lean.Name)) := none)
    (recursiveSyms : Std.HashMap String Lean.Name := {}) (requery : Bool := false) :
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
    let { vars, hyps, goal, logic, options, observations, shown, factRecs } ← prepare prelude c strings sets projection
      quantified funs kind contractFns applied? recursiveSyms hyps goal requery
    let o ← if needsExpansion prelude.marked (hyps.map (·.2) |>.push goal) then
        solveExpanded prelude.marked (runQuery logic options prelude · limits dump? · · · cache? observations c.path kind)
          vars hyps goal wantModel
      else runQuery logic options prelude vars limits dump? hyps goal wantModel cache? observations c.path kind
    -- A fact that applies a recursive function is never confirmed, a
    -- conservative choice, as the Lean front end decides it too.
    let o := match o with
      | .sat _ => if Fren.Core.recursiveCounterexample false true (!factRecs.isEmpty) then o
        else .unknown (Fren.Core.recursiveReason factRecs)
      | o => o
    return match o with
      | .sat m => .sat (m.filter fun (n, _) => shown.contains (n.toString (escape := false)) || (n.toString (escape := false)).startsWith "#member_observation_")
      | o => o
  falseF := "false"
  notF f := s!"(not {f})"
  conj := conj
  outputApplications? := some fun body => do
    let opaqueHeads := prelude.decls.foldl (init := ({} : Std.HashSet String)) fun acc d =>
      match SeqElems.parse d.text with
      | .list #[.atom "declare-fun", .atom f, _, _] => acc.insert f
      | _ => acc
    -- Dependency extraction must unfold pure definitions too: unlike
    -- `queryDefinitions`, `ignore(y) := 0` must erase its argument here.
    let defs := prelude.decls.foldl (init := ({} : Std.HashMap String (Array String × SeqElems.SExpr))) fun acc d =>
      match SeqElems.parse d.text with
      | .list #[.atom "define-fun", .atom f, .list ps, _, value] =>
        acc.insert f (ps.filterMap (fun | .list #[.atom p, _] => some p | _ => none), value)
      | _ => acc
    let fs := (c.natFacts true).map (·.2) |>.push body
    let vars := Std.HashSet.ofArray (c.vars.map fun v => Fren.Core.nameText v.name)
    return fs.toList.flatMap fun f => outputApplications opaqueHeads vars ((SeqElems.parse f).unfold defs)
  existsOutputs f := do
    -- Defined outputs are substituted, never searched for.
    let outs := c.vars.filter fun v => v.role == .output && v.defn?.isNone
    if outs.isEmpty then return f
    let binders := " ".intercalate (outs.toList.map fun v => s!"({quote (v.name.toString (escape := false))} {v.ty.sort})")
    -- The outputs' `Nat`s are at least 0, with the requirements.
    return s!"(exists ({binders}) {conj ((c.natFacts true).map (·.2) ++ #[f])})"
  -- A value of an abstract type names a solver-internal constant, such as
  -- `@U_0`, which a fresh query cannot parse.
  pin n v := return if v.contains '@' then none else some s!"(= {quote (n.toString (escape := false))} {v})"
  -- The tester of its variant (`DataDecl.tester`), by the variable's type.
  pinVariant n v := return do
    let ty ← (c.vars ++ primes c).find? (·.name == n) |>.map (·.ty)
    let (k, idx, d, args) ← variantOfValue dts ty v
    return (k, d.tester idx (quote (n.toString (escape := false))) args)
  -- By the variable's type, for its newtypes.
  render n v := return renderValue dts v ((c.vars ++ primes c).find? (·.name == n) |>.map (·.ty))
  prime := prime c
  samePrimed n := s!"(= {quote (n.toString (escape := false))} {quote (Fren.Core.copySymbol (n.toString (escape := false)))})"
  -- Each definition sees the earlier ones.
  subst ds f := ds.foldr (init := f) fun (d, e) f => s!"(let (({quote d.toString} {e})) {f})"

/-- `backendWith`'s backend for `c`, which can ask a query again
(`Fren.Core.askedAgain`), with `Fren.Core.requeryOptions`: a script of its
own, which is dumped and cached as any other. -/
def backend (prelude : Prelude) (dts : Array DataDecl) (c : CComp) (limits : Limits) (dump? : Option (String → IO Unit) := none)
    (strings sets : Bool := false) (projection : Bool := false) (cache? : Option QueryCache := none) (quantified : Bool := false)
    (funs : Std.HashMap String (Bool × Contract) := {}) (kind : Fren.Core.CheckKind)
    (contractFns : Std.HashMap String Lean.Name := {}) (applied? : Option (IO.Ref (Array Lean.Name)) := none)
    (recursiveSyms : Std.HashMap String Lean.Name := {}) :
    Fren.Core.Backend IO String String :=
  -- The functions whose contracts a query's facts apply are found in its
  -- hypotheses and goal, whatever `requery` is, so those of the query
  -- asked again are the first's, which the first records: the second
  -- records none, as in the Lean-hosted front end.
  let again := backendWith prelude dts c limits dump? strings sets projection cache? quantified funs kind contractFns none
    recursiveSyms (requery := true)
  { backendWith prelude dts c limits dump? strings sets projection cache? quantified funs kind contractFns applied?
      recursiveSyms with again? := some again.query }

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
