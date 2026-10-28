-- keep-sorted start
import FrenCore.SeqElems
-- keep-sorted end

/-!
# Expanding quantifiers over elements in a query (`Reqs/Lang/ElementQuantifiers#expansion`)

The elaborator writes a quantifier over a sequence's elements that is in
the decidable core with the head `fren.forall` or `fren.exists`
(`FrenCli.bindFree`), which no solver knows. Each query expands them before
it is asked, as the Lean-hosted front end expands its own (`Fren.SeqElems`):
each is instantiated at every tuple of the query's index set
(`Fren.Core.indexSet`), with its bound names' memberships, in its guard,
replaced by their positions' being in range. A quantifier whose sequence
mentions a name bound around it, as an output of the realizability check
may be, is given to the solver as it is written.

A model of the expanded query need not be one of the quantified query, so a
query that is satisfiable is asked again, with each sequence's length
pinned to its length in the model and each quantifier instantiated at every
position: that query is the quantified one at those lengths, so its models
are real ones. By the fragment's completeness, it is satisfiable whenever
the first is (`Fren.Core.project_all`).
-/

namespace FrenCli.SeqElems

open Fren.Core (IndexSources)

/-- An SMT-LIB term, with each atom as written, its `|` quotes kept. -/
inductive SExpr where
  | atom (s : String)
  | list (xs : Array SExpr)
  deriving Inhabited, BEq

partial def SExpr.toString : SExpr → String
  | .atom s => s
  | .list xs => "(" ++ " ".intercalate (xs.toList.map SExpr.toString) ++ ")"

instance : ToString SExpr := ⟨SExpr.toString⟩

/-- The terms of `cs` from `i`, up to an unmatched `)`, and where they end. -/
partial def parseAt (cs : Array Char) (i : Nat) : Array SExpr × Nat := Id.run do
  let mut i := i
  let mut out := #[]
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then i := i + 1
    else if c == ')' then return (out, i + 1)
    else if c == '(' then
      let (ts, j) := parseAt cs (i + 1)
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
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract i (j + 1)).toList))
      i := j + 1
    else
      let mut j := i
      while j < cs.size && !(cs[j]!.isWhitespace || cs[j]! == '(' || cs[j]! == ')') do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract i j).toList))
      i := j
  return (out, i)

/-- The term that `s` writes. -/
def parse (s : String) : SExpr := ((parseAt s.toList.toArray 0).1)[0]?.getD (.atom s)

/-- The heads of the quantifiers that the elaborator marks. -/
def markerHeads : List String := ["fren.forall", "fren.exists"]

/-- Whether the SMT-LIB text `s` has a marked quantifier. -/
def hasMarker (s : String) : Bool := markerHeads.any fun h => (s.splitOn h).length > 1

/-- Of a marked quantifier's head, after `scan` numbers it as
`fren.forall#k`: whether it is a `forall`, and its number. -/
def markerOf? (h : String) : Option (Bool × Option Nat) :=
  markerHeads.findSome? fun m =>
    if h == m then some (m == "fren.forall", none)
    else (h.dropPrefix? (m ++ "#")).bind fun k => k.toString.toNat?.map fun k => (m == "fren.forall", some k)

/-- The names that a binder form binds, and its body, if `e` is one:
`forall`, `exists`, their marked forms, `lambda`, and `let`. -/
def binderOf? : SExpr → Option (Array String × SExpr)
  | .list #[.atom h, .list decls, body] =>
    if h == "forall" || h == "exists" || h == "lambda" || h == "let" || (markerOf? h).isSome then
      some (decls.filterMap fun | .list d => (match d[0]? with | some (SExpr.atom x) => some x | _ => none) | _ => none, body)
    else none
  | _ => none

/-- Whether `e` mentions an atom of `xs`. -/
partial def SExpr.mentions (xs : Array String) : SExpr → Bool
  | .atom a => xs.contains a
  | .list ts => ts.any (·.mentions xs)

/-- `e` with each free atom `x` of `σ` replaced by `σ x`, stopping where a
binder binds it again. -/
partial def SExpr.subst (σ : Array (String × SExpr)) (e : SExpr) : SExpr :=
  if σ.isEmpty then e else
  match e with
  | .atom a => (σ.find? (·.1 == a)).map (·.2) |>.getD e
  | .list ts =>
    match binderOf? e, ts with
    | some (xs, body), #[h, .list decls, _] =>
      -- A `let`'s definitions are outside its scope.
      let decls := if h == .atom "let" then decls.map fun
          | .list #[x, d] => .list #[x, d.subst σ]
          | d => d
        else decls
      .list #[h, .list decls, body.subst (σ.filter (!xs.contains ·.1))]
    | _, _ => .list (ts.map (·.subst σ))

/-- `e` without `let`s, their definitions substituted, and with each
application of a `define-fun` of `defs` unfolded. -/
partial def SExpr.unfold (defs : Std.HashMap String (Array String × SExpr)) (e : SExpr) : SExpr :=
  match e with
  | .atom a => match defs[a]? with
    | some (#[], body) => body.unfold defs
    | _ => e
  | .list #[.atom "let", .list binds, body] =>
    let σ := binds.filterMap fun
      | .list #[.atom x, d] => some (x, d.unfold defs)
      | _ => none
    (body.subst σ).unfold defs
  | .list ts =>
    match ts[0]? with
    | some (SExpr.atom f) => match defs[f]? with
      | some (ps, body) =>
        if ps.size + 1 == ts.size then (body.subst (ps.zip ((ts.extract 1).map (·.unfold defs)))).unfold defs
        else .list (ts.map (·.unfold defs))
      | none => .list (ts.map (·.unfold defs))
    | _ => .list (ts.map (·.unfold defs))

/-- The conjuncts of `e`, through `and`. -/
partial def conjuncts : SExpr → Array SExpr
  | e@(.list ts) => if ts[0]? == some (.atom "and") then (ts.extract 1).flatMap conjuncts else #[e]
  | e => #[e]

/-- The sequences of the memberships of `x` in the guard of a marked
quantifier's body `b`, a `forall`'s if `all`: the antecedents of its
`=>`s, and an `exists`'s conjuncts. -/
partial def spineMembers (all : Bool) (x : String) (b : SExpr) : Array SExpr :=
  let member : SExpr → Option SExpr
    | .list #[.atom "seq.contains", q, .list #[.atom "seq.unit", .atom y]] => if y == x then some q else none
    | _ => none
  if all then
    match b with
    | .list #[.atom "=>", a, c] => (conjuncts a).filterMap member ++ spineMembers all x c
    | _ => #[]
  else (conjuncts b).filterMap member

/-- `b` with each membership of the sequence `q` and the term `x` in its
guard, as `spineMembers` reads it, replaced by `inRange`. -/
partial def replaceSpine (all : Bool) (q x inRange : SExpr) (b : SExpr) : SExpr :=
  let target := SExpr.list #[.atom "seq.contains", q, .list #[.atom "seq.unit", x]]
  let rec inGuard : SExpr → SExpr
    | e@(.list ts) =>
      if e == target then inRange
      else if ts[0]? == some (.atom "and") then .list (#[ts[0]!] ++ (ts.extract 1).map inGuard) else e
    | e => e
  if all then
    match b with
    | .list #[.atom "=>", a, c] => .list #[.atom "=>", inGuard a, replaceSpine all q x inRange c]
    | _ => b
  else inGuard b

/-- A marked quantifier of a query: a `forall` if `all`, its bound names,
and the sequence of each, or `none` for one that the body does not
mention; or `none` if it is not expanded, its sequence mentioning a name
bound around it. -/
structure Site where
  all : Bool
  vars : Array String
  receivers? : Option (Array (Option SExpr))

/-- What a query's traversal collects: its marked quantifiers, numbered in
order, and the sources of its index set. -/
structure Scan where
  sites : Array Site := #[]
  reads : Array SExpr := #[]
  updates : Array (SExpr × SExpr × SExpr) := #[]
  /-- The equations, between terms that mention no bound name. -/
  equations : Array (SExpr × SExpr) := #[]

def numeral (k : Int) : SExpr := if k < 0 then .list #[.atom "-", .atom (toString (-k))] else .atom (toString k)

def plus (t : SExpr) (k : Int) : SExpr := .list #[.atom (if k < 0 then "-" else "+"), t, .atom (toString k.natAbs)]

/-- The binders around a term of a query, outermost first, each with the
names that it binds (`Fren.Core.Frame`). -/
abbrev Frames := Array (Array String × Fren.Core.Frame)

/-- `frames` for a part of the term within them: still on the innermost
quantifier's spine only if `keep` (`Fren.Core.Frame`). -/
def Frames.within (frames : Frames) (keep : Bool) : Frames :=
  match frames.back? with
  | some (xs, .element all spine) => frames.pop.push (xs, .element all (spine && keep))
  | _ => frames

/-- `e`, within `frames`, with each marked quantifier numbered, as
`fren.forall#k`, and recorded with its sequences if it is expanded
(`Fren.Core.siteExpanded`); and its reads, updates and equations at terms
that mention no bound name. -/
partial def scan (frames : Frames) (e : SExpr) : StateM Scan SExpr := do
  let bound := frames.flatMap (·.1)
  match e with
  | .atom _ => return e
  | .list ts =>
    if let (some (xs, body), #[.atom h, decls, _]) := (binderOf? e, ts) then
      if let some (all, _) := markerOf? h then
        -- Each bound name's sequence, from its guard; one that the body
        -- does not mention needs none.
        let receivers := xs.map fun x =>
          if !body.mentions #[x] then some none
          else ((spineMembers all x body).find? (!·.mentions (bound ++ xs))).map some
        let mentioned := (List.range frames.size).filter fun j => body.mentions frames[j]!.1
        let expanded := Fren.Core.siteExpanded (frames.toList.map (·.2)) all (receivers.all Option.isSome) mentioned
        let k := (← get).sites.size
        let site : Site := { all := all, vars := xs
                             receivers? := if expanded then some (receivers.map (·.join)) else none }
        modify fun s => { s with sites := s.sites.push site }
        let head := s!"{if all then "fren.forall" else "fren.exists"}#{k}"
        let frame : Fren.Core.Frame := if expanded then .element all true else .other
        return .list #[.atom head, decls, ← scan (frames.push (xs, frame)) body]
      -- A `let`'s definitions are outside its scope.
      let decls ← if h == "let" then match decls with
          | .list ds => pure (.list (← ds.mapM fun
              | .list #[x, d] => return .list #[x, ← scan (frames.within false) d]
              | d => pure d))
          | d => pure d
        else pure decls
      return .list #[.atom h, decls, ← scan (frames.push (xs, .other)) body]
    match ts.toList with
    | [.atom "seq.nth", _, i] =>
      if !i.mentions bound then modify fun s => { s with reads := s.reads.push i }
    | [.atom "seq.update", _, i, _] =>
      if !i.mentions bound then modify fun s => { s with updates := s.updates.push (plus i (-1), i, plus i 1) }
    | [.atom "=", a, b] =>
      if !a.mentions bound && !b.mentions bound then modify fun s => { s with equations := s.equations.push (a, b) }
    | _ => pure ()
    -- The consequent of an implication, and the conjuncts of `and`, are on
    -- the innermost quantifier's spine; nothing else is.
    let head := ts[0]?
    let keepAt (i : Nat) : Bool :=
      head == some (.atom "and") || (head == some (.atom "=>") && i == 2)
    return .list (← ts.zipIdx.mapM fun (t, i) => scan (frames.within (keepAt i)) t)

/-- The terms at which the bound name `k` of the site `i`, whose sequence
is `q`, is instantiated. -/
abbrev TermsFor := Nat → Nat → SExpr → List SExpr

/-- `e`, with each numbered marked quantifier of `sites` expanded: at each
tuple of the terms that `terms` gives its bound names, with their
memberships in its guard replaced by their positions' being in range; or
as the solver's quantifier, if it is not expanded. The state counts the
instances, which may be at most `Fren.Core.maxElementInstances`; the
error is how many there would be. -/
partial def expand (sites : Array Site) (terms : TermsFor) (e : SExpr) : StateT Nat (Except Nat) SExpr := do
  match e with
  | .atom _ => return e
  | .list ts =>
    let some (SExpr.atom h) := ts[0]? | return .list (← ts.mapM (expand sites terms))
    let some (all, some i) := markerOf? h | return .list (← ts.mapM (expand sites terms))
    let (some site, #[_, decls, body]) := (sites[i]?, ts) | return e
    let some receivers := site.receivers? |
      return .list #[.atom (if all then "forall" else "exists"), decls, ← expand sites terms body]
    -- Each bound name's terms, or none if the body does not mention it.
    let choices := receivers.zipIdx.toList.map fun (q?, k) => match q? with
      | some q => (terms i k q).map some
      | none => [none]
    let tuples := choices.foldl (fun acc cs => acc.flatMap fun pre => cs.map (pre ++ [·])) [[]]
    let mut parts := #[]
    for t in tuples do
      let σ := (site.vars.zip (receivers.zip t.toArray)).filterMap fun (x, q?, t?) => do
        pure (x, ← q?, ← t?)
      let b := body.subst (σ.map fun (x, q, t) => (x, .list #[.atom "seq.nth", q, t]))
      let b := σ.foldl (init := b) fun b (_, q, t) =>
        replaceSpine all q (.list #[.atom "seq.nth", q, t])
          (.list #[.atom "and", .list #[.atom "<=", .atom "0", t], .list #[.atom "<", t, .list #[.atom "seq.len", q]]]) b
      modify (· + 1)
      let n ← get
      if !Fren.Core.elementSizeAccepted n then throw n
      parts := parts.push (← expand sites terms b)
    return if parts.size == 1 then parts[0]!
      else if parts.isEmpty then .atom (if all then "true" else "false")
      else .list (#[.atom (if all then "and" else "or")] ++ parts)

/-- The SMT-LIB `define-fun`s of a prelude whose bodies have a marked
quantifier, directly or through another, by symbol, with their
parameters and bodies: each query unfolds them. -/
def markedDefs (texts : Array String) : Std.HashMap String (Array String × SExpr) := Id.run do
  let mut out : Std.HashMap String (Array String × SExpr) := {}
  for t in texts do
    unless t.startsWith "(define-fun " do continue
    let .list #[_, .atom f, .list ps, _, body] := parse t | continue
    let calls := out.keys.any fun g => body.mentions #[g]
    unless hasMarker t || calls do continue
    out := out.insert f (ps.filterMap (fun | .list #[.atom x, _] => some x | _ => none), body)
  return out

/-- The text of a prelude declaration, with its marked quantifiers as the
solver's: a query that needs it unfolds it instead (`markedDefs`), but
another declaration may apply it. -/
def plainText (t : String) : String :=
  (t.replace "(fren.forall " "(forall ").replace "(fren.exists " "(exists "

/-- An expanded query: its hypotheses and goal, the fresh constants that it
declares, and the length constants that a model reads, each with its
sequence. -/
structure Expanded where
  hyps : Array (Lean.Name × String)
  goal : String
  consts : Array String
  lengths : Array (String × SExpr)

/-- `hyps` and `goal` with their marked quantifiers expanded, the
`define-fun`s `defs` that have them unfolded: at the query's index set
(`Fren.Core.indexSet`), with a witness for each bound name of each site
and for each equation between sequences of which one is a site's, which
two sequences that differ differ at; or with `pins`, the lengths of the
sequences in a model, at each position below a pinned sequence's length.
The error is the number of instances, if more than
`Fren.Core.maxElementInstances`. -/
def expandQuery (defs : Std.HashMap String (Array String × SExpr)) (hyps : Array (Lean.Name × String)) (goal : String)
    (pins? : Option (Array (SExpr × Nat)) := none) : Except Nat Expanded := do
  let scanned : StateM Scan (Array (Lean.Name × SExpr) × SExpr) := do
    let hs ← hyps.mapM fun (n, h) => return (n, ← scan #[] ((parse h).unfold defs))
    return (hs, ← scan #[] ((parse goal).unfold defs))
  let ((hs, g), sc) := scanned.run {}
  let expanded := sc.sites.filter (·.receivers?.isSome)
  let receivers := (expanded.flatMap fun s => (s.receivers?.getD #[]).filterMap id).foldl
    (fun acc q => if acc.contains q then acc else acc.push q) #[]
  let ws := (List.range (expanded.foldl (· + ·.vars.size) 0)).toArray.map (s!"|#w{·}|")
  let eqs := sc.equations.filter fun (a, b) => receivers.contains a || receivers.contains b
  let ds := eqs.mapIdx fun k (a, b) => (a, b, s!"|#d{k}|")
  let ix := Fren.Core.indexSet
    { zero := .atom "0"
      lasts := receivers.toList.map fun q => plus (.list #[.atom "seq.len", q]) (-1)
      reads := sc.reads.toList
      updates := sc.updates.toList
      witnesses := (ws ++ ds.map (·.2.2)).toList.map .atom : IndexSources SExpr }
  let terms : TermsFor := fun _ _ q => match pins? with
    | some pins => match pins.find? (·.1 == q) with
      | some (_, n) => (List.range n).map fun j => numeral (Int.ofNat j)
      | none => ix
    | none => ix
  let go : StateT Nat (Except Nat) (Array (Lean.Name × SExpr) × SExpr) := do
    return (← hs.mapM fun (n, h) => return (n, ← expand sc.sites terms h), ← expand sc.sites terms g)
  let ((hs, g), _) ← go.run 0
  let lengths := receivers.mapIdx fun k q => (s!"|#l{k}|", q)
  let extra := match pins? with
    | some pins => pins.map fun (q, n) => (`elementLength, s!"(= (seq.len {q}) {n})")
    | none => lengths.map (fun (l, q) => (`elementLength, s!"(= {l} (seq.len {q}))")) ++ ds.map fun (a, b, d) =>
      (`elementWitness, s!"(or (= {a} {b}) (not (= (seq.len {a}) (seq.len {b}))) (and (<= 0 {d}) (< {d} (seq.len {a})) (not (= (seq.nth {a} {d}) (seq.nth {b} {d})))))")
  return { hyps := hs.map (fun (n, h) => (n, toString h)) ++ extra, goal := toString g
           consts := if pins?.isSome then #[] else ws ++ ds.map (·.2.2) ++ lengths.map (·.1)
           lengths := if pins?.isSome then #[] else lengths }

end FrenCli.SeqElems
