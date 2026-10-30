-- keep-sorted start
import Fren.Seq
import FrenCore.SeqElems
import Lean
-- keep-sorted end

/-!
# Expanding quantifiers over elements in a query (`Reqs/Lang/ElementQuantifiers#expansion`)

The elaborator marks a quantifier over a sequence's elements that is in the
decidable core with `mdata` (`mark`), around Lean's `∀` or `∃`, which is its
meaning. Each query expands it before lean-smt sees it, as the binary
expands its own (`FrenCli.SeqElems`): it is instantiated at every tuple of
the query's index set (`Fren.Core.indexSet`), with its bound names'
memberships, in its guard, replaced by their positions' being in range. A
quantifier whose sequence mentions a name bound around it is left as it is.
-/

open Lean Meta

namespace Fren.Elems

/-- The key of the `mdata` of a marked quantifier, whose value is the number
of its bound names. -/
def key : Name := `fren.elems

/-- The key of the number that `scan` gives a marked quantifier. -/
def siteKey : Name := `fren.elems.site

/-- `e`, a quantifier over elements of `n` bound names, marked. -/
def mark (n : Nat) (e : Expr) : Expr := .mdata (KVMap.empty.insert key (.ofNat n)) e

/-- The number of bound names of `e`, if it is marked, its number, if it
has one, and the quantifier. -/
def marked? : Expr → Option (Nat × Option Nat × Expr)
  | .mdata d e => match d.find key with
    | some (.ofNat n) => some (n, match d.find siteKey with | some (.ofNat k) => some k | _ => none, e)
    | _ => none
  | _ => none

/-- Whether `e` has a marked quantifier. -/
def hasMark (e : Expr) : Bool := (e.find? fun x => (marked? x).isSome).isSome

/-- `e`, `∀ x₁ … xₙ, b` or `∃ x₁, … ∃ xₙ, b`, with its `n` bound names as
locals, passed to `k` with `b`; `none` if it is neither. -/
partial def withBound (all : Bool) (n : Nat) (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM (Option α) := do
  if n == 0 then return some (← k #[] e)
  if all then
    let .forallE x t b bi := e | return none
    withLocalDecl x bi t fun fv => withBound all (n - 1) (b.instantiate1 fv) fun xs b => k (#[fv] ++ xs) b
  else
    let_expr Exists t f := e | return none
    let .lam x _ b bi := f | return none
    withLocalDecl x bi t fun fv => withBound all (n - 1) (b.instantiate1 fv) fun xs b => k (#[fv] ++ xs) b

/-- Whether a marked quantifier over elements is a `forall`: `∀`'s body is
a `forallE`, and `∃`'s an application. -/
def isAll (e : Expr) : Bool := e.isForall

/-- The conjuncts of `e`, through `∧`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  match_expr e with
  | And a b => conjuncts a ++ conjuncts b
  | _ => #[e]

/-- The sequence of `e`, if it is a membership `x ∈ q` of the term `x`. -/
def memberOf? (x e : Expr) : Option Expr :=
  if e.isAppOfArity ``Membership.mem 5 && e.appArg! == x then some e.appFn!.appArg! else none

/-- The sequences of the memberships of `x` in the guard of `b`, the body of
a marked quantifier, a `forall`'s if `all`: the antecedents of its arrows,
and an `exists`'s conjuncts, through `∧`. -/
partial def spineMembers (all : Bool) (x b : Expr) : Array Expr :=
  if all then
    match b with
    | .forallE _ a c _ => if c.hasLooseBVars then #[] else (conjuncts a).filterMap (memberOf? x) ++ spineMembers all x c
    | _ => #[]
  else (conjuncts b).filterMap (memberOf? x)

/-- `b` with each membership `x ∈ q` in its guard, as `spineMembers` reads
it, replaced by `inRange`. -/
partial def replaceSpine (all : Bool) (q x inRange b : Expr) : Expr :=
  let rec inGuard (e : Expr) : Expr :=
    match_expr e with
    | And a c => mkAnd (inGuard a) (inGuard c)
    | _ => if memberOf? x e == some q then inRange else e
  if all then
    match b with
    | .forallE n a c bi => if c.hasLooseBVars then b else .forallE n (inGuard a) (replaceSpine all q x inRange c) bi
    | _ => b
  else inGuard b

/-- A marked quantifier of a query: a `forall` if `all`, the number of its
bound names, and the sequence of each, or `none` for one that the body does
not mention; or `none` if it is not expanded. -/
structure Site where
  all : Bool
  n : Nat
  receivers? : Option (Array (Option Expr))

/-- What a query's traversal collects (`FrenCli.SeqElems.Scan`). -/
structure Scan where
  sites : Array Site := #[]
  reads : Array Expr := #[]
  updates : Array (Expr × Expr × Expr) := #[]
  updateTerms : Array (Expr × Expr × Expr × Expr) := #[]
  equations : Array (Expr × Expr) := #[]

/-- Whether `e` mentions only the locals of `ctx`: none that a binder of
the query binds. -/
def closedIn (ctx : Std.HashSet FVarId) (e : Expr) : Bool :=
  !e.hasLooseBVars && (e.find? fun x => x.isFVar && !ctx.contains x.fvarId!).isNone

/-- `t + k`, an `Int`. -/
def plus (t : Expr) (k : Int) : MetaM Expr := do
  let int := mkConst ``Int
  if k < 0 then mkAppM ``HSub.hSub #[t, ← mkNumeral int k.natAbs]
  else mkAppM ``HAdd.hAdd #[t, ← mkNumeral int k.natAbs]

/-- The binders around a term of a query, outermost first, each with the
locals that stand for its bound names (`Fren.Core.Frame`). -/
abbrev Frames := Array (Array Expr × Core.Frame)

/-- `frames` for a part of the term within them: still on the innermost
quantifier's spine only if `keep`, as the binary's `Frames.within`. -/
def Frames.within (frames : Frames) (keep : Bool) : Frames :=
  match frames.back? with
  | some (xs, .element all spine) => frames.pop.push (xs, .element all (spine && keep))
  | _ => frames

/-- Records the reads, updates and equations between sequences of the
application `x`, at terms that mention only the locals of `ctx`. -/
def noteApp (ctx : Std.HashSet FVarId) (ref : IO.Ref Scan) (x : Expr) : MetaM Unit := do
  if x.isAppOfArity ``Fren.Seq.nth 4 then
    let i := x.appArg!
    if closedIn ctx i then ref.modify fun s => { s with reads := s.reads.push i }
  if x.isAppOfArity ``Fren.Seq.update 4 then
    let i := x.appFn!.appArg!
    if closedIn ctx i then
      let u := (← plus i (-1), i, ← plus i 1)
      ref.modify fun s => { s with updates := s.updates.push u }
    if closedIn ctx x && !(← ref.get).updateTerms.any (·.1 == x) then
      ref.modify fun s => { s with updateTerms := s.updateTerms.push (x, x.appFn!.appFn!.appArg!, i, x.appArg!) }
  if x.isAppOfArity ``Eq 3 && x.appFn!.appFn!.appArg!.isAppOfArity ``Fren.Seq 1 then
    let (a, b) := (x.appFn!.appArg!, x.appArg!)
    if closedIn ctx a && closedIn ctx b then ref.modify fun s => { s with equations := s.equations.push (a, b) }

/-- `e`, within `frames`, with each marked quantifier numbered, and recorded
with its sequences if it is expanded (`Fren.Core.siteExpanded`), as the
binary's `scan`; and its reads, updates and equations between sequences,
at terms that mention only the locals of `ctx`, which no binder of the
query binds. The consequent of an implication and the conjuncts of `∧`
are on the innermost quantifier's spine; nothing else is. -/
partial def scan (ctx : Std.HashSet FVarId) (ref : IO.Ref Scan) (frames : Frames) (e : Expr) : MetaM Expr := do
  if let some (n, none, q) := marked? e then
    let .mdata d _ := e | return e
    let all := isAll q
    let k := (← ref.get).sites.size
    ref.modify fun s => { s with sites := s.sites.push { all, n, receivers? := none } }
    let r ← withBound all n q fun xs b => do
      let receivers := xs.map fun x =>
        if !(b.containsFVar x.fvarId!) then some none
        else ((spineMembers all x b).find? (closedIn ctx)).map some
      let mentioned := (List.range frames.size).filter fun j => frames[j]!.1.any (b.containsFVar ·.fvarId!)
      let expanded := Core.siteExpanded (frames.toList.map (·.2)) all (receivers.all Option.isSome) mentioned
      if expanded then
        ref.modify fun s => { s with sites := s.sites.set! k { all, n, receivers? := some (receivers.map (·.join)) } }
      let frame : Core.Frame := if expanded then .element all true else .other
      let b ← scan ctx ref (frames.push (xs, frame)) b
      if all then mkForallFVars xs b
      else xs.foldrM (init := b) fun x acc => do mkAppM ``Exists #[← mkLambdaFVars #[x] acc]
    let some q := r | return e
    return .mdata (d.insert siteKey (.ofNat k)) q
  match e with
  | .mdata d b => return .mdata d (← scan ctx ref frames b)
  | .forallE n t b bi =>
    if b.hasLooseBVars then
      withLocalDecl n bi t fun fv => do
        mkForallFVars #[fv] (← scan ctx ref (frames.push (#[fv], .other)) (b.instantiate1 fv))
    else return .forallE n (← scan ctx ref (frames.within false) t) (← scan ctx ref (frames.within true) b) bi
  | .lam n t b bi =>
    withLocalDecl n bi t fun fv => do
      mkLambdaFVars #[fv] (← scan ctx ref (frames.push (#[fv], .other)) (b.instantiate1 fv))
  | .app .. =>
    noteApp ctx ref e
    let keep := e.isAppOfArity ``And 2
    let f := e.getAppFn
    let args ← e.getAppArgs.mapM (scan ctx ref (frames.within keep))
    return mkAppN f args
  | _ => return e

/-- A query whose quantifiers would have more instances than
`Fren.Core.maxElementInstances`: how many. -/
def tooManyTag : String := "fren.elems: too many instances: "

/-- `e` with each numbered marked quantifier of `sites` expanded: at each
tuple of the terms that `terms` gives its bound names, with their
memberships in its guard replaced by their positions' being in range,
counted by `count`, which may reach at most `Fren.Core.maxElementInstances`
(`FrenCli.SeqElems.expand`). -/
partial def expand (sites : Array Site) (terms : Nat → Nat → Expr → MetaM (List Expr)) (count : IO.Ref Nat) (e : Expr) :
    MetaM Expr :=
  Meta.transform e (pre := fun x => do
    let some (n, some i, q) := marked? x | return .continue
    let some site := sites[i]? | return .continue
    let some receivers := site.receivers? | return .visit q
    let all := site.all
    let some r ← withBound all n q fun xs b => do
      let choices ← receivers.zipIdx.toList.mapM fun (q?, k) => match q? with
        | some q => return (← terms i k q).map some
        | none => return [none]
      let tuples := choices.foldl (fun acc cs => acc.flatMap fun pre => cs.map (pre ++ [·])) [[]]
      let mut parts := #[]
      for t in tuples do
        let σ := (xs.zip (receivers.zip t.toArray)).filterMap fun (x, q?, t?) => do pure (x, ← q?, ← t?)
        let nths ← σ.mapM fun (_, q, t) => mkAppM ``Fren.Seq.nth #[q, t]
        let mut b' := b.replaceFVars (σ.map (·.1)) nths
        for (_, q, t) in σ, nth in nths do
          let inRange ← mkAppM ``And #[← mkAppM ``LE.le #[← mkNumeral (mkConst ``Int) 0, t],
            ← mkAppM ``LT.lt #[t, ← mkAppM ``Fren.Seq.len #[q]]]
          b' := replaceSpine all q nth inRange b'
        count.modify (· + 1)
        let c ← count.get
        unless Fren.Core.elementSizeAccepted c do throwError s!"{tooManyTag}{c}"
        parts := parts.push (← expand sites terms count b')
      return if parts.isEmpty then mkConst (if all then ``True else ``False)
        else parts.pop.foldr (init := parts.back!) fun p acc => if all then mkAnd p acc else mkOr p acc
      | return .visit q
    return .done r)

/-- An expanded query: its hypotheses and goal, its fresh locals (witnesses
and lengths), and the length locals, each with its sequence. -/
structure Expanded where
  hyps : Array (Name × Expr)
  goal : Expr
  locals : Array Expr
  lengths : Array (Expr × Expr)

/-- `hyps` and `goal` with their marked quantifiers expanded, at the query's
index set, with a witness for each bound name of each expanded quantifier
and for each equation between sequences of which one is a quantifier's,
and each update's reads at the index set (`lang::update_reads`); or with `pins`, the lengths of the sequences in a model, at each position
below a pinned sequence's length; passed to `k`, within the locals that it
declares (`FrenCli.SeqElems.expandQuery`). The error is the number of
instances, if more than `Fren.Core.maxElementInstances`. -/
def withExpanded (hyps : Array (Name × Expr)) (goal : Expr) (pins? : Option (Array (Expr × Nat)))
    (k : Expanded → MetaM α) : MetaM (Except Nat α) := do
  let ctx : Std.HashSet FVarId := .ofList (← getLCtx).getFVarIds.toList
  let ref ← IO.mkRef ({} : Scan)
  let hyps ← hyps.mapM fun (n, h) => return (n, ← scan ctx ref #[] h)
  let goal ← scan ctx ref #[] goal
  let sc ← ref.get
  let expanded := sc.sites.filter (·.receivers?.isSome)
  let receivers := (expanded.flatMap fun s => (s.receivers?.getD #[]).filterMap id).foldl
    (fun acc q => if acc.contains q then acc else acc.push q) #[]
  let nw := expanded.foldl (· + ·.n) 0
  let eqs := sc.equations.filter fun (a, b) => receivers.contains a || receivers.contains b
  let int := mkConst ``Int
  let names := (Array.range nw).map (s!"#w{·}") ++ (Array.range eqs.size).map (s!"#d{·}")
    ++ (Array.range receivers.size).map (s!"#l{·}")
  let decls := if pins?.isSome then #[] else names.map fun n => (Name.mkSimple n, fun _ => pure int)
  withLocalDeclsD decls fun fvs => do
  let (ws, rest) := (fvs.extract 0 nw, fvs.extract nw fvs.size)
  let (ds, ls) := (rest.extract 0 eqs.size, rest.extract eqs.size rest.size)
  let lasts ← receivers.mapM fun q => do plus (← mkAppM ``Fren.Seq.len #[q]) (-1)
  let ix := Fren.Core.indexSet
    { zero := ← mkNumeral int 0, lasts := lasts.toList, reads := sc.reads.toList, updates := sc.updates.toList
      witnesses := (ws ++ ds).toList : Fren.Core.IndexSources Expr }
  let terms (_ _ : Nat) (q : Expr) : MetaM (List Expr) := match pins? with
    | some pins => match pins.find? (·.1 == q) with
      | some (_, n) => (List.range n).mapM fun j => mkNumeral int j
      | none => pure ix
    | none => pure ix
  let count ← IO.mkRef 0
  let run : MetaM (Array (Name × Expr) × Expr) := do
    return (← hyps.mapM fun (n, h) => return (n, ← expand sc.sites terms count h), ← expand sc.sites terms count goal)
  let (hs, g) ← try run catch ex =>
    let msg ← ex.toMessageData.toString
    if let some n := (msg.dropPrefix? tooManyTag).bind (·.toString.toNat?) then return .error n
    throw ex
  let extra ← match pins? with
    | some pins => pins.mapM fun (q, n) => return (`elementLength, ← mkEq (← mkAppM ``Fren.Seq.len #[q]) (← mkNumeral int n))
    | none => do
      let lens ← (ls.zip receivers).mapM fun (l, q) => return (`elementLength, ← mkEq l (← mkAppM ``Fren.Seq.len #[q]))
      -- Two sequences that differ differ at the witness.
      let exts ← (eqs.zip ds).mapM fun ((a, b), d) => do
        let lenNe := mkNot (← mkEq (← mkAppM ``Fren.Seq.len #[a]) (← mkAppM ``Fren.Seq.len #[b]))
        let atNe := mkNot (← mkEq (← mkAppM ``Fren.Seq.nth #[a, d]) (← mkAppM ``Fren.Seq.nth #[b, d]))
        let inRange ← mkAppM ``And #[← mkAppM ``LE.le #[← mkNumeral int 0, d], ← mkAppM ``LT.lt #[d, ← mkAppM ``Fren.Seq.len #[a]]]
        return (`elementWitness, mkOr (← mkEq a b) (mkOr lenNe (mkAnd inRange atNe)))
      -- Each update's reads at the index set (`lang::update_reads`).
      let reads ← sc.updateTerms.mapM fun (u, r, i, x) => do
        let len ← mkEq (← mkAppM ``Fren.Seq.len #[u]) (← mkAppM ``Fren.Seq.len #[r])
        let parts ← ix.mapM fun t => do
          let inRange ← mkAppM ``And #[← mkAppM ``LE.le #[← mkNumeral int 0, t], ← mkAppM ``LT.lt #[t, ← mkAppM ``Fren.Seq.len #[r]]]
          let here ← mkEq (← mkAppM ``Fren.Seq.nth #[u, t]) x
          let other ← mkEq (← mkAppM ``Fren.Seq.nth #[u, t]) (← mkAppM ``Fren.Seq.nth #[r, t])
          return [← mkArrow (mkAnd inRange (← mkEq t i)) here, ← mkArrow (mkAnd inRange (mkNot (← mkEq t i))) other]
        return (`elementUpdate, parts.flatten.foldl mkAnd len)
      pure (lens ++ exts ++ reads)
  return .ok (← k { hyps := hs ++ extra, goal := g, locals := fvs, lengths := ls.zip receivers })

end Fren.Elems
