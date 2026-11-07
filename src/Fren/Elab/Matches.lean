-- keep-sorted start
import Fren.Elab.PatternLints
import Fren.Elab.Patterns
-- keep-sorted end

/-! # Hosted elaboration: matches -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The type of a `match`'s arms so far, `armsTy?`, after the arm whose body
`ref` is translated to `body` and checked against `shared?`
(`lang::arm_type`). A body that does not synthesize its type has the one
it is checked against, as in the `fren` command. -/
def armType (cx : ExprCtx) (armsTy? : Option Core.Ty) (ref : Syntax) (body : Term) (shared? : Option Core.Ty) :
    TermElabM (Option Core.Ty) := do
  let synth ← synthesizes cx ref
  let t? := (← frenTypeOf? body).orElse fun _ => if synth then none else shared?
  let some t := t? | return armsTy?
  return some (← liftMsg ref (Core.checkArm armsTy? t))

/-- Records the questions about the arms of the `match` `e`, whose patterns
are `pats`, each taken where `taken` says, of which those with a guard
are `guarded`, for its completeness and reachability checks
(`check::completeness`, `check::reachability`): completeness, unless its
arms without guards are exhaustive, is reported at `match`, and the
reachability of an arm at its pattern. Of a table over a scrutinee
(`table?`, the pairs of its arms that the disjointness check asks about,
whose guards' indexes are in range where `defined` says), also the
disjointness of those pairs, at the later arm's pattern, and completeness
at `table`. -/
def noteMatch (cx : ExprCtx) (e : Syntax) (pats : Array Syntax) (taken : Array (Option Term)) (guarded : Array Bool)
    (unguardedExhaustive : Bool) (table? : Option (Array (Nat × Nat))) (defined : Array (Option Term)) :
    TermElabM Unit := do
  unless cx.noteIndexes do return
  let orF (cs : Array Term) : Term := cs.pop.foldr (fun c acc => Unhygienic.run `($c ∨ $acc)) cs.back!
  let andF (a b : Term) : Term := Unhygienic.run `($a ∧ $b)
  let notF (c : Term) : Term := Unhygienic.run `(¬$c)
  let trueF : Term := Unhygienic.run `(True)
  let complete := Core.completenessAsked unguardedExhaustive
  let goals := match table? with
    | some pairs => Core.tableMatchGoals orF andF notF trueF taken guarded defined pairs complete
    | none => Core.splitGoals .match orF andF notF trueF taken guarded complete
  for (g, f) in goals do
    let ref := match g with
      | .reachability _ j | .disjointness _ _ j => pats[j]!
      | _ => e[0]
    let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

/-- The alternatives of the or-pattern `p` at the top of an arm's pattern,
each its own Lean pattern, or `p` alone (`patHeads`). -/
partial def topPats (p : Core.Pat) : Array Core.Pat :=
  match p with
  | .or alts => alts.flatMap topPats
  | p => #[p]

/-- The pattern `q` of a value of type `ty`, built from `_`, binders and
variants (`matchForm`), as a pattern of Lean's `match`: each binder is
named by the next of `names`, in preorder. -/
partial def leanPattern (names : Array Name) (ty : Expr) (q : Core.Pat) : StateT Nat TermElabM Term := do
  match q with
  | .wild false => `(_)
  | .wild true =>
    let k ← get
    set (k + 1)
    let some n := names[k]? | throwError "internal error: a binder without a name"
    pure ⟨mkIdent n⟩
  | .ctor idx args =>
    let some info := (← getState).enumOf? ty
      | throwError "internal error: a variant's pattern of a value that is not of an enumeration"
    let tys := (← info.payloadsAt ty.getAppArgs)[idx]!
    let ps ← (args.zip tys).mapM fun (a, t) => leanPattern names t a
    if ps.isEmpty then pure ⟨mkCIdent (info.ctor idx)⟩ else `($(mkCIdent (info.ctor idx)) $ps*)
  | _ => throwError "internal error: a pattern that is not Lean's"

/-- The arms of a Lean `match`, each an alternative of a pattern of `ty`
(`topPats`) with its right-hand side, but those that Lean would find
redundant after the earlier ones, with `_` and `default` last where those
are not exhaustive (`Reqs/Generated#matches`). -/
def leanMatchAlts (pty : Core.PatTy) (arms : Array (Array (Core.Pat × Term) × Term)) (default : Term) :
    TermElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  let sigs ← patSigs
  let mut rows : Array (List Core.Pat) := #[]
  let mut out := #[]
  for (alts, rhs) in arms do
    for (q, p) in alts do
      unless Core.useful sigs [pty] rows [q] do continue
      rows := rows.push [q]
      out := out.push (← `(Lean.Parser.Term.matchAltExpr| | $p:term => $rhs))
  if Core.useful sigs [pty] rows [.wild false] then
    out := out.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $default))
  return out

open Lang in
/-- The `match` `e` on `s`, of type `ty`, whose arms' patterns are `pats`, as
a Lean `match`, where `toTerm` translates its parts again, with each
binder the local that its pattern binds (`Reqs/Generated#matches`): an
arm with a guard is taken where its pattern matches and its guard holds,
and otherwise the arms after it are tried, as `rest k ()`, which tries the
arms from `k` on. `none` where its arms are propositions, which stay `if`s
(`matchForm`). Each arm's context, binders and expected type are
`armInfo`, as the `if`s' translation has them. -/
def leanMatchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (s : Term) (ty : Expr)
    (pty : Core.PatTy) (pats : Array Core.Pat) (armInfo : Array (ExprCtx × Array MatchBinder × Option Core.Ty))
    (vector? : Option (Array Expr × Array Term × Core.Sigs) := none) : TermElabM (Option Term) := do
  let arms := e[3].getSepArgs
  let mut bodies : Array Term := #[]
  let mut guards : Array (Option Term) := #[]
  let mut tys : Array (Option Expr) := #[]
  for arm in arms, (acx, new, exp) in armInfo do
    let decls := new.map fun b => (b.name, fun (_ : Array Expr) => pure b.type)
    let (g?, body, ty?) ← withLocalDeclsD decls fun _ => do
      let lcx : ExprCtx := { acx with binders := cx.binders ++ new.map fun (b : MatchBinder) => { b with term := ⟨mkIdent b.name⟩ } }
      let g? ← if arm[1].isNone then pure none
        else some <$> toTerm { lcx with natOk := false, emptyOk := Core.ExprSite.armGuard.checked false false, expected? := Core.ExprSite.armGuard.expected none none } arm[1][1]
      let body ← toTerm { lcx with expected? := exp } arm[3]
      let ty? ← try some <$> typeOf body catch _ => pure none
      return (g?, body, ty?)
    bodies := bodies.push body
    guards := guards.push g?
    tys := tys.push ty?
  let mut armKind : ArmKind := if tys.any (·.any (·.isProp)) then .propositions else .values
  if armKind == .propositions && cx.leanBoolArms then
    bodies ← (bodies.zip tys).mapM fun (b, t?) => if t?.any (·.isProp) then `(decide $b) else pure b
    tys := tys.map fun t? => if t?.any (·.isProp) then some (Lean.mkConst ``Bool) else t?
    armKind := .values
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  let heads := if vector?.isSome then pats.flatMap fun p => match p with
    | .ctor _ ps => ps.flatMap patHeads
    | _ => patHeads p
    else pats.flatMap patHeads
  unless matchForm scrutineeKind armKind heads == .leanMatch do return none
  -- An `Int` where another arm is a `Nat` (`widenMixed`).
  let mixed := tys.any (·.any (·.isConstOf ``Int)) && tys.any (·.any (·.isConstOf ``Nat))
  let widen (b : Term) (t? : Option Expr) : TermElabM Term :=
    if mixed && t?.any (·.isConstOf ``Nat) then `(($b : Int)) else pure b
  bodies ← (bodies.zip tys).mapM fun (b, t?) => widen b t?
  let default ← `(Fren.Seq.nth (∅ : Fren.Seq _) 0)
  let n := arms.size
  let rests ← (Array.range (n + 1)).mapM fun k => return mkIdent (← mkFreshUserName (Name.mkSimple s!"rest{k}"))
  let fallTo (k : Nat) : TermElabM Term := if k == n then pure default else `($(rests[k]!) ())
  let names := armInfo.map fun (_, new, _) => new.map (·.name)
  let altsOf (k : Nat) : TermElabM (Array (Core.Pat × Term)) :=
    (topPats pats[k]!).mapM fun q => return (q, ← (leanPattern names[k]! ty q).run' 0)
  -- The `match` of the arms from `start` on.
  let build (start : Nat) : TermElabM Term := do
    if let some (types, terms, signatures) := vector? then
      let mut rows : Array (List Core.Pat) := #[]
      let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for k in [start:n] do
        let rhs ← match guards[k]! with
          | some g => do let rest ← fallTo (k + 1); `(if $g then $(bodies[k]!) else $rest)
          | none => pure bodies[k]!
        for q in (pats[k]!.expand).1.map (·.1) do
          unless Core.useful signatures [pty] rows [q] do continue
          rows := rows.push [q]
          let columns ← match q with
            | .ctor _ ps => ((ps.zip types).mapM fun (p, t) => leanPattern names[k]! t p).run' 0
            | _ => types.mapM fun _ => `(_)
          alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $columns:term,* => $rhs))
      if Core.useful signatures [pty] rows [.wild false] then
        let wilds ← types.mapM fun _ => `(_)
        alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $wilds:term,* => $default))
      let discrs ← terms.mapM fun t => `(Lean.Parser.Term.matchDiscr| $t:term)
      return ← `(match $discrs:matchDiscr,* with $alts:matchAlt*)
    let mut out := #[]
    for k in [start:n] do
      let rhs ← match guards[k]! with
        | some g => do
          let r ← fallTo (k + 1)
          `(if $g then $(bodies[k]!) else $r)
        | none => pure bodies[k]!
      out := out.push (← altsOf k, rhs)
    let alts ← leanMatchAlts pty out default
    `(match $s:term with $alts:matchAlt*)
  -- Of the arms' type, so that a `match` of `Bool`s where a proposition is
  -- expected is coerced as a whole, rather than each arm, which would leave
  -- a `match` of propositions, with no `Decidable` instance.
  let t? := if mixed then some (Lean.mkConst ``Int) else tys.findSome? id
  let tStx? ← t?.mapM exprToSyntax
  let typed (m : Term) : TermElabM Term := match tStx? with
    | some t => `(($m : $t))
    | none => pure m
  let mut out ← typed (← build 0)
  let needed := (Array.range n).filterMap fun k => if guards[k]!.isSome && k + 1 < n then some (k + 1) else none
  unless needed.isEmpty do
    let some tStx := tStx? | throwError "internal error: no type for the arms of a `match`"
    for k in needed do
      out ← `(let $(rests[k]!) : Unit → $tStx := fun _ => $(← build k); $out)
  return some out

open Lang in
/-- Translates a `match` into a chain of `if`s that test its scrutinee
against each arm's pattern, where `toTerm` translates its parts: a variant
by comparing with the variant built from the value's own payload, a
literal by equality and a range by comparisons; binders read the payload
with the selectors. -/
def matchTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (slot : Option Core.Slot) :
    TermElabM Term := withRef e do
  -- What is expected of the whole, which only the parts named below see.
  let expected? := cx.expected?
  let cx := { cx with expected? := none }
  -- The scrutinee synthesizes its type, and each body is checked against the
  -- whole's, or another's (`lang::checked`).
  let original := e
  let many := isManyMatch e
  let scrutinees := matchScrutinees e
  let sourceArms := matchSourceArms e
  for arm in sourceArms do
    unless (matchPatterns e arm).size == scrutinees.size do
      throwErrorAt arm (Core.arityMsg `match scrutinees.size (matchPatterns e arm).size "pattern").text
  let terms ← scrutinees.mapM (toTerm { cx with emptyOk := Core.ExprSite.scrutinee.checked false false, natOk := false })
  let types ← terms.mapM typeOf
  let ptypes := types.map (patTyOf (← getState))
  for scr in scrutinees, pty in ptypes, ty in types do
    if pty == .other then throwErrorAt scr (Core.scrutineeMsg (← typeName ty)).text
  let scrutinee := scrutinees[0]!
  let origin? := scrutinees.findSome? cx.recOrigin?
  let arms := sourceArms.map (matchArm e)
  let mut resolved := #[]
  let mut rows := #[]
  for arm in sourceArms do
    let parts ← ((matchPatterns e arm).zipIdx).mapM fun (p, j) => do
      let (q, bs, test) ← resolveTop cx types[j]! terms[j]! false p
      return (q, bs.map fun b => { b with source? := some scrutinees[j]! }, test)
    rows := rows.push (parts.map (·.1))
    -- The arm's test, the conjunction of its patterns' tests, each of its
    -- scrutinee on its own, but none of a pattern that tests nothing
    -- (`Core.Pat.irrefutable`, `Core.armTest`), as the `fren` command has it.
    resolved := resolved.push (parts[0]!.1, parts.flatMap (·.2.1),
      Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b))
        (parts.filterMap fun (q, _, t?) => if q.irrefutable then none else t?))
  let baseSigs ← patSigs
  let (sigs, pty, pats) := if many then Core.matchVector baseSigs ptypes rows
    else (baseSigs, ptypes[0]!, rows.map (·[0]!))
  let s := terms[0]!
  let ty := types[0]!
  let e : Syntax := if many then (mkNode (if e.isOfKind ``Lang.tableMatchManyExpr then ``Lang.tableMatchExpr else ``Lang.matchExpr)
    #[e[0], scrutinee, mkAtom "{", Syntax.mkSep arms (mkAtom ","), mkAtom "}"]).raw else e
  let usesBefore := (← getLocal).recUses.size
  let guarded := arms.map (!·[1].isNone)
  let isTable := e.isOfKind ``Lang.tableMatchExpr
  -- In a table over a scrutinee, only the last arm may be `_` without a
  -- guard, the otherwise (`Reqs/Lang/Expressions#tables-over-a-scrutinee`).
  if isTable then
    if let some k := Core.rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g) then
      throwErrorAt arms[k]![0] Core.armAfterWildMsg.text
  let checked := if isTable then Core.checkTableArms sigs pty pats guarded
    else (Core.checkMatch sigs pty pats guarded).map (·, #[])
  let (unguardedExhaustive, pairs) ← match checked with
    | .ok u => pure u
    | .error (some (i, some j), msg) => throwErrorAt ((matchPatterns original sourceArms[i]!).flatMap topAlternatives)[j]! (if many then Core.vectorMsg msg else msg).text
    | .error (some (i, none), msg) => throwErrorAt arms[i]![0] (if many then Core.vectorMsg msg else msg).text
    | .error (none, msg) => throwError (if many then Core.vectorMsg msg else msg).text
  let p := if scrutinee.getNumArgs == 1 then scrutinee[0] else scrutinee
  let implicitArg := p.isOfKind ``Lang.fren_path && (pathSegs p).any (fun n => n.getId.toString.startsWith "#match")
  if cx.noteIndexes then
    -- A lambda match writes no scrutinees; its generated parameters have
    -- no source texts to compare.
    let texts := if implicitArg then #[] else scrutinees.map (exactText ∘ unparen)
    for (j, i, row?) in Core.duplicateScrutinees texts baseSigs ptypes rows do
      recordLint .duplicateScrutinee (unparen scrutinees[j]!) (Core.duplicateScrutineeMsg i row?)
  if cx.noteIndexes && !many && !implicitArg then
    lintMatch cx e ty pats slot
    lintCouldBeTable e sigs pty pats
    lintGuards cx e sigs pty pats
    lintArmIfElse cx e sigs pty pats
  -- In a defined function's Lean definition, a Lean `match`, where its
  -- patterns are Lean's (`Reqs/Generated#matches`).
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  let heads := if many then rows.flatMap (fun ps => ps.flatMap patHeads) else pats.flatMap patHeads
  let lean := cx.leanMatch && matchForm scrutineeKind .values heads == .leanMatch
  -- Each arm's context, binders and the type expected of its body.
  let mut armInfo : Array (ExprCtx × Array MatchBinder × Option Core.Ty) := #[]
  let mut bodies : Array Term := #[]
  -- Where each arm is taken, if no earlier one is: its test and its guard;
  -- `none` for an arm taken wherever it is tried.
  let mut taken : Array (Option Term) := #[]
  -- Of a table over a scrutinee, that the indexes in each arm's guard are
  -- in range where it evaluates them, if it has any.
  let mut defined : Array (Option Term) := #[]
  -- The type of the arms so far, once one has one.
  let mut armsTy? : Option Core.Ty := none
  -- The arms that wait for another's type: their index, context and body.
  let mut waiting : Array (Nat × ExprCtx × Syntax) := #[]
  -- An arm's guard is guarded by its pattern's matching where no earlier
  -- arm is taken (`Core.GuardedOperand.armGuard`), and its body by its
  -- being the first arm taken (`Core.GuardedOperand.armBody`). They are
  -- built directly: their negations are never needed, so `guard` would
  -- only return them.
  for arm in arms, (_, bs, t?) in resolved do
    let before := cx.guards ++ (← taken.filterMapM fun t? => t?.mapM fun t => `(¬$t))
    let armGuards := before ++ t?.toArray
    -- Distinct names (`lang::distinct_names`), by the names they declare,
    -- without the `!` of shadowing.
    let declared := bs.map fun b => (declaredIdent b.ident).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt bs[k]!.ident (Core.dupPatternBinderMsg declared[k]!).text
    let mut new : Array MatchBinder := #[]
    for b in bs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let y ← declare b.ident cx.modName locals
      let bn := y.getId
      liftMsg y (Core.checkVarName bn (some (b.type.isConstOf ``Bool || b.type.isProp)))
      lintName .binder bn y
      -- A payload of a parameter, or of a binder bound from one, is bound
      -- from a payload of that parameter; so is the whole of such a binder.
      let source := b.source?.getD scrutinee
      let payloadOf? := cx.recOrigin? source |>.bind fun (j, p) => if b.payload || p then some j else none
      new := new.push { name := bn, term := b.term, «type» := b.type, scrutinee := some source, outer := cx.binders.size, payloadOf? }
    let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
    -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
    let (g?, d?) ← if arm[1].isNone then pure (none, none) else if !isTable then do
      let g := arm[1][1]
      let c ← toTerm { gcx with natOk := false, emptyOk := Core.ExprSite.armGuard.checked false false, expected? := Core.ExprSite.armGuard.expected none none } g
      checkTermType g c .bool (some Core.armGuardNote)
      pure (some c, none)
    else do
      -- In a table over a scrutinee, translated under its pattern's test
      -- alone, so that its indexes say where it defines them, for its
      -- disjointness; then they, and the questions about its tables, are
      -- put under the earlier arms' not being taken, as a row's condition
      -- is.
      let g := arm[1][1]
      let (k, kt) := ((← getLocal).indexes.size, (← getLocal).tables.size)
      let c ← toTerm { gcx with natOk := false, emptyOk := Core.ExprSite.armGuard.checked false false, expected? := Core.ExprSite.armGuard.expected none none, guards := t?.toArray } g
      checkTermType g c .bool (some Core.armGuardNote)
      let l ← getLocal
      let inGuard := l.indexes.extract k
      let under (f : Term) : TermElabM Term := before.foldrM (fun g acc => `($g → $acc)) f
      let idx ← inGuard.mapM fun (r, f) => return (r, ← under f)
      let tbl ← (l.tables.extract kt).mapM fun (r, q, f) => return (r, q, ← under f)
      modifyLocal fun l => { l with indexes := l.indexes.extract 0 k ++ idx, tables := l.tables.extract 0 kt ++ tbl }
      pure (some c, Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) (inGuard.map (·.2)))
    defined := defined.push d?
    let own := t?.toArray ++ g?.toArray
    taken := taken.push (Core.allOf? (fun a b => Unhygienic.run `($a ∧ $b)) own)
    let others := (arms.eraseIdx! bodies.size).map (·[3])
    let emptyOk := Core.ExprSite.armBody.checked cx.emptyOk (← anySynthesizes cx others)
    let acx := { gcx with guards := armGuards ++ g?.toArray, emptyOk }
    -- Each body is checked against the whole's type, or the arms' so far,
    -- as the `fren` command does: one that does not synthesize its own,
    -- before any has given one, waits for a later arm that does.
    let shared? := Core.ExprSite.armBody.expected expected? armsTy?
    armInfo := armInfo.push (acx, new, shared?)
    if shared?.isNone && !(← synthesizes cx arm[3]) && (← arms.anyM (synthesizes cx ·[3])) then
      waiting := waiting.push (bodies.size, acx, arm[3])
      bodies := bodies.push (← `(sorry))
      continue
    let body ← toTerm { acx with expected? := shared? } arm[3]
    armsTy? ← armType cx armsTy? arm[3] body shared?
    bodies := bodies.push body
  for (k, acx, b) in waiting do
    let shared? := Core.ExprSite.armBody.expected expected? armsTy?
    armInfo := armInfo.modify k fun (c, n, _) => (c, n, shared?)
    let body ← toTerm { acx with expected? := shared? } b
    if armsTy?.isSome then armsTy? ← armType cx armsTy? b body shared?
    bodies := bodies.set! k body
  noteMatch cx e (arms.map (·[0])) taken guarded unguardedExhaustive (if isTable then some pairs else none) defined
  -- A recursive application under a `match` on an enumeration's parameter
  -- or payload that is not a Lean `match` (`lang::recursive_match`).
  if origin?.isSome && pty matches .enum .. then
    let nonLean? := if many then (rows.zipIdx.find? fun (ps, j) => ps.any (!·.leanPattern) || guarded[j]!).map (·.2)
      else Core.firstNonLeanPattern? pats guarded
    if let some k := nonLean? then
      if (← getLocal).recUses.size > usesBefore then
        modifyLocal fun l => { l with recMatches := l.recMatches.push arms[k]![0] }
  let widened ← widenMixed bodies
  if lean then
    if let some m ← leanMatchTerm toTerm cx e s ty pty pats armInfo (if many then some (types, terms, sigs) else none) then return m
  -- The first arm that is taken. Where the arms without guards are
  -- exhaustive, the last arm has none, and takes whatever is left;
  -- otherwise, where none is taken, the `match` is the index out of range
  -- of the empty sequence, as a table where no row holds is.
  let complete := !Core.completenessAsked unguardedExhaustive
  -- An arm with a test or a guard that is last only by completeness is
  -- marked with the scrutinees that its patterns test, so that a model's
  -- confirmation knows it only where it knows them, as `lang::eval`'s
  -- `match` (`Fren.lastArm`): not those of a pattern that tests nothing.
  let tested := (terms.zip (rows.back?.getD #[])).filterMap fun (t, q) => if q.irrefutable then none else some t
  let last ← if taken.back?.join.isSome then tested.foldrM (fun t b => `(Fren.lastArm $t $b)) widened.back!
    else pure widened.back!
  let mut out ← if complete then pure last else `(Fren.Seq.nth (∅ : Fren.Seq _) 0)
  for i in (List.range (if complete then bodies.size - 1 else bodies.size)).reverse do
    out ← match taken[i]! with
      | some t => `(if $t then $(widened[i]!) else $out)
      | none => pure widened[i]!
  return out

open Lang in
/-- Translates `e is P`, which is `match e { P => true, _ => false }`, into
the test of `P` (`Reqs/Lang/Expressions#pattern-tests`). -/
def isTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term := withRef e do
  let scrutinee := e[0]
  let s ← toTerm cx scrutinee
  let ty ← typeOf s
  let pty := patTyOf (← getState) ty
  if pty == .other then throwErrorAt scrutinee (Core.isScrutineeMsg (← typeName ty)).text
  -- Whether the names that it binds are in scope anywhere (`lang::test_scope`):
  -- then its or-patterns bind none, as a `match` arm's do.
  let (k, n) := cx.testAt?.getD (0, 1)
  let binds := Core.testBinds cx.testContext k n
  let (q, bs, test) ← resolveTop cx ty s (!binds) e[2]
  match Core.checkPatternTest (← patSigs) pty q (bs.map (·.ident.getId)) binds cx.testContext with
  | .ok () => pure ()
  | .error (.binder k, msg) => throwErrorAt bs[k]!.ident msg.text
  | .error (.alternative j, msg) => throwErrorAt (topAlternatives e[2])[j]! msg.text
  | .error (.whole, msg) => throwErrorAt e[2] msg.text
  if cx.noteIndexes && !bs.isEmpty then
    modifyLocal fun l => { l with bindingTests := l.bindingTests.push (e.getPos?, e.getTailPos?) }
  if binds && !bs.isEmpty then
    -- Declared as a `match` arm's binders are, for the later operands of the
    -- chain and the body that sees them.
    let declared := bs.map fun b => (declaredIdent b.ident).1.getId
    if let some k := (Core.repeatsAt declared)[0]? then
      throwErrorAt bs[k]!.ident (Core.dupPatternBinderMsg declared[k]!).text
    let mut new := #[]
    for b in bs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let y ← declare b.ident cx.modName locals
      let bn := y.getId
      liftMsg y (Core.checkVarName bn (some (b.type.isConstOf ``Bool || b.type.isProp)))
      if cx.noteIndexes then lintName .binder bn y
      -- With its type, so that where a `Prop` is expected, as in the body
      -- of `when`, the selector's type parameters are those of the
      -- scrutinee's type, not inferred from there.
      let term ← `(($(b.term) : $(← exprToSyntax b.type)))
      new := new.push (bn, term.raw, b.type, scrutinee, cx.binders.size)
    modifyLocal fun l => { l with bound := l.bound ++ new }
  if cx.noteIndexes then
    -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`).
    let irrefutable := Core.irrefutableIsAt (← patSigs) pty q
    if irrefutable then recordLint .irrefutableIs e (Core.irrefutableIsMsg (← patTypeName ty) (q matches .wild _))
    lintOrPatterns (orNode (topAlts e[2]).1 q)
    let texts := (topAlts e[2]).1.map exactText
    -- Not of the pattern shorthand's test, whose scrutinee is not written,
    -- and which has no form with `=` (`Reqs/Lang/SubsetTypes#the-pattern-shorthand`).
    let generated := (soleName? scrutinee).any (Core.generatedName <| Core.nameText ·)
    if !generated && Core.isEquality texts.size (Core.equatable q texts) irrefutable then
      let msg := Core.isEqualityMsg { text := exactText scrutinee, prec := exprPrec scrutinee } texts[0]!
      recordLint .isEquality e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)
  -- In a defined function's Lean definition, a test that binds nothing is a
  -- Lean `match` where its pattern is Lean's (`Reqs/Generated#matches`).
  let scrutineeKind : ScrutineeKind := if pty matches .enum .. then .enumeration else .other
  if cx.leanMatch && bs.isEmpty && matchForm scrutineeKind .values (patHeads q) == .leanMatch then
    let alts ← (topPats q).mapM fun a => return (a, ← (leanPattern #[] ty a).run' 0)
    let ms ← leanMatchAlts pty #[(alts, ← `(true))] (← `(false))
    return ← `(((match $s:term with $ms:matchAlt*) : Bool) = true)
  match test with
  | some t => return t
  | none => `(true)


end Fren
