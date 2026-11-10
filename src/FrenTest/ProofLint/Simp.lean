module

public import Lean

/-!
Linters for `@[simp]` lemmas, run over an imported environment.

The checks follow the `simpNF` and `simpComm` linters of Batteries
(`Batteries/Tactic/Lint/Simp.lean`, Apache 2.0, by Gabriel Ebner and others).
The code here is our own and smaller: Fren depends on neither Batteries nor
Mathlib.

`simpNF` reports a lemma when
- simp with the whole default simp set fails on its left-hand side (for
  example because the lemma loops);
- the default simp set without the lemma rewrites its left-hand side, so
  another lemma competes with it whichever simp tries first: either simp then
  also reaches the right-hand side (the lemma is redundant) or it reaches
  another term (the left-hand side is not in simp normal form);
- an unconditional lemma leaves its own left-hand side unchanged;
- its two sides are definitionally equal with reducible transparency, so
  rewriting with it changes nothing that simp can tell apart.

`simpLoop` reports a lemma
- whose right-hand side is its left-hand side with the variables renamed,
  such as commutativity;
- whose right-hand side contains an instance of its left-hand side, so the
  lemma applies to its own result;
- whose right-hand side the other linted lemmas rewrite to a term that
  contains an instance of its left-hand side. This search is bounded: it
  follows cycles of at most `cycleLength` lemmas, the first included, and
  gives up on a lemma after `cycleTerms` distinct terms. It rewrites all the
  instances of one lemma's left-hand side at a time, from the lemma's general
  form, so a cycle that needs the first lemma instantiated is found from the
  more special lemma of the cycle;
- on whose left-hand side simp with the whole default simp set runs out of
  `loopSteps` steps or `loopDepth` nested calls. No bounded search decides
  whether a set of lemmas loops, so this run is the general check, and the
  three above give the precise reasons where they apply.

Each finding has a kind (`redundant`, `cycle`, `step-limit`, `depth-limit`
and so on), and
its identity is the lemma and the kind, with `@n` for the n-th rewrite of a
lemma that states several, from the second on.

What `simpLoop` cannot see: a loop that starts only from a term that is no
linted lemma's left-hand side in its general form and that the cycle search's
bounds do not reach, such as one that needs a variable instantiated and more
than `cycleLength` lemmas; a loop that needs a hypothesis that simp cannot
discharge on the general left-hand side, beyond those bounds too; and a loop
that arises only with lemmas outside the default simp set of the linted
modules. In the other direction, a left-hand side whose simplification ends
but takes more than `loopSteps` steps is reported.

Limits. Only lemmas in the default simp set of the imported environment are
seen: `local` and `scoped` attributes, other simp sets and `simp only`
arguments are not. The sides of a lemma are read from its statement (`=`, `↔`,
`¬`, `≠`, `∧` and plain propositions), not through simp's own preprocessing,
so a statement hidden behind a definition is read as a plain proposition. The
simp set is that of all the linted modules together, a superset of the one in
scope at any use. Lean's simp applies a permutation lemma only when the
result is smaller in a term order, so such a lemma does not literally loop;
it is reported because its effect depends on that order, and the cycle search
takes no step with one. The loop checks ignore a lemma's hypotheses, so they
report a conditional lemma whose hypotheses would stop the loop. The cycle
search steps only with the linted modules' lemmas whose left-hand side is an
application of a constant, matched with reducible unfolding at that constant
and number of arguments.
-/

public section

namespace FrenTest.ProofLint
open Lean Meta

/-- A finding about a declaration: the linter's name, the declaration as its
author wrote it (a private name without its prefix) and the reason. -/
structure Finding where
  linter : String
  decl : Name
  kind : String
  message : String

/-- What the allowlist names a finding by: the lemma and the finding's kind. -/
def Finding.identity (finding : Finding) : String := s!"{finding.decl}:{finding.kind}"

/-- The rewrites `lhs → rhs` that simp reads from a lemma's conclusion. -/
private partial def sides (e : Expr) : MetaM (Array (Expr × Expr)) := do
  match_expr e with
  | Eq _ a b => return #[(a, b)]
  | Iff a b => return #[(a, b)]
  | Not p => return #[(p, mkConst ``False)]
  | Ne _ a b => return #[(← mkEq a b, mkConst ``False)]
  | And p q => return (← sides p) ++ (← sides q)
  | _ => return #[(e, mkConst ``True)]

/-- The variables among `xs` that occur in `e`, in order of first occurrence. -/
private partial def occurring (xs : Array Expr) (e : Expr) (found : Array Expr := #[]) : Array Expr :=
  match e with
  | .app f a => occurring xs a (occurring xs f found)
  | .fvar _ => if xs.contains e && !found.contains e then found.push e else found
  | .lam _ t b _ | .forallE _ t b _ => occurring xs b (occurring xs t found)
  | .letE _ t v b _ => occurring xs b (occurring xs v (occurring xs t found))
  | .mdata _ b | .proj _ _ b => occurring xs b found
  | _ => found

/-- `e` with its variables numbered by first occurrence: two terms have the
same shape exactly when one is the other with its variables renamed
one-to-one. -/
private def shape (xs : Array Expr) (e : Expr) : Expr :=
  e.abstract (occurring xs e)

private def same (a b : Expr) : MetaM Bool :=
  withReducible <| withNewMCtxDepth <| isDefEq a b

private def show_ (e : Expr) : MetaM String := return toString (← ppExpr e)

private def usedNames (stats : Simp.Stats) : String :=
  ", ".intercalate (stats.usedTheorems.toArray.toList.map (toString <| privateToUserName ·.key))

/-- The `simpNF` reasons for one rewrite of `decl`, each with its kind. -/
private def normalForm (decl : Name) (xs : Array Expr) (lhs rhs : Expr) : MetaM (Array (String × String)) := do
  let mut found := #[]
  if ← same lhs rhs then
    found := found.push <| .mk "reducible-sides" s!"the sides {← show_ lhs} and {← show_ rhs} are equal by reducible unfolding, so rewriting changes nothing"
  let theorems ← getSimpTheorems
  let congruence ← getSimpCongrTheorems
  let simprocs := #[← Simp.getSimprocs]
  let attempt (whole : Bool) (side : String) (e : Expr) : MetaM (Except String (Simp.Result × Simp.Stats)) := do
    let ctx ← Simp.mkContext (congrTheorems := congruence)
      (simpTheorems := #[if whole then theorems else theorems.eraseCore (.decl decl)])
    tryCatchRuntimeEx (do return .ok (← withCurrHeartbeats <| simp e ctx simprocs)) fun error => do
      return .error s!"simp fails on the {side}-hand side {← show_ e}: {← error.toMessageData.toString}"
  let (whole, _) ← match ← attempt true "left" lhs with
    | .ok result => pure result
    | .error reason => return found.push ("simp-fails", reason)
  -- Without the lemma, so that it cannot win against a lemma that competes
  -- with it for its own left-hand side.
  let (left, stats) ← match ← attempt false "left" lhs with
    | .ok result => pure result
    | .error reason => return found.push ("simp-fails", reason)
  let (right, _) ← match ← attempt false "right" rhs with
    | .ok result => pure result
    | .error reason => return found.push ("simp-fails", reason)
  if ← same left.expr right.expr then
    -- An unchanged left-hand side means the sides agree by unfolding alone,
    -- which the check above reports when the unfolding is reducible.
    if left.proof?.isSome || left.expr != lhs then
      found := found.push <| .mk "redundant" s!"simp proves this without the lemma, using {usedNames stats}"
  else if !(← same left.expr lhs) then
    found := found.push <| .mk "lhs-not-normal" s!"without the lemma, the left-hand side {← show_ lhs} simplifies to {← show_ left.expr} using {usedNames stats}, so the lemma does not fire as written"
  else
    let conditional ← xs.anyM fun x => do
      return (← isProp (← inferType x)) && !(occurring #[x] lhs).contains x
    -- Simp applies a lemma that only renames variables when the result is
    -- smaller in its term order, which a general left-hand side need not be.
    if !conditional && lhs == whole.expr && shape xs lhs != shape xs rhs then
      found := found.push <| .mk "never-applies" s!"simp does not rewrite the left-hand side {← show_ lhs} with this lemma, so it never applies"
  return found

/-- The longest cycle of lemmas that `simpLoop` follows, the first included. -/
def cycleLength : Nat := 4
/-- The number of distinct terms after which `simpLoop` gives up on a lemma. -/
def cycleTerms : Nat := 32

/-- The simp steps after which `simpLoop` takes a left-hand side to loop. -/
def loopSteps : Nat := 1000
/-- The depth of nested calls at which it does so. -/
def loopDepth : Nat := 256

/-- How simp with the whole default simp set runs away on `e`, if it does:
out of `loopSteps` steps or `loopDepth` nested calls. Any other failure is
`simpNF`'s to report. -/
private def runsAway (e : Expr) : MetaM (Option (String × String)) := do
  let ctx ← Simp.mkContext (config := { maxSteps := loopSteps })
    (simpTheorems := #[← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let simprocs := #[← Simp.getSimprocs]
  withTheReader Core.Context (fun context => { context with maxRecDepth := loopDepth }) do
    tryCatchRuntimeEx (do discard <| withCurrHeartbeats <| simp e ctx simprocs; return none) fun error => do
      if error.isMaxRecDepth then return some ("depth-limit", s!"needs more than {loopDepth} nested calls")
      if ((← error.toMessageData.toString).splitOn "maximum number of steps").length > 1 then
        return some ("step-limit", s!"takes more than {loopSteps} steps")
      return none

/-- One rewrite of a simp lemma, for the cycle search: the lemma, which of its
rewrites this is, the constant and argument count of its left-hand side, and
whether it only renames variables. -/
private structure Rule where
  decl : Name
  side : Nat
  head : Name
  arity : Nat
  permutes : Bool

/-- `e` with every instance of the rule's left-hand side rewritten, if it has one. -/
private def rewrite (rule : Rule) (e : Expr) : MetaM (Option Expr) := do
  let hit ← IO.mkRef false
  let info ← getConstInfo rule.decl
  let result ← Meta.transform e (pre := fun sub => do
    unless sub.getAppFn.isConstOf rule.head && sub.getAppNumArgs == rule.arity do return .continue
    let levels ← mkFreshLevelMVars info.levelParams.length
    let (_, _, body) ← forallMetaTelescope (info.type.instantiateLevelParams info.levelParams levels)
    let some (lhs, rhs) := (← sides body)[rule.side]? | return .continue
    unless ← withReducible (isDefEq lhs sub) do return .continue
    let rhs ← instantiateMVars rhs
    if rhs.hasMVar then return .continue
    hit.set true
    return .done rhs)
  return if ← hit.get then some result else none

/-- The lemmas that rewrite `rhs`, the result of `start`, to a term with an
instance of the left-hand side of `start`: none of them if `rhs` has one
already. The search is breadth-first within the bounds above. -/
private def cycle (rules : Array Rule) (start : Rule) (rhs : Expr) : MetaM (Option (List Name)) :=
  withoutModifyingState do
    if (← rewrite start rhs).isSome then return some []
    let mut frontier : Array (Expr × List Name) := #[(rhs, [])]
    let mut seen := #[rhs]
    for _ in [1:cycleLength] do
      let mut next := #[]
      for (term, path) in frontier do
        for rule in rules do
          if rule.permutes || seen.size ≥ cycleTerms then continue
          let some after ← rewrite rule term | continue
          if seen.contains after then continue
          let path := path ++ [privateToUserName rule.decl]
          if (← rewrite start after).isSome then return some path
          seen := seen.push after
          next := next.push (after, path)
      frontier := next
    return none

/-- Whether `decl` is a lemma that a person wrote, rather than one that Lean
generated (`injEq`, `sizeOf_spec`, equation lemmas and the like). -/
private def written (decl : Name) : CoreM Bool := do
  let some info := (← getEnv).find? decl | return false
  unless info matches .thmInfo .. | .axiomInfo .. do return false
  return !(← isAutoDeclOrPrivate_Internal (privateToUserName decl))

/-- The default simp set's lemmas that are declared in `modules`. -/
private def simpLemmas (modules : Array Name) : CoreM (Array Name) := do
  let env ← getEnv
  let indices := modules.filterMap env.getModuleIdx?
  let mut found := #[]
  for origin in (← getSimpTheorems).lemmaNames.toList do
    let .decl decl .. := origin | continue
    let some index := env.getModuleIdxFor? decl | continue
    if indices.contains index && !found.contains decl && (← written decl) then
      found := found.push decl
  return found.qsort (·.toString < ·.toString)

/-- The rewrites of a lemma, for the cycle search. -/
private def rulesOf (decl : Name) : MetaM (Array Rule) := do
  forallTelescope (← getConstInfo decl).type fun xs body => do
    let mut rules := #[]
    for (lhs, rhs) in ← sides body do
      let head := lhs.getAppFn.constName?.getD .anonymous
      rules := rules.push { decl, side := rules.size, head, arity := lhs.getAppNumArgs,
                            permutes := lhs != rhs && shape xs lhs == shape xs rhs }
    return rules

private def lint (modules : Array Name) : MetaM (Array Finding) := do
  let mut findings := #[]
  let lemmas ← simpLemmas modules
  let rules ← lemmas.flatMapM rulesOf
  for decl in lemmas do
    let name := privateToUserName decl
    let own := rules.filter (·.decl == decl)
    findings := findings ++ (← forallTelescope (← getConstInfo decl).type fun xs body => do
      let mut found : Array Finding := #[]
      let rewrites ← sides body
      -- Each rewrite with its own rule: `rulesOf` numbers them in this order.
      for i in [:rewrites.size] do
        let (lhs, rhs) := rewrites[i]!
        let some rule := own.find? (·.side == i) | continue
        let nth := if i == 0 then "" else s!"@{i + 1}"
        let reasons ← tryCatchRuntimeEx (normalForm decl xs lhs rhs) fun error => do
          return #[("linter-failed", s!"the linter failed: {← error.toMessageData.toString}")]
        found := found ++ reasons.map fun (kind, message) =>
          { linter := "simpNF", decl := name, kind := kind ++ nth, message }
        let loop (kind message : String) : Finding :=
          { linter := "simpLoop", decl := name, kind := kind ++ nth, message }
        if rule.permutes then
          found := found.push <| loop "renaming" s!"the right-hand side {← show_ rhs} is the left-hand side {← show_ lhs} with its variables renamed"
        else match ← cycle rules rule rhs with
          | none => pure ()
          | some [] =>
            found := found.push <| loop "self-instance" s!"the right-hand side {← show_ rhs} contains an instance of the left-hand side {← show_ lhs}, so the lemma applies to its own result"
          | some path =>
            found := found.push <| loop "cycle" s!"rewriting the right-hand side {← show_ rhs} with {", ".intercalate (path.map toString)} gives an instance of the left-hand side {← show_ lhs} again"
        if let some (kind, how) ← runsAway lhs then
          found := found.push <| loop kind s!"simp {how} on the left-hand side {← show_ lhs}, so the simp set loops from it"
      return found)
  return findings

/-- The findings of `simpNF` and `simpLoop` for the simp lemmas that `modules`
declare, and the number of lemmas checked. -/
def lintSimp (env : Environment) (modules : Array Name) : IO (Array Finding × Nat) := do
  let run : MetaM (Array Finding × Nat) := do
    return (← lint modules, (← simpLemmas modules).size)
  let context : Core.Context := { fileName := "<proofLint>", fileMap := default }
  let (result, _) ← (run.run' {} {}).toIO context { env }
  return result

end FrenTest.ProofLint
