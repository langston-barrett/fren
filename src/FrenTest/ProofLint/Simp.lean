module

public import Lean

/-!
Linters for `@[simp]` lemmas, run over an imported environment.

The checks follow the `simpNF` and `simpComm` linters of Batteries
(`Batteries/Tactic/Lint/Simp.lean`, Apache 2.0, by Gabriel Ebner and others).
The code here is our own and smaller: Fren depends on neither Batteries nor
Mathlib.

`simpNF` reports a lemma when
- simp fails on its left-hand side (for example because the lemma loops);
- the default simp set rewrites its left-hand side without using the lemma
  itself, so the lemma never fires as written: either simp then also reaches
  the right-hand side (the lemma is redundant) or it reaches another term
  (the left-hand side is not in simp normal form);
- an unconditional lemma leaves its own left-hand side unchanged;
- its two sides are definitionally equal with reducible transparency, so
  rewriting with it changes nothing that simp can tell apart.

`simpLoop` reports a lemma whose right-hand side is its left-hand side with
the variables renamed, such as commutativity, and two lemmas that are each
other's inverse up to such a renaming.

Limits. Only lemmas in the default simp set of the imported environment are
seen: `local` and `scoped` attributes, other simp sets and `simp only`
arguments are not. The sides of a lemma are read from its statement (`=`, `↔`,
`¬`, `≠`, `∧` and plain propositions), not through simp's own preprocessing,
so a statement hidden behind a definition is read as a plain proposition. The
simp set is that of all the linted modules together, a superset of the one in
scope at any use. Lean's simp applies a permutation lemma only when the
result is smaller in a term order, so such a lemma does not literally loop;
it is reported because its effect depends on that order. Inverse pairs are
found only when the sides match exactly up to renaming, not up to instances.
-/

public section

namespace FrenTest.ProofLint
open Lean Meta

/-- A finding about a declaration: the linter's name, the declaration as its
author wrote it (a private name without its prefix) and the reason. -/
structure Finding where
  linter : String
  decl : Name
  message : String

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

private def pair (a b : Expr) : Expr := mkApp2 (mkConst `FrenTest.ProofLint.pair) a b

private def same (a b : Expr) : MetaM Bool :=
  withReducible <| withNewMCtxDepth <| isDefEq a b

private def show_ (e : Expr) : MetaM String := return toString (← ppExpr e)

private def usedNames (stats : Simp.Stats) : String :=
  ", ".intercalate (stats.usedTheorems.toArray.toList.map (toString <| privateToUserName ·.key))

/-- The `simpNF` reasons for one rewrite of `decl`. -/
private def normalForm (decl : Name) (xs : Array Expr) (lhs rhs : Expr) : MetaM (Array String) := do
  let mut found := #[]
  if ← same lhs rhs then
    found := found.push s!"the sides {← show_ lhs} and {← show_ rhs} are equal by reducible unfolding, so rewriting changes nothing"
  let ctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let simprocs := #[← Simp.getSimprocs]
  let attempt (side : String) (e : Expr) : MetaM (Except String (Simp.Result × Simp.Stats)) := do
    tryCatchRuntimeEx (do return .ok (← withCurrHeartbeats <| simp e ctx simprocs)) fun error => do
      return .error s!"simp fails on the {side}-hand side {← show_ e}: {← error.toMessageData.toString}"
  let (left, stats) ← match ← attempt "left" lhs with
    | .ok result => pure result
    | .error reason => return found.push reason
  if stats.usedTheorems.map.toList.any (·.1.key == decl) then return found
  let (right, _) ← match ← attempt "right" rhs with
    | .ok result => pure result
    | .error reason => return found.push reason
  if ← same left.expr right.expr then
    -- An unchanged left-hand side means the sides agree by unfolding alone,
    -- which the check above reports when the unfolding is reducible.
    if left.proof?.isSome || left.expr != lhs then
      found := found.push s!"simp proves this without the lemma, using {usedNames stats}"
  else if !(← same left.expr lhs) then
    found := found.push s!"the left-hand side {← show_ lhs} simplifies to {← show_ left.expr} using {usedNames stats}, so the lemma never fires as written"
  else
    let conditional ← xs.anyM fun x => do
      return (← isProp (← inferType x)) && !(occurring #[x] lhs).contains x
    if !conditional && lhs == left.expr then
      found := found.push s!"simp does not rewrite the left-hand side {← show_ lhs} with this lemma, so it never applies"
  return found

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

private def lint (modules : Array Name) : MetaM (Array Finding) := do
  let mut findings := #[]
  -- Each rewrite's shape, to find the pairs that undo each other.
  let mut rewrites : Array (Name × Expr × Expr) := #[]
  for decl in ← simpLemmas modules do
    let name := privateToUserName decl
    let (reasons, loops, shapes) ← forallTelescope (← getConstInfo decl).type fun xs body => do
      let mut reasons := #[]
      let mut loops := #[]
      let mut shapes := #[]
      for (lhs, rhs) in ← sides body do
        reasons := reasons ++ (← tryCatchRuntimeEx (normalForm decl xs lhs rhs) fun error => do
          return #[s!"the linter failed: {← error.toMessageData.toString}"])
        if lhs != rhs && shape xs lhs == shape xs rhs then
          loops := loops.push s!"the right-hand side {← show_ rhs} is the left-hand side {← show_ lhs} with its variables renamed"
        else
          shapes := shapes.push (shape xs (pair lhs rhs), shape xs (pair rhs lhs))
      return (reasons, loops, shapes)
    findings := findings ++ reasons.map ({ linter := "simpNF", decl := name, message := · })
    findings := findings ++ loops.map ({ linter := "simpLoop", decl := name, message := · })
    for (forward, backward) in shapes do
      for (other, otherForward, _) in rewrites do
        if otherForward == backward && other != name then
          findings := findings.push { linter := "simpLoop", decl := name, message := s!"undoes the simp lemma {other}" }
          findings := findings.push { linter := "simpLoop", decl := other, message := s!"undoes the simp lemma {name}" }
      rewrites := rewrites.push (name, forward, backward)
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
