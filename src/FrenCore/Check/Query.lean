-- keep-sorted start
import FrenCore.Check.Backend
import FrenCore.Check.Component
-- keep-sorted end

/-!
# Query minimization, model rendering and forcing

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- A subset of `cands` that, with `base`, still entails `goal`: minimal if
the solver decides every query (deletion-based, so the result depends only
on which queries are `unsat`).
Assumes `base ++ cands` entails it. -/
def minimize (base cands : Array (Name × F)) (goal : F) : m (Array Name) := do
  let mut keep := cands
  for (n, _) in cands do
    let trial := keep.filter (·.1 != n)
    if (← b.query (base ++ trial) goal false).isUnsat then
      keep := trial
  return keep.map (·.1)

/-- Whether `hyps` force the variable `x` to `v`, its value in a model of
them: `x = v` follows from them (`check::forcing`). A value that cannot be
pinned is not known to be forced. -/
def forces (hyps : Array (Name × F)) (x : Name) (v : V) : m Bool := do
  let some f ← b.pin x v | return false
  return (← b.query hyps f false).isUnsat

/-- Whether `hyps` force the variable `x` to `v`'s variant, where `v` is
its value in a model of them: that `x` is of that variant follows from
them (`check::forcing`). A variant that cannot be pinned is not known to
be forced. -/
def forcesVariant (hyps : Array (Name × F)) (x : Name) (v : V) : m Bool := do
  let some (_, f) ← b.pinVariant x v | return false
  return (← b.query hyps f false).isUnsat

/-- What `hyps` force the variable `x` to, where `v` is its value in a model
of them and `k?` the variant of `v`: the value `v`, rendered as `s`, if it
is forced (`forces`); else its variant, if that is forced
(`forcesVariant`); else nothing (`check::forcing`). -/
def forcedOf (hyps : Array (Name × F)) (x : Name) (v : V) (s : String) (k? : Option Variant) : m (Option Forced) := do
  if ← forces b hyps x v then return some (.value s)
  let some k := k? | return none
  if ← forcesVariant b hyps x v then return some (.variant k)
  return none

/-- The clash at the guarantee `e` of the core `core`, under the fixed
hypotheses `pinned`: the first of the outputs `outs` that `{e}` and the
rest of the core force to different values, or to values of different
variants (`check::clash_notes`). Each side is asked for a model, then
whether each output's value in it follows (`forces`); only the outputs
whose values in the two models differ are asked about, since sides that
force an output both force its value in their models. Where the two
values have the same variant, or either has none, only a clash of whole
values is looked for; where their variants differ, each side forces the
output's whole value or, failing that, its variant (`forcedOf`), so a
clash of whole values is preferred to one of variants. None if the rest
is empty, which forces nothing, or a side has no model. -/
def clashAt (pinned core : Array (Name × F)) (outs : Array Name) (e : Name) : m (Option Clash) := do
  let one := core.filter (·.1 == e)
  let rest := core.filter (·.1 != e)
  if rest.isEmpty then return none
  let .sat m₁ ← b.query (pinned ++ one) b.falseF true | return none
  let .sat m₂ ← b.query (pinned ++ rest) b.falseF true | return none
  for o in outs do
    let some (_, v₁) := m₁.find? (·.1 == o) | continue
    let some (_, v₂) := m₂.find? (·.1 == o) | continue
    let s₁ ← b.render o v₁
    let s₂ ← b.render o v₂
    if s₁ == s₂ then continue
    let k₁ := (← b.pinVariant o v₁).map (·.1)
    let k₂ := (← b.pinVariant o v₂).map (·.1)
    -- Of the same variant, or of none: only whole values can clash.
    let variants := k₁.isSome && k₂.isSome && k₁ != k₂
    let some f₁ ← forcedOf b (pinned ++ one) o v₁ s₁ (if variants then k₁ else none) | continue
    let some f₂ ← forcedOf b (pinned ++ rest) o v₂ s₂ (if variants then k₂ else none) | continue
    return some { guarantee := e, rest := rest.map (·.1), output := o, forced := f₁, restForced := f₂ }
  return none

/-- Whether `found` notes leave room for another under the budget
`examples`, `none` for no limit (`check::clash_notes`). -/
def withinBudget (found : Nat) : Option Nat → Bool
  | none => true
  | some n => found < n

/-- The clashes under fixed hypotheses `pinned`, one at most at each
guarantee of `core`, in its order, and at most `examples` in all
(`check::clash_notes`): no query is asked once they are found. -/
def clashesOf (pinned core : Array (Name × F)) (outs : Array Name) (examples : Option Nat) : m (Array Clash) := do
  let mut found := #[]
  for (e, _) in core do
    if !withinBudget found.size examples then break
    if let some cl ← clashAt b pinned core outs e then found := found.push cl
  return found

def renderModel (vars : Array VarSig) (model : Array (Name × V)) (keep : VarSig → Bool) :
    m Assignment :=
  vars.filterMapM fun v => do
    if !keep v then return none
    let some (_, val) := model.find? (·.1 == v.name) | return none
    return some (v.name, ← b.render v.name val)

/-- The verdict `verdict` and the detail `d`, which reports `vals`, the
values that `model` of the query of `hyps` and `goal` gives, unless Fren's
semantics at those values contradicts the solver (`model::report`): then the
check is inconclusive, and its detail says what the values contradict. -/
def confirmReport (hyps : Array (Name × F)) (goal : F) (model : Array (Name × V)) (vals : Assignment)
    (verdict : Verdict) (d : Detail) : m (Verdict × Detail) := do
  let some confirm := b.confirm? | return (verdict, d)
  match ← confirm hyps goal model with
  | some how => return (.inconclusive, .refuted how vals)
  | none => return (verdict, d)

/-- The variables of `model` that are universally quantified, and not also
outputs, for a realizability conflict. -/
def conflictInput (vars : Array VarSig) (model : Array (Name × V)) : Array (Name × V) :=
  model.filter fun (n, _) =>
    vars.any (fun v => v.name == n && v.isIn) && !vars.any fun v => v.name == n && v.role == .output

/-- `x = v` for each `x` and value `v` of `input` that can be pinned. -/
def pins (input : Array (Name × V)) : m (Array (Name × F)) :=
  input.filterMapM fun (n, v) => do
    return (← b.pin n v).map (n.appendAfter "_value", ·)

/-- The value of `n` in `model`, rendered as a value of `x`. -/
def modelValue (x : Name) (model : Array (Name × V)) (n : Name) : m String := do
  let some (_, val) := model.find? (·.1 == n) | return "?"
  b.render x val

end Fren.Core
