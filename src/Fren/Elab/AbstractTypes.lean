-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: abstract types -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Abstract types and functions -/

/-- Records the questions about the tables and applications of the body
and contract of the function at `path`, whose parameters are `vars`, or of
the value of the constant at `path`, `tables`, with its preconditions and
postconditions, `props`, as a procedure for their checks (`Entry.bodyInfo`), if
it has any questions or postconditions to check (`Core.bodyKinds`). -/
def recordBody (path : Name) (ref : Syntax) (decl : Name) (vars : Array Var)
    (tables : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr)) (props : Array PropInfo := #[])
    (fn? : Option Name := none) : TermElabM Unit := do
  if tables.isEmpty && !props.any (·.kind == .ensure) then return
  let uses ← usesOf (vars.filterMap (·.fact?) ++ tables.map (·.2.2.2.2) ++ props.map (·.body))
  let info : CompInfo := { path := path.getPrefix, vars, props, ref, decl, uses, fn?
                           decidable := !(← getLocal).outsideCore, guarded := (← getLocal).guardedUsed
                           indexes := tables }
  record (.bodyInfo path info)
  modifyLocal fun l => { l with bodies := l.bodies.push path }.declared path

/-- Declares the placeholder for the abstract type or function at `path`
(`AbstractInfo`). -/
def declarePlaceholder (path : Name) (type : Expr) (isType : Bool) (ptys : Array Core.PTy × Core.PTy := (#[], default))
    (fact? : Option Expr := none) (typeParams : Array Name := #[]) (declared : Array Core.Ty := #[])
    (result : Core.Ty := .bool) (resultP : Core.PTy := default) : TermElabM Unit := do
  let placeholder := placeholderName path
  addDecl (.axiomDecl { name := placeholder, levelParams := [], type, isUnsafe := false })
  let s ← getState
  let deps := type.foldConsts #[] fun c acc => if s.placeholders.contains c && !acc.contains c then acc.push c else acc
  record (.abstractInfo { path, placeholder, isType, deps, ptys, fact?, typeParams, declared, result, resultP
                          module := ← getMainModule })
  -- An abstract type has a value, so its placeholder has an `Inhabited`
  -- instance, itself a placeholder, which an index of a sequence of it
  -- needs; an implementation gives the interpretation's own.
  if isType then
    let inst := inhabitedName placeholder
    let instType := mkApp (Lean.mkConst ``Inhabited [Level.one]) (Lean.mkConst placeholder)
    addDecl (.axiomDecl { name := inst, levelParams := [], type := instType, isUnsafe := false })
    addInstance inst .global 1000
    record (.abstractInfo { path := inhabitedName path, placeholder := inst, isType := false, deps := #[placeholder] })

/-- `t`, over the placeholders of the type parameters `tps` of the generic
function at `path` and of their `Inhabited` instances, as a type that takes
a `Type` and an instance of it for each, first (`typeParamPlaceholders`):
the type of the placeholder of a generic function without a body
(`Reqs/Generated#generic-functions`). -/
def withTypeParams (path : Name) (tps : Array Name) (t : Expr) : TermElabM Expr :=
  go 0 #[]
where
  go (k : Nat) (xs : Array Expr) : TermElabM Expr := do
    if h : k < tps.size then
      withLocalDeclD (Name.mkSimple tps[k].toString) (mkSort Level.one) fun x =>
        withLocalDecl (Name.mkSimple "#inhabited") .instImplicit (mkApp (Lean.mkConst ``Inhabited [Level.one]) x) fun i =>
          go (k + 1) (xs ++ #[x, i])
    else mkForallFVars xs (atInstance path tps xs t)

@[command_elab Lang.typeCmd] def elabAbstractType : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  -- A type alias names a type (`Reqs/Lang/Items#type-aliases`).
  unless stx[3].isNone do
    let n ← checkItemName "type alias" nameStx
    checkFresh modName n nameStx
    lintName .typeAlias n nameStx
    let (t, pt) ← liftTermElabM (elabPType modName stx[3][1])
    lintRelTypes modName stx[3][1]
    record (.item { item := { kind := .typeItem, path := modName ++ n, isPub, owner := modName }, ref := nameStx })
    record (.aliasInfo (modName ++ n) t pt)
    unless isPub do recordItem .typeAlias (modName ++ n) nameStx
    return
  let n ← checkItemName "abstract type" nameStx
  checkFresh modName n nameStx
  lintName .abstractType n nameStx
  let path := modName ++ n
  liftTermElabM <| declarePlaceholder path (mkSort (.succ .zero)) true
  record (.item { item := { kind := .typeItem, path, isPub, owner := modName }, ref := nameStx })
  unless isPub do recordItem .abstractType path nameStx


end Fren
