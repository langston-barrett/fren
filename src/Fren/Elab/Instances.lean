-- keep-sorted start
import Fren.Elab.Terms
-- keep-sorted end

/-! # Hosted elaboration: instances -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A call whose procedure has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Name
  ref : Syntax
  comp : CompInfo
  /-- `fren_binding`s. -/
  bindings : Array Syntax
  /-- Where its variables start among the calling procedure's. -/
  offset : Nat
  /-- A call's arguments, each bound to the parameter in its position,
  rather than bindings written by name. -/
  positional : Bool := false

/-- Resolves the call `call x := p(args)`: the called procedure, the
call's variables, and its bindings, each argument bound to the parameter
in its position (`F0408`, `F0409`). -/
def resolveInst (modName : Name) (x p : Syntax) (bs : Array Syntax) (offset : Nat) :
    TermElabM (PendingInst × Array Var) := do
  liftMsg x (Core.checkItemName "call" x.getId)
  let r ← resolvePath modName (pathSegs p)
  let .item { kind := .compItem, path, .. } := r | throwErrorAt p (Core.notACompMsg r).text
  let some c := (← getState).comps.get? path | throwError "internal error: unknown comp `{path}`"
  unless c.decidable do
    modifyLocal fun l => { l with outsideCore := true }
    recordLint .undecidable p (Core.undecidableInstMsg path)
  noteCounts c p
  let params := c.vars.filter (fun v => v.role == .input && v.name.isAtomic) |>.map (·.name)
  let callee := Core.showPath path
  let some bound := Core.callBindings (params.map Core.nameText) bs
    | let ref := if bs.size > params.size then mkNullNode (bs.extract params.size bs.size) else p
      throwErrorAt ref (Core.callArityMsg callee (params.map Core.nameText) bs.size).text
  -- Each argument, bound to its parameter, at the argument.
  let bs := (params.zip bound).map fun (n, (_, a)) =>
    mkNode ``Lang.fren_binding #[mkIdentFrom a n, mkNullNode #[mkAtom ":=", a]]
  let w := x.getId
  -- An input's constraint is the call's obligation, which the call
  -- check asks, rather than a fact (`Reqs/Check#call-assumptions`).
  let vars := c.vars.map fun v =>
    let role := Core.Role.ofInst v.role v.isPub
    { name := w ++ v.name, role, isPub := role == .instOutput, type := v.type, ref := x, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact? : Var }
  return ({ name := w, ref := x, comp := c, bindings := bs, offset, positional := true }, vars)

/-- The obligations of the inputs of `c`, whose variables are `slice`, an
call's among `fvs`, whose types have one: each named after its input,
with its type, as written, and closed over `fvs`
(`Reqs/Check#call-assumptions`). -/
def typedObligations (c : CompInfo) (slice fvs : Array Expr) : TermElabM (Array (Name × String × Expr)) := do
  let mut out := #[]
  for (v, x) in c.vars.zip slice do
    unless v.role == .input do continue
    let some o := v.ptype.obligation (← getState).shapeOf | continue
    let parts := o.namedParts
    let parts := if parts.isEmpty then #[(.anonymous, o)] else parts
    for (name, part) in parts, k in [0:parts.size] do
      let label := if name.isAnonymous then v.ptype.text else "@invariant:" ++ Core.showPath name
      let p ← predOf v.type part
      out := out.push (Name.num v.name k, label, ← mkLambdaFVars fvs (p.beta #[x]))
  return out

open Lang in
/-- The equations made by the bindings of a call, over the procedure's
variables `fvs`. -/
def elabBindings (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) : TermElabM Expr := do
  let mut eqs := #[]
  for b in pi.bindings do
    let x := b[0]
    let some idx := cx.vars.findIdx? (·.name == pi.name ++ x.getId)
      | throwError "internal error: no variable for `{x.getId}`"
    let natOk := cx.vars[idx]!.type.isConstOf ``Nat
    let t ← if b[1].isNone then toTerm cx (← `(fren_expr| $(⟨x⟩):ident)) else toTerm { cx with emptyOk := Core.ExprSite.binding.checked false false, natOk, expected? := Core.ExprSite.binding.expected (← coreTy? cx.vars[idx]!.type) none } b[1][1]
    checkDeclared (if b[1].isNone then x else b[1][1]) t cx.vars[idx]!.type fun ty =>
      s!"note: `{x.getId}` of `{Core.showPath pi.comp.path}` has type `{ty}`"
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if cx.vars[idx]!.type.isConstOf ``Int && (← frenTypeOf? t) == some .int then
      modifyLocal fun l => { l with natKept := l.natKept.push (pi.comp.path, Core.nameText x.getId) }
    unless b[1].isNone do lintBools b[1][1] (← hidesIn cx)
    unless pi.positional do lintRedundant b false
    let fv := fvs[idx]!
    eqs := eqs.push (← mkEq fv (← elabProp t (← inferType fv)))
  return mkAndN eqs.toList

/-- Elaborates a call, and the body over `fvs` of the definition `decl`
generated for it. -/
def elabInst (cx : ExprCtx) (fvs : Array Expr) (pi : PendingInst) (decl : Name) : TermElabM (InstInfo × Expr) := do
  let bindings ← elabBindings cx fvs pi
  let slice := fvs.extract pi.offset (pi.offset + pi.comp.vars.size)
  let behaviour := pi.comp.meaning slice
  let typed ← typedObligations pi.comp slice fvs
  -- A call's own meaning is not a hypothesis of its precondition check.
  -- Inline its local definitions into those obligations instead.
  let mut defined := slice
  for (name, value) in pi.comp.defs do
    if let some k := pi.comp.vars.findIdx? (·.name == name) then
      defined := defined.set! k (value.beta defined)
  return (·, mkAnd bindings (pi.comp.meaningDecl slice)) {
    name := pi.name, comp := pi.comp.path, ref := pi.ref, decl
    bindings := ← mkLambdaFVars fvs bindings
    behaviour := ← mkLambdaFVars fvs behaviour
    assumes := typed.map (fun (n, _, f) => (n, f))
      ++ (← pi.comp.assumes.mapM fun a => return (a.name, ← mkLambdaFVars fvs (a.body.beta defined)))
    typed := typed.map fun (n, t, _) => (n, t) }


end Fren
