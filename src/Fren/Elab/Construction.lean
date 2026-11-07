-- keep-sorted start
import Fren.Elab.ExpressionLints
-- keep-sorted end

/-! # Hosted elaboration: construction -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The Lean type of the Fren type `t`, the inverse of `coreTy?`, for the
type arguments of a construction. -/
partial def leanTypeOf (t : Core.Ty) : TermElabM Expr := do
  let s ← getState
  let set (e : Expr) := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) e
  match t with
  | .bool => return Lean.mkConst ``Bool
  | .int => return Lean.mkConst ``Int
  | .nat => return Lean.mkConst ``Nat
  | .string => return Lean.mkConst ``String
  | .set e => return set (← leanTypeOf e)
  | .rel a b => return set (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← leanTypeOf a) (← leanTypeOf b))
  | .seq e => return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← leanTypeOf e)
  | .enum p as =>
    let some e := s.enums.get? p | throwError "internal error: unknown enum `{p}`"
    return mkAppN e.const (e.leanArgs (← as.toArray.mapM leanTypeOf))
  | .record p as =>
    let some r := s.records.get? p | throwError "internal error: unknown record `{p}`"
    return mkAppN (Lean.mkConst r.decl) (← as.toArray.mapM leanTypeOf)
  | .abstract p => return Lean.mkConst (placeholderName p)
  | .newtype p _ =>
    let some n := s.newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    return Lean.mkConst n.decl
  | .param _ n => throwError "internal error: the type parameter `{n}` outside its declaration"

/-- A construction of a generic type (`Reqs/Lang/Generics#type-arguments`).
-/
structure Construction where
  /-- The generic type's path. -/
  path : Name
  params : Array Name
  /-- Its values' declared types, which mention the type parameters. -/
  declared : Array Core.Ty
  /-- Its values in their order: a record's fields in the order of its
  declaration, `none` for one that is not given. -/
  values : Array (Option Syntax)

open Lang in
/-- The construction of a generic enumeration or record that `e` is, if it
is one, as the `fren` command's `construction?` finds it. -/
def construction? (cx : ExprCtx) (e : Syntax) : TermElabM (Option Construction) := do
  let st ← getState
  let tys (params : Array Name) (ts : Array Expr) := ts.map fun t => (coreTyOf st t params).getD (.abstract .anonymous)
  let variant (p : Syntax) (vals : Array Syntax) : Option Construction := do
    let .ok (.variant en idx) := st.table.resolvePath cx.modName ((pathSegs p).map (·.getId)) cx.shadowing | none
    let info ← st.enums.get? en.path
    guard !info.params.isEmpty
    let ts ← info.payloads[idx]?
    return { path := en.path, params := info.params, declared := tys info.params ts, values := vals.map some }
  if e.isOfKind ``Lang.appExpr then return variant e[0] e[2].getSepArgs
  if e.getNumArgs == 1 && e[0].isOfKind ``Lang.fren_path then return variant e[0] #[]
  if e.isOfKind ``Lang.recordExpr then
    let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath cx.modName ((pathSegs e[0]).map (·.getId)) cx.shadowing
      | return none
    let some info := st.records.get? path | return none
    if info.params.isEmpty then return none
    let given := e[2].getSepArgs
    let vals ← info.fields.mapM fun (f, _) => do
      let some b := given.find? (·[0].getId == f) | return none
      if b[1].isNone then return some (← pathExpr b[0] b[0].getId) else return some b[1][1]
    return some { path, params := info.params, declared := tys info.params (info.fields.map (·.2)), values := vals }
  return none

open Lang in
/-- `e`'s shape, for whether it synthesizes a type (`Core.TypeShape`). -/
partial def typeShape (cx : ExprCtx) (e : Syntax) : TermElabM Core.TypeShape := do
  let go := typeShape cx
  if let some c ← construction? cx e then
    let shapes ← c.values.mapM fun v? => match v? with
      | some v => go v
      | none => pure .other
    return Core.constructionShape c.params c.declared shapes
  -- An application of a generic function (`Reqs/Lang/GenericFunctions#applications`).
  if e.isOfKind ``Lang.appExpr then
    let st ← getState
    if let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath cx.modName ((pathSegs e[0]).map (·.getId)) cx.shadowing then
      if let some d := (st.defined.get? path).filter (!·.typeParams.isEmpty) then
        return Core.callShape d.typeParams.size d.declared d.result (← e[2].getSepArgs.mapM go)
      -- One without a body, as the `fren` command has it.
      if let some a := (st.abstracts.get? path).filter (!·.typeParams.isEmpty) then
        return Core.callShape a.typeParams.size a.declared a.result (← e[2].getSepArgs.mapM go)
  if e.isOfKind ``Lang.setExpr || e.isOfKind ``Lang.seqExpr then
    let elems := e[1].getSepArgs
    if elems.isEmpty then return .emptyLiteral else return .anyPart (← elems.toList.mapM go)
  else if e.isOfKind ``Lang.pairExpr then return .pair (← go e[1]) (← go e[3])
  else if e.isOfKind ``Lang.unionExpr || e.isOfKind ``Lang.interExpr || e.isOfKind ``Lang.minusExpr then
    return .anyPart [← go e[0], ← go e[2]]
  else if isMatchLike e then return .anyPart (← (matchSourceArms e).toList.mapM (go ·[3]))
  else if e.isOfKind ``Lang.letExpr then return .anyPart [← go e[3]]
  else if e.isOfKind ``Lang.tableExpr then return .anyPart (← e[2].getSepArgs.toList.mapM (go ·[3]))
  else match e with
    | `(fren_expr| $a ++ $b) => return .anyPart [← go a, ← go b]
    | `(fren_expr| ($a)) => return .anyPart [← go a]
    | `(fren_expr| if $_ then $a else $b) => return .anyPart [← go a, ← go b]
    | _ => return .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← typeShape cx e).synthesizes

/-- Whether one of `es` synthesizes a type. -/
def anySynthesizes (cx : ExprCtx) (es : Array Syntax) : TermElabM Bool := es.anyM (synthesizes cx)

/-- Translates the values `vals` of the construction `c` of a generic type,
written `what` at `ref`, with `go`, which translates a value checked against
a type, if one is given, and returns their terms and the construction's
type arguments, which are inferred (`Core.inferConstruction`), as the
`fren` command's `elabConstruction` does, in the same order. `expected?` is
the type expected of the construction, and `note k t` explains that value
`k` has the type `t`. -/
def constructionTerms (go : Option Core.Ty → Syntax → TermElabM Term) (cx : ExprCtx) (expected? : Option Core.Ty)
    (ref : Syntax) (c : Construction) (vals : Array Syntax) (what : String) (note : Nat → Core.Ty → String) :
    TermElabM (Array Term × Array Core.Ty) := do
  let exp := match expected? with
    | some (.enum p as) | some (.record p as) => if p == c.path then some as.toArray else none
    | _ => none
  let synth ← vals.mapM (synthesizes cx)
  let run : StateT (Array Term) TermElabM (Array Core.Ty) :=
    Core.inferConstruction c.params c.declared synth exp
      (throwErrorAt ref (Core.cannotInferMsg what (Core.showPath c.path)).text : TermElabM Unit)
      (fun k x? => do
        let t ← (go x? vals[k]! : TermElabM Term)
        modify (·.set! k t)
        frenTypeOf? t)
      (fun k x f => (liftMsg vals[k]! (Core.checkType x f (some (note k x))) : TermElabM Unit))
  let (args, ts) ← run.run (vals.map fun _ => default)
  return (ts, args)

open Lang in
/-- `unnecessary_struct_initialization` on the record literal `e`, of the
type `ty`, with the fields `given`, where `go` translates expressions
(`lint::unnecessary_struct_initialization`). -/
def lintStructInit (go : Syntax → TermElabM Term) (ty : Core.Ty) (e : Syntax) (given : Array Syntax) :
    TermElabM Unit := do
  -- Each field's value as `r.f`, its own field `f` of `r`, with `r`'s text.
  let mut reads := #[]
  for b in given do
    if b[1].isNone then return
    let v := unparen b[1][1]
    let v := if v.getNumArgs == 1 then v[0] else v
    let f := b[0].getId
    if v.isOfKind ``Lang.fieldExpr && v[2].getId == f then
      reads := reads.push (v[0], srcText v[0])
    else if v.isOfKind ``Lang.fren_path && (pathSegs v).size == 1 then
      let id := (pathSegs v)[0]!
      unless !id.getId.isAtomic && id.getId.getString! == f.toString do return
      let t := srcText id
      let t := String.ofList (t.toList.take (t.length - f.toString.length - 1))
      reads := reads.push (← `(fren_expr| $(mkIdentFrom id id.getId.getPrefix):ident), t)
    else return
  let some (r, t) := reads[0]? | return
  let same := reads.all (Core.writtenSame ·.2 t)
  -- A value has a type; a call is not one.
  let saved ← saveState
  let ty? ← try some <$> typeOf (← go r) catch _ => pure none
  let core? ← ty?.bindM coreTy?
  saved.restore
  if Core.unnecessaryStructInit given.size true same ty?.isSome (core? == some ty) then
    let msg := Core.unnecessaryStructInitMsg t
    recordLint .unnecessaryStructInitialization e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)

open Lang in
/-- The precedence of `e`'s operator, as `lang::operand` uses it: an
expression in parentheses, or a field read, is an atom. -/
def exprPrec (e : Syntax) : Nat :=
  if (e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(") || e.isOfKind ``Lang.fieldExpr then Core.BKind.atom.prec
  else match boolNode "" 0 e with | .mk k .. => k.prec

open Lang in
/-- Where `e`, an operand of `p`, is, as `lang::operand` sees it; `none`
where any expression can be written. -/
def operandSlot (p e : Syntax) : Option Core.Slot :=
  let same (a : Syntax) := a.getPos? == e.getPos? && a.getTailPos? == e.getTailPos?
  let atom (i : Nat) := if p[i].isAtom then p[i].getAtomVal.trimAscii.toString else ""
  let at_ (k : Core.BKind) (idxs : Array Nat) := (idxs.findIdx? (same p[·])).bind (k.slots[·]?.join)
  if p.isOfKind ``Lang.fieldExpr || p.isOfKind ``Lang.methodExpr || p.isOfKind ``Lang.indexExpr then
    if same p[0] then some Core.receiverSlot else none
  else if isMatchLike p then
    if same p[1] then some Core.receiverSlot else none
  else if p.isOfKind ``Lang.isExpr then at_ .patternTest #[0]
  else if p.isOfKind ``Lang.quantExpr then at_ .quant #[3]
  -- A chained comparison's operands, not the comparisons within it.
  else if let some (xs, ops) := chainOf? p then (xs.findIdx? same).bind ((Core.BKind.chain (ops.map (·.getAtomVal.trimAscii.toString))).slots[·]?.join)
  else match p.getNumArgs, atom 0, atom 1 with
    | 3, "(", _ => none
    | 4, "when", _ => at_ (.when false) #[1, 3]
    | 4, "unless", _ => at_ (.when true) #[1, 3]
    | 2, "not", _ => at_ .not #[1]
    | 2, "-", _ => at_ .neg #[1]
    | 3, _, op => if op.isEmpty then none else at_ (.bin op) #[0, 2]
    | _, _, _ => none


end Fren
