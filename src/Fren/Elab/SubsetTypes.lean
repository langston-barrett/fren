-- keep-sorted start
import Fren.Elab.Construction
import Fren.Elab.Patterns
-- keep-sorted end

/-! # Hosted elaboration: subset types -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Subset types, and the items that declare types -/

/-- Records `undecidable` at `ref`, outside the decidable core, with `msg`. -/
def recordOutsideCore (ref : Syntax) (msg : Core.Msg) : TermElabM Unit := do
  modifyLocal fun l => { l with outsideCore := true }
  recordLint .undecidable ref msg

/-- The declared type `ty`, written in the module `modName`: its Lean type,
and the type with the invariants of the subset types within it
(`Reqs/Lang/Types#subset-types`), as the `fren` command's `elabPTy`. -/
partial def elabPType (modName : Name) (ty : Syntax) (params : Array Name := #[]) : TermElabM (Expr × Core.PTy) := do
  -- What Lean recovered from a parse error that it has reported.
  if ty.hasMissing then throwAbortTerm
  -- A function type is only a defined function's parameter's
  -- (`lang::function_type_place`).
  if let some w := Core.fnTypeWithin (typeSegs ty).toList then throwErrorAt ty (Core.fnTypePlaceMsg .constant w).text
  let text := Core.typeText (exactText ty)
  -- An element type, which is never a `Nat` (`lang::nat_place`), may be a
  -- type parameter (`lang::element_parameter`), and its
  -- constraint, if any, quantifies over the elements, outside the
  -- decidable core (`lang::subset_place`).
  let elem (e : Syntax) : TermElabM (Expr × Core.PTy) := do
    let (t, pt) ← elabPType modName e params
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
    if let .bvar k := t then
      unless Core.elementParamAccepted .datatype do throwErrorAt e (Core.typeParamPlaceMsg params[k]! .element "").text
    if let some n := t.constName?.bind (Core.typeParamName? ·) then
      unless Core.elementParamAccepted .function do
        throwErrorAt e (Core.typeParamPlaceMsg (Name.mkSimple n) .element "").text
    if (pt.cons (← getState).shapeOf).isSome then recordOutsideCore e Core.undecidableElementsMsg
    return (t, pt)
  if ty.isOfKind ``Lang.relType then
    let (a, pa) ← elem ty[2]
    let (b, pb) ← elem ty[4]
    return (mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) a b),
      { ty := .rel pa.ty pb.ty, elems := #[pa, pb], text })
  if ty.isOfKind ``Lang.seqType then
    let (a, pa) ← elem ty[2]
    return (mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) a, { ty := .seq pa.ty, elems := #[pa], text })
  if ty.isOfKind ``Lang.setType then
    let (a, pa) ← elem ty[2]
    return (mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) a, { ty := .set pa.ty, elems := #[pa], text })
  -- An instance of a generic type, `G<A, B>`, whose arguments are declared
  -- types, with their patterns, as the `fren` command's `elabBasePTy` checks
  -- them (`Reqs/Lang/Generics#type-parameters`).
  if ty.isOfKind ``Lang.instanceType then
    let segs := pathSegs ty[0]
    let given := ty[2].getSepArgs
    -- `Set`, `Seq` and `Rel` with too many or too few types, which the
    -- `fren` command's parser reports, at what follows the types it reads.
    if segs.size == 1 && [`Set, `Seq, `Rel].contains segs[0]!.getId then
      let n := if segs[0]!.getId == `Rel then 2 else 1
      let at_ := if given.size > n then ty[2].getArgs[2 * n - 1]! else ty[3]
      throwErrorAt at_ s!"expected `{if given.size > n then ">" else ","}`"
    let mut args := #[]
    let mut pts := #[]
    for a in given do
      let (t, pt) ← elabPType modName a params
      -- An argument is never `Nat` (`lang::nat_place`), and is a payload's
      -- type.
      unless !t.isConstOf ``Nat || Core.natPlaceAccepted .argument do throwErrorAt a (Core.natPlaceMsg .argument).text
      if let some (p, whole) ← abstractWithin? t then throwErrorAt a (Core.abstractFieldMsg p true !whole).text
      args := args.push t
      pts := pts.push pt
    let t ← instanceType modName segs args params ty
    let some ct ← coreTy? t params | throwErrorAt ty s!"internal error: a type without a Fren type"
    -- A recursive enumeration's type arguments bring no constraints
    -- (`Reqs/Lang/Generics#subset-types-as-type-arguments`).
    if let .enum p _ := ct then
      if ((← getState).shapeOf p).any (·.recursive) then
        for a in given, pt in pts do
          if (pt.cons (← getState).shapeOf).isSome then
            throwErrorAt a (Core.recursiveArgumentMsg pt.text (Core.showPath p)).text
    -- Nor do they within an instance, once its arguments stand for its
    -- parameters.
    if let some p := ct.dataPath? then
      if let some (a, q) := Core.recursiveArgumentWithin? (← getState).shapeOf p pts then
        throwErrorAt ty (Core.recursiveArgumentMsg a.text (Core.showPath q)).text
    return (t, { ty := ct, elems := pts, text })
  -- A path: an alias names a type, as declared.
  let t ← elabType modName ty params
  let segs := pathSegs (typePath? ty).get!
  if let .ok (.item { kind := .typeItem, path, .. }) := (← getState).table.resolvePath modName (← segNames segs) #[] then
    if let some (t, pt) := (← getState).aliases.get? path then return (t, { pt with text })
  let some ct ← coreTy? t params | throwErrorAt ty s!"internal error: a type without a Fren type"
  return (t, { Core.PTy.plain ct with text })

/-- That the term `x`, of the type `ty`, matches the pattern `p`, as a
pattern test is, and as the `fren` command's `patSmt` says. -/
partial def patTerm (ty : Core.Ty) (p : Core.Pat) (x : Term) : TermElabM Term := do
  match p with
  | .wild _ => `(True)
  | .bool b => if b then `(($x : Prop)) else `(¬($x : Prop))
  | .int lo hi =>
    let xi ← if ty == .nat then `(($x : Int)) else pure x
    if lo.isSome && lo == hi then return ← `($xi = $(← intTerm lo.get!))
    let parts := (← lo.toArray.mapM fun v => do `($(← intTerm v) ≤ $xi)) ++ (← hi.toArray.mapM fun v => do `($xi ≤ $(← intTerm v)))
    return (← conjTerm parts).getD (← `(True))
  | .str v => `($x = Fren.Str.lit $(quote v))
  | .ctor idx args =>
    let .enum ep targs := ty | `(True)
    let some info := (← getState).enums.get? ep | `(True)
    let ctor := info.ctor idx
    -- With an instance's arguments for its type parameters.
    let tys := (info.shape.inst (targs.toArray.map .plain)).parts[idx]?.getD #[]
    let sels ← (Array.range (info.payloads[idx]!.size)).mapM fun k => `($(mkCIdent (info.sel idx k)) $x)
    let mut tests := #[← `($x = $(mkCIdent ctor) $sels*)]
    for a in args, k in [0:args.size] do
      unless a matches .wild _ do
        tests := tests.push (← patTerm (tys[k]?.map (·.ty) |>.getD .int) a sels[k]!)
    return (← conjTerm tests).get!
  | .or alts =>
    if alts.any (· matches .wild _) then return ← `(True)
    let ts ← alts.mapM (patTerm ty · x)
    let some last := ts.back? | `(True)
    ts.pop.foldrM (init := last) fun t acc => `($t ∨ $acc)

/-- The constraint `c` of the term `x` (`Core.Cons`), as the `fren`
command's `consSmt` says, where `depth` numbers the bound variables of the
quantifiers around it. `natAsInt` is true at the root of a Nat-valued
uninterpreted function's facts, where the solver represents it by Int. -/
partial def consTerm (c : Core.Cons) (x : Term) (depth : Nat := 0) (natAsInt : Bool := false) : TermElabM Term := do
  let st ← getState
  match c with
  | .predicate i =>
    let some f := st.defined.get? i.predicate | throwError "internal error: unknown subset predicate"
    -- A Nat result is represented by Int in uninterpreted-function facts.
    -- Its nonnegativity is a separate base fact; evaluate the invariant
    -- on the corresponding Nat value while retaining that base fact.
    -- Do not elaborate `x` here: a collection's binder is syntax whose
    -- quantifier has not been elaborated yet. Projections and collection
    -- members already have their declared Lean types.
    let x ← if natAsInt && (f.ptys.1[0]?).any (·.ty == .nat) then `(Int.toNat $x)
      else pure x
    `(@$(mkCIdent f.decl) $(f.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $x)
  | .pat ty p => patTerm ty p x
  | .atLeast0 => `(0 ≤ $x)
  | .fields path _ cs =>
    let some r := st.records.get? path | `(True)
    let ts ← cs.mapM fun (k, c) => do consTerm c (← `($(mkCIdent (r.decl ++ r.fields[k]!.1)) $x)) depth
    return (← conjTerm ts).getD (← `(True))
  | .newtype path c =>
    let some n := st.newtypes.get? path | `(True)
    consTerm c (← `($(mkCIdent n.field) $x)) depth
  | .payloads path _ cs =>
    let some info := st.enums.get? path | `(True)
    let ts ← cs.mapM fun (v, k, c) => do
      let ctor := info.ctor v
      let sels ← (Array.range (info.payloads[v]!.size)).mapM fun j => `($(mkCIdent (info.sel v j)) $x)
      `($x = $(mkCIdent ctor) $sels* → $(← consTerm c sels[k]! depth))
    return (← conjTerm ts).getD (← `(True))
  | .elems seq _ c =>
    let b := mkIdent (Name.mkSimple s!"fren_e{depth}")
    if seq then
      `(∀ $b:ident : Int, 0 ≤ $b ∧ $b < Fren.Seq.len $x → $(← consTerm c (← `(Fren.Seq.nth $x $b)) (depth + 1)))
    else `(∀ $b:ident, $b ∈ $x → $(← consTerm c b (depth + 1)))
  | .pairs _ _ ca cb =>
    let (u, v) := (mkIdent (Name.mkSimple s!"fren_a{depth}"), mkIdent (Name.mkSimple s!"fren_b{depth}"))
    let parts := (← ca.toArray.mapM (consTerm · u (depth + 1))) ++ (← cb.toArray.mapM (consTerm · v (depth + 1)))
    `(Fren.relationObligation (∀ $u:ident $v:ident, ($u, $v) ∈ $x → $((← conjTerm parts).getD (← `(True)))))
  | .all cs =>
    let ts ← cs.mapM (consTerm · x depth natAsInt)
    return (← conjTerm ts).getD (← `(True))

/-- The constraint `c` of a value of the Lean type `ty`, as a predicate:
`fun x => c x`. -/
def predOf (ty : Expr) (c : Core.Cons) : TermElabM Expr :=
  withLocalDeclD `fren_x ty fun x => do
    let p ← elabProp (← consTerm c (mkIdent `fren_x) (natAsInt := ty.isConstOf ``Int))
    mkLambdaFVars #[x] p

/-- The constraint `c` of a value of the Lean type `ty`, which mentions the
type parameters `params` of a generic type as loose bound variables, as a
predicate over the arguments of a selector of the type, `{T : Type}`,
`[Inhabited T]` and the value: `fun T inst x => c x`. -/
def genericPredOf (params : Array Name) (ty : Expr) (c : Core.Cons) : TermElabM Expr := do
  if params.isEmpty then return ← predOf ty c
  let rec go (k : Nat) (ts : Array Expr) : TermElabM Expr := do
    if h : k < params.size then
      withLocalDecl params[k] .implicit (mkSort Level.one) fun t => go (k + 1) (ts.push t)
    else
      let insts := ts.mapIdx fun i t => (Name.mkSimple s!"inst{i}", mkApp (mkConst ``Inhabited [Level.one]) t)
      withLocalDeclsDND insts fun is =>
        withLocalDeclD `fren_x (ty.instantiate ts) fun x => do
          let p ← elabProp (← consTerm c (mkIdent `fren_x))
          mkLambdaFVars (ts ++ is ++ #[x]) p
  termination_by params.size - k
  go 0 #[]

/-- The constraint that a value of the declared type `pt`, of the Lean
type `ty`, brings, as a predicate (`Core.PTy.cons`). -/
def factPred? (ty : Expr) (pt : Core.PTy) (nat : Bool := false) : TermElabM (Option Expr) := do
  let some c := pt.cons (← getState).shapeOf nat | return none
  some <$> predOf ty c

/-- What the checks need of the elaborator (`ElabHooks`): for the instances
of generic functions without a body, the Lean types of their signatures,
and the constraints of their result types (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`). -/
def elabHooks : ElabHooks where
  leanType t := (leanTypeOf t).run'
  fact pt nat := (do
    if (pt.cons (← getState).shapeOf).isNone then return none
    let nat := nat && pt.ty == Core.Ty.nat
    let ty ← if nat then pure (Lean.mkConst ``Int) else leanTypeOf pt.ty
    factPred? ty pt nat).run'
  coreTy e := return coreTyOf (← getState) e

/-- The declared type of the variable, parameter or function `name`,
written `ty?`, which is `Bool` if it is not written: its Lean type, and the
type with its patterns, as `varType` checks it. -/
def varPType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM (Expr × Core.PTy) := do
  let n := name.getId
  let t ← ty?.mapM (elabPType modName)
  if let some ty := ty? then lintRelTypes modName ty
  unless Core.generatedName (Core.nameText n) do liftMsg name (Core.checkVarName n (t.map (·.1.isConstOf ``Bool)))
  if let (some ty, some (t, pt)) := (ty?, t) then
    if pt.invariants.isEmpty && !Core.generatedName (Core.nameText n) then lintBoolType n ty t
  return t.getD (Lean.mkConst ``Bool, .plain .bool)

/-- The declared type of the `k`th field or payload value of the variant
`v` of a record, newtype or enumeration whose parts are `shape`'s, with the
type arguments `args` for its type parameters, if it is generic, as the
`fren` command's `partPTy` has it (`Core.PTy.subst`). -/
def partPType (shape : Core.DataShape) (v k : Nat) (args : Array Core.Ty := #[]) : Core.PTy :=
  let t := (shape.parts[v]?.bind (·[k]?)).getD default
  if args.isEmpty then t else t.subst (args.map .plain)

/-- Records the obligation of the value `x`, given at `ref` where the type
`t` is declared, if it has one, for the subset-type check
(`Reqs/Check#subset-types`): its guard implies that the value matches,
marked with its type (`Fren.typeObligation`). -/
def noteObligation (cx : ExprCtx) (place : Core.ValuePlace) (ref : Syntax) (t : Core.PTy) (x : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some o := Core.siteObligation place (t.obligation (← getState).shapeOf) | return
  let parts := o.namedParts
  let parts := if parts.isEmpty then #[(.anonymous, o)] else parts
  for (name, part) in parts do
    let label := if name.isAnonymous then t.text else "@invariant:" ++ Core.showPath name
    let goal ← `(Fren.typeObligation $(quote label) $(← consTerm part x))
    let goal ← cx.guards.foldrM (fun g acc => `($g → $acc)) goal
    modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- The Lean type of a field or payload, `ty`, of the type `ownName`, with
the type parameters `params`, being declared in the module `modName` as the
Lean type `own`, and its type as declared, checking that it is accepted
(`lang::field_type`, `lang::type_parameter_place`), in the order of the
`fren` command's checks. -/
def fieldType (modName : Name) (ty : Syntax) (own : Name) (place : FieldPlace) (ownName : Name)
    (params : Array Name := #[]) : CommandElabM (Expr × Core.PTy) := do
  let path := modName ++ ownName
  checkFnTypeSite (if place == .payload then .payload else .field) ty
  let segs := typeSegs ty
  let (whole, inSet) := Core.ownIn segs ownName.toString
  let (isOwn, declared, nested) := Core.ownArgs segs ownName.toString (params.map toString)
  match place with
  | .payload =>
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
    -- A recursive payload is the enumeration with its own parameters.
    let place := Core.recursivePlace declared nested
    if (isOwn || nested) && !Core.typeParamPlaceAccepted place then
      throwErrorAt ty (Core.typeParamPlaceMsg .anonymous place (Core.ownWritten path params) !params.isEmpty).text
    if isOwn then
      return (mkAppN (Lean.mkConst own) ((Array.range params.size).map (.bvar ·)),
        .plain (.enum path (params.toList.zipIdx.map fun (p, k) => .param k p)))
  | .field =>
    if isOwn || nested then throwErrorAt ty (Core.recursiveRecordMsg ownName).text
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
  | .newtype =>
    if whole then throwErrorAt ty (Core.recursiveRecordMsg ownName).text
    if inSet then throwErrorAt ty (Core.recursiveSetMsg path).text
  let payload := place == .payload
  let (t, pt) ← liftTermElabM (elabPType modName ty params)
  lintRelTypes modName ty params
  if let some (p, whole) ← abstractWithin? t then
    unless Core.fieldTypeAccepted true false false payload do
      throwErrorAt ty (Core.abstractFieldMsg p payload !whole).text
  return (t, pt)

/-- The type parameters `params` of the enumeration or record being
declared in the module `modName`, checked as the `fren` command checks
them: distinct (`lang::distinct_names`), without `!`, and without the name
of a built-in type or of an item in scope (`Reqs/Lang/Generics`). -/
def elabTypeParams (modName : Name) (params : Array Syntax) : CommandElabM (Array Name) := do
  for p in params do discard (segName p)
  let ns := params.map (·.getId)
  if let some k := (Core.repeatsAt ns)[0]? then throwErrorAt params[k]! (Core.dupTypeParamMsg ns[k]!).text
  for p in params, n in ns do
    liftMsg p (Core.checkNoBang n)
    if [`Bool, `Int, `Nat, `String, `Set, `Seq, `Rel].contains n then
      throwErrorAt p (Core.typeParamNameMsg n s!"the built-in type `{n}`").text
    if let .ok r := (← getState).table.resolvePath modName #[n] #[] then
      throwErrorAt p (Core.typeParamNameMsg n r.describe).text
  return ns

/-- The binders of the type parameters `params` of a generic type's
declaration, `(T : Type)`, or implicit, `{T : Type}`, followed by an
`Inhabited` instance of each, `[Inhabited T]`. -/
def paramBinders (params : Array Name) (implicit : Bool) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  if !implicit then
    return ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent p) : Type))
  let types ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| {$(mkIdent p) : Type})
  let insts ← params.mapM fun p => `(Lean.Parser.Term.bracketedBinderF| [Inhabited $(mkIdent p)])
  return types ++ insts

/-- The Lean type `decl`, applied to the type parameters `params`. -/
def selfType (decl : Name) (params : Array Name) : CommandElabM Term :=
  if params.isEmpty then pure (mkCIdent decl) else `(($(mkCIdent decl) $(params.map fun p => (mkIdent p : Term))*))


end Fren
