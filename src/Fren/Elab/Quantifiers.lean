-- keep-sorted start
import Fren.Elab.Definitions
import Fren.Elab.Sets
-- keep-sorted end

/-! # Hosted elaboration: quantifiers -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The operand `a` of the arithmetic operator `op`, an `Int` or a `Nat`, of
which a `Nat` is expected if `natOk`, as the `fren` command checks it
(`lang::operator_type`). -/
def numberOperand (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (op : String) (natOk : Bool)
    (a : Syntax) : TermElabM Term := do
  let x ← toTerm { cx with natOk } a
  checkNumberTerm a x op
  return x

/-- The operand `a` of the logical operator `op`, a `Bool`, as the `fren`
command checks it (`lang::operator_type`). -/
def boolOperand (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (op : String) (a : Syntax) :
    TermElabM Term := do
  let x ← toTerm cx a
  checkTermType a x .bool (Core.opNote op .bool)
  return ← propositionTerm x

/-- Whether the quantifier `e` is a `forall`, rather than an `exists`. -/
def isForall (e : Syntax) : Bool :=
  let kw := if e[0].isAtom then e[0] else e[0][0]
  kw.getAtomVal.trimAscii.toString == "forall"

/-- The number of values of `ty`, if a quantifier ranges over it
(`lang::quantified_type`), counted without listing them. An unbounded
enumeration or record is recursive or has a part that a quantifier does
not range over, so it is not looked into, and the recursion ends. -/
def valueCount? (ty : Expr) : MetaM (Option Nat) := do
  -- As the `fren` command counts them, by an instance's arguments too
  -- (`lang::instance_values`).
  let s ← getState
  let some t := coreTyOf s (← instantiateMVars ty) | return none
  return t.valueCount (dataSig s)

/-- The Lean type of a quantifier's binder's type `ty`, which must not be a
procedure. -/
def binderType (modName : Name) (ty : Syntax) : TermElabM (Expr × Core.PTy) := do
  if let some p := (typePath? ty).filter fun _ => !hasFnType ty then
    if let .ok (.item { kind := .compItem, path, .. }) := (← getState).table.resolvePath modName (← segNames (pathSegs p)) #[] then
      throwErrorAt ty (Core.quantifiedComponentMsg (Core.showPath path)).text
  elabPType modName ty

/-- The value `v` of the Lean type `ty`, as a term (`Core.PVal`). -/
partial def valueTerm (ty : Expr) (v : Core.PVal) : TermElabM Term := do
  let s ← getState
  match v with
  | .bool b => if b then `(true) else `(false)
  | .int i => if ty.isConstOf ``Nat then `(($(Syntax.mkNumLit (toString i.toNat)) : Nat)) else intTerm i
  | .ctor idx args =>
    let some d := ty.getAppFn.constName? | `(sorry)
    -- With an instance's arguments for its type parameters.
    let targs := ty.getAppArgs
    let (c, ts) :=
      if let some e := s.enumOfDecl? d then (e.ctor idx, (e.payloadsAt targs)[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then (r.ctor, (r.fieldsAt targs).map (·.2))
      else if let some n := s.newtypeOfDecl? d then (n.ctor, #[n.under])
      else (.anonymous, #[])
    let as ← (args.zip ts).mapM fun (w, t) => valueTerm t w
    `($(mkCIdent c) $as*)

/-- The values of the declared type `pt`, of the Lean type `ty`, as terms,
and how many there are, if a quantifier ranges over it, as the `fren`
command's `binderValues`. -/
def binderValues (ty : Expr) (pt : Core.PTy) : TermElabM (Option (Nat × Array Term)) := do
  let st ← getState
  -- Only a listed type's values are listed (`lang::quantified_type`).
  unless (factsOf st pt).listed do return none
  if (pt.cons st.shapeOf).isNone then
    let some n ← valueCount? ty | return none
    return some (n, ← ((← valuesOf? ty Core.maxInstances).getD #[]).mapM exprToSyntax)
  let some n := pt.count? st.shapeOf | return none
  if n > Core.maxInstances then return some (n, #[])
  let vs := (pt.values st.shapeOf Core.maxInstances).getD #[]
  return some (n, ← vs.mapM (valueTerm ty))

/-- Whether `e` names `n` anywhere within it: as a path of one segment
whose root is `n`, or a field of a record literal or update written
without `:=`; not as an applied function, a record's type, or within a
type or pattern. A name is compared as written, whatever shadows it, as
the `fren` command's `Expr.names` does. -/
partial def namesBound (n : Name) (e : Syntax) : Bool :=
  if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    segs.size == 1 && segs[0]!.getId.getRoot == n
  else if e.isOfKind ``Lang.fren_binding then
    (e[1].isNone && e[0].getId == n) || namesBound n e[1]
  else if e.isOfKind ``Lang.appExpr || e.isOfKind ``Lang.recordExpr then e.getArgs.extract 1 |>.any (namesBound n)
  else if e.isOfKind ``Lang.fren_binder || e.isOfKind ``Lang.fren_top_pattern || e.isOfKind ``Lang.fren_or_pattern then false
  else if e.isOfKind ``Lang.fren_let_def then namesBound n e[3]
  else e.getArgs.any (namesBound n)

/-- What `Core.splitConjuncts` sees of a node of a guard, without the
parentheses around it, as the `fren` command's `guardNode`. -/
def guardNode (e : Syntax) : Core.GuardNode Syntax :=
  let e := unparen e
  let op (o : Syntax) := o.getAtomVal.trimAscii.toString
  if e.getNumArgs == 3 && e[1].isAtom && op e[1] == "and" then .conj e[0] e[2]
  else if let some (xs, ops) := chainOf? e then .compare xs (ops.map op)
  else if isComparison e then .compare #[e[0], e[2]] #[op e[1]]
  else .other

/-- The condition and body of `e`, if it is a `when`. -/
def whenOf? (e : Syntax) : Option (Syntax × Syntax) :=
  let e := unparen e
  if e.getNumArgs == 4 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "when" then some (e[1], e[3]) else none

/-- The conjuncts of the guard of a quantifier, a `forall` if `all`, whose
body is `body` (`Core.guardConjunctsBy`). -/
def guardConjuncts (all : Bool) (body : Syntax) : Array (Core.GuardConjunct Syntax) :=
  Core.guardConjunctsBy guardNode whenOf? all body

/-- The domain of the bound name at position `k` of `names`, the bound
names of a quantifier, a `forall` if `all`, with the body `body`, where
`nat` says that it is a `Nat` (`Core.boundDomain`), as the `fren` command's
`domainOf`. -/
def domainOf (all : Bool) (names : Array Name) (body : Syntax) (k : Nat) (nat : Bool) : Core.GuardDomain :=
  let alone (e : Syntax) : Option Nat :=
    -- A path, as an expression, is a node around it.
    let e := unparen e
    let e := if e.getNumArgs == 1 then e[0] else e
    if e.isOfKind ``Lang.fren_path then
      let segs := pathSegs e
      if segs.size == 1 then names.idxOf? segs[0]!.getId else none
    else none
  let mentions (e : Syntax) : List Nat := (List.range names.size).filter fun j => namesBound names[j]! e
  (Core.boundDomain alone mentions (guardConjuncts all body) k nat).1

/-- Records the lints of the quantifier `e`, a `forall` if `all`, whose
binders `binders` declare `ids`, with their types `bound`, of `sizes`
values each, and whose body is `body`: its bound names that the body does
not mention (`unused_variables`), and `trivial_quantifier`
(`lint::trivial_quantifier`), whose fix writes the value of each bound
name in place of its mentions recorded since `mark`, of the binders from
`outer`. A global expectation's binders over values, whose `e` is its
body, have no `forall` of their own, and no fix. -/
def lintQuant (e : Syntax) (all : Bool) (binders ids : Array Syntax) (bound : Array (Name × Expr)) (sizes : Array Nat)
    (body : Syntax) (outer mark : Nat) : TermElabM Unit := do
  let mentioned := (pathMentions body).map (·.getRoot)
  for x in ids, (bn, _) in bound do
    unless mentioned.contains bn do recordLint .unusedVariables (declaredIdent x).1 (Core.unusedBoundMsg bn all)
  unless Core.trivialQuantifier (sizes.filter (· == 1)).size do return
  let some i := sizes.idxOf? 1 | return
  -- The binder of each bound name.
  let bs := binders.flatMap fun b => b[1].getArgs.map fun _ => b
  let st ← getState
  -- The value of a type of one value, if it is a variant without a payload.
  let values := bound.mapIdx fun k (_, ty) => do
    let info ← ty.constName?.bind st.enumOfDecl?
    let #[v] := info.variants | none
    guard (info.payloads[0]?.all (·.isEmpty))
    pure s!"{exactText bs[k]![3]}::{v}"
  let str := sourceOf body
  let cs := str.toList.toArray
  let quant := charRange str e
  let own := e.getPos? != body.getPos?
  let recorded := (← getLocal).boundMentions.extract mark
  let fixed? : Option String := do
    -- A name the body declares again would hide nothing once the quantifier is gone.
    let redeclared := bound.any fun (bn, _) => (declaredNames body).contains (Core.nameText bn)
    guard (Core.trivialQuantifierFixed (sizes.filter (· == 1)).size sizes.size (values.all Option.isSome) (!own)
      redeclared)
    guard (!Core.hasComment (Core.textOf cs quant))
    let vs ← values.mapM id
    let ms := recorded.filterMap fun (r, k) =>
      if outer ≤ k && k < outer + vs.size then some (charRange.charRangeAt str r, vs[k - outer]!) else none
    pure (Core.substituted cs (charRange str body) ms)
  let msg := Core.trivialQuantifierMsg all bound[i]!.1 (exactText bs[i]![3]) values[i]! quant fixed?
  recordLint .trivialQuantifier bs[i]! (if (← getLocal).inMarkdown && fixed?.isSome then msg.note Core.fixHelp else msg)

/-- Whether the declaration `decl` of a defined function has a quantifier
over a type that is not listed, Lean's `∀` over a value or `∃`, directly or
through another defined function that it applies, to a depth of `fuel`,
beyond which it is taken to have one, as the `fren` command's
`fnQuantifies` (`Core.ElementUse.quantifiedArgument`). -/
partial def defQuantifies (env : Environment) (s : State) (fuel : Nat) (decl : Name) : Bool :=
  if fuel == 0 then true else
  match (env.find? decl).bind (·.value?) with
  | none => false
  | some v =>
    let dependent : Expr → Bool
      | .forallE _ _ b _ => b.hasLooseBVars
      | _ => false
    let quantified := (v.find? fun x => x.isAppOf ``Exists || dependent x).isSome
    let decls := s.defined.foldl (init := #[]) fun acc _ d => if d.decl != decl then acc.push d.decl else acc
    quantified || decls.any fun d => (v.find? (·.isConstOf d)).isSome && defQuantifies env s (fuel - 1) d

/-- How the expression `e`, within the body of a quantifier, uses the bound
name `x`, where `inner` are the names that the body declares, which may
stand for `x` (`Core.ElementUse`), as the `fren` command's `elementUses`. -/
partial def elementUses (cx : ExprCtx) (x : Name) (inner : Array Name) (e : Syntax) :
    TermElabM (Array Core.ElementUse) := do
  let names (e : Syntax) : Bool := (pathMentions e).any fun n => n.getRoot == x || inner.contains n.getRoot
  let st ← getState
  let positions (m : String) : Nat := match m with | "update" | "at" => 1 | "slice" => 2 | _ => 0
  let own : Array Core.ElementUse ← do
    if e.isOfKind ``Lang.indexExpr then
      pure (if names e[2] && !(← isConstant cx e[0]) then #[.index] else #[])
    else if e.isOfKind ``Lang.methodExpr then
      let n := if e[2].isIdent || e[2].isAtom then e[2] else e[2][0]
      let m := if n.isIdent then n.getId.toString else n.getAtomVal.trimAscii.toString
      pure (if (e[4].getSepArgs.extract 0 (positions m)).any names && !(← isConstant cx e[0]) then #[.index] else #[])
    else if e.isOfKind ``Lang.appExpr then
      let args := e[2].getSepArgs
      if !args.any names then pure #[]
      else if let some (_, m) := methodApp? cx e then
        pure (if (args.extract 0 (positions m.toString)).any names then #[.index] else #[])
      else
        let some names' ← (try some <$> segNames (pathSegs e[0]) catch _ => pure none) | pure #[]
        match st.table.resolvePath cx.modName names' cx.shadowing with
        | .ok (.item { kind := .fnItem, path, .. }) =>
          if let some d := st.defined.get? path then
            let ps := if d.typeParams.isEmpty then d.ptys.1.map (·.ty) else d.declared
            if ps.any (Core.hasSeqWithin st.shapeOf 8) then pure #[.seqArgument]
            else pure (if defQuantifies (← getEnv) st 8 d.decl then #[.quantifiedArgument] else #[])
          else
            let facts := (st.abstracts.get? path).any fun a =>
              a.ptys.2.ty == .nat || a.fact?.isSome || st.contracts.contains path
            pure (if facts then #[.factArgument] else #[])
        | _ => pure #[]
    else if e.isOfKind ``Lang.quantExpr then
      let receivers := (guardConjuncts (isForall e) e[3]).filterMap fun
        | some (_, .mem, r) => some r
        | _ => none
      pure (if receivers.any names then #[.receiver] else #[])
    else pure #[]
  return own ++ (← e.getArgs.flatMapM (elementUses cx x inner))

/-- The quantifier that is directly the body `e` of a quantifier over
elements, a `forall` if `all`, if any, by where it is (`elemKey`), as the
`fren` command's `elementSpine`. -/
partial def elementSpine (all : Bool) (e : Syntax) : Option (Option String.Pos.Raw × Option String.Pos.Raw) :=
  let e := unparen e
  if let some (_, d) := whenOf? e then (if all then elementSpine all d else none)
  else if let .conj _ b := guardNode e then (if all then none else elementSpine all b)
  else if e.isOfKind ``Lang.quantExpr && isForall e == all then some (elemKey e)
  else none

open Lang in
/-- `forall (x: T), e`, or `exists` unless `all`, with the binders
`binders` and the body `body`: expanded over the bound names of listed
types (`Reqs/Lang/Quantifiers#meaning`), and Lean's `∀` or `∃` over the
others, around the expansion (`Reqs/Lang/Quantifiers#unbounded-quantifiers`).
The body is elaborated once, over a local for each bound name, and
instantiated at every combination of the values of those of listed types,
the last name varying fastest, and the instances conjoined or disjoined;
so are the definedness goals of its indexes, which hold in every instance,
under `∀` whatever the quantifier. A local of a type that is not listed is
named `x'k`, with `k` its position among the binders in scope, as the
solver knows it, and `undecidable` is reported at its binder
(`lang::in_core`). The names must be distinct, follow the Boolean names
rule and be written with `!` exactly when they shadow (`lang::shadowing`),
and the combinations be at most `Core.maxInstances`
(`lang::quantifier_size`), as the `fren` command checks them. -/
def quantTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) (all : Bool)
    (binders : Array Syntax) (body : Syntax) : TermElabM Term := withRef e do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := binders.flatMap (·[1].getArgs)
  for x in ids do discard (segName x)
  let declared := ids.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt ids[k]! (Core.dupBoundMsg declared[k]!).text
  -- Each bound name, its Lean type and declared type, and its values if
  -- its type is listed.
  let mut bound : Array (Name × Expr × Core.PTy × Option (Array Term)) := #[]
  let mut sizes := #[]
  let mut unlisted := #[]
  for b in binders do
    let (ty, pt) ← binderType cx.modName b[3]
    let values? ← binderValues ty pt
    -- Reported once the quantifier's verdict is known.
    if values?.isNone then unlisted := unlisted.push b
    for x in b[1].getArgs do
      let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what) ++ bound.map (·.1, Core.BindingKind.boundName)) cx.selfFn.isSome
      let x ← declare x cx.modName locals
      let bn := x.getId
      liftMsg x (Core.checkVarName bn (some (ty.isConstOf ``Bool)))
      lintName .binder bn x
      bound := bound.push (bn, ty, pt, values?.map (·.2))
      if let some (n, _) := values? then sizes := sizes.push n
  let n := cx.instances * Core.instanceCount sizes
  unless Core.quantifierSizeAccepted n do
    throwErrorAt (mkNullNode binders) (Core.quantifierSizeMsg n (cx.instances > 1)).text
  let names := bound.map (·.1)
  -- A quantifier over a sequence's elements (`lang::element_quantifier`):
  -- each bound name of a type that is not listed has the members of `x in
  -- e` as its domain, by the first conjunct of the guard that names it, as
  -- the `fren` command finds them.
  let conjuncts := guardConjuncts all body
  let parts := Core.guardPartsBy guardNode whenOf? all body
  let members : Array (Option Syntax) := bound.zipIdx.filterMap fun ((bn, ty, _, vs?), k) =>
    if vs?.isSome then none else some <|
      match domainOf all names body k (ty.isConstOf ``Nat) with
      | .members j =>
        if (parts.extract 0 j).any (·.any (namesBound bn)) then none
        else match conjuncts[j]? with
          | some (some (_, .mem, m)) => some m
          | _ => none
      | _ => none
  let candidate := !members.isEmpty && members.all Option.isSome
  let nesting : Core.ElementNesting := match cx.elemKind? with
    | none => .top
    | some k => if k == all && cx.elemDirect.contains (elemKey e) then .direct else .other
  let bodyCx := if candidate then
      { cx with elemGuards := cx.elemGuards ++ members.filterMap (·.map elemKey), elemKind? := some all
                elemDirect := cx.elemDirect ++ (elementSpine all body).toArray
                elemChain := (if nesting == .direct then cx.elemChain else #[])
                  ++ (bound.filter (·.2.2.2.isNone)).map (·.1) }
    else cx
  let values ← bound.filterMapM fun (_, ty, _, vs?) => vs?.mapM (·.mapM (elabProp · ty))
  let combos := values.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]]
  let localName (k : Nat) (bn : Name) (listed : Bool) : Name :=
    if listed then bn else .mkSimple (Core.boundSymbol bn.getString! (cx.binders.size + k))
  withLocalDeclsD (bound.mapIdx fun k (bn, ty, _, vs?) => (localName k bn vs?.isSome, fun _ => pure ty)) fun fvs => do
    let new ← (bound.zip fvs).mapIdxM fun i ((bn, ty, _, vs?), fv) => do
      return { name := bn, term := ← exprToSyntax fv, «type» := ty, scrutinee := none, outer := cx.binders.size + i
               unbounded := vs?.isNone : MatchBinder }
    let listedFvs := (bound.zip fvs).filterMap fun ((_, _, _, vs?), fv) => vs?.map fun _ => fv
    let free := (bound.zip fvs).filterMap fun ((_, ty, pt, vs?), fv) => if vs?.isNone then some (fv, ty, pt) else none
    let outer := (← getLocal).indexes
    let outerTables := (← getLocal).tables
    modifyLocal fun l => { l with indexes := #[], tables := #[] }
    let mark := (← getLocal).boundMentions.size
    let t ← toTerm { bodyCx with binders := cx.binders ++ new, natOk := false, instances := cx.instances * combos.size } body
    -- Its bound names' lints, then whether its body is a `Bool`, before
    -- its verdict is reported, in the `fren` command's order. Each bound
    -- name's number of values, 0 for a type that is not listed.
    if cx.noteIndexes then
      lintQuant e all binders ids (bound.map fun (bn, ty, _, _) => (bn, ty))
        (bound.map fun (_, _, _, vs?) => (vs?.map (·.size)).getD 0) body cx.binders.size mark
    checkTermType body t .bool (some s!"note: the body of `{if all then "forall" else "exists"}` is a `Bool`")
    -- Its verdict, from its bound names of types that are not listed, in
    -- order, as the `fren` command decides it.
    let verdict ← if !candidate then pure Core.ElementVerdict.notMembers else do
      let recorded := (← getLocal).elemMembers
      let inner := (declaredNames body).map Name.mkSimple
      let unbounded := bound.filter (·.2.2.2.isNone)
      let mut infos := #[]
      for (bn, _, _, _) in unbounded, m? in members, k in [0:unbounded.size] do
        let some m := m? | continue
        let seq := (recorded.find? (·.1 == elemKey m)).any (·.2.1)
        let earlier := (unbounded.extract 0 k).map (·.1) ++ (cx.binders.filter (·.unbounded)).map (·.name)
        infos := infos.push
          { members := if seq then .seq else .set
            receiverBound := (pathMentions m).any (earlier.contains ·.getRoot)
            uses := (← elementUses cx bn inner body).toList : Core.ElementBinder }
      -- What the quantifier mentions, once its own bound names are not.
      let chain := if nesting == .direct then cx.elemChain else #[]
      let bodyNames := (pathMentions body).filter fun n => !names.contains n.getRoot
      let boundNames := bodyNames.any fun n =>
        let r := n.getRoot
        !chain.contains r && (cx.binder? r).any (·.unbounded)
      let output ← mentionsOutputOf cx bodyNames
      pure (Core.elementVerdict nesting output boundNames infos.toList)
    let inCore := verdict == .inCore
    -- The reports that its guard's memberships deferred, and its binders'.
    let keys := members.filterMap (·.map elemKey)
    let deferred := (← getLocal).elemMembers.filter (keys.contains ·.1)
    modifyLocal fun l => { l with elemMembers := l.elemMembers.filter (!keys.contains ·.1) }
    unless inCore || cx.unmentioned do
      for (_, _, r?) in deferred do
        if let some (ref, msg) := r? then
          modifyLocal fun l => { l with outsideCore := true }
          recordLint .undecidable ref msg
      for b in unlisted do
        modifyLocal fun l => { l with outsideCore := true }
        recordLint .undecidable b ((Core.elementUndecidableMsg verdict).getD (Core.undecidableMsg .quantifier false))
    -- A bound name of a type that is not listed, with a domain, makes the
    -- queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`), unless the
    -- quantifier is expanded.
    if !inCore && bound.zipIdx.any (fun ((_, ty, _, vs?), k) => vs?.isNone && domainOf all names body k (ty.isConstOf ``Nat) != .unbounded) then
      modifyLocal fun l => { l with guardedUsed := true }
    let b ← elabProp t
    let inner ← (← getLocal).indexes.mapM fun (ref, g) => return (ref, ← elabProp g)
    let innerTables ← (← getLocal).tables.mapM fun (ref, q, g) => return (ref, q, ← elabProp g)
    let inst (x : Expr) (vals : Array Expr) : Expr := x.replaceFVars listedFvs vals
    -- Lean's `∀`, or `∃` unless `forall?`, over the bound names of types
    -- that are not listed, with what their types bring as a hypothesis or a
    -- conjunct, and without `have`s, which lean-smt does not translate.
    let bindFree (forall? : Bool) (x : Expr) : TermElabM Expr := do
      if free.isEmpty then return x
      -- A quantifier over elements in the core is marked, for each query
      -- to expand (`Fren.Elems`).
      let marked (n : Nat) (q : Expr) : Expr := if inCore then Elems.mark n q else q
      let x ← zetaReduce x
      -- Only over the bound names that it mentions: one that it does not
      -- would be a non-dependent `∀`, an implication from a type, which
      -- lean-smt cannot translate, and every type has values, so leaving
      -- it out changes nothing.
      let free := if inCore then free else free.filter fun (fv, _, _) => x.containsFVar fv.fvarId!
      if free.isEmpty then return x
      let marked := marked free.size
      let cons ← free.filterMapM fun (fv, ty, pt) => return (← factPred? ty pt).map (·.beta #[fv])
      if forall? then
        return marked (← mkForallFVars (free.map (·.1)) (cons.foldr mkArrow' x))
      else
        return marked (← free.foldrM (init := cons.foldr mkAnd x) fun (fv, _, _) acc => do
          mkAppM ``Exists #[← mkLambdaFVars #[fv] acc])
    -- The names of enclosing `let`s and `where`s are locals here, which the
    -- `have`s that define them bind again: what mentions them is closed
    -- over them, and applied to their names.
    let lctx ← getLCtx
    let defs := cx.binders.filterMap fun d =>
      if d.isDef || d.closure then (lctx.findFromUserName? d.term.raw.getId).map (d.term, ·.toExpr) else none
    let close (x : Expr) : TermElabM Term := do
      let used := defs.filter fun (_, fv) => x.containsFVar fv.fvarId!
      if used.isEmpty then return ← exprToSyntax x
      let f ← exprToSyntax (← mkLambdaFVars (used.map (·.2)) x)
      `($f $(used.map (·.1))*)
    let goals ← inner.mapM fun (ref, g) => return (ref, ← close (← bindFree true (balanced mkAnd (combos.map (inst g)))))
    let tableGoals ← innerTables.mapM fun (ref, q, g) =>
      return (ref, q, ← close (← bindFree true (balanced mkAnd (combos.map (inst g)))))
    modifyLocal fun l => { l with indexes := outer ++ goals, tables := outerTables ++ tableGoals }
    close (← bindFree all (balanced (if all then mkAnd else mkOr) (combos.map (inst b))))
where
  /-- `p → q`, a non-dependent arrow. -/
  mkArrow' (p q : Expr) : Expr := .forallE `h p q .default


end Fren
