-- keep-sorted start
import Fren.Check
import Fren.Elab
import Fren.Prelude
import FrenCore.Enumeration
-- keep-sorted end

/-!
# Checking by enumeration in Lean (`Reqs/Check#checking-by-enumeration`)

The Lean-hosted front end's side of `Fren.Core.Enumeration`: each atom, a
proposition over the component's variables, is compiled, with Lean's
evaluator, into a function of an assignment of the slots, which reads each
variable's value from its slot's values and decides the proposition. The
defined outputs are replaced by their definitions, the abstract types by
`Nat`, whose `k` is the type's `k`th value, and the unspecified value of
each type, `Fren.Seq.nth ∅ 0`, by its hidden slot's.
-/

open Lean Meta

namespace Fren

/-- The value of slot `i` in the assignment `env`, of the slot's values
`vs`, or `d` if there is none. -/
def Enum.pick {α : Type} (vs : Array α) (d : α) (env : Array Nat) (i : Nat) : α := vs.getD (env.getD i 0) d

/-- The position of `a` among `vs`, or `vs.size` if it is not there. -/
def Enum.index {α : Type} [BEq α] (vs : Array α) (a : α) : Nat := (vs.findIdx? (· == a)).getD vs.size

/-- An uninterpreted function's value, in the assignment `env`, at the
arguments at the positions `idx` among its parameters' values, of sizes
`sizes`: the result of `rs` that the table of its slot `slot` gives, or
the first, `d` if none, where an argument is not among them
(`Core.Enumeration.FunSlot`). -/
def Enum.apply {β : Type} (rs : Array β) (d : β) (tables env : Array Nat) (slot : Nat) (sizes idx : Array Nat) : β :=
  match Core.Enumeration.tupleIndex sizes idx with
  | some pos => rs.getD (Core.Enumeration.tableEntry rs.size (tables.getD (env.getD slot 0) 0) pos) d
  | none => rs.getD 0 d

namespace Enumerate

open Core.Enumeration

/-- The integer `i` as a literal, as Lean writes it. -/
def intExpr (i : Int) : MetaM Expr := do
  if 0 ≤ i then mkNumeral (mkConst ``Int) i.toNat
  else mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (-i).toNat]

/-- The value `v` of the Lean type `ty` (`Core.Enumeration.EVal`), the
`k`th value of an abstract type being `k : Nat`. -/
partial def valueExpr (ty : Expr) (v : EVal) : MetaM Expr := do
  let s ← getState
  match v with
  | .bool b => return mkConst (if b then ``Bool.true else ``Bool.false)
  | .int i => if ty.isConstOf ``Int then intExpr i else return mkNatLit i.toNat
  | .abs k => return mkNatLit k
  | .ctor idx args =>
    let ty ← whnfR ty
    let some d := ty.getAppFn.constName? | throwError "not a datatype: {ty}"
    let targs := ty.getAppArgs
    -- A prelude type's constructor is at universe 0 (`EnumInfo.ctorConst`).
    let (c, ts) :=
      if let some e := s.enumOfDecl? d then (e.ctorConst idx, (e.payloadsAt targs)[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then (mkConst r.ctor, (r.fieldsAt targs).map (·.2))
      else if let some n := s.newtypeOfDecl? d then (mkConst n.ctor, #[n.under])
      else (mkConst .anonymous, #[])
    let as ← (args.toArray.zip ts).mapM fun (w, t) => valueExpr t w
    return mkAppN c (targs ++ as)

/-- `e` with its integers written as literals: `Int.ofNat n` and
`Int.negSucc n`, as reduction leaves them, become `n` and `-(n + 1)`. -/
def normInts (e : Expr) : MetaM Expr :=
  Lean.Core.transform e (pre := fun x => do
    let n? := fun (y : Expr) => y.rawNatLit? <|> y.nat?
    if x.isAppOfArity ``Int.ofNat 1 then
      if let some n := n? x.appArg! then return .done (← intExpr n)
    if x.isAppOfArity ``Int.negSucc 1 then
      if let some n := n? x.appArg! then return .done (← intExpr (-(n : Int) - 1))
    return .continue)

/-- The unspecified values of types that `e` reads, `Fren.Seq.nth ∅ 0`:
each application, once. -/
def unspecifiedIn (e : Expr) : Array Expr := go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    if e.isAppOfArity ``Fren.Seq.nth 4 && (e.getArg! 2).isAppOf ``EmptyCollection.emptyCollection then
      if acc.contains e then acc else acc.push e
    else match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b | .proj _ _ b => go b acc
      | _ => acc

/-- Whether `e` has an unbounded quantifier: a `∀` or `∃` over values
rather than propositions, which a quantifier over a listed type is not,
since it is expanded. -/
partial def hasQuantifier (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ t b _ =>
    if !(← isProp t) then return true
    -- An implication; its body may mention the hypothesis only in a proof.
    hasQuantifier t <||> hasQuantifier (b.instantiate1 (mkConst ``True.intro))
  | .app .. =>
    if e.isAppOf ``Exists then return true
    e.getAppArgs.anyM hasQuantifier <||> hasQuantifier e.getAppFn
  | .lam n t b bi => withLocalDecl n bi t fun x => hasQuantifier (b.instantiate1 x)
  | .letE _ _ v b _ => hasQuantifier v <||> hasQuantifier (b.instantiate1 v)
  | .mdata _ b | .proj _ _ b => hasQuantifier b
  | _ => return false

/-- A `Decidable` instance for the proposition `p`, built along its
connectives, so that a quantifier over a listed type, which is expanded
into as many conjuncts as it has instances, needs no search of the size
of the whole; each other proposition's is synthesized. -/
partial def decidableOf (p : Expr) : MetaM Expr := do
  match p.getAppFn.constName?, p.getAppArgs with
  | some ``And, #[a, b] => return mkApp4 (mkConst ``instDecidableAnd) a b (← decidableOf a) (← decidableOf b)
  | some ``Or, #[a, b] => return mkApp4 (mkConst ``instDecidableOr) a b (← decidableOf a) (← decidableOf b)
  | some ``Not, #[a] => return mkApp2 (mkConst ``instDecidableNot) a (← decidableOf a)
  | some ``Iff, #[a, b] => return mkApp4 (mkConst ``instDecidableIff) a b (← decidableOf a) (← decidableOf b)
  | _, _ =>
    if let .forallE _ a b _ := p then
      if !b.hasLooseBVars && (← isProp a) then
        return mkApp4 (mkConst ``instDecidableForall) a b (← decidableOf a) (← decidableOf b)
    synthInstance (mkApp (mkConst ``Decidable) p)

/-- Compiles `fs`, each a closed function, with Lean's evaluator. -/
unsafe def compileUnsafe (α : Type) [Inhabited α] (ty : Expr) (fs : Array Expr) : MetaM (Array α) := do
  if fs.isEmpty then return #[]
  let arr ← mkArrayLit ty fs.toList
  let arrTy := mkApp (mkConst ``Array [0]) ty
  evalExpr (Array α) arrTy arr

@[implemented_by compileUnsafe]
opaque compile (α : Type) [Inhabited α] (ty : Expr) (fs : Array Expr) : MetaM (Array α)

instance : Inhabited (Array Nat → Bool) := ⟨fun _ => false⟩
instance : Inhabited (Array Nat → Array Nat → Bool) := ⟨fun _ _ => false⟩

/-- Enumerates the checks of `c` set to enumeration
(`Reqs/Check#checking-by-enumeration`), as `checkComp`'s hook
(`EnumHook`): `full` is its comp, over the locals `fvs` of its variables
and `ufs` of the abstract types and functions it uses, of which `fns` are
the functions. -/
def enumerateOnly (c : CompInfo) (full : Core.Comp Expr) (fvs ufs : Array Expr) (fns : Array (Name × Expr × Nat × Bool))
    (kinds : Array CheckKind) (t : Core.Tested) (testing : Bool) : MetaM (Except Core.Msg Enumerated) := do
  let st ← getState
  -- A global expectation is shown by its module and name, as the `fren`
  -- command shows it.
  let global := st.globals.toList.any fun (_, g) => g.decl == c.decl
  let subject := s!"`{Core.showComp (if global then c.path ++ ((c.props[0]?.map (·.name)).getD .anonymous) else c.path)}`"
  let n := c.enumSize
  let (core, ks) := full.only t kinds
  let (ecomp, atoms0) := core.atoms
  -- The defined outputs, by their definitions, the last first, since each
  -- mentions only earlier ones.
  let varFv (x : Name) : Option Expr := (c.vars.findIdx? (·.name == x)).map (fvs[·]!)
  let defined := full.defs.filterMap fun (d, _, e) => (varFv d).map (d, ·, e)
  let substDefs (e : Expr) : Expr := defined.foldr (init := e) fun (_, fv, de) acc => acc.replaceFVar fv de
  let atoms ← atoms0.mapM fun a => unfoldDefined (substDefs a)
  -- And each defined output's definition, which `same` reads, and whose
  -- unspecified values and functions are enumerated as the atoms' are,
  -- as the `fren` command's are.
  let defExprs ← defined.mapM fun (_, fv, _) => unfoldDefined (substDefs fv)
  let scanned := atoms ++ defExprs
  -- The uninterpreted functions that the atoms apply, whose interpretations
  -- are enumerated, but not of one with a contract, which constrains them
  -- (`check::enumerable`).
  let mut used : Array (Name × Expr × Bool × FunVar) := #[]
  for (u, x, _, nat) in fns do
    if scanned.any (·.containsFVar x.fvarId!) then
      let some a := st.abstracts.foldl (init := none) fun acc _ a => if a.placeholder == u then some a else acc | continue
      if ((st.contracts.get? a.path).map (!·.posts.isEmpty)).getD false then
        return .error (notEnumerableMsg subject
          s!"it applies the uninterpreted function `{Core.showComp a.path}`, which has a contract")
      used := used.push (a.path, x, nat,
        { name := a.path, params := a.ptys.1.map (Core.PTy.plain ·.ty), result := a.ptys.2 })
  if ← scanned.anyM hasQuantifier then
    return .error (notEnumerableMsg subject "it has an unbounded quantifier")
  -- The abstract types become `Nat`, and their `Inhabited` instances `Nat`'s.
  let mut absTys : Array (Expr × Name) := #[]
  let mut absInsts : Array Expr := #[]
  for u in ufs do
    let t ← inferType u
    if t.isSort then
      let path := st.abstracts.foldl (init := Name.anonymous) fun acc _ a =>
        if c.uses[ufs.idxOf u]? == some a.placeholder then a.path else acc
      absTys := absTys.push (u, path)
    else if t.isAppOf ``Inhabited then absInsts := absInsts.push u
  let natTy (e : Expr) : Expr :=
    (e.replaceFVars (absTys.map (·.1)) (absTys.map fun _ => mkConst ``Nat)).replaceFVars absInsts
      (absInsts.map fun _ => mkConst ``instInhabitedNat)
  -- The hidden slots: each type whose unspecified value is read.
  let unspec := scanned.foldl (init := #[]) fun acc a =>
    (unspecifiedIn a).foldl (fun acc u => if acc.any (·.getArg! 0 == u.getArg! 0) then acc else acc.push u) acc
  let ptyOfLean (t : Expr) : Option Core.PTy :=
    match absTys.find? (·.1 == t) with
    | some (_, p) => some (Core.PTy.plain (.abstract p))
    | none => (coreTyOf st t).map Core.PTy.plain
  let mut hidden : Array (Name × Core.PTy) := #[]
  for u in unspec, k in [0:unspec.size] do
    let some pt := ptyOfLean (u.getArg! 0)
      | return .error (notEnumerableMsg subject (notEnumerableWhy none "`?`"))
    hidden := hidden.push (.mkNum `«[][0]» k, pt)
  let vars := c.vars.map fun v =>
    ({ sig := { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
       pty := if v.fact?.isSome then v.ptype else Core.PTy.plain v.ptype.ty
       defined := v.defn?.isSome } : SlotVar)
  let (space, values, shapes, fslots) ← match spaceOf st.shapeOf n vars hidden (used.map (·.2.2.2)) (if testing then testCount else 0) (hash c.path) with
    | .ok r => pure r
    | .error (x, why) => return .error (notEnumerableMsg subject (notEnumerableWhy x why))
  let determinism := ks.contains .determinism && ecomp.vars.any (·.isDet)
  let count := space.behaviours determinism fslots
  if !withinLimit count then return .error (tooManyMsg subject count n)
  -- Each slot's Lean type and values: a variable's, its second copy's, or
  -- an unspecified value's.
  let own := c.vars.filter (·.defn?.isNone)
  let copied := own.filter fun v => (Core.Symbol.ofRole v.role).copied
  let slotTys := own.map (·.type) ++ copied.map (·.type) ++ unspec.map (·.getArg! 0)
  let slotVals ← (slotTys.zip values).mapM fun (t, vs) => vs.mapM (valueExpr (natTy t))
  -- The locals that the slots stand for: the variables', then the hidden
  -- slots', which replace the unspecified values.
  withLocalDeclsD (unspec.map fun u => (`u, fun _ => pure (natTy (u.getArg! 0)))) fun hfvs => do
  let ownFvs := own.map fun v => (varFv v.name).get!
  let slotFvs := ownFvs ++ hfvs
  let slotIdx := (List.range own.size).toArray ++ (List.range hfvs.size).toArray.map (· + own.size + copied.size)
  -- Each function, as its interpretation in the assignment `env`.
  let interpreted (env : Expr) : MetaM (Array Expr) := (used.zip fslots).mapM fun ((_, x, nat, _), f) => do
    forallTelescope (natTy (← inferType x)) fun args res => do
      let res := if nat then mkConst ``Int else res
      let ptys ← args.mapM inferType
      let ps ← (ptys.zip f.params).mapM fun (t, vs) => do mkArrayLit t (← vs.toList.mapM (valueExpr t))
      let rs ← f.results.toList.mapM (valueExpr res)
      let d ← if let r :: _ := rs then pure r else mkAppOptM ``Inhabited.default #[some res, none]
      let idx ← (ps.zip args).mapM fun (p, a) => mkAppM ``Enum.index #[p, a]
      let natArr (xs : List Nat) := mkArrayLit (mkConst ``Nat) (xs.map mkNatLit)
      let body := mkAppN (mkConst ``Enum.apply) #[res, ← mkArrayLit res rs, d, ← natArr f.tables.toList, env,
        mkNatLit f.slot, ← natArr (f.params.map (·.size)).toList, ← mkArrayLit (mkConst ``Nat) idx.toList]
      mkLambdaFVars args body
  -- `e` over the assignment `env` of the slots.
  let over (env : Expr) (e : Expr) : MetaM Expr := do
    let e := unspec.zip hfvs |>.foldl (init := e) fun acc (u, h) => acc.replace fun x => if x == u then some h else none
    let e := (e.replaceFVars (used.map (·.2.1)) (← interpreted env)).headBeta
    let e ← Lean.Core.betaReduce e
    let e := natTy e
    let picks ← slotFvs.zipIdx.mapM fun (_, j) => do
      let i := slotIdx[j]!
      let t := natTy slotTys[i]!
      let vs := slotVals[i]!
      let d ← if h : 0 < vs.size then pure vs[0] else mkAppOptM ``Inhabited.default #[some t, none]
      return mkApp5 (mkConst ``Enum.pick) t (← mkArrayLit t vs.toList) d env (mkNatLit i)
    return e.replaceFVars slotFvs picks
  let arrNat := mkApp (mkConst ``Array [0]) (mkConst ``Nat)
  let decideOf (p : Expr) : MetaM Expr := do
    return mkApp2 (mkConst ``Decidable.decide) p (← decidableOf p)
  try
    let atomFns ← atoms.mapM fun a => withLocalDeclD `env arrNat fun env => do
      mkLambdaFVars #[env] (← decideOf (← over env a))
    let fnTy ← mkArrow arrNat (mkConst ``Bool)
    let evals ← compile (Array Nat → Bool) fnTy atomFns
    let sameFns ← defined.mapM fun (_, _, de) => withLocalDeclD `e₁ arrNat fun e₁ => withLocalDeclD `e₂ arrNat fun e₂ => do
      let de ← unfoldDefined de
      mkLambdaFVars #[e₁, e₂] (← decideOf (← mkEq (← over e₁ de) (← over e₂ de)))
    let sames ← compile (Array Nat → Array Nat → Bool) (← mkArrow arrNat (← mkArrow arrNat (mkConst ``Bool))) sameFns
    -- What each atom reads: the slots of the locals it mentions, and the
    -- defined outputs it mentions.
    let slotsOf (a : Expr) : Array Nat :=
      let a := unspec.zip hfvs |>.foldl (init := a) fun acc (u, h) => acc.replace fun x => if x == u then some h else none
      (slotFvs.zipIdx.filter fun (x, _) => a.containsFVar x.fvarId!).map (fun (_, j) => slotIdx[j]!)
        ++ (used.zip fslots).filterMap fun ((_, x, _, _), f) => if a.containsFVar x.fvarId! then some f.slot else none
    let atomSlots := atoms.map slotsOf
    let atomDefs := atoms0.map fun a => defined.filterMap fun (d, fv, _) => if a.containsFVar fv.fvarId! then some d else none
    let ats : Atoms := {
      slots := atomSlots, defs := atomDefs, eval := fun k env => evals[k]! env
      sameDefined := fun d e₁ e₂ => match defined.findIdx? (·.1 == d) with
        | some i => sames[i]! e₁ e₂
        | none => true
      defSlots := fun d => match defined.findIdx? (·.1 == d) with
        | some i => slotsOf defExprs[i]!
        | none => #[] }
    let varTy (x : Name) : Expr :=
      let base := if x.isStr && x.getString!.endsWith "'" then Name.mkStr x.getPrefix (x.getString!.dropEnd 1).toString else x
      ((c.vars.find? (·.name == base)).map (·.type)).getD (mkConst ``Bool)
    let renderSlot (s j : Nat) : MetaM String := do
      let some v := slotVals[s]?.bind (·[j]?) | return "?"
      Fren.render slotTys[s]! v
    -- A defined output's value in `env`: its definition, over the
    -- assignment, with the functions' interpretations and the unspecified
    -- values, reduced.
    let defValue (d : Name) (env : Array Nat) : MetaM (Option String) := do
      let some i := defined.findIdx? (·.1 == d) | return none
      let envE ← mkArrayLit (mkConst ``Nat) (env.toList.map mkNatLit)
      let v ← withTransparency .all <| Meta.reduce (← over envE defExprs[i]!)
      return some (← Fren.render (varTy d) (← normInts v))
    -- The variant of each value of a slot whose type is an enumeration,
    -- as the solver's backend names it.
    let variantOf (s j : Nat) : Option Core.Variant := do
      let v ← slotVals[s]?.bind (·[j]?)
      let e ← st.enumOf? (slotTys[s]?.getD (mkConst ``Bool))
      let .const c _ := v.getAppFn | none
      let idx ← e.ctorIdx? c
      return { name := s!"{e.path.getString!}::{e.variants[idx]!}", arity := (e.payloads[idx]?.map (·.size)).getD 0 }
    let raw ← Core.checkComp (fun _ => backend space ats renderSlot defValue (if testing then some (hash c.path) else none)
      variantOf) ecomp ks
    let exact := exhaustedAll shapes n (List.range space.names.size).toArray && fslots.all (·.exhausted)
    let outputsExact := exhaustedAll shapes n space.outputs
    return .ok { results := raw.map (classify n exact outputsExact), bound := n, exact }
  catch ex =>
    return .error (Core.Msg.internal s!"enumerating {subject} in Lean failed: {← ex.toMessageData.toString}")

/-- Enumerates the checks of `c` set to enumeration
(`Reqs/Check#checking-by-enumeration`), as `checkComp`'s hook
(`EnumHook`), those also set to testing tested beyond the bound too
(`Reqs/Check#enumeration-then-testing`), as the `fren` command does. -/
def enumerate (c : CompInfo) (full : Core.Comp Expr) (fvs ufs : Array Expr) (fns : Array (Name × Expr × Nat × Bool))
    (kinds : Array CheckKind) : MetaM (Except Core.Msg Enumerated) := do
  let run (t : Core.Tested) (testing : Bool) : MetaM (Except Core.Msg (Option Enumerated)) := do
    if !t.any then return .ok none
    return (← enumerateOnly c full fvs ufs fns kinds t testing).map some
  match ← run (c.enumerated.minus c.tested) false with
  | .error m => return .error m
  | .ok a =>
  match ← run (c.enumerated.inter c.tested) true with
  | .error m => return .error m
  | .ok b =>
  return .ok (Enumerated.merge c.enumSize a b c.enumerated.covers)

end Enumerate

end Fren
