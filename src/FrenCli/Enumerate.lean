-- keep-sorted start
import FrenCli.Confirm
import FrenCore.Enumeration
-- keep-sorted end

/-!
# Checking by enumeration (`Reqs/Check#checking-by-enumeration`)

The `fren` command's side of `Fren.Core.Enumeration`: the atoms are the
formulas that `pairCore` pairs with the solver's, as the evaluator reads
them, evaluated in each assignment of the slots, with the defined outputs
computed from their definitions and the unspecified value of each type
that a table or `match` reads given by its hidden slot.
-/

open Lean

namespace FrenCli

open Eval Fren.Core.Enumeration

/-- The expressions of a formula, each with its prefix, or `none` if the
evaluator does not know its meaning. -/
partial def Fm.exprs? : Fm → Option (Array (Name × Ex))
  | .atoms as => some (as.map fun a => (a.pfx, a.e))
  | .falsity => some #[]
  | .not f | .primed _ f => f.exprs?
  | .conj fs => fs.foldlM (fun acc f => (acc ++ ·) <$> f.exprs?) #[]
  | .defn _ e => some #[(.anonymous, e)]
  | .defined ds f => (fun r => ds.map (fun (_, e) => ((.anonymous : Name), e)) ++ r) <$> f.exprs?
  | .exOutputs _ f => f.exprs?
  | .pin .. | .pinVariant .. | .same _ => some #[]
  | .unknown => none

/-- Whether `f` holds, its constraints evaluated with `I` and `look`;
defined outputs are computed, so their equations hold. -/
partial def Fm.holds (I : Interp) (look : Look) : Fm → Bool
  | .atoms as => allHold I look as == some true
  | .falsity => false
  | .not f => !Fm.holds I look f
  | .conj fs => fs.all (Fm.holds I look)
  | .defn .. => true
  | .defined _ f => Fm.holds I look f
  | _ => false

/-- The value of `f`, with its constraints evaluated with `I` and `look`,
`none` where it is unknown: its atoms' conjunctions and `not` by the
strong Kleene connectives, as `Fm.holds` reads them where they are known. -/
partial def Fm.value? (I : Interp) (look : Look) : Fm → Option Bool
  | .atoms as => allHold I look as
  | .falsity => some false
  | .not f => (Fm.value? I look f).map (!·)
  | .conj fs =>
    let vs := fs.map (Fm.value? I look)
    if vs.contains (some false) then some false else if vs.all (·.isSome) then some true else none
  | .defn .. => some true
  | .defined _ f => Fm.value? I look f
  | _ => some false

/-- Whether `e` has a quantifier, guarded or not. -/
partial def Eval.Ex.hasQuantifier (e : Ex) : Bool :=
  (e matches .quant ..) || e.children.any (·.hasQuantifier)

/-- The declared types that the quantifiers in `e` without a domain range
over. -/
partial def Eval.Ex.quantifiedTypes (e : Ex) : Array Fren.Core.PTy :=
  let own := match e with
    | .quant _ _ _ _ domains types _ => types.zipIdx.filterMap fun (ty, i) =>
      if (domains[i]?.join).isNone then some ty else none
    | _ => #[]
  own ++ e.children.flatMap (·.quantifiedTypes)

/-- The variables that `e` reads, by name. -/
partial def Eval.Ex.varsOf (e : Ex) : Array Name :=
  match e with
  | .var n => #[n]
  | _ => e.children.flatMap (·.varsOf)

/-- Not a function: what `Eval.Ex.appsIn` lists where an index is read,
whose value out of range enumeration gives by one interpretation of all
(`Interp.outOfRange`), so that a query that reads one is unknown without
a model (`Atoms.readsIndex`). -/
def indexRead : Name := .str .anonymous "[]"

/-- Not a function: what `Eval.Ex.appsIn` lists for an index within a
recursive function's body, which enumeration does not enumerate. -/
def recursiveIndexRead : Name := .str .anonymous "[] in a recursion"

/- The functions that `e` applies, including type-membership dependencies. -/
mutual
/-- Include the bodies that type membership evaluates, with recursion cycles
visited once. These hidden dependencies share the ordinary function slots. -/
partial def Eval.Ex.appsIn (sp : Spec) (seenFns seenTypes : NameSet) (e : Ex) : Array Name :=
  let nested := e.children.flatMap (Eval.Ex.appsIn sp seenFns seenTypes)
  match e with
  | .app f _ =>
    match sp.defs.find? f with
    | some (_, body, _) =>
      if seenFns.contains f then nested else
      let inner := body.appsIn sp (seenFns.insert f) seenTypes
      -- An index within a recursion is the Lean-hosted front end's to
      -- evaluate by Lean's own default, so neither front end enumerates it.
      let inner := if sp.recDefs.contains f then inner.map fun n => if n == indexRead then recursiveIndexRead else n else inner
      nested ++ inner
    | none => #[f] ++ nested
  | .typed t _ _ => nested ++ typeAppsIn sp seenFns seenTypes t
  | .quant _ _ _ _ _ tys _ => nested ++ tys.flatMap (typeAppsIn sp seenFns seenTypes)
  | .table _ _ (some u) | .match _ _ _ _ (some u) _ => #[u] ++ nested
  -- `[][0]` is the unspecified value itself, as a table's is.
  | .index (.seqLit #[]) (.lit (.int 0)) _ u => #[u]
  -- After its parts, as the hosted front end's `Enum.nthOr` reads it.
  | .index _ _ _ u => nested ++ #[u, indexRead]
  | _ => nested

partial def typeAppsIn (sp : Spec) (seenFns seenTypes : NameSet) (t : Fren.Core.PTy) : Array Name :=
  let own := t.invariants.flatMap fun i =>
    if seenFns.contains i.predicate then #[] else
    match sp.defs.find? i.predicate with
    | some (_, body, _) => body.appsIn sp (seenFns.insert i.predicate) seenTypes
    | none => #[i.predicate]
  let nested := (t.parts ++ t.elems).flatMap (typeAppsIn sp seenFns seenTypes)
  let path? := match t.ty with
    | .record p _ | .enum p _ | .newtype p _ => some p
    | _ => none
  let fields := path?.map fun path =>
    if seenTypes.contains path then #[] else
    ((sp.shapes.find? path).map fun shape => (shape.inst t.parts).parts.flatten.flatMap
      (typeAppsIn sp seenFns (seenTypes.insert path))).getD #[]
  own ++ nested ++ fields.getD #[]
end

partial def Eval.Ex.appsOf (e : Ex) (sp : Spec) : Array Name := e.appsIn sp {} {}

/-- Whether `u` names the unspecified value of a type (`unspecifiedFn`). -/
def isUnspecified (u : Name) : Bool := match u with
  | .str .anonymous s => s.startsWith "[][0]"
  | _ => false

/-- The value `v` of the type `ty`, as the evaluator has it. -/
partial def evalOf (sp : Spec) (ty : VTy) (v : EVal) : Val :=
  match ty, v with
  | .abstract s, .abs k => .abs s k
  | .string, .str s => .str s
  | .set t, .set xs => Val.setOf (xs.toArray.map (evalOf sp t))
  | .seq t, .seq xs => .seq (xs.toArray.map (evalOf sp t))
  | .rel a b, .set xs => Val.setOf (xs.toArray.map fun
      | .pair x y => .pair (evalOf sp a x) (evalOf sp b y)
      | _ => .bool false)
  | .newtype _ t, .ctor _ [v] => evalOf sp t v
  | .data p args, .ctor idx xs =>
    let fields := ((sp.data.find? p).bind (·.ctors[idx]?)).map (·.fields.map fun (_, t) => t.subst args)
    .ctor p idx ((xs.toArray.zip (fields.getD #[])).map fun (v, t) => evalOf sp t v)
  | _, v => match v.toPVal? with
    | some pv => sp.ofPVal ty pv
    | none => .bool false

/-- Enumerates the checks of `c`, the evaluator's `ec`, that its evidence
sets to enumeration, of the kinds `kinds` (`Reqs/Check#checking-by-enumeration`).
`subject` is `c` as messages show it. -/
def enumerateComp (sp : Spec) (ec : Eval.Comp) (c : CComp) (kinds : Array Fren.Core.CheckKind) (subject : String)
    (t : Fren.Core.Tested := c.enumerated) (testing : Bool := false) :
    Except Fren.Core.Msg Enumerated := do
  let n := c.enumSize
  let paired := pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start)) (c.tables.map (·.2.2.1.start))
  let (core, ks) := paired.only t kinds
  let (ecomp, sourceAtoms) := core.atoms
  -- Shape enumeration is only an optimization. General named invariants
  -- remain semantic facts, including those nested inside data/collections.
  let domains := c.vars.filterMap fun v =>
    if v.defn?.isSome || v.fact?.isNone then none else
    some (v.role == .output, Fm.atoms #[{ label := v.name, pfx := .anonymous, e := .typed v.ptype #[] (.var v.name) }])
  let atoms := sourceAtoms ++ domains.map (fun (_, formula) => ("", formula))
  let facts := domains.zipIdx.map fun (_, i) => EF.atom (sourceAtoms.size + i)
  let outputFacts := domains.zipIdx.filterMap fun ((output, _), i) => if output then some (EF.atom (sourceAtoms.size + i)) else none
  let some exprs := atoms.mapM (·.2.exprs?)
    | throw (Fren.Core.Msg.internal s!"the evaluator does not know the meaning of a formula of `{Fren.Core.showComp c.path}`")
  -- And the definitions of the defined outputs, which the atoms read.
  let all := exprs.flatten ++ ec.defs.map fun (_, e) => ((.anonymous : Name), e)
  -- No uninterpreted function whose contract has a postcondition
  -- (`contractBlocker?`, `check::contract_blocker`).
  let apps := all.flatMap (fun e => e.2.appsOf sp)
  -- The uninterpreted functions, whose interpretations are enumerated, but
  -- not of one whose contract has a postcondition, which constrains them.
  let fnNames := apps.foldl (init := #[]) fun acc f =>
    if isUnspecified f || f == indexRead || f == recursiveIndexRead || acc.contains f then acc else acc.push f
  -- Nor of a generic function without a body, whose instances are
  -- functions of their own, the first in declaration order.
  let generics := fnNames.filterMap fun f => (sp.instanceOf.find? f).orElse fun _ =>
    let g := match f with
      | .str p "<?>" => p
      | f => f
    if sp.generics.any (·.1 == g) then some g else none
  if let some (g, _, _, _) := sp.generics.find? (generics.contains ·.1) then
    throw (notEnumerableMsg subject (genericNotEnumerable g))
  if let some f := contractBlocker? fnNames fun f => ((sp.contracts.find? f).map (·.2.2.size)).getD 0 then
    throw (notEnumerableMsg subject (contractNotEnumerable f))
  if let some f := fnNames.find? (fun f => !(sp.funs.contains f)) then
    throw (notEnumerableMsg subject s!"the evaluator does not know the function `{Fren.Core.showPath f}` used by a type invariant")
  let funs : Array FunVar := fnNames.filterMap fun f => (sp.funs.find? f).map fun (ps, r) =>
    { name := f, params := ps.map fun t => Fren.Core.PTy.plain (t.core sp)
      result := (sp.results.find? f).getD (Fren.Core.PTy.plain (r.core sp)) }
  if let some f := funs.find? (fun f => needsSemanticFilter sp.shapes.find? f.result) then
    throw (notEnumerableMsg subject s!"the result type of `{Fren.Core.showPath f.name}` has a named invariant that cannot be enumerated as an unconstrained function table")
  -- A quantifier without a domain ranges over its type's values up to the
  -- bound (`Reqs/Check#quantifiers-up-to-the-bound`).
  let quantified := all.flatMap (·.2.quantifiedTypes)
  for pt in quantified do
    let shape? : Except String Shape := Fren.Core.Enumeration.shapeOf sp.shapes.find? n pt
    match shape? with
    | .error why => throw (notEnumerableMsg subject (notEnumerableWhy none why))
    | .ok shape =>
      if shape.estimate n > maxBehaviours then throw (quantifiedTooManyMsg subject n)
  if apps.contains recursiveIndexRead then
    throw (notEnumerableMsg subject recursiveIndexWhy)
  -- The hidden slots: each type whose unspecified value is read, in the
  -- order of the atoms.
  let hiddenNames := apps.foldl (init := #[]) fun acc u => if !isUnspecified u || acc.contains u then acc else acc.push u
  let hidden := hiddenNames.filterMap fun u => (sp.funs.find? u).map fun (_, t) => (u, Fren.Core.PTy.plain (t.core sp))
  let defined := c.vars.filter (·.defn?.isSome) |>.map (·.name)
  let vars := c.vars.map fun v =>
    ({ sig := { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
       -- A variable whose type brings no constraint ranges over its type
       -- without patterns (`Reqs/Check#enumerable-types`).
       pty := if v.fact?.isSome then v.ptype else Fren.Core.PTy.plain v.ptype.ty
       defined := v.defn?.isSome } : SlotVar)
  let (space, values, shapes, fslots) ← match spaceOf sp.shapes.find? n vars hidden funs (if testing then testCount else 0) (hash c.path) with
    | .ok r => pure r
    | .error (x, why) =>
      throw (if why == tooManyMarker then tooManyMsg subject (maxBehaviours + 1) n (estimated := true) else notEnumerableMsg subject (notEnumerableWhy x why))
  let determinism := ks.contains .determinism && ecomp.vars.any (·.isDet)
  let count := space.behaviours determinism fslots
  if !withinLimit count then throw (tooManyMsg subject count n)
  -- Each slot's values, as the evaluator has them.
  let flat := sp.flatVars ec
  let tyOf (x : Name) : VTy :=
    let base := if x.isStr && x.getString!.endsWith "'" then Name.mkStr x.getPrefix (x.getString!.dropEnd 1).toString else x
    match (flat.find? (·.name == base)) with
    | some v => v.ty
    | none => ((sp.funs.find? x).map (·.2)).getD .bool
  let vals : Array (Array Val) := (space.names.zip values).map fun (x, vs) => vs.map (evalOf sp (tyOf x))
  -- Each function's parameters' and results' values, as the evaluator has them.
  let fvals := fslots.map fun f =>
    let (ps, r) := (sp.funs.find? f.name).getD (#[], .bool)
    (f, (f.params.zip ps).map (fun (vs, t) => vs.map (evalOf sp t)), f.results.map (evalOf sp r))
  let slotOf : Std.HashMap Name Nat := space.names.zipIdx.foldl (init := {}) fun m (x, i) => m.insert x i
  let defs := ec.defs
  let defOf : Std.HashMap Name Ex := defs.foldl (init := {}) fun m (x, e) => m.insert x e
  -- The value of each name in `env`: a slot's, or a defined output's,
  -- computed from its definition.
  -- A function's value at arguments within its domain is its table's; at
  -- any others, its first result, as one interpretation extends it.
  let apply (env : Array Nat) (f : FunSlot) (ps : Array (Array Val)) (rs : Array Val) (args : Array Val) : Option Val :=
    let idx := (ps.zip args).map fun (vs, a) => (vs.findIdx? (· == a)).getD vs.size
    let table := f.tables[env[f.slot]!]?.getD 0
    match tupleIndex (ps.map (·.size)) idx with
    | some pos => rs[tableEntry rs.size table pos]?
    | none => rs[0]?
  -- An index out of range is its element type's unspecified value, the
  -- hidden slot's, as a table where no row holds is.
  let interp (env : Array Nat) : Interp :=
    { fn := fun f args => match fvals.find? (·.1.name == f) with
        | some (fs, ps, rs) => apply env fs ps rs args
        | none => slotOf[f]?.bind fun i => vals[i]?.bind (·[env[i]!]?)
      outOfRange := fun u => slotOf[u]?.bind fun i => vals[i]?.bind (·[env[i]!]?)
      defs := sp.defs.find?, shapes := sp.shapes.find?, recDefs := sp.recDefs.find?
      defined := (defOf[·]?), definedCount := defs.size + 1
      domain := fun pt => do
        let shape ← (Fren.Core.Enumeration.shapeOf sp.shapes.find? n pt).toOption
        let ty := VTy.ofCore pt.ty
        return ((shape.ordered n).toArray.map fun (v, _) => evalOf sp ty v, shape.exhausted n) }
  let rec look (env : Array Nat) (fuel : Nat) (x : Name) : Option Val :=
    match slotOf[x]? with
    | some i => (vals[i]?.bind (·[env[i]!]?))
    | none => match fuel, defs.find? (·.1 == x) with
      | f + 1, some (_, e) => e.eval (interp env) (look env f)
      | _, _ => none
  let fuel := defs.size + 1
  let evalFm (f : Fm) (env : Array Nat) : Bool := Fm.holds (interp env) (look env fuel) f
  -- The same, with every index out of range unknown: where a value is
  -- known this way, it is the same in every interpretation of them.
  let strict (env : Array Nat) : Interp := { interp env with outOfRange := fun _ => none }
  let rec lookStrict (env : Array Nat) (fuel : Nat) (x : Name) : Option Val :=
    match slotOf[x]? with
    | some i => (vals[i]?.bind (·[env[i]!]?))
    | none => match fuel, defs.find? (·.1 == x) with
      | f + 1, some (_, e) => e.eval (strict env) (lookStrict env f)
      | _, _ => none
  let unknownFm (f : Fm) (env : Array Nat) : Bool :=
    (Fm.value? (strict env) (lookStrict env fuel) f).isNone && (Fm.value? (interp env) (look env fuel) f).isSome
  -- The slots that each atom reads: its variables', and those of the
  -- definitions of the defined outputs it mentions.
  let rec reads (fuel : Nat) (x : Name) : Array Nat :=
    match slotOf[x]?, fuel with
    | some i, _ => #[i]
    | none, f + 1 => ((defs.find? (·.1 == x)).map fun (_, e) => (e.varsOf.flatMap (reads f)) ++
        ((e.appsOf sp).filterMap (slotOf[·]?))).getD #[]
    | none, 0 => #[]
  let atomSlots := exprs.map fun es => es.foldl (init := #[]) fun acc (pfx, e) =>
    ((e.varsOf.flatMap fun v => reads fuel (pfx ++ v)) ++ (e.appsOf sp).filterMap (slotOf[·]?)).foldl
      (fun a s => if a.contains s then a else a.push s) acc
  let atomDefs := exprs.map fun es => es.foldl (init := #[]) fun acc (pfx, e) =>
    (e.varsOf.map (pfx ++ ·)).foldl (fun a v => if defined.contains v && !a.contains v then a.push v else a) acc
  -- Whether a defined output's definition has an index, through the
  -- definitions it mentions; and each atom, a type's facts too, through
  -- those and the bodies it applies.
  let rec defIndexed (fuel : Nat) (x : Name) : Bool :=
    match fuel, defs.find? (·.1 == x) with
    | f + 1, some (_, e) => (e.appsOf sp).contains indexRead || e.varsOf.any (defIndexed f)
    | _, _ => false
  let atomIndexed := exprs.map fun es => es.any fun (pfx, e) =>
    (e.appsOf sp).contains indexRead || e.varsOf.any fun v => defIndexed fuel (pfx ++ v)
  let ats : Atoms := {
    slots := atomSlots, defs := atomDefs
    eval := fun k env => evalFm (atoms[k]!.2) env
    -- Only a quantifier up to the bound leaves an atom's truth unknown.
    known := fun k env => (Fm.value? (interp env) (look env fuel) atoms[k]!.2).isSome
    total := !mayBeUnknown (all.map (·.2.hasQuantifier))
    sameDefined := fun d e₁ e₂ => look e₁ fuel d == look e₂ fuel d
    sameKnown := fun d e₁ e₂ => (look e₁ fuel d).isSome && (look e₂ fuel d).isSome
    defSlots := fun d => (reads fuel d).foldl (fun a s => if a.contains s then a else a.push s) #[]
    readsIndex := fun k => atomIndexed[k]!
    defReadsIndex := defIndexed fuel
    unknown := fun k env => atomIndexed[k]! && unknownFm (atoms[k]!.2) env
    defUnknown := fun d env => defIndexed fuel d && (lookStrict env fuel d).isNone && (look env fuel d).isSome }
  let render (s j : Nat) : String := ((vals[s]?.bind (·[j]?)).map (·.showAs sp (tyOf space.names[s]!))).getD "?"
  let defValue (d : Name) (env : Array Nat) : Option String := (look env fuel d).map (·.showAs sp (tyOf d))
  -- The variant of each value of a slot whose type is an enumeration, as
  -- the solver's backend names it (`variantOfValue`).
  let variantOf (s j : Nat) : Option Fren.Core.Variant := do
    let .ctor p idx _ ← vals[s]?.bind (·[j]?) | none
    let .data _ _ := tyOf space.names[s]! | none
    let d ← sp.data.find? p
    if d.isRecord then none
    let k ← d.ctors[idx]?
    return { name := s!"{p.getString!}::{k.name}", arity := k.fields.size }
  -- An unknown membership must not remove a world and produce a vacuous
  -- proof. Check domain evaluation before entering the Boolean backend.
  let domainSlots := facts.flatMap (fun f => (f.slots space ats).toArray) |>.toList.eraseDups
  for assignment in space.fairList (Array.replicate space.names.size 0) domainSlots do
    let env := setAll (Array.replicate space.names.size 0) domainSlots assignment
    for (_, formula) in domains do
      let some es := formula.exprs? | throw (notEnumerableMsg subject "a type invariant is unsupported")
      if es.any (fun (_, e) => (e.eval (interp env) (look env fuel)).isNone) then
        throw (notEnumerableMsg subject "the evaluator cannot decide a type invariant in an enumerated interpretation")
  let ecomp := { ecomp with typesInterpreted := ecomp.typesInterpreted || !apps.isEmpty }
  let raw := Id.run (Fren.Core.checkComp (m := Id) (fun _ => Fren.Core.Enumeration.backend space ats (fun s j => pure (render s j)) (fun d e => pure (defValue d e)) (if testing then some (hash c.path) else none) variantOf facts outputFacts) ecomp ks)
  let ownOutputs := space.outputs
  let exact := exhaustedAll shapes n (List.range space.names.size).toArray && fslots.all (·.exhausted)
  let outputsExact := exhaustedAll shapes n ownOutputs
  return { results := raw.map (classify n exact outputsExact (indexed := atomIndexed.any id)), bound := n, exact }

end FrenCli
