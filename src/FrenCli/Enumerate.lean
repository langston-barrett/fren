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

/-- The variables that `e` reads, by name. -/
partial def Eval.Ex.varsOf (e : Ex) : Array Name :=
  match e with
  | .var n => #[n]
  | _ => e.children.flatMap (·.varsOf)

/-- The functions that `e` applies, uninterpreted or an interpretation's
unspecified value. -/
partial def Eval.Ex.appsOf (e : Ex) : Array Name :=
  match e with
  | .app f args => #[f] ++ args.flatMap (·.appsOf)
  | .table _ _ (some u) => #[u] ++ e.children.flatMap (·.appsOf)
  | .match _ _ _ _ (some u) _ => #[u] ++ e.children.flatMap (·.appsOf)
  | _ => e.children.flatMap (·.appsOf)

/-- Whether `u` names the unspecified value of a type (`unspecifiedFn`). -/
def isUnspecified (u : Name) : Bool := match u with
  | .str .anonymous s => s.startsWith "[][0]"
  | _ => false

/-- The value `v` of the type `ty`, as the evaluator has it. -/
def evalOf (sp : Spec) (ty : VTy) (v : EVal) : Val :=
  match ty, v with
  | .abstract s, .abs k => .abs s k
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
  let (ecomp, atoms) := core.atoms
  let some exprs := atoms.mapM (·.2.exprs?)
    | throw (Fren.Core.Msg.internal s!"the evaluator does not know the meaning of a formula of `{Fren.Core.showComp c.path}`")
  -- And the definitions of the defined outputs, which the atoms read.
  let all := exprs.flatten ++ ec.defs.map fun (_, e) => ((.anonymous : Name), e)
  -- No uninterpreted function, nor unbounded quantifier (`check::enumerable`).
  let apps := all.flatMap (·.2.appsOf)
  -- The uninterpreted functions, whose interpretations are enumerated, but
  -- not of one with a contract, which constrains them.
  let fnNames := apps.foldl (init := #[]) fun acc f => if isUnspecified f || acc.contains f then acc else acc.push f
  -- Nor of a generic function without a body, whose instances are
  -- functions of their own, the first in declaration order.
  let generics := fnNames.filterMap fun f => (sp.instanceOf.find? f).orElse fun _ =>
    if sp.generics.any (·.1 == f) then some f else none
  if let some (g, _, _, _) := sp.generics.find? (generics.contains ·.1) then
    throw (notEnumerableMsg subject (genericNotEnumerable g))
  if let some f := fnNames.find? (sp.contracts.contains ·) then
    throw (notEnumerableMsg subject s!"it applies the uninterpreted function `{Fren.Core.showComp f}`, which has a contract")
  let funs : Array FunVar := fnNames.filterMap fun f => (sp.funs.find? f).map fun (ps, r) =>
    { name := f, params := ps.map fun t => Fren.Core.PTy.plain (t.core sp)
      result := (sp.results.find? f).getD (Fren.Core.PTy.plain (r.core sp)) }
  if all.any (·.2.unbounded) then
    throw (notEnumerableMsg subject "it has an unbounded quantifier")
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
      throw (notEnumerableMsg subject (notEnumerableWhy x why))
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
  let interp (env : Array Nat) : Interp :=
    { fn := fun f args => match fvals.find? (·.1.name == f) with
        | some (fs, ps, rs) => apply env fs ps rs args
        | none => slotOf[f]?.bind fun i => vals[i]?.bind (·[env[i]!]?)
      shapes := sp.shapes.find? }
  let rec look (env : Array Nat) (fuel : Nat) (x : Name) : Option Val :=
    match slotOf[x]? with
    | some i => (vals[i]?.bind (·[env[i]!]?))
    | none => match fuel, defs.find? (·.1 == x) with
      | f + 1, some (_, e) => e.eval (interp env) (look env f)
      | _, _ => none
  let fuel := defs.size + 1
  let evalFm (f : Fm) (env : Array Nat) : Bool := Fm.holds (interp env) (look env fuel) f
  -- The slots that each atom reads: its variables', and those of the
  -- definitions of the defined outputs it mentions.
  let rec reads (fuel : Nat) (x : Name) : Array Nat :=
    match slotOf[x]?, fuel with
    | some i, _ => #[i]
    | none, f + 1 => ((defs.find? (·.1 == x)).map fun (_, e) => (e.varsOf.flatMap (reads f)) ++
        (e.appsOf.filterMap (slotOf[·]?))).getD #[]
    | none, 0 => #[]
  let atomSlots := exprs.map fun es => es.foldl (init := #[]) fun acc (pfx, e) =>
    ((e.varsOf.flatMap fun v => reads fuel (pfx ++ v)) ++ e.appsOf.filterMap (slotOf[·]?)).foldl
      (fun a s => if a.contains s then a else a.push s) acc
  let atomDefs := exprs.map fun es => es.foldl (init := #[]) fun acc (pfx, e) =>
    (e.varsOf.map (pfx ++ ·)).foldl (fun a v => if defined.contains v && !a.contains v then a.push v else a) acc
  let ats : Atoms := {
    slots := atomSlots, defs := atomDefs
    eval := fun k env => evalFm (atoms[k]!.2) env
    sameDefined := fun d e₁ e₂ => look e₁ fuel d == look e₂ fuel d
    defSlots := fun d => (reads fuel d).foldl (fun a s => if a.contains s then a else a.push s) #[] }
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
  let raw := Id.run (Fren.Core.checkComp (m := Id) (fun _ => Fren.Core.Enumeration.backend space ats (fun s j => pure (render s j)) (fun d e => pure (defValue d e)) (if testing then some (hash c.path) else none) variantOf) ecomp ks)
  let ownOutputs := space.outputs
  let exact := exhaustedAll shapes n (List.range space.names.size).toArray && fslots.all (·.exhausted)
  let outputsExact := exhaustedAll shapes n ownOutputs
  return { results := raw.map (classify n exact outputsExact), bound := n, exact }

end FrenCli
