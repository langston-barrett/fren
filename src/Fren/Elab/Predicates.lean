-- keep-sorted start
import Fren.Elab.Declarations
import Fren.Elab.FunctionSupport
import Fren.Elab.Terms
-- keep-sorted end

/-! # Hosted elaboration: predicates -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- Source Boolean alternatives over the same closed variables as a clause.
Leading guards are distributed into each member, retaining exact owner
meaning; diagnostic-only translation records no duplicate obligations. -/
partial def clauseBranchGroups (cx : ExprCtx) (owner : Name) (expression : Syntax)
    (fvs : Array Expr) (subst : Expr → Expr := id) : TermElabM (Array (Core.BranchGroup Expr)) := do
  let rec strip (e : Syntax) (wrappers : Array Syntax) : TermElabM (Array (Core.BranchGroup Expr)) := do
    let e := unparen e
    if isBooleanGuard e || e.isOfKind ``Lang.letExpr then
      return ← strip e[3] (wrappers.push e)
    let group? := (booleanBlockView e).orElse fun _ =>
      if isBinOp e "iff" then some ("iff", #[(none, e[0]), (none, e[2])]) else none
    let some (op, members) := group? | return #[]
    if op != "or" && op != "iff" && op != "one" then return #[]
    if op == "iff" && members.size <= 1 then return #[]
    let saved ← getLocal
    try
      let source := (← getFileMap).source
      let members ← members.mapIdxM fun i (label, body) => do
        let segment := label.map (fun label => label.getId.toString (escape := false)) |>.getD (toString (i + 1))
        let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString (escape := false) ++ "." ++ segment)
        let guarded := wrappers.foldr (fun wrapper body => wrapper.setArg 3 body) body
        let value ← elabProp (← toTerm { cx with noteIndexes := false } guarded)
        let formula ← mkLambdaFVars fvs (subst value)
        let text := exactText body
        return { name, formula
                 range? := some (charRange source (label.getD (unparen body))), text : Core.BranchMember Expr }
      -- Recover activation from the already elaborated wrapper, avoiding a
      -- second elaboration of generated contract lets with hygienic binders.
      let guard? ← if !wrappers.any isBooleanGuard then pure none else do
        let wrapped ← if let some first := members[0]? then pure (first.formula.beta fvs) else do
          let original := wrappers.foldr (fun wrapper body => wrapper.setArg 3 body) e
          pure (subst (← elabProp (← toTerm { cx with noteIndexes := false } original)))
        let first ← zetaReduce wrapped
        let rec conditions (remaining : Nat) (body : Expr) : MetaM (List Expr) := do
          if remaining == 0 then return []
          if let .forallE _ condition tail _ := body.consumeMData then
            if !tail.hasLooseBVars && (← isProp condition) then
              return condition :: (← conditions (remaining - 1) tail)
          return []
        let active ← conditions (wrappers.filter isBooleanGuard).size first
        pure (some (← mkLambdaFVars fvs (mkAndN active)))
      return #[{ owner, guard?, kind := if op == "or" then .disjunction else if op == "one" then .exactlyOne else .equivalence, members }]
    finally modifyLocal fun _ => saved
  strip expression #[]

open Lang in
/-- Observe raw members only under their source evaluation guards. This
metadata is evaluated in the actual primary model, not by a fresh query. -/
partial def clauseMemberGroups (cx : ExprCtx) (owner : Name) (expression : Syntax)
    (fvs : Array Expr) (subst : Expr → Expr := id) : TermElabM (Array (Core.MemberGroup Expr)) := do
  let rec strip (e : Syntax) (wrappers : Array Syntax) (wanted : Bool) : TermElabM (Array (Core.MemberGroup Expr)) := do
    let e := unparen e
    if isBooleanGuard e || e.isOfKind ``Lang.letExpr then return ← strip e[3] (wrappers.push e) wanted
    if e.getNumArgs == 2 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "not" then
      return ← strip e[1] wrappers (!wanted)
    let group? := booleanBlockView e
    let some (op, members) := group? | return #[]
    let saved ← getLocal
    try
      let source := (← getFileMap).source
      let mut out := #[]
      for (label, body) in members, i in [0:members.size] do
        let mut conditions : Array Syntax := #[]
        for previous in [0:i] do
          if op == "iff" && previous == 0 then continue
          let previousBody := members[previous]!.2
          let condition ← if op == "or" then `(fren_expr| not $(⟨previousBody⟩):fren_expr)
            else if op == "iff" then `(fren_expr| $(⟨members[0]!.2⟩):fren_expr iff $(⟨previousBody⟩):fren_expr)
            else pure (⟨previousBody⟩ : TSyntax `fren_expr)
          conditions := conditions.push condition
        let mut guard ← lowerBooleanBlock "and" (conditions.map (none, ·))
        if op == "one" then
          let prior := members.extract 0 i
          let atMostOne ← lowerBooleanBlock "one" prior
          let noneTrue ← lowerBooleanBlock "and" (← prior.mapM fun (_, e) => do
            let neg ← `(fren_expr| not $(⟨e⟩):fren_expr)
            pure (none, neg.raw))
          guard ← `(fren_expr| $(⟨noneTrue⟩):fren_expr or $(⟨atMostOne⟩):fren_expr)
        let skipped := op == "iff" && members.size <= 1
        if skipped then guard ← `(fren_expr| false)
        let mut value : Syntax ← if skipped then do `(fren_expr| true) else pure body
        for wrapper in wrappers.reverse do
          value := wrapper.setArg 3 value
          if wrapper.isOfKind ``Lang.letExpr then guard := wrapper.setArg 3 guard
          else
            let condition := wrapper[1]
            guard ← if wrapper[0].getAtomVal.trimAscii.toString == "unless" then
                `(fren_expr| not $(⟨condition⟩):fren_expr and $(⟨guard⟩):fren_expr)
              else `(fren_expr| $(⟨condition⟩):fren_expr and $(⟨guard⟩):fren_expr)
        let raw ← elabProp (← toTerm { cx with noteIndexes := false } value)
        let reachable ← elabProp (← toTerm { cx with noteIndexes := false } guard)
        let raw ← mkLambdaFVars fvs (subst raw)
        let reachable ← mkLambdaFVars fvs (subst reachable)
        let segment := label.map (·.getId.toString) |>.getD (toString (i + 1))
        out := out.push { name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString ++ "." ++ segment), formula := raw
                          valueFormula? := some raw, evaluationGuard? := some reachable
                          range? := some (charRange source (label.getD (unparen body))), text := exactText body : Core.BranchMember Expr }
      return #[{ owner, op, wanted, members := out }]
    finally modifyLocal fun _ => saved
  strip expression #[] true

/-- Root source conjunctions of predicates, with leading wrappers kept
on each leaf. Ordinary conjunctions inside a leaf are not reinterpreted. -/
partial def predicateConjunction (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then predicateConjunction e[3]
  else (booleanBlockView e).any (·.1 == "and")

partial def predicateLeafSources (owner : Name) (source : Syntax) : TermElabM (Array (Name × Syntax × Syntax)) := do
  let e := unparen source
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then
    return (← predicateLeafSources owner e[3]).map fun (name, ref, body) => (name, ref, e.setArg 3 body)
  if let some ("and", members) := booleanBlockView e then
    let labels := members.filterMap (·.1)
    if let some k := (Core.repeatsAt (labels.map (·.getId)))[0]? then
      throwErrorAt labels[k]! "a Boolean block repeats label `{labels[k]!.getId}`"
    for label in labels do
      discard (segName label)
      liftMsg label (Core.checkNoBang label.getId)
    let mut out := #[]
    for (label, body) in members, i in [0:members.size] do
      let segment := label.map (·.getId.toString (escape := false)) |>.getD (toString (i + 1))
      let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString (escape := false) ++ "." ++ segment)
      let leaves ← predicateLeafSources name body
      out := out ++ leaves.map fun (n, ref, value) => (n, if n == name then label.getD ref else ref, value)
    return out
  return #[(owner, source, source)]

partial def predicateNamedRoot (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  let e := unparen e
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then return ← predicateNamedRoot cx e[3]
  if !e.isOfKind ``Lang.appExpr then return false
  let segs := pathSegs e[0]
  if let .ok (.item { kind := .fnItem, path, .. }) := (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing then
    return ((← getState).defined.find? path).any (fun info => !info.namedMembers.isEmpty || !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty)
  return false

/-- Metadata is elaborated again in the definition's own lexical scope and
closed over typed parameters. Callers instantiate lambdas, never substitute
raw source identifiers into their own scope. -/
def predicateMetadata (scope : Name) (vars : Array Var)
    (functions : Array (Name × Core.FnTy × Expr × Name)) (body : Syntax) :
    TermElabM (Array PredicateMemberInfo × Array (Core.BranchGroup Expr) × Array (Core.MemberGroup Expr)) := do
  let saved ← getLocal
  try
    withLocalDeclsD (functions.map fun p => (p.1, fun _ => pure p.2.2.1)) fun fnFvs =>
    withLocalDeclsD (vars.map fun v => (v.name, fun _ => pure v.type)) fun fvs => do
      let all := fvs ++ fnFvs
      let cx : ExprCtx := {
        modName := scope, vars, insts := #[], place := .prop
        fnParams := functions.map fun p => (p.1, p.2.1, (⟨(mkIdent p.1).raw⟩ : Term)) }
      let mut members := #[]
      if predicateConjunction body || (← predicateNamedRoot cx body) then
        for (name, ref, expression) in ← predicateLeafSources .anonymous body do
          discard (takeIndexes all)
          let statement ← elabProp (← toTerm cx expression)
          let sites ← takeIndexes all
          let branchGroups ← clauseBranchGroups cx name expression all
          let memberGroups ← clauseMemberGroups cx name expression all
          members := members.push { name, ref, body := ← mkLambdaFVars all statement, sites, branchGroups, memberGroups }
      let branchGroups ← clauseBranchGroups cx .anonymous body all
      let memberGroups ← clauseMemberGroups cx .anonymous body all
      return (members, branchGroups, memberGroups)
  finally modifyLocal fun _ => saved

/-- Source application occurrence identities, before typed expansion. -/
partial def predicateSourceApps (cx : ExprCtx) (source : Syntax) : TermElabM (Array (Name × Nat)) := do
  let mut out := #[]
  if source.isOfKind ``Lang.appExpr then
    let segs := pathSegs source[0]
    if !(segs.size == 1 && (cx.fnParam? segs[0]!.getId).isSome) then
      if let .ok (.item { kind := .fnItem, path, .. }) := (← getState).table.resolvePath cx.modName (segs.map (·.getId)) cx.shadowing then
        out := out.push (path, (source.getPos?.getD 0).byteIdx)
  for child in source.getArgs do
    out := out ++ (← predicateSourceApps cx child)
  return out

/-- The defined predicate at a typed root, after Bool-to-Prop coercion. -/
def predicateApplication? (state : State) (e : Expr) : Option (DefinedInfo × Array Expr) := do
  let e := e.consumeMData
  let call := if e.isAppOfArity ``Eq 3 && e.getAppArgs[0]!.isConstOf ``Bool && e.getAppArgs[2]!.isConstOf ``Bool.true then
      e.getAppArgs[1]! else e
  let declaration ← call.getAppFn.constName?
  let (_, info) ← state.defined.toList.find? (fun (_, d) => d.decl == declaration && d.result == .bool)
  if call.getAppNumArgs != info.uses.size + info.nParams then none else
    some (info, call.getAppArgs)

partial def predicateCallPolarity? (state : State) (body : Expr) (wanted : Bool := true) :
    Option (DefinedInfo × Array Expr × Bool) :=
  let body := body.consumeMData
  if body.isAppOfArity ``Not 1 then predicateCallPolarity? state body.appArg! (!wanted)
  else (predicateApplication? state body).map fun (info, arguments) => (info, arguments, wanted)

def predicateInstance (info : DefinedInfo) (arguments : Array Expr) (body : Expr) : Expr :=
  (replaceUses info.uses (arguments.extract 0 info.uses.size) body).beta (arguments.extract info.uses.size)

/-- Typed unfolding of named predicate conjunctions. Free constants keep
the defining module's meaning, and each call occurrence has its own path. -/
partial def expandPredicateConstraint (cx : ExprCtx) (prop : PropInfo) (source : Syntax) (fvs : Array Expr) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
  let state ← getState
  let applications ← predicateSourceApps cx source
  let wrap (guards : Array Expr) (body : Expr) : Expr :=
    guards.foldr (fun condition body => .forallE `condition condition body .default) body
  let rec contains (body : Expr) : MetaM Bool := do
    let body := body.consumeMData
    if let some (info, _, _) := predicateCallPolarity? state body then return !info.namedMembers.isEmpty || !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty
    if body.isAppOfArity ``And 2 then return (← contains body.getAppArgs[0]!) || (← contains body.getAppArgs[1]!)
    if let .forallE _ condition tail _ := body then
      if !tail.hasLooseBVars && (← isProp condition) then return ← contains tail
    return false
  let rec expand (body : Expr) (written : Syntax) (owner : Name) (guards : Array Expr) (label : Syntax) :
      StateT (Std.TreeMap Name Nat Name.quickCmp) TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
    let body := body.consumeMData
    if let .forallE _ condition tail _ := body then
      if !tail.hasLooseBVars && (← isProp condition) then
        return ← expand tail (if isBooleanGuard (unparen written) then (unparen written)[3] else written) owner (guards.push condition) label
    if prop.kind != .cover && body.isAppOfArity ``And 2 && (← contains body) then
      let leftSource := if isBinOp (unparen written) "and" then (unparen written)[0] else written
      let rightSource := if isBinOp (unparen written) "and" then (unparen written)[2] else written
      let left ← expand body.getAppArgs[0]! leftSource (Name.mkSimple (owner.toString (escape := false) ++ ".1")) guards leftSource
      let right ← expand body.getAppArgs[1]! rightSource (Name.mkSimple (owner.toString (escape := false) ++ ".2")) guards rightSource
      return (left.1 ++ right.1, left.2.1 ++ right.2.1, left.2.2 ++ right.2.2)
    if let some (info, arguments, wanted) := predicateCallPolarity? state body then
      if prop.kind != .cover && wanted && !info.namedMembers.isEmpty then
        let seen : Std.TreeMap Name Nat Name.quickCmp ← get
        let next := seen.getD info.path 0 + 1
        set (seen.insert info.path next : Std.TreeMap Name Nat Name.quickCmp)
        let same := applications.filter (·.1 == info.path)
        let index := ((same.findIdx? (fun (_, pos) => pos == (written.getPos?.getD 0).byteIdx)).map (· + 1)).getD next
        let occurrence := Core.showPath info.path ++ s!"@{index}"
        let prefixName := owner.toString (escape := false) ++ "." ++ occurrence
        let callOccurrences ← get
        set ({} : Std.TreeMap Name Nat Name.quickCmp)
        let mut props := #[]
        let mut declarations := #[]
        let mut sites := #[]
        for member in info.namedMembers do
          let name := Name.mkSimple (prefixName ++ (if member.name.isAnonymous then "" else "." ++ member.name.toString (escape := false)))
          let instantiated := wrap guards (predicateInstance info arguments member.body)
          let decl := prop.decl ++ name
          let trigger ← liftM <| do
            let rec top (e : Expr) (conditions : Array Expr) : MetaM (Array Expr) := do
              if let .forallE _ condition tail _ := e.consumeMData then
                if !tail.hasLooseBVars && (← isProp condition) then return ← top tail (conditions.push condition)
              return conditions
            let conditions ← top instantiated #[]
            if conditions.isEmpty then pure none else some <$> mkLambdaFVars fvs (mkAndN conditions.toList)
          let changeName (n : Name) := Name.mkSimple (prefixName ++ "." ++ n.toString (escape := false))
          let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
            let apply (e : Expr) := predicateInstance info arguments e
            let formula := apply m.formula
            let raw := m.valueFormula?.map apply
            let reach := m.evaluationGuard?.map apply
            let reach := if guards.isEmpty then reach else some (mkAndN (guards.toList ++ reach.toList))
            return { m with name := changeName m.name, formula := ← mkLambdaFVars fvs formula
                            valueFormula? := ← raw.mapM (fun e => liftM (mkLambdaFVars fvs e))
                            evaluationGuard? := ← reach.mapM (fun e => liftM (mkLambdaFVars fvs e)) }
          let branches ← member.branchGroups.mapM fun group => do
            return { group with
              owner := name, members := ← group.members.mapM (fun m => liftM (mapMember m))
              guard? := ← (if guards.isEmpty && group.guard?.isNone then pure none else do
                let conditions := guards.toList ++ (group.guard?.map (predicateInstance info arguments)).toList
                pure (some (← liftM (mkLambdaFVars fvs (mkAndN conditions))))) }
          let observations ← member.memberGroups.mapM fun group => do
            return { group with owner := name, members := ← group.members.mapM (fun m => liftM (mapMember m)) }
          let memberPath := if member.name.isAnonymous then "" else member.name.toString (escape := false)
          let sourceRef := Core.predicateCheckAtMember memberPath (prop.kind == .cover)
          let ref := if sourceRef then member.ref else label
          let child := { prop with name, ref, body := ← mkLambdaFVars fvs instantiated, decl
                                   trigger? := trigger, triggerRef? := (if trigger.isSome then some ref else none)
                                   branchGroups := branches, memberGroups := observations
                                   evidenceOwner? := some prop.name, source? := info.source?, sourceRef }
          if ← contains (predicateInstance info arguments member.body) then
            let nested ← expand (predicateInstance info arguments member.body) member.ref name guards ref
            props := props ++ nested.1
            declarations := declarations ++ nested.2.1
            sites := sites ++ nested.2.2
          else
            props := props.push child
            declarations := declarations.push (decl, instantiated)
          for (ref, question, goal) in member.sites do
            let goal := wrap guards (predicateInstance info arguments goal)
            let marked := mkApp (mkConst ``Fren.leafObligation) goal
            sites := sites.push (name, if prop.kind == .assume then .assume else .prop, ref, question, ← mkLambdaFVars fvs marked)
        set callOccurrences
        return (props, declarations, sites)
      else if !info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty then
        let prefixName := owner.toString (escape := false) ++ "." ++ Core.showPath info.path ++ "@1."
        let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
          let apply (e : Expr) := predicateInstance info arguments e
          let reach := m.evaluationGuard?.map apply
          let reach := if guards.isEmpty then reach else some (mkAndN (guards.toList ++ reach.toList))
          return { m with
            name := Name.mkSimple (prefixName ++ m.name.toString (escape := false))
            formula := ← mkLambdaFVars fvs (apply m.formula)
            valueFormula? := ← m.valueFormula?.mapM (fun e => liftM (mkLambdaFVars fvs (apply e)))
            evaluationGuard? := ← reach.mapM (fun e => liftM (mkLambdaFVars fvs e)) }
        let branches ← (if wanted then info.namedBranchGroups else #[]).mapM fun group => do
          let conditions := guards.toList ++ (group.guard?.map (predicateInstance info arguments)).toList
          let guard? ← if conditions.isEmpty then pure none else some <$> mkLambdaFVars fvs (mkAndN conditions)
          return { group with owner, guard?, members := ← group.members.mapM (fun m => liftM (mapMember m)) }
        let observations ← info.namedMemberGroups.mapM fun group => do
          return { group with
            owner, wanted := (if wanted then group.wanted else !group.wanted)
            members := ← group.members.mapM (fun m => liftM (mapMember m)) }
        let body := wrap guards body
        let decl := prop.decl ++ owner
        return (#[{ prop with
          name := owner, ref := if Core.predicateCheckAtMember "" (prop.kind == .cover) then written else label,
          body := ← mkLambdaFVars fvs body, decl
          branchGroups := branches, memberGroups := observations, source? := info.source?
          evidenceOwner? := some prop.name }], (if decl == prop.decl then #[] else #[(decl, body)]), #[])
    let body := wrap guards body
    let decl := prop.decl ++ owner
    let ref := if Core.predicateCheckAtMember "" (prop.kind == .cover) then written else label
    return (#[{ prop with name := owner, ref, body := ← mkLambdaFVars fvs body, decl,
                           evidenceOwner? := some prop.name }], (if decl == prop.decl then #[] else #[(decl, body)]), #[])
  let body ← zetaReduce (prop.body.beta fvs)
  if let some (info, arguments, wanted) := predicateCallPolarity? state body then
    if (prop.kind == .cover || info.namedMembers.isEmpty || !wanted) && (!info.namedBranchGroups.isEmpty || !info.namedMemberGroups.isEmpty) then
      let prefixName := prop.name.toString (escape := false) ++ "." ++ Core.showPath info.path ++ "@1."
      let mapMember (m : Core.BranchMember Expr) : TermElabM (Core.BranchMember Expr) := do
        let apply (e : Expr) := mkLambdaFVars fvs (predicateInstance info arguments e)
        return { m with
          name := Name.mkSimple (prefixName ++ m.name.toString (escape := false))
          formula := ← apply m.formula
          valueFormula? := ← m.valueFormula?.mapM (fun e => liftM (apply e))
          evaluationGuard? := ← m.evaluationGuard?.mapM (fun e => liftM (apply e)) }
      let branches ← (if wanted then info.namedBranchGroups else #[]).mapM fun g => do
        return { g with
          owner := prop.name, members := ← g.members.mapM mapMember
          guard? := ← g.guard?.mapM (fun e => liftM (mkLambdaFVars fvs (predicateInstance info arguments e))) }
      let observations ← info.namedMemberGroups.mapM fun g => do
        return { g with
          owner := prop.name, wanted := (if wanted then g.wanted else !g.wanted)
          members := ← g.members.mapM mapMember }
      let ref := if Core.predicateCheckAtMember "" (prop.kind == .cover) then source else prop.ref
      return (#[{ prop with ref, branchGroups := branches, memberGroups := observations, source? := info.source? }], #[], #[])
  if !(← contains body) then return (#[prop], #[], #[])
  return (← (expand body source prop.name #[] prop.ref).run {}).1


end Fren
