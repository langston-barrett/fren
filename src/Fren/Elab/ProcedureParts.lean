-- keep-sorted start
import Fren.Elab.Instances
import Fren.Elab.MemberLints
import Fren.Elab.Predicates
-- keep-sorted end

/-! # Hosted elaboration: procedure parts -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ### Elaborating a procedure, in parts

Each part is a definition of its own, so that the compiler, whose time grows
faster than the length of a `do` block, compiles several short ones, and
in parallel. -/

open Lang

/-- A procedure's variables, the names declared so far, and whether every one
was declared without an error, reporting each error, and one cycle of
definitions, as the `fren` command does. -/
def elabCompVars (scope : Name) (members : Array Syntax) : TermElabM (Array Var × NameSet × Bool) := do
  let mut ok := true
  let mut names : NameSet := {}
  let mut vars : Array Var := #[]
  for m in members do
    let (role, isPub, isDet, x, ty?, defn?) ← match m.getKind with
      -- An input has no definition (`checkParsed`).
      | ``Lang.inMember =>
        pure (Core.Role.input, true, false, m[1], if m[2].isNone then none else some m[2][1], none)
      | ``Lang.outMember =>
        pure (.output, !m[0].isNone, !m[1].isNone, m[3], if m[4].isNone then none else some m[4][1], definition? m)
      | _ => continue
    -- An error in shadowing leaves the variable's meaning clear.
    let x ← try declare x scope
      catch ex => logWithin ex; ok := false; pure (declaredIdent x).1
    names := names.insert x.getId
    lintName .variable x.getId x
    try
      if let some ty := ty? then checkFnTypeSite .variable ty
      let (ty, ptype) ← varPType scope x ty?
      let st ← getState
      unless (← getLocal).inSubset || Core.variableTypeAccepted (role == .output) (factsOf st ptype).unbounded defn?.isSome do
        throwErrorAt x (Core.unboundedOutputMsg x.getId ptype.text).text
      let fact? ← factPred? ty ptype
      vars := vars.push { name := x.getId, role, isPub, isDet, «type» := ty, ref := x, defn?, ptype, fact? }
    catch ex => logWithin ex; ok := false
  -- One cycle is reported, as by the `fren` command.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    logErrorAt v.ref (Core.cyclicDefinitionMsg cycle).text; ok := false
  return (vars, names, ok)

/-- A procedure's calls, whose variables follow the procedure's own `vars`: the
calls still to elaborate, all the variables, the names declared so
far, and whether every call was resolved. -/
def elabCompInsts (scope : Name) (members : Array Syntax) (vars : Array Var) (names : NameSet) :
    TermElabM (Array PendingInst × Array Var × NameSet × Bool) := do
  let mut ok := true
  let mut vars := vars
  let mut names := names
  let mut pending : Array PendingInst := #[]
  for m in members do
    unless m.isOfKind ``Lang.callMember do continue
    let (x, p, bs) := (m[1], m[3], m[5].getSepArgs)
    -- A call named by a literal is not resolved, which would report
    -- its name again; the `fren` command stops at the first report too.
    if let .error msg := Core.checkNotLiteral (declaredIdent x).1.getId then
      logErrorAt x msg.text; ok := false; continue
    let x ← try declare x scope
      catch ex => logWithin ex; ok := false; pure (declaredIdent x).1
    names := names.insert x.getId
    lintName .instance x.getId x
    try
      let (pi, ivars) ← resolveInst scope x p bs vars.size
      pending := pending.push pi
      vars := vars ++ ivars
      -- Its bindings give each input of its procedure a value, and the
      -- call's assumption check reads them (`unused_assumption`).
      let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Core.Role.input).map (pi.comp.path, ·.name)
      modifyLocal fun l => { l with globalReads := l.globalReads ++ reads }
    catch ex => logWithin ex; ok := false
  return (pending, vars, names, ok)

/-- A procedure's calls, over its variables `fvs`, and then its definitions,
each after those it mentions, with the earlier ones substituted, so that
each value mentions no defined output: the calls, the generated
definitions so far, the definitions' values, the variables they define,
and the indexes, and whether all were elaborated. -/
def elabCompDefinitions (scope : Name) (vars : Array Var) (pending : Array PendingInst) (declBase : Name)
    (fvs : Array Expr) :
    TermElabM (Array InstInfo × Array (Name × Expr) × Array (Name × Expr) × Array Expr × CompIndexes × Bool) := do
  let instNames := pending.map (·.name)
  let mut good := true
  let mut insts : Array InstInfo := #[]
  let mut indexes : CompIndexes := #[]
  -- The generated definitions, over `fvs`, added once the placeholders
  -- that they use are known.
  let mut defs : Array (Name × Expr) := #[]
  for pi in pending, k in [0:pending.size] do
    try
      let cx := { modName := scope, vars, insts := instNames, place := .binding, current := k }
      let (i, body) ← elabInst cx fvs pi (declBase ++ `call ++ pi.name)
      insts := insts.push i
      defs := defs.push (i.decl, body)
      indexes := indexes ++ (← takeIndexes fvs).map fun (r, q, g) => (pi.name, .binding k, r, q, g)
    catch ex => logWithin ex; good := false
  let mut values : Array (Name × Expr) := #[]
  let mut todo := vars.filter (·.defn?.isSome)
  let mut defnFvs : Array Expr := #[]
  while !todo.isEmpty do
    let some v := todo.find? fun v => (pathMentions v.defn?.get!).all fun n => !todo.any (·.name == n)
      | break
    todo := todo.filter (·.name != v.name)
    let some idx := vars.findIdx? (·.name == v.name) | continue
    try
      let e := v.defn?.get!
      discard (takeIndexes fvs)
      let value ← withRef e do
        -- A definition assigns once and acyclically, so `++` is in the core in it.
        let dcx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop, emptyOk := Core.ExprSite.outputDefinition.checked false false, concatOk := true
                               natOk := v.type.isConstOf ``Nat, expected? := Core.ExprSite.outputDefinition.expected (← coreTy? v.type) none }
        let t ← toTerm dcx e
        checkDeclared e t v.type fun ty => s!"note: `{v.name}` has type `{ty}`, so its definition must too"
        noteObligation dcx .definition e v.ptype t
        elabProp t v.type
      indexes := indexes ++ (← takeIndexes fvs).map fun (r, q, g) => (v.name, .prop, r, q, g)
      lintBools e (← hidesIn { modName := scope, vars, insts := instNames, place := .prop })
      let value := value.replaceFVars defnFvs (values.map (·.2))
      defs := defs.push (declBase ++ `def ++ v.name, ← mkEq fvs[idx]! value)
      values := values.push (v.name, value)
      defnFvs := defnFvs.push fvs[idx]!
    catch ex => logWithin ex; good := false
  return (insts, defs, values, defnFvs, indexes, good)

/-- A procedure's assumptions, requirements and expectations, over its variables
`fvs`, where the defined outputs `defnFvs` have the values `values`: the
constraints, the generated definitions with theirs added, the indexes with
theirs added, the names declared, and whether all were elaborated. -/
def elabCompConstraints (scope : Name) (members : Array Syntax) (vars : Array Var) (instNames : Array Name)
    (declBase : Name) (fvs defnFvs : Array Expr) (values : Array (Name × Expr)) (names : NameSet)
    (defs : Array (Name × Expr)) (indexes : CompIndexes) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes × NameSet × Bool) := do
  let mut good := true
  let mut names := names
  let mut defs := defs
  let mut indexes := indexes
  let mut props : Array PropInfo := #[]
  for m in members do
    let some (kind, x, e) := constraint? m | continue
    if let .error msg := Core.checkNoBang x.getId then
      logErrorAt x msg.text; good := false; continue
    names := names.insert x.getId
    if let .original .. := x.getHeadInfo then lintName .constraint x.getId x
    try
      if x.getId.toString.endsWith "?" then
        throwErrorAt x (Core.propNameMsg x.getId).text
      let cx := { modName := scope, vars, insts := instNames, place := if kind == .assume then .assume else .prop }
      discard (takeIndexes fvs)
      let t ← toTerm cx e
      checkDeclared e t (mkConst ``Bool) fun _ => "note: a constraint is a `Bool`"
      let body ← elabProp t
      -- An assumption sees defined outputs only as their definitions.
      let subst (b : Expr) := if kind == .assume then b.replaceFVars defnFvs (values.map (·.2)) else b
      let body := subst body
      let place : Core.IndexPlace := if kind == .assume then .assume else .prop
      let leaf := match x.getHeadInfo with | .original .. => false | _ => true
      indexes := indexes ++ (← takeIndexes fvs subst).map fun (r, q, g) =>
        (x.getId, place, r, q, if leaf then mkApp (mkConst ``Fren.leafObligation) g else g)
      lintBools e (← hidesIn cx)
      lintConstant cx kind.keyword e
      let trig ← triggerOf cx e
      let trigger? ← trig.mapM fun (t, _) => do mkLambdaFVars fvs (← elabProp t)
      let branchGroups ← clauseBranchGroups cx x.getId e fvs subst
      let memberGroups ← clauseMemberGroups cx x.getId e fvs subst
      let decl := declBase ++ Name.mkSimple kind.keyword ++ x.getId
      defs := defs.push (decl, body)
      props := props.push {
        kind, name := x.getId, ref := x, body := ← mkLambdaFVars fvs body,
        trigger?, triggerRef? := trig.map (·.2), decl, branchGroups, memberGroups }
    catch ex => logWithin ex; good := false
  let mut expanded := #[]
  for prop in props do
    let source := (members.findSome? fun member => do
      let (_, name, expression) ← constraint? member
      if name.getId == prop.name then some expression else none).getD prop.ref
    let cx : ExprCtx := { modName := scope, vars, insts := instNames, place := if prop.kind == .assume then .assume else .prop }
    let (leaves, generated, sites) ← expandPredicateConstraint cx prop source fvs
    if leaves.any (fun leaf => leaf.name != prop.name) then
      indexes ← indexes.mapM fun (name, place, ref, question, goal) => do
        if name == prop.name then
          return (name, place, ref, question, ← mkLambdaFVars fvs (mkApp (mkConst ``Fren.leafObligation) (goal.beta fvs)))
        else return (name, place, ref, question, goal)
    expanded := expanded ++ leaves
    defs := defs ++ generated
    indexes := indexes ++ sites
  return (expanded, defs, indexes, names, good)

/-- Instantiate a specification positionally and generate ordinary expectation
propositions. Specification assumptions are deliberately absent. -/
def elabRefinesMembers (scope : Name) (members : Array Syntax) (vars : Array Var)
    (insts : Array InstInfo) (declBase : Name) (fvs defnFvs : Array Expr)
    (values : Array (Name × Expr)) (props : Array PropInfo) :
    TermElabM (Array PropInfo × Array (Name × Expr) × CompIndexes) := do
  let mut out := #[]
  let mut defs := #[]
  let mut indexes := #[]
  let mut earlier : Array Name := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then earlier := earlier.push m[1].getId
    unless m.isOfKind ``Lang.refinesMember do continue
    let call := m[1].getId
    let some inst := insts.find? (·.name == call)
      | throwErrorAt m[1] "`{call}` is not a call in this global expectation block"
    let r ← resolvePath scope (pathSegs m[2])
    let .item { kind := .compItem, path, .. } := r
      | throwErrorAt m[2] (Core.notACompMsg r).text
    let some spec := (← getState).comps.get? path
      | throwErrorAt m[2] "unknown specification procedure"
    let some concrete := (← getState).comps.get? inst.comp
      | throwErrorAt m[1] "unknown called procedure"
    noteCounts spec m[2]
    unless spec.decidable do modifyLocal fun l => { l with outsideCore := true }
    let inputs := spec.vars.filter fun v => v.name.isAtomic && v.role == .input
    let results := spec.vars.filter fun v => v.name.isAtomic && v.role == .output && v.isPub
    let actual := concrete.vars.filter fun v => v.name.isAtomic && v.role == .output && v.isPub
    let args := m[4].getSepArgs
    unless args.size == inputs.size do
      throwErrorAt m[2] (Core.callArityMsg (Core.showPath path) (inputs.map (Core.nameText ·.name)) args.size).text
    unless results.size == actual.size do
      throwErrorAt m[2] "refinement result count mismatch: specification has {results.size}, call has {actual.size}"
    for v in spec.vars do
      if v.name.isAtomic && v.role != .input && !v.isPub && v.defn?.isNone then
        throwErrorAt m[2] "specification `exists` variable `{v.name}` is not supported by `refines`"
    discard (takeIndexes fvs)
    let cx : ExprCtx := { modName := scope, vars, insts := insts.map (·.name), place := .prop }
    let inputValues ← (inputs.zip args).mapM fun (v, arg) => do
      let t ← toTerm { cx with emptyOk := Core.ExprSite.binding.checked false false, natOk := v.type.isConstOf ``Nat
                               expected? := Core.ExprSite.binding.expected (← coreTy? v.type) none } arg
      checkDeclared arg t v.type fun ty => s!"note: specification parameter `{v.name}` has type `{ty}`"
      elabProp t v.type
    let resultValues ← (results.zip actual).mapM fun (v, cv) => do
      let some i := vars.findIdx? (·.name == call ++ cv.name)
        | throwErrorAt m "missing call result"
      let value := fvs[i]!
      if ← isDefEq cv.type v.type then return value
      if cv.type.isConstOf ``Nat && v.type.isConstOf ``Int then
        return mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt) value
      throwErrorAt m[2] "refinement result type mismatch at `{v.name}`: call result `{cv.name}` cannot flow to the specification result"
    let (body, specificationIndexes) ← withLocalDeclsD (spec.vars.map fun v => (v.name, fun _ => pure v.type)) fun sfvs => do
      let mut slice := sfvs
      for v in inputs, value in inputValues do
        slice := slice.set! (spec.vars.findIdx? (·.name == v.name)).get! value
      for v in results, value in resultValues do
        slice := slice.set! (spec.vars.findIdx? (·.name == v.name)).get! value
      -- Stored definitions already substitute dependencies on other lets.
      -- Public results retain the concrete result, even when defined in the spec.
      for (name, value) in spec.defs do
        let some i := spec.vars.findIdx? (·.name == name) | continue
        unless spec.vars[i]!.isPub do slice := slice.set! i (value.beta slice)
      let guarantees := spec.ensures.map (·.body.beta slice)
      let definitions ← spec.defs.filterMapM fun (name, value) => do
        let some i := spec.vars.findIdx? (·.name == name) | return none
        unless spec.vars[i]!.isPub do return none
        return some (← mkEq slice[i]! (value.beta slice))
      let typedResults ← ((inputs.zip inputValues) ++ (results.zip resultValues)).filterMapM fun (v, value) => do
        let some obligation := v.ptype.obligation (← getState).shapeOf | return none
        let pred ← predOf v.type obligation
        return some (pred.beta #[value])
      let goal := mkAndN (guarantees ++ definitions ++ typedResults).toList
      let internalFacts := (spec.vars.zip slice).filterMap fun (v, value) =>
        if v.name.isAtomic then none else v.fact?.map (·.beta #[value])
      let callFacts := internalFacts ++ spec.insts.map fun i => mkAnd (i.bindings.beta slice) (i.behaviour.beta slice)
      let internal := (spec.vars.zip sfvs).filterMap fun (v, fv) => if v.name.isAtomic then none else some fv
      let close (goal : Expr) : TermElabM Expr := do
        let goal ← if callFacts.isEmpty then pure goal else mkArrow (mkAndN callFacts.toList) goal
        mkForallFVars internal goal
      let checked := spec.ensures.map (·.name) ++ spec.defs.map (·.1)
      let specificationIndexes ← spec.indexes.filterMapM fun (n, _, _, question, value) => do
        unless question.isNone && checked.contains n do return none
        return some (← mkLambdaFVars fvs (← close (value.beta slice)))
      return (← close goal, specificationIndexes)
    let mut serial := defs.size + 1
    while (props ++ out).any (·.name == Name.mkSimple s!"refines_{serial}") do serial := serial + 1
    let name := Name.mkSimple s!"refines_{serial}"
    let decl := declBase ++ `expect ++ name
    indexes := indexes ++ ((← takeIndexes fvs).map fun (r, q, g) => (name, Core.IndexPlace.prop, r, q, g))
      ++ specificationIndexes.map (fun g => (name, Core.IndexPlace.prop, m, none, g))
    if !m[6].isNone then
      let assumptions := (props.filter (·.kind == .assume)).map (·.body.beta fvs)
      let calls := (insts.filter fun i => earlier.contains i.name).map fun i => mkAnd (i.bindings.beta fvs) (i.behaviour.beta fvs)
      let definitions ← (values.zip defnFvs).mapM fun ((_, value), fv) => mkEq fv value
      let goal ← mkForallFVars fvs (← mkArrow (mkAndN (assumptions ++ calls ++ definitions).toList) body)
      let tacs : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨m[6][1]⟩
      let pf ← withoutErrToSorry <| Term.elabTermEnsuringType (← `(by $tacs)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      if pf.hasSorry then throwErrorAt m[6] "a refinement proof must not contain `sorry`"
      if pf.hasMVar then throwErrorAt m[6] "refinement proof has unresolved goals"
      -- Kernel-check the proof while all block variables are abstracted.
      let uses ← usesOf #[goal, pf]
      let (proofType, proofValue) ← withUses uses fun xs => do
        return (← mkForallFVars xs (replaceUses uses xs goal), ← mkLambdaFVars xs (replaceUses uses xs pf))
      addDecl (.thmDecl { name := decl ++ `proof, levelParams := [], «type» := proofType, value := proofValue })
    defs := defs.push (decl, body)
    if m[6].isNone then
      out := out.push { kind := .expect, name, ref := m, decl, trigger? := none, triggerRef? := none, body := ← mkLambdaFVars fvs body
                        abstraction? := some path }
  return (out, defs, indexes)

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a procedure's
constraints, or a global expectation's if `global`. -/
def lintDuplicateConstraints (members : Array Syntax) (global := false) : TermElabM Unit := do
  let constraints := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some (Core.ConstraintKind.assume, x.raw, e.raw)
    | `(fren_member| ensure $x:ident : $e) => some (.ensure, x.raw, e.raw)
    | `(fren_member| expect $x:ident : $e) => some (.expect, x.raw, e.raw)
    | `(fren_member| cover $x:ident : $e) => some (.cover, x.raw, e.raw)
    | _ => none
  -- Cover goals are compared with each other, and constraints with each other.
  for group in #[constraints.filter (·.1 != .cover), constraints.filter (·.1 == .cover)] do
    for (i, j) in Core.repeatedConstraints (group.map fun (_, _, e) => srcText (unparen e)) do
      let (k, x, _) := group[i]!
      let (k', x', _) := group[j]!
      let msg := Core.duplicateConstraintMsg k' k x'.getId.toString global
      let fixable := (Core.duplicateConstraint k' k true).2 && (← getLocal).inMarkdown
      recordLint .duplicateConstraint x (if fixable then msg.note Core.fixHelp else msg)

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
procedure's outputs. -/
def lintOutputs (lcx : ExprCtx) (members : Array Syntax) (vars : Array Var) : TermElabM Unit := do
  let reqs := members.filterMap fun m => match constraint? m with
    | some (.ensure, x, e) => some (x.getId, e)
    | _ => none
  for v in vars.filter (fun v => v.role == .output && v.name.isAtomic) do
    let about := reqs.filter fun (_, e) => (pathMentions e).contains v.name
    let isX (e : Syntax) : Bool :=
      let e := unparen e
      let p := if e.getNumArgs == 1 then e[0] else e
      p.isOfKind ``Lang.fren_path && (pathSegs p).size == 1 && (pathSegs p)[0]!.getId == v.name
    -- The only requirement that mentions it, as `x = e` or `x? iff e`, with `e` other variables'.
    let equation := match about with
      | #[(_, e)] =>
        let e := unparen e
        (isBinOp e "=" || isBinOp e "iff")
          && ((isX e[0] && !(pathMentions e[2]).contains v.name) || (isX e[2] && !(pathMentions e[0]).contains v.name))
      | _ => false
    let mentioned ← match v.defn? with | some d => mentionedNames lcx d | none => pure []
    let (constant, definable) := Core.outputLints v.defn?.isSome mentioned about.size equation
    if constant then recordLint .constantOutput v.ref (Core.constantOutputMsg v.name)
    if definable then recordLint .definableOutput v.ref (Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a procedure's cover goals: each
assumption and guarantee as its kind, its name and its written form. -/
def lintTrivialCover (lcx : ExprCtx) (members : Array Syntax) : TermElabM Unit := do
  let facts := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some ("assumption", x.getId, Core.writtenForm (exactText (unparen e)))
    | `(fren_member| ensure $x:ident : $e) => some ("guarantee", x.getId, Core.writtenForm (exactText (unparen e)))
    | _ => none
  for m in members do
    let `(fren_member| cover $x:ident : $e) := m | continue
    let w := Core.writtenForm (exactText (unparen e))
    -- Only whether it has one: what elaborating it reports is reported where it is.
    let saved ← getLocal
    let trigger ← try Option.isSome <$> triggerOf lcx e catch _ => pure false
    modifyLocal fun _ => saved
    let same? := (facts.find? (·.2.2 == w)).map fun (k, n, _) => (k, n)
    if let some why := Core.trivialCover trigger same? then
      recordLint .trivialCover x (Core.trivialCoverMsg x.getId why)

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a procedure's
requirements. -/
def lintCaseSplitGuarantees (lcx : ExprCtx) (members : Array Syntax) (vars : Array Var) : TermElabM Unit := do
  -- Each requirement `when T, y = e`, as its name, where it is
  -- reported, `y`, the operator, `T` and the text of `e`.
  let mut cases : Array (Name × Syntax × String × String × Core.VariantTest × String) := #[]
  for m in members do
    let `(fren_member| ensure $x:ident : $e) := m | continue
    let e := unparen e.raw
    unless isConditional e && e[0].getAtomVal.trimAscii.toString == "when" do continue
    let body := unparen e[3]
    let op := if isBinOp body "=" then "=" else if isBinOp body "iff" then "iff" else ""
    if op.isEmpty then continue
    let y := unparen body[0]
    let y := if y.getNumArgs == 1 then y[0] else y
    unless y.isOfKind ``Lang.fren_path && (pathSegs y).size == 1 do continue
    let yn := (pathSegs y)[0]!.getId
    unless vars.any (fun v => v.role == .output && v.name == yn) do continue
    let some t ← variantTest? lcx e[1] | continue
    cases := cases.push (x.getId, x, srcText y, op, t, armBodyOf body[2])
  let mut grouped : Array Nat := #[]
  for i in [0:cases.size] do
    if grouped.contains i then continue
    let (_, _, y, op, t, _) := cases[i]!
    let group := (Array.range cases.size).filter fun j =>
      j ≥ i && cases[j]!.2.2.1 == y && cases[j]!.2.2.2.2.1.key == t.key && cases[j]!.2.2.2.2.1.enum == t.enum
    grouped := grouped ++ group
    let cs := group.map fun j => let (n, _, _, _, t, e) := cases[j]!; (n, t, e)
    let ts := cs.map (·.2.1)
    let n := (((← getState).enums.get? t.enum).map (·.variants.size)).getD 0
    if Core.caseSplitGuarantees cs.size (Core.repeatedVariants ts) then
      recordLint .caseSplitGuarantees cases[group[1]!]!.2.1 (Core.caseSplitGuaranteesMsg y op cs (Core.untestedVariants n ts))

/-- Adds a procedure's generated definitions `defs` over its variables `fvs`,
with `p.defs`, `p.assumes` and `p.ensures`, and `p.out.d` for each definition
that mentions only inputs. -/
def addCompDefs (vars : Array Var) (declBase : Name) (fvs : Array Expr) (uses : Array Name)
    (props : Array PropInfo) (values : Array (Name × Expr)) (defs : Array (Name × Expr)) : TermElabM Unit := do
  let appD (decl : Name) := mkAppN (Lean.mkConst decl) (uses.map (Lean.mkConst ·) ++ fvs)
  let app (p : PropInfo) := appD p.decl
  let mut defs := defs
  unless values.isEmpty do
    defs := defs.push (declBase ++ `defs, mkAndN (values.map fun (d, _) => appD (declBase ++ `def ++ d)).toList)
  -- The constraints of the inputs' and outputs' types first
  -- (`Reqs/Generated#procedures`).
  let typeFacts (role : Core.Role) : List Expr := ((vars.zip fvs).filter fun (v, _) =>
      v.name.isAtomic && v.role == role && v.defn?.isNone).toList.filterMap fun (v, x) =>
    v.fact?.map (·.beta #[x])
  defs := defs ++ #[(declBase ++ `assumes, mkAndN (typeFacts .input ++ (props.filter (·.kind == .assume) |>.map app).toList)),
    (declBase ++ `ensures, mkAndN (typeFacts .output ++ (props.filter (·.kind == .ensure) |>.map app).toList))]
  for (decl, body) in defs do
    addUsesDef uses decl (← mkLambdaFVars fvs body)
  -- `p.out.d`, a function of the inputs, when the definition mentions
  -- only inputs.
  let inputs := (vars.zip fvs).filter (·.1.role == .input) |>.map (·.2)
  for (d, value) in values do
    let others := fvs.filter (!inputs.contains ·)
    unless others.any (value.containsFVar ·.fvarId!) do
      addUsesDef uses (declBase ++ `out ++ d) (← mkLambdaFVars inputs value)

/-- A procedure's calls, definitions and constraints, elaborated over its
variables, with its lints of them, and, if all were elaborated, its
generated definitions added: the constraints, the calls, the
placeholders used, the definitions' values over the variables, the
indexes, and whether all were elaborated. -/
def elabCompBody (scope : Name) (members : Array Syntax) (vars : Array Var) (pending : Array PendingInst)
    (declBase : Name) (varsOk : Bool) (varNames : NameSet) (global := false) :
    TermElabM (Array PropInfo × Array InstInfo × Array Name × Array (Name × Expr) × CompIndexes × Bool) := do
  let instNames := pending.map (·.name)
  let decls := vars.map fun v => (v.name, fun _ => pure v.type)
  withLocalDeclsD decls fun fvs => do
    discard (takeIndexes fvs)
    let (insts, defs, values, defnFvs, indexes, defsOk) ← elabCompDefinitions scope vars pending declBase fvs
    let (props, defs, indexes, _, propsOk) ←
      elabCompConstraints scope members vars instNames declBase fvs defnFvs values varNames defs indexes
    let (refines, refineDefs, refineIndexes) ←
      elabRefinesMembers scope members vars insts declBase fvs defnFvs values props
    let props := props ++ refines
    let defs := defs ++ refineDefs
    let indexes := indexes ++ refineIndexes
    let good := varsOk && defsOk && propsOk
    lintDuplicateConstraints members global
    let lcx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop }
    lintOutputs lcx members vars
    lintTrivialCover lcx members
    lintCaseSplitGuarantees lcx members vars
    -- A subset's invariant is erased from its Lean type, but still brings
    -- the placeholders used by the generated assumptions and guarantees.
    let uses ← usesOf ((← fvs.mapM fun x => inferType x) ++ vars.filterMap (·.fact?) ++ defs.map (·.2))
    if good then addCompDefs vars declBase fvs uses props values defs
    let closed ← values.mapM fun (d, v) => return (d, ← mkLambdaFVars fvs v)
    return (props, insts, uses, closed, indexes, good)

/-- `unused_variables` and `unused_assumption` (`lint::unused_assumption`)
of a procedure whose items were all elaborated: the latter is recorded, to be
reported unless the file reads one of the inputs (`reportLints`), or one
that another assumption ties to a used variable, transitively. -/
def lintCompUnused (scope path : Name) (members : Array Syntax) (vars : Array Var) (instNames : Array Name)
    (global : Bool := false) : TermElabM Unit := do
  let mut mentioned := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do mentioned := mentioned ++ pathMentions a
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do mentioned := mentioned ++ pathMentions a
    if let some (_, _, e) := constraint? m then mentioned := mentioned ++ pathMentions e
  for v in vars do
    if let some d := v.defn? then mentioned := mentioned ++ pathMentions d
  -- A public definition says what the output is, so it is used.
  let own := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Core.unmentioned (own.map fun v => (v.name, v)) mentioned do
    recordLint .unusedVariables v.ref (Core.unusedVariableMsg x global (v.role == .output))
  let mut others := #[]
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do others := others ++ pathMentions a
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do others := others ++ pathMentions a
    if let some (kind, _, e) := constraint? m then
      unless kind == .assume do others := others ++ pathMentions e
  for v in vars do
    if let some d := v.defn? then others := others ++ pathMentions d
  let inputs := vars.filter (·.role == .input) |>.map (·.name)
  let level ← lintLevel .unusedAssumption
  let assumed := members.filterMap fun m => match constraint? m with
    | some (.assume, x, e) => some (x, e)
    | _ => none
  let mss := assumed.map fun (_, e) => (pathMentions e).foldl (init := #[]) fun acc n =>
    if vars.any (·.name == n) && !acc.contains n then acc.push n else acc
  -- The uninterpreted functions that they apply link too.
  let acx : ExprCtx := { modName := scope, vars, insts := instNames, place := .prop }
  for m in members do
    if m.isOfKind ``Lang.callMember then
      for a in m[5].getSepArgs do others := others ++ (← appliedFns acx a)
    if m.isOfKind ``Lang.refinesMember then
      for a in m[4].getSepArgs do others := others ++ (← appliedFns acx a)
    if let some (kind, _, e) := constraint? m then
      unless kind == .assume do others := others ++ (← appliedFns acx e)
  for v in vars do
    if let some d := v.defn? then others := others ++ (← appliedFns acx d)
  let links ← assumed.mapIdxM fun i (_, e) => return mss[i]! ++ (← appliedFns acx e)
  let used := Core.usedAssumptions links others
  for (x, _) in assumed, ms in mss, ls in links, u in used do
    if Core.unusedAssumption ms.size (ms.all inputs.contains) u false then
      let r : Core.AssumptionRecord := { component := path, name := x.getId, inputs := ms, links := ls, level }
      modifyLocal fun l => { l with assumptions := l.assumptions.push (r, x) }

/-- `unrelated_binders` (`lint::unrelated_binders`) of the global
expectation `n` with the members `members`: whether its calls fall into
groups that nothing relates. An atom of a constraint relates the calls it
mentions and those whose arguments mention a parameter it mentions; a call
relates itself to the calls its arguments mention; and a parameter
relates the calls whose arguments mention it. -/
def lintUnrelatedCalls (nameStx : Syntax) (n : String) (members : Array Syntax) : TermElabM Unit := do
  let calls := members.filterMap fun m =>
    if m.isOfKind ``Lang.callMember then
      some ((declaredIdent m[1]).1.getId, m[5].getSepArgs.flatMap fun a => (pathMentions a).map (·.getRoot))
    else none
  let params := members.filterMap fun m =>
    if m.isOfKind ``Lang.inMember then some (declaredIdent m[1]).1.getId else none
  let names := calls.map (·.1)
  let reading (p : Name) := (calls.filter (·.2.contains p)).map (·.1)
  let expand (roots : Array Name) := roots.filter names.contains ++ (roots.filter params.contains).flatMap reading
  let atoms := members.flatMap (fun m => match constraint? m with
      | some (_, _, e) => (boolNode "" 0 (unparen e)).atoms.map fun a => expand ((pathMentions a.ref).map (·.getRoot))
      | none => if m.isOfKind ``Lang.refinesMember then
          #[expand (#[m[1].getId] ++ m[4].getSepArgs.flatMap fun a => (pathMentions a).map (·.getRoot))]
        else #[])
    -- A relation of one call alone puts it in no group.
    ++ (calls.map (fun ((w, roots) : Name × Array Name) => #[w] ++ roots.filter names.contains) ++ params.map reading).filter (fun (a : Array Name) => a.size ≥ 2)
  let groups := Core.binderGroups names atoms
  if Core.unrelatedBinders groups.size then
    recordLint .unrelatedBinders nameStx (Core.unrelatedBindersMsg n groups)

/-- A procedure's members, elaborated, with the procedure recorded if all were: whether
they were, and the generated declarations. -/
def elabCompMembers (scope path modName declBase : Name) (isPub : Bool) (nameStx : Syntax)
    (members : Array Syntax) (tested : Core.Tested) (enumerated : Core.Tested := {}) (enumSize : Nat := 3)
    (global : Bool := false) :
    TermElabM (Bool × Array Name) := do
  unless global do
    for m in members do
      if m.isOfKind ``Lang.refinesMember then
        throwErrorAt m "`refines` is accepted only in global expectation blocks"
  let (vars, names, ok) ← elabCompVars scope members
  unless ok do return (false, #[])
  let (pending, vars, names, ok) ← elabCompInsts scope members vars names
  let instNames := pending.map (·.name)
  -- A call that is not resolved is reported once, not again at each
  -- use of it, as by the `fren` command (`Reqs/View#static-errors`).
  unless ok do return (false, #[])
  if global then lintUnrelatedCalls nameStx path.getString! members
  -- Bindings; assumptions, requirements and expectations
  let (props, insts, uses, values, indexes, ok) ← elabCompBody scope members vars pending declBase ok names global
  lintManualNat path members
  if ok then lintCompUnused scope path members vars instNames global
  let mut generated := insts.map (·.decl) ++ props.map (·.decl) ++ #[declBase ++ `assumes, declBase ++ `ensures]
    ++ values.map (declBase ++ `def ++ ·.1) ++ (if values.isEmpty then #[] else #[declBase ++ `defs])
  let env ← getEnv
  generated := generated ++ (values.map (declBase ++ `out ++ ·.1)).filter env.contains
  if ok then
    let (relational, counts) ← checkCounts
    let owners := props.map fun prop => (prop.name, prop.evidenceOwner?)
    let tested := tested.expandProps owners
    let enumerated := enumerated.expandProps owners
    let info : CompInfo := { path, vars, props, insts, ref := nameStx, decl := declBase, uses, defs := values
                             decidable := !(← getLocal).outsideCore, undecidableDenied := (← getLocal).undecidableDenied
                             relational, counts, indexes, tested, enumerated, enumSize, guarded := (← getLocal).guardedUsed
                             global }
    -- A global expectation is an item that nothing calls
    -- (`Reqs/Lang/Global`).
    if global then
      record (.item { item := { kind := .expectItem, path, isPub := false, owner := modName }, ref := nameStx })
      record (.globalInfo path info)
    else
      record (.item { item := { kind := .compItem, path, isPub, owner := modName }, ref := nameStx })
      record (.compInfo info)
  return (ok, generated)


end Fren
