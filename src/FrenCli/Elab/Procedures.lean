-- keep-sorted start
import FrenCli.Elab.ItemSupport
-- keep-sorted end

/-!
# Procedure elaboration for `.fren` files

Elaborates procedures, global expectations and trait laws. Procedure
elaboration is divided into variables, calls, definitions, constraints
and lints.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

/-! ### `elabComp`, in parts

Each part is a definition of its own, so that the compiler, whose time grows
faster than the length of a `do` block, compiles several short ones, and
in parallel. -/

/-- A procedure's variables, each reporting its own first static error, and one
cycle of definitions. -/
def elabCompVars (members : Array Member) : M (Array CVar) := do
  let mut vars := #[]
  for m in members do
    let .var isIn isPub' isDet x ty? defn? := m | continue
    -- An error in shadowing leaves the variable's meaning clear.
    let x := (← attempt (declare x)).getD (declaredIdent x).1
    let xn := Name.mkSimple x.name
    lintName .variable xn x.span
    let role := if isIn then Role.input else .output
    let some v ← attempt do
        if let some segs := ty? then checkFnTypeSite .variable segs
        let ptype ← varPTy ty? x
        let ty := ptype.ty
        unless (← get).inSubset || Fren.Core.variableTypeAccepted (role == .output) ((← get).unbounded ty) defn?.isSome do
          err x.span (Fren.Core.unboundedOutputMsg xn ptype.text)
        let fact? ← factOf ptype (quote xn.toString)
        return { name := xn, role, isPub := isPub', isDet, ty, span := x.span, defn?, ptype, fact? : CVar }
      | continue
    vars := vars.push v
  -- One cycle is reported.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    discard <| attempt (err (α := Unit) v.span (Fren.Core.cyclicDefinitionMsg cycle))
  return vars

/-- A procedure's calls, whose variables follow the procedure's own `vars`: the
calls still to elaborate, and all the variables. -/
def elabCompInsts (members : Array Member) (vars : Array CVar) : M (Array PendingInst × Array CVar) := do
  let mut vars := vars
  let mut pending := #[]
  for m in members do
    let .inst x p bs _ := m | continue
    -- Its name is checked once, whether or not it shadows.
    let x := (← attempt do
        let x ← declare x
        liftMsg x.span (Fren.Core.checkItemName "call" (Name.mkSimple x.name))
        return x).getD (declaredIdent x).1
    let xn := Name.mkSimple x.name
    lintName .instance xn x.span
    let some (pi, ivars) ← attempt (resolveInst x p bs) | continue
    pending := pending.push pi
    vars := vars ++ ivars
    -- Its bindings give each input of its procedure a value, and the
    -- call's assumption check reads them (`unused_assumption`).
    let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Role.input).map (pi.comp.path, ·.name)
    modify fun s => { s with globalReads := s.globalReads ++ reads }
  return (pending, vars)

/-- The bindings of a procedure's calls `pending`, with their indexes and
questions about tables. -/
def elabCompBindings (vars : Array CVar) (instNames : Array Name) (pending : Array PendingInst) :
    M (Array CInst × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut insts := #[]
  let mut indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) := #[]
  let mut tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := #[]
  discard takeIndexes
  discard takeTables
  for pi in pending, k in [0:pending.size] do
    let some (i, idx, tbl) ← attempt do
        let i ← elabInst { vars, insts := instNames, place := .binding, current := k } pi
        return (i, (← takeIndexes).map fun (sp, g, t) => (Name.mkSimple pi.name.name, Fren.Core.IndexPlace.binding k, sp, g, t),
          (← takeTables).map fun (sp, q, g) => (Name.mkSimple pi.name.name, Fren.Core.IndexPlace.binding k, sp, q, g))
      | continue
    insts := insts.push i
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (insts, indexes, tables)

/-- A procedure's definitions, each after those it mentions, with their indexes
and questions about tables added to `indexes` and `tables`. -/
def elabCompDefinitions (name : Ident) (vars : Array CVar) (instNames : Array Name) (indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)))
    (tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) : M (Array (Name × String) × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut indexes := indexes
  let mut tables := tables
  let mut defs : Array (Name × String) := #[]
  let mut todo := vars.filter (·.defn?.isSome)
  while !todo.isEmpty do
    let some v := todo.find? fun v => (mentions v.defn?.get!).all fun n => !todo.any (·.name == n)
      | internal name.span "cyclic definitions"
    todo := todo.filter (·.name != v.name)
    let e := v.defn?.get!
    let some (smt, idx, tbl) ← attempt do
        -- A definition assigns once and acyclically, so `++` is in the core in it.
        let dcx : ExprCtx := { vars, insts := instNames, place := .prop, expected? := Fren.Core.ExprSite.outputDefinition.expected (some v.ty) none, concatOk := true }
        let (smt, t) ← elabExpr dcx e
        liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{v.name}` has type `{v.ty.show}`, so its definition must too"))
        noteObligation dcx .definition e.span v.ptype smt
        lintBools e (← hidesIn dcx)
        return (smt, (← takeIndexes).map fun (sp, g, t) => (v.name, Fren.Core.IndexPlace.prop, sp, g, t),
          (← takeTables).map fun (sp, q, g) => (v.name, Fren.Core.IndexPlace.prop, sp, q, g))
      | continue
    defs := defs.push (v.name, smt)
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (defs, indexes, tables)

/-- Branch facts and model observations annotate an already-checked source
expression; rebuilding their formulas adds no evaluation site or use. -/
def annotateBranches (cx : ExprCtx) (owner : Name) (e : Expr) : M Unit := do
  let saved ← get
  let mut branches := saved.itemBranches
  let mut observations := saved.itemMemberGroups
  if let some (kind, guard, members) := branchMembers e then
    if kind != .equivalence || members.size > 1 then
      let leaves ← members.zipIdx.mapM fun ((label, source, member), i) => do
        let name := Name.mkSimple (owner.toString ++ "." ++ (label.map (·.name) |>.getD (toString (i + 1))))
        let (formula, _) ← elabExpr { cx with noteIndexes := false, expected? := some .bool } member
        let span := label.map (·.span) |>.getD source
        let text ← srcAt source
        return ({ name, formula, range? := some (toRange span), text } : Fren.Core.BranchMember String)
      let guard ← guard.mapM fun guard => do pure (← elabExpr { cx with noteIndexes := false, expected? := some .bool } guard).1
      branches := branches.push { owner, kind, members := leaves, guard? := guard }
  if let some group := observedMembers e then
    let leaves ← group.members.zipIdx.mapM fun ((label, source, member, guard), i) => do
      let name := Name.mkSimple (owner.toString ++ "." ++ (label.map (·.name) |>.getD (toString (i + 1))))
      let (evaluation, _) ← elabExpr { cx with noteIndexes := false, expected? := some .bool } guard
      let (formula, _) ← if evaluation == "false" then pure ("true", Ty.bool)
        else elabExpr { cx with noteIndexes := false, expected? := some .bool } member
      let span := label.map (·.span) |>.getD source
      let text ← srcAt source
      return ({
        name := name
        formula := formula
        valueFormula? := some formula
        evaluationGuard? := some evaluation
        range? := some (toRange span)
        text := text
      } : Fren.Core.BranchMember String)
    observations := observations.push { owner, op := group.op, wanted := group.wanted, members := leaves }
  set { saved with itemBranches := branches, itemMemberGroups := observations }

/-- Instantiate closed member templates at an application. SMT `let` uses
simultaneous bindings, so caller variables cannot capture definition binders. -/
partial def predicateClauses (cx : ExprCtx) (e : Expr) (splitConjunction : Bool := true)
    (leadingGuard : Bool := true) : M (Option (Name × Array NamedClause)) := do
  match e with
  | .when _ negative condition body =>
    -- A guard inside a negation is not a predicate application at the
    -- typed root. Keep its whole expression, as the hosted reader does.
    if !leadingGuard then return none
    let saved ← get
    let context : Fren.Core.TestContext := if negative then .unlessCondition else .whenCondition
    let (condition, bound) ← withBound do
      exprExpect { cx with noteIndexes := false, testContext := context } condition .bool none
    set saved
    let guard := if negative then s!"(not {condition})" else condition
    let visible := if negative then #[] else bound
    let some (path, clauses) ← predicateClauses { cx with binders := cx.binders ++ visible } body splitConjunction leadingGuard | return none
    return some (path, clauses.map fun clause => { clause with
      formula := guarded #[guard] clause.formula
      branches := clause.branches.map fun group => { group with guard? := some (conj #[guard, group.guard?.getD "true"]) }
      groups := clause.groups.map fun group => { group with members := group.members.map fun member =>
        { member with
          formula := guarded #[guard] member.formula
          valueFormula? := member.valueFormula?.map (guarded #[guard])
          evaluationGuard? := some (conj #[guard, member.evaluationGuard?.getD "true"]) } }
      indexes := clause.indexes.map fun (sp, f, t) => (sp, guarded #[guard] f, t)
      tables := clause.tables.map fun (sp, q, f) => (sp, q, guarded #[guard] f) })
  | .«let» _ defs body isWhere =>
    let saved ← get
    let (bcx, binds) ← elabDefinitions { cx with noteIndexes := false } defs (!isWhere) (usedDefinitions defs body)
    let clauses ← predicateClauses bcx body splitConjunction leadingGuard
    set saved
    return clauses.map fun (path, clauses) =>
      let bind := wrapLets binds
      (path, clauses.map fun clause => { clause with
        formula := bind clause.formula
        branches := clause.branches.map (·.map bind)
        groups := clause.groups.map (·.map bind)
        indexes := clause.indexes.map fun (sp, f, t) => (sp, bind f, t)
        tables := clause.tables.map fun (sp, q, f) => (sp, q, bind f) })
  | .not _ body =>
    let some (path, clauses) ← predicateClauses cx body false false | return none
    if clauses.size != 1 || !clauses[0]!.name.isEmpty then return none
    return some (path, clauses.map fun clause => { clause with formula := s!"(not {clause.formula})", branches := #[], groups := clause.groups.map fun group => { group with wanted := !group.wanted } })
  | .app _ segs _ =>
    let saved ← get
    if let .ok (.item { kind := .fnItem, path, .. }) := saved.table.resolvePath saved.scope (segs.map (fun x => Name.mkSimple x.name)) then
      if let some higher := saved.hofs.find? path then
        if let some template := saved.namedPredicates.find? path then
          let mut clauses := #[]
          for clause in (if splitConjunction then template.clauses else template.whole?.toArray) do
            let instantiate (body : String) : M String := do
              set { saved with hofs := saved.hofs.insert path { higher with body } }
              let (formula, _) ← elabExpr { cx with noteIndexes := false } e
              return formula
            set { saved with hofs := saved.hofs.insert path { higher with body := clause.formula }, indexes := #[], tables := #[] }
            let (formula, _) ← elabExpr cx e
            let actualIndexes ← takeIndexes
            let actualTables ← takeTables
            let indexes ← clause.indexes.mapM fun (sp, f, t) => do pure (sp, ← instantiate f, t)
            let tables ← clause.tables.mapM fun (sp, q, f) => do pure (sp, q, ← instantiate f)
            let branches ← clause.branches.mapM fun group => do
              let members ← group.members.mapM fun member => do
                let formula ← instantiate member.formula
                pure { member with formula }
              let guard ← group.guard?.mapM instantiate
              pure { group with members, guard? := guard }
            let groups ← clause.groups.mapM fun group => do
              let members ← group.members.mapM fun member => do
                let formula ← instantiate member.formula
                let value ← member.valueFormula?.mapM instantiate
                let guard ← member.evaluationGuard?.mapM instantiate
                pure { member with formula, valueFormula? := value, evaluationGuard? := guard }
              pure { group with members }
            clauses := clauses.push { clause with formula, indexes := actualIndexes ++ indexes, tables := actualTables ++ tables, branches, groups }
          set saved
          return some (path, clauses)
    let (formula, _) ← elabExpr { cx with noteIndexes := false } e
    let st ← get
    set saved
    let .list (.atom symbol :: args) := Fren.Core.STerm.parse formula | return none
    let some (_, template) := st.namedPredicates.toArray.find? fun (path, _) =>
      itemSym path == symbol || st.instSyms.find? path == some symbol | return none
    if args.length != template.params.size then return none
    let binds := template.params.zip args.toArray |>.map fun (name, value) => s!"({quote name.toString} {value.print})"
    let bind (body : String) := if binds.isEmpty then body else s!"(let ({" ".intercalate binds.toList}) {body})"
    return some (template.sourcePath, (if splitConjunction then template.clauses else template.whole?.toArray).map fun clause => { clause with
      formula := bind clause.formula
      branches := clause.branches.map (·.map bind)
      groups := clause.groups.map (·.map bind)
      indexes := clause.indexes.map fun (sp, f, t) => (sp, bind f, t)
      tables := clause.tables.map fun (sp, q, f) => (sp, q, bind f) })
  | _ => return none

/-- A procedure's assumptions, requirements, expectations and cover goals, with
their indexes and questions about tables added to `indexes` and `tables`. -/
def elabCompConstraints (members : Array Member) (vars : Array CVar) (instNames : Array Name) (indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)))
    (tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) : M (Array CProp × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut indexes := indexes
  let mut tables := tables
  let mut props := #[]
  modify fun s => { s with namedOccurrences := {} }
  for m in members do
    let .prop kind x e := m | continue
    let xn := Name.mkSimple x.name
    let some (p, idx, tbl) ← attempt do
        liftMsg x.span (Fren.Core.checkNoBang xn)
        -- Before the `?` error, as in Lean.
        lintName .constraint xn x.span
        if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg xn)
        let cx : ExprCtx := { vars, insts := instNames, place := if kind == .assume then .assume else .prop }
        let (smt, t) ← elabExpr cx e
        liftMsg e.span (Fren.Core.checkType .bool t (some "note: a constraint is a `Bool`"))
        lintBools e (← hidesIn cx)
        lintConstant cx (match kind with | .assume => "assume" | .ensure => "ensure" | .expect => "expect" | .cover => "cover") e
        let trig ← trigger? cx e
        annotateBranches cx xn e
        let place := if kind == .assume then Fren.Core.IndexPlace.assume else .prop
        let originalIndexes ← takeIndexes
        let originalTables ← takeTables
        if let some (path, clauses) ← predicateClauses cx e (kind != .cover) then
          if clauses.any (fun clause => !clause.name.isEmpty) then
            modify fun s => { s with itemExcludeGroups := s.itemExcludeGroups.push xn }
          let root := (x.name.splitOn ".").head!
          let key := root ++ ":" ++ path.toString
          let occurrence := (← get).namedOccurrences.getD key 0 + 1
          modify fun s => { s with namedOccurrences := s.namedOccurrences.insert key occurrence }
          let mut expanded := #[]
          let mut idx := originalIndexes.map fun (sp, g, t) => (xn, place, sp, g, t)
          let mut tbl := originalTables.map fun (sp, q, g) => (xn, place, sp, q, g)
          for clause in clauses do
            let namePrefix := x.name ++ "." ++ Fren.Core.showPath path ++ "@" ++ toString occurrence
            let name := if clause.name.isEmpty then xn else Name.mkSimple (namePrefix ++ "." ++ clause.name)
            let memberPrefix := if clause.name.isEmpty then namePrefix else namePrefix ++ "." ++ clause.name
            let memberName (n : Name) := Name.mkSimple (memberPrefix ++ (n.toString.dropPrefix? "#template" |>.getD n.toString))
            let branches := clause.branches.map fun group => { group with owner := name, members := group.members.map fun member => { member with name := memberName member.name } }
            let groups := clause.groups.map fun group => { group with owner := name, members := group.members.map fun member => { member with name := memberName member.name } }
            modify fun s => { s with itemBranches := s.itemBranches ++ branches, itemMemberGroups := s.itemMemberGroups ++ groups }
            let sourceRef := Fren.Core.predicateCheckAtMember clause.name (kind == .cover)
            expanded := expanded.push ({
              file? := some clause.file
              sourceRef
              sourceName? := some xn
              kind := kind
              name := name
              evidenceOwner? := some xn
              span := if sourceRef then clause.span else x.span
              smt := clause.formula
              trigger? := trig.map (·.1)
              triggerSpan? := trig.map (·.2)
            } : CProp)
            idx := idx ++ clause.indexes.map fun (sp, g, t) => (name, place, sp, g, t)
            tbl := tbl ++ clause.tables.map fun (sp, q, g) => (name, place, sp, q, g)
          return (expanded, idx, tbl)
        return (#[{ kind, name := xn, span := x.span, smt, trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) : CProp }],
          originalIndexes.map fun (sp, g, t) => (xn, place, sp, g, t), originalTables.map fun (sp, q, g) => (xn, place, sp, q, g))
      | continue
    props := props ++ p
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (props, indexes, tables)

/-- Written identity of a split clause. Synthetic guard/let nodes retain
an enclosing block's span, so that span cannot stand for their new body. -/
partial def Expr.clauseWritten (src : Array Char) (e : Expr) : String :=
  match e with
  | .when _ negative condition body =>
    (if negative then "unless " else "when ") ++
      Fren.Core.textOf src (toRange (condition.writtenSpan src)) ++ ", (" ++ body.clauseWritten src ++ ")"
  | .«let» _ defs body isWhere =>
    let bindings := defs.map fun (name, _, value) =>
      Fren.Core.textOf src { start := name.span.start, stop := value.span.stop }
    (if isWhere then "where{" else "let{") ++ String.intercalate "," bindings.toList ++
      "}in(" ++ body.clauseWritten src ++ ")"
  | _ => Fren.Core.textOf src (toRange (e.writtenSpan src))

/-- End of the actual written member, excluding enclosing synthetic wrappers. -/
partial def Expr.clauseWrittenStop (label : Span) (e : Expr) : Nat :=
  match e with
  | .when sp _ _ body | .«let» sp _ body _ =>
    max (if sp.start >= label.stop then sp.stop else 0) (body.clauseWrittenStop label)
  | _ => e.span.stop

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a procedure's
constraints, or a global expectation's if `global`. -/
def lintDuplicateConstraints (members writtenMembers : Array Member) (global := false) : M Unit := do
  let src := (← get).src
  let writtenLabels := writtenMembers.filterMap fun | .prop _ name _ => some name.span | _ => none
  -- Cover goals are compared with each other, and constraints with each other.
  let all := members.filterMap fun | .prop k x e => some (k.core, x, e) | _ => none
  for constraints in #[all.filter (·.1 != .cover), all.filter (·.1 == .cover)] do
    for (i, j) in Fren.Core.repeatedConstraints (constraints.map fun (_, _, e) => e.clauseWritten src) do
      let (k, x, e) := constraints[i]!
      let (k', x', _) := constraints[j]!
      let msg := Fren.Core.duplicateConstraintMsg k' k x'.name global
      if (Fren.Core.duplicateConstraint k' k true).2 then
        if !writtenLabels.contains x.span then
          -- Only a written label gives a removable member range. Never
          -- delete a generated clause's entire shared parent expression.
          let mut colon := x.span.stop
          while src[colon]?.any Char.isWhitespace do colon := colon + 1
          if src[colon]? == some ':' then
            let mut stop := e.clauseWrittenStop x.span
            while src[stop]?.any (fun c => c == ' ' || c == '\t') do stop := stop + 1
            if src[stop]? == some ',' then stop := stop + 1
            stop := withLineComment src stop
            lintEdits .duplicateConstraint x.span msg #[(Fren.Core.deletionRange src { start := x.span.start, stop }, "")]
          else lint .duplicateConstraint x.span msg
        else
          let stop := withLineComment src (Fren.Core.withParens src (toRange (e.writtenSpan src))).stop
          lintEdits .duplicateConstraint x.span msg #[(Fren.Core.deletionRange src { start := wordStart src x.span.start, stop }, "")]
      else lint .duplicateConstraint x.span msg

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
procedure's outputs. -/
def lintOutputs (lcx : ExprCtx) (members : Array Member) (vars : Array CVar) : M Unit := do
  let reqs := members.filterMap fun | .prop .ensure x e => some (Name.mkSimple x.name, e) | _ => none
  for v in vars.filter (fun v => v.role == .output && v.name.isAtomic) do
    let isX : Expr → Bool | .path _ #[seg] => Name.mkSimple seg.name == v.name | _ => false
    let about := reqs.filter fun (_, e) => (mentions e).contains v.name
    -- The only requirement that mentions it, as `x = e` or `x? iff e`, with `e` other variables'.
    let equation := match about with
      | #[(_, .bin _ op l r)] => (op == "=" || op == "iff") &&
          ((isX l && !(mentions r).contains v.name) || (isX r && !(mentions l).contains v.name))
      | _ => false
    let mentioned ← match v.defn? with | some d => mentionedNames lcx d | none => pure []
    let (constant, definable) := Fren.Core.outputLints v.defn?.isSome mentioned about.size equation
    if constant then lint .constantOutput v.span (Fren.Core.constantOutputMsg v.name)
    if definable then lint .definableOutput v.span (Fren.Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a procedure's cover goals: each
assumption and guarantee as its kind, its name and its written form. -/
def lintTrivialCover (lcx : ExprCtx) (members : Array Member) : M Unit := do
  let src := (← get).src
  let facts ← members.filterMapM fun m => match m with
    | .prop .assume x e => return some ("assumption", Name.mkSimple x.name, Fren.Core.writtenForm (← srcAt (e.writtenSpan src)))
    | .prop .ensure x e => return some ("guarantee", Name.mkSimple x.name, Fren.Core.writtenForm (← srcAt (e.writtenSpan src)))
    | _ => pure none
  for m in members do
    let .prop .cover x e := m | continue
    let w := Fren.Core.writtenForm (← srcAt (e.writtenSpan src))
    -- Only whether it has one: what elaborating it reports is reported where it is.
    let saved ← get
    let trigger ← tryCatch (Option.isSome <$> trigger? lcx e) fun _ => pure false
    set saved
    let same? := (facts.find? (·.2.2 == w)).map fun (k, n, _) => (k, n)
    if let some why := Fren.Core.trivialCover trigger same? then
      lint .trivialCover x.span (Fren.Core.trivialCoverMsg (Name.mkSimple x.name) why)

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a procedure's
requirements. -/
def lintCaseSplitGuarantees (lcx : ExprCtx) (members : Array Member) (vars : Array CVar) : M Unit := do
  -- `case_split_guarantees` (`lint::case_split_guarantees`): each requirement `when T, y = e`, as its name, where it is
  -- reported, `y`, the operator, `T` and the text of `e`.
  let mut cases : Array (Name × Span × String × String × Fren.Core.VariantTest × String) := #[]
  for m in members do
    let .prop .ensure x (.when _ false c (.bin _ op (.path _ #[y]) rhs)) := m | continue
    unless (op == "=" || op == "iff") && vars.any (fun v => v.role == .output && v.name == Name.mkSimple y.name) do continue
    let some t ← variantTest? lcx c | continue
    cases := cases.push (Name.mkSimple x.name, x.span, y.name, op, t, ← armBodyOf rhs)
  let mut grouped : Array Nat := #[]
  for i in [0:cases.size] do
    if grouped.contains i then continue
    let (_, _, y, op, t, _) := cases[i]!
    let group := (Array.range cases.size).filter fun j =>
      j ≥ i && cases[j]!.2.2.1 == y && cases[j]!.2.2.2.2.1.key == t.key && cases[j]!.2.2.2.2.1.enum == t.enum
    grouped := grouped ++ group
    let cs := group.map fun j => let (n, _, _, _, t, e) := cases[j]!; (n, t, e)
    let ts := cs.map (·.2.1)
    let n := (((← get).table.enums.get? t.enum).map (·.variants.size)).getD 0
    if Fren.Core.caseSplitGuarantees cs.size (Fren.Core.repeatedVariants ts) then
      lint .caseSplitGuarantees cases[group[1]!]!.2.1 (Fren.Core.caseSplitGuaranteesMsg y op cs (Fren.Core.untestedVariants n ts))

/-- `unused_variables` and `unused_assumption` of the procedure `n`, whose
members had no static error. -/
def lintCompUnused (n : Name) (members : Array Member) (vars : Array CVar) (instNames : Array Name)
    (global : Bool := false) : M Unit := do
  let mentioned := members.foldl (init := #[]) fun acc m => match m with
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .refines w _ args _ => acc.push (Name.mkSimple w.name) ++ args.flatMap mentions
    | .inst _ _ bs .. => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- A public definition says what the output is, so it is used.
  let candidates := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Fren.Core.unmentioned (candidates.map fun v => (v.name, v)) mentioned do
    lint .unusedVariables v.span (Fren.Core.unusedVariableMsg x global (v.role == .output))
  -- `unused_assumption` (`lint::unused_assumption`), unless the file reads
  -- one of the inputs (`finishLints`), or one that another assumption ties to
  -- a used variable, transitively.
  let others := members.foldl (init := #[]) fun acc m => match m with
    | .prop .assume _ _ => acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .refines w _ args _ => acc.push (Name.mkSimple w.name) ++ args.flatMap mentions
    | .inst _ _ bs .. => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- The uninterpreted functions that they apply link too.
  let acx : ExprCtx := { vars, insts := instNames, place := .prop }
  let others ← members.foldlM (init := others) fun acc m => match m with
    | .prop .assume _ _ => pure acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => return acc ++ (← appliedFns acx e)
    | .refines _ _ args _ => args.foldlM (fun acc e => return acc ++ (← appliedFns acx e)) acc
    | .inst _ _ bs .. => bs.foldlM (init := acc) fun acc (_, e?) => match e? with
      | some e => return acc ++ (← appliedFns acx e)
      | none => pure acc
    | _ => pure acc
  let inputs := vars.filter (·.role == .input) |>.map (·.name)
  let assumed := members.filterMap fun | .prop .assume x e => some (x, e) | _ => none
  let mss := assumed.map fun (_, e) =>
    (mentions e).foldl (init := #[]) fun acc n => if vars.any (·.name == n) && !acc.contains n then acc.push n else acc
  let links ← assumed.mapIdxM fun i (_, e) => return mss[i]! ++ (← appliedFns acx e)
  let used := Fren.Core.usedAssumptions links others
  for (x, _) in assumed, ms in mss, ls in links, u in used do
    if Fren.Core.unusedAssumption ms.size (ms.all inputs.contains) u false then
      let r : Fren.Core.AssumptionRecord :=
        { component := (← get).module ++ n, name := Name.mkSimple x.name, inputs := ms, links := ls
          level := (← get).levels.get .unusedAssumption }
      modify fun s => { s with assumptions := s.assumptions.push (r, x.span) }

/-- A procedure's members as a component's: its parameters and results
(`header`), each result with the definition that an `out` member of its
block gives it, at most one (`F0421`), and then its block's other
members. -/
def procMembers (header body : Array Member) : M (Array Member) := do
  let mut defs : Array (String × Expr) := #[]
  for m in body do
    if let .define x e := m then
      if defs.any (·.1 == x.name) then err x.span (Fren.Core.resultDefinedTwiceMsg x.name)
      defs := defs.push (x.name, e)
  let header := header.map fun
    | .var false true det x ty none => .var false true det x ty ((defs.find? (·.1 == (declaredIdent x).1.name)).map (·.2))
    | m => m
  return header ++ body.filter (!· matches .define ..)

/-- `unrelated_binders` (`lint::unrelated_binders`) of the global
expectation `name` with the members `members`: whether its calls fall
into groups that nothing relates. An atom of a constraint relates the
calls it mentions and those whose arguments mention a parameter it
mentions; a call relates itself to the calls its arguments mention; and a
parameter relates the calls whose arguments mention it. -/
def lintUnrelatedCalls (name : Ident) (members : Array Member) : M Unit := do
  let calls := members.filterMap fun
    | .inst x _ bs .. => some (Name.mkSimple (declaredIdent x).1.name, bs.flatMap fun (b, e?) =>
        match e? with
        | some e => (mentions e).map (·.getRoot)
        | none => #[Name.mkSimple b.name])
    | _ => none
  let params := members.filterMap fun
    | .var true _ _ x _ _ => some (Name.mkSimple (declaredIdent x).1.name)
    | _ => none
  let names := calls.map (·.1)
  let reading (p : Name) := (calls.filter (·.2.contains p)).map (·.1)
  let expand (roots : Array Name) := roots.filter names.contains ++ (roots.filter params.contains).flatMap reading
  let atoms := members.flatMap (fun
      | .prop _ _ e => (boolAtoms e).map fun a => expand ((mentions a).map (·.getRoot))
      | .refines w _ args _ => #[expand (#[Name.mkSimple w.name] ++ (args.flatMap mentions).map (·.getRoot))]
      | _ => #[])
    -- A relation of one call alone puts it in no group.
    ++ (calls.map (fun ((w, roots) : Name × Array Name) => #[w] ++ roots.filter names.contains) ++ params.map reading).filter (fun (a : Array Name) => a.size ≥ 2)
  let groups := Fren.Core.binderGroups names atoms
  if Fren.Core.unrelatedBinders groups.size then
    lint .unrelatedBinders name.span (Fren.Core.unrelatedBindersMsg name.name groups)

/-- The results and members of a procedure or global expectation, as
`lang::block_member` reads them, each with whether it is written with
`det` and where it is reported. -/
def blockMembers (header body : Array Member) (spans : Array Span) : Array (Span × Fren.Core.BlockMember × Bool) :=
  let results := header.filterMap fun
    | .var false _ det x _ _ => some (x.span, Fren.Core.BlockMember.result, det)
    | _ => none
  let others := (body.zip spans).filterMap fun (m, sp) => match m with
    | .var _ _ det _ _ none => some (sp, Fren.Core.BlockMember.exists, det)
    | .var _ _ det _ _ (some _) => some (sp, .let, det)
    | .define .. => some (sp, .define, false)
    | .prop .assume .. => some (sp, .assume, false)
    | .prop .ensure .. => some (sp, .ensure, false)
    | .prop .expect .. => some (sp, .expect, false)
    | .prop .cover .. => some (sp, .cover, false)
    | .inst .. => some (sp, .call, false)
    | .use .. | .useGroup .. => some (sp, .use, false)
    | .refines .. => some (sp, .refines, false)
    | .evidence .. => none
  results ++ others

/-- A member of a global expectation's block that it does not accept
(`lang::block_member`), with where it is reported. -/
def blockMemberError? (header body : Array Member) (spans : Array Span) : Option (Span × Fren.Core.Msg) :=
  (blockMembers header body spans).findSome? fun (sp, m, det) => (Fren.Core.blockMemberReport? m det).map (sp, ·)

/-- Claims an abstract procedure's guarantees with positional inputs and
results. Abstract local definitions are substituted in dependency order. -/
def elabRefinesMember (vars : Array CVar) (pending : Array PendingInst)
    (w : Ident) (path : Array Ident) (args : Array Expr) (sp : Span) (index : Nat) : M CProp := do
  let some concrete := pending.find? (fun i => i.name.name == w.name)
    | err w.span { code? := some "F0201", headline := s!"`{w.name}` is not a call in this global expectation block" }
  let resolved ← resolve path
  let .item { kind := .compItem, path := abstractPath, .. } := resolved
    | err sp (Fren.Core.notACompMsg resolved)
  let some abstract := (← get).comps.find? (·.path == abstractPath)
    | internal sp "missing abstract procedure"
  unless abstract.decidable do modify fun s => { s with outsideCore := true }
  let params := abstract.vars.filter (fun v => v.name.isAtomic && v.role == .input)
  unless params.size == args.size do
    err sp (Fren.Core.callArityMsg (showPath abstractPath) (params.map (Fren.Core.nameText ·.name)) args.size)
  let actual := concrete.comp.vars.filter (fun v => v.name.isAtomic && v.role == .output && v.isPub)
  let results := abstract.vars.filter (fun v => v.name.isAtomic && v.role == .output && v.isPub)
  unless actual.size == results.size do
    err sp { code? := some "F0408", headline := s!"refinement result count mismatch: specification has {results.size}, call has {actual.size}" }
  if let some hidden := abstract.vars.find? (fun v => v.name.isAtomic && v.role == .output && !v.isPub && v.defn?.isNone) then
    err sp { code? := some "F0417", headline := s!"specification `exists` variable `{hidden.name}` is not supported by `refines`"
             notes := #["help: make it a result of the specification"] }
  let cx : ExprCtx := { vars, insts := pending.map (Name.mkSimple ·.name.name), place := .prop }
  let mut substitutions : Array (Name × String) := #[]
  for param in params, arg in args do
    let (value, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.binding.expected (some param.ty) none } arg
    liftMsg arg.span (Fren.Core.checkType param.ty ty none)
    substitutions := substitutions.push (param.name, value)
  for required in results, given in actual do
    if let .error msg := Fren.Core.checkType required.ty given.ty none then
      err sp { msg with headline := s!"refinement result type mismatch at `{required.name}`: call result `{given.name}` cannot flow to the specification result" }
    substitutions := substitutions.push (required.name, quote (Name.mkSimple w.name ++ given.name).toString)
  let replace (subs : Array (Name × String)) (text : String) := substQuoted (fun p =>
    ((subs.find? (fun (n, _) => n.toString == p)).map (·.2)).getD (quote p)) text
  let internal := abstract.vars.filter (!·.name.isAtomic)
  -- The claim quantifies over the abstraction's call variables, so its
  -- queries need a logic with quantifiers (`cli::logic`), as Lean's have.
  unless internal.isEmpty do modify fun s => { s with quantified := true }
  for v in internal do
    substitutions := substitutions.push (v.name, quote s!"#refines{index}.{v.name}")
  let mut locals : Array (String × String) := #[]
  for (name, value) in abstract.defs do
    unless results.any (·.name == name) do
      let fresh := quote s!"#refines{index}#local.{name}"
      locals := locals.push (fresh, replace substitutions value)
      substitutions := substitutions.push (name, fresh)
  -- Separate fresh symbols prevent a caller's arguments from being
  -- captured by an abstraction's local names. The `#local` separator also
  -- keeps these symbols apart from its quantified call outputs, whose
  -- prefix is `#refines{index}.`. Sequential lets share each
  -- local value instead of expanding a chain once for every occurrence.
  let withLocals (body : String) := locals.foldr (fun (name, value) body =>
    s!"(let (({name} {value})) {body})") body
  let claims := (abstract.props.filter (·.kind == .ensure)).map (fun p => replace substitutions p.smt)
    ++ abstract.defs.filterMap (fun (n, value) => if results.any (·.name == n) then
      some s!"(= {replace substitutions (quote n.toString)} {replace substitutions value})" else none)
    ++ (params ++ results).filterMap (fun v => v.fact?.map (replace substitutions))
  let internalFacts := internal.flatMap fun v =>
    (if v.ty == .nat then #[s!"(>= {replace substitutions (quote v.name.toString)} 0)"] else #[])
      ++ v.fact?.toArray.map (replace substitutions)
  let calls := internalFacts ++ abstract.insts.map fun i => replace substitutions (conj #[i.bindings, i.behaviour])
  let close (goal : String) :=
    let goal := withLocals (if calls.isEmpty then goal else s!"(=> {conj calls} {goal})")
    if internal.isEmpty then goal else
      s!"(forall ({" ".intercalate (internal.map fun v => s!"({quote s!"#refines{index}.{v.name}"} {v.ty.sort})").toList}) {goal})"
  let body := close (conj claims)
  let defined := (abstract.props.filter (·.kind == .ensure)).map (·.name) ++ abstract.defs.map (·.1)
  modify fun s => { s with indexes := s.indexes ++ abstract.indexes.filterMap (fun (n, _, _, g, t) =>
    if defined.contains n then some (sp, close (replace substitutions g), t) else none) }
  noteCounts abstract sp
  let closeApp (app : String) :=
    let app := withLocals (replace substitutions app)
    let bound := internal.filter fun v => (app.splitOn (quote s!"#refines{index}.{v.name}")).length > 1
    if bound.isEmpty then app else
      s!"(forall ({" ".intercalate (bound.map fun v => s!"({quote s!"#refines{index}.{v.name}"} {v.ty.sort})").toList}) {app})"
  modify fun s => { s with natApps := s.natApps ++ abstract.natApps.map closeApp }
  return { kind := .expect, name := Name.mkSimple s!"refines_{index}"
           span := sp, smt := body, trigger? := none, triggerSpan? := none, abstraction? := some abstractPath }

def elabComp (isPub : Bool) (name : Ident) (header body : Array Member) (spans : Array Span) (openStop : Nat)
    (global : Bool := false) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[], itemExcludeGroups := #[], itemBranches := #[], itemMemberGroups := #[], inductionArgs := #[] }
  if global then
    liftMsg name.span (Fren.Core.checkNoBang n)
    if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  else liftMsg name.span (Fren.Core.checkItemName "procedure" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName (if global then .global else .component) n name.span
  startDeclared
  -- What a global expectation's block accepts (`lang::block_member`).
  if global then
    if let some (sp, msg) := blockMemberError? header body spans then
      err sp msg
  let distributed := body.flatMap fun
    | .prop kind owner expression =>
      if kind != .cover && expression.blockRoot then (expression.clauseLeaves owner).map fun (name, _) => Name.mkSimple name.name else #[]
    | _ => #[]
  let members ← procMembers header (splitConjunctionMembers body)
  declareMemberUses (module ++ n) members
  -- Distinct names (`lang::distinct_names`): variables, calls and
  -- constraints share one namespace.
  let named := members.filterMap fun
    | .var _ _ _ x _ _ | .inst x .. | .prop _ x _ => some x
    | _ => none
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err named[k]!.span (Fren.Core.dupMemberMsg declared[k]! global)
  lintMemberOrder body spans openStop global
  modify fun s => { s with inCompBody := true }
  -- Each variable, call, binding, definition and constraint reports its
  -- own first static error; after those of the variables, and of the
  -- calls, the item stops, since what follows would only repeat them
  -- (`Reqs/View#static-errors`).
  let vars ← elabCompVars members
  stopIfErrors
  let (pending, vars) ← elabCompInsts members vars
  stopIfErrors
  let instNames := pending.map (Name.mkSimple ·.name.name)
  let (insts, indexes, tables) ← elabCompBindings vars instNames pending
  let (defs, indexes, tables) ← elabCompDefinitions name vars instNames indexes tables
  let (props, indexes, tables) ← elabCompConstraints members vars instNames indexes tables
  let mut props := props
  let mut indexes := indexes
  let mut tables := tables
  let mut refinesIndex := 0
  for m in members do
    if let .refines w abstract args sp := m then
      refinesIndex := refinesIndex + 1
      while props.any (·.name == Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      unless global do err sp { code? := some "F0417", headline := "`refines` is accepted only in global expectation blocks" }
      discard takeIndexes
      discard takeTables
      if let some p ← attempt (elabRefinesMember vars pending w abstract args sp refinesIndex) then
        props := props.push p
        indexes := indexes ++ (← takeIndexes).map (fun (sp, g, t) => (p.name, Fren.Core.IndexPlace.prop, sp, g, t))
        tables := tables ++ (← takeTables).map (fun (sp, q, g) => (p.name, Fren.Core.IndexPlace.prop, sp, q, g))

  lintManualNat (module ++ n) members
  lintDuplicateConstraints members body global
  let lcx : ExprCtx := { vars, insts := instNames, place := .prop }
  lintOutputs lcx members vars
  lintTrivialCover lcx members
  lintCaseSplitGuarantees lcx members vars
  if global then lintUnrelatedCalls name members
  -- The lints above are found despite a constraint's static error, as in
  -- Lean; `unused_variables`, and the rest, only without one.
  stopIfErrors
  lintCompUnused n members vars instNames global
  let path := module ++ n
  let (tested, enumerated) ← testedOf (← evidenceOfEffect) members
  let owners := props.map fun prop => (prop.name, prop.evidenceOwner?)
  let tested := tested.expandProps owners
  let enumerated := enumerated.expandProps owners
  let (relational, counts) ← checkCounts
  let c : CComp := { path, file := (← get).file, span := name.span, vars, props, insts, defs, indexes, tables, distributed := distributed ++ (← get).itemExcludeGroups ++ (props.filter (fun p => p.name.toString.contains '@')).map (·.name)
                     branchGroups := (← get).itemBranches
                     memberGroups := (← get).itemMemberGroups
                     decidable := !(← get).outsideCore, relational, counts, tested, enumerated, enumSize := (← get).enumSize
                     natApps := (← get).natApps, guarded := (← get).guardedUsed, global }
  -- A global expectation is an item that nothing calls
  -- (`Reqs/Lang/Global`).
  if global then
    modify fun s => { s with
      table := s.table.addItem { kind := .expectItem, path, isPub := false, owner := s.module }
      scope := s.module
      globals := s.globals.push c }
  else
    modify fun s => { s with
      table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
      scope := s.module
      comps := s.comps.push c }
    -- `proc_without_outputs`, once the file's paths are known
    -- (`finishLints`). It has no fix (`Fren.Core.procWithoutOutputsMsg`).
    let members := (blockMembers header body spans).toList.map (·.2)
    if Fren.Core.procWithoutOutputs isPub members 0 then
      let r : Fren.Core.ProcRecord := { path, isPub, members, level := (← get).levels.get .procWithoutOutputs }
      modify fun s => { s with procs := s.procs.push (r, name.span) }

/-- Elaborates a global expectation (`Reqs/Lang/Global`). -/
def elabGlobal (name : Ident) (binders : Array Binder) (body : Expr) : M Unit := do
  if binders.isEmpty && (body.blockRoot || (observedMembers body).isSome) then
    elabComp false name #[] #[.prop .expect { name := "", span := name.span } body] #[body.span] name.span.stop (global := true)
    return
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkNoBang n)
  let all ← evidenceOfEffect
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .global n name.span
  startDeclared
  -- `duplicate_constraint` (`lint::duplicate_constraint`): its text after
  -- its name, against the earlier ones of its module.
  let st ← get
  let src := st.src
  let written := body.writtenSpan src
  let text := String.ofList (src.extract name.span.stop written.start).toList ++ (← srcAt written)
  if let some (_, earlier, _) := st.globalTexts.find? fun (m, _, t) => m == st.module && Fren.Core.writtenSame t text then
    let stop := withLineComment src (Fren.Core.withParens src (toRange written)).stop
    lintEdits .duplicateConstraint name.span (Fren.Core.duplicateConstraintMsg .expect .expect earlier)
      #[(Fren.Core.deletionRange src { start := st.settingStart?.getD st.itemStart, stop }, "")]
  modify fun s => { s with globalTexts := s.globalTexts.push (st.module, name.name, text) }
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binders.flatMap (·.names)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err binderIds[k]!.span (Fren.Core.dupBinderMsg declared[k]!)
  -- Its binders are a quantifier around the body, and it mentions no
  -- variables (`Reqs/Lang/Global#the-short-form`).
  let valueBinders := binders
  let cx : ExprCtx := { vars := #[], place := .prop }
  discard takeIndexes
  discard takeTables
  let quantified := if valueBinders.isEmpty then body
    else .quant { start := valueBinders[0]!.span.start, stop := body.span.stop } true valueBinders body
  let (smt, t) ← elabExpr cx quantified
  let indexes := (← takeIndexes).map fun (sp, g, t) => (n, Fren.Core.IndexPlace.prop, sp, g, t)
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.prop, sp, q, g)
  liftMsg body.span (Fren.Core.checkType .bool t (some "note: an expectation is a `Bool`"))
  -- The body is in the scope of the binders over values too.
  lintBools body (← hidesIn cx (valueBinders.flatMap (·.names) |>.map fun x =>
    (Name.mkSimple (declaredIdent x).1.name, .boundName)))
  lintConstant cx "expect" body
  let trig ← trigger? cx quantified
  lintDeclared .global n name.span
  let prop : CProp := { kind := .expect, name := n, span := name.span, smt
                        trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) }
  discard checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := module ++ n, isPub := false, owner := s.module }
    globals := s.globals.push { path := s.module, file := s.file, span := name.span, vars := #[], props := #[prop], indexes, tables
                                short := true
                                decidable := !s.outsideCore, natApps := s.natApps, guarded := s.guardedUsed
                                tested := Fren.Core.Tested.ofSettings all.tested #[] #[(n, none)] #[] #[]
                                enumerated := Fren.Core.Tested.ofSettings all.enumerated #[] #[(n, none)] #[] #[]
                                enumSize := s.enumSize } }

/-- Whether `undecidable` is an error in what reported `reports`, as the
Lean-hosted front end records it (`undecidableDenied`). -/
def undecidableDenied (reports : Array (Fren.Core.LintReport Span)) : Bool :=
  reports.any fun r => r.lint == .undecidable && r.level.level.severity? == some .error

/-- Elaborates a law of the trait being elaborated (`Reqs/Lang/Traits#laws`):
its variables are a quantifier around its equation, and it mentions no
variables, as a global expectation in the short form does. Records it in
`traitLaws`. -/
def elabLaw (name : Ident) (params : Array (Ident × Option (Array Ident))) (body : Expr) : M Unit := do
  -- Only variables, parameters, calls and binders are written with `!`.
  liftMsg name.span (Fren.Core.checkNoBang (Name.mkSimple name.name))
  let name := (declaredIdent name).1
  let n := Name.mkSimple name.name
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  let reportsBefore := (← get).lintReports.size
  lintName .law n name.span
  startDeclared
  -- Distinct names (`lang::distinct_names`), without the `!` of shadowing.
  let declared := params.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err params[k]!.1.span (Fren.Core.dupParamMsg declared[k]!)
  -- Each variable has its type written, but a `Bool`, which may be written
  -- `x?` alone, as a function's parameter may.
  let mut binders : Array Binder := #[]
  for (x, ty?) in params do
    let ty ← match ty? with
      | some segs => pure segs
      | none =>
        discard (varPTy none x)
        pure #[({ name := "Bool", span := x.span } : Ident)]
    binders := binders.push { names := #[x], ty, span := x.span.to ((ty.back?.map (·.span)).getD x.span) }
  let cx : ExprCtx := { vars := #[], place := .prop }
  discard takeIndexes
  discard takeTables
  let quantified := if binders.isEmpty then body
    else .quant { start := binders[0]!.span.start, stop := body.span.stop } true binders body
  let (smt, t) ← elabExpr cx quantified
  discard takeIndexes
  discard takeTables
  liftMsg body.span (Fren.Core.checkType .bool t (some "note: a law is a `Bool`"))
  lintBools body (← hidesIn cx (declared.map (·, .boundName)))
  lintDeclared .law n name.span
  discard checkCounts
  let denied := undecidableDenied ((← get).lintReports.extract reportsBefore)
  modify fun s => { s with
    traitLaws := s.traitLaws.push (n, smt, !s.outsideCore, s.natApps, s.guardedUsed, denied)
    theoryLaws := s.theoryLaws.push (s.module ++ n) }

end FrenCli
