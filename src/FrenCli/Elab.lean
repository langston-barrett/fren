-- keep-sorted start
import FrenCli.Elab.Procedures
-- keep-sorted end

/-!
# Elaboration for `.fren` files

Elaborates types, functions, constants and nested items, finishes their
lints, and assembles files and the SMT-LIB prelude. Uses `Elab.Procedures`
for procedures, global expectations and trait laws, and `Elab.ItemSupport`
for shared item helpers. Expression elaboration is in `Elab.Expr`,
`Elab.ExprSupport` and `Elab.Model`.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

/-- Elaborates the clauses of the contract of the function `n` at `path`,
whose parameters are `vars`, and records the contract, and each clause's
definition for the prelude (`Reqs/Lang/Items#contracts`). Gives each
clause as a constraint of the function's body's procedure, named after the
function and the clause, a postcondition only if the function is defined;
and the questions about the tables and applications in them: a
precondition's under the other preconditions, a postcondition's under all
of them. -/
def elabContract (path n : Name) (defined : Bool) (vars : Array CVar) (clauses : Array (Bool × Ident × Expr)) (result : Ty)
    (span : Span) (fnParams : Array (Name × Fren.Core.FnTy × String) := #[]) (params : Array Name := vars.map (·.name)) : M (Array CVar × Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  -- The clauses' names share one namespace with the parameters
  -- (`lang::distinct_names`).
  let names := vars.map (·.name) ++ clauses.map fun (_, x, _) => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt names)[0]? then
    if k ≥ vars.size then err clauses[k - vars.size]!.2.1.span (Fren.Core.dupClauseMsg names[k]!)
  let mut k : Contract := { defined }
  let mut props := #[]
  let mut sites := #[]
  let mut occurrences : Std.HashMap Name Nat := {}
  modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
  for (post, x, e) in clauses do
    let cn := Name.mkSimple x.name
    liftMsg x.span (Fren.Core.checkNoBang cn)
    lintName .constraint cn x.span
    if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg cn)
    discard takeTables
    discard takeIndexes
    let cx : ExprCtx := { vars, place := .prop, contract? := some (path, post, params), fnParams }
    let (smt, t) ← elabExpr cx e
    liftMsg e.span (Fren.Core.checkType .bool t (some "note: a clause of a contract is a `Bool`"))
    let indexes ← takeIndexes
    let tables ← takeTables
    let place := if post then Fren.Core.IndexPlace.body else .assume
    lintBools e (← hidesIn cx)
    lintContractClause cx post cn n params e
    let app := s!"({itemSym path} {" ".intercalate (vars.toList.map fun v => quote v.name.toString)})"
    let value := quote (Fren.Core.contractValueName n (vars.map (·.name))).toString
    let output (formula : String) := if post && !defined then formula.replace app value else formula
    let entries ← if let some (predicate, templates) ← predicateClauses cx e then do
        let occurrence := occurrences.getD predicate 0 + 1
        occurrences := occurrences.insert predicate occurrence
        pure <| templates.map fun entry =>
          let sourceRef := Fren.Core.predicateCheckAtMember entry.name false
          ({ entry with
            name := if entry.name.isEmpty then x.name else x.name ++ "." ++ Fren.Core.showPath predicate ++ "@" ++ toString occurrence ++ "." ++ entry.name
            span := if sourceRef then entry.span else x.span }, sourceRef)
      else do
        let (nb, ng) := ((← get).itemBranches.size, (← get).itemMemberGroups.size)
        annotateBranches cx (n ++ cn) e
        -- Over the value, as its formula is.
        modify fun s => { s with
          itemBranches := s.itemBranches.extract 0 nb ++ (s.itemBranches.extract nb).map (·.map output)
          itemMemberGroups := s.itemMemberGroups.extract 0 ng ++ (s.itemMemberGroups.extract ng).map (·.map output) }
        pure #[({ file := (← get).file, name := x.name, span := x.span, formula := smt : NamedClause }, false)]
    for (entry, sourceRef) in entries do
      let cn := Name.mkSimple entry.name
      let owner := n ++ cn
      let sym := clauseSym path cn
      modify fun s => { s with clauseDefs := s.clauseDefs.push (sym, vars.map fun v => (v.name, v.ty), entry.formula) }
      if post then k := { k with posts := k.posts.push (cn, sym) } else k := { k with pres := k.pres.push (cn, sym) }
      props := props.push ({
        file? := some entry.file
        sourceRef
        kind := if post then .ensure else .assume
        name := owner
        span := entry.span
        smt := output entry.formula
        trigger? := none
        triggerSpan? := none
      } : CProp)
      sites := sites ++ (tables ++ entry.tables).map fun (sp, question, goal) => (owner, place, sp, question, output goal)
      modify fun s => { s with
        contractIndexes := s.contractIndexes ++ ((indexes ++ entry.indexes).filter (·.2.2.isSome)).map fun (sp, goal, kind) => (owner, place, sp, output goal, kind)
        itemBranches := s.itemBranches ++ entry.branches.map fun group => { (group.map output) with owner }
        itemMemberGroups := s.itemMemberGroups ++ entry.groups.map fun group => { (group.map output) with owner } }
  modify fun s => { s with contracts := s.contracts.insert path k }
  -- Without postconditions, an uninterpreted function's contract has
  -- nothing to realize.
  if defined || k.posts.isEmpty then return (vars, props.filter (defined || ·.kind == .assume), sites)
  -- With its result's type, which it is realized in.
  let name := Fren.Core.contractValueName n (vars.map (·.name))
  let ptype := (((← get).funPTys.find? path).map (·.2)).getD (.plain result)
  let v : CVar := { name, role := .output, isPub := true, ty := result, span, ptype, fact? := ← factOf ptype (quote name.toString) }
  return (vars.push v, props, sites)

/-- Records what each application of the uninterpreted function at `path`,
whose result has the declared type `rp`, brings: what its result's type
does, a `Nat`'s among it (`State.funFacts`). -/
def noteResultFact (path : Name) (rp : Fren.Core.PTy) : M Unit := noteResultFactAt (itemSym path) rp

/-- Records the tables of the body of the function `n`, whose parameters
are `vars`, or of the value of the constant `n`, just elaborated, its
subset types' `obligations`, and the questions about the tables and
applications of the function's contract and its clauses, `contract`, as a
procedure for their checks (`State.bodies`), if it has any questions or
postconditions to check. -/
def noteBody (n : Name) (span : Span) (vars : Array CVar)
    (contract : Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := (#[], #[]))
    (fn? : Option Name := none) (obligations : Array (Span × String × Option (String × Bool)) := #[])
    (generic : Bool := false) : M Unit := do
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.body, sp, q, g)
  -- The indexes of its contract's clauses are not checked, nor their
  -- values given where subset types are declared.
  discard takeIndexes
  let (props, sites) := contract
  -- Its indexes are not checked either.
  let obligations := obligations.filter (·.2.2.isSome)
  if tables.isEmpty && sites.isEmpty && obligations.isEmpty && (← get).contractIndexes.isEmpty && !props.any (·.kind == .ensure) then return
  modify fun s => { s with
    bodies := s.bodies.push { path := s.module, file := s.file, span, vars, props, decidable := !s.outsideCore
                              tables := tables ++ sites, natApps := s.natApps, bodyOf? := some n, fn?, generic, guarded := s.guardedUsed
                              indexes := (obligations.map fun (sp, g, t) => (n, .body, sp, g, t)) ++ s.contractIndexes
                              branchGroups := s.itemBranches
                              memberGroups := s.itemMemberGroups
                              recursive := fn?.any s.recursiveDefs.contains } }

/-- The function type written `segs`, a defined function's parameter's
(`Reqs/Lang/HigherOrder#function-types`): its parameters' and result's
types are neither `Nat`s, subset types nor function types
(`lang::function_type_parts`). -/
def elabFnTy (segs : Array Ident) : M Fren.Core.FnTy := do
  let some (ps, r) := Fren.Core.splitFnSegs (segs.map (·.name)) | internal (typeSpan segs) "a function type"
  -- The segments of each part, which `splitFnSegs` gives by name.
  let mut i := 1
  let mut parts : Array (Array Ident) := #[]
  for p in ps do
    parts := parts.push (segs.extract i (i + p.size))
    i := i + p.size + 1
  parts := parts.push (segs.extract (segs.size - r.size) segs.size)
  let mut tys := #[]
  for part in parts do
    if part.isEmpty then internal (typeSpan segs) "a function type's part"
    if part.any (·.name == Parser.fnSeg) then
      if let some msg := Fren.Core.fnPartMsg? .function then err (typeSpan part) msg
    let pt ← elabPTy part
    let k : Fren.Core.FnPart := if pt.ty == .nat then .nat else if pt.pat?.isSome then .pattern else .plain
    if let some msg := Fren.Core.fnPartMsg? k then err (typeSpan part) msg
    tys := tys.push pt.ty
  return { params := tys.pop, result := tys.back! }

/-- `fn_params_excessive_bools` on the function `n`, declared at `span`,
whose parameters have the types `params` (`lint::fn_params_excessive_bools`). -/
def lintFnBools (n : Name) (span : Span) (params : Array Ty) : M Unit := do
  let nBools := (params.filter (· == .bool)).size
  if Fren.Core.fnParamsExcessiveBools nBools then lint .fnParamsExcessiveBools span (Fren.Core.fnParamsExcessiveBoolsMsg n nBools)

/-- Reports the lints of the string literals and comments of the current
item, at its level (`literalLints`). -/
def lintLiterals : M Unit := do
  for (l, span, msg) in (← get).literals do lintFix l span msg
  modify fun s => { s with literals := #[] }

/-- What `F0215` calls the item `item`, after `set_option ... in`, if it is
a function or a constant, through further settings with `in`, and what
its checks are of: a body, a constant's value, or a contract. -/
partial def evidenceTarget? : Item → Option (String × Fren.Core.CheckedItem)
  | .function _ _ _ _ _ body .. => some ("a function", if body.isSome then .body else .contract)
  | .const .. => some ("a constant", .body)
  | .lintSetting _ _ _ _ _ (some body) => evidenceTarget? body
  | _ => none

/-- Records that the settings that set `lints` here are in effect at an
item, or at a setting that reads their level (`unused_lint_setting`). -/
def noteSettingsSeen (lints : Array Lint := Lint.all) : M Unit :=
  modify fun s => { s with seenSettings := lints.foldl (init := s.seenSettings) fun acc l =>
    match (s.levels.get l).setting? with
    | some i => if acc.contains i then acc else acc.push i
    | none => acc }

/-- Elaborates an enumeration (`Reqs/Lang/Items#enumerations`). -/
def elabEnum (isPub : Bool) (name : Ident) (variants : Array (Ident × Option (Array (Array Ident)))) (isOrdered : Bool)
    (params : Array Ident) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "enum" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .enumeration n name.span
  let path := module ++ n
  let params ← elabTypeParams params
  modify fun s => { s with typeParams := params }
  let mut vs := #[]
  let mut ctors := #[]
  let mut nRecursive := 0
  let mut unbounded := false
  let mut payloadTys : Array (Array (Fren.Core.PTy × Span)) := #[]
  -- Distinct names (`lang::distinct_names`).
  if let some k := (Fren.Core.repeatsAt (variants.map (Name.mkSimple ·.1.name)))[0]? then
    err variants[k]!.1.span (Fren.Core.dupVariantMsg (Name.mkSimple variants[k]!.1.name))
  for (v, payload?) in variants do
    let vn := Name.mkSimple v.name
    liftMsg v.span (Fren.Core.checkItemName "variant" vn)
    lintName .variant vn v.span
    vs := vs.push vn
    let mut fs := #[]
    let mut pts := #[]
    for segs in payload?.getD #[], k in [0:(payload?.getD #[]).size] do
      checkFnTypeSite .payload segs
      -- The enum's own name, which is not declared yet (`lang::field_type`).
      let (_, ownInSet) := ownIn segs name
      let (own, declared, nested) := ownArgs segs name params
      let tspan := typeSpan segs
      if ownInSet then err tspan (Fren.Core.recursiveSetMsg path)
      -- A recursive payload is the enumeration with its own parameters
      -- (`lang::type_parameter_place`).
      let place := Fren.Core.recursivePlace declared nested
      if (own || nested) && !Fren.Core.typeParamPlaceAccepted place then
        err tspan (Fren.Core.typeParamPlaceMsg .anonymous place (Fren.Core.ownWritten path params) !params.isEmpty)
      let pt ← if own then pure (.plain (Ty.enum path (params.toList.zipIdx.map fun (p, k) => .param k p)))
        else elabPTy segs
      noteResolved "type" tspan fun _ => pt.ty.showQualified
      let t := pt.ty
      pts := pts.push (pt, tspan)
      let abstract := t.abstractWithin?
      unless Fren.Core.fieldTypeAccepted abstract.isSome own ownInSet true do
        err tspan (Fren.Core.abstractFieldMsg (abstract.getD path) true (!(t matches .abstract _)))
      unbounded := unbounded || own || (← get).unbounded t
      fs := fs.push (Name.mkSimple (toString k), t)
    -- Recursive if a payload's type is the enumeration or built from it
    -- (`lang::well_founded`).
    let own := (Fren.Core.PTy.plain (Ty.enum path (params.toList.zipIdx.map fun (p, k) => .param k p))).node
    if Fren.Core.recursiveVariant (← get).shapeOf own (pts.toList.map (·.1.node)) then nRecursive := nRecursive + 1
    ctors := ctors.push (vn, fs)
    payloadTys := payloadTys.push pts
  unless Fren.Core.wellFounded variants.size nRecursive do err name.span (Fren.Core.illFoundedMsg n)
  -- A recursive enumeration's payloads are never `Nat`s (`lang::nat_place`),
  -- and a constraint of one is outside the decidable core
  -- (`lang::subset_place`).
  let isRecursive := nRecursive > 0
  let shape : Fren.Core.DataShape := { recursive := isRecursive, parts := payloadTys.map (·.map (·.1)) }
  if isRecursive then
    let st ← get
    for pts in payloadTys do
      for (pt, tspan) in pts do
        unless pt.ty != .nat do err tspan (Fren.Core.natPlaceMsg .recursivePayload)
        if (pt.cons (fun q => if q == path then some shape else st.shapeOf q) true).isSome then
          lint .undecidable tspan Fren.Core.undecidableRecursivePayloadMsg
  -- `enum_variant_names` (`lint::enum_variant_names`, `lint::variant_has_enum_name`).
  if let some msg := Fren.Core.enumVariantNamesMsg? n vs then lint .enumVariantNames name.span msg
  for (v, _) in variants, vn in vs do
    if let some msg := Fren.Core.variantNameMsg? n vn then lint .enumVariantNames v.span msg
  -- Only an enumeration without payloads may be ordered
  -- (`lang::ordered_declaration`); the first payload is reported.
  let withPayload := variants.filter (·.2.isSome)
  unless Fren.Core.orderedDeclAccepted isOrdered withPayload.size none do
    let (v, _) := withPayload[0]!
    err v.span (Fren.Core.orderedPayloadMsg n (Name.mkSimple v.name))
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .enumeration, path, level := s.levels.get .deadCode }, name.span) }
  modify fun s => { s with
    table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs }
    datatypes := s.datatypes.push { path, isRecord := false, ctors, unbounded, ordered := isOrdered, params
                                    lean? := Fren.Core.leanTypeOf? path : DataDecl }.withPrelude
    shapes := s.shapes.insert path shape
    typeParams := #[] }
  -- Each read of a recursive enumeration's payload brings the payload's
  -- constraint (`Fren.Core.readCons`), as an application does.
  if isRecursive then
    let st ← get
    let some d := st.dataOf? path | pure ()
    for (c, fs) in ctors, v in [0:ctors.size] do
      for k in [0:fs.size] do
        if let some c' := Fren.Core.readCons st.shapeOf path v k then
          modify fun s => { s with funFacts := s.funFacts.insert (d.selSym c k) (consSmt st.dataOf? c' factHole) }

/-- Elaborates a record (`Reqs/Lang/Items#records`). -/
def elabRecord (isPub : Bool) (name : Ident) (fields : Array (Ident × Option (Array Ident))) (isOrdered : Bool)
    (params : Array Ident) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "record" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .record n name.span
  let path := module ++ n
  let params ← elabTypeParams params
  -- A generic record is not ordered, for now (`Fren.Core.orderedGenericAccepted`).
  unless Fren.Core.orderedGenericAccepted isOrdered params.size do err name.span (Fren.Core.orderedGenericMsg n)
  modify fun s => { s with typeParams := params }
  let mut fs : Array (Name × Ty) := #[]
  let mut fieldTys : Array Fren.Core.PTy := #[]
  -- Distinct names (`lang::distinct_names`).
  if let some k := (Fren.Core.repeatsAt (fields.map (Name.mkSimple ·.1.name)))[0]? then
    err fields[k]!.1.span (Fren.Core.dupFieldMsg (Name.mkSimple fields[k]!.1.name))
  for (f, ty?) in fields do
    let fn := Name.mkSimple f.name
    liftMsg f.span (Fren.Core.checkNoBang fn)
    lintName .field fn f.span
    if let some segs := ty? then
      checkFnTypeSite .field segs
      let (_, ownInSet) := ownIn segs name
      let (own, _, nested) := ownArgs segs name params
      if own || nested then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveRecordMsg n)
      if ownInSet then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveSetMsg path)
    let pt ← varPTy ty? f
    let t := pt.ty
    fieldTys := fieldTys.push pt
    if let some p := t.abstractWithin? then
      err ((ty?.map fun segs => segs[0]!.span.to segs.back!.span).getD f.span)
        (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
    fs := fs.push (fn, t)
  -- `struct_field_names` (`lint::struct_field_names`, `lint::field_has_record_name`).
  if let some msg := Fren.Core.structFieldNamesMsg? n (fs.map (·.1)) then lint .structFieldNames name.span msg
  for (f, _) in fields, (fn, _) in fs do
    if let some msg := Fren.Core.fieldNameMsg? n fn then lint .structFieldNames f.span msg
  -- `struct_excessive_bools` (`lint::struct_excessive_bools`).
  let nBools := (fs.filter (·.2 == .bool)).size
  if Fren.Core.structExcessiveBools nBools then lint .structExcessiveBools name.span (Fren.Core.structExcessiveBoolsMsg n nBools)
  let st ← get
  -- An ordered record's fields are ordered (`lang::ordered_declaration`);
  -- the first that is not is reported.
  let first? := Fren.Core.PTy.firstUnordered? st.orderedDecl fieldTys.toList
  unless Fren.Core.orderedDeclAccepted isOrdered 0 first? do
    if let some k := first? then
      let (f, ty?) := fields[k]!
      err ((ty?.map fun segs => segs[0]!.span.to segs.back!.span).getD f.span)
        (Fren.Core.unorderedFieldMsg .record n fs[k]!.1 fs[k]!.2)
  let unbounded := fs.any fun (_, t) => st.unbounded t
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
  modify fun s => { s with
    table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
    datatypes := s.datatypes.push { path, isRecord := true, ctors := #[(`«{}», fs)], unbounded, ordered := isOrdered, params : DataDecl }.withPrelude
    shapes := s.shapes.insert path { isRecord := true, parts := #[fieldTys] }
    typeParams := #[] }

/-- Elaborates a newtype (`Reqs/Lang/Items#newtypes`). -/
def elabNewtype (isPub : Bool) (name : Ident) (fields : Array (Array Ident)) (isOrdered : Bool) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "record" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .record n name.span
  let path := module ++ n
  -- Exactly one field, whose type is accepted as a record's field's
  -- (`lang::newtype`).
  let some segs := fields[0]? | err name.span (Fren.Core.newtypeFieldsMsg path 0)
  unless Fren.Core.newtypeAccepted fields.size true do err name.span (Fren.Core.newtypeFieldsMsg path fields.size)
  let span := typeSpan segs
  checkFnTypeSite .field segs
  let (own, ownInSet) := ownIn segs name
  if own then err span (Fren.Core.recursiveRecordMsg n)
  if ownInSet then err span (Fren.Core.recursiveSetMsg path)
  let pt ← elabPTy segs
  let t := pt.ty
  if let some p := t.abstractWithin? then err span (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
  -- An ordered newtype's underlying type is ordered
  -- (`lang::ordered_declaration`).
  unless Fren.Core.orderedDeclAccepted isOrdered 0 (Fren.Core.PTy.firstUnordered? (← get).orderedDecl [pt]) do
    err span (Fren.Core.unorderedFieldMsg .newtype n (Name.mkSimple "0") t)
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
  modify fun s => { s with
    table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
    newtypes := s.newtypes.insert path t
    orderedNewtypes := if isOrdered then s.orderedNewtypes.push path else s.orderedNewtypes
    shapes := s.shapes.insert path { isRecord := true, isNewtype := true, parts := #[#[pt]] } }

/-- Elaborates a type alias (`Reqs/Lang/Items#type-aliases`). -/
def elabTypeAlias (isPub : Bool) (name : Ident) (ty : Array Ident) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "type alias" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .typeAlias n name.span
  let t ← elabPTy ty
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .typeAlias, path := module ++ n, level := s.levels.get .deadCode }, name.span) }
  modify fun s => { s with
    table := s.table.addItem { kind := .typeItem, path := module ++ n, isPub, owner := s.module }
    aliases := s.aliases.insert (module ++ n) t }

/-- Elaborates an abstract type (`Reqs/Lang/Items#abstract-types`). -/
def elabAbstractType (isPub : Bool) (name : Ident) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "abstract type" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .abstractType n name.span
  let path := module ++ n
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .abstractType, path, level := s.levels.get .deadCode }, name.span) }
  modify fun s => { s with
    table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
    sorts := s.sorts.push path }

/-- Records the clauses of the function at `path`, whose parameters are
`vars` and whose body `body` elaborates to `smt`, in `namedPredicates`
when the body is a conjunction, observes members (`observedMembers`) or
is a predicate's clauses: each conjunction leaf is elaborated
independently at the definition site, rather than its raw source syntax
being substituted into a caller's scope. It then restores the state from
before those elaborations, so that only `namedPredicates` changes. -/
def notePredicateClauses (cx : ExprCtx) (path : Name) (vars : Array CVar) (body : Expr) (smt : String) : M Unit := do
  if body.conjunctionRoot || (observedMembers body).isSome || (← predicateClauses cx body).isSome then
    let leaves := if body.conjunctionRoot then body.clauseLeaves { name := "", span := body.span } else #[({ name := "", span := body.span }, body)]
    if true then
      let saved ← get
      let mut templates := #[]
      let mut nestedOccurrences : Std.HashMap Name Nat := {}
      for (label, expression) in leaves do
        discard takeIndexes
        discard takeTables
        let (formula, _) ← elabExpr cx expression
        let indexes ← takeIndexes
        let tables ← takeTables
        modify fun s => { s with itemBranches := #[], itemMemberGroups := #[] }
        annotateBranches cx (Name.mkSimple "#template") expression
        let own := ({
          file := saved.file
          name := label.name
          span := label.span
          formula := formula
          indexes := indexes
          tables := tables
          branches := (← get).itemBranches
          groups := (← get).itemMemberGroups
        } : NamedClause)
        if let some (nestedPath, nested) ← predicateClauses cx expression then
          let occurrence := nestedOccurrences.getD nestedPath 0 + 1
          nestedOccurrences := nestedOccurrences.insert nestedPath occurrence
          let nestedPrefix := Fren.Core.showPath nestedPath ++ "@" ++ toString occurrence
          for clause in nested do
            let name := (if label.name.isEmpty then "" else label.name ++ ".") ++ nestedPrefix ++ (if clause.name.isEmpty then "" else "." ++ clause.name)
            let rename (n : Name) := if !clause.name.isEmpty then n else Name.mkSimple ("#template." ++ nestedPrefix ++ (n.toString.dropPrefix? "#template" |>.getD ("." ++ n.toString)))
            templates := templates.push { clause with
              name := name
              indexes := indexes ++ clause.indexes
              tables := tables ++ clause.tables
              branches := clause.branches.map fun group => { group with members := group.members.map fun member => { member with name := rename member.name } }
              groups := clause.groups.map fun group => { group with members := group.members.map fun member => { member with name := rename member.name } } }
        else templates := templates.push own
      modify fun s => { s with itemBranches := #[], itemMemberGroups := #[] }
      annotateBranches cx (Name.mkSimple "#template") body
      let whole : NamedClause := {
        file := saved.file
        name := ""
        span := body.span
        formula := smt
        branches := (← get).itemBranches
        groups := (← get).itemMemberGroups
      }
      set { saved with namedPredicates := saved.namedPredicates.insert path { sourcePath := path, params := vars.map (fun (v : CVar) => v.name), clauses := templates, whole? := some whole } }

/-- The parameters of a function, declared like a procedure's parameters, but
for the function parameters, which are pushed, each with its position, to
the `StateT`'s array, and which only a defined function has
(`lang::function_type_place`). -/
def fnParamsOf (params : Array (Array Ident × Option (Array Ident))) (defined : Bool) :
    StateT (Array (Nat × Name × Span × Fren.Core.FnTy)) M (Array CVar) := do
  let mut vars : Array CVar := #[]
  -- Distinct names (`lang::distinct_names`).
  -- By the names they declare, without the `!` of shadowing.
  let declared := params.map fun p => Name.mkSimple (declaredIdent p.1[0]!).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err params[k]!.1[0]!.span (Fren.Core.dupParamMsg declared[k]!)
  for (p, ty?) in params, j in [0:params.size] do
    let x ← declare p[0]!
    let xn := Name.mkSimple x.name
    lintName .variable xn x.span
    if let some segs := ty?.filter (·[0]?.any (·.name == Parser.fnSeg)) then
      unless defined do checkFnTypeSite .uninterpretedParameter segs
      let ft ← elabFnTy segs
      modify (·.push (j, xn, x.span, ft))
      continue
    let ptype ← varPTy ty? x
    let fact? ← factOf ptype (quote xn.toString)
    vars := vars.push { name := xn, role := .input, isPub := true, ty := ptype.ty, span := x.span, ptype, fact? }
  return vars

/-- Records the signature of the generic function at `path`, named `n`, with
its type parameters `tps`, written `typeParams`, as `Ty.param`, each
inferred at applications from it (`lang::generic_signature`); nothing for a
function that is not generic. -/
def noteSignature (path n : Name) (typeParams : Array Ident) (tps : Array Name) (ps : Array Ty)
    (rp : Fren.Core.PTy) (defined : Bool) : M Unit := do
  if tps.isEmpty then return
  let r := rp.ty
  let declared := ps.map (·.asParams path tps)
  if let some k := Fren.Core.firstUnmentioned? declared (r.asParams path tps) tps.size then
    err typeParams[k]!.span (Fren.Core.unmentionedTypeParamMsg n tps[k]!)
  let g : GenericFn := { params := tps, declared, result := r.asParams path tps, resultP := rp.asParams path tps, defined
                         file := (← get).file }
  modify fun s => { s with genericFns := s.genericFns.insert path g }

/-- Elaborates the function at `path`, named `n`, with the body `body`
(`Reqs/Lang/Items#defined-functions`): its parameters, its body, checked
against its result type, and its contract, which `contract` says it has. -/
def elabDefinedFunction (isPub : Bool) (name : Ident) (n path : Name) (typeParams : Array Ident)
    (tps : Array Name) (params : Array (Array Ident × Option (Array Ident))) (result : Option (Array Ident))
    (body : Expr) (clauses : Array (Bool × Ident × Expr)) (contract : Bool) (last : Span) : M Unit := do
  let (vars, fnPs) ← (fnParamsOf params true).run #[]
  lintFnBools n name.span (vars.map (·.ty))
  let rp ← varPTy result name
  let r := rp.ty
  -- The parameters in order, a function parameter's type standing in
  -- for its own (`HigherOrderFn.params`).
  let ptypes := Id.run do
    let mut out : Array Fren.Core.PTy := vars.map (·.ptype)
    for (j, _, _, ft) in fnPs do out := out.insertIdxIfInBounds j (.plain ft.result)
    return out
  modify fun s => { s with funPTys := s.funPTys.insert path (ptypes, rp) }
  -- Each type parameter is inferred at applications from the signature
  -- (`lang::generic_signature`), where a function parameter's type
  -- stands for its parameters' and its result's.
  let declared := vars.map (·.ty.asParams path tps)
  let fnDeclared := fnPs.flatMap fun (_, _, _, ft) => (ft.asParams path tps).params.push (ft.asParams path tps).result
  if let some k := Fren.Core.firstUnmentioned? (declared ++ fnDeclared) (r.asParams path tps) tps.size then
    err typeParams[k]!.span (Fren.Core.unmentionedTypeParamMsg n tps[k]!)
  if fnPs.isEmpty then noteSignature path n typeParams tps (vars.map (·.ty)) rp true
  -- Each function parameter is an uninterpreted function for the
  -- function's own checks (`Reqs/Lang/HigherOrder#function-parameters`).
  let fnParams := fnPs.map fun (_, x, _, ft) => (x, ft, itemSym (path ++ x))
  for (_, x, _, ft) in fnPs do
    modify fun s => { s with funs := s.funs.push (path ++ x, ft.params, ft.result) }
  discard takeTables
  discard takeIndexes
  modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
  -- A first-order function, generic or not, may apply itself, in a
  -- structural recursion (`lang::self_application`,
  -- `lang::structural_recursion`).
  let selfRec? := if Fren.Core.selfApplicable (!tps.isEmpty) (!fnPs.isEmpty) then
    some (vars.map (·.name), ({ params := vars.map (·.ty), result := r } : Fren.Core.FnTy), itemSym path) else none
  -- The body is checked against the result type (`lang::checked`).
  let cx : ExprCtx := { vars, place := .prop, selfFn := if (← get).inSubset then none else some n, expected? := Fren.Core.ExprSite.functionBody.expected (some r) none, fnParams, selfRec? }
  modify fun s => { s with recUses := #[], recApps := #[], recMatches := #[] }
  let (smt, t) ← elabExpr cx body
  let uses := (← get).recUses
  -- Existing self-recursion is a singleton structural group.
  let recursion := Fren.Core.selfRecursion vars.size (uses.toList.map (·.2))
  if let .structural i := recursion then
    if let some m := (← get).recMatches[0]? then err m (Fren.Core.recursiveMatchMsg path)
    modify fun s => { s with recursiveDefs := s.recursiveDefs.insert path, recursiveDecreasing := s.recursiveDecreasing.insert path i }
    -- Each of its applications is opaque, and brings its result type's
    -- constraint, as its postconditions, a hypothesis at a recursive
    -- application in its own body too (`lang::recursive_facts`).
    if Fren.Core.recursiveResultFact (rp.cons (← get).shapeOf).isSome then noteResultFact path rp
  notePredicateClauses cx path vars body smt
  noteObligation cx .body body.span rp smt
  let bodyTables ← takeTables
  let bodyObligations ← takeIndexes
  liftMsg body.span (Fren.Core.checkType r t (some s!"note: `{n}` returns `{r.show}`"))
  lintBools body (← hidesIn cx)
  -- A parameter that only the contract mentions is used too.
  let mentioned := (mentions body ++ clauses.flatMap fun (_, _, e) => mentions e).map (·.getRoot)
  let mentioned := if fnPs.isEmpty then mentioned
    else mentioned ++ body.appliedNames ++ clauses.flatMap fun (_, _, e) => e.appliedNames
  let paramSpans := Id.run do
    let mut out := vars.map fun v => (v.name, v.span)
    for (j, x, sp, _) in fnPs do out := out.insertIdxIfInBounds j (x, sp)
    return out
  for (x, sp) in Fren.Core.unmentioned paramSpans mentioned do
    lint .unusedVariables sp (Fren.Core.unusedParamMsg x)
  modify fun s => { s with defs := s.defs.push (path, vars.map fun v => (v.name, v.ty), r, smt)
                           guardedItems := if s.guardedUsed then s.guardedItems.insert path else s.guardedItems }
  -- What its applications need to unfold it (`elabHigherOrderApp`):
  -- its contract may apply it, to its own parameters.
  let hofParams := Id.run do
    let mut out : Array (Name × String × Fren.Core.HoParam) := vars.map fun v => (v.name, quote v.name.toString, .value (v.ty.asParams path tps))
    for (j, x, _, ft) in fnPs do out := out.insertIdxIfInBounds j (x, itemSym (path ++ x), .function (ft.asParams path tps))
    return out
  if !fnPs.isEmpty then
    let h : HigherOrderFn := { typeParams := tps, params := hofParams, result := r.asParams path tps, body := smt
                               calls := (← get).genericCalls }
    modify fun s => { s with hofs := s.hofs.insert path h }
    unless isPub do
      for (j, x, sp, _) in fnPs do
        let r : Fren.Core.HofParamRecord :=
          { path, index := j, name := x, generic := !tps.isEmpty, level := (← get).levels.get .needlessHigherOrder }
        modify fun s => { s with hofParams := s.hofParams.push (r, sp) }
  let clausesBefore := (← get).clauseDefs.size
  let (_, props, sites) ← if contract then elabContract path n true vars clauses r name.span fnParams (paramSpans.map (·.1)) else pure (vars, #[], #[])
  if !fnPs.isEmpty then
    let st ← get
    let newClauses := st.clauseDefs.extract clausesBefore st.clauseDefs.size
    let pres := ((st.contracts.find? path).map (·.pres)).getD #[] |>.filterMap fun (pn, sym) =>
      (newClauses.find? (·.1 == sym)).map fun (_, _, body) => (pn, body)
    let calls := st.genericCalls
    modify fun s => { s with hofs := s.hofs.modify path (fun h => { h with pres, calls }), fnTypeParams := none }
  -- What its instances need (`instantiate`).
  if !tps.isEmpty && fnPs.isEmpty then
    modify fun s => { s with
      genericFns := s.genericFns.insert path { (s.genericFns.find? path).getD default with
        vars := vars.map fun v => (v.name, v.ty), body := smt, calls := s.genericCalls
        clauses := s.clauseDefs.extract clausesBefore s.clauseDefs.size }
      fnTypeParams := none }
    for args in (← get).pendingInsts do discard (instantiate path args)
    modify fun s => { s with pendingInsts := #[] }
  modify fun s => { s with tables := bodyTables }
  let st ← get
  let pres := ((st.contracts.find? path).map (·.pres)).getD #[]
  let selfSites := st.recApps.flatMap fun (sp, args, gs) =>
    pres.map fun (pn, sym) =>
      let p := s!"({sym} {" ".intercalate args.toList})"
      (sp, Fren.Core.TableGoal.precondition path pn, if gs.isEmpty then p else s!"(=> {conj gs} {p})")
  modify fun s => { s with tables := s.tables ++ selfSites }
  noteBody n name.span vars (props, sites) path bodyObligations
  lintDeclared .function n name.span
  lintLines .function n name.span last

/-- Elaborates a function (`Reqs/Lang/Items#functions`). -/
def elabFunction (isPub : Bool) (name : Ident) (typeParams : Array Ident) (params : Array (Array Ident × Option (Array Ident)))
    (result : Option (Array Ident)) (body : Option Expr) (clauses : Array (Bool × Ident × Expr)) (last : Span)
    (block : FnBlockInfo) : M Unit := do
  modify fun s => { s with outsideCore := false, guardedUsed := false }
  modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
  let clauses := splitContractClauses clauses
  -- A precondition or body of its block that mentions the result
  -- (`F0165`).
  if let some (sp, r) := block.resultMention? then err sp (Fren.Core.fnResultMentionMsg r)
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkNoBang n)
  liftMsg name.span (Fren.Core.checkFnName n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .function n name.span
  startDeclared
  let path := module ++ n
  modify fun s => { s with item := path }
  -- The `use`s of its block, in its scope, as a procedure's
  -- (`Reqs/Lang/Items#function-blocks`).
  declareMemberUses path block.uses
  -- Its block's `let`s that nothing needs, as a procedure's
  -- (`unused_variables`).
  for x in block.unusedLets do
    lint .unusedVariables x.span (Fren.Core.unusedVariableMsg (Name.mkSimple (declaredIdent x).1.name) false true)
  -- Its type parameters, which are abstract types within it, whether it
  -- is defined or not (`lang::generic_function`).
  let tps ← elabTypeParams typeParams
  if !tps.isEmpty then
    modify fun s => { s with fnTypeParams := some (path, tps), genericCalls := #[], pendingInsts := #[]
                             sorts := s.sorts ++ tps.mapIdx fun k p => Fren.Core.typeParamPath path k p }
  let (params, body) := lambdaMatchFunction params body
  let contract := !clauses.isEmpty
  -- A parameter is named if it has a type after `:`, or is a `Bool`
  -- written `x?` (`lang::function_params`).
  let named (p : Array Ident × Option (Array Ident)) :=
    p.2.isSome || (p.1.size == 1 && (declaredIdent p.1[0]!).1.name.endsWith "?")
  unless Fren.Core.functionParamsAccepted body.isSome contract params.size (params.filter named).size do
    let bad := (params.find? (named · != (body.isSome || contract))).map (·.1[0]!.span) |>.getD name.span
    err bad (Fren.Core.functionParamsMsg path body.isSome contract)
  let paramVars : M (Array CVar) := return (← (fnParamsOf params body.isSome).run #[]).1
  match body with
  | none =>
    -- Generic or not, the `declare-fun` of the function itself; a generic
    -- one's is over its type parameters' sorts, for the checks of its
    -- contract, and each instance that an application uses has its own
    -- (`instantiate`).
    if !contract then
      let pps ← params.mapM (elabPTy ·.1)
      let ps := pps.map (·.ty)
      lintFnBools n name.span ps
      -- As for a variable, with the result type (`lang::bool_naming`),
      -- after the parameters, in source order.
      let rp ← varPTy result name
      noteSignature path n typeParams tps ps rp false
      noteResultFact path rp
      modify fun s => { s with funs := s.funs.push (path, ps, rp.ty), funPTys := s.funPTys.insert path (pps, rp) }
    else
      let vars ← paramVars
      lintFnBools n name.span (vars.map (·.ty))
      let rp ← varPTy result name
      noteSignature path n typeParams tps (vars.map (·.ty)) rp false
      noteResultFact path rp
      modify fun s => { s with funs := s.funs.push (path, vars.map (·.ty), rp.ty)
                               funPTys := s.funPTys.insert path (vars.map (·.ptype), rp) }
      discard takeTables
      modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
      let clausesBefore := (← get).clauseDefs.size
      let (vars, props, sites) ← elabContract path n false vars clauses rp.ty name.span
      -- What its instances need (`instantiate`): its clauses, and the
      -- generic functions that they apply.
      if !tps.isEmpty then
        modify fun s => { s with
          genericFns := s.genericFns.insert path { (s.genericFns.find? path).getD default with
            calls := s.genericCalls, clauses := s.clauseDefs.extract clausesBefore s.clauseDefs.size } }
      noteBody n name.span vars (props, sites) path (generic := !tps.isEmpty)
      lintDeclared .function n name.span
      lintLines .function n name.span last
    modify fun s => { s with fnTypeParams := none }
  | some body =>
    elabDefinedFunction isPub name n path typeParams tps params result body clauses contract last
  unless isPub do
    modify fun s =>
      let r : Fren.Core.ItemRecord :=
        -- A trait's method is never dead (`lint::dead_item`).
        { what := if s.inTrait then .method else .function, path, level := s.levels.get .deadCode
          singleCall? := body.map fun _ => s.levels.get .singleCallFn }
      { s with items := s.items.push (r, name.span) }
  modify fun s => { s with
    outsideCoreItems := if s.outsideCore then s.outsideCoreItems.insert path else s.outsideCoreItems.erase path
    table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }

/-- Elaborates a constant (`Reqs/Lang/Items#constants`). -/
def elabConst (isPub : Bool) (name : Ident) (ty : Array Ident) (value : Expr) : M Unit := do
  modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkConstName n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .constant n name.span
  let pt ← elabPTy ty
  let t := pt.ty
  -- Its value must be known (`lang::constant`): first its type, then,
  -- once the functions it applies count as used, its value.
  let abstract := t matches .abstract _
  unless Fren.Core.constantAccepted abstract false do
    err (ty[0]!.span.to ty.back!.span) (Fren.Core.unknownConstantMsg abstract)
  let before := (← get).applied.size
  discard takeTables
  discard takeIndexes
  modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
  let cx : ExprCtx := { vars := #[], place := .prop, expected? := Fren.Core.ExprSite.constantValue.expected (some t) none }
  let (smt, t') ← elabExpr cx value
  noteObligation cx .constant value.span pt smt
  noteBody n name.span #[] (obligations := ← takeIndexes)
  let applies := (← get).applied.extract before
  unless Fren.Core.constantAccepted abstract applies.isEmpty.not do
    err applies[0]! (Fren.Core.unknownConstantMsg abstract)
  liftMsg value.span (Fren.Core.checkType t t' (some s!"note: `{n}` has type `{t.show}`"))
  lintBools value (← hidesIn cx)
  let path := module ++ n
  unless isPub do
    modify fun s => { s with items := s.items.push ({ what := .constant, path, level := s.levels.get .deadCode }, name.span) }
  let int? ← if t == .int || t == .nat then intConstValue? { vars := #[], place := .prop } value else pure none
  modify fun s => { s with
    table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
    consts := s.consts.insert path (smt, t)
    outsideCoreItems := if s.outsideCore then s.outsideCoreItems.insert path else s.outsideCoreItems.erase path
    guardedItems := if s.guardedUsed then s.guardedItems.insert path else s.guardedItems
    constInts := match int? with | some v => s.constInts.insert path v | none => s.constInts }

-- `elabItem` calls a function of its own for each larger kind of item,
-- and `elabFunction` for each of its larger parts. Lean's compiler, whose
-- simplifier takes time superlinear in a function's size, took 35 s on an
-- `elabItem` that held them all, and clang 11 s, on the path of every
-- build of `fren` and `fren_test`; it now takes a few seconds on each.
mutual
partial def elabItem (item : Item) : M Unit := do
  -- An item read whole whose first error is a clause's keyword's, of
  -- which nothing else is reported (`lang::item_error`).
  if let .broken span msg := item then err span msg
  -- Paths resolve in the module, but in a procedure's or a function's
  -- block with `use`s, which sets its own scope.
  modify fun s => { s with scope := s.module }
  -- A `set_option` leaves them to the item after it.
  unless item matches .lintSetting .. do
    lintLiterals
    let sp := (← get).itemSpan
    for (comma, closer) in (← get).trailingCommas do
      if sp.start ≤ comma.start && comma.start < sp.stop then
        lintFix .unnecessaryTrailingComma comma (Fren.Core.unnecessaryTrailingCommaMsg closer)
  -- A check, such as `#fren_check`, is not about any lint.
  unless item matches .lintSetting .. | .check _ do noteSettingsSeen
  match item with
  | .mod isPub segs => do
    let (path, new) ← liftResolve segs ((← get).table.declareModule (segNames segs) isPub)
    for i in new do
      if let some seg := segs[i.path.components.length - 1]? then
        -- Its name, without the `!` of one that shadows the prelude's, as
        -- the module's path has it.
        lintName .module (Name.mkSimple i.path.getString!) seg.span
        if let some msg := Fren.Core.moduleInceptionMsg? i.path then lint .moduleInception seg.span msg
        if let some msg := Fren.Core.moduleNameMsg? .module i.path.getPrefix (Name.mkSimple i.path.getString!) then
          lint .moduleNameRepetitions seg.span msg
    modify fun s => { s with table := new.foldl (·.addItem ·) s.table, module := path, scope := path }
  | .use span segs glob => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    declareUse segs glob { item := span, removal, path := segs[0]!.span.to segs.back!.span }
  | .useGroup span pre paths => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    for p in paths do
      declareUse (pre ++ p) false
        { item := span, removal, path := p[0]!.span.to p.back!.span, pre? := some (pre[0]!.span.to pre.back!.span) }
  | .enum isPub name variants isOrdered params => elabEnum isPub name variants isOrdered params
  | .record isPub name fields isOrdered params => elabRecord isPub name fields isOrdered params
  | .newtype isPub name fields isOrdered => elabNewtype isPub name fields isOrdered
  | .subsetType isPub name binder base clauses => elabSubsetType isPub name binder base clauses
  | .typeAlias isPub name ty => elabTypeAlias isPub name ty
  | .abstractType isPub name => elabAbstractType isPub name
  | .function isPub name typeParams params result body clauses last block =>
    elabFunction isPub name typeParams params result body clauses last block
  | .comp isPub name header members close spans openStop => do
    -- Its declaration and line lints are about its name, without its `!`.
    let shown := (declaredIdent name).1
    modify fun s => { s with item := s.module ++ Name.mkSimple shown.name }
    -- Its `use`s end with it, even when it has an error.
    modify fun s => { s with inCompBody := false }
    try elabComp isPub name header members spans openStop
    catch e =>
      modify (fun s => { s.keepLints e.state with scope := s.module })
      -- Its declaration and line lints, after an error in its members.
      if e.state.inCompBody then
        lintDeclared .component (Name.mkSimple shown.name) shown.span
        lintLines .component (Name.mkSimple shown.name) shown.span close
      throw { e with state := ← get }
    lintDeclared .component (Name.mkSimple shown.name) shown.span
    lintLines .component (Name.mkSimple shown.name) shown.span close
  | .const isPub name ty value => elabConst isPub name ty value
  | .global name binders body => do
    modify fun s => { s with item := s.module ++ Name.mkSimple (declaredIdent name).1.name }
    elabGlobal name binders body
  | .globalBlock name header members close spans openStop => do
    let shown := (declaredIdent name).1
    modify fun s => { s with item := s.module ++ Name.mkSimple shown.name }
    modify fun s => { s with inCompBody := false }
    -- Whether its block applies an uninterpreted function, which records
    -- the application (`lang::induction_candidate`).
    let applied := (← get).applied.size
    try elabComp false name header members spans openStop (global := true)
    catch e =>
      modify (fun s => { s.keepLints e.state with scope := s.module })
      if e.state.inCompBody then
        lintDeclared .global (Name.mkSimple shown.name) shown.span
        lintLines .global (Name.mkSimple shown.name) shown.span close
      throw { e with state := ← get }
    lintDeclared .global (Name.mkSimple shown.name) shown.span
    lintLines .global (Name.mkSimple shown.name) shown.span close
    elabInductions name header members ((← get).applied.size > applied)
  -- Never reached: a broken item's error is thrown above, before its lints.
  | .broken .. => pure ()
  | .law name params body => do
    -- Only a trait's members are laws, which the parser reads only there.
    modify fun s => { s with item := s.module ++ Name.mkSimple (declaredIdent name).1.name }
    elabLaw name params body
  | .«trait» isPub name members _ => elabTrait isPub name members
  | .claim tested segs texts => do
    let path ← match ← resolve segs with
      | .item { kind := .compItem, path, .. } => pure path
      | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.notACompMsg r)
    if !tested then
      for (why, span) in texts do liftMsg span (Fren.Core.checkTrusted why)
    modify fun s => { s with claims := s.claims.push { file := s.file, tested, comp := path, texts } }
  | .check none => pure ()
  | .check (some segs) => do
    match ← resolve segs with
    | .item { kind := .compItem, .. } | .item { kind := .expectItem, .. } => pure ()
    | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.wrongKindMsg "a procedure or a global expectation" r)
  | .lintSetting stx opt value valueSpan removal body? => elabLintSetting stx opt value valueSpan removal body?

/-- Elaborates a subset type (`Reqs/Lang/SubsetTypes`), with the items it declares. -/
partial def elabSubsetType (isPub : Bool) (name binder : Ident) (base : Array Ident) (clauses : Array (Ident × Expr)) : M Unit := do
  let module := (← get).module
  let n := Name.mkSimple (declaredIdent name).1.name
  let path := module ++ n
  liftMsg name.span (Fren.Core.checkItemName "subset type" n)
  liftMsg name.span ((← get).table.checkFreshItem module n (declaredIdent name).2)
  let baseTy ← elabPTy base
  let mut seen : Array Name := #[]
  let mut invariants := baseTy.invariants
  let mut previous : Array Expr := #[]
  let mut pattern := baseTy.pat?
  for (label, expression) in clauses do
    let logical := Name.mkSimple label.name
    if seen.contains logical then
      err label.span { code? := some "F0372", headline := s!"duplicate invariant `{Fren.Core.showPath (path ++ logical)}`", label? := some "already declared in this subset type" }
    seen := seen.push logical
    let predicate := subsetPredicateIdent name label
    let before := (← get).bodies.size
    let generatedBefore ← get
    let priorSubset := (← get).inSubset
    modify fun st => { st with inSubset := true }
    -- Only the lints of the invariant's own source are reported, as for
    -- any expression, whether or not it has a static error: not those of
    -- the binder, which the pattern shorthand does not write.
    -- The predicate's generated name borrows the invariant label's span;
    -- its result type is not a type declared at that label.
    -- The shorthand's unwritten binder borrows the base type's span,
    -- which is a written type, rather than a local value expression.
    let generatedAnnotation (a : ResolvedAnnotation) : Bool :=
      a.file == generatedBefore.file &&
        ((a.kind == "type" && a.span == predicate.span) ||
          (Fren.Core.generatedName binder.name && a.span == binder.span &&
            (a.kind == "local" || a.kind == "expr")))
    let ownSource (st : State) : State := { st with
      lintReports := generatedBefore.lintReports ++ (st.lintReports.extract generatedBefore.lintReports.size st.lintReports.size).filter (fun report => report.ref.start >= expression.span.start && report.ref.stop <= expression.span.stop)
      lintFixes := generatedBefore.lintFixes ++ (st.lintFixes.extract generatedBefore.lintFixes.size st.lintFixes.size).filter (fun fix => fix.span.start >= expression.span.start && fix.span.stop <= expression.span.stop)
      natReports := generatedBefore.natReports
      resolved? := st.resolved?.map (·.filter (!generatedAnnotation ·)) }
    try
      elabItem (.function true predicate #[] #[(#[binder], some base)] none (some expression) #[] expression.span {})
    catch failure =>
      if failure.diags.any (·.msg.code? == some "F0201") then
        err expression.span { code? := some "F0373", headline := "an invariant may mention only its binder, constants and functions", label? := some (Fren.Core.invariantScopeLabel binder.name) }
      throw { failure with state := ownSource failure.state }
    modify fun st => { ownSource st with inSubset := priorSubset }
    -- Its full-definedness check is guarded by earlier invariants below,
    -- rather than checked unconditionally as an ordinary function body.
    modify fun st => { st with bodies := st.bodies.extract 0 before }
    invariants := invariants.push { name := path ++ logical, predicate := module ++ Name.mkSimple predicate.name }
    if pattern.isNone && clauses.size == 1 then
      if let .is _ (.path _ #[x]) p := expression then
        if x.name == binder.name then
          let (pat, bs, _) ← resolvePattern { vars := #[], place := .prop } baseTy.ty binder.name false true p
          if bs.isEmpty then pattern := some pat
    let validator := subsetCheckIdent name s!"defined_{label.name.toLower}"
    let localName : Ident := { name := "subset_predicate?", span := label.span }
    let assumptions := previous.mapIdx fun i e => Member.prop .assume { name := s!"earlier_{i}", span := label.span } e
    let header := #[Member.var true true false binder (some base) none]
    let body := assumptions.push (.var false false false localName none (some expression))
    withoutGhostLints <| elabItem (.comp true validator header body expression.span (body.map fun _ => expression.span) label.span.stop)
    modify fun st => { st with comps := st.comps.map fun c => if c.path == module ++ Name.mkSimple validator.name then
      { c with subsetInvariant? := some (path ++ logical) } else c }
    previous := previous.push expression
  let restricted := { baseTy with invariants, pat? := pattern, text := name.name }
  modify fun st => { st with
    table := st.table.addItem { kind := .typeItem, path, isPub, owner := module }
    aliases := st.aliases.insert path restricted }
  let inhabit := subsetCheckIdent name "inhabited"
  let binderExpr := Expr.path binder.span #[binder]
  let guarantees := clauses.map fun (label, _) =>
    let predicate := subsetPredicateIdent name label
    Member.prop .ensure label (.app label.span #[predicate] #[binderExpr])
  let header := #[Member.var false true false binder (some base) none]
  modify fun st => { st with inSubset := true }
  withoutGhostLints <| elabItem (.comp true inhabit header guarantees name.span (guarantees.map fun _ => name.span) name.span.stop)
  modify fun st => { st with inSubset := false, comps := st.comps.map fun c => if c.path == module ++ Name.mkSimple inhabit.name then
    { c with subset? := some path, finiteModel := true } else c }

/-- Elaborates the functions generated for induction on the parameters of
the global expectation `name`, just elaborated, whose header and block are
`header` and `body`, where its block applies an uninterpreted function if
`abstract` (`Reqs/Lang/Recursion#induction`): one for each of its claims
and each candidate, in order (`Fren.Core.inductionCandidates`). Each is an
item of the module that nothing reports, whose body is kept in
`State.inductionBodies` rather than checked as a function's. -/
partial def elabInductions (name : Ident) (header body : Array Member) (abstract : Bool) : M Unit := do
  let st ← get
  let shown := (declaredIdent name).1
  let some c := st.globals.back? | return
  unless c.path == st.module ++ Name.mkSimple shown.name do return
  let members := splitConjunctionMembers body
  let kinds := (blockMembers #[] members (members.map fun _ => default)).map (·.2.1)
  let params := header.filterMap fun
    | .var true _ _ x ty none => some (x, ty)
    | _ => none
  let vars := params.filterMap fun (x, _) => c.vars.find? (·.name == Name.mkSimple (declaredIdent x).1.name)
  unless vars.size == params.size do return
  let tys := vars.map (·.ty)
  let candidates := Fren.Core.inductionCandidates st.shapeOf kinds.toList abstract
    (vars.map fun v => (v.name, v.ptype)) st.inductionArgs
  if candidates.isEmpty then return
  let assumptions := members.filterMap fun
    | .prop .assume _ e => some e
    | _ => none
  let mut inductions := #[]
  for m in members do
    let .prop .expect claim e := m | continue
    let mut fns := #[]
    for i in candidates do
      if let some f ← elabInduction shown params tys claim e i assumptions then fns := fns.push f
    inductions := inductions.push (Name.mkSimple claim.name, fns)
  modify fun s => { s with globals := s.globals.modify (s.globals.size - 1) fun g => { g with inductions } }
where
  /-- The function generated for induction on the parameter at `i` of the
  claim `e`, named `claim`, under the assumptions `assumptions`, of the
  expectation named `shown`, whose parameters are `params`, of types `tys`,
  elaborated: its path, or none if it is not a structural recursion. -/
  elabInduction (shown : Ident) (params : Array (Ident × Option (Array Ident))) (tys : Array Ty) (claim : Ident)
      (e : Expr) (i : Nat) (assumptions : Array Expr) : M (Option Name) := do
    let st ← get
    let .enum ep _ := tys[i]! | return none
    let some d := st.dataOf? ep | return none
    let sp := e.span
    let ident (s : String) : Ident := { name := s, span := sp }
    let fname := Fren.Core.inductionFnName shown.name claim.name (declaredIdent params[i]!.1).1.name name.span.start
    let fn := ident fname
    let builder : Fren.Core.InductionSyntax Expr := {
      truth := .bool sp true
      app := fun f xs => .app sp #[ident f] (xs.toArray.map fun x => .path sp #[ident x])
      conjoin := .bin sp "and"
      guard := .when sp false
      matchOn := fun x arms =>
        let arms := arms.map fun arm =>
          let pattern := Pattern.variant sp (arm.variant.toArray.map ident)
            (if arm.binders.isEmpty then none
             else some (arm.binders.map fun x => Pattern.variant sp #[ident x] none))
          (pattern, none, arm.value)
        .match sp (.path sp #[ident x]) arms false }
    let (fnBody, post) := Fren.Core.buildInduction builder st.shapeOf st.module ep (d.ctors.map (·.1))
      (params.map fun p => (declaredIdent p.1).1.name) tys fname i assumptions e
    let item := Item.function true fn #[] (params.map fun (x, ty) => (#[x], ty)) (some #[ident "Bool"]) (some fnBody)
      #[(true, ident "claim", post)] sp {}
    let before ← get
    try withoutGhostLints (elabItem item)
    catch _ =>
      set before
      return none
    let after ← get
    let path := after.module ++ Name.mkSimple fname
    let some b := (after.bodies.extract before.bodies.size after.bodies.size).find? (·.fn? == some path)
      | set before; return none
    unless after.recursiveDefs.contains path do
      set before
      return none
    modify fun s => { s with bodies := s.bodies.extract 0 before.bodies.size, inductionBodies := s.inductionBodies.insert path b }
    return some path

/-- Elaborates a `set_option` (`Reqs/Lang/Items#lint-settings`), and the item
after its `in`, if any. -/
partial def elabLintSetting (stx : Span) (opt : Ident) (value : String) (valueSpan : Span) (removal : Span) (body? : Option Item) : M Unit := do
  if opt.name == "fren.enumeration.size" then
    -- Like `fren.evidence`: for the item after `in`, or the rest of the
    -- file (`Reqs/Check#checking-by-enumeration`).
    let prev := (← get).enumSize
    let n := value.toNat!
    if n > Fren.Core.Enumeration.maxSize then
      modify fun s => { s with diags := s.diags.push { file := s.file, span := valueSpan, msg := Fren.Core.Enumeration.sizeTooLargeMsg n } }
    else modify fun s => { s with enumSize := n }
    if let some body := body? then
      elabItem body
      modify fun s => { s with enumSize := prev }
    return
  if opt.name == "fren.evidence" then
    -- Like a lint setting: for the item after `in`, or the rest of the file.
    let prev := (← get).evidence?
    -- An invalid value is reported here, once, and does not stop the
    -- items it would set (`Reqs/Check#checking-by-testing`).
    if (Fren.Core.evidenceTested? value).isNone then
      modify fun s => { s with diags := s.diags.push { file := s.file, span := valueSpan, msg := Fren.Core.invalidEvidenceMsg value } }
    if let some body := body? then
      -- Before a function or a constant, whose checks are the solver's,
      -- only the solver can be set (`F0215`), and the item is elaborated
      -- as though it were (`Fren.Core.dispatchOf`).
      if let (some (what, item), some ev) := (evidenceTarget? body, Fren.Core.evidenceOf? value) then
        unless ev.settable item do
          modify fun s => { s with diags := s.diags.push { file := s.file, span := stx, msg := Fren.Core.itemEvidenceMsg what value } }
          elabItem body
          return
      modify fun s => { s with evidence? := some (value, valueSpan) }
      elabItem body
      modify fun s => { s with evidence? := prev }
    else modify fun s => { s with evidence? := some (value, valueSpan) }
    return
  let some rest := opt.name.dropPrefix? "fren.lint." | internal opt.span "not a lint option"
  let some target := Fren.Core.LintTarget.ofName? rest.toString | err opt.span (Fren.Core.unknownLintMsg rest.toString)
  let some requested := LintLevel.ofName? value | err valueSpan (Fren.Core.invalidLevelMsg value)
  -- What the body restores; not the whole state, which would make each
  -- change to it while the body is elaborated a copy.
  let levels := (← get).levels
  let settingStart? := (← get).settingStart?
  -- A forbidden lint's setting decides whether this one is accepted.
  noteSettingsSeen (Fren.Core.settingLints ++ target.members.filter fun l => (levels.get l).level == .forbid)
  if let some lint := target.rejectedBy? (levels.get · |>.level) requested then
    err stx (Fren.Core.forbiddenMsg target lint requested)
  -- `allow_attributes` (`lint::allow_attributes`), at the level before the setting.
  let (allows, fix) := Fren.Core.allowAttributes requested (target == .lint .unfulfilledExpectations)
  if allows then lintFix .allowAttributes valueSpan (Fren.Core.allowAttributesMsg target fix)
  let expectation? ← if requested == .expect then do
      let e : Fren.Core.ExpectationRecord := { target, level := levels.get .unfulfilledExpectations }
      let k := (← get).expectations.size
      modify fun s => { s with expectations := s.expectations.push (e, stx),
                               expectationRemovals := s.expectationRemovals.push removal }
      pure (some k)
    else pure none
  -- `unused_lint_setting` (`lint::unused_lint_setting`).
  let r : Fren.Core.SettingRecord := { target, requested, level := levels.get .unusedLintSetting }
  let setting := (← get).settings.size
  modify fun s => { s with settings := (Fren.Core.SettingRecord.replace s.settings s.levels.get target requested).push (r, stx)
                           settingRemovals := s.settingRemovals.push removal }
  let set : LevelInEffect := { level := requested, isSet := true, group? := target.group?, expectation?
                               setting? := some setting }
  for lint in target.members do
    modify fun s => { s with levels := s.levels.set lint set }
  if let some body := body? then
    modify fun s => { s with settingStart? := some (settingStart?.getD stx.start) }
    elabItem body
    modify fun s => { s with levels, settingStart? }

/-- Elaborates a trait (`Reqs/Lang/Traits`): its carrier `Self`, an
abstract type; its methods, uninterpreted functions, each seen by those
after it; its laws; and its expectations, global expectations whose checks
have the laws among their hypotheses (`Fren.Core.Comp.laws`). Each member
is in the trait's scope, whose names shadow its module's, and reports its
own first static error. -/
partial def elabTrait (isPub : Bool) (name : Ident) (members : Array Item) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "trait" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .trait n name.span
  let path := module ++ n
  let selfPath := path ++ Fren.Core.selfName
  -- What each member is, under its settings (`lang::trait_member`).
  let rec under : Item → Item
    | .lintSetting _ _ _ _ _ (some b) => under b
    | i => i
  let kindOf : Item → Fren.Core.TraitMember × Bool × Bool × Bool × Option Ident
    | .function isPub f tps _ _ body _ _ block =>
      (if body.isSome then .definedFunction else .method, isPub, !tps.isEmpty, !block.uses.isEmpty, some f)
    | .law f .. => (.law, false, false, false, some f)
    | .global f .. => (.expectation, false, false, false, some f)
    | .globalBlock f _ ms .. => (.expectation, false, false, ms.any (· matches .use .. | .useGroup ..), some f)
    | .comp isPub f .. => (.other "procedures", isPub, false, false, some f)
    | .enum .. | .record .. | .newtype .. => (.other "enums or structs", false, false, false, none)
    | .abstractType .. | .typeAlias .. | .subsetType .. => (.other "types", false, false, false, none)
    | .const .. => (.other "constants", false, false, false, none)
    | .mod .. => (.other "modules", false, false, false, none)
    | .use .. | .useGroup .. => (.other "`use`s", false, false, false, none)
    | .trait .. => (.other "traits", false, false, false, none)
    | .claim .. => (.other "claims", false, false, false, none)
    -- Never a member: a keyword error of a member breaks the trait.
    | .check .. | .lintSetting .. | .broken .. => (.other "commands", false, false, false, none)
  let spanOf : Item → Span
    | .function _ f .. | .law f .. | .global f .. | .globalBlock f .. | .comp _ f .. | .enum _ f .. | .record _ f ..
    | .newtype _ f .. | .abstractType _ f | .typeAlias _ f _ | .subsetType _ f .. | .const _ f .. | .trait _ f .. => f.span
    | .mod _ segs => segs[0]!.span
    | .use sp .. | .useGroup sp .. => sp
    | .claim _ segs _ => segs[0]!.span
    | _ => name.span
  for m in members do
    let (kind, isPubM, generic, uses, _) := kindOf (under m)
    if let some msg := Fren.Core.traitMemberMsg? path kind isPubM generic uses then err (spanOf (under m)) msg
  -- Distinct names, with the carrier's (`lang::distinct_names`).
  let named := members.filterMap fun m => (kindOf (under m)).2.2.2.2
  let declared := #[Fren.Core.selfName] ++ named.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err named[k - 1]!.span (Fren.Core.dupTraitMemberMsg declared[k]!)
  -- The trait, and its carrier, which its members see first.
  let traitItem : Fren.Core.Item := { kind := .traitItem, path, isPub, owner := module }
  let selfItem : Fren.Core.Item := { kind := .typeItem, path := selfPath, isPub := true, owner := path }
  let selfUse : Fren.Core.UseDef := { module, scope := path, target := selfPath, glob := false }
  modify fun s => { s with
    table := ((s.table.addItem traitItem).addItem selfItem).addUse selfUse
    sorts := s.sorts.push selfPath
    traitLaws := #[] }
  -- Each member, in the trait's scope, reporting its own first error, and
  -- without the item's trailing commas, which the trait reported.
  let commas := (← get).trailingCommas
  let member (m : Item) : M Unit := do
    -- Its own errors alone stop what follows them in it, as an item's do.
    let errors := (← get).itemErrors
    modify fun s => { s with module := path, scope := path, trailingCommas := #[], itemErrors := #[], inTrait := true }
    discard (attempt (elabItem m))
    modify fun s => { s with module, scope := module, trailingCommas := commas, itemErrors := errors ++ s.itemErrors
                             inTrait := false }
  -- The methods, each in scope after it, then the laws, then the
  -- expectations, each checked with the laws among its hypotheses
  -- (`Fren.Core.traitOrder`).
  for i in Fren.Core.traitOrder (members.map fun m => (kindOf (under m)).1) do
    let m := members[i]!
    let (kind, _, _, _, f?) := kindOf (under m)
    match kind with
    | .method =>
      let before := (← get).itemErrors.size
      member m
      if let some f := f? then
        if (← get).itemErrors.size == before then
          let u : Fren.Core.UseDef := { module, scope := path, target := path ++ Name.mkSimple (declaredIdent f).1.name, glob := false }
          modify fun s => { s with table := s.table.addUse u }
    | .law =>
      -- The settings before it, which a law takes only if every one is a
      -- lint's (`Fren.Core.lawSettingsMsg?`).
      let rec settings : Item → Array (String × String × Span)
        | .lintSetting stx opt value _ _ (some b) =>
          #[(opt.name, if opt.name == "fren.enumeration.size" then value else s!"\"{value}\"", stx)] ++ settings b
        | _ => #[]
      let ss := settings m
      match Fren.Core.lawSettingsMsg? (ss.toList.map fun (o, v, _) => (o, v)) with
      | some (k, msg) =>
        -- Its own error alone, as a member's.
        let errors := (← get).itemErrors
        modify fun s => { s with itemErrors := #[] }
        discard (attempt (α := Unit) (err ss[k]!.2.2 msg))
        modify fun s => { s with itemErrors := errors ++ s.itemErrors }
      | none => member m
    | _ =>
      let laws := (← get).traitLaws
      let before := (← get).globals.size
      let reportsBefore := (← get).lintReports.size
      member m
      let denied := undecidableDenied ((← get).lintReports.extract reportsBefore)
      let st ← get
      if st.globals.size > before then
        let c := st.globals.back!
        -- Its checks are the solver's (`F0215`).
        if let some msg := Fren.Core.traitEvidenceMsg? c.tested.any c.enumerated.any then
          discard (attempt (α := Unit) (err ((f?.map (·.span)).getD name.span) msg))
        let flags := Fren.Core.CheckFlags.withLaws { inCore := c.decidable, denied, fmfBound := c.guarded }
          (laws.map fun (_, _, inCore, _, fmfBound, denied) => { inCore, denied, fmfBound })
        let c := { c with laws := laws.map fun (l, f, _) => (l, f), lawsOf := path
                          decidable := flags.inCore, guarded := flags.fmfBound
                          natApps := c.natApps ++ laws.flatMap (·.2.2.2.1) }
        modify fun s => { s with globals := s.globals.pop.push c }
  modify fun s => { s with traitLaws := #[] }
end

/-- The text of the current file at `sp`. -/
def State.text (s : State) (sp : Span) : String := String.ofList (s.src.extract sp.start sp.stop).toList

/-- `use pre::a`, or `use pre::{a, b}` for several names. -/
def useText (pre : String) (names : Array String) : String :=
  match names with
  | #[n] => s!"use {pre}::{n}"
  | ns => s!"use {pre}::\{{", ".intercalate ns.toList}}"

/-- The edits of `fren fix` in the current file (`Reqs/Lint#fixing-lints`),
given the lints that fire in it, and the lints they fix, each with the
span of its message. -/
def State.fixes (s : State) (fired : Array (Lint × Span)) :
    Array (Fren.Core.Range × String) × Array (Lint × Span) := Id.run do
  let fixU := s.fixing.contains .unusedImports
  let fixG := s.fixing.contains .globImports
  let fires (l : Lint) (sp : Span) := fired.contains (l, sp)
  let delete (sp : Span) := (Fren.Core.deletionRange s.src (toRange sp), "")
  let mut edits := #[]
  let mut fixed := #[]
  let items := s.useLocs.foldl (init := #[]) fun acc l => if acc.contains l.item then acc else acc.push l.item
  for item in items do
    let members := (Array.range s.useLocs.size).filter (s.useLocs[·]!.item == item)
    let path (i : Nat) := s.useRecords[i]!.2
    match s.useLocs[members[0]!]!.pre? with
    | none =>
      let i := members[0]!
      let u := s.useRecords[i]!.1
      let names := u.globNames s.used
      match Fren.Core.importFix (fires .unusedImports (path i)) (fires .globImports (path i)) fixU fixG names.size with
      | .remove =>
        edits := edits.push (delete s.useLocs[i]!.removal)
        fixed := fixed ++ #[(.unusedImports, path i), (.globImports, path i)]
      | .byName =>
        edits := edits.push (toRange item, useText (s.text s.useLocs[i]!.path) (names.map toString))
        fixed := fixed.push (.globImports, path i)
      | .keep => pure ()
    | some pre =>
      let removed := members.filter fun i => fixU && fires .unusedImports (path i)
      if removed.isEmpty then continue
      fixed := fixed ++ removed.map (.unusedImports, path ·)
      let kept := members.filter (!removed.contains ·)
      edits := edits.push <| if kept.isEmpty then delete s.useLocs[members[0]!]!.removal
        else (toRange item, useText (s.text pre) (kept.map (s.text s.useLocs[·]!.path)))
  let fixes (l : Lint) (sp : Span) := s.fixing.contains l && fires l sp
  for f in s.lintFixes do
    if fixes f.lint f.span && !(f.unless?.any fun (l, sp) => fixes l sp) then
      edits := edits ++ f.edits
      fixed := fixed.push (f.lint, f.span)
  if s.fixing.contains .unfulfilledExpectations then
    for (_, sp) in s.expectations, removal in s.expectationRemovals do
      if fires .unfulfilledExpectations sp then
        edits := edits.push (if removal == sp then delete sp else (toRange removal, ""))
        fixed := fixed.push (.unfulfilledExpectations, sp)
  if s.fixing.contains .unusedLintSetting then
    for (_, sp) in s.settings, removal in s.settingRemovals do
      if fires .unusedLintSetting sp then
        edits := edits.push (if removal == sp then delete sp else (toRange removal, ""))
        fixed := fixed.push (.unusedLintSetting, sp)
  return (edits, fixed)

/-- Records the reports of `manual_nat` in the file that no call or
refinement in it keeps an `Int` (`lint::manual_nat`). Their fix is a
suggestion, which `fren fix` does not make. -/
def finishNat : StateM State Unit := do
  let s ← get
  let rs := s.natReports.filter fun r => !s.natKept.contains (r.comp, r.var)
  set { s with lintReports := s.lintReports ++ rs.map NatReport.report }

/-- The lints of the file just elaborated, at its end, and the edits that
fix them, if `fren fix` fixes any. -/
def finishLints : StateM State Unit := do
  finishNat
  let s ← get
  let atEnd := Lint.all.filterMap (s.levels.get · |>.setting?)
  let (reports, fulfilled) := Fren.Core.finishReports
    (s.lintReports ++ Fren.Core.importReports s.useRecords s.used true ++ Fren.Core.deadCodeReports s.items s.usedItems
      ++ Fren.Core.unusedAssumptionReports s.assumptions s.globalReads
      ++ Fren.Core.unusedSettingReports s.settings s.seenSettings atEnd true
      ++ Fren.Core.singleCallReports s.items s.usedItems
      ++ Fren.Core.procWithoutOutputsReports s.procs s.usedItems
      ++ Fren.Core.needlessHigherOrderReports s.hofParams (s.fnArgs.map (·.1)))
  let (unfulfilled, _) := Fren.Core.finishReports (Fren.Core.expectationReports s.expectations fulfilled true)
  let all := reports ++ unfulfilled
  let (edits, fixed) := s.fixes (all.map fun (r, _) => (r.lint, r.ref))
  let diags := all.map fun (r, severity) =>
    { file := s.file, span := r.ref, severity, msg := r.msg, lint? := some r.lint
      fixed := fixed.contains (r.lint, r.ref) : Diag }
  set { s with diags := s.diags ++ diags, edits := s.edits ++ edits.map (s.file, ·) }

/-- The trailing commas among `toks` that `unnecessary_trailing_comma`
reports, each with the `}` or `]` after it
(`lint::unnecessary_trailing_comma`). -/
def trailingCommas (toks : Array Token) : Array (Span × String) :=
  let texts := toks.map fun t => ((match t.tok with | .kw k => k | _ => ""), t.nlBefore)
  (Fren.Core.trailingCommas texts).map fun i => (toks[i]!.span, texts[i + 1]!.1)

/-- The index of the first of `found`, which is in order of where each
starts, that starts at `pos` or after, or its size if none does. -/
def firstFrom (found : Array (Lint × Span × Msg)) (pos : Nat) : Nat :=
  go 0 found.size
where
  go (lo hi : Nat) : Nat :=
    if h : lo < hi then
      let mid := (lo + hi) / 2
      if found[mid]!.2.1.start < pos then go (mid + 1) hi else go lo mid
    else lo
  termination_by hi - lo

/-- Elaborates the items of one file, whose text is `src`, and which start
at `starts`, collecting an error per failed item, where `trailingCommas`
are the commas that `unnecessary_trailing_comma` reports, and `found` the
file's `literalLints`, in order of where each starts. `fren fix` fixes the lints `fixing` in it. -/
def elabFile (file : Nat) (src : Array Char) (items : Array Item) (starts : Array Nat)
    (trailingCommas : Array (Span × String)) (found : Array (Lint × Span × Msg)) (fixing : Array Lint := #[])
    (module : Name := .anonymous) :
    StateM State Unit := do
  modify fun s => { s with file, src, fixing, module, scope := module, levels := s.cliLevels, useRecords := #[], evidence? := none,
                           enumSize := Fren.Core.Enumeration.defaultSize,
                           used := #[], expectations := #[], lintReports := #[], useLocs := #[],
                           expectationRemovals := #[], items := #[], usedItems := #[], procs := #[], lintFixes := #[],
                           hofParams := #[], fnArgs := #[],
                           globalTexts := #[], natReports := #[], natKept := #[], settings := #[], settingRemovals := #[], seenSettings := #[],
                           assumptions := #[], globalReads := #[], trailingCommas }
  for item in items, k in [0:items.size] do
    -- An item has the literals and comments up to the next item, and the
    -- first, those before it too, and those that a `set_option` before it
    -- left.
    let start := starts[k]?.getD 0
    let stop := starts[k + 1]?.getD src.size
    let left ← if k > 0 && items[k - 1]! matches .lintSetting .. then pure (← get).literals else pure #[]
    -- `found` is in order of where each starts, so those that start in
    -- `[start, stop)` are a slice of it.
    let lo := if k == 0 then 0 else firstFrom found start
    let literals := left ++ found.extract lo (firstFrom found stop)
    modify fun s => { s with itemStart := start, literals, itemSpan := { start, stop } }
    let s ← get
    match (elabItem item).run s with
    | .ok ((), s') =>
      if s'.itemErrors.isEmpty then set s'
      else set { s.keepLints s' with diags := s.diags ++ s'.itemErrors }
    | .error f => set { s.keepLints f.state with diags := s.diags ++ f.diags }
  finishLints

/-- The file id of the prelude's items: no file that the `fren` command is
given has it, so that nothing of the prelude's is taken for a spec's. -/
def preludeFile : Nat := 1000000

/-- `st` with the prelude elaborated into it, before every spec
(`Reqs/Lang/Prelude`): its items, in the prelude's module, and none of its
messages. It has none: an error in it, as one that it does not parse, is
an internal error of every spec. -/
def State.withPrelude (st : State) : State :=
  let chars := Fren.Core.preludeSource.toList.toArray
  let broken (what : String) : State :=
    { st with diags := st.diags.push { file := 0, span := default, msg := Msg.internal s!"the prelude {what}" } }
  match lexWithComments chars with
  | .error e => broken s!"does not lex: {e.msg.headline}"
  | .ok (toks, _) => match parseItems toks chars with
    | .error e => broken s!"does not parse: {e.msg.headline}"
    | .ok (items, starts) =>
      let st' := (elabFile preludeFile chars items starts #[] #[] (module := Fren.Core.preludeModule) |>.run st).2
      match (st'.diags.extract st.diags.size st'.diags.size).find? (·.severity == .error) with
      | some d => broken s!"has an error: {d.msg.headline}"
      | none => { st' with diags := st.diags, file := 0, module := .anonymous, scope := .anonymous }

/-- Whether the queries of `c` may quantify over a collection's elements,
as the constraints of its variables' types, the facts of the applications
it makes, and the obligations it asks may: they then set `fmf-bound`
(`Fren.Core.boundedOptions`). It is read from the types, not the formulas,
as the Lean front end's `bounded` is. -/
def State.bounded (s : State) (c : CComp) : Bool :=
  c.guarded || c.vars.any (fun v => v.fact?.isSome && (v.ptype.cons s.shapeOf).any (·.quantifies))
    || c.indexes.any (fun (_, _, _, _, t) => t.any (·.2))
    || c.insts.any (·.bounded)
    || c.natApps.any fun app => ((quotedSymbols (peelLets app))[0]?).any fun h => s.quantifiedFns.contains (quote h)

/-- A declaration of the prelude: its SMT-LIB text, and the names of the
quoted symbols that it declares. -/
structure PreludeDecl where
  text : String
  syms : Array String
  recursion? : Option (Array String × String) := none
  domain : Array String := #[]
  deriving Inhabited, BEq

/-- `(declare-sort ...)` for every abstract type, `(declare-datatype ...)`
for every enum and record, in order, since each may contain those before
it, `(declare-fun ...)` for every uninterpreted function, and
`(define-fun ...)` for every defined function, in order, since each may
apply those before it, and then for every clause of a contract. -/
def State.prelude (s : State) : Array PreludeDecl :=
  let unquote (sym : String) : String := if sym.startsWith "|" then ((sym.drop 1).dropEnd 1).toString else sym
  let sorts := s.sorts.map fun p => { text := s!"(declare-sort {itemSym p} 0)\n", syms := #[unquote (itemSym p)] }
  -- A datatype declares its constructors and selectors too.
  let enums := s.datatypes.map fun d => { text := d.text, syms := d.syms }
  let funs := s.funs.map fun (p, ps, r) =>
    -- An instance of a generic function has a symbol of its own.
    let sym := (s.instSyms.find? p).getD (itemSym p)
    { text := s!"(declare-fun {sym} ({" ".intercalate (ps.toList.map (·.sort))}) {r.sort})\n", syms := #[unquote sym] }
  let defs := s.defs.map fun (p, ps, r, body) =>
    let binders := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    -- An instance of a generic function has a symbol of its own.
    let sym := (s.instSyms.find? p).getD (itemSym p)
    if s.recursiveDefs.contains p then
      ({ text := s!"(declare-fun {sym} ({" ".intercalate (ps.toList.map (·.2.sort))}) {r.sort})\n"
         syms := #[unquote sym], recursion? := some (ps.map (quote ∘ toString ∘ Prod.fst), body)
         domain := ((s.recInstances.find? p).map (·.2)).getD
           (((s.bodies.find? (·.fn? == some p)).map fun b => b.vars.filterMap (·.fact?)).getD #[]) } : PreludeDecl)
    else
      { text := s!"(define-fun {sym} ({binders}) {r.sort} {body})\n", syms := #[unquote sym] }
  -- After every function, since a clause may apply its own and those
  -- declared before it.
  let clauses := s.clauseDefs.map fun (sym, ps, body) =>
    let ps := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    { text := s!"(define-fun {sym} ({ps}) Bool {body})\n", syms := #[unquote sym] }
  sorts ++ enums ++ funs ++ defs ++ clauses

/-- Of each uninterpreted function, by its SMT-LIB symbol: whether its
result is a `Nat`, and its contract, for the facts that its applications
bring (`appFactsOf`). -/
def State.appFuns (s : State) : Std.HashMap String (Bool × Contract) :=
  (s.funs ++ s.defs.filterMap (fun (p, ps, r, _) => if s.recursiveDefs.contains p then some (p, ps.map (·.2), r) else none)).foldl (init := {}) fun m (p, _, r) =>
    m.insert ((s.instSyms.find? p).getD (itemSym p)) (r == .nat, (s.contracts.find? p).getD {})

/-- Of each recursive function, by its SMT-LIB symbol, its path: those that
a fact may apply, which evaluation cannot confirm a model of
(`Fren.Core.recursiveCounterexample`). -/
def State.recursiveSyms (s : State) : Std.HashMap String Name :=
  -- An instance's, its function's (`Reqs/Lang/Recursion#generic-recursion`).
  s.recursiveDefs.fold (init := {}) fun m p => m.insert ((s.instSyms.find? p).getD (itemSym p)) (((s.recInstances.find? p).map (·.1)).getD p)

/-- Of each uninterpreted function with postconditions, by its SMT-LIB
symbol, its path: the function whose contract's realizability the checks
whose queries apply it rest on (`Fren.Core.appFactsWith`). Not instances
of generic functions, whose premise is not applied yet (#522), nor
recursive functions, which are defined. -/
def State.contractFns (s : State) : Std.HashMap String Name :=
  s.funs.foldl (init := {}) fun m (p, _, _) =>
    if s.instSyms.contains p || s.genericFns.contains p then m
    else match s.contracts.find? p with
      | some k => if k.posts.isEmpty then m else m.insert (itemSym p) p
      | none => m

/-- Each instance that the spec's items use of a generic function without a
body, with where its contract is checked (`Fren.Core.instanceSites`). -/
def State.instanceSites (s : State) : Array (Fren.Core.InstanceSite × Name × Array Ty) :=
  Fren.Core.instanceSites s.genericUses (fun g => ((s.genericFns.find? g).map (·.params)).getD #[])
    fun g => (s.genericFns.find? g).bind fun gf => if gf.defined then none else some gf.file

/-- The whole prelude, as one script. -/
def State.preludeText (s : State) : String := String.join (s.prelude.toList.map (·.text))

end FrenCli
