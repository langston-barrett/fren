-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: data types -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

@[command_elab Lang.enumCmd] def elabEnum : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "enum" nameStx
  checkFresh modName n nameStx
  lintName .enumeration n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  let params ← elabTypeParams modName (if stx[4].isNone then #[] else stx[4][0][1].getSepArgs)
  let variantStxs := stx[6].getSepArgs
  -- Distinct names (`lang::distinct_names`), of names that are single
  -- segments, as the `fren` command parses them.
  for v in variantStxs do discard (segName v[0])
  if let some k := (Core.repeatsAt (variantStxs.map (·[0].getId)))[0]? then
    throwErrorAt variantStxs[k]![0] (Core.dupVariantMsg variantStxs[k]![0].getId).text
  let mut variants := #[]
  let mut payloads : Array (Array Expr) := #[]
  let mut ptys : Array (Array (Core.PTy × Syntax)) := #[]
  let mut nRecursive := 0
  let mut unbounded := false
  for v in variantStxs do
    let vn ← checkItemName "variant" v[0]
    lintName .variant vn v[0]
    variants := variants.push vn
    let tys := if v[1].isNone then #[] else v[1][1].getSepArgs
    let tps ← tys.mapM fun t => fieldType modName t decl .payload n params
    let ts := tps.map (·.1)
    let st ← getState
    -- Recursive if a payload's type is the enumeration or built from it
    -- (`lang::well_founded`).
    let own := (Core.PTy.plain (.enum path (params.toList.zipIdx.map fun (p, k) => .param k p))).node
    let nodes := tps.toList.map fun (t, pt) => if t.getAppFn.isConstOf decl then own else pt.node
    if Core.recursiveVariant st.shapeOf own nodes then nRecursive := nRecursive + 1
    unbounded := unbounded || tps.any fun (t, pt) => t.getAppFn.isConstOf decl || (factsOf st pt).unbounded
    payloads := payloads.push ts
    ptys := ptys.push (tps.zip tys |>.map fun ((_, pt), t) => (pt, t))
  unless Core.wellFounded variants.size nRecursive do throwErrorAt nameStx (Core.illFoundedMsg n).text
  -- A recursive enumeration's payloads are never `Nat`s (`lang::nat_place`),
  -- and a constraint of one is outside the decidable core
  -- (`lang::subset_place`).
  let isRecursive := nRecursive > 0
  let shape : Core.DataShape := { recursive := isRecursive, parts := ptys.map (·.map (·.1)) }
  if isRecursive then
    let st ← getState
    for pts in ptys do
      for (pt, t) in pts do
        if pt.ty == .nat then throwErrorAt t (Core.natPlaceMsg .recursivePayload).text
        if (pt.cons (fun q => if q == path then some shape else st.shapeOf q) true).isSome then
          liftTermElabM (recordOutsideCore t Core.undecidableRecursivePayloadMsg)
  -- `enum_variant_names` (`lint::enum_variant_names`, `lint::variant_has_enum_name`).
  if let some msg := Core.enumVariantNamesMsg? n variants then recordLint .enumVariantNames nameStx msg
  for v in variantStxs, vn in variants do
    if let some msg := Core.variantNameMsg? n vn then recordLint .enumVariantNames v[0] msg
  -- Only an enumeration without payloads may be ordered
  -- (`lang::ordered_declaration`); the first payload is reported.
  let withPayload := variantStxs.filter (!·[1].isNone)
  unless Core.orderedDeclAccepted isOrdered withPayload.size none do
    throwErrorAt withPayload[0]![0] (Core.orderedPayloadMsg n withPayload[0]![0].getId).text
  -- One of the prelude's types is the Lean type that it is, for which
  -- nothing is generated (`Reqs/Lang/Prelude#lean`).
  if let some l := Core.leanTypeOf? path then
    record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
    record (.enumInfo { path, decl := l.lean, variants, payloads, unbounded, ordered := isOrdered, shape, params, lean? := some l })
    return
  let own : Term ← if params.isEmpty then pure (mkIdent decl) else `(($(mkIdent decl) $(params.map fun p => (mkIdent p : Term))*))
  let ctors ← (variants.zip payloads).mapM fun (v, ts) => do
    let bs ← ts.mapIdxM fun k t => do
      let ty := if t.getAppFn.isConstOf decl then own else typeSyntax t params
      `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent (Name.mkSimple s!"x{k}")) : $ty))
    `(Lean.Parser.Command.ctor| | $(mkIdent v):ident $bs:bracketedBinder*)
  -- A generic type has a parameter of type `Type` for each of its type
  -- parameters (`Reqs/Generated#generic-types`). Declared by its name
  -- relative to the current namespace, `decl`, so that Lean names the
  -- instances it derives in `decl`'s namespace, apart from other items' and
  -- Lean's own.
  let binders ← paramBinders params false
  elabCommand (← `(inductive $(mkIdentFrom nameStx (leanName .anonymous path)):ident $binders:bracketedBinder* where $ctors:ctor*
    deriving DecidableEq, Repr, Inhabited))
  if payloads.all (·.isEmpty) && params.isEmpty then
    let vals := variants.map fun v => mkCIdent (decl ++ v)
    -- Named after the full path: an anonymous instance is named after `n`
    -- alone, which enumerations in different modules can share.
    elabCommand (← `(instance $(mkIdent (`_root_ ++ decl ++ `instFinite)):ident : Fren.Finite $(mkCIdent decl) :=
      ⟨[$vals,*], by intro x; cases x <;> decide⟩))
  -- A selector for each value of each payload, which a `match` reads; of a
  -- generic type, with its parameters implicit, and an `Inhabited` instance
  -- of each, for `default`.
  let self ← selfType decl params
  let implicits ← paramBinders params true
  for v in variants, ts in payloads do
    let ctor := decl ++ v
    let xs := (Array.range ts.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
    for t in ts, k in [0:ts.size] do
      let sel := mkIdent (`_root_ ++ selectorName ctor k)
      let x := xs[k]!
      let ty := if t.getAppFn.isConstOf decl then self else typeSyntax t params
      let cmd ← if variants.size == 1 then
          `(def $sel:ident $implicits:bracketedBinder* (v : $self) : $ty := match v with | $(mkCIdent ctor) $xs* => $x)
        else
          `(def $sel:ident $implicits:bracketedBinder* (v : $self) : $ty := match v with | $(mkCIdent ctor) $xs* => $x | _ => default)
      elabCommand cmd
      -- So that `simp [fren_spec]` reads a payload of a variant that is
      -- built (`Reqs/Generated#proofs`).
      let names ← get
      elabCommand (← `(attribute [fren_spec] $sel:ident))
      modify fun t => { t with nextMacroScope := names.nextMacroScope, ngen := names.ngen }
  -- Each read of a recursive enumeration's payload brings the payload's
  -- constraint (`Core.readCons`), as an application does.
  let readFacts ← if !isRecursive then pure #[] else liftTermElabM do
    let st ← getState
    let shapes (q : Name) := if q == path then some shape else st.shapeOf q
    let mut out := #[]
    for v in variants, ts in payloads, vi in [0:variants.size] do
      for t in ts, k in [0:ts.size] do
        if let some c := Core.readCons shapes path vi k then
          out := out.push (selectorName (decl ++ v) k, ← genericPredOf params t c)
    return out
  record (.item { item := { kind := .enumItem, path, isPub, owner := modName }, ref := nameStx })
  record (.enumInfo { path, decl, variants, payloads, unbounded, ordered := isOrdered, shape, readFacts, params })
  unless isPub do recordItem .enumeration path nameStx

@[command_elab Lang.structCmd] def elabStruct : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  lintItem stx
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  let params ← elabTypeParams modName (if stx[4].isNone then #[] else stx[4][0][1].getSepArgs)
  -- A generic record is not ordered, for now (`Core.orderedGenericAccepted`).
  unless Core.orderedGenericAccepted isOrdered params.size do throwErrorAt nameStx (Core.orderedGenericMsg n).text
  let mut fields : Array (Name × Expr) := #[]
  let mut ptys : Array Core.PTy := #[]
  let fieldStxs := stx[6].getSepArgs
  for f in fieldStxs do discard (segName f[0])
  if let some k := (Core.repeatsAt (fieldStxs.map (·[0].getId)))[0]? then
    throwErrorAt fieldStxs[k]![0] (Core.dupFieldMsg fieldStxs[k]![0].getId).text
  for f in fieldStxs do
    let fn := f[0].getId
    liftMsg f[0] (Core.checkNoBang fn)
    lintName .field fn f[0]
    let (t, pt) ← if f[1].isNone then pure (Lean.mkConst ``Bool, .plain .bool) else fieldType modName f[1][1] decl .field n params
    ptys := ptys.push pt
    -- As for a variable (`lang::bool_naming`).
    liftMsg f[0] (Core.checkVarName fn (if f[1].isNone then none else some (t.isConstOf ``Bool)))
    unless f[1].isNone || !pt.invariants.isEmpty do liftTermElabM (lintBoolType fn f[1][1] t)
    fields := fields.push (fn, t)
  -- `struct_field_names` (`lint::struct_field_names`, `lint::field_has_record_name`).
  if let some msg := Core.structFieldNamesMsg? n (fields.map (·.1)) then recordLint .structFieldNames nameStx msg
  for f in fieldStxs, (fn, _) in fields do
    if let some msg := Core.fieldNameMsg? n fn then recordLint .structFieldNames f[0] msg
  -- `struct_excessive_bools` (`lint::struct_excessive_bools`).
  let nBools := (fields.filter (·.2.isConstOf ``Bool)).size
  if Core.structExcessiveBools nBools then recordLint .structExcessiveBools nameStx (Core.structExcessiveBoolsMsg n nBools)
  let st ← getState
  -- An ordered record's fields are ordered (`lang::ordered_declaration`);
  -- the first that is not is reported.
  let first? := Core.PTy.firstUnordered? st.orderedDecl ptys.toList
  unless Core.orderedDeclAccepted isOrdered 0 first? do
    if let some k := first? then
      let f := fieldStxs[k]!
      throwErrorAt (if f[1].isNone then f[0] else f[1][1]) (Core.unorderedFieldMsg .record n fields[k]!.1 ptys[k]!.ty).text
  let unbounded := ptys.any fun pt => (factsOf st pt).unbounded
  let bs ← fields.mapM fun (f, t) => `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent f):ident : $(typeSyntax t params)))
  let binders ← paramBinders params false
  elabCommand (← `(structure $(mkIdentFrom nameStx (leanName .anonymous path)):ident $binders:bracketedBinder* where
    $(mkIdent (if params.isEmpty then `«{}» else Name.mkSimple "mk!")):ident :: $bs:structExplicitBinder*
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.recordInfo { path, decl, fields, unbounded, shape := { isRecord := true, parts := #[ptys] }, params, ordered := isOrdered })
  unless isPub do recordItem .record path nameStx

@[command_elab Lang.newtypeCmd] def elabNewtype : CommandElab := fun stx => do
  -- What Lean recovered from a parse error that it has reported.
  if stx.hasMissing then return
  openGenerated
  checkLexemes stx
  checkParsed stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let isOrdered := !stx[1].isNone
  let nameStx := stx[3]
  let n ← checkItemName "record" nameStx
  checkFresh modName n nameStx
  lintName .record n nameStx
  let path := modName ++ n
  let decl ← generatedName path
  -- Exactly one field, whose type is accepted as a record's field's
  -- (`lang::newtype`).
  let tys := stx[5].getSepArgs
  let some ty := tys[0]? | throwErrorAt nameStx (Core.newtypeFieldsMsg path 0).text
  unless Core.newtypeAccepted tys.size true do throwErrorAt nameStx (Core.newtypeFieldsMsg path tys.size).text
  let (under, pt) ← fieldType modName ty decl .newtype n
  -- An ordered newtype's underlying type is ordered
  -- (`lang::ordered_declaration`).
  unless Core.orderedDeclAccepted isOrdered 0 (Core.PTy.firstUnordered? (← getState).orderedDecl [pt]) do
    throwErrorAt ty (Core.unorderedFieldMsg .newtype n (Name.mkSimple "0") pt.ty).text
  let unbounded := Core.newtypeUnbounded (factsOf (← getState) pt).unbounded
  -- One field, `«0»`, so that `x.0` in Fren is `x.«0»` in Lean.
  elabCommand (← `(structure $(mkIdentFrom nameStx (leanName .anonymous path)):ident where
    $(mkIdent `mk):ident :: $(mkIdent (Name.mkSimple "0")):ident : $(typeSyntax under)
    deriving DecidableEq, Repr, Inhabited))
  record (.item { item := { kind := .recordItem, path, isPub, owner := modName }, ref := nameStx })
  record (.newtypeInfo { path, decl, under, unbounded, shape := { isRecord := true, isNewtype := true, parts := #[#[pt]] }, ordered := isOrdered })
  unless isPub do recordItem .record path nameStx



end Fren
