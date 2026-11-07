-- keep-sorted start
import Fren.Elab.Syntax
-- keep-sorted end

/-! # Hosted elaboration: types -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The path of a type written as one, or `none` for `Set<T>`, `Rel<A, B>`
and an instance of a generic type. -/
def typePath? (ty : Syntax) : Option Syntax :=
  if ty.isOfKind ``Lang.fren_path then some ty
  else if ty.isOfKind ``Lang.setType || ty.isOfKind ``Lang.relType || ty.isOfKind ``Lang.seqType
    || ty.isOfKind ``Lang.instanceType then none
  else some ty[0]

/-- The type `ty` as its segments, as the `fren` command's parser has it
(`Core.ownIn`). -/
partial def typeSegs (ty : Syntax) : Array String :=
  if ty.isOfKind ``Lang.setType then #[Core.setSeg] ++ typeSegs ty[2]
  else if ty.isOfKind ``Lang.seqType then #[Core.seqSeg] ++ typeSegs ty[2]
  else if ty.isOfKind ``Lang.relType then #[Core.relSeg] ++ typeSegs ty[2] ++ #[Core.relSep] ++ typeSegs ty[4]
  -- A function type (`Reqs/Lang/HigherOrder#function-types`).
  else if ty.isOfKind ``Lang.fnType then
    let ps := (ty[2].getSepArgs.map typeSegs).toList.intersperse #[Core.fnSep]
    #[Core.fnSeg] ++ ps.foldl (· ++ ·) #[] ++ #[Core.fnArrow] ++ typeSegs ty[5]
  else if ty.isOfKind ``Lang.instanceType then
    let args := (ty[2].getSepArgs.map typeSegs).toList.intersperse #[Core.argsSep]
    (pathSegs ty[0]).map (·.getId.toString) ++ #[Core.argsOpen] ++ args.foldl (· ++ ·) #[] ++ #[Core.argsClose]
  else match typePath? ty with
    | some p => (pathSegs p).map (·.getId.toString)
    | none => #[]

/-- The Lean types within the `Fren.FinSet`s and pairs of `t`. -/
partial def elemTypes (t : Expr) : Array Expr :=
  if t.isAppOfArity ``Fren.FinSet 1 || t.isAppOfArity ``Fren.Seq 1 then elemTypes t.appArg!
  else if t.isAppOfArity ``Prod 2 then elemTypes t.appFn!.appArg! ++ elemTypes t.appArg!
  else #[t]

/-- The abstract type that the Lean type `t` is, or that is an element type
within it (`Core.Ty.abstractWithin?`), and whether it is `t` itself. -/
def abstractWithin? [Monad m] [MonadEnv m] (t : Expr) : m (Option (Name × Bool)) := do
  let st ← getState
  -- A generic function's type parameter may be anywhere a type is
  -- (`Core.Ty.abstractWithin?`).
  let some e := (elemTypes t).find? fun e => e.isConst && st.placeholders.contains e.constName
    && (Core.typeParamName? e.constName).isNone | return none
  let p := st.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == e.constName then some a.path else none
  return some (p.getD .anonymous, e == t)

/-- The Lean type of the type named by the path `segs`, with the type
arguments `args`, as many as its type parameters (`lang::type_arguments`),
written at `ref`; `params` are the type parameters in scope. -/
def instanceType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name)
    (segs : Array Syntax) (args : Array Expr) (params : Array Name) (ref : Syntax) : m Expr := do
  let one := segs.size == 1
  let builtin := one && [`Bool, `Int, `Nat, `String, `Set, `Seq, `Rel].contains segs[0]!.getId
  let fnParam := one && ((← getLocal).fnTypeParams.any (·.2.contains segs[0]!.getId))
  if builtin || fnParam || (one && params.contains segs[0]!.getId) then
    unless Core.writtenArgumentsAccepted (if builtin then .builtin else .parameter) 0 args.size do
      throwErrorAt ref (Core.typeArgsMsg segs[0]!.getId.toString #[] args.size).text
  let arity (named : Core.TypeNamed) (path : Name) (ps : Array Name) : m Unit := do
    unless Core.writtenArgumentsAccepted named ps.size args.size do
      throwErrorAt ref (Core.typeArgsMsg (Core.showPath path) ps args.size).text
  match ← resolveWritten modName segs with
  | .item { kind := .enumItem, path, .. } =>
    let some e := (← getState).enums.get? path | throwError "internal error: unknown enum `{path}`"
    arity .data path e.params
    return mkAppN e.const (e.leanArgs args)
  | .item { kind := .recordItem, path, .. } =>
    if let some n := (← getState).newtypes.get? path then
      arity .other path #[]
      return Lean.mkConst n.decl
    let some r := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
    arity .data path r.params
    return mkAppN (Lean.mkConst r.decl) args
  | .item { kind := .typeItem, path, .. } =>
    arity .other path #[]
    if let some (t, _) := (← getState).aliases.get? path then return t
    return Lean.mkConst (placeholderName path)
  | r => throwErrorAt ref (Core.notATypeMsg r).text

/-- Whether a function type is written within the type `ty`, or is `ty`. -/
partial def hasFnType (ty : Syntax) : Bool := ty.isOfKind ``Lang.fnType || ty.getArgs.any hasFnType

/-- A function type written `ty` at `site`, where it may not be
(`lang::function_type_place`); a function type within another is reported
where that one is elaborated. -/
def checkFnTypeSite [Monad m] [MonadError m] (site : Core.TypeSite) (ty : Syntax) : m Unit := do
  if ty.isOfKind ``Lang.fnType then throwErrorAt ty (Core.fnTypePlaceMsg site []).text

/-- The Lean type of the Fren type `ty`. Within the declaration of a generic
type, its type parameters `params` are types, the `k`th the loose bound
variable `.bvar k` (`Reqs/Lang/Generics`). -/
partial def elabType [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name) (ty : Syntax)
    (params : Array Name := #[]) : m Expr := do
  -- A function type is only a defined function's parameter's, which
  -- `fnParamType` elaborates (`lang::function_type_place`).
  if let some w := Core.fnTypeWithin (typeSegs ty).toList then throwErrorAt ty (Core.fnTypePlaceMsg .constant w).text
  -- `Set<T>`: `"Set" "<" T ">"`; `Rel<A, B>`: `"Rel" "<" A "," B ">"`.
  -- An element type, which is never a `Nat` (`lang::nat_place`), and
  -- may be a type parameter (`lang::element_parameter`).
  let elem (e : Syntax) : m Expr := do
    let t ← elabType modName e params
    if t.isConstOf ``Nat then throwErrorAt e (Core.natPlaceMsg .element).text
    if let .bvar k := t then
      unless Core.elementParamAccepted .datatype do throwErrorAt e (Core.typeParamPlaceMsg params[k]! .element "").text
    if let some n := t.constName?.bind (Core.typeParamName? ·) then
      unless Core.elementParamAccepted .function do
        throwErrorAt e (Core.typeParamPlaceMsg (Name.mkSimple n) .element "").text
    return t
  -- An instance of a generic type, `G<A, B>`, whose arguments are payloads'
  -- types (`Reqs/Lang/Generics#type-parameters`).
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
    for a in given do
      let t ← elabType modName a params
      unless !t.isConstOf ``Nat || Core.natPlaceAccepted .argument do throwErrorAt a (Core.natPlaceMsg .argument).text
      if let some (p, whole) ← abstractWithin? t then throwErrorAt a (Core.abstractFieldMsg p true !whole).text
      args := args.push t
    return ← instanceType modName segs args params ty
  let some p := typePath? ty |
    if ty.isOfKind ``Lang.relType then
      return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero])
        (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (← elem ty[2]) (← elem ty[4]))
    else if ty.isOfKind ``Lang.seqType then return mkApp (Lean.mkConst ``Fren.Seq [Level.zero]) (← elem ty[2])
    else return mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) (← elem ty[2])
  let segs := pathSegs p
  if segs.size == 1 then
    if let some k := params.idxOf? segs[0]!.getId then return .bvar k
    -- A generic function's type parameter, an abstract type within it
    -- (`Reqs/Lang/GenericFunctions#type-parameters`).
    if let some (fn, ps) := (← getLocal).fnTypeParams then
      if let some k := ps.idxOf? segs[0]!.getId then
        return Lean.mkConst (placeholderName (Core.typeParamPath fn k ps[k]!))
  if segs.size == 1 && segs[0]!.getId == `Bool then return Lean.mkConst ``Bool
  if segs.size == 1 && segs[0]!.getId == `Int then return Lean.mkConst ``Int
  if segs.size == 1 && segs[0]!.getId == `Nat then return Lean.mkConst ``Nat
  if segs.size == 1 && segs[0]!.getId == `String then return Lean.mkConst ``String
  instanceType modName segs #[] params p

/-- The `Rel<A, B>`s within the type `ty`. -/
partial def relTypes (ty : Syntax) : Array Syntax :=
  (if ty.isOfKind ``Lang.relType then #[ty] else #[]) ++ ty.getArgs.flatMap relTypes

/-- Records `zero_sized_map_values` on each `Rel<A, B>` within the type
`ty` whose `B` is an enumeration of one variant without a payload
(`lint::zero_sized_map_values`). -/
def lintRelTypes [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadFileMap m] (modName : Name)
    (ty : Syntax) (params : Array Name := #[]) : m Unit := do
  for r in relTypes ty do
    let b ← elabType modName r[4] params
    let some e := (← getState).enumOf? b | continue
    if Core.zeroSizedMapValues true e.variants.size (e.payloads.any (!·.isEmpty)) then
      let text (t : Syntax) := ((t.reprint.getD "").trimAscii).toString
      recordLint .zeroSizedMapValues r (Core.zeroSizedMapValuesMsg (text r[2]) (text r[4]) e.variants[0]!.toString)

/-- Where the annotation `: T` of the type `ty` is, from the end of what
precedes it. -/
def annotationRef (ty : Syntax) : Syntax := Id.run do
  let some sub := ty.getSubstring? false false | return ty
  let before := (String.Pos.Raw.extract sub.str 0 sub.startPos).toList.reverse
  let ws := before.takeWhile Char.isWhitespace
  let rest := before.drop ws.length
  let colon := if rest.head? == some ':' then [':'] else []
  let ws' := (rest.drop colon.length).takeWhile Char.isWhitespace
  let n := (ws ++ colon ++ ws').foldl (fun n c => n + c.utf8Size) 0
  return .atom (.synthetic ⟨sub.startPos.byteIdx - n⟩ sub.stopPos) ""

/-- Records `redundant_bool_type` on the declaration of `n` with the type
`ty`, if it is `Bool` (`lint::redundant_bool_type`). -/
def lintBoolType (n : Name) (ty : Syntax) (t : Expr) : TermElabM Unit := do
  if Core.redundantBoolType n (some (t.isConstOf ``Bool)) then
    recordLint .redundantBoolType (annotationRef ty) (Core.redundantBoolTypeMsg n)

def varType (modName : Name) (name : Syntax) (ty? : Option Syntax) : TermElabM Expr := do
  let n := name.getId
  let t ← ty?.mapM (elabType modName)
  if let some ty := ty? then lintRelTypes modName ty
  unless Core.generatedName (Core.nameText n) do
    liftMsg name (Core.checkVarName n (t.map (·.isConstOf ``Bool)))
    if let (some ty, some t) := (ty?, t) then lintBoolType n ty t
  return t.getD (Lean.mkConst ``Bool)

/-- What a field's or payload's type is declared in: a payload of an
enumeration, a field of a record, or a newtype's. -/
inductive FieldPlace where
  | payload
  | field
  | newtype
  deriving BEq

/-- Lean syntax for the Lean type of a Fren type: a constant, or one applied
to type arguments; within the declaration of a generic type, `.bvar k` is
its type parameter `params[k]`. -/
partial def typeSyntax (t : Expr) (params : Array Name := #[]) : Term :=
  let go (t : Expr) := typeSyntax t params
  if t.isAppOfArity ``Fren.FinSet 1 then Unhygienic.run `(Fren.FinSet $(go t.appArg!))
  else if t.isAppOfArity ``Fren.Seq 1 then Unhygienic.run `(Fren.Seq $(go t.appArg!))
  else if t.isAppOfArity ``Prod 2 then Unhygienic.run `($(go t.appFn!.appArg!) × $(go t.appArg!))
  else if let .bvar k := t then mkIdent (params[k]?.getD `_)
  else if t.isConst then mkCIdent t.constName!
  else if t.getAppFn.isConst then
    Unhygienic.run `(($(mkCIdent t.getAppFn.constName!) $(t.getAppArgs.map go)*))
  -- Not known yet, as the element type of `[]`: Lean infers it.
  else Unhygienic.run `(_)


end Fren
