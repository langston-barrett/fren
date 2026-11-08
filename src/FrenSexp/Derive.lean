module

public import FrenSexp.Constructor
public meta import FrenSexp.Basic
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public meta import Lean.PrettyPrinter.Delaborator

/-!
`deriving Fren.ToSexp, Fren.FromSexp` supports nonrecursive inductives and
structures with uniform type and value parameters, including phase-computed
field types. Only field codecs are required; parameters are never serialized.
Computed families use Lean instance search (use an abbrev/reducible family for
concrete-phase inference, or supply its field codec). Tags use `constructorAtom`;
structures use their type name. Fields use constructor declaration order, including Unit
fields, and their existing codecs. Nullary constructors use atoms, payloads use
lists with exact arity. Parsing is type-directed and prefixes field failures by
their wire child index.

Recursive, mutual, nested-recursive and constructor-refined indexed types,
higher-kinded/proof parameters, proof fields, dependent fields and function
fields are rejected in this slice. No recursive parser, production IR schema or proof-field omission
is implied. Roundtrip evidence for derived clients is in FrenSexpTests.Derive
and FrenSexpTests.Phase; the handler does not generate a roundtrip theorem.
-/

namespace Fren.Sexp.Deriving

open Lean Meta Elab Command Parser.Term
open Lean.Elab.Deriving
open TSyntax.Compat

private meta def validate (name : Name) : TermElabM (InductiveVal × Array String) := do
  let ind ← getConstInfoInduct name
  if ind.all.length != 1 || ind.isRec || ind.isNested || ind.numIndices != 0 then
    throwError "S-expression deriving supports only nonrecursive, nonmutual types without indices"
  if ind.ctors.isEmpty then
    throwError "S-expression deriving requires at least one constructor"
  forallTelescopeReducing ind.type fun params _ => do
    for param in params do
      let type ← whnf (← inferType param)
      if type.isForall || (← isProp type) || (type.isSort && (← isProp param)) then
        throwError "S-expression deriving: unsupported higher-kinded or proof parameter"
    let mut tags := #[]
    for ctorName in ind.ctors do
      let tagName := if isStructure (← getEnv) name then name else ctorName
      let tag ← match constructorAtom tagName.eraseMacroScopes with
        | .ok a => pure a.val
        | .error error => throwError "S-expression deriving: {error}"
      if tags.contains tag then
        throwError "S-expression constructor tag collision: {tag}"
      tags := tags.push tag
      let ctor ← getConstInfoCtor ctorName
      let type ← mkConstWithFreshMVarLevels ctorName
      let type ← inferType (mkAppN type params)
      forallTelescopeReducing type fun fields _ => do
        for i in [:fields.size] do
          let field := fields[i]!
          let fieldType ← whnf (← inferType field)
          if fieldType.isForall then
            throwError "S-expression deriving: unsupported function field {i + 1} of {privateToUserName ctor.name}"
          if ← isProp fieldType then
            throwError "S-expression deriving: unsupported proof field {i + 1} of {privateToUserName ctor.name}"
          if (fields.extract 0 i).any (fun prev => fieldType.containsFVar prev.fvarId!) then
            throwError "S-expression deriving: unsupported dependent field {i + 1} of {privateToUserName ctor.name}"
    return (ind, tags)

/-- Ask for codecs on the actual field types, not on parameter values. Closed
fields use existing instances. Parameter-dependent constraints let instance
search compute a reducible annotation family at concrete phases. -/
private meta def fieldBinders (ind : InductiveVal) (argNames : Array Name) (cls : Name) :
    TermElabM (Array Syntax) :=
  forallTelescopeReducing ind.type fun params _ => do
    let mut lctx ← getLCtx
    for i in [:params.size] do
      lctx := lctx.setUserName params[i]!.fvarId! argNames[i]!
    withLCtx lctx (← getLocalInstances) do
      let mut types : Array Expr := #[]
      let mut binders := #[]
      for ctorName in ind.ctors do
        let ctor := mkConst ctorName (ind.levelParams.map Level.param)
        let fieldTypes ← forallTelescopeReducing (← inferType (mkAppN ctor params)) fun fields _ =>
          fields.mapIdxM fun i field => do
            let escapes := fun type : Expr => (type.abstract params).hasFVar
            let type ← instantiateMVars (← inferType field)
            -- Erase apparent field dependencies while their locals are scoped.
            -- Stop once closed over params: unfolding further could replace an
            -- independent Ann p with its recursor and lose its codec interface.
            let type ← if escapes type then
                whnfHeadPred type (fun t => pure (escapes t))
              else pure type
            -- No constructor-field (or other nonparameter) fvar may escape this
            -- telescope into generated constraints, for either codec class.
            if escapes type then
              throwError "S-expression deriving: unsupported dependent field {i + 1} of {privateToUserName ctorName}"
            return type
        for type in fieldTypes do
          if params.any (fun p => type.containsFVar p.fvarId!) && !types.contains type then
            types := types.push type
            -- Preserve hidden parameters and independent universe arguments.
            let stx ← withOptions (fun o =>
                (o.setBool `pp.universes true).setBool `pp.explicit true) do
              PrettyPrinter.delab type
            binders := binders.push (← `(instBinderF| [$(mkCIdent cls) $stx]))
      return binders

private meta def mkInstance (name : Name) (encode : Bool) : TermElabM Syntax := do
  let (ind, tags) ← validate name
  let cls := if encode then ``Fren.ToSexp else ``Fren.FromSexp
  let argNames ← mkInductArgNames ind
  let binders ← mkImplicitBinders argNames
  let binders := binders ++ (← fieldBinders ind argNames cls)
  let target ← mkInductiveApp ind argNames
  let value := mkIdent (← mkFreshUserName `value)
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  let tag := mkIdent (← mkFreshUserName `tag)
  let mut parser ← ``(Fren.Sexp.unknownConstructor $value $(quote (", ".intercalate tags.toList)))
  -- Reverse only the construction of nested ifs; dispatch retains declaration order.
  for idx in (List.range ind.ctors.length).reverse do
    let ctorName := ind.ctors[idx]!
    let ctor ← getConstInfoCtor ctorName
    let names ← (List.range ctor.numFields).toArray.mapM fun _ =>
      return mkIdent (← mkFreshUserName `field)
    let params ← argNames.mapM fun _ => `(_)
    let ctorApp ← `(@$(mkCIdent ctorName) $params* $names*)
    let tagText := quote tags[idx]!
    if encode then
      let fields ← names.mapM fun x => ``(Fren.toSexp $x)
      let body ← if names.isEmpty then ``(Fren.Sexp.symbol $tagText)
        else ``(Fren.Sexp.list #[Fren.Sexp.symbol $tagText, $fields,*])
      alts := alts.push (← `(matchAltExpr| | $ctorApp => $body))
    else
      let xs := mkIdent (← mkFreshUserName `fields)
      let reads ← names.mapIdxM fun i _ =>
        ``(Fren.Sexp.atChild $(quote (i + 1)) (Fren.fromSexp $xs[$(quote (i + 1))]!))
      -- Monad.bind fixes one value universe. Explicit Except.bind permits each
      -- field, the Type-0 wire intermediates and the result to have different ones.
      let mut branch ← ``(Except.ok $ctorApp)
      for i in (List.range names.size).reverse do
        branch ← ``(Except.bind $(reads[i]!) (fun $(names[i]!) => $branch))
      branch ← ``(Except.bind
        (Fren.Sexp.readConstructorFields $value $tagText $(quote ctor.numFields))
        (fun $xs => $branch))
      parser ← `(if $tag == $tagText then $branch else $parser)
  let body ← if encode then `(term| match $value:term with $alts:matchAlt*)
    else ``(Except.bind (Fren.Sexp.readConstructorTag $value) (fun $tag => $parser))
  let instName ← mkInstName cls name
  `(command|
    instance $(mkIdent instName):ident $binders:implicitBinder* :
        $(mkCIdent cls):ident $target := ⟨fun $value => $body⟩)

private meta def handler (encode : Bool) (names : Array Name) : CommandElabM Bool := do
  if names.isEmpty || !(← names.allM isInductive) then return false
  for name in names do
    withoutExposeFromCtors name do
      elabCommand (← liftTermElabM (mkInstance name encode))
  return true

meta initialize
  registerDerivingHandler ``Fren.ToSexp (handler true)
  registerDerivingHandler ``Fren.FromSexp (handler false)

end Fren.Sexp.Deriving
