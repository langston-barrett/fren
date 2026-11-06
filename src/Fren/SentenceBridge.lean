-- keep-sorted start
import FrenCore.SentenceBridge
import Lean.Meta.Basic
-- keep-sorted end

/-! Extraction and reconstruction of executable Lean sentence formulas (#758).
The caller supplies resolved heads, locals, literal values and types from
elaboration. A head includes its type, instance and placeholder arguments;
only its explicit value arguments enter the shared first-order syntax. -/

namespace Fren.SentenceBridge

open Lean
open Core.SentenceBridge

abbrev Adapter := Bindings Expr

private def staticHead (b : Adapter) (e : Expr) : Bool :=
  !e.hasLooseBVars && !(e.find? fun t =>
    b.parameters.any (·.2.2 == t) || b.locals.any (·.2.2 == t)).isSome

/-- Read actual expression structure. No expression printing or declaration
unfolding participates in symbol identity. Local `let`s are reduced lexically. -/
partial def extract (b : Adapter) (e : Expr) : Option Input := do
  match e with
  | .mdata _ e => extract b e
  | .letE _ _ value body _ => extract b (body.instantiate1 value)
  | .bvar k => return .bound k
  | _ =>
    let refs := (b.parameters.filter (·.2.2 == e)).map (Input.reference ∘ (·.1)) ++
      (b.locals.filter (·.2.2 == e)).map (Input.query ∘ (·.1))
    if !refs.isEmpty then return ← unique? refs
    let values := b.values.filter (·.2 == e)
    if !values.isEmpty then return .values (values.map (·.1))
    match e with
    | .forallE _ ty body _ =>
      if let some (ty, _) := unique? (b.types.filter (·.2 == ty)) then
        return .all ty (← extract b body)
      guard (!body.hasLooseBVar 0)
      return .apply implication [← extract b ty, ← extract b (body.lowerLooseBVars 1 1)]
    | _ =>
      if e.isAppOfArity ``Exists 2 then
        let ty := e.getArg! 0
        let (ty, _) ← unique? (b.types.filter (·.2 == ty))
        let .lam _ _ body _ := e.getArg! 1 | none
        return .ex ty (← extract b body)
      let heads := b.heads.filter fun (h, native) =>
        staticHead b native && e.getAppNumArgs == native.getAppNumArgs + h.arguments.length &&
          e.getAppFn == native.getAppFn &&
          (e.getAppArgs.toList.take native.getAppNumArgs == native.getAppArgs.toList)
      let (_, native) ← heads.head?
      guard (heads.all fun (_, head) => head.getAppNumArgs == native.getAppNumArgs)
      return .overloaded (heads.map (·.1))
        (← (e.getAppArgs.toList.drop native.getAppNumArgs).mapM (extract b))

def project (b : Adapter) (parameters : List (Name × Core.Ty)) (e : Expr) : Option Core.TheoryTerm := do
  let i ← extract b e
  return (← Core.SentenceBridge.project b.signature parameters [] i).1

/-- The core decodes and type-checks first. Backend reconstruction only
restores implicit arguments, concrete types, and de Bruijn binders. -/
partial def build (b : Adapter) : Input → Option Expr
  | .reference n => (unique? (b.parameters.filter (·.1 == n))).map (·.2.2)
  | .query n => (unique? (b.locals.filter (·.1 == n))).map (·.2.2)
  | .bound k => some (.bvar k)
  | .value v => (unique? (b.values.filter (·.1 == v))).map (·.2)
  | .apply h args => do
    if h == implication then
      let [p, q] ← args.mapM (build b) | none
      return .forallE .anonymous p (q.liftLooseBVars 0 1) .default
    let (_, native) ← unique? (b.heads.filter (·.1 == h))
    return mkAppN native (← args.mapM (build b)).toArray
  | .overloaded .. | .values .. => none
  | .all ty body => do
    let (_, ty) ← unique? (b.types.filter (·.1 == ty))
    return .forallE .anonymous ty (← build b body) .default
  | .ex ty body => do
    let (_, ty) ← unique? (b.types.filter (·.1 == ty))
    return mkApp2 (mkConst ``Exists [Level.zero]) ty (.lam .anonymous ty (← build b body) .default)

def rebuild (b : Adapter) (parameters : List (Name × Core.Ty)) (t : Core.TheoryTerm) : Option Expr := do
  let (i, _) ← decode b.signature parameters [] t
  build b i

def sentence (b : Adapter) (s : Sentence Expr) : Option (Sentence Core.TheoryTerm) := do
  Core.SentenceBridge.sentence b.signature (← s.mapM (extract b))

def rebuildSentence (b : Adapter) (s : Sentence Core.TheoryTerm) : Option (Sentence Expr) := do
  (← decodeSentence b.signature s).mapM (build b)

def query (b : Adapter) (terms calls : List Expr) : Option Core.GroundMatching.Query := do
  Core.SentenceBridge.query b.signature (← terms.mapM (extract b)) (← calls.mapM (extract b))

def context (b : Adapter) (defs : List (Expr × Expr))
    (listed : List (Core.Ty × List Expr)) : Option Core.GroundMatching.Context := do
  let defs ← defs.mapM fun (lhs, rhs) => return (← extract b lhs, ← extract b rhs)
  let listed ← listed.mapM fun (ty, values) => return (ty, ← values.mapM (extract b))
  prepareContext b.signature defs listed

end Fren.SentenceBridge
