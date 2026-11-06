-- keep-sorted start
import FrenCli.SeqElems
import FrenCore.SentenceBridge
-- keep-sorted end

/-! Extraction and reconstruction of executable SMT sentence formulas (#758).
Use `SeqElems.parse` on elaborated formulas, whose quoted symbols are retained.
Resolved metadata must accompany SMT terms: erased sorts alone cannot distinguish
newtypes, generic instances or `Nat` from `Int`. -/

namespace FrenCli.SentenceBridge

open Fren.Core
open Fren.Core.SentenceBridge
open SeqElems (SExpr)

abbrev Adapter := Bindings SExpr

/-- The environment contains lexical binders and already extracted aliases.
In particular, SMT `let` right-hand sides all see the outer environment. -/
partial def extract (b : Adapter) (e : SExpr) (env : List (String × Input) := []) : Option Input := do
  if let .atom a := e then
    if let some (_, i) := env.find? (·.1 == a) then return i
  let refs := (b.parameters.filter (·.2.2 == e)).map (Input.reference ∘ (·.1)) ++
    (b.locals.filter (·.2.2 == e)).map (Input.query ∘ (·.1))
  if !refs.isEmpty then return ← unique? refs
  let values := b.values.filter (·.2 == e)
  if !values.isEmpty then return .values (values.map (·.1))
  match e with
  | .list #[.atom "let", .list bindings, body] =>
    let aliases ← bindings.toList.mapM fun binding => do
      let .list #[.atom n, value] := binding | none
      return (n, ← extract b value env)
    extract b body (aliases ++ env)
  | .list #[.atom q, .list bindings, body] =>
    if q == "forall" || q == "exists" then
      readBinders q bindings.toList body env
    else readApplication e env
  | _ => readApplication e env
where
  readBinders (q : String) (bindings : List SExpr) (body : SExpr) (env : List (String × Input)) :
      Option Input := do
    match bindings with
    | [] => extract b body env
    | binding :: rest =>
      let .list #[.atom n, sort] := binding | none
      let (ty, _) ← unique? (b.types.filter (·.2 == sort))
      let env := (n, Input.bound 0) :: env.map fun (n, i) => (n, i.lift 1)
      let body ← readBinders q rest body env
      return if q == "forall" then .all ty body else .ex ty body
  readApplication (e : SExpr) (env : List (String × Input)) : Option Input := do
    let constants := b.heads.filter fun (h, native) => h.arguments.isEmpty && native == e
    if !constants.isEmpty then return .overloaded (constants.map (·.1)) []
    let (native, args) := match e with
      | .list xs => (xs[0]?.getD e, xs.toList.drop 1)
      | _ => (e, [])
    if native == .atom "=>" then return .apply implication (← args.mapM fun a => extract b a env)
    let hs := b.heads.filter fun (h, term) => term == native && h.arguments.length == args.length
    return .overloaded (hs.map (·.1)) (← args.mapM fun a => extract b a env)

def project (b : Adapter) (parameters : List (Lean.Name × Ty)) (e : SExpr) : Option TheoryTerm := do
  let i ← extract b e
  return (← Fren.Core.SentenceBridge.project b.signature parameters [] i).1

/-- Fresh names are chosen against every native term in the table, including
free query locals and symbol heads. The generated binder cannot capture one. -/
private def fresh (b : Adapter) (bound : List String) : String := Id.run do
  let terms := b.heads.map (·.2) ++ b.locals.map (·.2.2) ++ b.parameters.map (·.2.2) ++ b.values.map (·.2)
  let used := terms.flatMap fun t => (t.freeAtoms).toList
  let mut n := 0
  while used.contains s!"fren.bridge.{n}" || bound.contains s!"fren.bridge.{n}" do n := n + 1
  return s!"fren.bridge.{n}"

partial def build (b : Adapter) (bound : List String := []) : Input → Option SExpr
  | .reference n => (unique? (b.parameters.filter (·.1 == n))).map (·.2.2)
  | .query n => (unique? (b.locals.filter (·.1 == n))).map (·.2.2)
  | .bound k => (bound[k]?).map .atom
  | .value v => (unique? (b.values.filter (·.1 == v))).map (·.2)
  | .apply h args => do
    if h == implication then return .list ((.atom "=>" :: (← args.mapM (build b bound))).toArray)
    let (_, native) ← unique? (b.heads.filter (·.1 == h))
    if args.isEmpty then return native
    return .list ((native :: (← args.mapM (build b bound))).toArray)
  | .overloaded .. | .values .. => none
  | .all ty body => quantifier "forall" ty body
  | .ex ty body => quantifier "exists" ty body
where
  quantifier (q : String) (ty : Ty) (body : Input) : Option SExpr := do
    let (_, sort) ← unique? (b.types.filter (·.1 == ty))
    let n := fresh b bound
    return .list #[.atom q, .list #[.list #[.atom n, sort]], ← build b (n :: bound) body]

def rebuild (b : Adapter) (parameters : List (Lean.Name × Ty)) (t : TheoryTerm) : Option SExpr := do
  let (i, _) ← decode b.signature parameters [] t
  build b [] i

def sentence (b : Adapter) (s : Sentence SExpr) : Option (Sentence TheoryTerm) := do
  Fren.Core.SentenceBridge.sentence b.signature (← s.mapM (extract b))

def rebuildSentence (b : Adapter) (s : Sentence TheoryTerm) : Option (Sentence SExpr) := do
  (← decodeSentence b.signature s).mapM (build b [])

def query (b : Adapter) (terms calls : List SExpr) : Option GroundMatching.Query := do
  Fren.Core.SentenceBridge.query b.signature (← terms.mapM (extract b)) (← calls.mapM (extract b))

def context (b : Adapter) (defs : List (SExpr × SExpr))
    (listed : List (Ty × List SExpr)) : Option GroundMatching.Context := do
  let defs ← defs.mapM fun (lhs, rhs) => return (← extract b lhs, ← extract b rhs)
  let listed ← listed.mapM fun (ty, values) => return (ty, ← values.mapM (extract b))
  prepareContext b.signature defs listed

end FrenCli.SentenceBridge
