-- keep-sorted start
import FrenCore.GroundMatching
-- keep-sorted end

/-!
# Executable sentences (#758)

Front ends extract resolved nodes into `Input`. This module assigns the three
variable namespaces, checks types, and builds the syntax consumed by ground
matching. The inverse traversal lets each backend rebuild an instance without
using pretty-printed expressions as identities. Symbol tables describe concrete
instances, including the type arguments of generic items.
-/

namespace Fren.Core.SentenceBridge

open Lean (Name)

inductive Symbol where
  | item (name : Name)
  | constant (name : Name)
  | builtin (name : String)
  deriving Inhabited, BEq

/-- A resolved, fully instantiated first-order symbol. Backend adapters retain
its concrete head, including implicit arguments, alongside this description. -/
structure Head where
  symbol : Symbol
  types : List Ty := []
  arguments : List Ty := []
  result : Ty
  deriving Inhabited, BEq

/-- Builtin overloads include their whole signature. Signature items retain
their resolved path and explicit type arguments. -/
def Head.term (h : Head) : TheoryTerm :=
  let (head, types) := match h.symbol with
    | .constant n => (TheoryTerm.item n, h.types)
    -- Even a nullary call must be an application for the matching engine.
    | .item n => (TheoryTerm.item n,
        if h.types.isEmpty && h.arguments.isEmpty then [h.result] else h.types)
    | .builtin n => (.literal s!"op:{h.types.length}:{h.arguments.length}:{n}",
        h.types ++ h.arguments ++ [h.result])
  types.foldl (fun f t => .app f (.sort t)) head

/-- A literal's canonical value and Fren type, before solver sort erasure.
The text is a value encoding, never the printing of a compound expression. -/
structure Value where
  type : Ty
  text : String
  deriving Inhabited, BEq

def Value.term (v : Value) : TheoryTerm := .app (.literal ("value:" ++ v.text)) (.sort v.type)

/-- Lean represents implication with a nondependent proof binder, rather
than an application. Both adapters expose the same logical operator. -/
def implication : Head := ⟨.builtin "=>", [], [.bool, .bool], .bool⟩

/-- Resolved types for sentence parameters and free query locals. The two
namespaces may contain the same name with different native references. -/
structure Signature where
  heads : List Head := []
  parameters : List (Name × Ty) := []
  locals : List (Name × Ty) := []
  /-- Functions and procedures in declaration order. -/
  items : List Name := []
  deriving Inhabited

inductive Input where
  | reference (name : Name)
  | query (name : Name)
  | bound (index : Nat)
  | value (value : Value)
  | values (values : List Value)
  | apply (head : Head) (arguments : List Input)
  | overloaded (heads : List Head) (arguments : List Input)
  | all (type : Ty) (body : Input)
  | ex (type : Ty) (body : Input)
  deriving Inhabited

/-- Lift an extracted alias when entering a binder. SMT `let` bindings are
simultaneous; lifting their already extracted values avoids textual capture. -/
def Input.lift (amount : Nat) (cutoff : Nat := 0) : Input → Input
  | .bound k => .bound (if k < cutoff then k else k + amount)
  | .apply h args => .apply h (args.map (Input.lift amount cutoff))
  | .overloaded hs args => .overloaded hs (args.map (Input.lift amount cutoff))
  | .all ty b => .all ty (b.lift amount (cutoff + 1))
  | .ex ty b => .ex ty (b.lift amount (cutoff + 1))
  | t => t

/-- Backend terms accompany resolved metadata, not printed expression keys.
Heads include any backend-only implicit arguments. Types and literal values
are supplied before solver erasure, which cannot recover newtype identity. -/
structure Bindings (α : Type) where
  heads : List (Head × α) := []
  parameters : List (Name × Ty × α) := []
  locals : List (Name × Ty × α) := []
  types : List (Ty × α) := []
  values : List (Value × α) := []
  items : List Name := []

def Bindings.signature (b : Bindings α) : Signature :=
  let heads := b.heads.map (·.1)
  { heads := if heads.contains implication then heads else implication :: heads,
    parameters := b.parameters.map fun (n, ty, _) => (n, ty),
    locals := b.locals.map fun (n, ty, _) => (n, ty), items := b.items }

def hasParameter : List (Name × Ty) → Name → Bool
  | [], _ => false
  | (p, _) :: ps, n => p == n || hasParameter ps n

def reference (parameters : List (Name × Ty)) (n : Name) : TheoryTerm :=
  if hasParameter parameters n then .variable n else .query n

/-- Exactly one interpretation is required; ambiguity is never resolved by
table order. -/
def unique? : List α → Option α
  | [a] => some a
  | _ => none

private def lookupType (locals : List (Name × Ty)) (n : Name) : Option Ty :=
  unique? ((locals.filter (·.1 == n)).map (·.2))

private def localType (s : Signature) (ps : List (Name × Ty)) (n : Name) : Option Ty :=
  if hasParameter ps n then do
    let ty ← lookupType s.parameters n
    guard (lookupType ps n == some ty)
    return ty
  else lookupType s.locals n

/-- Type checking and namespace assignment are shared by both adapters.
An expected type selects an erased literal or overloaded builtin. Unknown,
ill-typed and ambiguous subtrees fail the whole projection. -/
partial def project (s : Signature) (ps : List (Name × Ty)) (bound : List Ty := [])
    (input : Input) (expected : Option Ty := none) : Option (TheoryTerm × Ty) := do
  let result ← match input with
    | .reference n => do
      guard (hasParameter ps n)
      pure (reference ps n, ← localType s ps n)
    | .query n => do pure (reference [] n, ← lookupType s.locals n)
    | .bound k => do pure (.bound k, ← bound[k]?)
    | .value v => some (v.term, v.type)
    | .values vs => do
      let v ← unique? (vs.filter fun v => expected.isNone || expected == some v.type)
      pure (v.term, v.type)
    | .apply h args => application [h] args
    | .overloaded hs args => application hs args
    | .all ty b => do
      let (b, _) ← project s ps (ty :: bound) b (some .bool)
      pure (.all ty b, .bool)
    | .ex ty b => do
      let (b, _) ← project s ps (ty :: bound) b (some .bool)
      pure (.ex ty b, .bool)
  guard (expected.isNone || expected == some result.2)
  return result
where
  application (hs : List Head) (args : List Input) : Option (TheoryTerm × Ty) :=
    unique? (hs.filterMap fun h => do
      guard (s.heads.contains h && args.length == h.arguments.length)
      guard (expected.isNone || expected == some h.result)
      let args ← (args.zip h.arguments).mapM fun (a, ty) => project s ps bound a (some ty)
      pure (args.foldl (fun f a => .app f a.1) h.term, h.result))

/-- Decode the typed syntax before handing it back to a backend. Partial
applications and type arguments in value position are rejected. -/
partial def decode (s : Signature) (ps : List (Name × Ty)) (bound : List Ty := [])
    (t : TheoryTerm) : Option (Input × Ty) := do
  match t with
  | .variable n =>
    guard (hasParameter ps n)
    let ty ← localType s ps n
    return (.reference n, ty)
  | .query n =>
    let ty ← lookupType s.locals n
    return (.query n, ty)
  | .bound k => return (.bound k, ← bound[k]?)
  | .all ty b | .ex ty b =>
    let (b, bt) ← decode s ps (ty :: bound) b
    guard (bt == .bool)
    return (if let .all .. := t then .all ty b else .ex ty b, .bool)
  | .app (.literal text) (.sort ty) =>
    if let some v := text.dropPrefix? "value:" then
      return (.value ⟨ty, v.toString⟩, ty)
    else decodeApplication t
  | _ => decodeApplication t
where
  decodeApplication (t : TheoryTerm) : Option (Input × Ty) := do
    let (base, args) := GroundMatching.spine t
    unique? (s.heads.filterMap fun h => do
      let (_, types) := GroundMatching.spine h.term
      guard (base == (GroundMatching.spine h.term).1 && args.take types.length == types
        && args.length == types.length + h.arguments.length)
      let args ← (args.drop types.length).mapM fun a => decode s ps bound a
      guard (args.map (·.2) == h.arguments)
      pure (.apply h (args.map (·.1)), h.result))

/-- Labels stay beside their formulas throughout instantiation. -/
structure Sentence (α : Type) where
  name : Name
  role : TheorySentenceRole
  variables : List (Name × Ty)
  domain : α
  calls : List (Name × α) := []
  claims : List (Name × α) := []
  deriving Inhabited

def Sentence.mapM [Monad m] (f : α → m β) (s : Sentence α) : m (Sentence β) := do
  let domain ← f s.domain
  let calls ← s.calls.mapM fun (n, t) => return (n, ← f t)
  let claims ← s.claims.mapM fun (n, t) => return (n, ← f t)
  return { name := s.name, role := s.role, variables := s.variables, domain, calls, claims }

def Sentence.theory (s : Sentence TheoryTerm) : TheorySentence :=
  ⟨s.role, s.variables, s.domain, s.calls.map (·.2), s.claims.map (·.2)⟩

private def validVariables (s : Signature) (ps : List (Name × Ty)) : Bool :=
  ps.all (fun (n, ty) => lookupType s.parameters n == some ty) &&
    (ps.map (·.1)).eraseDups.length == ps.length

def sentence (s : Signature) (input : Sentence Input) : Option (Sentence TheoryTerm) := do
  guard (validVariables s input.variables)
  input.mapM fun i => do
    let (t, ty) ← project s input.variables [] i (some .bool)
    guard (ty == .bool)
    return t

def decodeSentence (s : Signature) (input : Sentence TheoryTerm) : Option (Sentence Input) := do
  guard (validVariables s input.variables)
  input.mapM fun t => do
    let (i, ty) ← decode s input.variables [] t
    guard (ty == .bool)
    return i

/-- Reattach a closure instance to its source labels. The caller uses the
candidate's rule index to select the source sentence. -/
def Sentence.withInstance (s : Sentence α) (t : TheorySentence) : Option (Sentence TheoryTerm) := do
  guard (s.role == t.role && s.calls.length == t.calls.length && s.claims.length == t.claims.length)
  return {
    name := s.name, role := t.role, variables := t.variables, domain := t.domain,
    calls := (s.calls.zip t.calls).map fun ((n, _), term) => (n, term),
    claims := (s.claims.zip t.claims).map fun ((n, _), term) => (n, term) }

/-- Instantiation reuses the same simultaneous, capture-free core operation
as the closure engine. Labels never participate in matching. -/
def Sentence.instantiate (s : Sentence TheoryTerm) (images : Name → Option TheoryTerm) :
    Option (Sentence TheoryTerm) := do
  s.withInstance (← s.theory.instantiate images)

def query (s : Signature) (terms calls : List Input) : Option GroundMatching.Query := do
  let apps ← terms.mapM fun t => (project s [] [] t).map (·.1)
  let calls ← calls.mapM fun t => (project s [] [] t).map (·.1)
  return { applications := apps, calls }

/-- Definitions are supplied newest first, as the shared matching normalizer
expects. The bridge does not unfold function bodies. -/
def context (s : Signature) (definitions : List (TheoryTerm × TheoryTerm) := [])
    (listed : Ty → Option (List TheoryTerm) := fun _ => none) : GroundMatching.Context :=
  { items := s.items, typeOf := fun t => (decode s [] [] t).map (·.2), definitions, listed }

/-- Project lexical definitions and listed values with the same type checker
as formulas. An applied function cannot be a definition's left-hand side. -/
def prepareContext (s : Signature) (defs : List (Input × Input))
    (listed : List (Ty × List Input)) : Option GroundMatching.Context := do
  let defs ← defs.mapM fun (lhs, rhs) => do
    let (lhs, ty) ← project s [] [] lhs
    let valid : Bool := match lhs with | .query _ | .item _ => true | _ => false
    guard valid
    let (rhs, _) ← project s [] [] rhs (some ty)
    guard (rhs.ground)
    return (lhs, rhs)
  let listed ← listed.mapM fun (ty, values) => do
    let values ← values.mapM fun i => do
      let (t, _) ← project s [] [] i (some ty)
      guard (t.ground)
      return t
    return (ty, values)
  return context s defs (listed.lookup ·)

end Fren.Core.SentenceBridge
