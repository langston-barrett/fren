-- keep-sorted start
import FrenCore.Closures
import FrenCore.Generics
import FrenCore.Names
import FrenCore.SubsetTypes
import FrenCore.Theories
import FrenCore.Traits
import Lean.Data.Json.Printer
-- keep-sorted end

/-! # The structural theories dump (`Reqs/Cli#theories`)

Both front ends supply declaration facts from their own elaborated models.
This view uses the shared theory, signature and morphism structures, but its
term slots are opaque placeholders, never inputs to checking.
-/

namespace Fren.Core

open Lean (Name)

/-- A variable of an elaborated procedure, including its call variables. -/
structure TheoryDumpVariable where
  name : Name
  type : Ty
  role : Role
  isPub : Bool
  deriving Inhabited

/-- The declaration facts needed for the structural view. Clause keywords
are `require`, `ensure`, `expect` and `define`; their terms remain opaque. -/
structure TheoryDumpItem where
  item : Item
  parameters : Array Name := #[]
  types : Array Ty := #[]
  higherOrder : Array HoParam := #[]
  defined : Bool := false
  alias? : Option PTy := none
  carrier? : Option Ty := none
  constructors : Array (Name × Array (Name × Ty)) := #[]
  variables : Array TheoryDumpVariable := #[]
  clauses : Array (Name × String) := #[]
  calls : Array (Name × Name) := #[]
  subset? : Option Name := none
  subsetInvariant? : Option Name := none
  deriving Inhabited

/-- An interpretation or implementation whose Lean term is opaque. -/
structure TheoryDumpBinding where
  kind : String
  source : Name
  reference : String
  deriving Inhabited

structure TheoryDumpInput where
  items : Array TheoryDumpItem
  uses : Array UseDef := #[]
  genericUses : Array GenericUse := #[]
  laws : Array Name := #[]
  bindings : Array TheoryDumpBinding := #[]
  deriving Inhabited

/-- A named theory and the names of its sentence entries, in the same order. -/
structure DumpTheory where
  name : Name
  owner : Name
  kind : String
  theory : Theory
  sentences : Array Name := #[]
  deriving Inhabited

structure DumpMorphism where
  kind : String
  source : Name
  target : Name
  types : Array (Name × Ty) := #[]
  items : Array (Name × Name) := #[]
  bindings : Bool := false
  reference? : Option String := none
  deriving Inhabited

structure DumpInstance where
  name : Name
  source : Name
  sites : Array Name
  signature : TheorySignature
  deriving Inhabited

structure TheoryDiagram where
  theories : Array DumpTheory := #[]
  morphisms : Array DumpMorphism := #[]
  instances : Array DumpInstance := #[]
  deriving Inhabited

/-- Implementation names and the numeric components of type-parameter
placeholders cannot be source declaration paths. The prelude root is kept
for looking up signatures of instances; its declarations are not printed. -/
def theorySourceName : Name → Bool
  | .anonymous => true
  | .str p n => (p.isAnonymous && Name.mkSimple n == preludeModule) ||
      (theorySourceName p && !generatedName n)
  | .num .. => false

/-- Sentence roles use the declaration's status, not the outcome of a check. -/
def theoryDumpRole (defined : Bool) : String → TheorySentenceRole
  | "require" | "define" => .domain
  | "expect" => .goal
  | "ensure" => if defined then .theorem else .axiom
  | _ => .axiom

private def opaqueTerm : TheoryTerm := .literal ""

/-- The term fields deliberately carry no front-end syntax. -/
def theoryDumpSentence (role : TheorySentenceRole) (vars : List (Name × Ty)) (calls : Nat) : TheorySentence :=
  { role, variables := vars, domain := opaqueTerm, calls := List.replicate calls opaqueTerm, claims := [opaqueTerm] }

private def declaration (d : TheoryDumpItem) : TheoryDeclaration :=
  let kind := match d.item.kind with
    | .enumItem | .recordItem => TheoryDeclarationKind.datatype
    | .typeItem => if d.carrier?.isSome then .datatype else .type
    | .fnItem => .function
    | .compItem => .procedure
    | .constItem => .constant
    | _ => .implementation
  let types := if d.item.kind == .compItem then
      d.variables.filterMap fun v => if v.isPub && v.name.isAtomic then some v.type else none
    else if !d.higherOrder.isEmpty then
      d.higherOrder.filterMap (fun | .value t => some t | _ => none) ++ d.types.back?.toArray
    else d.types
  { name := d.item.path, kind
    abstract := match kind with
      | .function => !d.defined
      | .procedure => true
      | .type => d.alias?.isNone
      | _ => false
    types := (types.map (·.asParams d.item.path d.parameters)).toList }

private def entries (d : TheoryDumpItem) : List TheoryEntry := Id.run do
  let main := declaration d
  let mut out := [TheoryEntry.declaration main]
  if let some carrier := d.carrier? then
    for (ctor, fields) in d.constructors do
      let name := match carrier with
        | .newtype .. => d.item.path
        | _ => if d.item.kind == .enumItem then d.item.path ++ ctor
          else d.item.path ++ Name.mkSimple "{}"
      let args := fields.map (·.2.asParams d.item.path d.parameters)
      out := out ++ [.declaration { name, kind := .constructor, abstract := false, types := args.toList ++ [carrier] }]
      for (field, ty) in fields do
        let name := if d.item.kind == .enumItem then name ++ field else d.item.path ++ field
        let selector : TheoryDeclaration := {
          name, kind := .function, abstract := false
          types := [carrier, ty.asParams d.item.path d.parameters] }
        out := out ++ [.declaration selector]
  return out

private def parameters (d : TheoryDumpItem) : List TheoryDeclaration := Id.run do
  let mut out := d.parameters.toList.map fun n =>
    { name := d.item.path ++ n, kind := .type, abstract := true : TheoryDeclaration }
  for p in d.higherOrder, k in [0:d.higherOrder.size] do
    if let .function f := p then
      out := out ++ [{
        name := d.item.path ++ Name.mkSimple s!"argument_{k}", kind := .function, abstract := true
        types := ((f.params.push f.result).map (·.asParams d.item.path d.parameters)).toList }]
  return out

private def sentences (d : TheoryDumpItem) : Array (Name × TheorySentence) := Id.run do
  -- Function clauses are closed over positional arguments. Binder names inside
  -- opaque function terms have no bearing on the structural comparison.
  let vars := if d.item.kind == .fnItem then
      ((declaration d).types.dropLast.zipIdx.map fun (t, k) => (Name.mkSimple s!"arg{k}", t))
    else d.variables.toList.map fun v => (v.name, v.type.asParams d.item.path d.parameters)
  return d.clauses.toList.eraseDups.toArray.map fun (n, keyword) =>
    (d.item.path ++ n, theoryDumpSentence (theoryDumpRole (d.item.kind == .fnItem && d.defined) keyword) vars d.calls.size)

private def addSentences (t : DumpTheory) (ss : Array (Name × TheorySentence)) : DumpTheory :=
  { t with theory := { t.theory with entries := t.theory.entries ++ ss.toList.map (.sentence ·.2) }
           sentences := t.sentences ++ ss.map (·.1) }

private partial def symbolicType (ty : Ty) : Bool :=
  match ty with
  | .param .. => true
  | _ => ty.hasTypeParam || ty.parts.any symbolicType

private def dumpInstanceName (source scope : Name) (args : Array Ty) : Name :=
  let parent := if args.any symbolicType then scope ++ source.getPrefix else source.getPrefix
  parent ++ Name.mkSimple (source.getString! ++ s!"<{", ".intercalate (args.toList.map Ty.showQualified)}>")

private def translateSignature (s : TheorySignature) (m : TheoryMorphism) : TheorySignature :=
  { parameters := [], items := s.items.map fun d => { d with name := m.item d.name, types := d.types.map m.type } }

private partial def typeApplications (ty : Ty) : Array (Name × Array Ty) :=
  let nested := ty.parts.toArray.flatMap typeApplications
  match ty with
  | .enum p ts | .record p ts => if ts.isEmpty then nested else nested.push (p, ts.toArray)
  | _ => nested

/-- Build the diagram without elaborating, unfolding or querying a term. The
same projection chooses roles, parameterization, instance names and maps for
both front ends. Ordering is canonicalized by the printer. -/
def theoryDiagram (input : TheoryDumpInput) : TheoryDiagram := Id.run do
  let hidden := input.items.flatMap fun d =>
    (d.alias?.toArray.flatMap (·.invariants.map (·.predicate))) ++
      (if d.subset?.isSome || d.subsetInvariant?.isSome then #[d.item.path] else #[])
  let items := input.items.filter fun d => theorySourceName d.item.path && !hidden.contains d.item.path
  let mut nodes : Array DumpTheory := #[{
    name := .anonymous, owner := .anonymous, kind := "module"
    theory := { parameters := [], entries := [] } }]
  for d in items do
    if d.item.kind == .moduleItem || d.item.kind == .traitItem then
      unless nodes.any (·.name == d.item.path) do
        nodes := nodes.push {
          name := d.item.path, owner := d.item.owner
          kind := if d.item.kind == .traitItem then "interface" else "module"
          theory := { parameters := [], entries := [] } }
  for d in items do
    if d.item.kind == .moduleItem || d.item.kind == .traitItem then continue
    let es := if d.item.kind == .expectItem then [] else entries d
    let ss := sentences d
    if let some k := nodes.findIdx? (·.name == d.item.owner) then
      let t := nodes[k]!
      let self := d.item.path == d.item.owner ++ selfName && t.kind == "interface"
      nodes := nodes.set! k <| addSentences
        { t with theory := { t.theory with
            parameters := t.theory.parameters ++ (if self then [declaration d] else [])
            entries := t.theory.entries ++ (if self then [] else es) } } ss
    if d.item.kind == .fnItem || d.item.kind == .compItem || d.item.kind == .expectItem || !d.parameters.isEmpty then
      nodes := nodes.push <| addSentences
        { name := d.item.path, owner := d.item.owner
          kind := match d.item.kind with
            | .fnItem => "function" | .compItem => "procedure" | .expectItem => "sentence" | _ => "datatype"
          theory := { parameters := parameters d, entries := es } } ss
    if let some alias := d.alias? then
      for inv in alias.invariants do
        if inv.name.getPrefix == d.item.path then
          if let some k := nodes.findIdx? (·.name == d.item.owner) then
            nodes := nodes.modify k (addSentences · #[(inv.name, theoryDumpSentence .«axiom» [] 0)])
  for law in input.laws do
    if let some k := nodes.findIdx? (·.name == law.getPrefix) then
      nodes := nodes.modify k (addSentences · #[(law, theoryDumpSentence .«axiom» [] 0)])
  let mut out : TheoryDiagram := { theories := nodes.filter (!inPrelude ·.name) }
  for u in input.uses do
    if inPrelude u.scope then continue
    unless theorySourceName u.scope && theorySourceName u.target do continue
    let signature : Option TheorySignature := (nodes.find? (·.name == u.target)).map (·.theory.signature)
    let names := match signature with
      | some s => s.items.toArray.map TheoryDeclaration.name
      | none => #[u.target]
    out := { out with morphisms := out.morphisms.push {
      kind := if u.glob then "open" else "inclusion",
      source := u.target, target := u.scope, items := names.map fun n => (n, n) } }
  for d in items do
    if inPrelude d.item.path then continue
    for (name, callee) in d.calls do
      let target := d.item.path ++ name
      out := { out with morphisms := out.morphisms.push {
        kind := "call", source := callee, target, items := #[(callee, target)], bindings := true } }
      if let some base := nodes.find? (·.name == callee) then
        let m : TheoryMorphism := { item := fun n => n.replacePrefix callee target }
        out := { out with instances := out.instances.push {
          name := target, source := callee, sites := #[d.item.path],
          signature := translateSignature base.theory.signature m } }
  let mut applications : Array (Name × Name × Array Ty × Name) := #[]
  for u in input.genericUses do
    if inPrelude u.item then continue
    let scope := u.caller?.getD u.item
    unless theorySourceName u.item && theorySourceName scope do continue
    let ps := ((items.find? (·.item.path == scope)).map (·.parameters)).getD #[]
    applications := applications.push (u.callee, scope, u.targs.map (·.asParams scope ps), u.item)
  for d in items do
    if inPrelude d.item.path then continue
    -- Visit the projected signature: backends store higher-order value and
    -- function parameters in different raw fields.
    let declarations := parameters d ++ theorySignatureItems (entries d)
    let tys := (declarations.flatMap TheoryDeclaration.types).toArray ++ d.variables.map (·.type)
    for ty in tys do
      for (p, args) in typeApplications (ty.asParams d.item.path d.parameters) do
        if p == d.item.path then continue
        applications := applications.push (p, d.item.path, args, d.item.path)
  for (source, scope, args, site) in applications do
    let some base := nodes.find? (·.name == source) | continue
    let target := dumpInstanceName source scope args
    if let some k := out.instances.findIdx? (·.name == target) then
      unless out.instances[k]!.sites.contains site do
        out := { out with instances := out.instances.modify k fun i => { i with sites := i.sites.push site } }
      continue
    let ps := ((items.find? (·.item.path == source)).map (·.parameters)).getD #[]
    let m : TheoryMorphism := { type := (·.subst args), item := fun n => n.replacePrefix source target }
    let signature := translateSignature base.theory.signature m
    out := { out with instances := out.instances.push {
      name := target, source, sites := #[site], signature } }
    out := { out with morphisms := out.morphisms.push {
      kind := "generic", source, target,
      types := ps.zip args |>.map fun (p, t) => (source ++ p, t),
      items := base.theory.signature.items.toArray.map fun d => (d.name, m.item d.name) } }
  for b in input.bindings do
    if inPrelude b.source then continue
    out := { out with morphisms := out.morphisms.push {
      kind := b.kind, source := b.source, target := .anonymous, reference? := some b.reference } }
  return out

def theoriesStart : String := "; theories"
def theoriesEnd : String := "; end of theories"

/-- One canonical printer. No term, Lean expression, SMT symbol or map
iteration order is printed. Identical lines are kept once. -/
def dumpTheories (diagram : TheoryDiagram) : String := Id.run do
  let q (s : String) := (Lean.Json.str s).compress
  let name (n : Name) := q (if n.isAnonymous then "<root>" else (if inPrelude n then "prelude::" else "") ++ showPath n)
  let sorted (xs : Array String) := (xs.qsort (· < ·)).toList.eraseDups
  let list (xs : List String) := " ".intercalate xs
  let decl (d : TheoryDeclaration) :=
    let kind := match d.kind with
      | .type => "type" | .datatype => "datatype" | .constructor => "constructor"
      | .constant => "constant" | .function => "function" | .procedure => "procedure" | .implementation => "implementation"
    s!"({kind} {name d.name} {if d.abstract then "abstract" else "defined"} ({list (d.types.map (q ∘ Ty.showQualified))}))"
  let sig (s : TheorySignature) :=
    s!"(signature (parameters {list (sorted (s.parameters.toArray.map decl))}) (items {list (sorted (s.items.toArray.map decl))}))"
  let mut lines := #[]
  for t in diagram.theories do
    let mut ss := #[]
    let mut k := 0
    for e in t.theory.entries do
      if let .sentence s := e then
        let role := match s.role with
          | .domain => "domain" | .«theorem» => "theorem" | .«axiom» => "axiom" | .goal => "goal"
        let vars := s.variables.map fun (n, ty) => s!"({name n} {q ty.showQualified})"
        ss := ss.push s!"(sentence {name (t.sentences[k]?.getD .anonymous)} {role} (parameters {list vars}) (domain opaque) (calls {s.calls.length}) (claims opaque))"
        k := k + 1
    lines := lines.push s!"(theory {name t.name} {t.kind} (owner {name t.owner}) {sig t.theory.signature} (sentences {list (sorted ss)}))"
  for m in diagram.morphisms do
    let types := sorted (m.types.map fun (n, ty) => s!"({name n} {q ty.showQualified})")
    let items := sorted (m.items.map fun (a, b) => s!"({name a} {name b})")
    let bindings := if m.bindings then " (bindings opaque)" else ""
    let reference := (m.reference?.map fun r => s!" (opaque {q r})").getD ""
    lines := lines.push s!"(morphism {m.kind} (source {name m.source}) (target {name m.target}) (types {list types}) (items {list items}){bindings}{reference})"
  for i in diagram.instances do
    lines := lines.push s!"(instantiation {name i.name} (source {name i.source}) (sites {list (sorted (i.sites.map name))}) {sig i.signature})"
  return theoriesStart ++ "\n" ++ String.join ((sorted lines).map (· ++ "\n")) ++ theoriesEnd ++ "\n"

end Fren.Core
