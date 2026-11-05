-- keep-sorted start
import FrenCore.Theories
-- keep-sorted end

/-!
# Typed ground matching

Input extraction supplies resolved typed syntax, declaration order and finite
listed values. The core chooses anchors and substitutions. Candidate
construction and closure follow in unit 9b; claim integration in unit 10.
-/

namespace Fren.Core.GroundMatching

open Lean (Name)

deriving instance DecidableEq, ReflBEq, LawfulBEq for TheoryTerm

abbrev Substitution := List (Name × TheoryTerm)

/-- Expand an already normalized environment. Local aliases use `query`,
constants use `item`; applied item heads stay opaque. -/
def normalize (defs : List (TheoryTerm × TheoryTerm)) : TheoryTerm → TheoryTerm
  | .app (.item n) a => .app (.item n) (normalize defs a)
  | .app f a => .app (normalize defs f) (normalize defs a)
  | .all ty b => .all ty (normalize defs b)
  | .ex ty b => .ex ty (normalize defs b)
  | t@(.query _) | t@(.item _) => ((defs.find? (·.1 == t)).map (·.2)).getD t
  | t => t

/-- Normalize definitions newest first, each value in the scope of its tail. -/
def definitions : List (TheoryTerm × TheoryTerm) → List (TheoryTerm × TheoryTerm)
  | [] => []
  | (n, v) :: rest =>
    let ds := definitions rest
    (n, normalize ds v) :: ds

def same (defs : List (TheoryTerm × TheoryTerm)) (a b : TheoryTerm) : Bool :=
  normalize (definitions defs) a == normalize (definitions defs) b

/-- Simultaneous structural matching. Only declared parameters are holes.
A hole never captures a query binder. The extractor supplies term types,
including those of instantiated compound terms. -/
def matchTerm (variables : List (Name × Ty)) (typeOf : TheoryTerm → Option Ty)
    (pattern target : TheoryTerm) (s : Substitution := []) : Option Substitution :=
  match pattern with
  | .variable n =>
    match variables.lookup n with
    | none => if pattern == target then some s else none
    | some ty =>
      if !target.ground || typeOf target != some ty then none else
      match s.lookup n with
      | some t => if t == target then some s else none
      | none => some (s ++ [(n, target)])
  | .app f a =>
    match target with
    | .app g b => do
      let s ← matchTerm variables typeOf f g s
      matchTerm variables typeOf a b s
    | _ => none
  | .all ty b =>
    match target with
    | .all ty' c => if ty == ty' then matchTerm variables typeOf b c s else none
    | _ => none
  | .ex ty b =>
    match target with
    | .ex ty' c => if ty == ty' then matchTerm variables typeOf b c s else none
    | _ => none
  | _ => if pattern == target then some s else none

def spine : TheoryTerm → TheoryTerm × List TheoryTerm
  | .app f a => let (h, args) := spine f; (h, args ++ [a])
  | t => (t, [])

def mentions (n : Name) : TheoryTerm → Bool
  | .variable v => v == n
  | .app f a => mentions n f || mentions n a
  | .all _ b | .ex _ b => mentions n b
  | _ => false

mutual
/-- Complete curried applications, including applications in arguments.
Partial prefixes are not additional applications. Builtin heads are absent
from `items`, but their arguments can contain signature applications. -/
def applications (items : List Name) (t : TheoryTerm) : List TheoryTerm :=
  match t with
  | .app f a =>
    let here := match (spine t).1 with
      | .item n => if items.contains n then [t] else []
      | _ => []
    here ++ argumentApps items f ++ applications items a
  | .all _ b | .ex _ b => applications items b
  | _ => []

def argumentApps (items : List Name) : TheoryTerm → List TheoryTerm
  | .app f a => argumentApps items f ++ applications items a
  | _ => []
end

/-- A call term includes its inputs and outputs. Calls have their own
channel, distinct from function applications at the same syntax. -/
structure Query where
  applications : List TheoryTerm := []
  calls : List TheoryTerm := []
  deriving Inhabited

structure Rule where
  sentence : TheorySentence
  deriving Inhabited

def Rule.terms (r : Rule) : List TheoryTerm :=
  r.sentence.domain :: r.sentence.calls ++ r.sentence.claims

def callApplications (items : List Name) (calls : List TheoryTerm) : List TheoryTerm :=
  calls.flatMap fun c => (spine c).2.flatMap (applications items)

def Rule.applications (r : Rule) (items : List Name) : List TheoryTerm :=
  (r.sentence.domain :: r.sentence.claims).flatMap (GroundMatching.applications items) ++
  callApplications items r.sentence.calls

def headName (t : TheoryTerm) : Option Name :=
  match (spine t).1 with | .item n => some n | _ => none

def uses (terms : List TheoryTerm) (n : Name) : Bool :=
  terms.any (fun t => headName t == some n)

def lastSubject : List Name → List TheoryTerm → Option Name
  | [], _ => none
  | n :: ns, terms => (lastSubject ns terms).orElse fun _ => if uses terms n then some n else none

def Rule.subject (r : Rule) (items : List Name) : Option Name :=
  lastSubject items (r.applications items ++ r.sentence.calls)

/-- Whether there is no query binder dependency, treating sentence
parameters as free. This also detects binders in nested arguments. -/
def outer (t : TheoryTerm) (depth : Nat := 0) : Bool :=
  match t with
  | .bound k => k < depth
  | .app f a => outer f depth && outer a depth
  | .all _ b | .ex _ b => outer b (depth + 1)
  | _ => true

def compoundArg (vars : List (Name × Ty)) : TheoryTerm → Bool
  | .variable _ => false
  | t => vars.any fun (n, _) => mentions n t

def subjectApps (subject : Option Name) (apps : List TheoryTerm) : List TheoryTerm :=
  apps.filter fun t => subject.isSome && headName t == subject && outer t

def compoundApps (vars : List (Name × Ty)) (apps : List TheoryTerm) : List TheoryTerm :=
  apps.filter fun t => (spine t).2.any (compoundArg vars)

def anchors (vars : List (Name × Ty)) (apps : List TheoryTerm) : List TheoryTerm :=
  let compound := compoundApps vars apps
  if compound.isEmpty then apps else compound

def Rule.anchors (r : Rule) (items : List Name) : List TheoryTerm :=
  GroundMatching.anchors r.sentence.variables (subjectApps (r.subject items) (r.applications items))

/-- `some []` means a listed empty type; `none` means unlisted. Types of
resolved ground terms are extraction inputs, not matching decisions. -/
structure Context where
  items : List Name
  /-- Types of normalized ground terms. Resolved names and literal syntax
  include type identity, so syntactic equality cannot identify two types. -/
  typeOf : TheoryTerm → Option Ty
  listed : Ty → Option (List TheoryTerm) := fun _ => none
  /-- Only `query` aliases and `item` constants, in their resolved lexical
  scopes. Values contain no escaping de Bruijn indices; sentence parameters
  and query locals retain their separate resolved names. -/
  definitions : List (TheoryTerm × TheoryTerm) := []
  deriving Inhabited

def Rule.normalize (r : Rule) (defs : List (TheoryTerm × TheoryTerm)) : Rule :=
  { sentence := { r.sentence with
      domain := GroundMatching.normalize defs r.sentence.domain
      calls := r.sentence.calls.map (GroundMatching.normalize defs)
      claims := r.sentence.claims.map (GroundMatching.normalize defs) } }

/-- Laws failing the binding rule remain quantified; this engine contributes
no instances of them. Surface diagnostics belong to claim integration. -/
def binding (ctx : Context) (apps matched : List TheoryTerm) (vars : List (Name × Ty)) : Bool :=
  vars.all fun (n, ty) =>
    (ctx.listed ty).isSome ||
    !apps.any (mentions n) || matched.any (mentions n)

def Rule.instantiable (r : Rule) (ctx : Context) : Bool :=
  binding ctx (r.applications ctx.items ++ r.sentence.calls)
    (r.anchors ctx.items ++ r.sentence.calls.filter (outer ·)) r.sentence.variables

def matchTargets (ctx : Context) (vs : List (Name × Ty)) (p : TheoryTerm)
    (ts : List TheoryTerm) (s : Substitution) : List Substitution :=
  ts.filterMap fun t => if t.ground then matchTerm vs ctx.typeOf p t s else none

def join (ctx : Context) (vs : List (Name × Ty)) :
    List TheoryTerm → List TheoryTerm → List Substitution → List Substitution
  | [], _, ss => ss
  | p :: ps, ts, ss => join ctx vs ps ts (ss.flatMap (matchTargets ctx vs p ts))

def typedExtensions (ctx : Context) (n : Name) (ty : Ty) (values : List TheoryTerm)
    (s : Substitution) : List Substitution :=
  values.filterMap fun t =>
    if t.ground && ctx.typeOf t == some ty then some (s ++ [(n, t)]) else none

/-- Fill only mentioned, unbound listed parameters. An unused parameter
and an outside-only unlisted parameter retain their original quantifier. -/
def listedExtensions (ctx : Context) (terms : List TheoryTerm) (n : Name) (ty : Ty)
    (s : Substitution) : List Substitution :=
  if (s.lookup n).isSome || !terms.any (mentions n) then [s] else
    match ctx.listed ty with
    | none => [s]
    | some values => typedExtensions ctx n ty values s

def completeListed (ctx : Context) (terms : List TheoryTerm) :
    List (Name × Ty) → List Substitution → List Substitution
  | [], ss => ss
  | (n, ty) :: vs, ss => completeListed ctx terms vs (ss.flatMap (listedExtensions ctx terms n ty))

/-- Raw normalized matching, shared with the future closure engine. -/
def matchNormalized (ctx : Context) (r : Rule) (q : Query) : List Substitution :=
  if !r.instantiable ctx || !(r.subject ctx.items).all (uses (q.applications ++ q.calls)) then [] else
    let ss := join ctx r.sentence.variables (r.anchors ctx.items) q.applications [[]]
    let ss := join ctx r.sentence.variables (r.sentence.calls.filter (outer ·)) q.calls ss
    (completeListed ctx r.terms r.sentence.variables ss).eraseDups

/-- Join all anchors and calls through one substitution and two channels.
This structural matcher is also usable independently of closure. -/
def matchApplications (ctx : Context) (r : Rule) (q : Query) : List Substitution :=
  let ds := definitions ctx.definitions
  let norm := normalize ds
  let ctx := { ctx with listed := fun ty => (ctx.listed ty).map (List.map norm) }
  let calls := q.calls.map norm
  matchNormalized ctx (r.normalize ds) {
    applications := q.applications.flatMap (fun t => applications ctx.items (norm t)) ++
      callApplications ctx.items calls,
    calls }

/-- Preserve the complete domain/calls/claims and remaining quantifiers. -/
def instances (ctx : Context) (r : Rule) (q : Query) : List TheorySentence :=
  let normalized := r.normalize (definitions ctx.definitions)
  (matchApplications ctx r q).filterMap fun s => normalized.sentence.instantiate (fun n => s.lookup n)

end Fren.Core.GroundMatching
