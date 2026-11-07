-- keep-sorted start
import Fren.Elab.TypeTerms
-- keep-sorted end

/-! # Hosted elaboration: names -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ### Patterns (`Reqs/Lang/Patterns`) -/

/-- The alternatives of a pattern of `match` or `is`, a `fren_top_pattern`,
as written, and whether it is an or-pattern: of more than one, or with a
leading `|`. -/
def topAlts (top : Syntax) : Array Syntax × Bool :=
  let alts := top[1].getSepArgs
  (alts, alts.size > 1 || !top[0].isNone)

/-- The payload's patterns of a variant pattern, each a `fren_or_pattern`. -/
def patternArgs (p : Syntax) : Array Syntax :=
  if p.isOfKind ``Lang.variantPattern && !p[1].isNone then p[1][1].getSepArgs else #[]

mutual
/-- The alternatives of the or-patterns within the pattern `p`, in preorder
(`Core.Pat.alternatives`). -/
partial def innerAlternatives (p : Syntax) : Array Syntax :=
  (patternArgs p).flatMap fun a => orAlternatives a[0].getSepArgs (a[0].getSepArgs.size > 1)

/-- The alternatives `alts` of an or-pattern (`isOr`), each followed by
those within it, or those within its only pattern. -/
partial def orAlternatives (alts : Array Syntax) (isOr : Bool) : Array Syntax :=
  if isOr then alts.flatMap fun a => #[a] ++ innerAlternatives a else alts.flatMap innerAlternatives
end

/-- The alternatives of the or-patterns of the pattern `top` of `match` or
`is`, in preorder. -/
def topAlternatives (top : Syntax) : Array Syntax := let (alts, isOr) := topAlts top; orAlternatives alts isOr

/-- The identifiers of one segment, not applied, of the pattern `p`, in
preorder: its binders, once those that name variants, `true` and `false`
are told apart. -/
partial def patternNames (p : Syntax) : Array Syntax :=
  if p.isOfKind ``Lang.variantPattern then
    if p[1].isNone then
      match pathSegs p[0] with
      | #[x] => #[x]
      | _ => #[]
    else (patternArgs p).flatMap fun a => a[0].getSepArgs.flatMap patternNames
  else #[]

/-- The identifiers of one segment, not applied, of the pattern `top` of
`match` or `is`. -/
def topNames (top : Syntax) : Array Syntax := (topAlts top).1.flatMap patternNames

/-- The names that the quantifier `e` binds, without the `!` of shadowing. -/
def quantNames (e : Syntax) : Array Name :=
  e[1].getArgs.flatMap fun b => b[1].getArgs.map fun x => (declaredIdent x).1.getId

/-- The identifier of the closure's parameter `p`, at `k`: for `_`, which
declares no name, one that no spec can write or mention. -/
def closureParamIdent (p : Syntax) (k : Nat) : Syntax :=
  if !p[0].isIdent then mkIdentFrom p[0] (Name.mkSimple s!"#_{k}") else p[0]

/-- The names of the parameters of the closure `e`, without the `!` of
shadowing. -/
def closureNames (e : Syntax) : Array Name :=
  e[1].getSepArgs.mapIdx fun k p => (declaredIdent (closureParamIdent p k)).1.getId

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def pathMentions (e : Syntax) (all : Bool := true) : Array Name :=
  let pathMentions (e : Syntax) := pathMentions e all
  if e.isOfKind ``Lang.appExpr then
    -- `x.m(a)` is a method call, which mentions `x`: a function's name has
    -- no dots.
    let recv := match (pathSegs e[0]).toList with
      | [id] => if id.getId.isAtomic then #[] else
        (id.getId.getPrefix.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
      | _ => #[]
    e[2].getSepArgs.foldl (· ++ pathMentions ·) recv
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size == 1 then
      (segs[0]!.getId.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
    else #[]
  else if e.isOfKind ``Lang.recordExpr then
    e[2].getSepArgs.foldl (init := #[]) fun acc b => acc ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
  else if e.isOfKind ``Lang.updateExpr then
    e[3].getSepArgs.foldl (init := pathMentions e[1]) fun acc b =>
      acc ++ if b[1].isNone then #[b[0].getId] else pathMentions b[1][1]
  else if isMatchLike e || e.isOfKind ``Lang.lambdaMatchExpr then
    (matchSourceArms e).foldl (init := (matchScrutinees e).flatMap pathMentions) fun acc arm =>
      -- In its arm, a binder's name means the binder, not what it shadows.
      let bound := ((matchPatterns e arm).flatMap topNames).map fun b => (declaredIdent b).1.getId
      let guard := if arm[1].isNone then #[] else pathMentions arm[1][1]
      acc ++ (guard ++ pathMentions arm[3]).filter (!bound.contains ·.getRoot)
  -- A pattern's paths name variants.
  else if e.isOfKind ``Lang.isExpr then pathMentions e[0]
  else if e.isOfKind ``Lang.letExpr then
    let defs := e[1].getSepArgs
    (Core.clauseMentions (defs.map fun d => (declaredIdent d[0]).1.getId) (defs.map fun d => pathMentions d[3]) (pathMentions e[3]) all).1
  -- In its body, a bound name means the bound name, not what it shadows,
  -- and its binders' types are not variables.
  else if e.isOfKind ``Lang.quantExpr then
    let bound := quantNames e
    (pathMentions e[3]).filter (!bound.contains ·.getRoot)
  else if e.isOfKind ``Lang.closureExpr then
    let bound := closureNames e
    (pathMentions e[3]).filter (!bound.contains ·.getRoot)
  -- In what sees them, the names that the pattern tests of a condition, or
  -- of the left operand of `and`, bind mean them (`lang::test_scope`).
  else if let some (c, d, others) := testScoped? e then
    let bound := (chainTests c).flatMap fun (_, p) => (topNames p).map fun b => (declaredIdent b).1.getId
    pathMentions c ++ (pathMentions d).filter (!bound.contains ·.getRoot) ++ others.foldl (· ++ pathMentions ·) #[]
  else e.getArgs.foldl (· ++ pathMentions ·) #[]

/-- The segments of the paths in `t`, a type or a bound of a range
pattern. -/
partial def pathNamesIn (t : Syntax) : Array Name :=
  if t.isOfKind ``Lang.fren_path then (pathSegs t).map (·.getId.getRoot)
  else t.getArgs.flatMap pathNamesIn

/-- The names that `e` writes other than its variables, which no binder of
`e` declares (`lint::closure_names`): the first segment of the function
that each application applies (but for a method's receiver, which is a
variable), and of each path of more than one segment, the type of each
record literal, the variant of each pattern that is applied or written
with `::`, and the segments of each type and each range pattern's bound. -/
partial def itemNames (e : Syntax) : Array Name :=
  let head (p : Syntax) : Array Name := ((pathSegs p)[0]?.map (·.getId.getRoot)).toArray
  if e.isOfKind ``Lang.fren_path then if (pathSegs e).size > 1 then head e else #[]
  else if e.isOfKind ``Lang.appExpr then
    let segs := pathSegs e[0]
    (if segs.size == 1 && !segs[0]!.getId.isAtomic then #[] else head e[0]) ++ e[2].getSepArgs.flatMap itemNames
  else if e.isOfKind ``Lang.recordExpr then head e[0] ++ e[2].getSepArgs.flatMap itemNames
  else if e.isOfKind ``Lang.variantPattern then
    (if e[1].isNone && (pathSegs e[0]).size == 1 then #[] else head e[0]) ++ e[1].getArgs.flatMap itemNames
  else if e.isOfKind ``Lang.pathBound then pathNamesIn e
  -- The type of a quantifier's binders, of a closure's parameter, or of a
  -- definition of a `let` or `where`.
  else if e.isOfKind ``Lang.fren_binder then pathNamesIn e[3]
  else if e.isOfKind ``Lang.fren_closure_param || e.isOfKind ``Lang.fren_let_def || e.isOfKind ``Lang.fren_def then
    pathNamesIn e[1] ++ e.getArgs.flatMap itemNames
  else e.getArgs.flatMap itemNames

/-- The names that the body of the closure `e` has free, but for the
closure's own parameters (`lint::closure_names`): the variables it
mentions (`pathMentions`) and the other names it writes (`itemNames`),
each once, as written. -/
def closureFreeNames (e : Syntax) : Array String :=
  let params := closureNames e
  (((pathMentions e[3]).map (·.getRoot) ++ itemNames e[3]).filter (!params.contains ·)).toList.eraseDups.toArray.map
    Core.nameText

/-- Which of the definitions `defs` of a `let` or `where` clause its body
`body` mentions, directly or through the later ones that it mentions: the
others count for nothing (`Reqs/Lang/Let#meaning`). -/
def usedDefinitions (defs : Array Syntax) (body : Syntax) : Array Bool :=
  (Core.clauseMentions (defs.map fun d => (declaredIdent d[0]).1.getId) (defs.map fun d => pathMentions d[3] false)
    (pathMentions body false) false).2

/-- The variables that the defined output `v` stands for: those its
definition mentions, through other definitions, transitively. -/
partial def defDeps (vars : Array Var) (v : Var) (seen : Array Name := #[]) : Array Var := Id.run do
  let some d := v.defn? | return #[v]
  let mut out := #[]
  for n in (pathMentions d).toList.eraseDups do
    let some u := vars.find? (·.name == n) | continue
    if seen.contains u.name then continue
    out := out ++ defDeps vars u (seen.push v.name)
  return out

/-- The cycle of definitions through `start`, if any, each mentioning the
next. -/
partial def defCycle? (vars : Array Var) (start : Name) (path : Array Name := #[]) : Option (Array Name) :=
  match (vars.find? (·.name == start)).bind (·.defn?) with
  | none => none
  | some d =>
    let path := path.push start
    (pathMentions d).toList.eraseDups.findSome? fun n =>
      if n == path[0]! then some path
      else if path.contains n then none
      else defCycle? vars n path

/-- A reference to procedure variable `n`, if it is one, checking that it may be
mentioned here (`inst::mention`). -/
def varRef? (cx : ExprCtx) (id : Syntax) (n : Name) : TermElabM (Option Term) := do
  let some v := cx.vars.find? (·.name == n) | return none
  -- A defined output mentions what its definition does.
  for u in if cx.unmentioned then #[] else defDeps cx.vars v do
    let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
    let ok := Core.checkMention cx.place u.role earlier u.name
    match ok with
    | .ok () => pure ()
    | .error msg => throwErrorAt id (if u.name == n then msg else Core.throughDefinition n msg).text
  return some (mkIdentFrom id n)

open Lang in
/-- The expression that is the name `n`, a path of one segment. -/
def pathExpr (ref : Syntax) (n : Name) : TermElabM Syntax := do
  let tmpl ← `(fren_expr| x)
  return tmpl.raw.setArg 0 (mkNode ``Lang.fren_path #[mkNullNode #[mkIdentFrom ref n]])

/-- Give an implicit match its fresh, unspellable argument references. -/
def explicitLambdaMatch (e : Syntax) (names : Array Syntax) : TermElabM Syntax := do
  let values ← names.mapM fun n => do
    let value ← pathExpr n n.getId
    -- The implicit scrutinee stands at its written parameter or closure.
    let info := match n.getPos?, n.getTailPos? with
      | some start, some stop => SourceInfo.synthetic start stop true
      | _, _ => SourceInfo.none
    return Syntax.setInfo info value
  let arms := e[2].getSepArgs
  for arm in arms do
    unless arm[0].getSepArgs.size == names.size do
      throwErrorAt arm (Core.arityMsg `match names.size arm[0].getSepArgs.size "pattern").text
  if names.size == 1 then
    return mkNode ``Lang.matchExpr #[e[0], values[0]!, mkAtom "{",
      Syntax.mkSep (arms.map fun a => (mkNode ``Lang.fren_arm ((a.setArg 0 a[0].getSepArgs[0]!).getArgs)).raw) (mkAtom ","), mkAtom "}"]
  return mkNode ``Lang.matchManyExpr #[e[0], values[0]!, mkAtom ",",
    Syntax.mkSep (values.extract 1 values.size) (mkAtom ","), mkAtom "{", e[2], mkAtom "}"]

open Lang in
/-- Expand unnamed function parameters before normal function elaboration. -/
def anonymousMatchFunction (stx : Syntax) : TermElabM Syntax := do
  if !stx[8].isNone && (unparen stx[8][1]).isOfKind ``Lang.lambdaMatchExpr &&
      stx[5].getSepArgs.all (fun p => p[1].isNone && !(typePath? p[0]).any (fun q => (pathSegs q).size == 1 && (pathSegs q)[0]!.getId.toString.endsWith "?")) then do
    let ps := stx[5].getSepArgs
    let names := ps.mapIdx fun j p => mkIdentFrom p (Name.mkSimple s!"#match{j}")
    let fnTemplate ← `(command| fn placeholder(x: Int): Int := 0)
    let template := fnTemplate.raw[5].getSepArgs[0]!
    let params := ps.zip names |>.map fun (p, n) =>
      let path := mkNode ``Lang.fren_path #[mkNullNode #[n]]
      let named := template.setArg 0 ((template[0]).setArg 0 path)
      named.setArg 1 (mkNullNode #[mkAtom ":", p[0]])
    let body ← explicitLambdaMatch (unparen stx[8][1]) names
    pure ((stx.setArg 5 (Syntax.mkSep params (mkAtom ","))).setArg 8 (stx[8].setArg 1 body))
  else pure stx

/-- For `x.m(a)`, an application of a dotted name, the receiver `x` and the
method `m`. Paths are written with `::`, so an applied dotted name is a
method call, as the `fren` command parses it: of a value, or of a variable
read from a call, as in `w.x.len()`. The only root that is not a
receiver is a call without variables (unless a binder shadows it).

This does not resolve the root or the method. Elaborating the receiver
reports a root that is not a value, such as a misspelled name or an
enumeration, and elaborating the call reports a method that its type does
not have. -/
def methodApp? (cx : ExprCtx) (e : Syntax) : Option (Name × Name) := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  let n := segs[0]!.getId
  guard (!n.isAtomic && ((cx.binder? n.getRoot).isSome || !cx.insts.contains n.getRoot
    || cx.vars.any (·.name.getRoot == n.getRoot)))
  return (n.getPrefix, Name.mkSimple n.getString!)

/-- For `c(a, b)`, an application of a cardinality operator
(`Reqs/Lang/Expressions#cardinality`), the operator. A variable named like
it shadows it, which applying the variable reports. -/
def cardinalityApp? (e : Syntax) : Option Core.Cardinality := do
  guard (e.isOfKind ``Lang.appExpr)
  let segs := pathSegs e[0]
  guard (segs.size == 1)
  Core.builtinFunction? segs[0]!.getId

/-- What the identifier `x` of one segment, not applied, is in a pattern
(`lang::pattern_name`). -/
def patternName (cx : ExprCtx) (x : Syntax) : TermElabM Core.PatternName := do
  let (n, bang) := Core.declaredName x.getId
  return Core.patternName (n == `true || n == `false) bang ((← getState).table.namesVariant? cx.modName n)

/-- The binders of the pattern `top` of `match` or `is`, in preorder. -/
def topBinders (cx : ExprCtx) (top : Syntax) : TermElabM (Array Syntax) :=
  (topNames top).filterM fun x => return (← patternName cx x) == .binder

/-- Whether a pattern test of the chain of `and` `c` binds names. -/
def chainBinds (cx : ExprCtx) (c : Syntax) : TermElabM Bool :=
  (chainTests c).anyM fun (_, p) => return !(← topBinders cx p).isEmpty

/-- The names that the pattern tests of the chain of `and` `c` bind, which
what follows the chain sees (`lang::test_scope`). -/
def chainBinders (cx : ExprCtx) (c : Syntax) : TermElabM (List String) := do
  let bs ← (chainTests c).mapM fun (_, p) => topBinders cx p
  return bs.toList.flatMap fun xs => xs.toList.map fun x => (Core.declaredName x.getId).1.toString


end Fren
