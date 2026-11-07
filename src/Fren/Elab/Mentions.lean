-- keep-sorted start
import Fren.Elab.Names
-- keep-sorted end

/-! # Hosted elaboration: mentions -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The shape of `e`, for what it mentions (`lang::mentions`), where `bs`
are the binders of `e` around the subexpression, each with the shape of its
scrutinee. -/
private partial def shapeOfM (cx : ExprCtx) (e : Syntax) (bs : Array (Name × Core.MentionShape) := #[]) : StateT (NameMap Core.MentionShape) TermElabM Core.MentionShape := do
  let parts (k : Core.MentionKind) (es : Array Syntax) : StateT (NameMap Core.MentionShape) TermElabM Core.MentionShape :=
    return .node k (← es.toList.mapM (shapeOfM cx · bs))
  if let some (recv, _) := methodApp? cx e then
    return ← parts .method (#[(← pathExpr e recv)[0]] ++ e[2].getSepArgs)
  -- A cardinality operator has a fixed meaning, as an operator does.
  if (cardinalityApp? e).isSome then return ← parts .compound e[2].getSepArgs
  if e.isOfKind ``Lang.appExpr then
    let k : Core.MentionKind ← if ← isConstruction cx e[0] then pure .construction
      else if (← definedFn? cx e[0]).isSome then pure .defined
      else pure (.uninterpreted ("::".intercalate ((pathSegs e[0]).toList.map (·.getId.toString (escape := false)))))
    parts k e[2].getSepArgs
  else if e.isOfKind ``Lang.recordExpr then
    -- A field without `:= e` is `x := x`.
    parts .construction (← e[2].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1])
  else if e.isOfKind ``Lang.updateExpr then
    -- The updated value, and the new values.
    parts .compound (#[e[1]] ++ (← e[3].getSepArgs.mapM fun b =>
      if b[1].isNone then return (← pathExpr b[0] b[0].getId)[0] else pure b[1][1]))
  else if isMatchLike e || e.isOfKind ``Lang.lambdaMatchExpr then
    let shapes ← (matchScrutinees e).mapM (shapeOfM cx · bs)
    let arms ← (matchSourceArms e).toList.flatMapM fun arm => do
      let mut new := #[]
      for p in matchPatterns e arm, j in [0:(matchPatterns e arm).size] do
        new := new ++ (← topBinders cx p).map fun b => ((declaredIdent b).1.getId,
          Core.MentionShape.node .binder (shapes[j]?.toList))
      ((if arm[1].isNone then [] else [arm[1][1]]) ++ [arm[3]]).mapM (shapeOfM cx · (bs ++ new))
    return .node .compound (shapes.toList ++ arms)
  else if e.isOfKind ``Lang.isExpr then parts .compound #[e[0]]
  else if e.isOfKind ``Lang.letExpr then
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← e[1].getSepArgs.foldlM (init := bs) fun bs d => do
      return bs.push ((declaredIdent d[0]).1.getId, .node .definition [(← shapeOfM cx d[3] bs).summary])
    return .node .compound [← shapeOfM cx e[3] bs]
  else if e.isOfKind ``Lang.quantExpr then
    let new := quantNames e |>.map fun n => (n, Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOfM cx e[3] (bs ++ new)]
  -- A closure's parameter varies, as a variable does
  -- (`Reqs/Lang/HigherOrder#arguments`).
  else if e.isOfKind ``Lang.closureExpr then
    let new := closureNames e |>.map fun n => (n, Core.MentionShape.leaf (.variable (n.toString (escape := false))))
    return .node .compound [← shapeOfM cx e[3] (bs ++ new)]
  else if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size != 1 then return .leaf .constant
    let n := segs[0]!.getId
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf (if b.unbounded then .variable (n.toString (escape := false)) else .bound)
      return .node .binder [← shapeOfM (cx.at b) sc]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      if let some cached := (← get).find? n.getRoot then return cached
      let summary := (← shapeOfM { cx with binders := #[] } d).summary
      let shaped := Core.MentionShape.node .definition [summary]
      modify fun cache => cache.insert n.getRoot shaped
      return shaped
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable (n.toString (escape := false)) else .constant)
  else if e.isAtom || e.isIdent then return .leaf .literal
  -- The names that the pattern tests of a condition, or of the left
  -- operand of `and`, bind, in what sees them (`lang::test_scope`).
  else if let some (c, d, others) := testScoped? e then
    let new ← (chainTests c).flatMapM fun (sc, p) => do
      let s ← shapeOfM cx sc bs
      return (← topBinders cx p).map fun b => ((declaredIdent b).1.getId, Core.MentionShape.node .binder [s])
    return .node .compound ([← shapeOfM cx c bs, ← shapeOfM cx d (bs ++ new)] ++ (← others.toList.mapM (shapeOfM cx · bs)))
  else parts .compound e.getArgs

/-- Each definition's support is computed once in this lexical context.
`Core.MentionShape.summary` preserves its mentions while keeping repeated
local references compact, as in the standalone front end. -/
def shapeOf (cx : ExprCtx) (e : Syntax) (bs : Array (Name × Core.MentionShape) := #[]) : TermElabM Core.MentionShape :=
  (shapeOfM cx e bs).run' {}

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return (← shapeOf cx e).mentions

/-- The names of the variables and uninterpreted functions that `e`
mentions (`lang::mentions`). -/
def mentionedNames (cx : ExprCtx) (e : Syntax) : TermElabM (List Core.Mention) := return (← shapeOf cx e).mentioned

/-- The applications of uninterpreted functions in `e`. -/
partial def applications (cx : ExprCtx) (e : Syntax) : TermElabM (Array Syntax) := do
  let inner ← e.getArgs.foldlM (init := #[]) fun acc a => return acc ++ (← applications cx a)
  if e.isOfKind ``Lang.appExpr && (methodApp? cx e).isNone && (cardinalityApp? e).isNone then
    if !(← isConstruction cx e[0]) && (← definedFn? cx e[0]).isNone then return #[e] ++ inner
  return inner

/-- Whether the Lean type of a Fren type has infinitely many values
(`Reqs/Lang/Decidability#outputs`): it is not finite (`lang::type_facts`),
so an abstract type counts. -/
def infiniteType (ty : Expr) : TermElabM Bool := return !(exprFacts (← getState) ty).finite

/-- Whether `e` mentions an output of an infinite type, directly, through a
definition or through a binder. -/
partial def mentionsInfiniteOutput (cx : ExprCtx) (e : Syntax) : TermElabM Bool := do
  for n in pathMentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsInfiniteOutput (cx.at b) sc then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    for u in defDeps cx.vars v do
      if u.role == .output && (← infiniteType u.type) then return true
  return false

/-- Whether `e` is a constant: it mentions no variable or uninterpreted
function (`lang::mentions`). -/
def isConstant (cx : ExprCtx) (e : Syntax) : TermElabM Bool := return !(← mentionsAny cx e)

/-- The definition of `e`, if it names a defined output. -/
partial def definitionOf? (cx : ExprCtx) (e : Syntax) : Option Syntax :=
  if e.isOfKind ``Lang.fren_path then
    let segs := pathSegs e
    if segs.size == 1 then (cx.vars.find? (·.name == segs[0]!.getId)).bind (·.defn?) else none
  else if e.getNumArgs == 1 then definitionOf? cx e[0]
  else if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then definitionOf? cx e[1]
  else none

/-- Whether `e` is a variable, a field read from one, or an application of
an uninterpreted function, which is as unknown as a variable. -/
partial def isVariable (cx : ExprCtx) (e : Syntax) : Bool :=
  if e.isOfKind ``Lang.fren_path then (pathSegs e).size == 1
  -- A path, as an expression.
  else if e.getNumArgs == 1 then isVariable cx e[0]
  else if e.isOfKind ``Lang.fieldExpr then isVariable cx e[0]
  else if e.isOfKind ``Lang.appExpr then (methodApp? cx e).isNone
  else e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" && isVariable cx e[1]

/-- Where `e` is written, without its parentheses: how the memberships of
quantifiers over elements are found again (`ExprCtx.elemGuards`). -/
def elemKey (e : Syntax) : Option String.Pos.Raw × Option String.Pos.Raw :=
  let e := unparen e
  (e.getPos?, e.getTailPos?)

/-- Whether the names `ns`, as mentioned, are an output that is not
defined, or mention one, through a definition or through a binder: one
that the realizability check quantifies over, as the `fren` command's
`mentionsOutput`. -/
partial def mentionsOutputOf (cx : ExprCtx) (ns : Array Name) : TermElabM Bool := do
  for n in ns do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsOutputOf (cx.at b) (pathMentions sc) then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && u.defn?.isNone then return true
  return false

/-- `mentionsOutputOf` of the names that `e` mentions. -/
def mentionsOutput (cx : ExprCtx) (e : Syntax) : TermElabM Bool := mentionsOutputOf cx (pathMentions e)

/-- Inherit a function or constant's opt-out (`lang::inherited_core`). -/
def noteItemCore (path : Name) : TermElabM Unit := do
  let dependency := !(← getState).outsideCoreItems.contains path
  modifyLocal fun l => { l with outsideCore := !(Core.inheritCore (!l.outsideCore) dependency) }

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (ref : Syntax) (c : Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Syntax) (ground : Bool := false) (finiteRange : Bool := true) (literalOperand : Bool := false) :
    TermElabM Unit := do
  if cx.unmentioned then return
  let infinite ← operands.anyM (mentionsInfiniteOutput cx)
  unless Core.inCore c constantArgs comparable infinite ground (finiteRange := finiteRange)
      (literalOperand := literalOperand) do
    modifyLocal fun l => { l with outsideCore := true }
    recordLint .undecidable ref (Core.undecidableMsg c infinite)

/-- Reports `undecidable` if the method `m` of the relation type `ty`, with
`operands`, ranges over a type that is not finite
(`Reqs/Lang/Decidability#relations`). -/
def checkRelational (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (operands : Array Syntax) :
    TermElabM Unit := do
  if cx.unmentioned then return
  let some (a, b) := relTypes? ty | return
  let tys ← match Core.Method.ofName? m with
    | some .inverse => pure #[a, b]
    | some .closure | some .image | some .range => pure #[a]
    | some .domain => pure #[b]
    | _ => return
  let finite ← tys.allM fun t => return !(← infiniteType t)
  modifyLocal fun l => { l with relationalUsed := true }
  checkCore cx ref .relational true true operands (← operands.allM (isConstant cx ·)) finite

/-- Records a `card`, of the receiver `recv` of Lean type `ty`: in a procedure
that applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (ref : Syntax) (ty : Expr) (m : String) (recv : Syntax) : TermElabM Unit := do
  if cx.unmentioned then return
  if m == "card" && ty.isAppOfArity ``Fren.FinSet 1 && !(← isConstant cx recv) then
    modifyLocal fun l => { l with countRefs := l.countRefs.push ref }

/-- Reports `undecidable` at each count of the current procedure, if it also
applies a relational operator; gives whether it does and whether it counts. -/
def checkCounts [Monad m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m] : m (Bool × Bool) := do
  let l ← getLocal
  if l.relationalUsed then
    for r in l.countRefs do
      modifyLocal fun l => { l with outsideCore := true }
      recordLint .undecidable r (Core.undecidableMsg .relationalCard false)
  return (l.relationalUsed, !l.countRefs.isEmpty)

/-- Records what a call of `c`, written at `ref`, brings to the current
procedure's mix of relational operators and counting. -/
def noteCounts [Monad m] [MonadEnv m] (c : CompInfo) (ref : Syntax) : m Unit :=
  modifyLocal fun l => { l with relationalUsed := l.relationalUsed || c.relational, guardedUsed := l.guardedUsed || c.guarded
                                countRefs := if c.counts then l.countRefs.push ref else l.countRefs }

/-- Reads the field `f` of the term `t` of Lean type `ty`, which is the dotted
name `id` up to its `k`th component, checking the decidable core. -/
def readPathField (cx : ExprCtx) (id : Syntax) (parts : List Name) (k : Nat) (t : Term) (ty : Expr) (f : Name) :
    TermElabM (Term × Expr) := do
  let recv := (parts.take k).foldl (· ++ ·) .anonymous
  if ty.isConstOf ``String then checkCore cx id .stringAtom true true #[← pathExpr id recv]
  let r ← readField id t ty f
  if (relTypes? ty).isSome then checkRelational cx id ty f.toString #[← pathExpr id recv]
  if let (true, some m) := (ty.isAppOfArity ``Fren.Seq 1, Core.Method.ofName? f.toString) then
    let p ← pathExpr id recv
    checkCore cx id m.seqConstruct true true #[p] (← isConstant cx p)
  checkRelationalCard cx id ty f.toString (← pathExpr id recv)
  return r

/-- `(e).a.b` or `(e).a.m(x)`, whose name after the `.` is dotted, as the
reads one after another, `((e).a).b` or `((e).a).m(x)`, as the `fren`
command's parser reads it, each name at its own place in the source, so
that an error underlines only the name it is about; `none` for any other
expression. -/
def splitDotted? (e : Syntax) : Option Syntax := do
  guard (e.isOfKind ``Lang.fieldExpr || e.isOfKind ``Lang.methodExpr)
  guard e[2].isIdent
  let n := e[2].getId
  guard !n.isAtomic
  let start := (e[2].getPos? (canonicalOnly := false)).getD 0
  -- Each name, with its place: after the names and dots before it.
  let (_, ids) := n.components.foldl (init := (start, #[])) fun (p, ids) c =>
    let stop : String.Pos.Raw := ⟨p.byteIdx + c.toString.utf8ByteSize⟩
    (⟨stop.byteIdx + 1⟩, ids.push (mkIdentFrom (Syntax.atom (.synthetic p stop) "") c))
  let recv := ids.pop.foldl (init := e[0]) fun (r : Syntax) id => Syntax.node .none ``Lang.fieldExpr #[r, e[1], id]
  return (e.setArg 0 recv).setArg 2 ids.back!

/-- `e.f`, a field read or a method without arguments, of the term `t` for
`e`, checking the decidable core. -/
def fieldTerm (cx : ExprCtx) (e : Syntax) (t : Term) : TermElabM Term := do
  let ty ← typeOf t
  if ty.isConstOf ``String then checkCore cx e .stringAtom true true #[e[0]]
  let f := fieldName e[2]
  -- For `redundant_newtype_roundtrip`.
  if let (some n, true) := ((← getState).newtypeOf? ty, cx.noteIndexes && f == Name.mkSimple "0") then
    modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .unwraps n.path.toString) }
  let r ← readField e[2] t ty f
  if let (true, some m) := (ty.isAppOfArity ``Fren.Seq 1, Core.Method.ofName? f.toString) then
    checkCore cx e m.seqConstruct true true #[e[0]] (← isConstant cx e[0])
  checkRelational cx e ty f.toString #[e[0]]
  checkRelationalCard cx e ty f.toString e[0]
  return r.1


end Fren
