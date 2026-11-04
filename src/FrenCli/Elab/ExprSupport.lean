-- keep-sorted start
import FrenCli.Elab.Model
import FrenCore.SetCard
-- keep-sorted end

/-!
# Expression helpers for `.fren` elaboration

Provides the expression context, type and pattern helpers, and diagnostic
helpers shared by expression and item elaboration.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

/-! ## Expressions -/

structure ExprCtx where
  vars : Array CVar
  /-- The procedure's calls, in order. -/
  insts : Array Name := #[]
  place : Place
  /-- For a binding, the index of its call. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array CBinder := #[]
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a defined function's body, if it may recurse
  (`lang::structural_recursion`): its parameters' names, its type, and its
  symbol. -/
  selfRec? : Option (Array Name × Fren.Core.FnTy × String) := none
  /-- In a higher-order function's body or contract, its function
  parameters: each one's name, type and symbol (`Reqs/Lang/HigherOrder#function-parameters`). -/
  fnParams : Array (Name × Fren.Core.FnTy × String) := #[]
  /-- In a closure's body, which applies no uninterpreted function. -/
  inClosure : Bool := false
  /-- In a clause of a function's contract: the function, whether the
  clause is a postcondition, and the parameters (`lang::contract_application`). -/
  contract? : Option (Name × Bool × Array Name) := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- The type this expression must have, which gives `{}` its type. -/
  expected? : Option Ty := none
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array String := #[]
  /-- Whether to record the indexes and tables of this expression for their
  checks, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, or of `and`, whose chain
  `membership_chain` looks at from its top: that operator, or `""`. -/
  chain : String := ""
  /-- The expression this one is part of, if any: where a `match` is, for
  the match lints. -/
  parent? : Option Expr := none
  /-- This expression is the `else` branch of an `if`, whose chain
  `if_chain_match` looks at from its top. -/
  inElse : Bool := false
  /-- In a definition of a `let` or `where`, the names of it and of the
  later definitions of its clause that hide nothing, each with whether it
  is its own: a mention of one is used before its definition
  (`lang::definition_order`). -/
  pending : Array (Name × Bool) := #[]
  /-- In a definition of a `let` or `where` that nothing mentions, which
  counts for nothing: what it may mention, linear arithmetic and the
  decidable core are not checked in it (`Reqs/Lang/Let#meaning`). -/
  unmentioned : Bool := false
  /-- What the chain of `and` that this expression is an operand of, or is,
  is a part of, for its pattern tests (`lang::test_scope`). Only `and` and
  `is` read it, and only their operands see it. -/
  testContext : Fren.Core.TestContext := .standalone
  /-- For an operand of a chain of `and`, its position in the chain and the
  chain's number of operands. -/
  testAt? : Option (Nat × Nat) := none
  /-- The members' expressions of the guards of the quantifiers over
  elements around this expression, by span (`State.elemMembers`). -/
  elemGuards : Array Span := #[]
  /-- Within the body of a quantifier over elements: whether it is a
  `forall`; and the quantifiers that are directly its body, or the body
  of one of those, by span (`Fren.Core.ElementNesting`). -/
  elemKind? : Option Bool := none
  elemDirect : Array Span := #[]
  /-- The bound names of the quantifiers over elements, of the same kind,
  that this expression is directly the body of, which its quantifier may
  mention (`Fren.Core.ElementVerdict.mentionsBound`). -/
  elemChain : Array Name := #[]

/-- What the binder `b` is, for a declaration that hides it (`Fren.Core.bindingLocals`). -/
def CBinder.what (b : CBinder) : Name × Fren.Core.BindingKind :=
  (b.name, if b.scrutinee.isNone then .boundName else if b.isDef then .definition else .patternBinder)

/-- The binder named `n` in scope, if any. -/
def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option CBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : CBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name) ++ cx.fnParams.map (·.1)

/-- The function parameter named `n`, with its type and symbol, if no
binder or variable hides it (`Reqs/Lang/HigherOrder#function-parameters`). -/
def ExprCtx.fnParam? (cx : ExprCtx) (n : Name) : Option (Fren.Core.FnTy × String) :=
  if (cx.binder? n).isSome || cx.vars.any (·.name == n) then none
  else (cx.fnParams.find? (·.1 == n)).map fun (_, t, sym) => (t, sym)

/-- The single name that the expression `a` is, if it is one. -/
def soleName? : Expr → Option Name
  | .path _ #[x] => some (identName x.name)
  | _ => none

/-- In a defined function's body that may recurse, where the expression `a`
comes from (`lang::structural_recursion`): the position of the parameter
that it is, or that it is bound from a payload of, with whether it is a
payload. -/
def ExprCtx.recOrigin? (cx : ExprCtx) (a : Expr) : Option (Nat × Bool) := do
  let (ps, _, _) ← cx.selfRec?
  let n ← soleName? a
  match cx.binder? n with
  | some b => return (← b.payloadOf?, true)
  | none =>
    guard (cx.vars.any (·.name == n))
    return (← ps.idxOf? n, false)

/-- Where the argument `a` at position `i` of a recursive application comes
from, relative to the parameter there (`lang::structural_recursion`). -/
def ExprCtx.recArg (cx : ExprCtx) (a : Expr) (i : Nat) : Fren.Core.RecArg :=
  match cx.recOrigin? a with
  | some (j, true) => if j == i then .payload else .name
  | some (j, false) => if j == i then .itself else .name
  | none => if (soleName? a).isSome then .name else .expr


/-- The constant that `segs` names, without recording its use. -/
def constPath? (cx : ExprCtx) (segs : Array Ident) : M (Option Name) := do
  let st ← get
  let .ok (.item { kind := .constItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return none
  return some path

/-- The value of `e`, if it is an integer constant expression: integer
literals and constants whose values are, combined by `+`, `-`, `*`, `div`,
`mod`, `abs`, `min` and `max` (`Reqs/Lang/Expressions#division-and-remainder`). -/
partial def intConstValue? (cx : ExprCtx) (e : Expr) : M (Option Int) := do
  match e with
  | .num _ v => return some v
  | .neg _ a => return (← intConstValue? cx a).map (- ·)
  | .bin _ op a b =>
    let some x ← intConstValue? cx a | return none
    let some y ← intConstValue? cx b | return none
    return Fren.Core.intConstOp? op x y
  | .path _ segs =>
    -- A constant, then the methods without arguments applied to it.
    let parts := if segs.size == 1 then segs[0]!.name.splitOn "." else [""]
    let root := if segs.size == 1 then #[{ segs[0]! with name := parts.head! }] else segs
    if segs.size > 1 && segs.any (·.name.contains '.') then return none
    if root.size == 1 && (cx.vars.any (·.name.getRoot == Name.mkSimple parts.head!) || (cx.binder? (Name.mkSimple parts.head!)).isSome) then
      return none
    let some path ← constPath? cx root | return none
    let some v := (← get).constInts.find? path | return none
    return parts.tail.foldlM (fun x m => Fren.Core.intConstMethod? m x []) v
  | .method _ r m args =>
    let some x ← intConstValue? cx r | return none
    let some ys := (← args.toList.mapM (intConstValue? cx)).mapM id | return none
    return Fren.Core.intConstMethod? m.name x ys
  | .field _ r f =>
    let some x ← intConstValue? cx r | return none
    return Fren.Core.intConstMethod? f.name x []
  | _ => return none

/-- The form of the divisor `k` (`lang::divisor`), without its `-`: its form,
its value if it is known, and the constant it names, if any. -/
partial def divisorForm (cx : ExprCtx) (k : Expr) : M (Fren.Core.DivisorForm × Int × Name) := do
  match k with
  | .neg _ a => let (f, v, c) ← divisorForm cx a; return (f, -v, c)
  | .num _ v => return (.literal, v, .anonymous)
  | .path _ segs =>
    if segs.any (·.name.contains '.') then return (.other, 0, .anonymous)
    if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
      return (.other, 0, .anonymous)
    let some path ← constPath? cx segs | return (.other, 0, .anonymous)
    return match (← get).constInts.find? path with
      | some v => (.knownConstant, v, path)
      | none => (.unknownConstant, 0, path)
  | _ => return (.other, 0, .anonymous)

/-- The newtype that `segs` names, with its underlying type, if it names
one. -/
def newtypeNamed? (cx : ExprCtx) (segs : Array Ident) : M (Option (Name × Ty)) := do
  let st ← get
  let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return none
  return (st.newtypes.find? path).map (path, ·)

/-- Whether `segs` names a variant. -/
def isVariant (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  return st.table.resolvePath st.scope (segNames segs) cx.shadowing matches .ok (.variant ..)

/-- Whether `segs`, applied, builds a variant or a newtype rather than
applying a function. -/
def isConstruction (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  if st.table.resolvePath st.scope (segNames segs) cx.shadowing matches .ok (.variant ..) then return true
  return (← newtypeNamed? cx segs).isSome

/-- Whether `segs`, applied, applies a cardinality operator
(`Reqs/Lang/Expressions#cardinality`). -/
def isCardinality (segs : Array Ident) : Bool :=
  segs.size == 1 && (Fren.Core.builtinFunction? (identName segs[0]!.name)).isSome

/-- Whether `segs`, applied, applies a defined function. -/
def isDefined (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return false
  return st.defs.any (·.1 == path)

/-- What the identifier `x` of one segment, not applied, is in a pattern
(`lang::pattern_name`). -/
def patternName (_cx : ExprCtx) (x : Ident) : M Fren.Core.PatternName := do
  let (d, bang) := declaredIdent x
  return Fren.Core.patternName (d.name == "true" || d.name == "false") bang
    ((← get).table.namesVariant? (← get).scope (Name.mkSimple d.name))

/-- The binders of the pattern `p`, in preorder. -/
def patternBinders (cx : ExprCtx) (p : Pattern) : M (Array Ident) :=
  p.names.filterM fun x => return (← patternName cx x) == .binder

/-- The operands of a chain of `op`, `or` or `and`. -/
partial def chainOperands (op : String) (e : Expr) : Array Expr :=
  match e with
  | .block _ op' members => if op' == op then members.flatMap fun (_, value) => chainOperands op value else #[e]
  | .bin _ op' l r => if op' == op then chainOperands op l ++ chainOperands op r else #[e]
  | _ => #[e]

/-- Whether a pattern test of the chain of `and` `c` binds names. -/
def chainBinds (cx : ExprCtx) (c : Expr) : M Bool :=
  (chainOperands "and" c).anyM fun
    | .is _ _ p => return !(← patternBinders cx p).isEmpty
    | _ => pure false

/-- The names that the pattern tests of the chain of `and` `c` bind, which
what follows the chain sees (`lang::test_scope`). -/
def chainBinders (cx : ExprCtx) (c : Expr) : M (List String) := do
  let bs ← (chainOperands "and" c).mapM fun
    | .is _ _ p => patternBinders cx p
    | _ => pure #[]
  return bs.toList.flatMap fun xs => xs.toList.map (·.name)

/-- The paths of the functions that `e` applies (`unused_assumption`). -/
partial def appliedPaths : Expr → Array (Array Ident)
  | .block _ _ members => members.flatMap (appliedPaths ·.2)
  | .app _ segs args => args.foldl (· ++ appliedPaths ·) #[segs]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => appliedPaths c ++ appliedPaths d
  | .not _ a | .neg _ a | .field _ a _ => appliedPaths a
  | .method _ r _ args => args.foldl (· ++ appliedPaths ·) (appliedPaths r)
  | .set _ es | .seq _ es | .chain _ es _ => es.foldl (· ++ appliedPaths ·) #[]
  | .ite _ c a b => appliedPaths c ++ appliedPaths a ++ appliedPaths b
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .update _ r fs => fs.foldl (init := appliedPaths r) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .match _ s arms _ => (armParts arms).foldl (init := appliedPaths s) fun acc e => acc ++ appliedPaths e
  | .matches _ ss arms _ => (ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).flatMap appliedPaths
  | .is _ s _ => appliedPaths s
  | _ => #[]

/-- The uninterpreted functions that `e` applies, as links of
`unused_assumption` (`Fren.Core.fnLink`). -/
def appliedFns (cx : ExprCtx) (e : Expr) : M (Array Name) := do
  let st ← get
  return (appliedPaths e).filterMap fun segs =>
    match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
    | .ok (.item { kind := .fnItem, path, .. }) => if st.defs.any (·.1 == path) then none else some (Fren.Core.fnLink path)
    | _ => none

/-- The shape of `e`, for what it mentions (`lang::mentions`), where `bs`
are the binders of `e` around the subexpression, each with the shape of its
scrutinee. -/
partial def shapeOf (cx : ExprCtx) (bs : Array (Name × Fren.Core.MentionShape) := #[]) (e : Expr) : M Fren.Core.MentionShape := do
  let parts (k : Fren.Core.MentionKind) (es : List Expr) : M Fren.Core.MentionShape :=
    return .node k (← es.mapM (shapeOf cx bs))
  -- The binders of the pattern tests of the chain of `and` `c`, each with
  -- the shape of its scrutinee.
  let testBinderShapes (c : Expr) : M (Array (Name × Fren.Core.MentionShape)) :=
    (chainOperands "and" c).flatMapM fun
      | .is _ sc p => do
        let s' ← shapeOf cx bs sc
        return (← patternBinders cx p).map fun x => (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder [s'])
      | _ => pure #[]
  match e with
  | .block sp op members => shapeOf cx bs (Expr.lowerBlock sp op members)
  | .path _ segs =>
    if segs.size != 1 then return .leaf .constant
    let n := identName segs[0]!.name
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf (if b.unbounded then .variable (n.toString (escape := false)) else .bound)
      return .node .binder [← shapeOf (cx.at b) #[] sc]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return .node .definition [← shapeOf { cx with binders := #[] } #[] d]
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable (n.toString (escape := false)) else .constant)
  -- The names that the pattern tests of a condition, or of the left
  -- operand of `and`, bind, in what sees them (`lang::test_scope`).
  | .when _ false c d | .bin _ "and" c d => do
    let new ← testBinderShapes c
    return .node .compound [← shapeOf cx bs c, ← shapeOf cx (bs ++ new) d]
  | .ite _ c a b => do
    let new ← testBinderShapes c
    return .node .compound [← shapeOf cx bs c, ← shapeOf cx (bs ++ new) a, ← shapeOf cx bs b]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => parts .compound [c, d]
  | .not _ a | .neg _ a | .field _ a _ => parts .compound [a]
  | .method _ r _ args => parts .method (r :: args.toList)
  | .set _ es | .seq _ es | .chain _ es _ => parts .compound es.toList
  | .quant _ _ binders body =>
    let new := binders.flatMap (·.names) |>.map fun x => (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOf cx (bs ++ new) body]
  -- A closure's parameter varies, as a variable does
  -- (`Reqs/Lang/HigherOrder#arguments`).
  | .closure _ ps body =>
    let new := ps.map fun (x, _) =>
      let n := (declaredIdent x).1.name
      (Name.mkSimple n, Fren.Core.MentionShape.leaf (.variable n))
    return .node .compound [← shapeOf cx (bs ++ new) body]
  | .app _ segs args =>
    -- A cardinality operator has a fixed meaning, as an operator does.
    let k : Fren.Core.MentionKind ← if isCardinality segs then pure .compound
      else if ← isConstruction cx segs then pure .construction
      else if ← isDefined cx segs then pure .defined else pure (.uninterpreted ("::".intercalate (segs.toList.map (·.name))))
    parts k args.toList
  | .record _ _ fs => parts .construction (fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .update _ r fs => parts .compound (r :: fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .match _ s arms _ =>
    let s' ← shapeOf cx bs s
    let arms ← arms.toList.flatMapM fun (p, g?, body) => do
      let new := (← patternBinders cx p).map fun x =>
        (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder [s'])
      (g?.toList ++ [body]).mapM (shapeOf cx (bs ++ new))
    return .node .compound (s' :: arms)
  | .matches _ ss arms _ =>
    let shapes ← ss.mapM (shapeOf cx bs)
    let children ← arms.toList.flatMapM fun (ps, g, body) => do
      let mut new := #[]
      for p in ps, j in [0:ps.size] do
        new := new ++ (← patternBinders cx p).map fun x =>
          (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder (shapes[j]?.toList))
      (g.toList ++ [body]).mapM (shapeOf cx (bs ++ new))
    return .node .compound (shapes.toList ++ children)
  | .is _ s _ => parts .compound [s]
  | .«let» _ defs body _ =>
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← defs.foldlM (init := bs) fun bs (x, _, d) => do
      return bs.push (Name.mkSimple (declaredIdent x).1.name, .node .definition [← shapeOf cx bs d])
    return .node .compound [← shapeOf cx bs body]
  | .table _ rows => parts .compound (tableParts rows).toList
  | .num .. | .bool .. | .str .. => return .leaf .literal

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Expr) : M Bool := return (← shapeOf cx #[] e).mentions

/-- The names that the pattern tests of the chain of `and` `c` would bind,
as written, without their `!`. -/
def testNames (c : Expr) : Array Name :=
  (chainOperands "and" c).flatMap fun
    | .is _ _ p => p.names.map fun b => Name.mkSimple (declaredIdent b).1.name
    | _ => #[]

/-- The names of the variables and uninterpreted functions that `e`
mentions (`lang::mentions`). -/
def mentionedNames (cx : ExprCtx) (e : Expr) : M (List Fren.Core.Mention) := return (← shapeOf cx #[] e).mentioned

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def mentions (e : Expr) (all : Bool := true) : Array Name :=
  let mentions (e : Expr) := mentions e all
  match e with
  | .block _ _ members => members.flatMap fun (_, value) => mentions value
  | .path _ segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      (n.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
    else #[]
  -- In what sees them, the names that the pattern tests of a condition,
  -- or of the left operand of `and`, bind mean them (`lang::test_scope`).
  | .when _ false c d | .bin _ "and" c d => mentions c ++ (mentions d).filter (!(testNames c).contains ·.getRoot)
  | .ite _ c a b => mentions c ++ (mentions a).filter (!(testNames c).contains ·.getRoot) ++ mentions b
  | .when _ _ c d => mentions c ++ mentions d
  | .not _ a | .neg _ a | .field _ a _ => mentions a
  | .method _ r _ args => args.foldl (· ++ mentions ·) (mentions r)
  | .set _ es => es.foldl (· ++ mentions ·) #[]
  | .pair _ a b | .index _ a b => mentions a ++ mentions b
  | .seq _ es | .chain _ es _ => es.foldl (· ++ mentions ·) #[]
  | .bin _ _ a b => mentions a ++ mentions b
  | .app _ _ args => args.foldl (· ++ mentions ·) #[]
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .update _ r fs => fs.foldl (init := mentions r) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .match _ s arms _ => arms.foldl (init := mentions s) fun acc (p, g?, body) =>
    -- In its arm, a binder's name means the binder, not what it shadows.
    let bound := p.names.map fun b => Name.mkSimple (declaredIdent b).1.name
    acc ++ ((g?.map mentions).getD #[] ++ mentions body).filter (!bound.contains ·.getRoot)
  | .matches _ ss arms _ => arms.foldl (init := ss.flatMap mentions) fun acc (ps, g, body) =>
    let bound := ps.flatMap Pattern.names |>.map fun b => Name.mkSimple (declaredIdent b).1.name
    acc ++ (g.toArray.flatMap mentions ++ mentions body).filter (!bound.contains ·.getRoot)
  | .is _ s _ => mentions s
  | .«let» _ defs body _ =>
    (Fren.Core.clauseMentions (defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name)
      (defs.map fun (_, _, d) => mentions d) (mentions body) all).1
  | .quant _ _ binders body =>
    -- In its body, a bound name means the bound name, not what it shadows.
    let bound := binders.flatMap (·.names) |>.map fun x => Name.mkSimple (declaredIdent x).1.name
    (mentions body).filter (!bound.contains ·.getRoot)
  | .closure _ ps body =>
    let bound := ps.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
    (mentions body).filter (!bound.contains ·.getRoot)
  | .table _ rows => (tableParts rows).foldl (· ++ mentions ·) #[]
  | _ => #[]

/-- The first segment of the path `segs`. -/
def pathHead (segs : Array Ident) : Array Name := (segs[0]?.map fun s => (identName s.name).getRoot).toArray

/-- The names of a type's segments, but for those that write its form
(`fn(`, a type's pattern). -/
def typeNames (segs : Array Ident) : Array Name :=
  segs.filterMap fun s =>
    if Fren.Core.isIdStart s.name.front && s.name.all (fun c => Fren.Core.isIdRest c || c == '.') then
      some (identName s.name).getRoot
    else none

/-- The names that the pattern `p` writes other than its binders: the
variant of each pattern that is applied or written with `::`, and the
segments of each range pattern's bound (`lint::closure_names`). -/
partial def patternItemNames : Pattern → Array Name
  | .variant _ path args =>
    (if args.isNone && path.size == 1 then #[] else pathHead path) ++ (args.getD #[]).flatMap patternItemNames
  | .range _ lo hi _ =>
    #[lo, hi].flatMap fun | some (.path _ segs) => segs.map fun s => (identName s.name).getRoot | _ => #[]
  | .or _ alts => alts.flatMap patternItemNames
  | _ => #[]

/-- The names that `e` writes other than its variables, which no binder of
`e` declares (`lint::closure_names`): the first segment of the function
that each application applies, and of each path of more than one
segment, the type of each record literal, the names that its patterns
write other than their binders (`patternItemNames`), and the segments of
each type. -/
partial def itemNames (e : Expr) : Array Name :=
  match e with
  | .block _ _ members => members.flatMap fun (_, value) => itemNames value
  | .path _ segs => if segs.size > 1 then pathHead segs else #[]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => itemNames c ++ itemNames d
  | .ite _ c a b => itemNames c ++ itemNames a ++ itemNames b
  | .not _ a | .neg _ a | .field _ a _ => itemNames a
  | .method _ r _ args => args.foldl (· ++ itemNames ·) (itemNames r)
  | .set _ es | .seq _ es | .chain _ es _ => es.flatMap itemNames
  | .app _ fn args =>
    (if fn.size == 1 && fn[0]!.name.contains '.' then #[] else pathHead fn) ++ args.flatMap itemNames
  | .record _ ty fs => pathHead ty ++ fs.flatMap fun (_, e?) => (e?.map itemNames).getD #[]
  | .update _ r fs => fs.foldl (init := itemNames r) fun acc (_, e?) => acc ++ (e?.map itemNames).getD #[]
  | .match _ s arms _ => arms.foldl (init := itemNames s) fun acc (p, g?, body) =>
    acc ++ patternItemNames p ++ (g?.map itemNames).getD #[] ++ itemNames body
  | .matches _ ss arms _ => arms.foldl (init := ss.flatMap itemNames) fun acc (ps, g, body) =>
    acc ++ ps.flatMap patternItemNames ++ g.toArray.flatMap itemNames ++ itemNames body
  | .is _ s p => itemNames s ++ patternItemNames p
  | .«let» _ defs body _ =>
    defs.foldl (init := itemNames body) fun acc (_, ty?, d) => acc ++ (ty?.map typeNames).getD #[] ++ itemNames d
  | .quant _ _ binders body => binders.foldl (init := itemNames body) fun acc b => acc ++ typeNames b.ty
  | .closure _ ps body => ps.foldl (init := itemNames body) fun acc (_, ty?) => acc ++ (ty?.map typeNames).getD #[]
  | .table _ rows => (tableParts rows).flatMap itemNames
  | .num .. | .bool .. | .str .. => #[]

/-- The names that the closure's body `body` has free, but for the
closure's own parameters `params` (`lint::closure_names`): the variables
it mentions (`mentions`) and the other names it writes (`itemNames`),
each once, as written. -/
def closureFreeNames (params : Array String) (body : Expr) : Array String :=
  (((mentions body).map (·.getRoot) ++ itemNames body).map Fren.Core.nameText).filter (!params.contains ·)
    |>.toList.eraseDups.toArray

/-- The atoms of `e`, a `Bool` expression: its operands through `and`
(`lint::unrelated_binders`). -/
partial def boolAtoms : Expr → Array Expr
  | .bin _ "and" a b => boolAtoms a ++ boolAtoms b
  | e => #[e]

/-- Which of the definitions `defs` of a `let` or `where` clause its body
`body` mentions, directly or through the later ones that it mentions: the
others count for nothing (`Reqs/Lang/Let#meaning`). -/
def usedDefinitions (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) : Array Bool :=
  (Fren.Core.clauseMentions (defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name)
    (defs.map fun (_, _, d) => mentions d false) (mentions body false) false).2

/-- The variables that the defined output `v` stands for: those its
definition mentions, through other definitions, transitively. -/
partial def defDeps (vars : Array CVar) (v : CVar) (seen : Array Name := #[]) : Array CVar := Id.run do
  let some d := v.defn? | return #[v]
  let mut out := #[]
  for n in (mentions d).toList.eraseDups do
    let some u := vars.find? (·.name == n) | continue
    if seen.contains u.name then continue
    out := out ++ defDeps vars u (seen.push v.name)
  return out

/-- The cycle of definitions through `start`, if any, each mentioning the
next. -/
partial def defCycle? (vars : Array CVar) (start : Name) (path : Array Name := #[]) : Option (Array Name) :=
  match (vars.find? (·.name == start)).bind (·.defn?) with
  | none => none
  | some d =>
    let path := path.push start
    (mentions d).toList.eraseDups.findSome? fun n =>
      if n == path[0]! then some path
      else if path.contains n then none
      else defCycle? vars n path

/-- Whether `e` mentions an output of an infinite type, directly, through a
definition or through a binder (`Reqs/Lang/Decidability#outputs`). -/
partial def mentionsInfiniteOutput (cx : ExprCtx) (e : Expr) : M Bool := do
  let st ← get
  for n in mentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsInfiniteOutput (cx.at b) sc then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && st.infinite u.ty then return true
  return false

/-- Whether `e` is a constant: it mentions no variable or uninterpreted
function (`lang::mentions`). -/
def isConstant (cx : ExprCtx) (e : Expr) : M Bool := return !(← mentionsAny cx e)

/-- Whether `e` is a variable, a field read from one, or an application of
an uninterpreted function, which is as unknown as a variable. -/
partial def isVariable : Expr → Bool
  | .path _ segs => segs.size == 1
  | .field _ a _ => isVariable a
  | .app .. => true
  | _ => false

/-- The definition of `e`, if it names a defined output. -/
def definitionOf? (cx : ExprCtx) : Expr → Option Expr
  | .path _ segs => if segs.size == 1 then (cx.vars.find? (·.name == identName segs[0]!.name)).bind (·.defn?) else none
  | _ => none

/-- Whether `e` contains a `++` that is not a constant, itself or in a
defined output's definition (acyclic, so this ends). -/
partial def hasConcat (cx : ExprCtx) (e : Expr) : M Bool := do
  if e matches .bin _ "++" _ _ then
    if !(← isConstant cx e) then return true
  match e with
  | .path .. => match definitionOf? cx e with | some d => hasConcat cx d | none => return false
  | .when _ _ c d | .bin _ _ c d => return (← hasConcat cx c) || (← hasConcat cx d)
  | .not _ a | .neg _ a | .field _ a _ => hasConcat cx a
  | .method _ r _ args => (#[r] ++ args).anyM (hasConcat cx)
  | .set _ es | .app _ _ es => es.anyM (hasConcat cx)
  | .pair _ a b | .index _ a b => return (← hasConcat cx a) || (← hasConcat cx b)
  | .seq _ es | .chain _ es _ => es.anyM (hasConcat cx)
  | .ite _ c a b => return (← hasConcat cx c) || (← hasConcat cx a) || (← hasConcat cx b)
  | .record _ _ fs => fs.anyM fun (_, e?) => match e? with | some e => hasConcat cx e | none => pure false
  | .update _ r fs =>
    return (← hasConcat cx r) || (← fs.anyM fun (_, e?) => match e? with | some e => hasConcat cx e | none => pure false)
  | .match _ s arms _ => return (← hasConcat cx s) || (← (armParts arms).anyM (hasConcat cx))
  | .matches _ ss arms _ => return (← ss.anyM (hasConcat cx)) || (← (arms.flatMap fun (_, g, b) => g.toArray.push b).anyM (hasConcat cx))
  | .is _ s _ => hasConcat cx s
  | .«let» _ defs body _ => return (← defs.anyM (hasConcat cx ·.2.2)) || (← hasConcat cx body)
  | .quant _ _ _ b => hasConcat cx b
  | .table _ rows => (tableParts rows).anyM (hasConcat cx)
  | _ => return false

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (span : Span) (c : Fren.Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Expr) (ground : Bool := false) (infiniteElems : Bool := true) (finiteRange : Bool := true)
    (literalOperand : Bool := false) : M Unit := do
  if cx.unmentioned then return
  let infinite ← operands.anyM (mentionsInfiniteOutput cx)
  unless Fren.Core.inCore c constantArgs comparable infinite ground infiniteElems finiteRange literalOperand do
    modify fun s => { s with outsideCore := true }
    lint .undecidable span (Fren.Core.undecidableMsg c infinite)

/-- Whether `e` mentions an output that is not defined, directly, through a
definition or through a binder: one that the realizability check
quantifies over (`lang::ElementBinder`). -/
partial def mentionsOutput (cx : ExprCtx) (e : Expr) : M Bool := do
  for n in mentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsOutput (cx.at b) sc then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && u.defn?.isNone then return true
  return false

/-- Whether the body of the defined function `path` has a quantifier over a
type that is not listed, directly or through another defined function that
it applies, to a depth of `fuel`, beyond which it is taken to have one: its
`define-fun` has the solver's quantifier, or a quantifier over elements
(`Fren.Core.ElementUse.quantifiedArgument`). -/
partial def fnQuantifies (st : State) (fuel : Nat) (path : Name) : Bool :=
  if fuel == 0 then true else
  let body? := ((st.genericFns.find? path).map (·.body)).orElse fun _ =>
    (st.defs.find? (·.1 == path)).map (·.2.2.2)
  match body? with
  | none => false
  | some body =>
    let quantified := ["(forall (", "(exists (", "(fren.forall (", "(fren.exists ("].any fun h => (body.splitOn h).length > 1
    quantified || st.defs.any fun (p, _, _, _) =>
      p != path && (body.splitOn ((st.instSyms.find? p).getD (itemSym p))).length > 1 && fnQuantifies st (fuel - 1) p

/-- How an application of `segs` uses an argument that mentions a bound
name (`elementUses`): a defined function with a parameter that has a
sequence within it, or an uninterpreted function whose applications bring
facts. -/
def appElementUse (cx : ExprCtx) (segs : Array Ident) : M (Array Fren.Core.ElementUse) := do
  let st ← get
  let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return #[]
  let declared : Option (Array Ty) := match st.genericFns.find? path, st.defs.find? (·.1 == path) with
    | some g, _ => some g.declared
    | none, some d => some (d.2.1.map (·.2))
    | none, none => none
  if let some ps := declared then
    if ps.any (Fren.Core.hasSeqWithin st.shapeOf 8) then return #[.seqArgument]
    return if fnQuantifies st 8 path then #[.quantifiedArgument] else #[]
  let facts : Bool := match st.funs.find? (·.1 == path) with
    | some f => f.2.2 == .nat || (st.contracts.find? path).isSome || st.funFacts.contains (itemSym path)
    | none => false
  return cond facts #[.factArgument] #[]

/-- How the expression `e`, within the body of a quantifier, uses the bound
name `x`, where `inner` are the names that the body declares, which may
stand for `x` (`Fren.Core.ElementUse`): as an index, or an `update`'s
position, of a sequence that is not a constant; in an argument of a
defined function with a parameter that has a sequence within it, or of an
uninterpreted function whose applications bring facts; or in the members of
a quantifier's guard. -/
partial def elementUses (cx : ExprCtx) (x : Name) (inner : Array Name) (e : Expr) : M (Array Fren.Core.ElementUse) := do
  let names (e : Expr) : Bool := (mentions e).any fun n => n.getRoot == x || inner.contains n.getRoot
  let own : Array Fren.Core.ElementUse ← match e with
    | .index _ r i => pure <| if names i && !(← isConstant cx r) then #[.index] else #[]
    | .method _ r m args =>
      let positions := match m.name with | "update" | "at" => 1 | "slice" => 2 | _ => 0
      pure <| if (args.extract 0 positions).any names && !(← isConstant cx r) then #[.index] else #[]
    | .app _ segs args => if args.any names then appElementUse cx segs else pure #[]
    | .quant _ all _ b =>
      let receivers := (guardConjuncts all b).filterMap fun
        | some (_, .mem, r) => some r
        | _ => none
      pure <| if receivers.any names then #[.receiver] else #[]
    | _ => pure #[]
  return own ++ (← e.children.flatMapM (elementUses cx x inner))

/-- The quantifier that is directly the body `e` of a quantifier over
elements, a `forall` if `all`, if any, by its span: under a `forall`'s
`when`s, or as the last conjunct of an `exists`'s body, of the same kind
(`Fren.Core.ElementNesting`). -/
partial def elementSpine (all : Bool) : Expr → Option Span
  | .when _ false _ d => if all then elementSpine all d else none
  | .bin _ "and" _ b => if all then none else elementSpine all b
  | .quant sp a _ _ => if a == all then some sp else none
  | _ => none

/-- The expressions directly within `e`, in order. -/
def Expr.operands : Expr → Array Expr
  | .block _ _ members => members.map (·.2)
  | .when _ _ c d => #[c, d]
  | .ite _ c a b => #[c, a, b]
  | .bin _ _ a b | .pair _ a b | .index _ a b => #[a, b]
  | .not _ a | .neg _ a | .field _ a _ => #[a]
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args
  | .method _ r _ args => #[r] ++ args
  | .record _ _ fs => fs.filterMap (·.2)
  | .update _ r fs => #[r] ++ fs.filterMap (·.2)
  | .match _ s arms _ => #[s] ++ armParts arms
  | .matches _ ss arms _ => ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)
  | .quant _ _ _ b | .closure _ _ b => #[b]
  | .is _ s _ => #[s]
  | .«let» _ defs body _ => defs.map (·.2.2) |>.push body
  | .table _ rows => tableParts rows
  | .num .. | .bool .. | .path .. | .str .. => #[]

/-- The names of one segment that `e` applies as functions, anywhere within
it: a function parameter is mentioned by applying it. -/
partial def Expr.appliedNames (e : Expr) : Array Name :=
  (match e with | .app _ #[s] _ => #[identName s.name] | _ => #[]) ++ e.operands.flatMap (·.appliedNames)

/-- The names that `e` declares, without their `!`: those of its `let`s and
`where` clauses, its bound names and its patterns' binders
(`Fren.Core.ForallCx`). -/
partial def Expr.declaredNames (e : Expr) : Array String :=
  let own := match e with
    | .«let» _ defs _ _ => defs.map fun (x, _, _) => (declaredIdent x).1.name
    | .quant _ _ bs _ => bs.flatMap (·.names) |>.map fun x => (declaredIdent x).1.name
    | .matches _ _ arms _ => arms.flatMap fun (ps, _, _) => ps.flatMap Pattern.names |>.map fun x => (declaredIdent x).1.name
    | .closure _ ps _ => ps.map fun (x, _) => (declaredIdent x).1.name
    | .match _ _ arms _ => arms.flatMap fun (p, _, _) => p.names.map fun x => (declaredIdent x).1.name
    | .is _ _ p => p.names.map fun x => (declaredIdent x).1.name
    | _ => #[]
  own ++ e.operands.flatMap (·.declaredNames)

/-- The integer literals of a pattern: its own, its bounds' and those of
its parts. -/
partial def Pattern.integerSpans : Pattern → Array Span
  | .num s _ => #[s]
  | .range _ lo hi _ => (lo.toArray ++ hi.toArray).filterMap fun | .num s _ => some s | _ => none
  | .variant _ _ (some args) => args.flatMap (·.integerSpans)
  | .or _ alts => alts.flatMap (·.integerSpans)
  | _ => #[]

/-- The integer literals of `e` and of its patterns, which
`zero_prefixed_literal` reads. -/
partial def Expr.integerSpans (e : Expr) : Array Span :=
  let own := match e with
    | .num s _ => #[s]
    | .match _ _ arms _ => arms.flatMap (·.1.integerSpans)
    | .matches _ _ arms _ => arms.flatMap fun (ps, _, _) => ps.flatMap Pattern.integerSpans
    | .is _ _ p => p.integerSpans
    | _ => #[]
  own ++ e.operands.flatMap (·.integerSpans)

/-- The span of `e` as written: a field read, method call or index of a
receiver in parentheses starts at the `(`, which its span leaves out. -/
partial def Expr.writtenSpan (src : Array Char) (e : Expr) : Span :=
  match e with
  | .field _ r _ | .method _ r _ _ | .index _ r _ =>
    let r := Fren.Core.withParens src (toRange (r.writtenSpan src))
    { e.span with start := r.start }
  | _ => e.span

/-- `e` as the lints that rewrite it (`Fren.Core.ExLint`) and the operator
lints see it, with its ranges counted from `base`. Given `src`, a field
read or method call is at its span as written. -/
partial def Expr.boolNode (e : Expr) (src : Array Char := #[]) (base : Nat := 0) : Fren.Core.BNode Span :=
  match e with
  | .block sp _ members => .mk .atom (toRange sp) sp (members.map (fun m => m.2.boolNode src base))
  | .when s n c d => .mk (.when n) (toRange s) s #[c.boolNode src base, d.boolNode src base]
  | .ite s c a b => .mk .ite (toRange s) s #[c.boolNode src base, a.boolNode src base, b.boolNode src base]
  | .bin s op a b => .mk (.bin op) (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .not s a => .mk .not (toRange s) s #[a.boolNode src base]
  | .neg s a => .mk .neg (toRange s) s #[a.boolNode src base]
  | .bool s b => .mk (.lit b) (toRange s) s #[]
  | .method s r m args =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk (.method m.name) (toRange s) s (#[r.boolNode src base] ++ args.map (·.boolNode src base))
  | .app s _ args | .set s args | .seq s args => .mk .atom (toRange s) s (args.map (·.boolNode src base))
  | .record s _ fields => .mk .atom (toRange s) s (fields.filterMap (·.2.map (·.boolNode src base)))
  | .update s r fields => .mk .atom (toRange s) s (#[r.boolNode src base] ++ fields.filterMap (·.2.map (·.boolNode src base)))
  | .field s a _ =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk .atom (toRange s) s #[a.boolNode src base]
  | .is s scrutinee _ => .mk .patternTest (toRange s) s #[scrutinee.boolNode src base]
  | .match s scrutinee arms _ => .mk .atom (toRange s) s (#[scrutinee.boolNode src base] ++ (armParts arms).map (·.boolNode src base))
  | .table s rows => .mk .atom (toRange s) s ((tableParts rows).map (·.boolNode src base))
  | .pair s a b | .index s a b => .mk .atom (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .chain s es ops => .mk (.chain (ops.map (·.1))) (toRange s) s (es.map (·.boolNode src base))
  | .«let» s _ body _ => .mk .«let» (toRange s) s #[body.boolNode src base]
  | .matches s ss arms _ => .mk .atom (toRange s) s ((ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).map (·.boolNode src base))
  | .quant s _ _ b | .closure s _ b => .mk .quant (toRange s) s #[b.boolNode src base]
  | .num s _ | .path s _ | .str s .. => .mk .atom (toRange s) s #[]
-- `base` is at most the start of `e`'s span as written, and every span in
-- `e` is within it, so the subtractions do not truncate.
where toRange (sp : Span) : Fren.Core.Range := { start := sp.start - base, stop := sp.stop - base }

/-- The pairs of parentheses directly around `sp` in `src`, from the inside
out, each from its `(` to its `)`. -/
def parenLayers (src : Array Char) (sp : Span) : Array Span := Id.run do
  let mut out := #[]
  let mut (i, j) := (sp.start, sp.stop)
  repeat
    let mut a := i
    while a > 0 && src[a - 1]!.isWhitespace do a := a - 1
    let mut b := j
    while b < src.size && src[b]!.isWhitespace do b := b + 1
    unless a > 0 && src[a - 1]! == '(' && b < src.size && src[b]! == ')' do break
    (i, j) := (a - 1, b + 1)
    out := out.push { start := i, stop := j }
  return out

/-- Reports `double_parens` in `e` and within it (`lint::double_parens`),
where `call` says that `e` is the only argument of an application, whose
parentheses are not its own. The parentheses around `e` are those around
it as written (`writtenSpan`): a receiver's own, as in `({1}).card`, are
not. -/
partial def lintParens (e : Expr) (call : Bool := false) : M Unit := do
  let src := (← get).src
  let layers := parenLayers src (e.writtenSpan src)
  let layers := if call then layers.pop else layers
  if Fren.Core.doubleParens layers.size then
    lintFix .doubleParens layers.back! (Fren.Core.doubleParensMsg (String.ofList (src.extract layers[0]!.start layers[0]!.stop).toList))
  match e with
  | .app _ _ #[a] => lintParens a true
  | .method _ r _ #[a] => lintParens r; lintParens a true
  | _ => for k in e.operands do lintParens k

/-- The members of `e` if it is a pair, `(a, b)`, not in parentheses: in
them it would be an expression, which a pair is not. -/
def Expr.pair? (src : Array Char) : Expr → Option (Expr × Expr)
  | .pair s a b => if Fren.Core.enclosed src { start := 0, stop := src.size } (toRange s) then none else some (a, b)
  | _ => none

/-- Where `e`, an operand of `p`, is, as `lang::operand` sees it; `none`
where any expression can be written, as in parentheses. -/
def Expr.operandSlot (src : Array Char) (p e : Expr) : Option Fren.Core.Slot :=
  if Fren.Core.enclosed src { start := 0, stop := src.size } (toRange e.span) then none else
  match p with
  | .field _ x _ | .method _ x _ _ | .index _ x _ | .match _ x _ _ =>
    if x.span == e.span then some Fren.Core.receiverSlot else none
  | _ =>
    let .mk k _ _ kids := p.boolNode
    (kids.findIdx? fun | .mk _ r _ _ => r == toRange e.span).bind (k.slots[·]?.join)

/-- `e` as written, with the parentheses around it, and its precedence
(`lang::operand`). -/
def Expr.text (src : Array Char) (e : Expr) : Fren.Core.BText :=
  let r := Fren.Core.withParens src (toRange e.span)
  let prec := if r != toRange e.span then Fren.Core.BKind.atom.prec else match e.boolNode with | .mk k .. => k.prec
  { text := Fren.Core.textOf src r, prec }

/-- Whether a name declared in `cx`, or among `extra`, would hide
something in scope (`lang::shadowing`). -/
def hidesIn (cx : ExprCtx) (extra : Fren.Core.Locals := #[]) : M (String → Bool) := do
  let st ← get
  let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome ++ extra
  return fun n => (st.table.hidden? st.scope locals (Name.mkSimple n)).isSome

/-- Reports the expressions in `e` that the lints that rewrite them
(`Fren.Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated, where `hides` says
whether a name declared there would hide something in scope. -/
def lintBools (e : Expr) (hides : String → Bool) (onlyArg : Bool := false) : M Unit := do
  -- Not a rewrite of an expression with a pattern test that binds names,
  -- which could move what mentions them out of their scope
  -- (`lang::test_scope`).
  let tests := (← get).bindingTests
  modify fun s => { s with bindingTests := #[] }
  let keeps (sp : Span) := !tests.any fun t => sp.start ≤ t.start && t.stop ≤ sp.stop
  -- The text of `e` alone, as written, and `e` over it, as the Lean front
  -- end gives them: the three lints read no text outside `e`
  -- (`Fren.Core.upTo`), and report at the spans, which stay as they are.
  -- Cutting out `e`, not all the text before it, keeps the cost of each
  -- expression to its size.
  let full := (← get).src
  let w := e.writtenSpan full
  let src := full.extract w.start w.stop
  let root := e.boolNode full w.start
  -- A fix's own range is counted in `src`, from `w.start`.
  let shift (m : Msg) : Msg :=
    { m with fixes := m.fixes.map fun f => { f with range? := f.range?.map fun r => { start := r.start + w.start, stop := r.stop + w.start } } }
  for (l, ref, msg) in Fren.Core.rewriteReports src root do
    if keeps ref then lintFix l ref (shift msg)
  let (boolEqs, ordereds, variants, absEnds, mentioning, facts) :=
    ((← get).boolEqs, (← get).ordereds, (← get).variants, (← get).absEnds, (← get).mentioning, (← get).facts)
  modify fun s => { s with boolEqs := #[], ordereds := #[], variants := #[], absEnds := #[], mentioning := #[], facts := #[] }
  -- Looked up by span, in maps, rather than by reading the arrays, which
  -- would take time quadratic in the expression's size: the first entry
  -- for each span, as `find?` gives it, and whether one has the span, as
  -- `contains` says.
  let firstBySpan {α : Type} (xs : Array (Span × α)) : Std.HashMap Span α :=
    xs.foldl (init := {}) fun m (sp, a) => if m.contains sp then m else m.insert sp a
  let (variants, facts, ordereds) := (firstBySpan variants, firstBySpan facts, firstBySpan ordereds)
  let mentioning := firstBySpan mentioning
  let boolEqs := Std.HashSet.ofArray boolEqs
  let absEnds := Std.HashSet.ofArray absEnds
  let variant? (sp : Span) := variants[sp]?
  let fact? (sp : Span) := facts[sp]?
  let ordered? (sp : Span) := ordereds[sp]?
  let mentioned (sp : Span) := mentioning[sp]?.getD []
  let st ← get
  let fcx : Fren.Core.ForallCx :=
    { variants? := fun p => (st.dataOf? p.toName).bind fun d =>
        if d.isRecord || d.ctors.any (!·.2.isEmpty) then none else some d.ctors.size
      declared := e.declaredNames, hides, unguarded := !Fren.Core.hasGuarded (String.ofList src.toList) }
  for r in Fren.Core.opReports src boolEqs.contains ordered? variant? (absEnds.contains ·.stop) mentioned fact? fcx root do
    let ref := match r.last? with | some l => r.ref.to l | none => r.ref
    if keeps ref then lintFix r.lint ref (shift r.msg) r.unless?
  for r in Fren.Core.arithReports src root do
    if keeps r.ref then lintFix r.lint r.ref (shift r.msg)
  for sp in e.integerSpans do
    if let some (r, msg) := Fren.Core.zeroPrefixedReport? full (toRange sp) then
      lintFix .zeroPrefixedLiteral { start := r.start, stop := r.stop } msg
  -- The only argument of a call is in the call's parentheses, as a
  -- function's is.
  lintParens e onlyArg

/-- Which enumerations, records and newtypes are declared `ordered`
(`Reqs/Lang/Items#ordered-declarations`), for `Fren.Core.Ty.ordered`. -/
def State.orderedDecl (s : State) (p : Name) : Bool :=
  (s.dataOf? p).any (·.ordered) || s.orderedNewtypes.contains p

/-- `State.orderedDecl` of the current state. -/
def orderedDecl : M (Name → Bool) := return (← get).orderedDecl

/-- How values of `t` are compared, if it is ordered (`Fren.Core.orderPlan?`). -/
def orderPlan? (t : Ty) : M (Option Fren.Core.OrderPlan) := do
  let s ← get
  let fieldsOf (p : Name) := ((s.dataOf? p).filter (·.isRecord)).bind (·.ctors[0]?) |>.map (·.2.toList) |>.getD []
  return Fren.Core.orderPlan? s.orderedDecl fieldsOf (s.datatypes.size + s.newtypes.size) t

/-- `x < y`, or `x <= y` if not `strict`, of values compared by `o`, as
SMT-LIB: a record's lexicographically, by its fields in the order
declared, and a newtype's as its value's, which it is erased to. -/
partial def orderSmt (o : Fren.Core.OrderPlan) (strict : Bool) (x y : String) : M String := do
  let op := if strict then "<" else "<="
  match o with
  | .number => return s!"({op} {x} {y})"
  | .string => return Fren.Core.strCompareSmt x y !strict
  | .enum p as =>
    let some d := (← get).dataOf? p | return s!"({op} {x} {y})"
    return s!"({op} {d.ordinal x as} {d.ordinal y as})"
  | .newtype _ u => orderSmt u strict x y
  | .record p fs =>
    -- From the last field, compared as the whole is, back to the first,
    -- which decides unless the two are equal.
    let sel (f : Name) (v : String) := s!"({fieldSym p f} {v})"
    let some (fl, ol) := fs.getLast? | return (if strict then "false" else "true")
    let mut acc ← orderSmt ol strict (sel fl x) (sel fl y)
    for (f, of) in fs.dropLast.reverse do
      let (a, b) := (sel f x, sel f y)
      acc := s!"(or {← orderSmt of true a b} (and (= {a} {b}) {acc}))"
    return acc

/-- The ordering `op` of `x` and `y`, compared by `o`, as SMT-LIB: as
`orderSmt` writes it, with `>` and `>=` as `<` and `<=` of `y` and `x`, but
of numbers and enumerations, and newtypes of them, with `op` itself. -/
partial def orderingSmt (o : Fren.Core.OrderPlan) (op : String) (x y : String) : M String := do
  match o with
  | .newtype _ u => orderingSmt u op x y
  | .number => return s!"({op} {x} {y})"
  | .enum p as =>
    let some d := (← get).dataOf? p | return s!"({op} {x} {y})"
    return s!"({op} {d.ordinal x as} {d.ordinal y as})"
  | _ => match op with
    | "<" => orderSmt o true x y
    | "<=" => orderSmt o false x y
    | ">" => orderSmt o true y x
    | _ => orderSmt o false y x

/-- `e` has type `found` where `expected` was required. -/
def mismatch (e : Expr) (expected found : Ty) (why : Option String := none) : M α :=
  err e.span (Fren.Core.typeMismatchMsg expected found why)

/-- Count every listed element instead of using cvc5's native finite-sort
cardinality, which may fail or return a refuted model (#820). -/
def setCardSmt (recv : String) (t : Ty) : M String := do
  let s ← get
  let values? := match t with
    | .set a => (s.values Fren.Core.maxInstances a).map (·.map (s!"(tuple {·})"))
    | .rel a b => do
      let xs ← s.values Fren.Core.maxInstances a
      let ys ← s.values Fren.Core.maxInstances b
      if xs.size * ys.size > Fren.Core.maxInstances then none else
        some (xs.flatMap fun x => ys.map fun y => s!"(tuple {x} {y})")
    | _ => none
  let some vs := Fren.Core.setCardExpansion values? | return s!"(set.card {recv})"
  Fren.Core.sumSetMembersM vs "0"
    (fun v => pure s!"(ite (set.member {v} {recv}) 1 0)")
    (fun a b => pure s!"(+ {a} {b})")

/-- Calls the method `m` of the value `recv` of type `t`, with the
arguments `args`, each with its type and span (`lang::method_type`). -/
def callMethod (span : Span) (recv : String) (t : Ty) (m : String) (args : Array (String × Ty × Span)) :
    M (String × Ty) := do
  if let .rel a b := t then
    let project (k : Nat) (other : Ty) : M String := do
      if let some vs := (← get).values 64 other then
        let u := match vs.toList.map (s!"(tuple {·})") with
          | [] => s!"(as set.empty {(Ty.set other).sort})"
          | [v] => s!"(set.singleton {v})"
          | v :: vs => s!"(set.insert {v} {" ".intercalate vs.dropLast} (set.singleton {vs.getLast!}))"
        return if k == 0 then s!"(rel.join {recv} {u})" else s!"(rel.join {u} {recv})"
      modify fun s => { s with usesProjection := true }
      return s!"((_ rel.project {k}) {recv})"
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false true)
      | err span (Fren.Core.unknownMethodMsg m t.show false false true)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    return ← match method with
      | .card => do pure (← setCardSmt recv t, .int)
      | .inverse => pure (s!"(rel.transpose {recv})", .rel b a)
      -- A join with every value of the other type, if it is finite; else a
      -- projection, which needs higher-order logic.
      | .domain => do pure (← project 0 b, .set a)
      | .range => do pure (← project 1 a, .set b)
      | .closure => do
        unless a == b do err span (Fren.Core.closureTypeMsg t.show)
        pure (s!"(rel.tclosure {recv})", t)
      | _ => do
        -- `image(s)`: `s` as a unary relation, joined with the relation.
        let (x, ta, sp) := args[0]!
        unless ta == .set a do
          err sp { code? := some "F0304", headline := s!"type mismatch: expected `{(Ty.set a).show}`, found `{ta.show}`"
                   label? := some s!"expected `{(Ty.set a).show}`, found `{ta.show}`"
                   notes := #[s!"note: the image of a `{t.show}` is of a set of its pairs' first members"] }
        pure (s!"(rel.join {x} {recv})", .set b)
  if let .set _ := t then
    unless m == "card" do err span (Fren.Core.unknownSetMethodMsg m t.show)
    unless args.isEmpty do err span (Fren.Core.arityMsg (Name.mkSimple m) 0 args.size)
    return (← setCardSmt recv t, .int)
  if let .seq elem := t then
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false false true)
      | err span (Fren.Core.unknownMethodMsg m t.show false false false true)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    let tyOf : Fren.Core.MethodTy → Ty | .bool => .bool | .int => .int | .elem => elem | _ => t
    for (_, ta, sp) in args, p in method.params, k in [0:args.size] do
      let tp := tyOf p
      unless ta.widens tp do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `{tp.show}`, found `{ta.show}`"
                 label? := some s!"expected `{tp.show}`, found `{ta.show}`"
                 notes := #[s!"note: argument {k + 1} of `{m}` is {if tp == .int then "an" else "a"} `{tp.show}`"] }
    let a := (args.map (·.1))[0]?.getD ""
    let b := (args.map (·.1))[1]?.getD ""
    let smt := match method with
      | .len => s!"(seq.len {recv})"
      | .startsWith => s!"(seq.prefixof {a} {recv})"
      | .endsWith => s!"(seq.suffixof {a} {recv})"
      | .contains => s!"(seq.contains {recv} {a})"
      | .at => s!"(seq.at {recv} {a})"
      | .slice => s!"(seq.extract {recv} {a} {b})"
      | .indexOf => s!"(seq.indexof {recv} {a} {b})"
      | .replace => s!"(seq.replace {recv} {a} {b})"
      | .update => s!"(seq.update {recv} {a} (seq.unit {b}))"
      | _ => s!"(seq.rev {recv})"
    return (smt, tyOf method.result)
  if t == .int || t == .nat then
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false (int := true))
      | err span (Fren.Core.unknownMethodMsg m t.show false (int := true))
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    for (_, ta, sp) in args, k in [0:args.size] do
      unless ta.widens .int do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `Int`, found `{ta.show}`"
                 label? := some s!"expected `Int`, found `{ta.show}`"
                 notes := #[s!"note: argument {k + 1} of `{m}` is an `Int`"] }
    -- Conditionals, so that they stay linear.
    let y := (args.map (·.1))[0]?.getD ""
    -- `min` and `max` of `Nat`s are `Nat`s (`lang::nat_result`).
    let op : Fren.Core.NatOp := match method with | .min => .min | .max => .max | _ => .abs
    let nat := Fren.Core.natResult op (t == .nat) (args.any (·.2.1 == .nat)) false
    return (match method with
      | .min => s!"(ite (<= {recv} {y}) {recv} {y})"
      | .max => s!"(ite (>= {recv} {y}) {recv} {y})"
      | _ => s!"(ite (< {recv} 0) (- {recv}) {recv})", if nat then .nat else .int)
  -- `min` and `max` of a value of an ordered type, and an enumeration's,
  -- record's or newtype's other methods, which it has none of
  -- (`lang::method_type`, `lang::ordered_type`).
  if t.orderedDecl?.isSome || (t == .string && (m == "min" || m == "max")) then
    let ordered := t.ordered (← get).orderedDecl
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false (ordered := ordered))
      | if ordered then err span (Fren.Core.unknownMethodMsg m t.show false (ordered := true))
        else if m == "min" || m == "max" then err span (Fren.Core.unorderedMethodMsg (t.orderedDecl?.getD .record) m t.show)
        else err span (Fren.Core.noMethodsMsg m t.show)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    for (_, ta, sp) in args do
      unless ta == t do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `{t.show}`, found `{ta.show}`"
                 label? := some s!"expected `{t.show}`, found `{ta.show}`"
                 notes := #[s!"note: the argument of `{m}` is a `{t.show}`, as its receiver is"] }
    -- Conditionals on the order, as for an `Int`.
    let y := (args.map (·.1))[0]?.getD ""
    let some plan ← orderPlan? t | internal span s!"`{t.show}` is not ordered"
    let cmp ← orderingSmt plan (if method == .min then "<=" else ">=") recv y
    return (s!"(ite {cmp} {recv} {y})", t)
  unless t == .string do err span (Fren.Core.noMethodsMsg m t.show)
  let some method := (Fren.Core.Method.ofName? m).filter (·.accepts true false)
    | err span (Fren.Core.unknownMethodMsg m t.show (ordered := true))
  unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
  let tyOf : Fren.Core.MethodTy → Ty | .bool => .bool | .int => .int | _ => .string
  for (_, ta, sp) in args, p in method.params, k in [0:args.size] do
    let tp := tyOf p
    unless ta.widens tp do
      err sp { code? := some "F0304", headline := s!"type mismatch: expected `{tp.show}`, found `{ta.show}`"
               label? := some s!"expected `{tp.show}`, found `{ta.show}`"
               notes := #[s!"note: argument {k + 1} of `{m}` is {if tp == .int then "an" else "a"} `{tp.show}`"] }
  let a := (args.map (·.1))[0]?.getD ""
  let b := (args.map (·.1))[1]?.getD ""
  let smt := match method with
    | .len => s!"(str.len {recv})"
    | .startsWith => s!"(str.prefixof {a} {recv})"
    | .endsWith => s!"(str.suffixof {a} {recv})"
    | .contains => s!"(str.contains {recv} {a})"
    | .matches => s!"(str.in_re {recv} {a})"
    | .at => s!"(str.at {recv} {a})"
    | .slice => s!"(str.substr {recv} {a} {b})"
    | .indexOf => s!"(str.indexof {recv} {a} {b})"
    | .replace => s!"(str.replace {recv} {a} {b})"
    | .replaceAll => s!"(str.replace_all {recv} {a} {b})"
    | _ => s!"(set.card {recv})"
  return (smt, tyOf method.result)

/-- Reads the field `f` of the value `smt` of type `t`; of a `String`, calls
the method `f`, without arguments. -/
def readField (span : Span) (smt : String) (t : Ty) (f : Name) : M (String × Ty) := do
  -- The field `0` of a newtype, which is erased (`Reqs/Lang/Expressions#newtypes`).
  if let .newtype p u := t then
    if f == Name.mkSimple "0" then return (smt, u)
    err span (Fren.Core.noFieldMsg f (showPath p) #[Name.mkSimple "0"])
  -- A field named by digits is no method's name.
  if Fren.Core.positionalField f && !(t matches .record ..) then err span (Fren.Core.noFieldMsg f t.show #[])
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (t == .int || t == .nat) && f == `abs then modify fun s => { s with absEnds := s.absEnds.push span.stop }
  if t matches .string | .set _ | .rel .. | .seq _ | .int | .nat then return ← callMethod span smt t f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if t matches .enum .. && (f == `min || f == `max) then return ← callMethod span smt t f.toString #[]
  let .record p args := t | err span (Fren.Core.noFieldMsg f t.show #[])
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let fields : Array (Name × Ty) := ((← get).dataOf? p).map (·.instCtors args |>.getD 0 default |>.2) |>.getD #[]
  let some (_, ft) := fields.find? (·.1 == f) | err span (Fren.Core.noFieldMsg f t.show (fields.map (·.1)))
  return (s!"({fieldSym p f} {smt})", ft)

/-- The types that the method `m` of the relation type `t` ranges over
(`Reqs/Lang/Decidability#relations`), or `none` if it is not relational. -/
def relRange? (t : Ty) (m : String) : Option (Array Ty) :=
  match t, Fren.Core.Method.ofName? m with
  | .rel a b, some .inverse => some #[a, b]
  | .rel a _, some .closure | .rel a _, some .image | .rel a _, some .range => some #[a]
  | .rel _ b, some .domain => some #[b]
  | _, _ => none

def andSmt (a b : String) : String := s!"(and {a} {b})"

/-- The SMT-LIB disjunction of `cs`. -/
def orSmt (cs : Array String) : String := if cs.size == 1 then cs[0]! else s!"(or {" ".intercalate cs.toList})"

/-- The indexes recorded since the last call, which it forgets. -/
def takeIndexes : M (Array (Span × String × Option (String × Bool))) := do
  let xs := (← get).indexes
  modify fun s => { s with indexes := #[] }
  return xs

/-- The source text at `span`. -/
def srcAt (span : Span) : M String := return String.ofList ((← get).src.extract span.start span.stop).toList

/-- Whether an infix operator follows `span` (`Fren.Core.followedAt`). -/
def followedSpan (span : Span) : M Bool := return Fren.Core.followedAt (← get).src (toRange span)

/-- Whether `e` is a set or relation literal, rather than a string or
sequence literal, and its characters or elements, if it is one of those. -/
def Expr.literalCount? : Expr → Option (Bool × Nat)
  | .str _ v => some (false, v.length)
  | .seq _ xs => some (false, xs.size)
  | .set _ xs => some (true, xs.size)
  | _ => none

/-- The receiver of `e`, if it reads `len` or `card` without arguments. -/
def lengthOf? : Expr → Option (Expr × Bool)
  | .path sp #[seg] =>
    let parts := seg.name.splitOn "."
    let m := parts.getLast?.getD ""
    if parts.length < 2 || !(m == "len" || m == "card") then none else
    let recv := ".".intercalate parts.dropLast
    let rs : Span := { sp with stop := sp.start + recv.length }
    some (.path rs #[{ name := recv, span := rs }], m == "card")
  | .field _ r f | .method _ r f #[] =>
    if f.name == "len" then some (r, false) else if f.name == "card" then some (r, true) else none
  | _ => none

/-- The receiver of `e` and the name it reads, if it reads a field or calls a
method without arguments. -/
def lastName? : Expr → Option (Expr × String)
  | .path sp #[seg] =>
    let parts := seg.name.splitOn "."
    if parts.length < 2 then none else
    let recv := ".".intercalate parts.dropLast
    let rs : Span := { sp with stop := sp.start + recv.length }
    some (.path rs #[{ name := recv, span := rs }], parts.getLast!)
  | .field _ r f | .method _ r f #[] => some (r, f.name)
  | _ => none

/-- The names that `e` reads one after another, innermost first, each with
its receiver. -/
partial def namesRead (e : Expr) : Array (Expr × String) :=
  match lastName? e with
  | some (r, n) => (namesRead r).push (r, n)
  | none => #[]

/-- The sequences that `e` indexes, as their text. -/
partial def indexedIn : Expr → M (Array String)
  | .block _ _ members => members.foldlM (fun acc (_, value) => return acc ++ (← indexedIn value)) #[]
  | .index _ q i => return #[← srcAt q.span] ++ (← indexedIn q) ++ (← indexedIn i)
  | .bin _ _ a b | .when _ _ a b | .pair _ a b => return (← indexedIn a) ++ (← indexedIn b)
  | .not _ a | .neg _ a | .field _ a _ | .is _ a _ => indexedIn a
  | .ite _ c a b => return (← indexedIn c) ++ (← indexedIn a) ++ (← indexedIn b)
  | .method _ r _ args => return (← indexedIn r) ++ (← args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[])
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | .record _ _ fs => fs.foldlM (fun acc (_, e?) => return acc ++ (← (e?.map indexedIn).getD (pure #[]))) #[]
  | .match _ sc arms _ => return (← indexedIn sc) ++ (← (armParts arms).foldlM (fun acc b => return acc ++ (← indexedIn b)) #[])
  | .matches _ ss arms _ => (ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).foldlM (fun acc b => return acc ++ (← indexedIn b)) #[]
  -- As the Lean front end reads it: the record, and the new values.
  | .update _ r fs => do
    fs.foldlM (init := ← indexedIn r) fun acc (_, e?) => return acc ++ (← (e?.map indexedIn).getD (pure #[]))
  | .quant _ _ _ b => indexedIn b
  | .table _ rows => (tableParts rows).foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | _ => return #[]

/-- Whether `e` bounds the sequence written `q`: it mentions `q.len`, or
compares `q` with `[]` (`lint::index_after_use`). -/
def boundsSeq (e : Expr) (q : String) : M Bool := do
  let t := (← srcAt e.span).replace " " ""
  return (t.splitOn s!"{q}.len").length > 1 || (t.splitOn s!"{q}!=[]").length > 1 || (t.splitOn s!"{q}=[]").length > 1

/-- Remove leading evaluation guards, keeping the operation and actual
arguments as part of a generated site's identity. -/
partial def siteOperation (formula : String) : String :=
  match Fren.Core.STerm.parse formula with
  | .list [.atom "=>", _, body] => siteOperation body.print
  | .list [.atom "ite", condition, yes, no] =>
    (Fren.Core.STerm.list [.atom "ite", condition, Fren.Core.STerm.parse (siteOperation yes.print), Fren.Core.STerm.parse (siteOperation no.print)]).print
  | .list (.atom "and" :: members) =>
    let operations := members.map fun member => siteOperation member.print
    if let first :: rest := operations then
      if rest.all (· == first) then first else (Fren.Core.STerm.list (.atom "and" :: members)).print
    else "(and)"
  | .list [.atom binder, bindings, body] =>
    if binder == "let" || binder == "forall" || binder == "exists" then
      (Fren.Core.STerm.list [.atom binder, bindings, Fren.Core.STerm.parse (siteOperation body.print)]).print
    else (Fren.Core.STerm.list [.atom binder, bindings, body]).print
  | term => term.print

/-- `goal` where `guards` hold. -/
def guarded (guards : Array String) (goal : String) : String :=
  if guards.isEmpty then goal else s!"(=> (and true {" ".intercalate guards.toList}) {goal})"

/-- `e` within the SMT-LIB `let`s of `binds`, each a symbol and its
definition, the first outermost. -/
def wrapLets (binds : Array (String × String)) (e : String) : String :=
  binds.foldr (fun (x, d) acc => s!"(let (({x} {d})) {acc})") e

/-- The term within the SMT-LIB `let`s that `wrapLets` puts around it, and
the `forall`s that an unbounded quantifier puts around an application in
its body (`natApps`), read outside string literals, where `""` is a `"`. -/
partial def peelLets (t : String) : String := Id.run do
  let start := if t.startsWith "(let ((" then 5 else if t.startsWith "(forall ((" then 8 else 0
  if start == 0 then return t
  let cs := t.toList.toArray
  -- The bindings start at the second `(`, and end where it closes.
  let mut depth := 0
  let mut inString := false
  let mut i := start
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then inString := !inString
    else if !inString && c == '(' then depth := depth + 1
    else if !inString && c == ')' then
      depth := depth - 1
      if depth == 0 then break
    i := i + 1
  -- `(let BINDINGS TERM)`.
  return peelLets (String.ofList (cs.extract (i + 2) (cs.size - 1)).toList)

/-- Records the index `q[i]` at `span`, whose sequence and position are the
SMT-LIB `q` and `i`, for the definedness check (`check::definedness`). -/
def noteIndex (cx : ExprCtx) (span : Span) (q i : String) : M Unit := do
  unless cx.noteIndexes do return
  let bounds := s!"(and (<= 0 {i}) (< {i} (seq.len {q})))"
  modify fun s => { s with indexes := s.indexes.push (span, guarded cx.guards bounds, none) }

/-- Records the obligation of the value `value`, in SMT-LIB, given at
`span` where the type `t` is declared, if it has one, for the subset-type
check (`Reqs/Check#subset-types`): its guard implies that the value
matches. It is a definedness goal, with its type beside it. -/
def noteObligation (cx : ExprCtx) (place : Fren.Core.ValuePlace) (span : Span) (t : Fren.Core.PTy) (value : String) :
    M Unit := do
  unless cx.noteIndexes do return
  let some o := Fren.Core.siteObligation place (t.obligation (← get).shapeOf) | return
  let st ← get
  for (label, part) in o.namedParts do
    let text := if label.isAnonymous then t.text else "@invariant:" ++ Fren.Core.showPath label
    modify fun s => { s with indexes := s.indexes.push (span, guarded cx.guards (consSmt st.dataOf? part value), some (text, part.quantifies)) }

/-- The declared type of the `k`th field or payload value of the variant
`v` of the record, newtype or enumeration `p`, with the type arguments
`args` for its type parameters, if it is generic (`Fren.Core.PTy.subst`). -/
def partPTy (p : Name) (v k : Nat) (args : Array Ty := #[]) : M Fren.Core.PTy := do
  let some t := ((← get).shapeOf p).bind (·.parts[v]?) |>.bind (·[k]?) | return default
  return if args.isEmpty then t else t.subst (args.map .plain)

/-- The value of a table of type `t` where no row holds: an index out of
range of the empty sequence, which is unspecified
(`Reqs/Lang/Expressions#tables`). -/
def unspecified (t : Ty) : String := s!"(seq.nth (as seq.empty (Seq {t.sort})) 0)"

/-- The questions about tables recorded since the last call, which it forgets. -/
def takeTables : M (Array (Span × Fren.Core.TableGoal × String)) := do
  let xs := (← get).tables
  modify fun s => { s with tables := #[] }
  return xs

/-- Records what each application of the uninterpreted function whose
symbol is `sym`, whose result has the declared type `rp`, brings: what its
result's type does, a `Nat`'s among it (`State.funFacts`). -/
def noteResultFactAt (sym : String) (rp : Fren.Core.PTy) : M Unit := do
  let st ← get
  if (rp.cons st.shapeOf).isNone then return
  let some c := rp.cons st.shapeOf (rp.ty == .nat) | return
  modify fun s => { s with funFacts := s.funFacts.insert sym (consSmt st.dataOf? c factHole)
                           quantifiedFns := if c.quantifies then s.quantifiedFns.insert sym else s.quantifiedFns }

/-- The symbol of the clause whose symbol is `csym`, of the generic
function at `path`, at its instance with the type arguments `args`. -/
def clauseInstSym (path : Name) (args : Array Ty) (csym : String) : String :=
  ((instSym path args).dropEnd 1).toString ++ (csym.drop (3 + (showPath path).length)).toString

/-- The symbol of the instance of the generic function at `path` with the
type arguments `args`, whose `define-fun`, and its clauses', it adds to
`defs` and `clauseDefs` the first time, after the instances that they
apply (`Reqs/Lang/GenericFunctions#meaning`): each is the function's own,
with the arguments' sorts for its type parameters' and the instances that
they give for those that it applies. Where `args` are the function's own
type parameters, it is the function's own symbol. -/
partial def instantiate (path : Name) (args : Array Ty) : M String := do
  let some g := (← get).genericFns.find? path | return itemSym path
  let own := g.params.mapIdx fun k p => Ty.abstract (Fren.Core.typeParamPath path k p)
  if args == own then return itemSym path
  let name := instName path args
  if let some sym := (← get).instSyms.find? name then return sym
  let sym := instSym path args
  -- Applied in its own contract, at another instance: made once its body
  -- and contract are known (`State.pendingInsts`).
  if (← get).fnTypeParams.any (·.1 == path) then
    modify fun s => { s with pendingInsts := s.pendingInsts.push args }
    return sym
  let inst (t : Ty) : Ty := (t.asParams path g.params).subst args
  let mut repl : Std.HashMap String String := {}
  for p in g.params, k in [0:g.params.size] do
    repl := repl.insert (itemSym (Fren.Core.typeParamPath path k p)) args[k]!.sort
  -- Its applications of itself, at its own type parameters, apply this
  -- instance, in a structural recursion too (`lang::applied_instance`).
  repl := repl.insert (itemSym path) (instSym path (Fren.Core.appliedInstance path g.params args own))
  for (csym, _, _) in g.clauses do repl := repl.insert csym (clauseInstSym path args csym)
  for (callee, cargs) in g.calls do
    if callee == path then continue
    repl := repl.insert (instSym callee cargs) (← instantiate callee (Fren.Core.appliedInstance path g.params args cargs))
  let clauses := g.clauses.map fun (csym, cvars, cbody) =>
    (clauseInstSym path args csym, cvars.map fun (x, t) => (x, inst t), replaceSymbols cbody repl)
  if !g.defined then
    -- An unknown function of its own, with the instance's sorts, whose
    -- applications bring its contract's postconditions and its result
    -- type's constraint at the instance, as any uninterpreted function's
    -- do (`lang::uninterpreted_instance`).
    let (ps, r) := Fren.Core.instanceSig g.declared g.result args
    let k := ((← get).contracts.find? path).getD {}
    let atInst (cs : Array (Name × String)) := cs.map fun (n, csym) => (n, clauseInstSym path args csym)
    modify fun s => { s with
      instSyms := s.instSyms.insert name sym
      funs := s.funs.push (name, ps, r)
      contracts := s.contracts.insert name { k with pres := atInst k.pres, posts := atInst k.posts }
      clauseDefs := s.clauseDefs ++ clauses }
    -- Its result type's constraint is the instance's.
    noteResultFactAt sym (Fren.Core.instanceResult g.resultP args)
    -- Its contract at the instance's sorts, with the instance for the
    -- function, for the check of its realizability where the one at the
    -- type parameters' sorts does not pass.
    if let some b := (← get).bodies.find? fun b => b.fn? == some path && b.generic then
      let instP (t : Fren.Core.PTy) := Fren.Core.instanceResult (t.asParams path g.params) args
      let vars ← b.vars.mapM fun v => do
        let ptype := instP v.ptype
        let st ← get
        return { v with ty := inst v.ty, ptype, fact? := (ptype.cons st.shapeOf).map (consSmt st.dataOf? · (quote v.name.toString)) }
      let rs (t : String) := replaceSymbols t repl
      let ic : CComp := { b with
        vars, generic := false, fn? := some (Fren.Core.instanceName path args), finiteModel := args.any (·.hasTypeParam)
        props := b.props.map fun p => { p with smt := rs p.smt, trigger? := p.trigger?.map rs }
        defs := b.defs.map fun (d, e) => (d, rs e)
        indexes := b.indexes.map fun (n, pl, sp, g, t) => (n, pl, sp, rs g, t)
        tables := b.tables.map fun (n, pl, sp, q, g) => (n, pl, sp, q, rs g)
        natApps := b.natApps.map rs }
      modify fun s => { s with instContracts := s.instContracts.insert path (((s.instContracts.find? path).getD #[]).push (args, ic)) }
    return sym
  if let some template := (← get).namedPredicates.find? path then
    let map (f : String) := replaceSymbols f repl
    let transform (c : NamedClause) := { c with
      formula := map c.formula
      branches := c.branches.map (·.map map)
      groups := c.groups.map (·.map map)
      indexes := c.indexes.map fun (sp, f, t) => (sp, map f, t)
      tables := c.tables.map fun (sp, q, f) => (sp, q, map f) }
    modify fun s => { s with namedPredicates := s.namedPredicates.insert name { template with
      clauses := template.clauses.map transform
      whole? := template.whole?.map transform } }
  let vars := g.vars.map fun (x, t) => (x, inst t)
  modify fun s => { s with
    instSyms := s.instSyms.insert name sym
    defs := s.defs.push (name, vars, g.result.subst args, replaceSymbols g.body repl)
    clauseDefs := s.clauseDefs ++ clauses }
  -- An instance of a structural recursion is one too, at the instance: its
  -- applications are opaque, with its contract's postconditions at the
  -- instance and one step of its body, which applies the instance itself
  -- (`Reqs/Lang/Recursion#generic-recursion`).
  if (← get).recursiveDefs.contains path then
    let k := ((← get).contracts.find? path).getD {}
    let atInst (cs : Array (Name × String)) := cs.map fun (n, csym) => (n, clauseInstSym path args csym)
    let domain := ((← get).bodies.find? (·.fn? == some path)).map (·.vars.filterMap (·.fact?)) |>.getD #[]
    modify fun s => { s with
      recursiveDefs := s.recursiveDefs.insert name
      contracts := s.contracts.insert name { k with pres := atInst k.pres, posts := atInst k.posts }
      recInstances := s.recInstances.insert name (path, domain.map (replaceSymbols · repl)) }
    -- Its result type's constraint, at the instance, where its declared
    -- result type has one, as the Lean front end decides from the declared
    -- type: a result that is a type parameter brings none, whatever its
    -- argument (`Reqs/Lang/Recursion#generic-recursion`).
    let st ← get
    if Fren.Core.recursiveResultFact (g.resultP.cons st.shapeOf).isSome then
      noteResultFactAt sym (Fren.Core.instanceResult g.resultP args)
  return sym

/-- The quoted symbols that the prelude declares: a closure captures each
other quoted symbol that it mentions free (`Fren.Core.inlineCall`). -/
def globalSyms : M (Std.HashSet String) := do
  let s ← get
  let mut g : Std.HashSet String := {}
  for p in s.sorts do g := g.insert (itemSym p)
  for d in s.datatypes do
    for x in d.syms do g := g.insert (quote x)
  for (p, _, _) in s.funs do g := g.insert (itemSym p)
  for (p, _, _, _) in s.defs do g := g.insert ((s.instSyms.find? p).getD (itemSym p))
  for (x, _, _) in s.clauseDefs do g := g.insert x
  return g

/-- `text`, the body or a precondition of the higher-order function at
`path`, at its instance with the type arguments `targs`: each type
parameter's sort is the argument's, and each generic function that it
applies is at the instance that the arguments give, which the function
being declared applies too (`State.genericCalls`). -/
partial def hofText (path : Name) (h : HigherOrderFn) (targs : Array Ty) (text : String) : M String := do
  if h.typeParams.isEmpty then return text
  let inst (t : Ty) : Ty := (t.asParams path h.typeParams).subst targs
  let mut repl : Std.HashMap String String := {}
  for p in h.typeParams, k in [0:h.typeParams.size] do
    repl := repl.insert (itemSym (Fren.Core.typeParamPath path k p)) targs[k]!.sort
  for (callee, cargs) in h.calls do
    let cargs' := cargs.map inst
    repl := repl.insert (instSym callee cargs) (← instantiate callee cargs')
    modify fun s => { s with genericCalls := s.genericCalls.push (callee, cargs') }
  return replaceSymbols text repl

/-- Records the questions about the application at `span` of the function
at `path` to the SMT-LIB arguments `args`, if the function has
preconditions, for the precondition check (`check::precondition`): its
guard implies each precondition at the arguments, in order; for a generic
function, its clauses at the instance with the type arguments `targs`. -/
def notePreconditions (cx : ExprCtx) (span : Span) (path : Name) (args : Array String) (targs : Array Ty := #[]) :
    M Unit := do
  unless cx.noteIndexes do return
  let some k := (← get).contracts.find? path | return
  -- Of a generic function, its clauses at the instance.
  let generic := !targs.isEmpty && (← instantiate path targs) != itemSym path
  let pres := k.pres.map fun (n, sym) =>
    (n, s!"({if generic then clauseInstSym path targs sym else sym} {" ".intercalate args.toList})")
  for (q, goal) in Fren.Core.preconditionQuestions (guarded cx.guards) path pres do
    modify fun s => { s with tables := s.tables.push (span, q, goal) }

/-- Records the questions about the rows of the table at `span`, whose
rows other than `_` have the SMT-LIB conditions `conds`, written at
`starts`, each row's condition or its `_`, whose indexes are in range where
`defined` says, for its completeness, disjointness and reachability checks
(`check::completeness`, `check::disjointness`, `check::reachability`):
completeness is reported at `table`, the disjointness of two rows at the
later one's condition, and the reachability of a row at its condition or
`_`. -/
def noteTable (cx : ExprCtx) (span : Span) (starts : Array Span) (conds : Array String) (defined : Array (Option String))
    (wild : Bool) : M Unit := do
  unless cx.noteIndexes do return
  for (g, f) in Fren.Core.tableGoals orSmt andSmt (s!"(not {·})") "true" conds defined wild do
    let at_ := match g with
      | .disjointness _ _ j | .reachability _ j => starts[j]!
      | _ => { start := span.start, stop := span.start + "table".length }
    modify fun s => { s with tables := s.tables.push (at_, g, guarded cx.guards f) }

/-- An item's questions, with each case's reachability questions merged
(`Fren.Core.mergeReach`). -/
def mergeReachTables (tbl : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) :
    Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) :=
  (Fren.Core.mergeReach andSmt (tbl.map fun (n, place, sp, g, f) => ((n, place, sp), g, f))).map
    fun ((n, place, sp), g, f) => (n, place, sp, g, f)

/-- Records the questions about the arms of the `match` at `span`, whose
patterns are at `pats`, each taken where `taken` says, of which those with
a guard are `guarded`, for its completeness and reachability checks
(`check::completeness`, `check::reachability`): completeness, unless its
arms without guards are exhaustive, is reported at `match`, and the
reachability of an arm at its pattern. Of a table over a scrutinee
(`table?`, the pairs of its arms that the disjointness check asks about,
whose guards' indexes are in range where `defined` says), also the
disjointness of those pairs, at the later arm's pattern, and completeness
at `table`. -/
def noteMatch (cx : ExprCtx) (span : Span) (pats : Array Span) (taken : Array (Option String)) (hasGuard : Array Bool)
    (unguardedExhaustive : Bool) (table? : Option (Array (Nat × Nat))) (defined : Array (Option String)) : M Unit := do
  unless cx.noteIndexes do return
  let complete := Fren.Core.completenessAsked unguardedExhaustive
  let goals := match table? with
    | some pairs => Fren.Core.tableMatchGoals orSmt andSmt (s!"(not {·})") "true" taken hasGuard defined pairs complete
    | none => Fren.Core.splitGoals .match orSmt andSmt (s!"(not {·})") "true" taken hasGuard complete
  let kw := if table?.isSome then "table" else "match"
  for (g, f) in goals do
    let at_ := match g with
      | .reachability _ j | .disjointness _ _ j => pats[j]!
      | _ => { start := span.start, stop := span.start + kw.length }
    modify fun s => { s with tables := s.tables.push (at_, g, guarded cx.guards f) }

/-- Records a `card`, of the receiver `recv` of type `t`: in a procedure that
applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (span : Span) (t : Ty) (m : String) (recv : Expr) : M Unit := do
  if cx.unmentioned then return
  if m == "card" && t matches .set _ | .rel .. && !(← isConstant cx recv) then
    modify fun s => { s with countSpans := s.countSpans.push span }

/-- Reports `undecidable` at each count of the current procedure, if it also
applies a relational operator; gives whether it does and whether it counts. -/
def checkCounts : M (Bool × Bool) := do
  let st ← get
  if st.relationalUsed then
    for sp in st.countSpans do
      modify fun s => { s with outsideCore := true }
      lint .undecidable sp (Fren.Core.undecidableMsg .relationalCard false)
  return (st.relationalUsed, !st.countSpans.isEmpty)

/-- Reports `undecidable` if a relational construct that ranges over `tys` is
outside the decidable core. -/
def checkRelational (cx : ExprCtx) (span : Span) (tys : Array Ty) (operands : Array Expr) : M Unit := do
  if cx.unmentioned then return
  let st ← get
  modify fun s => { s with relationalUsed := true }
  checkCore cx span .relational true true operands (← operands.allM (isConstant cx)) (finiteRange := tys.all (!st.infinite ·))

/-- The pattern `p`, resolved as `q`, as written (`Fren.Core.PatNode`): an
or-pattern is where its alternatives are, without a leading `|`. -/
partial def patNode (src : Array Char) (p : Pattern) (q : Fren.Core.Pat) : Fren.Core.PatNode Span :=
  let ps : Array Pattern := match p with
    | .or _ alts => alts
    | .variant _ _ (some args) => args
    | _ => #[]
  let qs : Array Fren.Core.Pat := match q with
    | .or qs | .ctor _ qs => qs
    | _ => #[]
  let sp := match p with
    | .or _ alts => alts[0]!.span.to alts.back!.span
    | p => p.span
  .mk q (Fren.Core.textOf src (toRange sp)) sp ((ps.zip qs).map fun (a, b) => patNode src a b)

/-- The lints of each or-pattern within the pattern `n`, of a `match` arm
or of `is` (`Reqs/Lint/Complexity/Patterns`): `wildcard_in_or_patterns`,
`manual_range_patterns` and `unnested_or_patterns`. -/
def lintOrPatterns (n : Fren.Core.PatNode Span) : M Unit := do
  for o in n.orPatterns do
    let alts := o.kids
    if Fren.Core.wildcardInOr (alts.any (·.pat matches .wild false)) then
      lintFix .wildcardInOrPatterns o.at_ Fren.Core.wildcardInOrMsg
    else if let some fixed := Fren.Core.manualRangeFix? (alts.map fun a => (a.pat, a.text)) then
      lintFix .manualRangePatterns o.at_ (Fren.Core.manualRangeMsg fixed)
    else
      for (i, j, fixed) in Fren.Core.unnestedRuns alts do
        lintFix .unnestedOrPatterns (alts[i]!.at_.to alts[j]!.at_) (Fren.Core.unnestedOrMsg fixed)

/-- The name that the binder written `x` declares, without its `!`. -/
def binderName (x : Ident) : String := (declaredIdent x).1.name

/-- `collapsible_match` on the arm `i` of the `match` `e`, whose patterns
are `pats` (`lint::collapsible_match`): the arm's pattern is one variant
whose payload's patterns are `_` or binders, and its body a `match` on one
of those binders. -/
def lintCollapsible (cx : ExprCtx) (arms : Array (Pattern × Option Expr × Expr)) (pats : Array Fren.Core.Pat) (i : Nat) : M Unit := do
  let src := (← get).src
  let (p, _, body) := arms[i]!
  let .variant _ segs (some args) := p | return
  let .ctor _ qs := pats[i]! | return
  let .match inner (.path _ #[x]) innerArms false := body | return
  -- An arm with a guard may not be taken where its pattern matches.
  if arms.any (·.2.1.isSome) || innerArms.any (·.2.1.isSome) then return
  let binders := (args.zip qs).filterMap fun
    | (.variant _ #[b] none, .wild true) => some (binderName b)
    | _ => none
  let isX : Pattern × Fren.Core.Pat → Bool
    | (.variant _ #[b] none, .wild true) => binderName b == x.name
    | _ => false
  let some k := (args.zip qs).findIdx? isX | return
  let flat := qs.all (· matches .wild _)
  let innerWildcard := innerArms.back?.any (·.1 matches .wild _)
  -- The first later arm that matches a value of the variant: one with `_`
  -- or a binder among its alternatives, since an arm that names the variant
  -- after this one is unreachable.
  let wild? := ((List.range arms.size).filter (· > i)).find? fun j => pats[j]!.top.any (· matches .wild _)
  let some d := innerArms.back? | return
  let sameWildcard := wild?.any fun j => pats[j]! matches .wild false &&
    Fren.Core.writtenSame (arms[j]!.2.2.text src).text (d.2.2.text src).text
  -- The inner `_` arm's body is taken where the outer one's is after the
  -- fix, outside the arm's pattern, so it must mention none of its binders.
  let dText := (d.2.2.text src).text
  let mentioned := Fren.Core.mentionsName (← srcAt { start := x.span.stop, stop := inner.stop }) x.name ||
    binders.any (Fren.Core.mentionsName dText ·)
  let innerBinders ← innerArms.flatMapM fun (q, _, _) => return (← patternBinders cx q).map binderName
  let clash := innerBinders.any binders.contains
  unless Fren.Core.collapsibleMatch true flat innerWildcard sameWildcard mentioned clash innerArms.size do return
  let armRange : Fren.Core.Range := { start := p.span.start, stop := (Fren.Core.withParens src (toRange body.span)).stop }
  let commented := Fren.Core.hasComment (Fren.Core.textOf src armRange)
  let path ← srcAt (segs[0]!.span.to segs.back!.span)
  let argTexts ← args.mapM (srcAt ·.span)
  let innerTexts ← (innerArms.pop).mapM fun (q, _, b) => do
    return (" | ".intercalate (← q.alts.mapM (srcAt ·.span)).toList, (b.text src).text)
  let fixed := Fren.Core.collapsedArms path argTexts k innerTexts
  let msg := Fren.Core.collapsibleMatchMsg x.name (if commented then none else some fixed)
  -- The fix replaces the outer arm, and the message is at the inner `match`.
  lintFix .collapsibleMatch inner { msg with fixes := msg.fixes.map ({ · with range? := some armRange }) }

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Fren.Core.Pat.flat`), where no arm overlaps another without
containing it. -/
def lintMatch (cx : ExprCtx) (e : Expr) (ty : Ty) (pats : Array Fren.Core.Pat) (slot : Option Fren.Core.Slot) :
    M Unit := do
  let .match span scrutinee arms isTable := e | return
  let src := (← get).src
  -- A table over a scrutinee is called a table (`Fren.Core.Msg.ofTable`).
  let tm (m : Fren.Core.Msg) : Fren.Core.Msg := if isTable then m.ofTable else m
  -- An arm with a guard may not be taken where its pattern matches, so
  -- the lints that move, merge or remove arms, or replace the `match`,
  -- look only at a `match` without guards, and the arms with guards name
  -- no variant for the lints of `_` (`Reqs/Lint/Pedantic/Matches#arms`).
  let guarded := arms.map (·.2.1.isSome)
  let anyGuard := guarded.any id
  let mut infos : Array Fren.Core.ArmInfo := #[]
  for (p, _, body) in arms, pat in pats do
    let alts := if p matches .wild _ then #[] else p.alts.map fun a => Fren.Core.textOf src (toRange a.span)
    let binds := !(← patternBinders cx p).isEmpty
    infos := infos.push { alts, binds, noPayload := pat.noPayload, equatable := Fren.Core.equatable pat alts
                          disjoint := alts.isEmpty || Fren.Core.disjointPat pat alts, body := body.text src }
  let flat := pats.all (·.flat)
  -- `trivial_match` (`lint::trivial_match`).
  if let #[info] := infos then
    if Fren.Core.trivialMatch infos.size info.binds && !anyGuard then
      lintFix .trivialMatch span (tm (Fren.Core.trivialMatchMsg (info.body.inSlot slot (← followedSpan span))))
  -- `needless_match` (`lint::needless_match`).
  let st ← get
  let scr ← srcAt scrutinee.span
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  -- Only a `match` whose arms are `_` and variants whose payloads'
  -- patterns are `_` or binders.
  let ep := match ty with
    | .enum p _ => p
    | _ => .anonymous
  for (p, _, body) in arms, pat in pats do
    match p, pat with
    | _, .wild false =>
      wildcard := true
      scrutineeBack := Fren.Core.writtenSame (← srcAt body.span) scr
    | .variant _ _ args?, .ctor idx qs =>
      unless qs.all (· matches .wild _) do givenBack := false; continue
      let binders := (args?.getD #[]).map fun
        | .variant _ #[x] none => x.name
        | _ => "_"
      -- The arm's binders shadow items in its body.
      let shadowing := cx.shadowing ++ (binders.filter (· != "_")).map Name.mkSimple
      let (segs?, args) := match body with
        | .path _ segs => (some segs, #[])
        | .app _ segs args => (some segs, args)
        | _ => (none, #[])
      let same := segs?.any fun segs => match st.table.resolvePath st.scope (segNames segs) shadowing with
        | .ok (.variant en i) => en.path == ep && i == idx
        | _ => false
      unless Fren.Core.givesBack same binders (← args.mapM (srcAt ·.span)) do givenBack := false
    | _, _ => givenBack := false
  let trivial := Fren.Core.trivialMatch infos.size (infos[0]?.any (·.binds))
  let needless := Fren.Core.needlessMatch (givenBack && !anyGuard) wildcard scrutineeBack trivial
  if needless then
    let bare : Fren.Core.BText := { text := scr, prec := scrutinee.boolNode.kind.prec }
    lintFix .needlessMatch span (tm (Fren.Core.needlessMatchMsg (bare.inSlot slot (← followedSpan span))))
  let bodyRanges := arms.map fun (_, _, b) => Fren.Core.withParens src (toRange b.span)
  let armRanges := arms.zipWith (fun (p, _) (b : Fren.Core.Range) => { start := p.span.start, stop := b.stop }) bodyRanges
  let groups := if flat && !anyGuard then Fren.Core.sameArmGroups infos else #[]
  let mut firstSame? : Option Span := none
  if flat && !anyGuard then
    let edits := Fren.Core.sameArmsEdits (toRange span) infos armRanges (arms.map (toRange ·.1.span)) bodyRanges slot (← followedSpan span)
    for g in groups do
      let (i, msg) := Fren.Core.sameArmsMsg infos g slot (← followedSpan span)
      let at_ : Span := { start := armRanges[i]!.start, stop := armRanges[i]!.stop }
      lintEdits .matchSameArms at_ (tm msg) (if firstSame?.isNone then edits else #[])
      if firstSame?.isNone then firstSame? := some at_
  let scr := scrutinee.text src
  let membership? := if anyGuard then none else Fren.Core.membershipParts? infos scr slot
  if let some (pre, post, test) := membership? then
    let r := Fren.Core.withParens src (toRange scrutinee.span)
    lintEdits .matchLikeMembership span (tm (Fren.Core.membershipMsg (pre ++ scr.text ++ post) test))
      #[({ start := span.start, stop := r.start }, pre), ({ start := r.stop, stop := span.stop }, post)]
  -- `single_match_else` (`lint::single_match_else`).
  let followed ← followedSpan span
  if let some fixed := (if anyGuard then none else
      Fren.Core.singleMatchElseFix? infos scr slot (membership?.isSome || needless || trivial) followed (ty == .bool)) then
    lintFix .singleMatchElse span (tm (Fren.Core.singleMatchElseMsg fixed (Fren.Core.hasComment (← srcAt span))))
  -- `match_bool` (`lint::match_bool`).
  if ty == .bool && !anyGuard then
    if let some fixed := Fren.Core.matchBoolFix? pats infos scr.text slot (membership?.isSome || trivial) (← followedSpan span) then
      lintFix .matchBool span (tm (Fren.Core.matchBoolMsg fixed (Fren.Core.hasComment (← srcAt span))))
  -- `match_overlapping_arm` (`lint::match_overlapping_arm`). An arm with a
  -- guard is left out, as in Clippy; the arms of a table over a scrutinee
  -- are checked to be disjoint instead.
  let intervals := (pats.zip guarded).map fun (p, g) => p.top.map fun
    | .int lo hi => if g || isTable then none else some (lo, hi)
    | _ => none
  for ((j, b), (i, a)) in Fren.Core.overlappingArms intervals do
    lint .matchOverlappingArm arms[j]!.1.alts[b]!.span (Fren.Core.overlappingArmMsg (← srcAt arms[i]!.1.alts[a]!.span))
  unless isTable do
    for i in [0:arms.size] do lintCollapsible cx arms pats i
  for (p, _, _) in arms, q in pats do lintOrPatterns (patNode src p q)
  -- In a table over a scrutinee, `_` also takes what the guards of the
  -- other arms leave, which no pattern can name without overlapping them.
  unless flat && !(isTable && anyGuard) do return
  let .enum ep _ := ty | return
  let some d := (← get).dataOf? ep | return
  let some w := (Array.range arms.size).find? fun i => arms[i]!.1 matches .wild _ && !guarded[i]! | return
  let names (p : Fren.Core.Pat) : Array Nat := match p with
    | .ctor k _ => #[k]
    | .or alts => alts.filterMap fun | .ctor k _ => some k | _ => none
    | _ => #[]
  let unguarded := (pats.zip guarded).filterMap fun (p, g) => if g then none else some p
  let covered := ((List.range d.ctors.size).filter fun k => !unguarded.any (names · |>.contains k)).toArray
  let siblings := (arms.flatMap (·.1.alts)).filterMap fun | .variant _ segs _ => some (segs.map (Name.mkSimple ·.name)) | _ => none
  let st ← get
  -- The pattern that names each variant that `_` matches, if one resolves.
  let named := covered.map fun k => (st.table.variantPath? st.scope cx.shadowing d.path d.ctors[k]!.1 siblings).map
    (Fren.Core.variantPattern · d.ctors[k]!.2.size)
  -- Removing an arm into `_` makes it cover more variants.
  let unless? := if groups.any (Fren.Core.groupFix infos · == .remove) then firstSame?.map (.matchSameArms, ·) else none
  -- `wildcard_enum_match_arm` (`lint::wildcard_enum_match_arm`).
  let (_, fixable) := Fren.Core.wildcardEnumMatchArm true (named.filter (·.isNone)).size
  let pattern? := if fixable then some (" | ".intercalate (named.filterMap id).toList) else none
  lintFix .wildcardEnumMatchArm arms[w]!.1.span (tm (Fren.Core.wildcardEnumMsg (covered.map (d.path ++ d.ctors[·]!.1)) pattern?))
    unless?
  unless Fren.Core.wildcardSingle covered.size do return
  lintFix .wildcardSingleVariant arms[w]!.1.span (tm (Fren.Core.wildcardMsg (d.path ++ d.ctors[covered[0]!]!.1) named[0]!)) unless?

/-- `match_could_be_table` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_could_be_table`): the fix writes
`table` in place of the keyword. -/
def lintCouldBeTable (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) : M Unit := do
  let .match span _ arms false := e | return
  let guarded := arms.map (·.2.1.isSome)
  unless Fren.Core.matchCouldBeTable arms.size (guarded.any id) (Fren.Core.acceptedAsTable sigs pty pats guarded) do return
  let keyword : Fren.Core.Range := { start := span.start, stop := span.start + "match".length }
  unless (← srcAt { start := keyword.start, stop := keyword.stop }) == "match" do return
  let msg := Fren.Core.matchCouldBeTableMsg
  lintFix .matchCouldBeTable span { msg with fixes := msg.fixes.map ({ · with range? := some keyword }) }

/-- The value that the guard operand `v` is, as `redundant_guards` reads it,
with its text in a pattern and in an expression: a literal, or a variant
without a payload, which is written by its path (`Fren.Core.Table.variantPath?`). -/
def guardValue (cx : ExprCtx) (extra : Array Name) (sigs : Fren.Core.Sigs) (siblings : Array (Array Name)) (v : Expr) :
    M (Fren.Core.GuardValue × String × String) := do
  let other := (Fren.Core.GuardValue.other, "", "")
  match v with
  | .bool _ b => return (.pattern (.bool b), toString b, toString b)
  | .num _ n => return (.pattern (.int (some n) (some n)), toString n, toString n)
  | .neg _ (.num _ n) => return (.pattern (.int (some (-(n : Int))) (some (-(n : Int)))), s!"-{n}", s!"(-{n})")
  | .str sp t => let w ← srcAt sp; return (.pattern (.str t), w, w)
  | .path _ segs =>
    let st ← get
    let shadowing := cx.shadowing ++ extra
    let .ok (.variant en i) := st.table.resolvePath st.scope (segNames segs) shadowing | return other
    unless ((sigs en.path)[i]?.map (·.2.size)) == some 0 do return other
    let some path := st.table.variantPath? st.scope shadowing en.path en.variants[i]! siblings | return other
    let t := Fren.Core.variantPattern path 0
    return (.pattern (.ctor i #[]), t, t)
  | _ => return other

/-- `trivial_guard` and `redundant_guards` on the arms of the `match` `e`,
whose patterns are `pats`, on a value of `pty` (`lint::trivial_guard`,
`lint::redundant_guards`): each fix is given only where the static rules
accept the `match` after it (`Fren.Core.matchAccepted`). -/
def lintGuards (cx : ExprCtx) (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) :
    M Unit := do
  let .match _ _ arms isTable := e | return
  let src := (← get).src
  let tm (m : Fren.Core.Msg) : Fren.Core.Msg := if isTable then m.ofTable else m
  let guarded := arms.map (·.2.1.isSome)
  let siblings := (arms.flatMap (·.1.alts)).filterMap fun | .variant _ segs _ => some (segs.map (Name.mkSimple ·.name)) | _ => none
  let bodyStop (i : Nat) : Nat := (Fren.Core.withParens src (toRange arms[i]!.2.2.span)).stop
  for h : i in [0:arms.size] do
    let (p, g?, body) := arms[i]
    let some g := g? | continue
    let gStop := (Fren.Core.withParens src (toRange g.span)).stop
    -- `trivial_guard` (`lint::trivial_guard`).
    if let .bool _ b := g then
      let accepted := if b then Fren.Core.matchAccepted sigs pty pats (guarded.set! i false) isTable
        else Fren.Core.matchAccepted sigs pty (pats.eraseIdxIfInBounds i) (guarded.eraseIdxIfInBounds i) isTable
      -- What the fix removes: the guard, from the pattern's end; or the
      -- arm, up to the next one, or from the previous one's end.
      let removed : Fren.Core.Range := if b then { start := p.span.stop, stop := gStop }
        else if i + 1 < arms.size then { start := p.span.start, stop := arms[i + 1]!.1.span.start }
        else if i > 0 then { start := bodyStop (i - 1), stop := bodyStop i }
        else { start := p.span.start, stop := bodyStop i }
      let (_, fix) := Fren.Core.trivialGuard (.literal b) accepted (Fren.Core.hasComment (Fren.Core.textOf src removed))
      let msg := tm (Fren.Core.trivialGuardMsg b fix !accepted)
      lintFix .trivialGuard g.span { msg with fixes := msg.fixes.map ({ · with range? := some removed }) }
      continue
    -- `redundant_guards` (`lint::redundant_guards`).
    let .bin _ "=" l r := g | continue
    let bs ← patternBinders cx p
    let binders := bs.map binderName
    let soleName? : Expr → Option String
      | .path _ #[n] => some n.name
      | _ => none
    let some (x, v) := #[(l, r), (r, l)].findSome? fun (a, b) => (soleName? a).bind fun n =>
      if binders.contains n then some (n, b) else none | continue
    let (value, inPattern, inExpr) ← guardValue cx (binders.map Name.mkSimple) sigs siblings v
    let some q := Fren.Core.redundantGuard? pats[i]! (Fren.Core.guardBinderPath? pats[i]! (binders.idxOf? x)) value | continue
    unless Fren.Core.matchAccepted sigs pty (pats.set! i q) (guarded.set! i false) isTable do continue
    let some bx := bs.find? (binderName · == x) | continue
    let pattern := Fren.Core.textOf src { start := p.span.start, stop := bx.span.start } ++ inPattern ++
      Fren.Core.textOf src { start := bx.span.stop, stop := p.span.stop }
    let bodyText := Fren.Core.textOf src (Fren.Core.withParens src (toRange body.span))
    let head : Fren.Core.Range := { start := p.span.start, stop := gStop }
    let commented := Fren.Core.hasComment (Fren.Core.textOf src head)
    let why := "note: the fix would drop the comments in the arm's pattern or guard, so it has none"
    let (fixed?, why?) :=
      if !Fren.Core.mentionsName bodyText x then
        if commented then (none, some why) else (some (pattern, head), none)
      else match Fren.Core.replaceMentions? bodyText x inExpr with
        | some b' => if commented then (none, some why)
          else (some (s!"{pattern} => {b'}", { head with stop := bodyStop i }), none)
        | none => (none, some s!"note: the body mentions `{x}` where its value cannot be written in its place, so it has no fix")
    let msg := tm (Fren.Core.redundantGuardsMsg x (← srcAt v.span) (fixed?.map (·.1)) why?)
    lintFix .redundantGuards g.span { msg with fixes := msg.fixes.map ({ · with range? := fixed?.map (·.2) }) }

/-- `match_arm_if_else` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_arm_if_else`): the fix moves each
condition into its arm's guard, and adds a `_` arm with the `else` branch
where the last arm is not one. -/
def lintArmIfElse (cx : ExprCtx) (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) :
    M Unit := do
  let .match _ _ arms false := e | return
  if arms.any (·.2.1.isSome) then return
  let src := (← get).src
  let mut infos : Array (Fren.Core.IfArmInfo String) := #[]
  let mut binders : Array (Array String) := #[]
  for (p, _, body) in arms, q in pats do
    let armBody : Fren.Core.IfArmBody String := match body with
      | .ite _ _ _ d => .ifElse (d.text src).text
      | _ => .plain (body.text src).text
    -- A condition that binds names cannot be a guard (`F0334`).
    let condBinds ← match body with
      | .ite _ c _ _ => chainBinds cx c
      | _ => pure false
    binders := binders.push ((← patternBinders cx p).map binderName)
    infos := infos.push { wild := q matches .wild _, body := armBody, binds := condBinds }
  -- `d` names a binder of arm `j`'s pattern.
  let mentions (d : String) (j : Nat) : Bool := binders[j]!.any (Fren.Core.mentionsName d ·)
  let overlap (i j : Nat) : Bool := (pats[i]!.overlapWit? sigs pty pats[j]!).isSome
  let some (group, d, append) := Fren.Core.matchArmIfElse? Fren.Core.writtenSame mentions overlap infos.toList
    | return
  let guarded := (Array.range arms.size).map group.contains
  let (pats', guarded') := if append then (pats.push (.wild false), guarded.push false) else (pats, guarded)
  unless Fren.Core.matchAccepted sigs pty pats' guarded' false do return
  let bodyStop (i : Nat) : Nat := (Fren.Core.withParens src (toRange arms[i]!.2.2.span)).stop
  let part (e : Expr) : M String := return Fren.Core.rowPart (← srcAt e.span) (e matches .when .. | .quant .. | .«let» ..)
  let mut edits : Array (Fren.Core.Range × String) := #[]
  let mut commented := false
  for i in group do
    let (p, _, body) := arms[i]!
    let .ite _ c a _ := body | return
    let r : Fren.Core.Range := { start := p.span.stop, stop := bodyStop i }
    commented := commented || Fren.Core.hasComment (Fren.Core.textOf src r)
    edits := edits.push (r, s!" if {← part c} => {← part a}")
  if append then
    let .ite _ _ _ de := arms[group[0]!]!.2.2 | return
    let stop := bodyStop (arms.size - 1)
    edits := edits.push ({ start := stop, stop }, s!", _ => {← part de}")
  let msg := Fren.Core.matchArmIfElseMsg group.size d commented
  let at_ := arms[group[0]!]!.2.2.span
  if commented then lint .matchArmIfElse at_ msg else lintEdits .matchArmIfElse at_ msg edits

/-! ## Patterns -/

/-- A binder of a pattern, with the type of its value, and its value, read
from the scrutinee with selectors. -/
structure PBinder where
  source? : Option Expr := none
  ident : Ident
  ty : Ty
  smt : String
  /-- Bound from a payload of the scrutinee, directly or nested, rather
  than to the whole scrutinee. -/
  payload : Bool := false
  deriving Inhabited

/-- The variants of each enumeration, with their payloads' types, as
patterns see them. -/
def patSigs : M Fren.Core.Sigs := do
  let st ← get
  return fun p => ((st.dataOf? p).map fun d => d.ctors.map fun (c, fs) => (c, fs.map (·.2.patTy))).getD #[]

/-- The conjunction of `ts` in SMT-LIB, `none` for none. -/
def smtConj (ts : Array String) : Option String :=
  match ts with
  | #[] => none
  | #[t] => some t
  | ts => some s!"(and {" ".intercalate ts.toList})"

/-- The value of the bound `b` of a range pattern. -/
def boundValue (cx : ExprCtx) (b : Bound) : M Int := do
  match b with
  | .num _ v => return v
  | .path sp segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      if cx.vars.any (·.name == n.getRoot) then err sp (Fren.Core.rangeBoundMsg "a variable")
      if (cx.binder? n.getRoot).isSome then err sp (Fren.Core.rangeBoundMsg "a binder")
    match ← resolve segs cx.shadowing with
    | .item { kind := .constItem, path, .. } =>
      let some (_, t) := (← get).consts.find? path | internal sp s!"unknown constant `{path}`"
      unless t matches .int | .nat do err sp (Fren.Core.rangeBoundMsg s!"a constant of `{t.show}`")
      let some v := (← get).constInts.find? path | err sp (Fren.Core.rangeConstantMsg path)
      return v
    | r => err sp (Fren.Core.rangeBoundMsg r.describe)

/-- Resolves the pattern `p` of a value of type `ty`, which is `x` in
SMT-LIB (`Reqs/Lang/Patterns`), within an or-pattern if `inOr`: the
pattern, its binders in preorder, and its test, `none` if it matches every
value. In a pattern test (`test`), a binder is reported once the pattern is
resolved, rather than within an or-pattern. -/
partial def resolvePattern (cx : ExprCtx) (ty : Ty) (x : String) (inOr test : Bool) (p : Pattern) :
    M (Fren.Core.Pat × Array PBinder × Option String) := do
  let wrong (sp : Span) (what : String) : M Unit := err sp (Fren.Core.patternTypeMsg ty.show what)
  match p with
  | .wild _ => return (.wild, #[], none)
  | .str sp v =>
    unless ty == .string do wrong sp "a pattern of `String`"
    liftMsg sp (Fren.Core.checkStringChars v)
    modify fun s => { s with usesStrings := true }
    return (.str v, #[], some s!"(= {x} {Fren.Core.smtStringLit v})")
  | .num sp v =>
    unless ty matches .int | .nat do wrong sp "a pattern of `Int`"
    return (.int v v, #[], some s!"(= {x} {smtInt v})")
  | .range sp lo hi inclusive =>
    unless ty matches .int | .nat do wrong sp "a pattern of `Int`"
    let lo' ← lo.mapM (boundValue cx)
    let hi' ← hi.mapM (boundValue cx)
    if Fren.Core.rangeEmpty lo' hi' inclusive then err sp (Fren.Core.emptyRangeMsg (← srcAt sp))
    let (l, h) := Fren.Core.rangeInterval lo' hi' inclusive
    return (.int l h, #[], smtConj (l.toArray.map (s!"(<= {smtInt ·} {x})") ++ h.toArray.map (s!"(<= {x} {smtInt ·})")))
  | .variant sp segs args? =>
    if segs.size == 1 && args?.isNone then
      match ← patternName cx segs[0]! with
      | .boolLiteral =>
        unless ty == .bool do wrong sp "a pattern of `Bool`"
        let b := segs[0]!.name == "true"
        return (.bool b, #[], some (if b then x else s!"(not {x})"))
      | .binder =>
        if inOr && !test then err sp (Fren.Core.orBinderMsg (Name.mkSimple (declaredIdent segs[0]!).1.name))
        return (.wild true, #[{ ident := segs[0]!, ty, smt := x }], none)
      | .variant => pure ()
    let r ← resolveWritten segs cx.shadowing cx.noteIndexes
    let .enum ep tyArgs := ty
      | err sp (Fren.Core.patternTypeMsg ty.show (match r with
          | .variant en _ => s!"a pattern of `{showPath en.path}`"
          | r => r.describe))
    let .variant en idx := r | err sp (Fren.Core.notAVariantOfMsg ep r.describe)
    if en.path != ep then err sp (Fren.Core.notAVariantOfMsg ep s!"a variant of `{showPath en.path}`")
    let some d := (← get).dataOf? ep | internal sp s!"unknown enum `{ep}`"
    -- The payload's types, with the scrutinee's arguments (`lang::instantiation`).
    let (c, fs) := (d.instCtors tyArgs)[idx]!
    let v := ep ++ en.variants[idx]!
    if let some msg := Fren.Core.variantMentionMsg? v fs.size args?.isSome then err sp msg
    let args := args?.getD #[]
    unless args.size == fs.size do err sp (Fren.Core.arityMsg v fs.size args.size "pattern")
    let mut pats := #[]
    let mut bs := #[]
    let mut tests := #[d.tester idx x tyArgs]
    for a in args, (_, t) in fs, k in [0:args.size] do
      let (q, qbs, qt) ← resolvePattern cx t s!"({d.selSym c k} {x})" inOr test a
      pats := pats.push q
      bs := bs ++ qbs.map ({ · with payload := true })
      tests := tests ++ qt.toArray
    return (.ctor idx pats, bs, smtConj tests)
  | .or _ alts =>
    let mut pats := #[]
    let mut bs := #[]
    let mut tests := #[]
    let mut every := false
    for a in alts do
      let (q, qbs, qt) ← resolvePattern cx ty x true test a
      pats := pats.push q
      bs := bs ++ qbs
      match qt with
      | some t => tests := tests.push t
      | none => every := true
    return (.or pats, bs, if every then none else if tests.size == 1 then tests[0]? else some s!"(or {" ".intercalate tests.toList})")

/-- The variant that `e` names, if it is a path to one without a payload:
its enumeration, its index and its text. -/
def variantOf? (cx : ExprCtx) : Expr → M (Option (Name × Nat × String))
  | .path span segs => do
    let st ← get
    let .ok (.variant en idx) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return none
    unless ((st.dataOf? en.path).bind (·.ctors[idx]?)).any (·.2.isEmpty) do return none
    return some (en.path, idx, ← srcAt span)
  | _ => return none

/-- `e` as a test of which variant a scrutinee is, if it is one
(`Fren.Core.VariantTest`). -/
partial def variantTest? (cx : ExprCtx) : Expr → M (Option Fren.Core.VariantTest)
  | .bin _ "or" a b => do
    let some x ← variantTest? cx a | return none
    let some y ← variantTest? cx b | return none
    return x.or y
  | .bin _ "=" l v => do
    let some (en, i, t) ← variantOf? cx v | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := #[(i, t)] }
  | .is _ l p => do
    -- `x is P`, of the variants that `P` names, each with only `_` in its
    -- payload, so that it tests the variant alone.
    let st ← get
    let mut out : Array (Nat × String) := #[]
    let mut en? : Option Name := none
    for alt in p.alts do
      let .variant span segs args := alt | return none
      unless (args.getD #[]).all (· matches .wild _) do return none
      let .ok (.variant en i) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return none
      unless en?.all (· == en.path) do return none
      en? := some en.path
      out := out.push (i, ← srcAt span)
    let some en := en? | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := out }
  | .bin _ "in" l (.set _ vs) => do
    let mut out : Array (Nat × String) := #[]
    let mut en? : Option Name := none
    for v in vs do
      let some (en, i, t) ← variantOf? cx v | return none
      unless en?.all (· == en) do return none
      en? := some en
      out := out.push (i, t)
    let some en := en? | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := out }
  | _ => return none

/-- The tests, the branches and the final `else` of a chain of `if`. -/
partial def ifChain : Expr → Array Expr × Array Expr × Expr
  | .ite _ c a b => let (cs, as, z) := ifChain b; (#[c] ++ cs, #[a] ++ as, z)
  | z => (#[], #[], z)

/-- The text of `e` as the body of a `match` arm. -/
def armBodyOf (e : Expr) : M String := return Fren.Core.armBody (← srcAt e.span) (e matches .when .. | .quant ..)

/-- The text of `e` as a row's condition or value in a table. -/
def rowPartOf (e : Expr) : M String := return Fren.Core.rowPart (← srcAt e.span) (e matches .when .. | .quant .. | .«let» ..)

/-- `if_chain_match` and `manual_table` on the chain of `if` that starts at
`e` (`lint::if_chain_match`, `lint::manual_table`). -/
def lintIfChain (cx : ExprCtx) (e : Expr) : M Unit := do
  let (cs, as, z) := ifChain e
  -- A table's row does not see what its condition's pattern tests bind
  -- (`lang::test_scope`).
  if ← cs.anyM (chainBinds cx) then return
  let ts? := Fren.Core.sameScrutinee (← cs.mapM (variantTest? cx))
  let ts := ts?.getD #[]
  let enums := (← get).table.enums
  let n := ((ts[0]?.bind fun t => enums.get? t.enum).map (·.variants.size)).getD 0
  let (fires, wildcard) := Fren.Core.ifChainMatch cs.size ts?.isSome (Fren.Core.repeatedVariants ts)
    (Fren.Core.untestedVariants n ts)
  -- `manual_table` (`lint::manual_table`).
  if Fren.Core.manualTable cs.size ts?.isSome then
    lint .manualTable e.span (Fren.Core.manualTableMsg (← cs.mapM rowPartOf) (← as.mapM rowPartOf) (← rowPartOf z))
  unless fires do return
  let final? ← if wildcard then some <$> armBodyOf z else pure none
  lintFix .ifChainMatch e.span (Fren.Core.ifChainMatchMsg ts (← as.mapM armBodyOf) final?)

/-- `redundant_bindings` on the binding, or field, `b := e`
(`lint::redundant_bindings`). -/
def lintRedundant (b : Ident) (e : Expr) (field : Bool) : M Unit := do
  let after := (Fren.Core.withoutComments (← srcAt { start := b.span.stop, stop := e.span.stop })).trimAscii.toString
  let value := String.ofList (after.toList.drop 2)
  if after.startsWith ":=" && Fren.Core.redundantBinding (Fren.Core.writtenForm b.name) (Fren.Core.writtenForm value) then
    lintFix .redundantBindings (b.span.to e.span) (Fren.Core.redundantBindingMsg b.name field)

/-- The generic enumeration or record that `e` builds, if it builds one
(`Reqs/Lang/Generics#type-arguments`): its declaration, the constructor's
index, its values' declared types, and its values in their order, a
record's fields in the order of its declaration, `none` for one that is not
given. -/
def construction? (cx : ExprCtx) (e : Expr) : M (Option (DataDecl × Nat × Array Ty × Array (Option Expr))) := do
  let st ← get
  let variant (segs : Array Ident) (vals : Array Expr) : Option (DataDecl × Nat × Array Ty × Array (Option Expr)) := do
    let .ok (.variant en idx) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | none
    let d ← st.dataOf? en.path
    guard !d.params.isEmpty
    let (_, fs) ← d.ctors[idx]?
    return (d, idx, fs.map (·.2), vals.map some)
  match e with
  | .path _ segs => return variant segs #[]
  | .app _ segs args => return variant segs args
  | .record _ tySegs fields =>
    let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath st.scope (segNames tySegs) cx.shadowing
      | return none
    let some d := st.dataOf? path | return none
    if d.params.isEmpty then return none
    let fs := d.ctors[0]!.2
    return some (d, 0, fs.map (·.2), fs.map fun (f, _) =>
      (fields.find? (Name.mkSimple ·.1.name == f)).map fun (fi, e?) => e?.getD (.path fi.span #[fi]))
  | _ => return none

/-- `e`'s shape, for whether it synthesizes a type (`Fren.Core.TypeShape`). -/
partial def typeShape (cx : ExprCtx) (e : Expr) : M Fren.Core.TypeShape := do
  if let some (d, _, declared, vals) ← construction? cx e then
    let shapes ← vals.mapM fun v? => match v? with
      | some v => typeShape cx v
      | none => pure .other
    return Fren.Core.constructionShape d.params declared shapes
  -- An application of a generic function (`Reqs/Lang/GenericFunctions#applications`).
  if let .app _ segs args := e then
    let st ← get
    if let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing then
      if let some g := st.genericFns.find? path then
        return Fren.Core.callShape g.params.size g.declared g.result (← args.mapM (typeShape cx))
      if let some h := (st.hofs.find? path).filter (!·.typeParams.isEmpty) then
        return Fren.Core.callShape h.typeParams.size (h.params.map (·.2.2.ty)) h.result (← args.mapM (typeShape cx))
  match e with
  | .set _ #[] | .seq _ #[] => return .emptyLiteral
  | .set _ es | .seq _ es => return .anyPart (← es.toList.mapM (typeShape cx))
  | .pair _ a b => return .pair (← typeShape cx a) (← typeShape cx b)
  | .bin _ op a b => if op == "union" || op == "inter" || op == "minus" || op == "++" then
      return .anyPart [← typeShape cx a, ← typeShape cx b] else return .other
  | .ite _ _ a b => return .anyPart [← typeShape cx a, ← typeShape cx b]
  | .match _ _ arms _ => return .anyPart (← arms.toList.mapM (typeShape cx ·.2.2))
  | .matches _ ss arms _ => if ss.isEmpty then return .other else return .anyPart (← arms.toList.mapM (typeShape cx ·.2.2))
  | .«let» _ _ body _ => return .anyPart [← typeShape cx body]
  | .table _ rows => return .anyPart (← rows.toList.mapM (typeShape cx ·.2.2))
  | _ => return .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (cx : ExprCtx) (e : Expr) : M Bool := return (← typeShape cx e).synthesizes

/-- Elaborates the values `vals` of a construction of the generic type `d`,
written `what`, at `span`, whose values have the declared types `declared`,
with `elabValue`, and returns their SMT-LIB terms and its type arguments, which
are inferred (`Fren.Core.inferConstruction`). `note k t` explains that
value `k` has the type `t`. -/
def elabConstruction (elabValue : ExprCtx → Expr → M (String × Ty)) (site : Fren.Core.ExprSite) (cx : ExprCtx) (d : DataDecl) (declared : Array Ty)
    (vals : Array Expr) (span : Span) (what : String) (note : Nat → Ty → String) : M (Array String × Array Ty) := do
  let expected? := match cx.expected? with
    | some (.enum p as) | some (.record p as) => if p == d.path then some as.toArray else none
    | _ => none
  let synth ← vals.mapM (synthesizes cx)
  let go : StateT (Array String) M (Array Ty) :=
    Fren.Core.inferConstruction d.params declared synth expected?
      (err span (Fren.Core.cannotInferMsg what (showPath d.path)) : M Unit)
      (fun k x? => do
        let (smt, t) ← (elabValue { cx with expected? := site.expected x? none } vals[k]! : M _)
        modify fun a => a.set! k smt
        return some t)
      (fun k x f => (liftMsg vals[k]!.span (Fren.Core.checkType x f (some (note k x))) : M Unit))
  let (args, smts) ← go.run (vals.map fun _ => "")
  return (smts, args)

/-- How `e` is written, for whether it is written as a sequence
(`Fren.Core.WrittenShape`). Parentheses are not kept in an `Expr`, so
none is `WrittenShape.parenthesized`. -/
partial def writtenShape : Expr → Fren.Core.WrittenShape
  | .seq .. => .seqLiteral
  | .bin _ "++" a b => .concat (writtenShape a) (writtenShape b)
  | .ite _ _ a b => .conditional (writtenShape a) (writtenShape b)
  | .match _ _ arms _ => .match (arms.toList.map (writtenShape ·.2.2))
  | .matches _ _ arms _ => .match (arms.toList.map (writtenShape ·.2.2))
  | .«let» _ _ body _ => .let (writtenShape body)
  | .table _ rows => .table (rows.toList.map (writtenShape ·.2.2))
  | _ => .other

/-- Whether `e` is written as a sequence, so that the right of `in` is
checked against a sequence (`lang::written_sequence`). -/
def seqShaped (e : Expr) : Bool := (writtenShape e).sequence

/-- The span of the type written `segs`, from its first token to its last:
a pattern's segment may come before its base's (`Parser.patOuterSeg`). -/
def typeSpan (segs : Array Ident) : Span :=
  { start := segs.foldl (fun m s => min m s.span.start) segs[0]!.span.start
    stop := segs.foldl (fun m s => max m s.span.stop) 0 }

/-- The constraint that a value of the declared type `t` brings
(`Fren.Core.PTy.cons`). -/
def consOf (t : Fren.Core.PTy) : M (Option Fren.Core.Cons) := do
  let s ← get
  return t.cons s.shapeOf

/-- `x`'s constraint of the type `t`, in SMT-LIB, if it has one. -/
def factOf (t : Fren.Core.PTy) (x : String) : M (Option String) := do
  let s ← get
  return (t.cons s.shapeOf).map (consSmt s.dataOf? · x)

/-- The span of the type written `segs`, as `typeSpan` gives it, with the
`>` of each `Set<`, `Seq<` and `Rel<` within it that it leaves out. -/
def writtenTypeSpan (segs : Array Ident) : M Span := do
  let src := (← get).src
  let sp := typeSpan segs
  let mut depth : Int := 0
  for c in src.extract sp.start sp.stop do
    if c == '<' then depth := depth + 1 else if c == '>' then depth := depth - 1
  let mut stop := sp.stop
  while depth > 0 && stop < src.size do
    if src[stop]! == '>' then depth := depth - 1
    stop := stop + 1
  return { sp with stop }

/-- The type that the path `segs` names, written at `span`, with the
declared type arguments `args`, as many as its type parameters
(`lang::type_arguments`); a type alias's type as declared. -/
def instanceTy (segs : Array Ident) (args : Array Fren.Core.PTy) (span : Span) : M Fren.Core.PTy := do
  let builtin := segs.size == 1 && #["Bool", "Int", "Nat", "String", "Set", "Seq", "Rel"].contains segs[0]!.name
  let fnParam := segs.size == 1 && ((← get).fnTypeParams.any (·.2.contains (Name.mkSimple segs[0]!.name)))
  if builtin || fnParam || (segs.size == 1 && (← get).typeParams.contains (Name.mkSimple segs[0]!.name)) then
    unless Fren.Core.writtenArgumentsAccepted (if builtin then .builtin else .parameter) 0 args.size do
      err span (Fren.Core.typeArgsMsg segs[0]!.name #[] args.size)
  let arity (named : Fren.Core.TypeNamed) (path : Name) (params : Array Name) : M Unit := do
    unless Fren.Core.writtenArgumentsAccepted named params.size args.size do
      err span (Fren.Core.typeArgsMsg (showPath path) params args.size)
  let tys := args.toList.map (·.ty)
  match ← resolveWritten segs with
  | .item { kind := .enumItem, path, .. } =>
    arity .data path ((((← get).dataOf? path).map (·.params)).getD #[])
    return { ty := .enum path tys, elems := args }
  | .item { kind := .recordItem, path, .. } =>
    if let some u := (← get).newtypes.find? path then
      arity .other path #[]
      return .plain (.newtype path u)
    arity .data path ((((← get).dataOf? path).map (·.params)).getD #[])
    return { ty := .record path tys, elems := args }
  | .item { kind := .typeItem, path, .. } =>
    arity .other path #[]
    if let some t := (← get).aliases.find? path then return t
    return .plain (.abstract path)
  | r => err span (Fren.Core.notATypeMsg r)

/-- A function type written `segs` at `site`, where it may not be
(`lang::function_type_place`); a function type within another is reported
where that one is elaborated. -/
def checkFnTypeSite (site : Fren.Core.TypeSite) (segs : Array Ident) : M Unit := do
  if segs[0]?.any (·.name == Parser.fnSeg) then err (typeSpan segs) (Fren.Core.fnTypePlaceMsg site [])

mutual
/-- The declared type written `segs`, with the invariants of the subset
types within it (`Reqs/Lang/Types#subset-types`). -/
partial def elabPTy (segs : Array Ident) : M Fren.Core.PTy := do
  -- A function type is only a defined function's parameter's, which
  -- `elabFnTy` elaborates (`lang::function_type_place`).
  if let some w := Fren.Core.fnTypeWithin (segs.toList.map (·.name)) then
    err (typeSpan segs) (Fren.Core.fnTypePlaceMsg .constant w)
  let t ← elabBasePTy segs
  let text := Fren.Core.typeText (← srcAt (← writtenTypeSpan segs))
  return { t with text }

/-- The declared type `segs`, which has no pattern of its own: a type
parameter, within the declaration of a generic type, or an instance of one,
`G<A, B>` (`Reqs/Lang/Generics#type-arguments`), whose type arguments are
declared types, with their patterns. -/
partial def elabBasePTy (segs : Array Ident) : M Fren.Core.PTy := do
  let span := segs[0]!.span.to segs.back!.span
  if let some i := segs.findIdx? (·.name == Parser.argsOpen) then
    if i > 0 && segs[0]!.name != Parser.setSeg && segs[0]!.name != Parser.seqSeg && segs[0]!.name != Parser.relSeg then
      let argSegs := Parser.splitArgs (segs.extract (i + 1) (segs.size - 1))
      let mut args := #[]
      for a in argSegs do
        let t ← elabPTy a
        let aspan := a[0]!.span.to a.back!.span
        -- An argument is never `Nat` (`lang::nat_place`), and is a payload's
        -- type (`Reqs/Lang/Generics#type-parameters`).
        unless t.ty != .nat || Fren.Core.natPlaceAccepted .argument do err aspan (Fren.Core.natPlaceMsg .argument)
        if let some p := t.ty.abstractWithin? then err aspan (Fren.Core.abstractFieldMsg p true (!(t.ty matches .abstract _)))
        args := args.push t
      let t ← instanceTy (segs.extract 0 i) args span
      -- A recursive enumeration's type arguments bring no constraints
      -- (`Reqs/Lang/Generics#subset-types-as-type-arguments`).
      if let .enum p _ := t.ty then
        if ((← get).shapeOf p).any (·.recursive) then
          for a in args, aSegs in argSegs do
            if (← consOf a).isSome then
              err (← writtenTypeSpan aSegs) (Fren.Core.recursiveArgumentMsg a.text (showPath p))
      -- Nor do they within an instance, once its arguments stand for its
      -- parameters.
      if let some p := t.ty.dataPath? then
        if let some (a, q) := Fren.Core.recursiveArgumentWithin? (← get).shapeOf p args then
          err (← writtenTypeSpan segs) (Fren.Core.recursiveArgumentMsg a.text (showPath q))
      return t
  if let some k := (← get).typeParams.idxOf? (Name.mkSimple segs[0]!.name) then
    if segs.size == 1 then return .plain (.param k (Name.mkSimple segs[0]!.name))
  -- A generic function's type parameter, an abstract type within it
  -- (`Reqs/Lang/GenericFunctions#type-parameters`).
  if let some (fn, ps) := (← get).fnTypeParams then
    if let some k := ps.idxOf? (Name.mkSimple segs[0]!.name) then
      if segs.size == 1 then return .plain (.abstract (Fren.Core.typeParamPath fn k ps[k]!))
  if segs.size == 1 && segs[0]!.name == "Bool" then return .plain .bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .plain .int
  if segs.size == 1 && segs[0]!.name == "Nat" then return .plain .nat
  if segs.size == 1 && segs[0]!.name == "String" then
    modify fun s => { s with usesStrings := true }
    return .plain .string
  -- An element type, which is never a `Nat` (`lang::nat_place`), nor a
  -- generic type's type parameter (`lang::element_parameter`), and whose
  -- constraint, if any, quantifies over the elements, outside the
  -- decidable core (`lang::subset_place`).
  let elem (segs : Array Ident) : M Fren.Core.PTy := do
    let t ← elabPTy segs
    if t.ty == .nat then err (typeSpan segs) (Fren.Core.natPlaceMsg .element)
    if let .param _ p := t.ty then
      unless Fren.Core.elementParamAccepted .datatype do err (typeSpan segs) (Fren.Core.typeParamPlaceMsg p .element "")
    if let .abstract p := t.ty then
      if let some n := Fren.Core.typeParamName? p then
        unless Fren.Core.elementParamAccepted .function do
          err (typeSpan segs) (Fren.Core.typeParamPlaceMsg (Name.mkSimple n) .element "")
    if (← consOf t).isSome then
      modify fun s => { s with outsideCore := true }
      lint .undecidable (typeSpan segs) Fren.Core.undecidableElementsMsg
    return t
  if segs[0]!.name == Parser.setSeg then
    modify fun s => { s with usesSets := true }
    let e ← elem (segs.extract 1)
    return { ty := .set e.ty, elems := #[e] }
  if segs[0]!.name == Parser.seqSeg then
    modify fun s => { s with usesSeqs := true }
    let e ← elem (segs.extract 1)
    return { ty := .seq e.ty, elems := #[e] }
  if segs[0]!.name == Parser.relSeg then
    modify fun s => { s with usesSets := true }
    let (a, b) := Parser.splitRel (segs.extract 1)
    let (pa, pb) := (← elem a, ← elem b)
    let (ta, tb) := (pa.ty, pb.ty)
    -- `zero_sized_map_values` (`lint::zero_sized_map_values`).
    if let .enum p _ := tb then
      if let some d := (← get).dataOf? p then
        if Fren.Core.zeroSizedMapValues true d.ctors.size (d.ctors.any (!·.2.isEmpty)) then
          let s ← get
          let text (xs : Array Ident) (stop : Nat) :=
            (String.ofList (s.src.extract (typeSpan xs).start stop).toList).trimAscii.toString
          let sep := segs[a.size + 1]!.span
          -- To the `>` after `B`.
          let mut stop := (typeSpan b).stop
          while stop < s.src.size && s.src[stop]! != '>' do stop := stop + 1
          lint .zeroSizedMapValues { start := segs[0]!.span.start, stop := stop + 1 }
            (Fren.Core.zeroSizedMapValuesMsg (text a sep.start) (text b (typeSpan b).stop) d.ctors[0]!.1.toString)
    return { ty := .rel ta tb, elems := #[pa, pb] }
  instanceTy segs #[] (segs[0]!.span.to segs.back!.span)
end

/-- The type of a quantifier's binder, written `segs`, which must not be a
procedure. -/
def binderTy (segs : Array Ident) : M Fren.Core.PTy := do
  let st ← get
  if let .ok (.item { kind := .compItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) #[] then
    err (segs[0]!.span.to segs.back!.span) (Fren.Core.quantifiedComponentMsg (showPath path))
  elabPTy segs

/-- The value `v` of the type `t` in SMT-LIB (`Fren.Core.PVal`). -/
partial def State.valueSmt (s : State) (t : Ty) (v : Fren.Core.PVal) : String :=
  match t, v with
  | _, .bool b => toString b
  | _, .int i => smtInt i
  -- Erased, as a newtype's values are.
  | .newtype _ u, .ctor _ #[w] => s.valueSmt u w
  | .enum p targs, .ctor idx args | .record p targs, .ctor idx args => Id.run do
    let some d := s.dataOf? p | return "?"
    -- With an instance's arguments for its type parameters.
    let (c, fs) := (d.instCtors targs)[idx]!
    return d.build targs c ((args.zip fs).toList.map fun (w, (_, ft)) => s.valueSmt ft w)
  | _, _ => "?"

/-- The values of the declared type `t` in SMT-LIB, and how many there are,
if a quantifier ranges over it (`lang::quantified_type`): a type whose
values bring no constraint as `State.values` lists them, and one that does,
those that meet it (`Fren.Core.PTy.values`). -/
def binderValues (t : Fren.Core.PTy) : M (Option (Nat × Array String)) := do
  let st ← get
  -- Only a listed type's values are listed (`lang::quantified_type`).
  unless (st.typeFacts t).listed do return none
  if (t.cons st.shapeOf).isNone then
    let some n := st.valueCount t.ty | return none
    return some (n, (st.values Fren.Core.maxInstances t.ty).getD #[])
  let some n := t.count? st.shapeOf | return none
  if n > Fren.Core.maxInstances then return some (n, #[])
  let vs := (t.values st.shapeOf Fren.Core.maxInstances).getD #[]
  return some (n, vs.map (st.valueSmt t.ty))

/-- A bound name of an unbounded quantifier, as the solver's quantifier
declares it: its symbol, its sort, and what its type brings of it, if
anything, as a formula (`Reqs/Cli#solver-queries`). -/
structure FreeBound where
  sym : String
  sort : String
  cons? : Option String

/-- The bound names of a quantifier's binders `bs`, declared in `cx`, every
combination of the values of those of listed types, as SMT-LIB terms, the
last name varying fastest (`Reqs/Lang/Quantifiers#meaning`), and those of
the other types, which the solver's quantifier binds
(`Reqs/Lang/Quantifiers#unbounded-quantifiers`). The names must be
distinct, follow the Boolean names rule and be written with `!` exactly
when they shadow (`lang::shadowing`), and the combinations be at most
`Fren.Core.maxInstances` (`lang::quantifier_size`). A bound name of a
listed type has a symbol that no variable has, which each instance
replaces; one of another type, the symbol `x#k` (`Fren.Core.boundSymbol`), with `k` its position
among the binders in scope, which the solver's quantifier binds, and which
`undecidable` reports at its binder (`lang::in_core`), unless `defer`,
for its caller to report at the spans returned last, once it knows whether
the quantifier is one over elements in the core
(`lang::element_quantifier`). -/
def quantBinders (cx : ExprCtx) (bs : Array Binder) (defer : Bool := false) :
    M (Array CBinder × Array (Array String) × Array FreeBound × Array Span) := do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := bs.flatMap (·.names)
  let declared := ids.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then err ids[k]!.span (Fren.Core.dupBoundMsg declared[k]!)
  let mut out : Array CBinder := #[]
  let mut sizes := #[]
  let mut listed := #[]
  let mut free := #[]
  let mut unlisted := #[]
  for b in bs do
    let pt ← binderTy b.ty
    let t := pt.ty
    let values? ← binderValues pt
    if values?.isNone then
      unlisted := unlisted.push b.span
      unless defer do
        modify fun s => { s with quantified := true }
        checkCore cx b.span .quantifier true true #[]
    for x in b.names do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        ((cx.binders ++ out).map (·.what)) cx.selfFn.isSome
      let y ← declare x locals
      let bn := Name.mkSimple y.name
      liftMsg y.span (Fren.Core.checkVarName bn (some (t == .bool)))
      lintName .binder bn y.span
      let k := cx.binders.size + out.size
      match values? with
      | some (n, vs) =>
        out := out.push { name := bn, smt := quote s!"{k} {bn}", ty := t, scrutinee := none, outer := k }
        sizes := sizes.push n
        listed := listed.push vs
      | none =>
        let sym := quote (Fren.Core.boundSymbol y.name k)
        let st ← get
        free := free.push { sym, sort := t.sort, cons? := (pt.cons st.shapeOf true).map (consSmt st.dataOf? · sym) }
        out := out.push { name := bn, smt := sym, ty := t, scrutinee := none, outer := k, unbounded := true }
  let n := cx.instances * Fren.Core.instanceCount sizes
  unless Fren.Core.quantifierSizeAccepted n do
    err (bs[0]!.span.to bs.back!.span) (Fren.Core.quantifierSizeMsg n (cx.instances > 1))
  return (out, listed.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]], free, unlisted)

/-- An operand of `=` or `!=`, as `lang::function_comparison` sees it: a
closure, the name of a function or of a function parameter, or a value. -/
def comparand (cx : ExprCtx) (e : Expr) : M Fren.Core.Comparand := do
  match e with
  | .closure .. | .matches _ #[] _ _ => return .closure
  | .path _ #[s] =>
    let n := identName s.name
    if (cx.fnParam? n).isSome then return .functionName
    if (cx.binder? n.getRoot).isSome || cx.vars.any (·.name.isPrefixOf n) then return .value
    let st ← get
    match st.table.resolvePath st.scope #[n] cx.shadowing with
    | .ok (.item { kind := .fnItem, .. }) => return .functionName
    | _ => return .value
  | .path _ segs =>
    let st ← get
    match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
    | .ok (.item { kind := .fnItem, .. }) => return .functionName
    | _ => return .value
  | _ => return .value

/-- `body` under the solver's quantifier over `free`, a `forall` if `all`,
or `body` if there are none: what their types bring is a hypothesis of a
`forall`'s body, and a conjunct of an `exists`'s. A quantifier over
elements in the core (`elem`) is written with the head `fren.forall` or
`fren.exists`, which each query expands (`FrenCli.SeqElems`). -/
def bindFree (free : Array FreeBound) (all : Bool) (body : String) (elem : Bool := false) : String :=
  if free.isEmpty then body else
  let decls := " ".intercalate (free.toList.map fun u => s!"({u.sym} {u.sort})")
  let cons := free.filterMap (·.cons?)
  let body := if cons.isEmpty then body else if all then s!"(=> {conj cons} {body})" else s!"(and {conj cons} {body})"
  s!"({if elem then "fren." else ""}{if all then "forall" else "exists"} ({decls}) {body})"

/-- An operand of arithmetic, `e` of type `t`, is an `Int` or a `Nat`. -/
def exprNumber (e : Expr) (t : Ty) (op : String) : M Unit := liftMsg e.span (Fren.Core.checkNumber op t)

/-- The operator `op` at `span`, prefix if `pre`, of operands of the types
`tx` and `ty`: if one is a newtype, it must have `op`, and both must be
of it (`lang::newtype_operator`). -/
def exprNewtypeOp (op : String) (span : Span) (tx ty : Ty) (pre := false) : M Unit := do
  liftMsg span (Fren.Core.checkNewtypeOperator op pre tx ty (← orderedDecl))

/-- Reports the lints of the `let` or `where` clause at `span`, of the
definitions `defs` and the body `body`: its names that neither the body nor
a later definition mentions (`unused_variables`), `let_and_return` and
`redundant_locals` (`lint::let_and_return`, `lint::redundant_locals`). -/
def lintClause (span : Span) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool) :
    M Unit := do
  let names := defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name
  let used := (Fren.Core.clauseMentions names (defs.map fun (_, _, d) => mentions d) (mentions body) true).2
  for (x, _, _) in defs, n in names, u in used do
    unless u do lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedDefinitionMsg n)
  let src := (← get).src
  let clause := toRange span
  let commented := Fren.Core.hasComment (Fren.Core.textOf src clause)
  -- Each definition from its name to the end of its expression, and the
  -- body, with their parentheses.
  let written (e : Expr) := Fren.Core.withParensIn src clause (toRange e.span)
  let ranges : Array Fren.Core.Range := defs.map fun (x, _, d) => { start := x.span.start, stop := (written d).stop }
  if let some (x, ty?, d) := defs.back? then
    let bodyIsLast := match body with | .path _ #[y] => y.name == (declaredIdent x).1.name | _ => false
    if Fren.Core.letAndReturn bodyIsLast ty?.isSome then
      let earlier? := if defs.size < 2 then none
        else some (Fren.Core.textOf src { start := ranges[0]!.start, stop := ranges[defs.size - 2]!.stop })
      let fixed := Fren.Core.letAndReturnFixed isWhere earlier? (Fren.Core.textOf src (written d))
      lintFix .letAndReturn body.span (Fren.Core.letAndReturnMsg names.back! isWhere clause fixed commented)
  for (x, ty?, d) in defs, n in names do
    let (y, bang) := declaredIdent x
    let own := match d with | .path _ #[z] => z.name == y.name | _ => false
    if Fren.Core.redundantLocal bang ty?.isSome own then lint .redundantLocals x.span (Fren.Core.redundantLocalMsg n)

/-- Reports the lints of the quantifier at `span`, a `forall` if `all`,
whose binders `bs` declare `new` and whose body is `body`: its bound names
that the body does not mention (`unused_variables`), and
`trivial_quantifier` (`lint::trivial_quantifier`), whose fix writes the
value of each bound name in place of its mentions recorded since `mark`. -/
def lintQuant (span : Span) (all : Bool) (bs : Array Binder) (new : Array CBinder) (body : Expr) (mark : Nat) :
    M Unit := do
  let mentioned := (mentions body).map (·.getRoot)
  for x in bs.flatMap (·.names), b in new do
    unless mentioned.contains b.name do lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedBoundMsg b.name all)
  let st ← get
  let counts := new.map fun b => (st.valueCount b.ty).getD 0
  unless Fren.Core.trivialQuantifier (counts.filter (· == 1)).size do return
  -- The binder of each bound name.
  let binders := bs.flatMap fun b => b.names.map fun _ => b
  let some i := counts.idxOf? 1 | return
  let tyText (k : Nat) : M String := srcAt (binders[k]!.ty[0]!.span.to binders[k]!.ty.back!.span)
  -- The value of a type of one value, if it is a variant without a payload.
  let values ← (List.range new.size).toArray.mapM fun k => do
    let some b := new[k]? | return none
    let Ty.enum p .. := b.ty | return none
    let some { ctors := #[(v, #[])], .. } := st.dataOf? p | return none
    return some s!"{← tyText k}::{v}"
  let quant := toRange span
  -- A global expectation's binders over values have no `forall` of their own.
  let own := bs[0]?.any (·.span.start != span.start)
  let fixed? : Option String := do
    -- A name the body declares again would hide nothing once the quantifier is gone.
    let redeclared := new.any fun b => body.declaredNames.contains (Fren.Core.nameText b.name)
    guard (Fren.Core.trivialQuantifierFixed (counts.filter (· == 1)).size counts.size (values.all Option.isSome) (!own)
      redeclared)
    guard (!Fren.Core.hasComment (Fren.Core.textOf st.src quant))
    let vs ← values.mapM id
    let ms := (st.boundMentions.extract mark).filterMap fun (sp, sym) =>
      (new.findIdx? (·.smt == sym)).map fun k => (toRange sp, vs[k]!)
    pure (Fren.Core.substituted st.src (Fren.Core.withParensIn st.src quant (toRange body.span)) ms)
  let some b := new[i]? | return
  lintFix .trivialQuantifier binders[i]!.span
    (Fren.Core.trivialQuantifierMsg all b.name (← tyText i) values[i]! quant fixed?)


/-- Runs `x`, and returns with its result the names that the pattern tests
that it elaborates bind (`State.bound`), which it removes: those of the
condition of a `when` or `if` (`lang::test_scope`). -/
def withBound (x : M α) : M (α × Array CBinder) := do
  let mark := (← get).bound.size
  let r ← x
  let new := (← get).bound.extract mark
  modify fun s => { s with bound := s.bound.extract 0 mark }
  return (r, new)

/-- `redundant_type_annotations` and `redundant_closure` on the closure at `span`, of the parameters `params` and the body `body`,
given for a function parameter whose parameters' types are `ps` where they
are known before the closure, and whose result's is `r?`
(`lint::redundant_type_annotations`, `lint::redundant_closure`). -/
def lintClosure (cx : ExprCtx) (ps : Array (Option Ty)) (r? : Option Ty) (span : Span)
    (params : Array (Ident × Option (Array Ident))) (body : Expr) : M Unit := do
  let names := params.map fun (x, _) => (declaredIdent x).1.name
  -- `redundant_type_annotations` (`lint::redundant_type_annotations`).
  for (x, ty?) in params, p? in ps do
    let some segs := ty? | continue
    unless Fren.Core.redundantTypeAnnotation true p?.isSome do continue
    let tr := typeSpan segs
    let msg := Fren.Core.redundantTypeAnnotationMsg (if x.name.startsWith "#_" then "_" else (declaredIdent x).1.name) (← srcAt tr)
    lintFix .redundantTypeAnnotations tr { msg with fixes := msg.fixes.map ({ · with range? := some { start := x.span.stop, stop := tr.stop } }) }
  -- `unused_variables` on its parameters (`lint::unused_closure_params`).
  let mentioned := (mentions body).map (·.getRoot)
  for (x, _) in params, n in names do
    unless Fren.Core.closureParamOptedOut n || mentioned.contains (Name.mkSimple n) do
      lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedClosureParamMsg (Name.mkSimple n))
  -- `redundant_closure` (`lint::redundant_closure`).
  let .app _ segs args := body | return
  let args := args.toList.map fun | .path _ #[y] => names.idxOf? y.name | _ => none
  let st ← get
  let some rt := r? | return
  let some pts := ps.mapM id | return
  let (callee, exact) : Fren.Core.Callee × Bool :=
    if segs.size == 1 && names.contains segs[0]!.name then (.other, false)
    else if let some (ft, _) := (if segs.size == 1 then cx.fnParam? (identName segs[0]!.name) else none) then
      (.fnParameter, ft.params == pts && ft.result == rt)
    else match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
      | .ok (.item { kind := .fnItem, path, .. }) =>
        match (if st.hofs.contains path then none else st.defs.find? (·.1 == path)), st.funPTys.find? path with
        | some (_, dps, dr, _), some (pps, rp) =>
          (.defined, dps.map (·.2) == pts && dr == rt && (pps.push rp).all (!·.restricted))
        | _, _ => (.other, false)
      | _ => (.other, false)
  unless Fren.Core.redundantClosure names.size args true callee exact do return
  lintFix .redundantClosure span (Fren.Core.redundantClosureMsg (← srcAt (segs[0]!.span.to segs.back!.span)))

/-- Records what the application of the higher-order function `path` gives
its parameter at `k`, the closure or function's name `e`, for
`needless_higher_order` (`lint::needless_higher_order`): its text, and the
names that a closure's body has free (`closureFreeNames`), of which a
function's name is one, or that it is a lambda match. -/
def noteFnArg (path : Name) (k : Nat) (e : Expr) : M Unit := do
  if (← get).fnArgs.any fun (a, sp) => sp == e.span && a.index == k then return
  let src := (← get).src
  let (lambdaMatch, names) : Bool × Array String := match e with
    | .closure _ params body => (false, closureFreeNames (params.map fun (x, _) => (declaredIdent x).1.name) body)
    | .path _ segs => (false, #[(segs.map (·.name)).foldl (· ++ "::" ++ ·) ""])
    -- `elabFnArg` accepts nothing else but a lambda match.
    | _ => (true, #[])
  let text := (e.text src).text
  modify fun s => { s with fnArgs := s.fnArgs.push ({ path, index := k, text, lambdaMatch, names }, e.span) }

end FrenCli
