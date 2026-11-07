-- keep-sorted start
import Fren.Elab.Context
import Fren.Elab.Types
-- keep-sorted end

/-! # Hosted elaboration: type terms -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The Lean type `t` as the Fren type it stands for (`coreTy?`), given the
model `s`. -/
partial def coreTyOf (s : State) (t : Expr) (params : Array Name := #[]) : Option Core.Ty :=
  let t := t.consumeMData
  let go (t : Expr) := coreTyOf s t params
  if t.isProp || t.isConstOf ``Bool then some .bool
  else if t.isConstOf ``Int then some .int
  else if t.isConstOf ``Nat then some .nat
  else if t.isConstOf ``String then some .string
  else if let .bvar k := t then some (.param k (params[k]?.getD .anonymous))
  else if t.isAppOfArity ``Fren.Seq 1 then (go t.appArg!).map .seq
  else if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then do
      return .rel (← go e.appFn!.appArg!) (← go e.appArg!)
    else (go e).map .set
  else if let some e := s.enumOf? t then do
    return .enum e.path (← (e.frenArgs t.getAppArgs).toList.mapM go)
  else if let some r := s.recordOf? t then do
    return .record r.path (← t.getAppArgs.toList.mapM go)
  else match t.constName? with
    | none => none
    | some d =>
      if let some n := s.newtypeOfDecl? d then (go n.under).map (.newtype n.path)
      else (s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none).map
        (.abstract ·.path)

/-- What counting the values of the instances of the enumeration or record
`p` needs of its declaration (`Core.Ty.valueCount`), given the model `s`. -/
def dataSig (s : State) (p : Name) : Option Core.DataSig :=
  let tys (params : Array Name) (ts : Array Expr) := ts.map fun t => (coreTyOf s t params).getD (.abstract .anonymous)
  match s.enums.get? p, s.records.get? p with
  | some e, _ => some { isRecord := false, unbounded := e.unbounded, ctors := e.payloads.map (tys e.params) }
  | none, some r => some { isRecord := true, unbounded := r.unbounded, ctors := #[tys r.params (r.fields.map (·.2))] }
  | none, none => none

/-- The facts of the declared type `t` (`lang::type_facts`), from the
declarations as both front ends give them to `Core.typeFacts`. -/
def factsOf (s : State) (t : Core.PTy) : Core.TypeFacts := Core.typeFacts s.shapeOf t.node

/-- The facts of the Lean type `ty` (`factsOf`), which accept the least if
it stands for no Fren type. -/
def exprFacts (s : State) (ty : Expr) : Core.TypeFacts :=
  match coreTyOf s ty with
  | some t => factsOf s (.plain t)
  | none => .unknown

/-- The Fren name of the type whose Lean type is `t`. -/
partial def typeName (t : Expr) : TermElabM String := do
  -- A comparison or connective is a `Prop` in Lean, and a `Bool` in Fren.
  if t.isConstOf ``Bool || t.isProp then return "Bool"
  if t.isConstOf ``Int then return "Int"
  if t.isConstOf ``Nat then return "Nat"
  if t.isConstOf ``String then return "String"
  if t.isAppOfArity ``Fren.Seq 1 then return s!"Seq<{← typeName t.appArg!}>"
  if t.isAppOfArity ``Fren.FinSet 1 then
    let e := t.appArg!
    if e.isAppOfArity ``Prod 2 then return s!"Rel<{← typeName e.appFn!.appArg!}, {← typeName e.appArg!}>"
    return s!"Set<{← typeName e}>"
  let s ← getState
  -- An instance of a generic type, with its arguments (`Reqs/Lang/Generics#printing`).
  if let some e := s.enumOf? t then return ((coreTyOf s t).map (·.show)).getD (Core.showPath e.path)
  if let some r := s.recordOf? t then return ((coreTyOf s t).map (·.show)).getD (Core.showPath r.path)
  let some d := t.constName? | return toString t
  if let some n := s.newtypeOfDecl? d then return Core.showPath n.path
  if let some a := s.abstracts.foldl (init := none) fun acc _ a => acc <|> if a.placeholder == d then some a else none then
    return Core.Ty.show (.abstract a.path)
  return toString d

/-- The Lean type `t` as the Fren type it stands for, as the `fren` command
has it (`Core.Ty`), if it is one: a condition's `Prop` is a `Bool`, and
`.bvar k`, within the declaration of a generic type, its type parameter
`params[k]`. -/
def coreTy? (t : Expr) (params : Array Name := #[]) : TermElabM (Option Core.Ty) := do
  return coreTyOf (← getState) (← instantiateMVars t) params

/-- The operator `op`, prefix if `pre`, at the current syntax, of operands
of the Fren types `tx?` and `ty?`, if they have them: if one is a newtype,
it must have `op`, and both must be of it, as the `fren` command checks
(`Core.checkNewtypeOperator`). -/
def checkNewtypeOp (op : String) (tx? ty? : Option Core.Ty) (pre := false) : TermElabM Unit := do
  let (some tx, some ty) := (tx?, ty?) | return
  liftMsg (← getRef) (Core.checkNewtypeOperator op pre tx ty (← getState).orderedDecl)

/-- The newtypes that a value of the newtype `n` is, from the outermost
in: `n`, then its underlying type, if that is a newtype, and so on. -/
partial def newtypeChain (st : State) (n : NewtypeInfo) : Array NewtypeInfo :=
  #[n] ++ ((st.newtypeOf? n.under).map (newtypeChain st)).getD #[]

/-- `x`, a value of the newtypes `chain`, from the outermost in, read
through each of their fields: the value that the solver sees. -/
def unwrapTerm (chain : Array NewtypeInfo) (x : Term) : TermElabM Term :=
  chain.foldlM (fun t n => `($(mkCIdent n.field) $t)) x

/-- The Lean type of the Fren expression `t`, elaborated with the procedure's
variables in scope. The translation asks for the types of the same terms
again and again, as of an operand for each check of it, so each one's is
elaborated once in each command that `recordingErrors` wraps
(`LocalState.types`; its key, `TypedTerm`, says why that is sound): two
of every three were asked for again, and elaborating them took about a
quarter of the time of `Reqs.Lint`. Only a type without metavariables is kept. One with a
metavariable, as `[]`'s `Seq<?>`, is elaborated afresh each time: a caller
may assign the metavariable, as `isDefEq` against a sequence's element
type does, and a kept copy would then give the next asker that assignment
rather than a fresh metavariable. Nor is an error kept: it is thrown each
time. With `fren.checkTypeCache`, which `lake test`'s ui jobs set, each
type taken from the cache is checked against the term's type elaborated
again, and an error is thrown where they differ. -/
def typeOf (t : Term) : TermElabM Expr := do
  let key : TypedTerm :=
    { fvars := (← getLCtx).getFVarIds, currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls, term := t.raw }
  let elaborate : TermElabM Expr := do
    let e ← withoutErrToSorry <| Term.withSynthesize <| elabTerm (← `(open Classical in $t)) none
    whnfR (← instantiateMVars (← inferType e))
  if let some ty := (← getLocal).types.get? key then
    -- With `fren.checkTypeCache`, the kept type against the term's type
    -- elaborated again, with everything that this elaboration did rolled
    -- back, the cache, messages and info trees among it.
    if fren.checkTypeCache.get (← getOptions) then
      let s ← Term.saveState
      let again ← try some <$> elaborate catch _ => pure none
      s.restore (restoreInfo := true)
      unless again == some ty do
        throwError m!"`fren.checkTypeCache`: the type of `{t}` kept in `typeOf`'s cache, `{ty}`, is not the one it has \
          when elaborated again, {(again.map (m!"`{·}`")).getD m!"an error"}"
    return ty
  let ty ← elaborate
  unless ty.hasMVar do modifyLocal fun l => { l with types := l.types.insert key ty }
  return ty

/-- The Fren type of the term `t` (`coreTy?`), if it has one. A term whose
type cannot be found alone, as `{}`'s, has none: its error, if any, is
left to Lean's elaboration of the whole. -/
def frenTypeOf? (t : Term) : TermElabM (Option Core.Ty) := do
  let s ← saveState
  try coreTy? (← typeOf t) catch _ => s.restore; pure none

/-- Reports `ref`, translated to `t`, unless it may stand where the type
`expected` is needed, as the `fren` command does (`Core.checkType`), with
`why` it is needed. -/
def checkTermType (ref : Syntax) (t : Term) (expected : Core.Ty) (why : Option String := none) : TermElabM Unit := do
  if let some found ← frenTypeOf? t then liftMsg ref (Core.checkType expected found why)

/-- Reports `ref`, translated to `t`, an operand of the arithmetic operator
`op`, unless it is an `Int` or a `Nat` (`Core.checkNumber`). -/
def checkNumberTerm (ref : Syntax) (t : Term) (op : String) : TermElabM Unit := do
  if let some found ← frenTypeOf? t then liftMsg ref (Core.checkNumber op found)

/-- `t`, widened to an `Int` if it is a `Nat` (`lang::widening`): Lean
inserts `↑`. -/
def widenTerm (t : Term) : TermElabM Term := do
  if (← typeOf t).isConstOf ``Nat then `(($t : Int)) else pure t

/-- Reports `ref`, translated to `t` and written where its type is declared
to be `expected`, unless it may stand there (`lang::widening`), with the
`fren` command's message and the note `why` gives from the type's name.
A Lean type that is not a Fren type is left to Lean. -/
def checkDeclared (ref : Syntax) (t : Term) (expected : Expr) (why : String → String) : TermElabM Unit := do
  if let some et ← coreTy? expected then checkTermType ref t et (some (why et.show))

/-- `ts`, each widened to an `Int` if one is an `Int` and another a `Nat`:
the branches of a conditional or the bodies of a `match`'s arms
(`lang::operator_type`). -/
def widenMixed (ts : Array Term) : TermElabM (Array Term) := do
  let tys ← ts.mapM typeOf
  if tys.any (·.isConstOf ``Int) && tys.any (·.isConstOf ``Nat) then ts.mapM widenTerm else pure ts

/-- The types of the parameters of a function of type `type`, which none
depends on. -/
def paramTypes : Expr → Array Expr
  | .forallE _ d b _ => #[d] ++ paramTypes b
  | _ => #[]

/-- The single name that the expression `a` is, without parentheses, if it
is one. -/
def soleName? (a : Syntax) : Option Name :=
  let a := unparen a
  let a := if a.getNumArgs == 1 then a[0] else a
  if a.isOfKind ``Lang.fren_path && (pathSegs a).size == 1 then some (pathSegs a)[0]!.getId else none

/-- In a defined function's body that may recurse, where the expression `a`
comes from (`lang::structural_recursion`): the position of the parameter
that it is, or that it is bound from a payload of, with whether it is a
payload. -/
def ExprCtx.recOrigin? (cx : ExprCtx) (a : Syntax) : Option (Nat × Bool) := do
  let (ps, _, _) ← cx.selfRec?
  let n ← soleName? a
  match cx.binder? n with
  | some b => return (← b.payloadOf?, true)
  | none =>
    guard (cx.vars.any (·.name == n))
    return (← ps.idxOf? n, false)

/-- Where the argument `a` at position `i` of a recursive application comes
from, relative to the parameter there (`lang::structural_recursion`). -/
def ExprCtx.recArg (cx : ExprCtx) (a : Syntax) (i : Nat) : Core.RecArg :=
  match cx.recOrigin? a with
  | some (j, true) => if j == i then .payload else .name
  | some (j, false) => if j == i then .itself else .name
  | none => if (soleName? a).isSome then .name else .expr

/-- Whether `e` is the binary operator `op`. -/
def isBinOp (e : Syntax) (op : String) : Bool :=
  e.getNumArgs == 3 && e[1].isAtom && e[1].getAtomVal.trimAscii.toString == op

/-- The operands of a chain of `op`, `or` or `and`, through parentheses, as
the `fren` command's parser, which drops them, sees it. -/
partial def chainOperands (op : String) (e : Syntax) : Array Syntax :=
  let e := unparen e
  if isBinOp e op then chainOperands op e[0] ++ chainOperands op e[2] else #[e]

/-- Whether `e` is `if c then a else b`. -/
def isIte (e : Syntax) : Bool := e.getNumArgs == 6 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "if"

/-- Of `when c, d`, `c and d` and `if c then d else f`: `c`, whose pattern
tests' names `d` sees, `d`, and the other parts (`lang::test_scope`). -/
def testScoped? (e : Syntax) : Option (Syntax × Syntax × Array Syntax) :=
  if e.getNumArgs == 4 && e[0].isAtom && e[0].getAtomVal.trimAscii.toString == "when" then some (e[1], e[3], #[])
  else if isBinOp e "and" then some (e[0], e[2], #[])
  else if isIte e then some (e[1], e[3], #[e[5]])
  else none

/-- The pattern tests of the chain of `and` `c`, each with its scrutinee and
its pattern. -/
def chainTests (c : Syntax) : Array (Syntax × Syntax) :=
  (chainOperands "and" c).filterMap fun o => if o.isOfKind ``Lang.isExpr then some (o[0], o[2]) else none

/-- The pattern of `s.matches?(p)`, `p`, as a closed `Fren.Core.Re` term
(`Reqs/Lang/Expressions#patterns`). -/
def patternTerm (p : Syntax) : TermElabM Term := do
  let some lit := (let p := unparen p; if p.getNumArgs == 1 then p[0] else p).isStrLit?
    | throwErrorAt p Core.patternNotLiteralMsg.text
  match Core.parseRe lit with
  | .ok re => exprToSyntax (Lean.toExpr re)
  | .error e => throwErrorAt p e.msg.text

/-- The set of the nonempty `xs`, as `insert` and `singleton`, as `{a, b}`
elaborates, without its ambiguity with structure instances. -/
def finSetLit (xs : Array Term) : TermElabM Term := do
  let mut t ← `(Singleton.singleton $(xs.back!))
  for x in xs.pop.reverse do t ← `(Insert.insert $x $t)
  return t

/-- The element types of the relation type `ty`, if it is one. -/
def relTypes? (ty : Expr) : Option (Expr × Expr) :=
  if ty.isAppOfArity ``Fren.FinSet 1 && ty.appArg!.isAppOfArity ``Prod 2 then
    some (ty.appArg!.appFn!.appArg!, ty.appArg!.appArg!)
  else none

/-- The constructor `c` of an enumeration or record, applied to the type
arguments `targs`, explicitly if there are any, and to `args`: so that Lean
infers no argument that Fren does not (`Reqs/Generated#generic-types`). -/
def ctorApp (c : Name) (targs : Array Expr) (args : Array Term) (ref : Syntax := .missing) : TermElabM Term := do
  let f := if ref.isMissing then mkCIdent c else mkCIdentFrom ref c
  if targs.isEmpty then return ← `($f $args*)
  `(@$f $(targs.map typeSyntax)* $args*)

/-- Every value of a finite type, as closed expressions, if there are at
most `cap` of them. Shared by relation projections, quantifier instances
and set cardinality translation; pairs use their Cartesian product. -/
partial def valuesOf? (ty : Expr) (cap : Nat := 64) : MetaM (Option (Array Expr)) := do
  if ty.isConstOf ``Bool then
    return if cap < 2 then none else some #[Lean.mkConst ``Bool.true, Lean.mkConst ``Bool.false]
  let s ← getState
  let targs := ty.getAppArgs
  let ctors : Array (Name × Array Expr) ←
    if ty.isAppOfArity ``Prod 2 then pure #[(``Prod.mk, targs)]
    else if let some e := s.enumOf? ty then
      if (exprFacts s ty).unbounded then return none
      let ps := e.payloadsAt targs
      pure (e.variants.mapIdx fun i _ => (e.ctor i, ps[i]?.getD #[]))
    else if let some r := s.recordOf? ty then
      if (exprFacts s ty).unbounded then return none
      pure #[(r.ctor, (r.fieldsAt targs).map (·.2))]
    else if let some n := ty.constName?.bind s.newtypeOfDecl? then
      pure #[(n.ctor, #[n.under])]
    else return none
  let mut out := #[]
  for (c, ts) in ctors do
    let mut combos : Array (Array Expr) := #[#[]]
    for t in ts do
      let some vs ← valuesOf? t cap | return none
      if combos.size * vs.size > cap then return none
      combos := combos.flatMap fun pre => vs.map pre.push
    let info ← getConstInfo c
    let ctor := Lean.mkConst c (info.levelParams.map fun _ => Level.zero)
    out := out ++ combos.map fun args => mkAppN ctor (targs ++ args)
    if out.size > cap then return none
  return some out

/-- The position of `s`'s variant among the variants of the ordered
enumeration `info`, an `Int`: its constructor's index, as a conditional on
each variant but the last, as the `fren` command writes it
(`FrenCli.DataDecl.ordinal`), so that comparing two values compares their
positions without quantifiers. -/
def ordinalTerm (info : EnumInfo) (s : Term) : TermElabM Term := do
  let last := info.variants.size - 1
  (List.range last).foldrM (init := ← `(($(Syntax.mkNumLit (toString last)) : Int))) fun k acc =>
    `(if $s = $(mkCIdent (info.ctor k)) then ($(Syntax.mkNumLit (toString k)) : Int) else $acc)

/-- `x < y`, or `x ≤ y` if not `strict`, of values compared by `o`, as a
Lean proposition, as the `fren` command's `orderSmt` writes it: a record's
lexicographically, by its fields in the order declared, and a newtype's as
its field's. -/
partial def orderTerm (o : Core.OrderPlan) (strict : Bool) (x y : Term) : TermElabM Term := do
  let st ← getState
  match o with
  | .number => if strict then `($x < $y) else `($x ≤ $y)
  | .string => if strict then `(Fren.Str.lt $x $y) else `(Fren.Str.le $x $y)
  | .enum p _ =>
    let some info := st.enums.get? p | throwError "internal error: unknown enum `{p}`"
    let (i, j) := (← ordinalTerm info x, ← ordinalTerm info y)
    if strict then `($i < $j) else `($i ≤ $j)
  | .newtype p u =>
    let some n := st.newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    orderTerm u strict (← `($(mkCIdent n.field) $x)) (← `($(mkCIdent n.field) $y))
  | .record p fs =>
    let some r := st.records.get? p | throwError "internal error: unknown record `{p}`"
    -- From the last field, compared as the whole is, back to the first,
    -- which decides unless the two are equal.
    let sel (f : Name) (v : Term) : TermElabM Term := `($(mkCIdent (r.decl ++ f)) $v)
    let some (fl, ol) := fs.getLast? | if strict then `(False) else `(True)
    let mut acc ← orderTerm ol strict (← sel fl x) (← sel fl y)
    for (f, of) in fs.dropLast.reverse do
      let (a, b) := (← sel f x, ← sel f y)
      acc ← `($(← orderTerm of true a b) ∨ ($a = $b ∧ $acc))
    return acc

/-- The ordering `op` of `x` and `y`, compared by `o`: of a newtype, its
field's; of numbers and enumerations, with `op` itself; otherwise as
`orderTerm` writes it, with `>` and `≥` as `<` and `≤` of `y` and `x`. -/
partial def orderingTerm (o : Core.OrderPlan) (op : String) (x y : Term) : TermElabM Term := do
  match o with
  | .newtype p u =>
    let some n := (← getState).newtypes.get? p | throwError "internal error: unknown newtype `{p}`"
    orderingTerm u op (← `($(mkCIdent n.field) $x)) (← `($(mkCIdent n.field) $y))
  | .number => match op with
    | "<" => `($x < $y) | "<=" => `($x ≤ $y) | ">" => `($x > $y) | _ => `($x ≥ $y)
  | .enum p _ =>
    let some info := (← getState).enums.get? p | throwError "internal error: unknown enum `{p}`"
    let (i, j) := (← ordinalTerm info x, ← ordinalTerm info y)
    match op with
    | "<" => `($i < $j) | "<=" => `($i ≤ $j) | ">" => `($i > $j) | _ => `($i ≥ $j)
  | _ => match op with
    | "<" => orderTerm o true x y
    | "<=" => orderTerm o false x y
    | ">" => orderTerm o true y x
    | _ => orderTerm o false y x

/-- Calls the method `m` of the term `t` of Lean type `ty`, with the
arguments `args`, each with its syntax (`lang::method_type`). -/
def callMethod (ref : Syntax) (t : Term) (ty : Expr) (m : String) (args : Array (Term × Syntax)) :
    TermElabM (Term × Expr) := do
  if ty.isAppOfArity ``Fren.Seq 1 then
    let elem := ty.appArg!
    let some method := (Core.Method.ofName? m).filter (·.accepts false false false true)
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false false false true).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    let leanTy : Core.MethodTy → Expr
      | .bool => Lean.mkConst ``Bool | .int => Lean.mkConst ``Int | .elem => elem | _ => ty
    let mut widened := #[]
    for (a, stx) in args, p in method.params do
      let a ← if (leanTy p).isConstOf ``Int then widenTerm a else pure a
      let ta ← typeOf a
      unless ← isDefEq ta (leanTy p) do
        throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
      widened := widened.push (a, stx)
    let args := widened
    let a : Term := (args.map (·.1))[0]?.getD t
    let b : Term := (args.map (·.1))[1]?.getD t
    let term ← match method with
      | .len => `(Fren.Seq.len $t)
      | .startsWith => `(Fren.Seq.startsWith $t $a)
      | .endsWith => `(Fren.Seq.endsWith $t $a)
      | .contains => `(Fren.Seq.contains $t $a)
      | .at => `(Fren.Seq.«at» $t $a)
      | .slice => `(Fren.Seq.slice $t $a $b)
      | .indexOf => `(Fren.Seq.indexOf $t $a $b)
      | .replace => `(Fren.Seq.replace $t $a $b)
      | .update => `(Fren.Seq.update $t $a $b)
      | _ => `(Fren.Seq.rev $t)
    return (term, leanTy method.result)
  if let some (a, b) := relTypes? ty then
    let some method := (Core.Method.ofName? m).filter (·.accepts false false true)
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false false true).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    let set (e : Expr) := mkApp (Lean.mkConst ``Fren.FinSet [Level.zero]) e
    let rel (x y : Expr) := set (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) x y)
    -- The image of the inverse under every value of `other`, if it is finite.
    let project (inv : Term) (other : Expr) (dflt : Term) : TermElabM Term := do
      let some vs ← valuesOf? other | return dflt
      `(Fren.FinSet.image $inv ($(← finSetLit (← vs.mapM exprToSyntax)) : Fren.FinSet $(typeSyntax other)))
    match method with
      | .card => return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
      | .inverse => return (← `(Fren.FinSet.inverse $t), rel b a)
      | .domain => return (← project (← `(Fren.FinSet.inverse $t)) b (← `(Fren.FinSet.domain $t)), set a)
      | .range => return (← project t a (← `(Fren.FinSet.range $t)), set b)
      | .closure => do
        unless ← isDefEq a b do throwErrorAt ref (Core.closureTypeMsg (← typeName ty)).text
        return (← `(Fren.FinSet.closure $t), ty)
      | _ => do
        let (x, stx) := args[0]!
        let tx ← typeOf x
        unless ← isDefEq tx (set a) do
          throwErrorAt stx s!"type mismatch: expected `{← typeName (set a)}`, found `{← typeName tx}`"
        return (← `(Fren.FinSet.image $t $x), set b)
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (int := true))
      | throwErrorAt ref (Core.unknownMethodMsg m (← typeName ty) false (int := true)).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ta.isConstOf ``Int || ta.isConstOf ``Nat do
        throwErrorAt stx s!"type mismatch: expected `Int`, found `{← typeName ta}`"
    -- `min` and `max` of `Nat`s are `Nat`s; otherwise both are widened
    -- (`lang::nat_result`).
    let op : Core.NatOp := match method with | .min => .min | .max => .max | _ => .abs
    let argNat ← args.anyM fun (a, _) => return (← typeOf a).isConstOf ``Nat
    let nat := Core.natResult op (ty.isConstOf ``Nat) argNat false
    let t ← if nat then pure t else widenTerm t
    let args ← if nat then pure args else args.mapM fun (a, stx) => return (← widenTerm a, stx)
    -- Conditionals, so that they stay linear.
    let y : Term := (args.map (·.1))[0]?.getD t
    let term ← match method with
      | .min => `(if $t ≤ $y then $t else $y)
      | .max => `(if $t ≥ $y then $t else $y)
      | _ => `(if $t < 0 then -$t else $t)
    return (term, Lean.mkConst (if nat then ``Nat else ``Int))
  -- `min` and `max` of an ordered record's, newtype's or `String`'s value,
  -- by their order, and a record's or newtype's other methods, which it has
  -- none of (`lang::method_type`, `lang::ordered_type`).
  let st ← getState
  if let some ct := (← coreTy? ty).filter (fun ct => ct matches .record .. | .newtype .. || (ct == .string && (m == "min" || m == "max"))) then
    let name := ct.show
    let ordered := ct.ordered st.orderedDecl
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (ordered := ordered))
      | throwErrorAt ref (if ordered then Core.unknownMethodMsg m name false (ordered := true)
          else if m == "min" || m == "max" then Core.unorderedMethodMsg (ct.orderedDecl?.getD .record) m name
          else Core.noMethodsMsg m name).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ← isDefEq ta ty do throwErrorAt stx s!"type mismatch: expected `{← typeName ty}`, found `{← typeName ta}`"
    let y : Term := (args.map (·.1))[0]?.getD t
    let some plan := st.orderPlan? ct | throwError "internal error: `{name}` is not ordered"
    let cmp ← orderingTerm plan (if method == .min then "<=" else ">=") t y
    return (← `(if $cmp then $t else $y), ty)
  if let some info := st.enumOf? ty then
    let name := Core.showPath info.path
    let some method := (Core.Method.ofName? m).filter (·.accepts false false (ordered := info.ordered))
      | throwErrorAt ref (if info.ordered then Core.unknownMethodMsg m name false (ordered := true)
          else if m == "min" || m == "max" then Core.unorderedMethodMsg .enumeration m name
          else Core.noMethodsMsg m name).text
    unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
    for (a, stx) in args do
      let ta ← typeOf a
      unless ← isDefEq ta ty do throwErrorAt stx s!"type mismatch: expected `{← typeName ty}`, found `{← typeName ta}`"
    -- Conditionals on the variants' positions, as for an `Int`.
    let y : Term := (args.map (·.1))[0]?.getD t
    let (i, j) := (← ordinalTerm info t, ← ordinalTerm info y)
    let term ← if method == .min then `(if $i ≤ $j then $t else $y) else `(if $i ≥ $j then $t else $y)
    return (term, ty)
  unless ty.isConstOf ``String do throwErrorAt ref (Core.noMethodsMsg m (← typeName ty)).text
  let some method := (Core.Method.ofName? m).filter (·.accepts true false)
    | throwErrorAt ref (Core.unknownMethodMsg m "String" (ordered := true)).text
  unless args.size == method.arity do throwErrorAt ref (Core.arityMsg (Name.mkSimple m) method.arity args.size).text
  let leanTy : Core.MethodTy → Expr
    | .bool => Lean.mkConst ``Bool | .int => Lean.mkConst ``Int | _ => Lean.mkConst ``String
  let mut widened := #[]
  for (a, stx) in args, p in method.params do
    -- A pattern is a `Fren.Core.Re`, which `patternTerm` checked.
    if method == .matches then widened := widened.push (a, stx); continue
    let a ← if (leanTy p).isConstOf ``Int then widenTerm a else pure a
    let ta ← typeOf a
    unless ← isDefEq ta (leanTy p) do
      throwErrorAt stx s!"type mismatch: expected `{← typeName (leanTy p)}`, found `{← typeName ta}`"
    widened := widened.push (a, stx)
  let args := widened
  let a : Term := (args.map (·.1))[0]?.getD (← `(""))
  let b : Term := (args.map (·.1))[1]?.getD (← `(""))
  let term ← match method with
    | .len => `(Fren.Str.len $t)
    | .startsWith => `(Fren.Str.startsWith $t $a)
    | .endsWith => `(Fren.Str.endsWith $t $a)
    | .contains => `(Fren.Str.contains $t $a)
    -- `toTerm` gives the pattern, as a `Fren.Core.Re`.
    | .matches => `(Fren.Core.Re.matches $a $t)
    | .at => `(Fren.Str.«at» $t $a)
    | .slice => `(Fren.Str.slice $t $a $b)
    | .indexOf => `(Fren.Str.indexOf $t $a $b)
    | .replace => `(Fren.Str.replace $t $a $b)
    | .replaceAll => `(Fren.Str.replaceAll $t $a $b)
    | _ => `(Fren.FinSet.card $t)
  return (term, leanTy method.result)

/-- Reads the field `f` of the term `t` of Lean type `ty`; of a `String` or
a set, calls the method `f`, without arguments. -/
def readField (ref : Syntax) (t : Term) (ty : Expr) (f : Name) : TermElabM (Term × Expr) := do
  -- The field `0` of a newtype (`Reqs/Lang/Expressions#newtypes`).
  if let some n := (← getState).newtypeOf? ty then
    unless f == Name.mkSimple "0" do throwErrorAt ref (Core.noFieldMsg f (Core.showPath n.path) #[Name.mkSimple "0"]).text
    return (← `($(mkCIdentFrom ref n.field) $t), n.under)
  -- A field named by digits is no method's name.
  if Core.positionalField f && ((← getState).recordOf? ty).isNone then
    throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (ty.isConstOf ``Int || ty.isConstOf ``Nat) && f == `abs then
    modifyLocal fun l => { l with absEnds := l.absEnds.push ref.getTailPos? }
  if ty.isConstOf ``String || ty.isConstOf ``Int || ty.isConstOf ``Nat || (relTypes? ty).isSome || ty.isAppOfArity ``Fren.Seq 1 then
    return ← callMethod ref t ty f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if ((← getState).enumOf? ty).isSome && (f == `min || f == `max) then
    return ← callMethod ref t ty f.toString #[]
  if ty.isAppOfArity ``Fren.FinSet 1 then
    unless f == `card do throwErrorAt ref (Core.unknownSetMethodMsg f.toString (← typeName ty)).text
    return (← `(Fren.FinSet.card $t), Lean.mkConst ``Int)
  let some r := (← getState).recordOf? ty
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) #[]).text
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let some (_, ft) := (r.fieldsAt ty.getAppArgs).find? (·.1 == f)
    | throwErrorAt ref (Core.noFieldMsg f (← typeName ty) (r.fields.map (·.1))).text
  return (← `($(mkCIdentFrom ref (r.decl ++ f)) $t), ft)


end Fren
