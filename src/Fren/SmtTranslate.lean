-- keep-sorted start
import Fren.FinSet
import Fren.Seq
import FrenCore.Regex
import FrenCore.Str
import Smt
-- keep-sorted end

/-!
# Translating fields, payloads and strings for lean-smt

lean-smt declares each inductive type it meets as an SMT-LIB datatype, with
a selector for each field of each constructor named `{ctor}.{field}`, and
translates constructor applications, but not projections. This translates
a field read, `p.x` or a projection `.proj`, of a structure, and the
selectors that Fren generates for payloads (`Fren.selectorName`), which
are named after the constructor's fields, to those selectors.
-/

open Lean Meta Smt Translator Term

namespace Fren

/-- The selector of the field `field` of the constructor `ctor`, as
lean-smt names it, applied to `arg`; `none` if `ctor` belongs to an indexed
inductive, or one with a parameter that is not a type, which lean-smt does
not declare as a datatype. One whose parameters are types, as a generic
type's are (`Reqs/Generated#generic-types`), it declares as a parametric
datatype, whose selectors are named as any other's. -/
def selectorApp (ctor : Name) (field : Name) (arg : Expr) : TranslationM (Option Smt.Term) := do
  let some (.ctorInfo c) := (← getEnv).find? ctor | return none
  let some (.inductInfo i) := (← getEnv).find? c.induct | return none
  if i.numIndices != 0 then return none
  let typesOnly ← forallBoundedTelescope i.type i.numParams fun ps _ => ps.allM fun p => return (← inferType p).isSort
  unless typesOnly do return none
  -- The datatype that declares the selector.
  modify fun st => { st with depConstants := st.depConstants.insert c.induct }
  return some (appT (symbolT s!"{ctor}.{field}") (← applyTranslators! arg))

/-- lean-smt's name of the `k`th field of the constructor `c`: the field's
own, or `fieldk`, counted from 1, if it has none, as a hygienic binder,
such as `Except.error`'s, has none (`Reqs/Lang/Prelude#smt`). -/
def leanSmtField (c : ConstructorVal) (k : Nat) : Name :=
  let rec binder : Nat → Expr → Name
    | 0, .forallE n _ _ _ => n
    | i + 1, .forallE _ _ b _ => binder i b
    | _, _ => .anonymous
  let n := binder (c.numParams + k) c.type
  if n.isAnonymous || n.hasMacroScopes then Name.mkSimple s!"field{k + 1}" else n

@[smt_translate] def translateSelector : Translator := fun e => do
  let env ← getEnv
  match e with
  | .proj s idx arg =>
    let some info := getStructureInfo? env s | return none
    let some field := info.fieldNames[idx]? | return none
    selectorApp (getStructureCtor env s).name field arg
  | .app .. =>
    -- The value is the last argument, after a generic type's parameters and,
    -- for a payload selector, their `Inhabited` instances.
    let .const f _ := e.getAppFn | return none
    let args := e.getAppArgs
    let some arg := args.back? | return none
    if let some p := env.getProjectionFnInfo? f then
      if p.fromClass || args.size != p.numParams + 1 then return none
      return ← selectorApp p.ctorName (Name.mkSimple f.getString!) arg
    -- A payload selector, `ctor.xk` (`Fren.selectorName`), or of a Lean
    -- constructor of a prelude type, under `Fren.Prelude`
    -- (`Fren.preludeSelectors`), with lean-smt's name of the field.
    let ctor := if (`Fren.Prelude).isPrefixOf f then (f.replacePrefix `Fren.Prelude .anonymous).getPrefix else f.getPrefix
    let some (.ctorInfo c) := env.find? ctor | return none
    let some (.defnInfo _) := env.find? f | return none
    unless args.size == 2 * c.numParams + 1 do return none
    let some k := (f.getString!.drop 1).toNat? | return none
    selectorApp ctor (leanSmtField c k) arg
  | _ => return none

/-- The result of an uninterpreted function whose result is a `Nat`, in a
check: the function is given to the solver with an `Int` result, and each
application is at least 0 by a hypothesis of every query, rather than by
the quantified axiom that lean-smt asserts of a function into `Nat`
(`Reqs/Lang/Decidability`). -/
def natResult (i : Int) : Nat := i.toNat

/-- A `Nat` as an `Int`: `↑n`, which Lean inserts to widen a `Nat`, and
`Fren.natResult`, are the identity, since every `Nat` the solver sees is at
least 0. -/
@[smt_translate] def translateNatCast : Translator := fun e => do
  match_expr e with
  | Nat.cast α _ n => if α.isConstOf ``Int then return some (← applyTranslators! n) else return none
  | Int.ofNat n =>
    if let .lit (.natVal k) := n.consumeMData then return some (literalT (toString k))
    return some (← applyTranslators! n)
  | Fren.natResult i => return some (← applyTranslators! i)
  -- `x.toNat`, which lean-smt's preprocessing writes for a `Nat` that it
  -- makes an `Int` and which reaches a `Nat` field or payload: exactly, as
  -- a conditional, rather than as a function that a quantified axiom states
  -- is at least 0.
  | Int.toNat i =>
    let x ← applyTranslators! i
    return some (mkApp3 (symbolT "ite") (mkApp2 (symbolT ">=") x (literalT "0")) x (literalT "0"))
  | _ => return none

/-- The character that `e`, as `Lean.ToExpr` writes one, stands for. -/
def charOf? (e : Expr) : Option Char :=
  match e.consumeMData with
  | .app (.const ``Char.ofNat _) (.lit (.natVal k)) => some (Char.ofNat k)
  | _ => none

/-- The list that `e`, built from `List.cons` and `List.nil`, stands for. -/
partial def listOf? (f : Expr → Option α) (e : Expr) : Option (List α) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => some []
  | (``List.cons, #[_, h, t]) => do return (← f h) :: (← listOf? f t)
  | _ => none

/-- The pattern that `e`, a closed term built from constructors, stands for:
what `Lean.ToExpr` makes of a `Fren.Core.Re`. -/
partial def exprToRe? (e : Expr) : Option Fren.Core.Re :=
  let pair (e : Expr) : Option (Char × Char) := match e.consumeMData.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) => do return (← charOf? a, ← charOf? b)
    | _ => none
  match e.consumeMData.getAppFnArgs with
  | (``Fren.Core.Re.none, #[]) => some .none
  | (``Fren.Core.Re.any, #[]) => some .any
  | (``Fren.Core.Re.str, #[cs]) => do return .str (← listOf? charOf? cs)
  | (``Fren.Core.Re.cls, #[neg, rs]) => do return .cls (neg.isConstOf ``Bool.true) (← listOf? pair rs)
  | (``Fren.Core.Re.union, #[a, b]) => do return .union (← exprToRe? a) (← exprToRe? b)
  | (``Fren.Core.Re.cat, #[a, b]) => do return .cat (← exprToRe? a) (← exprToRe? b)
  | (``Fren.Core.Re.star, #[a]) => do return .star (← exprToRe? a)
  | _ => none

/-- `decide p`, a condition as a `Bool`, is `p`: lean-smt makes a `Bool`
variable a `Prop`, and a `Bool` member of a set or sequence its `decide`,
which it would otherwise declare as an uninterpreted function of an
uninterpreted `Decidable`, which cvc5 rejects. -/
@[smt_translate] def translateDecide : Translator := fun e => do
  match_expr e with
  | Decidable.decide p _ => return some (← applyTranslators! p)
  | _ => return none

/-- Equivalence may survive the Boolean embedding inside a defined
quantified condition. It is logical equality, never an uninterpreted symbol. -/
@[smt_translate] def translateIff : Translator := fun e => do
  match_expr e with
  | Iff p q => return some (mkApp2 (symbolT "=") (← applyTranslators! p) (← applyTranslators! q))
  | _ => return none

/-- Fren's string literals and methods (`Fren.Str`), as SMT-LIB's string
functions. lean-smt translates `++` and `<` on strings, but writes literals
without escaping them, and `>` as `str.>`, which is not SMT-LIB: so Fren
wraps literals in `Fren.Str.lit`, and writes `a > b` as `Fren.Str.lt b a`.
A comparison with a literal is a match, as in the binary. -/
@[smt_translate] def translateStr : Translator := fun e => do
  let tr := applyTranslators!
  match_expr e with
  | Fren.Str.lit s =>
    let .lit (.strVal v) := s.consumeMData | return none
    return literalT (Fren.Core.smtStringLit v)
  | Fren.Str.len s => return appT (symbolT "str.len") (← tr s)
  | Fren.Str.startsWith s p => return mkApp2 (symbolT "str.prefixof") (← tr p) (← tr s)
  | Fren.Str.endsWith s p => return mkApp2 (symbolT "str.suffixof") (← tr p) (← tr s)
  | Fren.Str.contains s t => return mkApp2 (symbolT "str.contains") (← tr s) (← tr t)
  | Fren.Str.«at» s i => return mkApp2 (symbolT "str.at") (← tr s) (← tr i)
  | Fren.Str.slice s i n => return mkApp3 (symbolT "str.substr") (← tr s) (← tr i) (← tr n)
  | Fren.Str.indexOf s t i => return mkApp3 (symbolT "str.indexof") (← tr s) (← tr t) (← tr i)
  | Fren.Str.replace s a b => return mkApp3 (symbolT "str.replace") (← tr s) (← tr a) (← tr b)
  | Fren.Str.replaceAll s a b => return mkApp3 (symbolT "str.replace_all") (← tr s) (← tr a) (← tr b)
  | Fren.Core.Re.matches r s =>
    let some re := exprToRe? r | return none
    return mkApp2 (symbolT "str.in_re") (← tr s) (literalT re.toSmt)
  | Fren.Str.lt a b => compare a b false
  | Fren.Str.le a b => compare a b true
  | LE.le α _ a b =>
    unless α.isConstOf ``String do return none
    return mkApp2 (symbolT "str.<=") (← tr a) (← tr b)
  | _ => return none
where
  /-- The value of a literal. -/
  lit? (e : Expr) : Option String :=
    match e.consumeMData.getAppFnArgs with
    | (``Fren.Str.lit, #[s]) => match s.consumeMData with
      | .lit (.strVal v) => some v
      | _ => none
    | _ => none
  /-- `a < b`, or with `orEqual`, `a <= b`: against a literal, as a match,
  as the binary writes it (`Fren.Core.strCompareSmt`). -/
  compare (a b : Expr) (orEqual : Bool) : TranslationM (Option Smt.Term) := do
    let tr := applyTranslators!
    match lit? a, lit? b with
    | none, some c => return mkApp2 (symbolT "str.in_re") (← tr a) (literalT (Fren.Core.belowPattern c orEqual))
    | some c, none =>
      return appT (symbolT "not") (mkApp2 (symbolT "str.in_re") (← tr b) (literalT (Fren.Core.belowPattern c !orEqual)))
    | _, _ => return mkApp2 (symbolT (if orEqual then "str.<=" else "str.<")) (← tr a) (← tr b)

/-- Fren's sets (`Fren.FinSet`), as cvc5's: every set is a unary relation, a
set of 1-tuples (`Reqs/Cli`). -/
@[smt_translate] def translateSet : Translator := fun e => do
  let tr := applyTranslators!
  let isSet (γ : Expr) : Bool := γ.isAppOfArity ``Fren.FinSet 1
  -- A member: a relation's pairs are 2-tuples, written only as `Prod.mk`.
  let tuple (x : Expr) : TranslationM Smt.Term := do
    match_expr x with
    | Prod.mk _ _ a b => return mkApp2 (symbolT "tuple") (← tr a) (← tr b)
    | _ => return appT (symbolT "tuple") (← tr x)
  match_expr e with
  | Fren.FinSet α =>
    match_expr α with
    | Prod a b => return appT (symbolT "Set") (mkApp2 (symbolT "Tuple") (← tr a) (← tr b))
    | _ => return appT (symbolT "Set") (appT (symbolT "Tuple") (← tr α))
  | Membership.mem _ γ _ s x =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.member") (← tuple x) (← tr s)
  | HasSubset.Subset γ _ s t =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.subset") (← tr s) (← tr t)
  | Union.union γ _ s t =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.union") (← tr s) (← tr t)
  | Inter.inter γ _ s t =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.inter") (← tr s) (← tr t)
  | SDiff.sdiff γ _ s t =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.minus") (← tr s) (← tr t)
  | EmptyCollection.emptyCollection γ _ =>
    unless isSet γ do return none
    return mkApp2 (symbolT "as") (symbolT "set.empty") (← tr γ)
  | Singleton.singleton _ γ _ x =>
    unless isSet γ do return none
    return appT (symbolT "set.singleton") (← tuple x)
  | Insert.insert _ γ _ x s =>
    unless isSet γ do return none
    return mkApp2 (symbolT "set.insert") (← tuple x) (← tr s)
  | Fren.FinSet.card _ _ s => return appT (symbolT "set.card") (← tr s)
  | Fren.FinSet.join _ _ _ _ r q => return mkApp2 (symbolT "rel.join") (← tr r) (← tr q)
  | Fren.FinSet.inverse _ _ r => return appT (symbolT "rel.transpose") (← tr r)
  | Fren.FinSet.closure _ _ r => return appT (symbolT "rel.tclosure") (← tr r)
  -- `s` is a unary relation, so the image is a join.
  | Fren.FinSet.image _ _ _ r s => return mkApp2 (symbolT "rel.join") (← tr s) (← tr r)
  | Fren.FinSet.domain _ _ r => return appT (literalT "(_ rel.project 0)") (← tr r)
  | Fren.FinSet.range _ _ r => return appT (literalT "(_ rel.project 1)") (← tr r)
  | _ => return none

/-- Fren's sequences (`Fren.Seq`), as cvc5's (`Reqs/Cli`). -/
@[smt_translate] def translateSeq : Translator := fun e => do
  let tr := applyTranslators!
  let isSeq (γ : Expr) : Bool := γ.isAppOfArity ``Fren.Seq 1
  match_expr e with
  | Fren.Seq α => return appT (symbolT "Seq") (← tr α)
  | EmptyCollection.emptyCollection γ _ =>
    unless isSeq γ do return none
    return mkApp2 (symbolT "as") (symbolT "seq.empty") (← tr γ)
  | HAppend.hAppend γ _ _ _ q r =>
    unless isSeq γ do return none
    return mkApp2 (symbolT "seq.++") (← tr q) (← tr r)
  | Membership.mem _ γ _ q x =>
    unless isSeq γ do return none
    return mkApp2 (symbolT "seq.contains") (← tr q) (appT (symbolT "seq.unit") (← tr x))
  | Fren.Seq.unit _ x => return appT (symbolT "seq.unit") (← tr x)
  | Fren.Seq.len _ q => return appT (symbolT "seq.len") (← tr q)
  | Fren.Seq.nth _ _ q i => return mkApp2 (symbolT "seq.nth") (← tr q) (← tr i)
  | Fren.Seq.«at» _ q i => return mkApp2 (symbolT "seq.at") (← tr q) (← tr i)
  | Fren.Seq.slice _ q i n => return mkApp3 (symbolT "seq.extract") (← tr q) (← tr i) (← tr n)
  | Fren.Seq.indexOf _ _ q t i => return mkApp3 (symbolT "seq.indexof") (← tr q) (← tr t) (← tr i)
  | Fren.Seq.startsWith _ _ q p => return mkApp2 (symbolT "seq.prefixof") (← tr p) (← tr q)
  | Fren.Seq.endsWith _ _ q p => return mkApp2 (symbolT "seq.suffixof") (← tr p) (← tr q)
  | Fren.Seq.contains _ _ q t => return mkApp2 (symbolT "seq.contains") (← tr q) (← tr t)
  | Fren.Seq.replace _ _ q a b => return mkApp3 (symbolT "seq.replace") (← tr q) (← tr a) (← tr b)
  | Fren.Seq.update _ q i x => return mkApp3 (symbolT "seq.update") (← tr q) (← tr i) (appT (symbolT "seq.unit") (← tr x))
  | Fren.Seq.rev _ q => return appT (symbolT "seq.rev") (← tr q)
  | _ => return none

/-- An element's sort in a model: SMT-LIB's `Bool` is `Bool` there, not a
proposition, since a collection's elements are data, as in `Fren.Seq Bool`. -/
def reconstructElementSort (s : cvc5.Sort) : Smt.ReconstructM Expr :=
  if s.isBoolean then return mkConst ``Bool else Smt.Reconstruct.reconstructSort s

/-- An element in a model, a `Bool` where its SMT sort is `Bool`. -/
def reconstructElement (t : cvc5.Term) : Smt.ReconstructM Expr := do
  let e ← Smt.Reconstruct.reconstructTerm t
  unless t.getSort!.isBoolean do return e
  if e.isConstOf ``True then return mkConst ``Bool.true
  if e.isConstOf ``False then return mkConst ``Bool.false
  Meta.mkDecide e

/-- A sequence in a model. -/
@[smt_sort_reconstruct] def reconstructSeqSort : Smt.SortReconstructor := fun s => do
  match s.getKind! with
  | .SEQUENCE_SORT =>
    let α ← reconstructElementSort s.getSequenceElementSort!
    return mkApp (mkConst ``Fren.Seq [Level.zero]) α
  | _ => return none

@[smt_term_reconstruct] def reconstructSeq : Smt.TermReconstructor := fun t => do
  let seqOf (ty : Expr) : Option Expr := if ty.isAppOfArity ``Fren.Seq 1 then some ty.appArg! else none
  match t.getKind! with
  | .CONST_SEQUENCE =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := seqOf ty | return none
    -- A model's sequence value is a constant whatever its length, with its
    -- elements as its value rather than its children (`Reqs/Models#reading`).
    let elems ← t.getSequenceValue!.mapM Smt.Reconstruct.reconstructTerm
    return Lean.mkApp2 (mkConst ``Fren.Seq.ofList [Level.zero]) α (← mkListLit α elems.toList)
  | .SEQ_UNIT =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := seqOf ty | return none
    return Lean.mkApp2 (mkConst ``Fren.Seq.unit [Level.zero]) α (← reconstructElement t[0]!)
  | .STRING_CONCAT =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := seqOf ty | return none
    let parts ← (Array.range t.getNumChildren).mapM fun i => Smt.Reconstruct.reconstructTerm t[i]!
    let app (a b : Expr) := Lean.mkApp6 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero]) ty ty ty
      (Lean.mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) ty (mkApp (mkConst ``Fren.Seq.instAppend [Level.zero]) α)) a b
    return some (parts.pop.foldr app parts.back!)
  | _ => return none

/-- A set in a model: a set of 1-tuples. -/
@[smt_sort_reconstruct] def reconstructSetSort : Smt.SortReconstructor := fun s => do
  match s.getKind! with
  | .SET_SORT =>
    let e := s.getSetElementSort!
    unless e.isTuple do return none
    let ts := e.getTupleSorts!
    if ts.size == 2 then
      let a ← reconstructElementSort ts[0]!
      let b ← reconstructElementSort ts[1]!
      return mkApp (mkConst ``Fren.FinSet [Level.zero]) (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b)
    unless ts.size == 1 do return none
    let α ← reconstructElementSort ts[0]!
    return mkApp (mkConst ``Fren.FinSet [Level.zero]) α
  | _ => return none

@[smt_term_reconstruct] def reconstructSet : Smt.TermReconstructor := fun t => do
  let setOf (ty : Expr) : Option Expr := if ty.isAppOfArity ``Fren.FinSet 1 then some ty.appArg! else none
  match t.getKind! with
  | .SET_EMPTY =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := setOf ty | return none
    return mkApp2 (mkConst ``EmptyCollection.emptyCollection [Level.zero]) ty
      (mkApp (mkConst ``Fren.FinSet.instEmptyCollection [Level.zero]) α)
  | .SET_SINGLETON =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := setOf ty | return none
    -- The member is a 1-tuple, whose only field is its last child, or a
    -- relation's 2-tuple, a pair.
    let tup := t[0]!
    let n := tup.getNumChildren
    let x ← if α.isAppOfArity ``Prod 2 then
        pure (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α.appFn!.appArg! α.appArg!
          (← reconstructElement tup[n - 2]!) (← reconstructElement tup[n - 1]!))
      else reconstructElement tup[n - 1]!
    return mkApp4 (mkConst ``Singleton.singleton [Level.zero, Level.zero]) α ty
      (mkApp (mkConst ``Fren.FinSet.instSingleton [Level.zero]) α) x
  | .SET_UNION =>
    let ty ← Smt.Reconstruct.reconstructSort t.getSort!
    let some α := setOf ty | return none
    return mkApp4 (mkConst ``Union.union [Level.zero]) ty (mkApp (mkConst ``Fren.FinSet.instUnion [Level.zero]) α)
      (← Smt.Reconstruct.reconstructTerm t[0]!) (← Smt.Reconstruct.reconstructTerm t[1]!)
  | _ => return none

/-- A string in a model. -/
@[smt_sort_reconstruct] def reconstructStringSort : Smt.SortReconstructor := fun s => do
  match s.getKind! with
  | .STRING_SORT => return mkConst ``String
  | _ => return none

@[smt_term_reconstruct] def reconstructString : Smt.TermReconstructor := fun t => do
  match t.getKind! with
  | .CONST_STRING => return (Fren.Core.parseSmtString? (toString t)).map mkStrLit
  | _ => return none

/-! ## Lean `match`es, of structural recursions

A structural recursion's definition, which the solver is given as a
recursive definition (`Reqs/Lang/Recursion#solver-encoding`), is a Lean `match`
(`lang::recursive_match`): its matcher's `casesOn`s are a chain of `ite`s
on the constructors' testers, each arm with its fields read by the
selectors. -/

/-- The arm `minor` of a `casesOn`, whose fields are `sels`, the selectors
applied to the value, each bound by an SMT-LIB `let`. -/
partial def casesOnArm (minor : Expr) (sels : List Smt.Term) (extra : Array Expr := #[]) : TranslationM Smt.Term := do
  match sels, minor with
  | [], _ => applyTranslators! (← Lean.Core.betaReduce (mkAppN minor extra))
  | s :: rest, .lam n t b bi => withScopedName n.eraseMacroScopes b fun n => do
    let tmB ← Meta.withLocalDecl n bi t fun x => do
      modify fun st => { st with localFVars := st.localFVars.insert x.fvarId! }
      let r ← casesOnArm (b.instantiate1 x) rest extra
      modify fun st => { st with localFVars := st.localFVars.erase x.fvarId! }
      return r
    return letT n.toString s tmB
  | _, _ => casesOnArm (← Meta.etaExpand minor) sels extra

/-- `T.casesOn` of an enumeration's value, without indices, as `ite`s on
its constructors' testers. -/
@[smt_translate] def translateCasesOn : Translator := fun e => do
  let .const c _ := e.getAppFn | return none
  let env ← getEnv
  unless isCasesOnRecursor env c do return none
  let some (.inductInfo i) := env.find? c.getPrefix | return none
  if i.numIndices != 0 then return none
  let args := e.getAppArgs
  -- With any arguments after the minor premises, where the motive is a
  -- function's type, applied to each arm.
  let base := i.numParams + 2 + i.ctors.length
  unless args.size ≥ base do return none
  let major := args[i.numParams + 1]!
  let minors := args.extract (i.numParams + 2) base
  let extra := args.extract base args.size
  let majorT ← applyTranslators! major
  let mut out : Option Smt.Term := none
  for (ctor, minor) in (i.ctors.zip minors.toList).reverse do
    let some (.ctorInfo cv) := env.find? ctor | return none
    let mut sels := #[]
    for k in [0:cv.numFields] do
      let some s ← selectorApp ctor (leanSmtField cv k) major | return none
      sels := sels.push s
    let arm ← casesOnArm minor sels.toList extra
    out := some <| match out with
      | none => arm
      | some rest => Smt.Term.mkApp3 (symbolT "ite") (appT (literalT s!"(_ is {Smt.Term.quoteSymbol ctor.toString})") majorT) arm rest
  return out

/-- A sparse `casesOn`, which a matcher may be of, on some constructors and
a default for the rest, as the `casesOn` of its definition. -/
@[smt_translate] def translateSparseCasesOn : Translator := fun e => do
  let .const f _ := e.getAppFn | return none
  let .str _ s := f | return none
  unless s.startsWith "_sparseCasesOn" do return none
  let some e' ← Meta.delta? e (· == f) | return none
  return some (← applyTranslators! (← Lean.Core.betaReduce e'))

/-- A matcher's application, a Lean `match`, as the `casesOn`s of its
definition. -/
@[smt_translate] def translateMatcher : Translator := fun e => do
  let .const f _ := e.getAppFn | return none
  let some info ← Meta.getMatcherInfo? f | return none
  if e.getAppNumArgs != info.arity then return none
  let some e' ← Meta.delta? e (· == f) | return none
  return some (← applyTranslators! (← Lean.Core.betaReduce e'))

end Fren
