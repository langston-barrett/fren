-- keep-sorted start
import Fren.FinSet
import Fren.SentenceBridge
import Fren.Seq
import FrenCli.SentenceBridge
import FrenCore.GroundClosure
import Lean.Elab.Command
import Lean.Meta.Check
-- keep-sorted end

/-! Executable projection, instantiation and reconstruction, independent of
the structural theory dump and the existing check pipeline (#758). -/
-- fren-covers: lang::bridge_reference_step, lang::bridge_unique_step
-- fren-covers: lang::theory_instance, lang::ground_close_step

namespace FrenTest.SentenceBridge

open Lean
open Fren.Core Fren.Core.SentenceBridge
open FrenCli.SeqElems (SExpr parse)

private def f (x : Int) : Int := x
private def g (x : Int) : Int := x + 1
private def relation (x y : Int) : Prop := x = y
private def ident (α : Type) (x : α) : α := x
private axiom a : Int
private axiom x : Int
private axiom y : Int
private axiom alias : Int
private axiom zero : Int

private def fn : Head := ⟨.item `M.f, [], [.int], .int⟩
private def gn : Head := ⟨.item `M.g, [], [.int], .int⟩
private def pn : Head := ⟨.item `M.p, [], [.int, .int], .bool⟩
private def eqn : Head := ⟨.builtin "=", [], [.int, .int], .bool⟩
private def cn : Head := ⟨.constant `M.zero, [], [], .int⟩
private def gnInt : Head := ⟨.item `M.id, [.int], [.int], .int⟩
private def intTy : Expr := mkConst ``Int
private def eqInt : Expr := mkApp (mkConst ``Eq [1]) intTy
private def one : Expr := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)

private def lean : Fren.SentenceBridge.Adapter := {
  heads := [(fn, mkConst ``f), (gn, mkConst ``g), (pn, mkConst ``relation),
    (eqn, eqInt), (cn, mkConst ``zero), (gnInt, mkApp (mkConst ``ident) intTy)]
  parameters := [(`x, .int, mkConst ``x), (`y, .int, mkConst ``y)]
  locals := [(`a, .int, mkConst ``a), (`alias, .int, mkConst ``alias)]
  types := [(.int, intTy)]
  values := [(⟨.int, "1"⟩, one), (⟨.bool, "true"⟩, mkConst ``True)]
  items := [`M.zero, `M.g, `M.id, `M.f, `M.p]
}

private def smt : FrenCli.SentenceBridge.Adapter := {
  heads := [(fn, parse "|::M::f|"), (gn, parse "|::M::g|"), (pn, parse "|::M::p|"),
    (eqn, parse "="), (cn, parse "|::M::zero|"), (gnInt, parse "|::M::id<Int>|")]
  parameters := [(`x, .int, parse "|x|"), (`y, .int, parse "|y|")]
  -- This name would be captured by a reconstruction that only counted binders.
  locals := [(`a, .int, parse "fren.bridge.0"), (`alias, .int, parse "|alias|")]
  types := [(.int, parse "Int")]
  values := [(⟨.int, "1"⟩, parse "1"), (⟨.bool, "true"⟩, parse "true")]
  items := lean.items
}

private def claimLean : Expr := mkApp2 eqInt (mkApp (mkConst ``f) (mkConst ``x)) (mkConst ``y)
private def sourceLean : Sentence Expr := {
  name := `M.law, role := .theorem, variables := [(`x, .int), (`y, .int)]
  domain := mkApp2 eqInt (mkConst ``x) (mkConst ``x)
  calls := [(`call, mkApp2 (mkConst ``relation) (mkConst ``x) (mkConst ``y))]
  claims := [(`claim, claimLean), (`nested, .forallE `v intTy
    (mkApp2 eqInt (mkConst ``x) (.bvar 0)) .default)]
}
private def sourceSmt : Sentence SExpr := {
  name := `M.law, role := .theorem, variables := sourceLean.variables
  domain := parse "(= |x| |x|)"
  calls := [(`call, parse "(|::M::p| |x| |y|)")]
  claims := [(`claim, parse "(= (|::M::f| |x|) |y|)"),
    (`nested, parse "(forall ((v Int)) (= |x| v))")]
}

private def projected := Fren.SentenceBridge.sentence lean sourceLean
private def projectedSmt := FrenCli.SentenceBridge.sentence smt sourceSmt
#guard projected.map Sentence.theory == projectedSmt.map Sentence.theory
#guard projected.isSome
#guard projected.map (·.claims.map (·.1)) == some [`claim, `nested]

private def image := TheoryTerm.app gn.term (.query `a)
private def images : Name → Option TheoryTerm
  | `x => some image
  | `y => some (Value.term ⟨.int, "1"⟩)
  | _ => none
private def instanceSentence := projected.bind (·.instantiate images)
private def rebuiltLean := instanceSentence.bind (Fren.SentenceBridge.rebuildSentence lean)
private def rebuiltSmt := instanceSentence.bind (FrenCli.SentenceBridge.rebuildSentence smt)
#guard instanceSentence.isSome && rebuiltLean.isSome && rebuiltSmt.isSome
#guard (rebuiltLean.bind (Fren.SentenceBridge.sentence lean)).map Sentence.theory ==
  instanceSentence.map Sentence.theory
#guard (rebuiltSmt.bind (FrenCli.SentenceBridge.sentence smt)).map Sentence.theory ==
  instanceSentence.map Sentence.theory
#guard rebuiltSmt.map (·.claims[1]!.2.toString) ==
  some "(forall ((fren.bridge.1 Int)) (= (|::M::g| fren.bridge.0) fren.bridge.1))"
#guard instanceSentence.map (·.variables) == some []
#guard instanceSentence.map (·.calls.map (·.1)) == some [`call]
#guard instanceSentence.map (·.role) == some .theorem
#guard (projected.bind (·.instantiate fun _ => some (.bound 0))).isNone
#guard (Fren.SentenceBridge.rebuildSentence lean
  { projected.get! with domain := .query `a }).isNone
#guard (FrenCli.SentenceBridge.rebuildSentence smt
  { projected.get! with claims := [(`bad, .query `a)] }).isNone

-- Query extraction feeds the actual matcher and closure. Calls have their
-- own channel; nested function applications remain visible in their inputs.
private def qLean := Fren.SentenceBridge.query lean
  [mkApp (mkConst ``f) (mkApp (mkConst ``g) (mkConst ``a))]
  [mkApp2 (mkConst ``relation) (mkApp (mkConst ``g) (mkConst ``a)) one]
private def qSmt := FrenCli.SentenceBridge.query smt
  [parse "(|::M::f| (|::M::g| fren.bridge.0))"]
  [parse "(|::M::p| (|::M::g| fren.bridge.0) 1)"]
#guard qLean.map (·.applications) == qSmt.map (·.applications)
#guard qLean.map (·.calls) == qSmt.map (·.calls)
#guard qLean.isSome
private def ctx := context lean.signature
#guard ctx.typeOf image == some .int
#guard ctx.typeOf (.app fn.term (.literal "untyped")) == none
private def closed := Fren.Core.GroundClosure.close ctx
  [⟨projected.get!.theory⟩] qLean.get!
#guard closed.instanceList.length == 1
#guard closed.instanceList[0]!.sentence == instanceSentence.get!.theory
private def fromClosure := sourceLean.withInstance closed.instanceList[0]!.sentence
#guard (fromClosure.bind (Fren.SentenceBridge.rebuildSentence lean) |>.bind
  (Fren.SentenceBridge.sentence lean)).map Sentence.theory == some closed.instanceList[0]!.sentence
#guard (fromClosure.bind (FrenCli.SentenceBridge.rebuildSentence smt) |>.bind
  (FrenCli.SentenceBridge.sentence smt)).map Sentence.theory == some closed.instanceList[0]!.sentence
#guard (sourceLean.withInstance { closed.instanceList[0]!.sentence with calls := [] }).isNone

-- Definitions use the existing matching normalizer, including a constant
-- and two lexical aliases. Function heads stay opaque.
private def defs : List (TheoryTerm × TheoryTerm) := [
  (.query `alias, .item `M.zero), (.item `M.zero, image)]
private def normalized := GroundMatching.prepareQuery (context lean.signature defs)
  (GroundMatching.definitions defs) { applications := [.app fn.term (.query `alias)] }
#guard normalized.applications.contains (.app fn.term image)
#guard Fren.SentenceBridge.project lean []
  (.letE `v intTy (mkConst ``a) (mkApp (mkConst ``f) (.bvar 0)) false) ==
  some (.app fn.term (.query `a))
#guard FrenCli.SentenceBridge.project smt []
  (parse "(let ((v fren.bridge.0)) (|::M::f| v))") == some (.app fn.term (.query `a))

private def extractedContext := Fren.SentenceBridge.context lean
  [(mkConst ``alias, mkConst ``zero), (mkConst ``zero, mkApp (mkConst ``g) (mkConst ``a))]
  [(.int, [one]), (.enum `Empty [], [])]
private def extractedSmtContext := FrenCli.SentenceBridge.context smt
  [(parse "|alias|", parse "|::M::zero|"), (parse "|::M::zero|", parse "(|::M::g| fren.bridge.0)")]
  [(.int, [parse "1"]), (.enum `Empty [], [])]
#guard extractedContext.map (·.definitions) == some defs
#guard extractedSmtContext.map (·.definitions) == some defs
#guard (extractedContext.bind fun c => c.listed .int) == some [Value.term ⟨.int, "1"⟩]
#guard (extractedSmtContext.bind fun c => c.listed (.enum `Empty [])) == some []
#guard (extractedContext.bind fun c => c.listed (.enum `Unknown [])) == none
#guard (Fren.SentenceBridge.context lean [(mkApp (mkConst ``f) (mkConst ``a), one)] []).isNone
#guard (FrenCli.SentenceBridge.context smt [] [(.string, [parse "1"])]).isNone
#guard (Fren.SentenceBridge.sentence lean { sourceLean with variables := [(`x, .string)] }).isNone

-- An alias of an outer bound variable must be lifted under the inner one.
private def aliasUnderBinder := FrenCli.SentenceBridge.project smt []
  (parse "(forall ((v Int)) (let ((a v)) (exists ((v Int)) (= a v))))")
#guard aliasUnderBinder == some (.all .int (.ex .int
  (.app (.app eqn.term (.bound 1)) (.bound 0))))

private def implicationLean : Expr := .forallE `v intTy
  (.forallE `proof (mkApp2 eqInt (.bvar 0) (mkConst ``a))
    (mkApp2 eqInt (mkApp (mkConst ``g) (.bvar 1)) (mkConst ``a)) .default) .default
private def implicationProjected := Fren.SentenceBridge.project lean [] implicationLean
#guard implicationProjected.isSome
#guard implicationProjected == FrenCli.SentenceBridge.project smt []
  (parse "(forall ((v Int)) (=> (= v fren.bridge.0) (= (|::M::g| v) fren.bridge.0)))")
#guard (implicationProjected.bind (Fren.SentenceBridge.rebuild lean []) |>.bind
  (Fren.SentenceBridge.project lean [])) == implicationProjected

-- A backend-only prefix may contain type and instance arguments, but must
-- not hide a sentence parameter inside the symbol's identity.
#guard (Fren.SentenceBridge.project
  { lean with heads := [(⟨.item `M.hidden, [], [], .int⟩, mkApp (mkConst ``f) (mkConst ``x))] }
  [(`x, .int)] (mkApp (mkConst ``f) (mkConst ``x))).isNone
#guard FrenCli.SentenceBridge.project smt [(`x, .int)]
  (parse "(let ((|x| fren.bridge.0) (v |x|)) (= |x| v))") ==
  some (.app (.app eqn.term (.query `a)) (.variable `x))

-- Generic heads retain explicit type arguments, independently of backend
-- spelling and of implicit Lean arguments.
#guard Fren.SentenceBridge.project lean []
  (mkApp2 (mkConst ``ident) intTy (mkConst ``a)) ==
  FrenCli.SentenceBridge.project smt [] (parse "(|::M::id<Int>| fren.bridge.0)")
#guard Fren.SentenceBridge.project lean [] (mkApp (mkConst ``f) (mkConst ``True)) == none
#guard FrenCli.SentenceBridge.project smt [] (parse "(unknown fren.bridge.0)") == none
#guard Fren.SentenceBridge.project lean [] (.bvar 0) == none
#guard FrenCli.SentenceBridge.project smt [] (parse "(|::M::f|)") == none
#guard FrenCli.SentenceBridge.project smt [] (parse "(forall ((v Unknown)) true)") == none

-- Nullary functions are still applications; constants remain expandable
-- references. The distinction is shared, not guessed from backend arity.
private def nullary : Head := ⟨.item `M.tick, [], [], .int⟩
private def nullaryLean := { lean with heads := (nullary, mkConst ``zero) :: lean.heads.filter (·.1 != cn) }
private def nullarySmt := { smt with heads := (nullary, parse "|::M::tick|") :: smt.heads }
#guard Fren.SentenceBridge.project nullaryLean [] (mkConst ``zero) == some nullary.term
#guard FrenCli.SentenceBridge.project nullarySmt [] (parse "|::M::tick|") == some nullary.term
#guard GroundMatching.applications [`M.tick] nullary.term == [nullary.term]
#guard nullary.term != cn.term

private def optionTy := Ty.enum `Option [.int]
private def noneHead : Head := ⟨.constant `Option.None, [.int], [], optionTy⟩
private def noneLean := mkApp (mkConst ``Option.none [0]) intTy
private def noneSmt := parse "(as |Option.none| (Option Int))"
private def constructorLean := { lean with heads := (noneHead, noneLean) :: lean.heads }
private def constructorSmt := { smt with heads := (noneHead, noneSmt) :: smt.heads }
#guard Fren.SentenceBridge.project constructorLean [] noneLean == some noneHead.term
#guard FrenCli.SentenceBridge.project constructorSmt [] noneSmt == some noneHead.term
#guard Fren.SentenceBridge.rebuild constructorLean [] noneHead.term == some noneLean
#guard FrenCli.SentenceBridge.rebuild constructorSmt [] noneHead.term == some noneSmt

private def stringValue : Value := ⟨.string, "a\"|x|"⟩
private def stringLean := mkStrLit stringValue.text
private def stringSmt := parse "\"a\"\"|x|\""
private def literalLean := { lean with values := (stringValue, stringLean) :: lean.values }
private def literalSmt := { smt with values := (stringValue, stringSmt) :: smt.values }
#guard Fren.SentenceBridge.project literalLean [] stringLean == some stringValue.term
#guard FrenCli.SentenceBridge.project literalSmt [] stringSmt == some stringValue.term
#guard Fren.SentenceBridge.rebuild literalLean [] stringValue.term == some stringLean
#guard FrenCli.SentenceBridge.rebuild literalSmt [] stringValue.term == some stringSmt

-- Erased literals are resolved by the expected argument type, never by
-- table order. Without an expected type, ambiguity is rejected.
private def acceptsNat : Head := ⟨.builtin "accept", [], [.nat], .bool⟩
private def erased : FrenCli.SentenceBridge.Adapter := {
  smt with
  heads := (acceptsNat, parse "accept") :: smt.heads
  values := (⟨.nat, "1"⟩, parse "1") :: smt.values
}
#guard FrenCli.SentenceBridge.project erased [] (parse "1") == none
#guard FrenCli.SentenceBridge.project erased [] (parse "(accept 1)") ==
  some (.app acceptsNat.term (Value.term ⟨.nat, "1"⟩))
#guard Value.term ⟨.nat, "1"⟩ != Value.term ⟨.int, "1"⟩
#guard Value.term ⟨.string, "1"⟩ != Value.term ⟨.int, "1"⟩
#guard (FrenCli.SentenceBridge.project { smt with heads := smt.heads ++ smt.heads } []
  (parse "(|::M::f| fren.bridge.0)")).isNone

-- Parameter names and query names may coincide. Their native references and
-- namespaces remain separate even beneath a binder or a partial substitution.
private def collisionLean : Fren.SentenceBridge.Adapter := {
  lean with locals := (`x, .int, mkConst ``a) :: lean.locals.filter (·.1 != `a)
}
private def collisionSmt : FrenCli.SentenceBridge.Adapter := {
  smt with locals := (`x, .int, parse "free.x") :: smt.locals
}
private def collision := projected.bind (·.instantiate fun n =>
  if n == `x then some (.query `x) else none)
#guard Fren.SentenceBridge.project collisionLean [] (mkConst ``x) == none
#guard FrenCli.SentenceBridge.project collisionSmt [] (parse "|x|") == none
#guard (collision.bind (Fren.SentenceBridge.rebuildSentence collisionLean) |>.bind
  (Fren.SentenceBridge.sentence collisionLean)).map Sentence.theory == collision.map Sentence.theory
#guard (collision.bind (FrenCli.SentenceBridge.rebuildSentence collisionSmt) |>.bind
  (FrenCli.SentenceBridge.sentence collisionSmt)).map Sentence.theory == collision.map Sentence.theory

private inductive Color where | red | blue
private structure Box (α : Type) where value : α
private axiom Abstract : Type
private def Age := Int

private def typeCases : Array (Ty × Expr × SExpr) := #[
  (.bool, mkSort .zero, parse "Bool"),
  (.int, intTy, parse "Int"),
  (.nat, mkConst ``Nat, parse "Int"),
  (.string, mkConst ``String, parse "String"),
  (.set .int, mkApp (mkConst ``Fren.FinSet [0]) intTy, parse "(Set (Tuple Int))"),
  (.rel .int .string, mkApp (mkConst ``Fren.FinSet [0])
    (mkApp2 (mkConst ``Prod [0, 0]) intTy (mkConst ``String)), parse "(Set (Tuple Int String))"),
  (.seq .int, mkApp (mkConst ``Fren.Seq [0]) intTy, parse "(Seq Int)"),
  (.enum `Color [], mkConst ``Color, parse "|Color|"),
  (.enum `Option [.int], mkApp (mkConst ``Option [0]) intTy, parse "(|Option| Int)"),
  (.record `Box [.int], mkApp (mkConst ``Box) intTy, parse "(|Box| Int)"),
  (.abstract `Abstract, mkConst ``Abstract, parse "|::Abstract|"),
  (.newtype `Age .int, mkConst ``Age, parse "Int"),
  (.param 0 `T, mkConst ``Abstract, parse "|T|")]

-- The kernel checks native expressions, rather than the bridge's metadata
-- type checker checking its own result. Include universes 0, 1 and 2, mixed
-- and nested binders, and every native type used by the bounded generator.
#guard (Fren.SentenceBridge.rebuild lean []
  (.ex .int (Value.term ⟨.bool, "true"⟩))).isNone

open Lean Meta in
run_meta do
  let domains := typeCases.toList ++ [
    (.abstract `Proof, mkConst ``True, parse "Bool"),
    (.abstract `Higher, mkSort 1, parse "Type")]
  for (ty, native, _) in domains do
    checkWithKernel native
    let b ← Fren.SentenceBridge.Adapter.ofBindings {
      types := [(ty, native)], values := [(⟨.bool, "true"⟩, mkConst ``True)] }
    let body := Value.term ⟨.bool, "true"⟩
    for term in [TheoryTerm.ex ty body, .ex ty (.ex ty body),
        .all ty (.ex ty (.all ty body))] do
      let some rebuilt := Fren.SentenceBridge.rebuild b [] term
        | throwError "existential reconstruction failed"
      checkWithKernel rebuilt
      unless Fren.SentenceBridge.project b [] rebuilt == some term do
        throwError "existential reconstruction changed the projected formula"
  let b ← Fren.SentenceBridge.Adapter.ofBindings lean.toBindings
  let term := TheoryTerm.ex .int (.ex .int (.app (.app eqn.term (.bound 1)) (.bound 0)))
  let some rebuilt := Fren.SentenceBridge.rebuild b [] term
    | throwError "nested existential reconstruction failed"
  checkWithKernel rebuilt
  unless Fren.SentenceBridge.project b [] rebuilt == some term do
    throwError "nested existential reconstruction captured a bound variable"
  for s in [rebuiltLean, collision.bind (Fren.SentenceBridge.rebuildSentence collisionLean),
      fromClosure.bind (Fren.SentenceBridge.rebuildSentence lean)] do
    let some s := s | throwError "sentence reconstruction failed"
    for formula in s.domain :: (s.calls ++ s.claims).map (·.2) do
      checkWithKernel formula
  for e in [Fren.SentenceBridge.rebuild constructorLean [] noneHead.term,
      Fren.SentenceBridge.rebuild literalLean [] stringValue.term,
      Fren.SentenceBridge.rebuild nullaryLean [] nullary.term,
      implicationProjected.bind (Fren.SentenceBridge.rebuild lean [])] do
    let some e := e | throwError "native reconstruction failed"
    checkWithKernel e
  -- These negative controls are the reviewed bugs: structural round trips
  -- alone accepted them, while native type checking must reject both.
  let badExists := mkApp2 (mkConst ``Exists [0]) intTy
    (.lam .anonymous intTy (mkConst ``True) .default)
  for bad in [badExists, mkApp (mkConst ``Box [0]) intTy] do
    if (Kernel.check (← getEnv) (← getLCtx) bad).isOk then
      throwError "kernel accepted an incorrect universe argument"

/-- A bounded generator for the new bridge, independent of the existing
front-end corpus. It varies types, generic instances and application depth;
both concrete representations must project and rebuild the same term, and
the kernel must accept the native types, inputs and reconstructed results. -/
unsafe def check (seed : Nat := 758100) (count : Nat := 100) : IO (Array String) := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `FrenTest.SentenceBridge }] {} (loadExts := true)
  let mut failures := #[]
  for i in [:count] do
    let k := seed + i * 37
    let (ty, nativeTy, sort) := typeCases[k % typeCases.size]!
    let h : Head := ⟨.item `generic.id, [ty], [ty], ty⟩
    let nativeHead := mkApp (mkConst ``ident) nativeTy
    let nativeLocal := mkFVar ⟨`local⟩
    let l : Fren.SentenceBridge.Adapter := {
      heads := [(h, nativeHead)], locals := [(`a, ty, nativeLocal)],
      types := [(ty, nativeTy)], items := [`generic.id] }
    let s : FrenCli.SentenceBridge.Adapter := {
      heads := [(h, parse "|::generic::id<T>|")], locals := [(`a, ty, parse "|a|")],
      types := [(ty, sort)], items := [`generic.id] }
    let mut le := nativeLocal
    let mut se := parse "|a|"
    for _ in [:k % 5 + 1] do
      le := mkApp nativeHead le
      se := .list #[parse "|::generic::id<T>|", se]
    let lt := Fren.SentenceBridge.project l [] le
    let st := FrenCli.SentenceBridge.project s [] se
    let rebuilt := lt.bind (Fren.SentenceBridge.rebuild l [])
    let nativeGood := (Kernel.check env {} nativeTy).isOk &&
      [some le, rebuilt].all fun result => match result with
        | none => false
        | some e =>
          let closed := mkLambda `a .default nativeTy (e.abstract #[nativeLocal])
          (Kernel.check env {} closed).isOk
    let good := nativeGood && lt.isSome && lt == st && rebuilt == some le &&
      (st.bind (FrenCli.SentenceBridge.rebuild s [])) == some se &&
      (lt.bind (context l.signature).typeOf) == some ty
    unless good do failures := failures.push s!"sentence bridge seed {k}: projection/rebuild/kernel type disagreement"
  return failures

end FrenTest.SentenceBridge
