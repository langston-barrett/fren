-- fren-covers: model::fill_rule
-- keep-sorted start
import Fren.Check
import Fren.View
import FrenCli.Confirm
import Reqs.Models
-- keep-sorted end
open Fren.Lang

/-!
# The fill rule of both front ends (`Reqs/Models#free-values`)

`model::default_value` gives the value that fills what a model leaves free,
and `model::fill_rule` says that both front ends' rules are it: the `fren`
command's `Eval.Spec.defaultVal` and the Lean-hosted front end's
`Fren.defaultValue`. Each is compared with the spec's own function, which
Lean generates from `Reqs/Models.md`, over the `TypeShape` of the type,
built below: so the test checks the implementations against the spec, not
against each other. The values are compared as `lang::Value`s, with the
constructor of a newtype, which neither implementation's value records,
restored, as each front end restores it when it prints one. That both front
ends then *show* the same value is checked over the strings at the end.

The types here recurse only into themselves, which is all that Fren's
types can do (`Reqs/Models#free-values`). A generic function's type
parameter is `Abstract`, as `shapeOf` maps it, and
`test/ui/misread/misread_type_parameter.fren` checks what both front ends
do with one.
-/

mod model_defaults_test

pub enum F { L(Seq<Int>), N(F) }
pub enum G { N(G), L }
pub struct Ms(Int)
pub struct P { x: Int, on?, ms: Ms, s: Set<Int>, t: String }
pub enum W { Wrapped(P, G), Bare }

namespace ModelDefaults

open Fren.Generated

/-- The types to check, and the value that each front end shows for the
default value of each. -/
def cases : Array (Lean.Name × String) := #[
  (`model_defaults_test.F, "F::L([])"),
  (`model_defaults_test.G, "G::L"),
  (`model_defaults_test.Ms, "Ms(0)"),
  (`model_defaults_test.P, "P { x := 0, on? := false, ms := Ms(0), s := {}, t := \"\" }"),
  (`model_defaults_test.W, "W::Wrapped(P { x := 0, on? := false, ms := Ms(0), s := {}, t := \"\" }, G::L)")]

/-! ## The spec's model of a type -/

open FrenCli FrenCli.Eval

/-- The `model::TypeShape` of `t`: an enumeration or a record is the list of
its variants, in the order declared, each with its constructor's full path
and the list of its payload's or fields' types, a record having one
variant, and `Itself` stands for a type within its own payload. -/
partial def shapeOf (sp : Spec) (t : VTy) (seen : List Lean.Name := []) : model.TypeShape :=
  match t with
  | .bool => .Boolean
  | .int => .Integer
  | .nat => .Natural
  | .string => .Text
  | .seq e => .Seq (shapeOf sp e seen)
  -- A relation is a set of pairs; the spec's `Set` covers both.
  | .set _ | .rel _ _ => .Set
  | .abstract _ | .param _ => .Abstract
  | .newtype p u => .Newtype (Fren.Core.showPath p) (shapeOf sp u seen)
  | .data p targs =>
    if seen.contains p then .Itself else
    match sp.data.find? p with
    | none => .Abstract
    | some d => .Data (d.ctors.foldr (init := model.TypeShape.NoVariant) fun c rest =>
        let path := if d.isRecord then Fren.Core.showPath p else s!"{Fren.Core.showPath p}::{c.name}"
        .Variant path (c.fields.foldr (init := model.TypeShape.Nil) fun (_, ft) fs =>
          .Cons (shapeOf sp (ft.subst targs) (p :: seen)) fs) rest)

/-- The value that `model::default_value` gives for the type `t`. -/
def specDefault (sp : Spec) (t : VTy) : Option lang.Value :=
  match model.default_value (shapeOf sp t) with
  | .Defined v => some v
  | .Undefined => none

/-! ## The `fren` command's rule -/

/-- `v`, a value of type `t`, as a `lang::Value`: a newtype's constructor,
which `Val` does not record, is restored, as `Val.showAs` restores it when
it prints one. A nonempty set has no `lang::Value`
(`Reqs/Lang/Semantics#what-the-model-leaves-out`), so it has none here. -/
partial def langValue (sp : Spec) (t : VTy) (v : Val) : Option lang.Value :=
  match t, v with
  | .newtype p u, _ => (langValue sp u v).map fun w =>
    .Constructed (Fren.Core.showPath p) (.Cons w .Nil)
  | _, .bool b => some (if b then .True else .False)
  | _, .int i => some (.Integer i)
  | _, .str s => some (.Text s)
  | .seq e, .seq xs => xs.foldr (init := some lang.Value.Nil) fun x rest => do
    return .Cons (← langValue sp e x) (← rest)
  | .set _, .set xs | .rel _ _, .set xs => if xs.isEmpty then some .Nil else none
  | .data p targs, .ctor _ idx args => do
    let d ← sp.data.find? p
    let c ← d.ctors[idx]?
    let path := if d.isRecord then Fren.Core.showPath p else s!"{Fren.Core.showPath p}::{c.name}"
    let fields ← (c.fields.zip args).foldr (init := some lang.Value.Nil) fun ((_, ft), a) rest => do
      return .Cons (← langValue sp (ft.subst targs) a) (← rest)
    return .Constructed path fields
  | _, _ => none

def src : String := "mod model_defaults_test
pub enum F { L(Seq<Int>), N(F) }
pub enum G { N(G), L }
pub struct Ms(Int)
pub struct P { x: Int, on?, ms: Ms, s: Set<Int>, t: String }
pub enum W { Wrapped(P, G), Bare }
"

def spec : Spec := (specOf #[("t.fren", src.toList.toArray)]).toOption.getD default

/-- The type at `path`, as the `fren` command has it. -/
def tyOf (sp : Spec) (path : Lean.Name) : VTy :=
  match sp.newtypes.find? path with
  | some u => .newtype path u
  | none => .data path []

-- Each default value of the `fren` command's rule is the spec's. Each case
-- has one, so the guard cannot pass by both rules giving none, as they would
-- if `src` failed to elaborate.
#guard cases.all fun (path, _) =>
  let ty := tyOf spec path
  let v := (spec.defaultVal ty).bind (langValue spec ty)
  v.isSome && v == specDefault spec ty

-- And each is the value that a counterexample would show.
#guard cases.all fun (path, shown) =>
  let ty := tyOf spec path
  (spec.defaultVal ty).map (·.showAs spec ty) == some shown

-- A generic function's type parameter is `Abstract`, and has no default
-- value in the spec or in the `fren` command's rule.
#guard specDefault spec (.param 0) == none && (spec.defaultVal (.param 0)).isNone

/-! ## The Lean-hosted front end's rule -/

-- Nor in the Lean-hosted front end's, where it is a local type.
open Lean Meta in
run_meta do
  if let some v ← withLocalDeclD `T (mkSort 1) fun t => Fren.defaultValue t then
    throwError "a type parameter has the default value {← ppExpr v}"

open Lean Meta in
/-- `s` as a term, to apply the generated `model::default_value` to. -/
partial def shapeExpr : model.TypeShape → Lean.Expr
  | .Boolean => mkConst ``model.TypeShape.Boolean
  | .Integer => mkConst ``model.TypeShape.Integer
  | .Natural => mkConst ``model.TypeShape.Natural
  | .Text => mkConst ``model.TypeShape.Text
  | .Seq t => mkApp (mkConst ``model.TypeShape.Seq) (shapeExpr t)
  | .Set => mkConst ``model.TypeShape.Set
  | .Abstract => mkConst ``model.TypeShape.Abstract
  | .Newtype n t => mkApp2 (mkConst ``model.TypeShape.Newtype) (mkStrLit n) (shapeExpr t)
  | .Data t => mkApp (mkConst ``model.TypeShape.Data) (shapeExpr t)
  | .Variant n a b => mkApp3 (mkConst ``model.TypeShape.Variant) (mkStrLit n) (shapeExpr a) (shapeExpr b)
  | .NoVariant => mkConst ``model.TypeShape.NoVariant
  | .Itself => mkConst ``model.TypeShape.Itself
  | .Nil => mkConst ``model.TypeShape.Nil
  | .Cons a b => mkApp2 (mkConst ``model.TypeShape.Cons) (shapeExpr a) (shapeExpr b)

open Lean Meta in
/-- The hosted front end's value `val`, of the Lean type `ty`, as a
`lang::Value` term, as `langValue` reads the `fren` command's. -/
partial def langValueExpr (ty val : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let st ← Fren.getState
  let cons (vs : Array Lean.Expr) : Lean.Expr := vs.foldr (mkApp2 (mkConst ``lang.Value.Cons))
    (mkConst ``lang.Value.Nil)
  if let some n := st.newtypeOf? ty then
    if val.isAppOfArity n.ctor 1 then
      let some w ← langValueExpr n.under val.appArg! | return none
      return some (mkApp2 (mkConst ``lang.Value.Constructed)
        (mkStrLit (Fren.Core.showPath n.path)) (cons #[w]))
  if ty.isConstOf ``Bool then
    if val.isConstOf ``Bool.false then return some (mkConst ``lang.Value.False)
    if val.isConstOf ``Bool.true then return some (mkConst ``lang.Value.True)
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then
    if let some i := Fren.intValue? val then
      return some (mkApp (mkConst ``lang.Value.Integer) (toExpr i))
  if let .lit (.strVal s) := val then return some (mkApp (mkConst ``lang.Value.Text) (mkStrLit s))
  -- Only a default value is read here, so a sequence and a set are empty.
  if ty.isAppOfArity ``Fren.Seq 1 || ty.isAppOfArity ``Fren.FinSet 1 then
    let some (_, []) := val.appArg!.listLit? | return none
    return some (mkConst ``lang.Value.Nil)
  let targs := ty.getAppArgs
  if let some r := st.recordOf? ty then
    let args := val.getAppArgs.extract r.params.size
    let some fs ← ((r.fieldsAt targs).zip args).mapM (fun ((_, t), a) => langValueExpr t a)
      <&> (·.mapM id) | return none
    return some (mkApp2 (mkConst ``lang.Value.Constructed)
      (mkStrLit (Fren.Core.showPath r.path)) (cons fs))
  if let some e := st.enumOf? ty then
    let .const c _ := val.getAppFn | return none
    let some idx := e.ctorIdx? c | return none
    let tys := (e.payloadsAt targs)[idx]?.getD #[]
    let args := val.getAppArgs.extract e.params.size
    let some ps ← (tys.zip args).mapM (fun (t, a) => langValueExpr t a) <&> (·.mapM id) | return none
    return some (mkApp2 (mkConst ``lang.Value.Constructed)
      (mkStrLit s!"{Fren.Core.showPath e.path}::{e.variants[idx]!}") (cons ps))
  return none

open Lean Meta in
run_meta do
  let st ← Fren.getState
  for (path, shown) in cases do
    let decl? := (st.enums.get? path).map (·.decl) <|> (st.records.get? path).map (·.decl)
      <|> (st.newtypes.get? path).map (·.decl)
    let some decl := decl? | throwError "no type `{path}`"
    let ty := mkConst decl
    let some v ← Fren.defaultValue ty | throwError "no default value of `{path}`"
    -- Against the spec's `model::default_value`, at the same `TypeShape`.
    let some w ← langValueExpr ty v | throwError "`{path}`: cannot read {← ppExpr v} as a `lang::Value`"
    let expected := mkApp (mkConst ``model.default_value) (shapeExpr (shapeOf spec (tyOf spec path)))
    let claim ← mkEq (mkApp (mkConst ``lang.Outcome.Defined) w) expected
    let decision ← synthInstance (mkApp (mkConst ``Decidable) claim)
    let truths ← Fren.compileValues Bool (mkConst ``Bool)
      #[mkApp2 (mkConst ``Decidable.decide) claim decision]
    unless truths == #[true] do
      throwError "`{path}`: {← ppExpr v} is not `model::default_value`'s {← ppExpr expected}"
    -- And is the value that a counterexample would show.
    let rendered ← Fren.render ty v
    unless rendered == shown do throwError "`{path}`: {rendered}, not {shown}"

end ModelDefaults
