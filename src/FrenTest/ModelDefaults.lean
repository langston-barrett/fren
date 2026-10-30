-- keep-sorted start
import Fren.Check
import Fren.View
import FrenCli.Confirm
-- keep-sorted end
open Fren.Lang

/-!
The default values that fill what a model leaves free
(`Reqs/Models#free-values`, `model::default_value`), as both front ends
give them: the `fren` command's `Spec.defaultVal` and the Lean-hosted
front end's `Fren.defaultValue`, at an enumeration whose first variant has
one, one whose first variant's payload is the enumeration itself, a
record, a newtype and a generic enumeration, each shown as a
counterexample shows it.
-/

-- fren-covers: model::fill_rule

mod model_defaults_test

pub enum F { L(Seq<Int>), N(F) }
pub enum G { N(G), L }
pub struct Ms(Int)
pub struct P { x: Int, on?, ms: Ms, s: Set<Int>, t: String }
pub enum W { Wrapped(P, G), Bare }

/-- The types, and the default value that `model::default_value` gives each. -/
def defaultCases : Array (Lean.Name × String) := #[
  (`model_defaults_test.F, "F::L([])"),
  (`model_defaults_test.G, "G::L"),
  (`model_defaults_test.Ms, "Ms(0)"),
  (`model_defaults_test.P, "P { x := 0, on? := false, ms := Ms(0), s := {}, t := \"\" }"),
  (`model_defaults_test.W, "W::Wrapped(P { x := 0, on? := false, ms := Ms(0), s := {}, t := \"\" }, G::L)")]

-- The Lean-hosted front end's.
open Lean Meta in
run_meta do
  let st ← Fren.getState
  for (path, expected) in defaultCases do
    let decl? := (st.enums.get? path).map (·.decl) <|> (st.records.get? path).map (·.decl)
      <|> (st.newtypes.get? path).map (·.decl)
    let some decl := decl? | throwError "no type `{path}`"
    let some v ← Fren.defaultValue (mkConst decl) | throwError "no default value of `{path}`"
    let shown ← Fren.render (mkConst decl) v
    unless shown == expected do throwError "`{path}`: {shown}, not {expected}"

def defaultsSrc : String := "mod model_defaults_test
pub enum F { L(Seq<Int>), N(F) }
pub enum G { N(G), L }
pub struct Ms(Int)
pub struct P { x: Int, on?, ms: Ms, s: Set<Int>, t: String }
pub enum W { Wrapped(P, G), Bare }
"

-- The `fren` command's.
open FrenCli FrenCli.Eval in
#guard
  match specOf #[("t.fren", defaultsSrc.toList.toArray)] with
  | .ok sp => defaultCases.all fun (path, expected) =>
    let ty : VTy := match sp.newtypes.find? path with
      | some u => .newtype path u
      | none => .data path []
    (sp.defaultVal ty).map (·.showAs sp ty) == some expected
  | .error _ => false
