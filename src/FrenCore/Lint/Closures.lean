-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Lint.Text
import FrenCore.Names
-- keep-sorted end

/-!
# Closure and higher order argument lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Closures -/

/-- What the body of a closure applies, as `redundant_closure` reads it
(`lint::Callee`): a defined function that is not generic nor higher-order,
the enclosing function's function parameter, or anything else, such as a
generic function, whose type arguments the closure may fix. -/
inductive Callee where
  | defined
  | fnParameter
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `redundant_closure` fires on a closure of `nParams` parameters
whose body, without parentheses, is an application (`applies`) of
`callee`, whose arguments are `args`, each the position of the closure's
parameter that it is, if it is one, written as its name alone, and where
`exact` says that the callee's parameters' and result's types are the
function type's, without a subset type (`lint::redundant_closure`): the
closure applies the function to its parameters, in order, each once. -/
def redundantClosure (nParams : Nat) (args : List (Option Nat)) (applies : Bool) (callee : Callee) (exact : Bool) : Bool :=
  applies && callee != .other && exact && args == (List.range nParams).map some

/-- `redundant_closure` on a closure that only applies the function
written `g` to its parameters. -/
def redundantClosureMsg (g : String) : Msg :=
  { code? := some Lint.redundantClosure.code
    headline := s!"this closure only applies `{g}` to its parameters"
    label? := some s!"`{g}` with extra steps"
    notes := #[s!"note: the name `{g}` given here means this closure"]
    fixes := #[{ msg := s!"write `{g}`", replacement := g }] }

/-- Whether a closure's parameter named `n` is left out of `unused_variables`
(`lint::unused_closure_params`): `_`, which declares no name, and a name
that starts with `_`. -/
def closureParamOptedOut (n : String) : Bool := n.startsWith "_" || n.startsWith "#_"

/-- A parameter of a closure that its body never mentions. -/
def unusedClosureParamMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused closure parameter `{n}`", label? := some "never mentioned"
    notes := #["note: the closure's value does not depend on it",
      "help: write `_` in its place, start its name with `_`, or mention it in the body"] }

/-- Whether `redundant_type_annotations` fires on a closure's parameter,
from whether its type is written, and whether the function type already
gives it, rather than the annotation fixing a type argument
(`lint::redundant_type_annotations`). -/
def redundantTypeAnnotation (written known : Bool) : Bool := written && known

/-- `redundant_type_annotations` on the type `t` of the closure's parameter
`x`, whose fix removes it. -/
def redundantTypeAnnotationMsg (x t : String) : Msg :=
  { code? := some Lint.redundantTypeAnnotations.code
    headline := s!"the type of `{x}` is the function type's, `{t}`"
    label? := some "given by the function type"
    notes := #["note: a closure's parameter has the type of the function type's parameter, which is written once, in the signature"]
    fixes := #[{ msg := "remove the type", replacement := "" }] }

/-- A function parameter of a private higher-order function, declared at
`ref`, with the level of `needless_higher_order` there
(`lint::needless_higher_order`). -/
structure HofParamRecord where
  path : Name
  /-- Its position among the function's parameters. -/
  index : Nat
  name : Name
  /-- The function is generic: its body is written over its type
  parameters, where a closure's body need not type-check. -/
  generic : Bool
  level : LevelInEffect
  deriving Inhabited

/-- What an application of the higher-order function `path` gives its
parameter at `index`: a closure, a lambda match or a function's name, as
written, whether it is a lambda match, and the names it has free, but for
a closure's own parameters (`lint::closure_names`). Each of those may mean something else in the
function's body, or nothing: a name of where it is written (a variable, a
binder, a parameter, a call, a `let`), an item declared after the
function, or one that the function's parameters shadow
(`lint::needless_higher_order`). -/
structure FnArgRecord where
  path : Name
  index : Nat
  text : String
  /-- It is a lambda match, `match { P => e, ... }`, whose arms are not
  read. -/
  lambdaMatch : Bool
  names : Array String
  deriving Inhabited

/-- Whether `needless_higher_order` fires on a function parameter, from
what the applications of its function give it, as written, whether one of
them mentions a name (`FnArgRecord.names`), whether one is a lambda match,
and whether the function is generic (`lint::needless_higher_order`): there
is one, each is the same as the first, by `same`, none mentions a name,
none is a lambda match, and the function is not generic. -/
def needlessHigherOrderBy (same : String → String → Bool) (texts : List String) (named lambdaMatch generic : Bool) : Bool :=
  match texts with
  | [] => false
  | t :: ts => !named && !lambdaMatch && !generic && ts.all (same · t)

/-- `needlessHigherOrderBy`, comparing the texts as written
(`writtenSame`). -/
def needlessHigherOrder (texts : List String) (named lambdaMatch generic : Bool) : Bool :=
  needlessHigherOrderBy writtenSame texts named lambdaMatch generic

def needlessHigherOrderMsg (f p : Name) (text : String) : Msg :=
  { code? := some Lint.needlessHigherOrder.code
    headline := s!"each application of `{f.getString!}` gives `{p}` the same function"
    label? := some s!"always `{text}`"
    notes := #[s!"note: every application in this file gives `{text}`, and `{f.getString!}` is private",
      s!"help: apply it in the body of `{f.getString!}` where `{p}` is applied, writing its body with `{p}`'s arguments, and remove the parameter"] }

/-- The `needless_higher_order` messages of a file's private higher-order
functions' function parameters `params`, from what the applications in
the file give them, `args`. -/
def needlessHigherOrderReports (params : Array (HofParamRecord × α)) (args : Array FnArgRecord) : Array (LintReport α) :=
  params.filterMap fun (p, ref) =>
    let given := args.filter fun a => a.path == p.path && a.index == p.index
    if needlessHigherOrder (given.toList.map (·.text)) (given.any (!·.names.isEmpty)) (given.any (·.lambdaMatch)) p.generic then
      some { lint := .needlessHigherOrder, level := p.level, ref, msg := needlessHigherOrderMsg p.path p.name given[0]!.text }
    else none

end Fren.Core
