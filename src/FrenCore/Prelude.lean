-- keep-sorted start
import Lean.Data.Name
-- keep-sorted end

/-!
# The prelude (`Reqs/Lang/Prelude`)

The items that every spec can use without declaring them, `Option<T>` and
`Result<T, E>`, written in Fren in `Prelude.fren`, which both front ends
load before every spec, into the module `preludeModule`, which no path can
name. Its types are Lean's own (`leanTypes`): the Lean-hosted front end
uses Lean's `Option` and `Except`, and the `fren` command gives the solver
exactly the declarations that lean-smt gives it for them.
-/

open Lean

namespace Fren.Core

/-- The prelude's text. -/
def preludeSource : String := include_str "Prelude.fren"

/-- The module that the prelude's items are declared in: a segment that no
Fren path can write, so that only resolution finds them
(`Reqs/Lang/Modules#resolution`), and that a path prints without
(`showPath`). -/
def preludeModule : Name := .mkSimple "#prelude"

/-- Whether `path` is the path of one of the prelude's items or variants. -/
def inPrelude (path : Name) : Bool := path.components.head? == some preludeModule

/-- A prelude type and the Lean type that it is, with the names that
lean-smt gives the solver for the Lean type's datatype, constructors and
selectors (`Reqs/Lang/Prelude#lean`). -/
structure LeanType where
  /-- The prelude type's name. -/
  name : Name
  /-- Its variants, in the order declared. -/
  variants : Array Name
  /-- The Lean type. -/
  lean : Name
  /-- The Lean type's parameters, as lean-smt names its sort parameters. -/
  leanParams : Array String
  /-- For each of the Lean type's parameters, in order, the position of the
  type parameter that it is among the prelude type's. -/
  argOrder : Array Nat
  /-- For each variant, the Lean constructor. -/
  ctors : Array Name
  /-- For each variant, lean-smt's selector of each value of its payload:
  the constructor's field's name, or `fieldk` for its `k`th field, from 1,
  if it has none of its own (`Except.error : ε → Except ε α`). -/
  selectors : Array (Array String)
  /-- The Lean constructors, in Lean's order, as positions of variants. -/
  ctorOrder : Array Nat
  deriving Inhabited, BEq, Repr

/-- The prelude's types and the Lean types that they are: `Option<T>` is
`Option T`, and `Result<T, E>` is `Except E T`, whose parameters are
`Result`'s swapped, and whose constructors, `error` before `ok`, are its
variants' swapped. -/
def leanTypes : Array LeanType := #[
  { name := `Option, variants := #[`None, `Some], lean := `Option, leanParams := #["α"], argOrder := #[0]
    ctors := #[`Option.none, `Option.some], selectors := #[#[], #["Option.some.val"]], ctorOrder := #[0, 1] },
  { name := `Result, variants := #[`Ok, `Err], lean := `Except, leanParams := #["ε", "α"], argOrder := #[1, 0]
    ctors := #[`Except.ok, `Except.error], selectors := #[#["Except.ok.field1"], #["Except.error.field1"]]
    ctorOrder := #[1, 0] }]

/-- The Lean type of the item at `path`, if it is one of the prelude's
types. -/
def leanTypeOf? (path : Name) : Option LeanType :=
  if inPrelude path then leanTypes.find? (·.name == Name.mkSimple path.getString!) else none

/-- The Lean type's arguments, in its order, from the prelude type's, in
theirs: `Result<Int, Bool>` is `Except Bool Int`. -/
def LeanType.leanArgs [Inhabited α] (l : LeanType) (args : Array α) : Array α :=
  if args.size != l.argOrder.size then args else l.argOrder.map (args[·]!)

/-- The prelude type's arguments, from the Lean type's: the inverse of
`leanArgs`. -/
def LeanType.frenArgs [Inhabited α] (l : LeanType) (args : Array α) : Array α :=
  if args.size != l.argOrder.size then args
  else (Array.range args.size).map fun k => args[(l.argOrder.idxOf? k).getD k]!

/-- The variant whose Lean constructor is `c`, by its position. -/
def LeanType.variantOf? (l : LeanType) (c : Name) : Option Nat := l.ctors.idxOf? c

/-- The names of the Lean types that the prelude's types are, which are the
solver's names of their datatypes: a user's type with one of them as its
path has a symbol apart from it (`FrenCli.dataSortSym`). -/
def leanSortNames : Array String := leanTypes.map (·.lean.getString!)

/-- The SMT-LIB symbol of a user's enumeration or record, whose path prints
as `shown`: its path between `|`s, or after `::` if its path is the name of
one of the Lean types that the prelude's are, so that the two are apart
(`lang::prelude_sort`). -/
def userSortSym (shown : String) : String :=
  if leanSortNames.contains shown then "|::" ++ shown ++ "|" else "|" ++ shown ++ "|"

/-- The symbols that lean-smt gives the solver for the prelude's types,
without `|`s: the datatypes, their constructors and their selectors. -/
def leanSymbols : Array String :=
  leanTypes.flatMap fun l => #[l.lean.toString] ++ l.ctors.map (·.toString) ++ l.selectors.flatten

/-- `frenArgs` undoes `leanArgs`, for each of the prelude's types and any
arguments: an instance's type arguments, from its Lean type's, are its own. -/
theorem LeanType.frenArgs_leanArgs (l : LeanType) (hl : l ∈ leanTypes) {α} [Inhabited α] (args : Array α) :
    l.frenArgs (l.leanArgs args) = args := by
  have h : l = leanTypes[0]! ∨ l = leanTypes[1]! := by
    simp [leanTypes] at hl ⊢; exact hl
  have r1 : Array.range 1 = #[0] := rfl
  have r2 : Array.range 2 = #[0, 1] := rfl
  have i0 : List.idxOf? 0 [1, 0] = some 1 := rfl
  have i1 : List.idxOf? 1 [1, 0] = some 0 := rfl
  rcases args with ⟨xs⟩
  rcases h with rfl | rfl <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, xs⟩⟩⟩ <;>
    simp [r1, r2, i0, i1, leanTypes, LeanType.leanArgs, LeanType.frenArgs]

end Fren.Core
