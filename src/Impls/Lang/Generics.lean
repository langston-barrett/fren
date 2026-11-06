-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Angle brackets (`Reqs/Lang/Generics#angle-brackets`) -/

/-- A bracket, as the spec writes it. -/
def toBracket : lang.Bracket → Fren.Core.Bracket
  | .Angle => .angle
  | .Paren => .paren
  | .Other => .other

/-- What a bracket after a name does, as the spec writes it. -/
def ofAfterName : Fren.Core.AfterName → lang.AfterName
  | .opens => .Opens
  | .spaced => .Spaced
  | .ends => .Ends

-- For every bracket after a type's name: what the `fren` command's parser
-- does with it.
impl type_bracket: lang::type_bracket for (b : lang.Bracket) (a : Bool) {
  bracket := b,
  adjacent? := a,
  reading := ofAfterName (Fren.Core.afterName (toBracket b) a),
} by
  intro b a _
  cases b <;> cases a <;> simp [fren_spec, toBracket, ofAfterName, Fren.Core.afterName]

/-! ## Generic types (`Reqs/Lang/Generics`) -/

/-- Where a type parameter is written (`lang::ParamPlace`). -/
def toParamPlace : Fren.Core.ParamPlace → lang.ParamPlace
  | .whole => .Whole
  | .argument => .Argument
  | .ownParameter => .OwnParameter
  | .ownOther => .OwnOther
  | .element => .Element

-- For every place where a type parameter is written, with the check that
-- both front ends make (`Core.typeParamPlaceAccepted`).
impl type_parameter_place: lang::type_parameter_place for (p : Fren.Core.ParamPlace) {
  place := toParamPlace p,
  accepted? := Fren.Core.typeParamPlaceAccepted p,
} by
  intro p _
  cases p <;> simp [fren_spec, toParamPlace, Fren.Core.typeParamPlaceAccepted]

-- For every number of type parameters and of arguments, with the check that
-- both front ends make wherever a type is written (`Core.typeArgumentsAccepted`).
impl type_arguments: lang::type_arguments for (params args : Nat) {
  params := (params : Int),
  args := (args : Int),
  accepted? := Fren.Core.typeArgumentsAccepted params args,
} by
  intro params args _
  simp [fren_spec, Fren.Core.typeArgumentsAccepted, Int.natCast_inj]

-- For every record, whether it is ordered and how many type parameters it
-- has, with the check that both front ends make of its declaration
-- (`Core.orderedGenericAccepted`).
impl ordered_generic: lang::ordered_generic for (o : Bool) (params : Nat) {
  ordered? := o,
  params := params,
  accepted? := Fren.Core.orderedGenericAccepted o params,
} by
  intro o params _
  cases o <;> simp [fren_spec, Fren.Core.orderedGenericAccepted]

/-- The type that the declared type of a construction's value is here: the
type parameter it mentions, or `Int`, which mentions none. -/
def argTy : lang.Arg → Fren.Core.Ty
  | .P0 => .param 0 `T0
  | .P1 => .param 1 `T1
  | .P2 => .param 2 `T2
  | .Other => .int

def valueTy : lang.ArgMode → Fren.Core.Ty
  | .Gives a | .Waits a => argTy a

/-- A value that synthesizes its type, and one that does not. -/
def valueShape : lang.ArgMode → Fren.Core.TypeShape
  | .Gives _ => .other
  | .Waits _ => .emptyLiteral

def argOf : Nat → lang.Arg
  | 0 => .P0
  | 1 => .P1
  | 2 => .P2
  | _ => .Other

-- For every enumeration with at most three type parameters, every written
-- list of its own type's arguments, and within an instance's argument or
-- not: the check that both front ends make of a recursive payload
-- (`Core.recursivePlace`), once each has read the payload's type into
-- whether its arguments are the parameters, in order (`Core.ownArgs`).
impl recursive_payload: lang::recursive_payload for (n : Fin 4) (as : List lang.Arg) (nested : Bool) {
  params := Fren.Seq.ofList ((List.range n).map argOf),
  args := Fren.Seq.ofList as,
  nested? := nested,
  accepted? := Fren.Core.typeParamPlaceAccepted
    (Fren.Core.recursivePlace (decide (as = (List.range n).map argOf)) nested),
} by
  intro n as nested _
  obtain ⟨n, hn⟩ := n
  obtain _ | _ | _ | _ | n := n
  all_goals first | omega | skip
  all_goals cases nested <;>
    simp [fren_spec, Fren.Core.recursivePlace, Fren.Seq.ext_iff, List.range_succ, argOf] <;>
    first | rfl | (split <;> simp_all [Fren.Core.typeParamPlaceAccepted])

/-- What a type's path names (`lang::Named`). -/
def toTypeNamed : Fren.Core.TypeNamed → lang.Named
  | .builtin => .Builtin
  | .parameter => .Parameter
  | .data => .Data
  | .other => .OtherItem

-- For whatever a type's path names, with its type parameters if it is an
-- enumeration or record, and every list of written arguments: the check
-- that both front ends make wherever a type is written with type arguments
-- (`Core.writtenArgumentsAccepted`).
impl written_type_arguments: lang::written_type_arguments for (k : Fren.Core.TypeNamed) (ps as : List lang.Arg) {
  named := toTypeNamed k,
  params := Fren.Seq.ofList ps,
  args := Fren.Seq.ofList as,
  accepted? := Fren.Core.writtenArgumentsAccepted k ps.length as.length,
} by
  intro k ps as _
  cases k <;> simp [fren_spec, toTypeNamed, Fren.Core.writtenArgumentsAccepted, Fren.Core.typeArgumentsAccepted, Int.natCast_inj]

end Fren.Impls
