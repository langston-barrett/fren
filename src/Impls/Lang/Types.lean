-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- The type written for a variable: `none` if none is, else whether it is
`Bool`. -/
def isBool? : lang.Annot → Option Bool
  | .Missing => none
  | .BoolTy => some true
  | .IntTy | .NatTy | .StringTy | .NamedTy => some false

interp lang::Ty := Fren.Core.Ty

/-- The kind of a type (`lang::kind`). -/
def kindOf : Fren.Core.Ty → lang.ValueType
  | .bool => .BoolTy
  | .int => .IntTy
  | .nat => .NatTy
  | .string => .StringTy
  | .set _ => .SetTy
  | .rel .. => .RelTy
  | .seq _ => .SeqTy
  | .enum .. => .EnumTy
  | .record .. => .RecordTy
  | .abstract _ => .AbstractTy
  -- Within its declaration, a type parameter's values are not described
  -- there, like an abstract type's (`Reqs/Lang/Generics#type-parameters`).
  | .param .. => .AbstractTy
  -- A newtype is a record (`Reqs/Lang/Items#newtypes`).
  | .newtype _ _ => .RecordTy

interp lang::kind := kindOf

/-- Whether a type is a newtype (`lang::newtype?`). -/
def isNewtype : Fren.Core.Ty → Bool
  | .newtype .. => true
  | _ => false

interp lang::newtype? := isNewtype

/-- The underlying type of a newtype, and any other type itself. -/
def underOf : Fren.Core.Ty → Fren.Core.Ty
  | .newtype _ u => u
  | t => t

interp lang::under := underOf

-- For every two types, with the check that both front ends make wherever a
-- type is declared (`Core.checkType`).
def toNewtypeOp : Fren.Core.NewtypeOp → lang.NewtypeOp
  | .equality => .Equality
  | .order => .Order
  | .add => .Addition
  | .sub => .Subtraction
  | .other => .Other

interp lang::TypeName := Lean.Name

/-- The path of an enumeration, record or newtype (`lang::type_name`). -/
def typeNameOf : Fren.Core.Ty → Lean.Name
  | .enum p _ | .record p _ | .newtype p _ => p
  | _ => .anonymous

interp lang::type_name := typeNameOf

/-- A position, or `-1` for none. -/
def posOr : Option Nat → Int
  | none => -1
  | some i => i

interp lang::FieldName := Lean.Name

interp lang::VariantName := Lean.Name



interp lang::first_giver := fun (d : Fren.Seq Fren.Core.Ty) (s : Fren.Seq Bool) (k : Nat) =>
  Fren.Core.firstGiver d.toList.toArray s.toList.toArray k
interp lang::widened := Fren.Core.Ty.widen

end Fren.Impls
