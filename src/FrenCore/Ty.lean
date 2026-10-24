-- keep-sorted start
import FrenCore.Names
-- keep-sorted end

/-!
# Types

The types of Fren's values, as the `fren` command elaborates them, and the
rule for applications over them (`lang::application`). The Lean-hosted
front end has Lean's types instead, which its elaborator compares.
-/

namespace Fren.Core

open Lean (Name)

/-- A type of values (`lang::Ty`). -/
inductive Ty where
  | bool
  | int
  | string
  /-- `Set(T)`. -/
  | set (elem : Ty)
  /-- `Rel(A, B)`. -/
  | rel (a b : Ty)
  /-- `Seq(T)`. -/
  | seq (elem : Ty)
  | enum (path : Name)
  | record (path : Name)
  /-- An abstract type. -/
  | abstract (path : Name)
  deriving Inhabited, DecidableEq

/-- The abstract type that `t` is, or that is an element type within it. -/
def Ty.abstractWithin? : Ty → Option Name
  | .abstract p => some p
  | .set t => t.abstractWithin?
  | .rel a b => a.abstractWithin? <|> b.abstractWithin?
  | .seq t => t.abstractWithin?
  | _ => none

def Ty.show : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .string => "String"
  | .set t => s!"Set({t.show})"
  | .rel a b => s!"Rel({a.show}, {b.show})"
  | .seq t => s!"Seq({t.show})"
  | .enum p | .record p | .abstract p => showPath p

/-- Whether an application is accepted, from its parameters' types and its
arguments' (`lang::application`). -/
def applicationAccepted (params args : Array Ty) : Bool := args == params

end Fren.Core
