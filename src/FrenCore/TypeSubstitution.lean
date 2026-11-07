-- keep-sorted start
import FrenCore.Ty
-- keep-sorted end

/-! Simultaneous substitution of generic type parameters. This primitive
sits below theories and the rules for generic functions and datatypes, so
both can use the same type morphisms without an import cycle. -/

namespace Fren.Core

mutual
/-- `t`, with `args[k]` for each type parameter `k`
(`lang::instantiation`). A parameter with no argument stays as it is, and
a newtype, which has no type parameters, is left alone. -/
def Ty.subst (args : Array Ty) : Ty → Ty
  | .param k n => args[k]?.getD (.param k n)
  | .set t => .set (t.subst args)
  | .rel a b => .rel (a.subst args) (b.subst args)
  | .seq t => .seq (t.subst args)
  | .enum p as => .enum p (Ty.substAll args as)
  | .record p as => .record p (Ty.substAll args as)
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .abstract p => .abstract p
  | .newtype p u => .newtype p u

/-- Each of `ts`, with `args` for the type parameters (`Ty.subst`). -/
def Ty.substAll (args : Array Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => t.subst args :: Ty.substAll args ts
end

end Fren.Core
