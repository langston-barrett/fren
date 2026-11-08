import Fren.Impl
import Fren.Literate
import FrenBase.Binding

open Fren.Lang

#fren_md "Types.md"

#fren_check

namespace Spec.Language.Types

/-- A local has its actual context entry, not merely some type at an
in-bounds index. This law uses the existing production binding primitive. -/
theorem local_type_unique {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (a b : Ty) (ha : FrenBase.Binding.HasType ctx i a)
    (hb : FrenBase.Binding.HasType ctx i b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

theorem local_type_scoped {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (ty : Ty) (h : FrenBase.Binding.HasType ctx i ty) :
    FrenBase.Binding.InScope ctx.length i :=
  FrenBase.Binding.hasType_scoped h

-- Equal lengths and valid indices alone cannot choose a local's type.
#guard FrenBase.Binding.HasType [true, false] 0 true
#guard ¬ FrenBase.Binding.HasType [true, false] 0 false
#guard FrenBase.Binding.HasType [false, true] 0 false
#guard ¬ FrenBase.Binding.HasType ([] : List Bool) 0 true

end Spec.Language.Types
