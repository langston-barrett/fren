import Fren.Impl
import Fren.Literate

open Fren.Lang

#fren_md "Example.md"

#fren_check

namespace Spec.Compiler.Example

def double (n : Int) : Int := n + n

impl double_meets: double for (n : Int) {
  n := n, result := double n
} by
  intro n _
  simp [fren_spec, double]

end Spec.Compiler.Example
