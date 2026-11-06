-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

instance : Fren.Finite Fren.Core.Construct :=
  ⟨[.stringCompare, .stringAtom, .stringIndex, .stringSearch, .setAlgebra, .setFunction, .relational, .relationalCard, .seqArray, .seqWord,
    .quantifier], by intro x; cases x <;> simp⟩

def toConstruct : Fren.Core.Construct → lang.Construct
  | .stringCompare => .StringCompare
  | .stringAtom => .StringAtom
  | .stringIndex => .StringIndex
  | .stringSearch => .StringSearch
  | .setAlgebra => .SetAlgebra
  | .setFunction => .SetFunction
  | .relational => .Relational
  | .relationalCard => .RelationalCard
  | .seqArray => .SeqArray
  | .seqWord => .SeqWord
  | .quantifier => .Quantifier

impl in_core: lang::in_core for (c : Fren.Core.Construct) (a m i g f r l : Bool) {
  construct := toConstruct c,
  constant_args? := a,
  comparable? := m,
  infinite_output? := i,
  ground? := g,
  infinite_elems? := f,
  finite_range? := r,
  literal_operand? := l,
  decidable? := Fren.Core.inCore c a m i g f r l,
} by
  intro c a m i g f r l _
  cases c <;> simp [fren_spec, toConstruct, Fren.Core.inCore]

end Fren.Impls
