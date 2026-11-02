-- keep-sorted start
import FrenCli.Confirm
-- keep-sorted end

/-! A test of `Spec.compiledRecs?`: the structural recursions that a
reading of a spec keeps compiled (`Spec.keepCompiledRecs`, which `specOf`
calls) are those that compiling them again for the spec's own shapes
gives (`Spec.withCompiledRecs`), which `Spec.quickComp` would otherwise
do at each procedure. Read from two files, each with recursions over a
type of the first, so that a recursion read after another file is
kept too. -/

namespace Fren.Test.CompiledRecs

open FrenCli FrenCli.Eval

def treeSrc : String := "mod trees
pub enum Tree { Leaf, Node(Tree, Int, Tree) }

pub fn size(t: Tree): Int := match t {
    Tree::Leaf => 0,
    Tree::Node(l, _, r) => size(l) + 1 + size(r),
}
"

def useSrc : String := "mod uses
use trees::Tree

pub fn zeros(t: Tree): Int := match t {
    Tree::Leaf => 0,
    Tree::Node(l, k, r) => (if k = 0 then 1 else 0) + zeros(l) + zeros(r),
}

pub fn leaves?(t: Tree, n: Int) := match t {
    Tree::Leaf => n = 1,
    Tree::Node(l, _, r) => leaves?(l, n - 1) or leaves?(r, n - 1),
}
"

/-- The spec of the two files, read by `specOf`. -/
def sp : Spec :=
  (specOf #[("trees.fren", treeSrc.toList.toArray), ("uses.fren", useSrc.toList.toArray)] {}).toOption.getD default

/-- Whether two maps of recursions have the same names, parameters and
bodies (`Ex.same`). -/
def sameRecs (a b : Lean.NameMap (Array Lean.Name × Ex)) : Bool :=
  a.size == b.size && a.toList.all fun (f, ps, body) => match b.find? f with
    | some (ps', body') => ps == ps' && body.same body'
    | none => false

-- The reading keeps its three recursions compiled, as compiling them
-- again for its own shapes gives them.
#guard sp.recDefs.size == 3
#guard sp.compiledRecs?.isSome
#guard
  let shapes := sp.shapeMap
  sameRecs (sp.withOwnCompiledRecs shapes).recDefs (sp.withCompiledRecs fun p => shapes[p]?).recDefs
-- And they differ from the bodies as read, so that the check above is not
-- of two copies of `recDefs`.
#guard !sameRecs (sp.withOwnCompiledRecs sp.shapeMap).recDefs sp.recDefs

end Fren.Test.CompiledRecs
