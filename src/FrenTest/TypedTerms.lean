-- keep-sorted start
import Fren.Model
-- keep-sorted end

/-!
`typeOf` keeps the type of each term that it elaborates, by `TypedTerm`:
the same term written at another position is the same key, with the same
hash, and a term with another name in it, other local variables, or
another scope is another.
-/

open Lean Fren

/-- `x + 1`, with every node and token at `pos`. -/
def plusOne (pos : Nat) (x : Name := `x) : Syntax :=
  let info := SourceInfo.synthetic ⟨pos⟩ ⟨pos + 1⟩
  Syntax.node info `«term_+_» #[Syntax.ident info x.toString.toRawSubstring x [], Syntax.atom info "+",
    Syntax.node info `num #[Syntax.atom info "1"]]

/-- The key of `plusOne pos x`, with the local variables `fvars` and the
open namespaces `opens`. -/
def keyOf (pos : Nat) (x : Name := `x) (fvars : Array FVarId := #[⟨`a⟩]) (opens : List OpenDecl := []) : TypedTerm :=
  { fvars, currNamespace := `Fren, openDecls := opens, term := plusOne pos x }

#guard keyOf 3 == keyOf 40
#guard hash (keyOf 3) == hash (keyOf 40)
#guard !(keyOf 3 == keyOf 3 `y)
#guard !(keyOf 3 == keyOf 3 (fvars := #[⟨`a⟩, ⟨`b⟩]))
#guard !(keyOf 3 == keyOf 3 (opens := [.simple `Fren.Lang []]))
#guard !(keyOf 3 == { keyOf 3 with currNamespace := `Fren.Generated })
