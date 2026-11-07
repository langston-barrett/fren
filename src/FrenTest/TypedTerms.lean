-- keep-sorted start
import Fren.Elab.TypeTerms
-- keep-sorted end

/-!
`typeOf` keeps the type of each term that it elaborates, if that type has
no metavariables, by `TypedTerm`: the same term written at another position
is the same key, with the same hash, and a term with another name in it,
other local variables, or another scope is another. A type with a
metavariable is not kept, so a caller that assigns it does not change what
the next one gets; `test/ui/lang/empty_method_arguments.fren` checks the
same through both front ends.
-/

open Lean Elab Term Meta Fren

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

/-- `[]`'s type, `Seq<?>`, unified with `Seq<Int>` by its first asker, as a
sequence method's check of its argument does: the second asker can still
unify the type it gets with `Seq<Bool>`, where a stale copy would be
`Seq<Int>`. -/
def emptyTypeFresh : TermElabM Bool := do
  let t ← `((∅ : Fren.Seq _))
  unless ← isDefEq (← typeOf t) (← elabType (← `(Fren.Seq Int))) do return false
  isDefEq (← typeOf t) (← elabType (← `(Fren.Seq Bool)))

/-- A type without metavariables is kept, and one with a metavariable is
not: after `[]`'s and `1`'s, the cache holds `1`'s alone. -/
def closedTypeKept : TermElabM Bool := do
  discard (typeOf (← `((∅ : Fren.Seq _))))
  discard (typeOf (← `((1 : Int))))
  return (← getLocal).types.size == 1

#guard_msgs in
#eval show TermElabM Unit from do
  unless ← emptyTypeFresh do throwError "a type with a metavariable was served stale"
  unless ← closedTypeKept do throwError "the cache does not hold exactly the type without a metavariable"
