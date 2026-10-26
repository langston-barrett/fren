-- keep-sorted start
import Lean.Elab.Term
import Std.Data.HashMap
import Std.Data.HashSet
-- keep-sorted end

/-!
# Comparing states field by field

`Same α` says when two values of `α` are the same, for types without a
`BEq`, such as maps, whose `BEq` would compare their trees. `same_fields%`
compares every field of a structure, but for those it names, so that a
field added later is compared unless someone decides otherwise
(`FrenCli.sameForLater`).
-/

namespace FrenCli

open Lean

class Same (α : Type u) where
  same : α → α → Bool

instance (priority := low) [BEq α] : Same α := ⟨(· == ·)⟩

instance [Same α] : Same (Array α) := ⟨fun a b => a.isEqv b Same.same⟩
instance [Same α] : Same (List α) := ⟨fun a b => a.length == b.length && (a.zip b).all fun (x, y) => Same.same x y⟩
instance [Same α] : Same (Option α) := ⟨fun
  | some x, some y => Same.same x y
  | none, none => true
  | _, _ => false⟩
instance [Same α] [Same β] : Same (α × β) := ⟨fun (a, b) (a', b') => Same.same a a' && Same.same b b'⟩
instance [Same α] : Same (NameMap α) := ⟨fun a b => Same.same a.toList b.toList⟩
instance [BEq κ] [Hashable κ] [Same α] : Same (Std.HashMap κ α) :=
  ⟨fun a b => a.size == b.size && a.fold (init := true) fun ok k v => ok && (b[k]?.map (Same.same v)).getD false⟩
instance [BEq α] [Hashable α] : Same (Std.HashSet α) := ⟨fun a b => a.size == b.size && a.all b.contains⟩

open Elab Term in
/-- `same_fields% S a b except [f, ...]`: whether the structures `a` and
`b` of type `S` are the `Same` on every field but `f, ...`, each of which
must be a field of `S`. -/
elab "same_fields% " s:ident a:term:max b:term:max " except " "[" ex:ident,* "]" : term => do
  let S ← realizeGlobalConstNoOverloadWithInfo s
  let env ← getEnv
  unless isStructure env S do throwErrorAt s "`{S}` is not a structure"
  let fields := getStructureFieldsFlattened env S (includeSubobjectFields := false)
  let excluded := ex.getElems.map (·.getId)
  for e in ex.getElems do
    unless fields.contains e.getId do throwErrorAt e "`{e.getId}` is not a field of `{S}`"
  let conj ← fields.filter (!excluded.contains ·) |>.foldlM (init := ← `(true)) fun acc f => do
    let proj := mkIdent (S ++ f)
    `($acc && Same.same ($proj $a) ($proj $b))
  elabTerm conj (some (mkConst ``Bool))

end FrenCli
