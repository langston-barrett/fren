-- keep-sorted start
import Fren.Impl
import FrenCore.Literate
import Reqs.Markdown
-- keep-sorted end
open Fren.Lang

/-! # Markdown specs (`Reqs/Markdown#code-blocks`) -/

namespace Fren.Impls

-- For every line, as split by `Fren.Core.fenceParts`, the fence reader
-- that both front ends, `fren fmt` and the tests read blocks with.
impl fence: markdown::fence for (indent run : Nat) (info : String) {
  indent := indent,
  run := run,
  info := info,
  fence? := Fren.Core.isFence indent run info,
} by
  intro indent run info _
  simp only [fren_spec, Fren.Core.isFence, Fren.Str.lit]
  by_cases hc : Fren.Str.contains info "`" = true <;> simp [hc] <;> omega

impl closes: markdown::closes for (o indent run : Nat) (info : String) {
  opening := o,
  indent := indent,
  run := run,
  info := info,
  closes? := Fren.Core.closesBlock o indent run info,
} by
  intro o indent run info _
  simp only [fren_spec, Fren.Core.closesBlock, Fren.Core.isFence, Fren.Str.lit]
  refine ⟨indent, run, info, ?_⟩
  by_cases hc : Fren.Str.contains info "`" = true <;> simp [hc] <;> omega

/-- The specification's kind of block for the reader's. -/
def ofBlockKind : Fren.Core.BlockKind → markdown.BlockKind
  | .spec => .Spec
  | .exampleBlock => .Example
  | .looksLikeFren => .LooksLikeFren
  | .prose => .Prose

impl block_kind: markdown::block_kind for (info : String) {
  info := info,
  kind := ofBlockKind (Fren.Core.blockKind info),
} by
  intro info _
  simp only [fren_spec, Fren.Core.blockKind, Fren.Core.frenInfo, Fren.Core.frenExampleInfo]
  split
  · rfl
  split
  · rfl
  simp only [Bool.or_eq_true]
  split <;> simp_all [ofBlockKind]

end Fren.Impls
