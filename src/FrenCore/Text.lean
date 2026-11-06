/-!
# Searching text

Both front ends read SMT-LIB text for what it contains, such as a
quantifier's head (`hasQuantifier`). `occursIn` searches for it in place.
`(s.splitOn t).length > 1`, which these searches were, splits `s` at every
occurrence of `t`, only to count the pieces, and `String.contains`
searches through slices, with the pattern machinery's overhead at each
position: each took several per cent of a `fren check` with a warm query
cache. `FrenCore.Text.Correctness` proves `occursIn`'s character-level
meaning. `FrenTest.TextSearch` checks the native comparison against
`splitOn`, and `projectsRelation` against `String.contains` for the
needle `"rel.project"`.
-/

namespace Fren.Core

/-- Whether `t`'s bytes are at byte `i` of `s` or later, `m` being `t`'s
size and `n` `s`'s; never if `t` is empty. Each position whose first byte
is `t`'s is compared in full. -/
def occursFrom (s t : String) (m n i : Nat) (hm : m = t.utf8ByteSize) (hn : n = s.utf8ByteSize) : Bool :=
  if h : 0 < m ∧ i + m ≤ n then
    (s.getUTF8Byte ⟨i⟩ (by simp [String.Pos.Raw.lt_iff]; omega) == t.getUTF8Byte 0 (by simp [String.Pos.Raw.lt_iff]; omega)
      -- Core Lean's native `memcmp` of the two strings' bytes: an internal
      -- API, this module's one, which a toolchain bump may rename or
      -- change. `FrenCore.Text.Correctness` proves the search from
      -- `memcmpStr`'s Lean specification. `FrenTest.TextSearch` checks the
      -- native code against `splitOn`, and `projectsRelation` against
      -- `String.contains` for the needle `"rel.project"`.
      && String.Slice.Pattern.Internal.memcmpStr s t ⟨i⟩ 0 ⟨m⟩
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy]; omega)
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy]; omega))
    || occursFrom s t m n (i + 1) hm hn
  else false
termination_by n - i

/-- Whether the text `t` occurs in `s`, as `(s.splitOn t).length > 1`
says, without splitting `s`: never if `t` is empty, which `splitOn` does
not split at. It compares bytes at each byte of `s`.
`FrenCore.Text.Correctness` proves the character-level equivalence
(`occursIn_iff`) and the empty-needle result (`occursIn_empty`);
`FrenTest.TextSearch` checks the native byte comparison. -/
def occursIn (t s : String) : Bool := occursFrom s t t.utf8ByteSize s.utf8ByteSize 0 rfl rfl

#guard occursIn "fren.forall" "(fren.forall ((i Int)) x)"
#guard !occursIn "fren.forall" "(fren.foral ((i Int)) x)"
#guard !occursIn "" "abc"
#guard occursIn "aab" "aaab"
#guard occursIn "é" "café" && !occursIn "e" "café"

end Fren.Core
