/-!
# Searching text

Both front ends read SMT-LIB text for what it contains, such as a
quantifier's head (`hasQuantifier`). `occursIn` searches for it in place.
`(s.splitOn t).length > 1`, which these searches were, splits `s` at every
occurrence of `t`, only to count the pieces, and `String.contains`
searches through slices, with the pattern machinery's overhead at each
position: each took several per cent of a `fren check` with a warm query
cache. `FrenTest.TextSearch` checks `occursIn` against `splitOn`.
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
      -- change. `FrenTest.TextSearch` checks `occursIn` against the old
      -- `splitOn` search, and would catch a change in its meaning.
      && String.Slice.Pattern.Internal.memcmpStr s t ⟨i⟩ 0 ⟨m⟩
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy]; omega)
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy]; omega))
    || occursFrom s t m n (i + 1) hm hn
  else false
termination_by n - i

/-- Whether the text `t` occurs in `s`, as `(s.splitOn t).length > 1`
says, without splitting `s`: never if `t` is empty, which `splitOn` does
not split at. It compares bytes, at each byte of `s`: in UTF-8, one text
occurs in another as characters just where it occurs as bytes, since no
character's bytes start inside another's. -/
def occursIn (t s : String) : Bool := occursFrom s t t.utf8ByteSize s.utf8ByteSize 0 rfl rfl

#guard occursIn "fren.forall" "(fren.forall ((i Int)) x)"
#guard !occursIn "fren.forall" "(fren.foral ((i Int)) x)"
#guard !occursIn "" "abc"
#guard occursIn "aab" "aaab"
#guard occursIn "é" "café" && !occursIn "e" "café"

end Fren.Core
