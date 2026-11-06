-- keep-sorted start
import FrenCore.Text
import Init.Data.String.Lemmas.Pattern.Find.String
import Init.Data.String.Lemmas.Pattern.Memcmp
-- keep-sorted end

/-! Correctness of the byte search, including its empty-needle case.
The native comparison is also checked by FrenTest.TextSearch. -/

namespace Fren.Core

/-- The first-byte filter discards no full byte match. -/
private theorem byteMatch_iff (s t : String) (i : Nat)
    (h : 0 < t.utf8ByteSize ∧ i + t.utf8ByteSize ≤ s.utf8ByteSize) :
    (s.getUTF8Byte ⟨i⟩ (by simp [String.Pos.Raw.lt_iff]; omega) ==
      t.getUTF8Byte 0 (by simp [String.Pos.Raw.lt_iff]; omega) &&
      String.Slice.Pattern.Internal.memcmpStr s t ⟨i⟩ 0 ⟨t.utf8ByteSize⟩
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy]; omega)
        (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.offsetBy])) = true ↔
      s.toByteArray.extract i (i + t.utf8ByteSize) = t.toByteArray := by
  rw [Bool.and_eq_true, String.Slice.Pattern.Internal.memcmpStr_eq_true_iff]
  simp only [String.Pos.Raw.offsetBy, String.Pos.Raw.byteIdx_zero,
    Nat.zero_add, ← String.size_toByteArray, ByteArray.extract_zero_size]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    have he' : s.toByteArray.extract i (i + t.toByteArray.size) =
        t.toByteArray.extract 0 (0 + t.toByteArray.size) := by
      simpa only [Nat.zero_add, ByteArray.extract_zero_size] using he
    have hb := (ByteArray.extract_eq_extract_iff_getElem (as := s.toByteArray) (bs := t.toByteArray)
      (i := i) (j := 0) (len := t.toByteArray.size)
      (by simpa using h.2) (by simp)).1 he' 0 (by simpa using h.1)
    rw [beq_iff_eq]
    exact hb

/-- The byte search examines exactly the offsets at or after `i` that
leave room for a nonempty needle. -/
theorem occursFrom_iff (s t : String) (m n i : Nat) (hm : m = t.utf8ByteSize) (hn : n = s.utf8ByteSize) :
    occursFrom s t m n i hm hn = true ↔
      ∃ j, i ≤ j ∧ j + m ≤ n ∧ 0 < m ∧ s.toByteArray.extract j (j + m) = t.toByteArray := by
  rw [occursFrom]
  split
  · rename_i h
    rw [Bool.or_eq_true, occursFrom_iff s t m n (i + 1) hm hn]
    have hb := byteMatch_iff s t i (by simpa [hm, hn] using h)
    subst m n
    rw [hb]
    constructor
    · rintro (he | ⟨j, hj, hlen, hpos, he⟩)
      · exact ⟨i, Nat.le_refl i, h.2, h.1, he⟩
      · exact ⟨j, by omega, hlen, hpos, he⟩
    · rintro ⟨j, hj, hlen, hpos, he⟩
      by_cases hij : i = j
      · exact Or.inl (hij.symm ▸ he)
      · exact Or.inr ⟨j, by omega, hlen, hpos, he⟩
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j hj hlen hpos _
    exact h ⟨hpos, by omega⟩
termination_by n - i

/-- A nonempty UTF-8 byte match is a character infix: the matched bytes
are valid UTF-8, so both ends lie on character boundaries. -/
private theorem byteInfix_iff (s t : String) (ht : t ≠ "") :
    (∃ i, i + t.utf8ByteSize ≤ s.utf8ByteSize ∧
      s.toByteArray.extract i (i + t.utf8ByteSize) = t.toByteArray) ↔ t.toList <:+: s.toList := by
  have hpos : 0 < t.utf8ByteSize := by simpa [Nat.pos_iff_ne_zero] using ht
  constructor
  · rintro ⟨i, hlen, he⟩
    have hv := (String.Pos.Raw.isValidUTF8_extract_iff (s := s) ⟨i⟩ ⟨i + t.utf8ByteSize⟩
      (by simp [String.Pos.Raw.le_iff]) (by simpa [String.Pos.Raw.le_iff] using hlen)).1
      (he ▸ t.isValidUTF8)
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + t.utf8ByteSize⟩ := by
      simp only [ne_eq, String.Pos.Raw.ext_iff]; omega
    obtain ⟨hstart, hend⟩ := hv.resolve_left hne
    let p := s.pos ⟨i⟩ hstart
    let q := s.pos ⟨i + t.utf8ByteSize⟩ hend
    have hpq : p ≤ q := by simp [p, q, String.Pos.le_iff, String.Pos.Raw.le_iff]
    have hs : (s.slice p q hpq).copy = t := String.toByteArray_inj.mp (by
      simpa [String.toByteArray_copy_slice, p, q] using he)
    obtain ⟨a, b, ha, _⟩ := String.copy_slice_eq_iff_splits.mp ⟨hpq, hs⟩
    rw [ha.eq_append]
    exact ⟨a.toList, b.toList, by simp [String.toList_append, List.append_assoc]⟩
  · rintro ⟨a, b, hab⟩
    have hs : s = String.ofList a ++ t ++ String.ofList b :=
      String.toList_inj.mp (by simpa [String.toList_append] using hab.symm)
    rw [hs]
    refine ⟨(String.ofList a).utf8ByteSize, by simp [String.utf8ByteSize_append], ?_⟩
    rw [String.toByteArray_append, String.toByteArray_append, ByteArray.append_assoc]
    have he := ByteArray.extract_append_size_add (a := (String.ofList a).toByteArray)
      (b := t.toByteArray ++ (String.ofList b).toByteArray) (i := 0) (j := t.toByteArray.size)
    have ht := ByteArray.extract_append_eq_left (a := t.toByteArray)
      (b := (String.ofList b).toByteArray) rfl
    simpa only [Nat.add_zero, String.size_toByteArray] using he.trans ht

/-- An empty needle is never found, as with `String.splitOn`. -/
theorem occursIn_empty (s : String) : occursIn "" s = false := by
  simp [occursIn, occursFrom]

/-- For every nonempty needle, the optimized byte search finds exactly
its character infixes, including overlapping and multibyte matches. -/
theorem occursIn_iff (t s : String) (ht : t ≠ "") :
    occursIn t s = true ↔ t.toList <:+: s.toList := by
  rw [occursIn, occursFrom_iff]
  have hpos : 0 < t.utf8ByteSize := by simpa [Nat.pos_iff_ne_zero] using ht
  simpa [hpos] using byteInfix_iff s t ht

/-- `String.contains` is the character-level reference for the byte
search; the empty needle is deliberately excluded by `occursIn`. -/
theorem occursIn_eq_contains (t s : String) (ht : t ≠ "") :
    occursIn t s = s.contains t := by
  rw [Bool.eq_iff_iff, occursIn_iff t s ht, String.contains_string_iff]

end Fren.Core
