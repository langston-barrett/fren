-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Lexical structure -/

-- For every identifier: the lexer's reserved words are the spec's.
impl reserved_word: lang::reserved_word for (s : String) {
  lexeme := s,
  reserved? := FrenCli.reserved.contains s,
} by
  intro s _
  simp [fren_spec, FrenCli.reserved, Fren.Core.reservedWords]

-- For every lexeme: the lexer's punctuators are the spec's.
impl punctuator: lang::punctuator for (s : String) {
  lexeme := s,
  accepted? := FrenCli.punctuators.contains s,
} by
  intro s _
  simp [fren_spec, FrenCli.punctuators]

namespace Lexical

open Fren.Core (inRanges isIdStart isIdRest Re)

/-- A one-character range is that character. -/
theorem le_le_self (d c : Char) : (decide (d ≤ c) && decide (c ≤ d)) = (c == d) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩

/-- `[A-Za-z_]` is `isIdStart`. -/
theorem start_class (c : Char) : inRanges [('A', 'Z'), ('a', 'z'), ('_', '_')] c = isIdStart c := by
  simp [inRanges, isIdStart, le_le_self, Bool.or_assoc]

/-- `[A-Za-z0-9_'?!]` is what continues an identifier. -/
theorem continue_class (c : Char) :
    inRanges [('A', 'Z'), ('a', 'z'), ('0', '9'), ('_', '_'), ('\'', '\''), ('?', '?'), ('!', '!')] c =
      (isIdRest c || c == '?' || c == '!') := by
  simp [inRanges, isIdRest, le_le_self, Bool.or_assoc]

theorem dot_class (c : Char) : inRanges [('.', '.')] c = (c == '.') := by
  simp [inRanges, le_le_self]

/-- `ends_with?("?")` is about the last character. -/
theorem endsWith_question (cs : List Char) :
    Fren.Str.endsWith (String.ofList cs) (Fren.Str.lit "?") = (cs.getLast? == some '?') := by
  rcases List.eq_nil_or_concat cs with h | ⟨l, x, rfl⟩
  · subst h; rfl
  · simp [Fren.Str.endsWith, Fren.Str.lit, List.isSuffixOf, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

/-- A character, then `r`: the first character is that one. -/
theorem mat_cat_char (a : Char) (r : Re) (cs : List Char) :
    (Re.cat (.str [a]) r).mat cs = match cs with
      | [] => false
      | c :: t => c == a && r.mat t := by
  rw [Re.mat_cat]
  cases cs with
  | nil => simp [Re.mat]
  | cons c t =>
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Re.mat, beq_iff_eq]
    constructor
    · rintro ⟨i, _, h1, h2⟩
      match i, h1, h2 with
      | 1, h1, h2 => simp at h1 h2; exact ⟨h1, h2⟩
      | 0, h1, _ => simp at h1
      | k + 2, h1, h2 =>
        cases t with
        | nil => simp at h1 h2; exact ⟨h1, h2⟩
        | cons _ _ => simp at h1
    · rintro ⟨h1, h2⟩
      exact ⟨1, by simp, by simp [h1], by simpa using h2⟩

/-- A repeated class, then a class: the last character is in the second, and
the others in the first. -/
theorem mat_star_cls_cls (n m : Bool) (rs qs : List (Char × Char)) (cs : List Char) :
    (Re.cat (.star (.cls n rs)) (.cls m qs)).mat cs = match cs.getLast? with
      | some c => (inRanges qs c != m) && cs.dropLast.all fun d => inRanges rs d != n
      | none => false := by
  rw [Re.mat_cat]
  rcases List.eq_nil_or_concat cs with rfl | ⟨l, x, rfl⟩
  · simp [Re.mat_cls]
  · simp only [List.concat_eq_append, List.getLast?_concat, List.dropLast_concat]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Re.mat_star_cls]
    constructor
    · rintro ⟨i, hi, h1, h2⟩
      rw [Re.mat_cls] at h2
      have hlen : (List.drop i (l ++ [x])).length = 1 := by split at h2 <;> simp_all
      have hi' : i = l.length := by simp at hlen hi; omega
      subst hi'
      simp at h1 h2
      exact ⟨by simpa using h2, by simpa using h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨l.length, by simp; omega, by simpa using h2, by simp [Re.mat_cls, h1]⟩

theorem mat_union (a b : Re) (cs : List Char) : (Re.union a b).mat cs = (a.mat cs || b.mat cs) := by
  rw [Re.mat]

theorem mat_empty (cs : List Char) : (Re.str []).mat cs = (cs == []) := by
  rw [Re.mat]

theorem decimal_class (c : Char) : inRanges [('0', '9')] c = Fren.Core.isDecimalDigit c := by
  simp [inRanges, Fren.Core.isDecimalDigit]

theorem decimal_sep_class (c : Char) :
    inRanges [('0', '9'), ('_', '_')] c = (Fren.Core.isDecimalDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isDecimalDigit, le_le_self]

theorem hex_class (c : Char) :
    inRanges [('0', '9'), ('a', 'f'), ('A', 'F')] c = Fren.Core.isHexDigit c := by
  simp [inRanges, Fren.Core.isHexDigit, Fren.Core.isDecimalDigit, Bool.or_assoc]

theorem hex_sep_class (c : Char) :
    inRanges [('0', '9'), ('a', 'f'), ('A', 'F'), ('_', '_')] c = (Fren.Core.isHexDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isHexDigit, Fren.Core.isDecimalDigit, le_le_self, Bool.or_assoc]

theorem binary_class (c : Char) : inRanges [('0', '1')] c = Fren.Core.isBinaryDigit c := by
  simp [inRanges, Fren.Core.isBinaryDigit]

theorem binary_sep_class (c : Char) :
    inRanges [('0', '1'), ('_', '_')] c = (Fren.Core.isBinaryDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isBinaryDigit, le_le_self]

theorem octal_class (c : Char) : inRanges [('0', '7')] c = Fren.Core.isOctalDigit c := by
  simp [inRanges, Fren.Core.isOctalDigit]

theorem octal_sep_class (c : Char) :
    inRanges [('0', '7'), ('_', '_')] c = (Fren.Core.isOctalDigit c || c == '_') := by
  simp [inRanges, Fren.Core.isOctalDigit, le_le_self]

theorem pair_class (a b c : Char) : inRanges [(a, a), (b, b)] c = (c == a || c == b) := by
  simp [inRanges, le_le_self]

/-- `ends_with?("!")` is about the last character. -/
theorem endsWith_bang (cs : List Char) :
    Fren.Str.endsWith (String.ofList cs) (Fren.Str.lit "!") = (cs.getLast? == some '!') := by
  rcases List.eq_nil_or_concat cs with h | ⟨l, x, rfl⟩
  · subst h; rfl
  · simp [Fren.Str.endsWith, Fren.Str.lit, List.isSuffixOf, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

/-- `starts_with?("!")` is about the first character. -/
theorem startsWith_bang (cs : List Char) :
    Fren.Str.startsWith (String.ofList cs) (Fren.Str.lit "!") = (cs.head? == some '!') := by
  rcases cs with _ | ⟨c, t⟩
  · rfl
  · simp [Fren.Str.startsWith, Fren.Str.lit, List.isPrefixOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

end Lexical

-- For every lexeme and the input after it: whether the lexer continues it.
-- The lexer calls `identExtends src last j` on the whole input, which reads
-- only `src[j]` and `src[j + 1]`, so it is this applied to the input after
-- `j`.
impl identifier_end: lang::identifier_end for (cs rest : List Char) {
  lexeme := String.ofList cs,
  remaining := String.ofList rest,
  ends? := Fren.Core.identExtends rest.toArray (cs.getLast?.getD ' ') 0 == 0,
} by
  rintro cs rest -
  simp only [fren_spec, Lexical.endsWith_question, Lexical.endsWith_bang, Lexical.startsWith_bang,
    Fren.Core.Re.matches, String.toList_ofList, Fren.Core.Re.mat_cat_cls, Fren.Core.Re.mat_star_any]
  cases h : cs.getLast? with
  | some l =>
    by_cases hb : l = '!'
    · subst hb; simp [Fren.Core.identExtends]
    by_cases hl : l = '?'
    · subst hl
      rcases rest with _ | ⟨c, t⟩
      · simp [Fren.Core.identExtends]
      · by_cases hc : c = '!'
        · subst hc; simp [Fren.Core.identExtends, Lexical.continue_class]
        · simp [Fren.Core.identExtends, hc]
    · rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
        simp [Fren.Core.identExtends, hl, hb, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
        split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with (hc | hc) | hc <;> simp_all)
  | none =>
    rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
      simp [Fren.Core.identExtends, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
      split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with (hc | hc) | hc <;> simp_all)

namespace Lexical

open Fren.Core (Re)

/-- The patterns of `lang::integer_literal`, as `Reqs/Lang/Lexical.md` writes
them. -/
def decimalRe : Re :=
  .cat (.cls false [('0', '9')]) (.union (.str []) (.cat (.star (.cls false [('0', '9'), ('_', '_')])) (.cls false [('0', '9')])))

def basedRe (b B : Char) (digits : List (Char × Char)) : Re :=
  .cat (.str ['0']) (.cat (.cls false [(b, b), (B, B)]) (.cat (.star (.cls false (digits ++ [('_', '_')]))) (.cls false digits)))

theorem beq_flip (a b : Char) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact eq_comm

theorem integerLiteral_regex (s : String) :
    Fren.Core.integerLiteral s =
      ((decimalRe.mat s.toList && !['0', '_'].isPrefixOf s.toList)
        || (basedRe 'x' 'X' [('0', '9'), ('a', 'f'), ('A', 'F')]).mat s.toList
        || (basedRe 'b' 'B' [('0', '1')]).mat s.toList
        || (basedRe 'o' 'O' [('0', '7')]).mat s.toList) := by
  simp only [Fren.Core.integerLiteral, decimalRe, basedRe, List.cons_append, List.nil_append]
  generalize s.toList = cs
  rcases cs with _ | ⟨c, _ | ⟨b, ds⟩⟩
  · simp [Fren.Core.Re.mat_cat_cls, mat_cat_char, List.isPrefixOf]
  · simp [Fren.Core.Re.mat_cat_cls, mat_cat_char, mat_union, mat_empty, mat_star_cls_cls, decimal_class,
      List.isPrefixOf]
  · simp only [mat_cat_char, Fren.Core.Re.mat_cat_cls, mat_star_cls_cls, mat_union, mat_empty,
      Fren.Core.digitsEndingInDigit, decimal_class, decimal_sep_class, hex_class, hex_sep_class, binary_class,
      binary_sep_class, octal_class, octal_sep_class, pair_class, List.isPrefixOf, Bool.bne_false, Bool.and_true,
      List.isEmpty_cons, Bool.false_or, List.head?_cons]
    rw [beq_flip '0' c, beq_flip '_' b]
    cases hd : ds.getLast? <;> rcases hl : (b :: ds).getLast? with _ | l <;>
      rw [Bool.eq_iff_iff] <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.false_eq_true, and_false, or_false] <;>
      by_cases hc : c = '0' <;> by_cases hb : b = '_' <;> simp_all [or_assoc]

end Lexical

-- For every lexeme: the lexer's test for an integer literal is the spec's.
impl integer_literal: lang::integer_literal for (s : String) {
  lexeme := s,
  accepted? := Fren.Core.integerLiteral s,
} by
  intro s _
  have h0 : "0_".toList = ['0', '_'] := by decide
  simp only [fren_spec, Fren.Core.Re.matches, Fren.Str.startsWith, Fren.Str.lit, Lexical.integerLiteral_regex, h0,
    Lexical.decimalRe, Lexical.basedRe, List.cons_append, List.nil_append, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Bool.not_eq_true, or_assoc]

end Fren.Impls
