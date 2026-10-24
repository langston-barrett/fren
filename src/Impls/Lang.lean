-- keep-sorted start
import FrenCli.Lex
import FrenCore.Ty
import Impls.Check
-- keep-sorted end
open Fren.Lang

/-! # Language rules (`Reqs/Lang`) -/

namespace Fren.Impls

/-- The type written for a variable: `none` if none is, else whether it is
`Bool`. -/
def isBool? : lang.Annot → Option Bool
  | .Missing => none
  | .BoolTy => some true
  | .IntTy | .StringTy | .NamedTy => some false

-- For every name: `checkVarName` reads the suffix from the name itself, with
-- the meaning of `ends_with?` that Fren fixes.
impl bool_naming: lang::bool_naming for (s : String) (a : lang.Annot) {
  name := s,
  annot := a,
  accepted? := (Fren.Core.checkVarName (.mkSimple s) (isBool? a)).isOk,
} by
  intro s a _
  have hs : Fren.Core.nameText (.mkSimple s) = s := rfl
  cases h : Fren.Str.endsWith s "?" <;> cases a <;>
    simp [fren_spec, Fren.Core.checkVarName, Fren.Core.checkVarKind, isBool?, hs, h, Except.isOk, Except.toBool] <;> rfl

-- Over `Nat`, so a proof by cases.
impl linear_product: lang::linear_product for (a b : Nat) {
  a_vars := a,
  b_vars := b,
  accepted? := Fren.Core.productAccepted a b,
} by
  intro a b _
  rcases a with _ | a <;> rcases b with _ | b <;> simp [fren_spec, Fren.Core.productAccepted] <;> omega

interp lang::Ty := Fren.Core.Ty

-- For every application, over the types that the `fren` command compares.
impl application: lang::application for (ps as : Array Fren.Core.Ty) (k : Int) {
  params := Fren.Seq.ofList ps.toList,
  args := Fren.Seq.ofList as.toList,
  k := k,
  accepted? := Fren.Core.applicationAccepted ps as,
} by
  intro ps as k _
  simp [fren_spec, Fren.Core.applicationAccepted, Fren.Seq.ext_iff]

impl constant: lang::constant for (t : lang.ValueType) (a : Bool) {
  ty := t,
  applies? := a,
  accepted? := Fren.Core.constantAccepted (t == .AbstractTy) a,
}

impl field_type: lang::field_type for (k : lang.ValueType) (a own s pay : Bool) {
  kind := k,
  abstract_within? := a,
  own? := own,
  own_in_set? := s,
  payload? := pay,
  accepted? := Fren.Core.fieldTypeAccepted a own s pay,
} by
  intro k a own s pay _
  cases a <;> cases own <;> cases s <;> cases pay <;> simp [fren_spec, Fren.Core.fieldTypeAccepted]

/-- The variants of `vs` for which `p` holds are all of them exactly when
there are as many. -/
theorem ofList_filter_eq (vs : List Lean.Name) (p : Lean.Name → Bool) :
    Fren.FinSet.ofList (vs.filter p) = Fren.FinSet.ofList vs ↔ (vs.filter p).length = vs.length := by
  rw [Fren.FinSet.ext_iff]
  simp only [Fren.FinSet.mem_ofList, List.mem_filter]
  have hle := List.length_filter_le p vs
  have hlt := @List.length_filter_lt_length_iff_exists _ p vs
  constructor
  · intro h
    have : ¬ (vs.filter p).length < vs.length := fun hl =>
      let ⟨x, hx, hp⟩ := hlt.mp hl; hp ((h x).mpr hx).2
    omega
  · intro h x
    refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
    cases hp : p x
    · have := hlt.mpr ⟨x, hx, by simp [hp]⟩
      omega
    · rfl

interp lang::VariantName := Lean.Name

-- For every enumeration, its variants `vs` and which are recursive, `p`,
-- with the count that both front ends compare.
impl well_founded: lang::well_founded for (vs : List Lean.Name) (p : Lean.Name → Bool) {
  variants := Fren.FinSet.ofList vs,
  recursive := Fren.FinSet.ofList (vs.filter p),
  accepted? := Fren.Core.wellFounded vs.length (vs.filter p).length,
} by
  intro vs p _
  simp [fren_spec, Fren.Core.wellFounded, ofList_filter_eq]

interp lang::FieldName := Lean.Name

-- For every literal, with the check that both front ends use.
impl record_literal: lang::record_literal for (fields given : Array Lean.Name) {
  fields := Fren.FinSet.ofArray fields,
  given := Fren.FinSet.ofArray given,
  n_repeated := Fren.Core.repeatsOf given,
  accepted? := Fren.Core.recordLiteralAccepted fields given,
} by
  intro fields given _
  have : Fren.FinSet.ofArray given = Fren.FinSet.ofArray fields ↔ (∀ g ∈ given, g ∈ fields) ∧ ∀ f ∈ fields, f ∈ given := by
    rw [Fren.FinSet.ext_iff]
    simp only [Fren.FinSet.mem_ofArray]
    exact ⟨fun h => ⟨fun g hg => (h g).mp hg, fun f hf => (h f).mpr hf⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩
  simp only [fren_spec, Fren.Core.recordLiteralAccepted, this, Bool.and_eq_true, Array.all_eq_true',
    Array.contains_iff_mem, beq_iff_eq]
  simp

impl variable_type: lang::variable_type for (o u d : Bool) {
  output? := o,
  unbounded? := u,
  defined? := d,
  accepted? := Fren.Core.variableTypeAccepted o u d,
}

impl field_init: lang::field_init for (f : Bool) (n : Nat) {
  field? := f,
  n := n,
  accepted? := Fren.Core.fieldInitOk f n,
} by
  intro f n _
  cases f <;> simp [fren_spec, Fren.Core.fieldInitOk] <;> omega

-- For every `match`, the variants `vs`, those with an arm, `p`, and the
-- counts, with the count that both front ends compare.
impl match_arms: lang::match_arms for (vs : List Lean.Name) (p : Lean.Name → Bool) (w : Bool) (r a : Nat) {
  variants := Fren.FinSet.ofList vs,
  covered := Fren.FinSet.ofList (vs.filter p),
  wildcard? := w,
  n_repeated := r,
  n_after := a,
  accepted? := Fren.Core.matchArmsAccepted vs.length (vs.filter p).length w r a,
} by
  intro vs p w r a _
  have hle := List.length_filter_le p vs
  cases w <;> simp [fren_spec, Fren.Core.matchArmsAccepted, ofList_filter_eq] <;> omega

impl function_params: lang::function_params for (d : Bool) (p n : Nat) {
  defined? := d,
  n_params := p,
  n_named := n,
  accepted? := Fren.Core.functionParamsAccepted d p n,
} by
  intro d p n _
  cases d <;> simp [fren_spec, Fren.Core.functionParamsAccepted] <;> omega

/-! ## Strings and decidability (`Reqs/Lang/Types#strings`, `Reqs/Lang/Decidability`) -/

impl string_char: lang::string_char for (c : Int) {
  code := c,
  accepted? := Fren.Core.stringCharAccepted c,
} by
  intro c _
  simp [fren_spec, Fren.Core.stringCharAccepted, Fren.Core.maxChar]

-- With the pattern parser, which both front ends use.
impl char_range: lang::char_range for (lo hi : Int) {
  low := lo,
  high := hi,
  accepted? := Fren.Core.charRangeAccepted lo hi,
} by
  intro lo hi _
  simp [fren_spec, Fren.Core.charRangeAccepted]

instance : Fren.Finite Fren.Core.Method :=
  ⟨Fren.Core.Method.all.toList, by intro x; cases x <;> simp [Fren.Core.Method.all]⟩

def toMethod : Fren.Core.Method → lang.Method
  | .len => .Len
  | .startsWith => .StartsWith
  | .endsWith => .EndsWith
  | .contains => .Contains
  | .matches => .Matches
  | .at => .At
  | .slice => .Slice
  | .indexOf => .IndexOf
  | .replace => .Replace
  | .replaceAll => .ReplaceAll
  | .card => .Card
  | .inverse => .Inverse
  | .closure => .Closure
  | .image => .Image
  | .domain => .Domain
  | .range => .Range
  | .update => .Update
  | .rev => .Rev

-- The table of methods that both front ends use.
impl method_type: lang::method_type for (m : Fren.Core.Method) (k : lang.ValueType) {
  method := toMethod m,
  receiver := k,
  accepted? := m.accepts (k == .StringTy) (k == .SetTy) (k == .RelTy) (k == .SeqTy),
  -- `string` is the receiver's type, and `elem` is never a result.
  result := match m.result with
    | .bool => .BoolTy | .int => .IntTy | .string | .elem => k | .set => .SetTy | .rel => .RelTy,
  n_params := m.arity,
} by
  intro m k _
  cases m <;> cases k <;> simp [fren_spec, toMethod, Fren.Core.Method.accepts, Fren.Core.Method.relational,
    Fren.Core.Method.result,
    Fren.Core.Method.arity, Fren.Core.Method.params]

instance : Fren.Finite Fren.Core.Construct :=
  ⟨[.stringCompare, .stringAtom, .stringIndex, .stringSearch, .setAlgebra, .setFunction, .relational, .relationalCard, .seqArray, .seqWord], by intro x; cases x <;> simp⟩

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

/-! ## Lexical structure -/

-- For every identifier: the lexer's reserved words are the spec's.
impl reserved_word: lang::reserved_word for (s : String) {
  lexeme := s,
  reserved? := FrenCli.reserved.contains s,
} by
  intro s _
  simp [fren_spec, FrenCli.reserved]

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

/-- `[A-Za-z0-9_'?]` is what continues an identifier. -/
theorem continue_class (c : Char) :
    inRanges [('A', 'Z'), ('a', 'z'), ('0', '9'), ('_', '_'), ('\'', '\''), ('?', '?')] c = (isIdRest c || c == '?') := by
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

end Lexical

-- For every lexeme and the input after it: whether the lexer continues it.
impl identifier_end: lang::identifier_end for (cs rest : List Char) {
  lexeme := String.ofList cs,
  remaining := String.ofList rest,
  ends? := Fren.Core.identExtends rest.toArray (cs.getLast?.getD ' ') 0 == 0,
} by
  rintro cs rest -
  simp only [fren_spec, Lexical.endsWith_question, Fren.Core.Re.matches, String.toList_ofList,
    Fren.Core.Re.mat_cat_cls, Fren.Core.Re.mat_star_any]
  cases h : cs.getLast? with
  | some l =>
    by_cases hl : l = '?'
    · subst hl; simp [Fren.Core.identExtends]
    · rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
        simp [Fren.Core.identExtends, hl, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
        split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with hc | hc <;> simp_all)
  | none =>
    rcases rest with _ | ⟨c, _ | ⟨d, t⟩⟩ <;>
      simp [Fren.Core.identExtends, Lexical.continue_class, Lexical.dot_class, Lexical.start_class] <;>
      split <;> (try split) <;> (try simp_all) <;> (rename_i hc; rcases hc with hc | hc <;> simp_all)

end Fren.Impls
