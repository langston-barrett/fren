-- keep-sorted start
import FrenCore.Closures
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Higher-order functions (`Reqs/Lang/HigherOrder`) -/

namespace Fren.Impls

def toTypeSite : Fren.Core.TypeSite → lang.TypeSite
  | .definedParameter => .DefinedParameter
  | .uninterpretedParameter => .UninterpretedParameter
  | .result => .Result
  | .constant => .Constant
  | .variable => .Variable
  | .field => .Field
  | .payload => .Payload
  | .definition => .Definition
  | .boundName => .BoundName
  | .alias => .Alias
  | .closureParameter => .ClosureParameter

-- For every place where a type is written and every way down to a function
-- type within it: the code that both front ends report (`Core.fnTypeCode?`),
-- which reads only whether the function type is within another.
impl function_type_place: lang::function_type_place for (site : Fren.Core.TypeSite) (w : List lang.Within) {
  site := toTypeSite site,
  within := Fren.Seq.ofList w,
  accepted? := (Fren.Core.fnTypeCode? site !w.isEmpty).isNone,
  code := (Fren.Core.fnTypeCode? site !w.isEmpty).getD "",
} by
  intro site w _
  cases site <;> cases w <;> simp [fren_spec, toTypeSite, Fren.Core.fnTypeCode?, Fren.Seq.ext_iff]

def toFnPart : Fren.Core.FnPart → lang.FnPart
  | .plain => .Plain
  | .nat => .Natural
  | .pattern => .Patterned
  | .function => .Function

-- For every function type's parts, as both front ends classify them.
impl function_type_parts: lang::function_type_parts for (ps : List Fren.Core.FnPart) {
  kinds := Fren.Seq.ofList (ps.map toFnPart),
  accepted? := Fren.Core.fnPartsAccepted ps,
} by
  intro ps _
  simp only [fren_spec, Fren.Core.fnPartsAccepted]
  induction ps with
  | nil => simp
  | cons p ps ih => cases p <;> simp_all [toFnPart]

def toParamKind : Fren.Core.ParamKind → lang.ParamKind
  | .value => .Value
  | .function n => .Function n

def toArgShape : Fren.Core.ArgShape → lang.ArgShape
  | .closure n => .Closure n
  | .definedName => .DefinedName
  | .uninterpretedName => .UninterpretedName
  | .fnParameterName => .FnParameterName
  | .other => .Other

-- For every parameter and argument: whether both front ends accept it, and
-- the code that they report (`Core.argumentCode?`).
impl function_argument: lang::function_argument for (p : Fren.Core.ParamKind) (a : Fren.Core.ArgShape) {
  param := toParamKind p,
  arg := toArgShape a,
  accepted? := (Fren.Core.argumentCode? p a).isNone,
  code := (Fren.Core.argumentCode? p a).getD "",
} by
  intro p a _
  cases p <;> cases a <;> simp [fren_spec, toParamKind, toArgShape, Fren.Core.argumentCode?]
  all_goals rename_i m n _
  all_goals by_cases h : m = n <;> simp [h, lang.ParamKind.Function.x0] <;> omega

def toComparand : Fren.Core.Comparand → lang.Comparand
  | .value => .Value
  | .closure => .Closure
  | .functionName => .FunctionName

-- For every comparison's operands, as both front ends classify them.
impl function_comparison: lang::function_comparison for (ops : List Fren.Core.Comparand) {
  operands := Fren.Seq.ofList (ops.map toComparand),
  accepted? := Fren.Core.comparisonAccepted ops,
} by
  intro ops _
  simp only [fren_spec, Fren.Core.comparisonAccepted]
  induction ops with
  | nil => simp
  | cons o os ih => cases o <;> simp_all [toComparand]

/-! ## Capture -/

interp lang::capture_symbol := fun (k : Int) => Fren.Core.captureSym k.toNat
interp lang::capture_symbols := fun (next : Nat) (cs : Fren.Seq String) =>
  Fren.Seq.ofList (Fren.Core.captureNames next cs.toList)
interp lang::renamed := fun (next : Nat) (cs ps : Fren.Seq String) (x : String) =>
  Fren.Core.captureRename next cs.toList ps.toList x

/-- Capture symbols are told apart by their numbers. -/
theorem captureSym_inj {a b : Nat} (h : Fren.Core.captureSym a = Fren.Core.captureSym b) : a = b := by
  have h' := congrArg String.toList h
  simp [Fren.Core.captureSym] at h'
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) h'
  simpa [Nat.ofDigitChars_ten_toDigits] using this

theorem captureNames_length (next : Nat) (cs : List String) : (Fren.Core.captureNames next cs).length = cs.length := by
  simp [Fren.Core.captureNames]

theorem captureNames_getElem (next : Nat) (cs : List String) (i : Nat) (h : i < (Fren.Core.captureNames next cs).length) :
    (Fren.Core.captureNames next cs)[i] = Fren.Core.captureSym (next + i) := by
  simp [Fren.Core.captureNames]

/-- What is after position `i` of `l`, as Fren's `slice` reads it. -/
theorem mem_slice_after (l : List String) (i : Int) (hi : 0 ≤ i) (y : String) :
    y ∈ ((Fren.Seq.ofList l).slice (i + 1) (l.length : Int)).toList ↔ y ∈ l.drop (i + 1).toNat := by
  unfold Fren.Seq.slice
  simp only [Fren.Seq.toList_ofList]
  split
  · rw [Fren.Seq.toList_ofList, List.take_of_length_le (by simp)]
  · rename_i hn
    have : l.length ≤ (i + 1).toNat := by omega
    simp [List.drop_of_length_le this]

/-- What is before position `k` of `l`, as Fren's `slice` reads it. -/
theorem mem_slice_before (l : List String) (k : Int) (_hk : 0 ≤ k) (hl : k < l.length) (y : String) :
    y ∈ ((Fren.Seq.ofList l).slice 0 k).toList ↔ y ∈ l.take k.toNat := by
  unfold Fren.Seq.slice
  simp only [Fren.Seq.toList_ofList]
  split
  · simp
  · rename_i hn
    have : k.toNat = 0 := by omega
    simp [this]

/-- The first position of `x` in `l`, where it is at `k` and not before. -/
theorem idxOf?_of_first (l : List String) (x : String) (k : Nat) (_hk : k < l.length) (hx : l[k] = x)
    (hb : x ∉ l.take k) : l.idxOf? x = some k := by
  rw [List.idxOf?_eq_some_iff]
  refine ⟨_hk, hx, fun i hi heq => hb ?_⟩
  rw [List.mem_take_iff_getElem]
  exact ⟨i, by omega, by simpa using heq⟩

-- For every closure body's mention, the binders around it once unfolded,
-- as `Core.inlineCall` builds them: the capture symbols, from
-- `Core.captureNames`, and the mention, from `Core.captureRename`.
impl closure_capture: lang::closure_capture
    for (next : Nat) (captured params values around inner : List String) (x : String) (k j : Int) {
  next := next,
  captured := Fren.Seq.ofList captured,
  params := Fren.Seq.ofList params,
  values := Fren.Seq.ofList values,
  around := Fren.Seq.ofList around,
  inner := Fren.Seq.ofList inner,
  x := x,
  k := k,
  j := j,
  symbols := (Fren.Seq.ofList (Fren.Core.captureNames next captured) : Fren.Seq String),
  mention := (if x ∈ inner then x else Fren.Core.captureRename next captured params x : String),
  binders := (Fren.Seq.ofList (Fren.Core.captureNames next captured ++ values ++ around ++ params ++ inner) : Fren.Seq String),
} by
  intro next captured params values around inner x k j h
  simp only [fren_spec] at h ⊢
  obtain ⟨hfresh, _, hfirst, hlast, hapart⟩ := h
  simp only [Fren.Seq.toList_ofList, Fren.Seq.mem_iff, Fren.Seq.len_eq] at hfresh hfirst hlast hapart ⊢
  have hlen := captureNames_length next captured
  refine ⟨by simp [Fren.Seq.ext_iff], ⟨by simp [hlen], fun i hi => ?_⟩, fun hx => by simp [hx], ?_, ?_⟩
  · rw [Fren.Seq.nth_of_lt _ _ hi.1 (by simp [hlen]; omega)]
    simp only [Fren.Seq.toList_ofList, captureNames_getElem]
    congr 1
    omega
  · rintro ⟨hni, hc⟩
    obtain ⟨⟨⟨hk0, hkl⟩, hkx⟩, hkb⟩ := hfirst hc
    have hnp : x ∉ params := fun hp => hapart ⟨hc, hp⟩
    rw [Fren.Seq.nth_of_lt (Fren.Seq.ofList captured) k hk0 (by simpa using hkl)] at hkx
    rw [mem_slice_before captured k hk0 hkl] at hkb
    have hidx := idxOf?_of_first captured x k.toNat (by omega) hkx hkb
    have hm : (if x ∈ inner then x else Fren.Core.captureRename next captured params x)
        = Fren.Core.captureSym (next + k.toNat) := by
      simp [hni, Fren.Core.captureRename, hnp, hidx]
    rw [hm, decide_eq_true_eq]
    have hkA : k.toNat < (Fren.Core.captureNames next captured).length := by rw [hlen]; omega
    refine ⟨⟨⟨hk0, by simp; omega⟩, ?_⟩, ?_⟩
    · rw [Fren.Seq.nth_of_lt _ _ hk0 (by simp; omega)]
      simp only [Fren.Seq.toList_ofList]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega), List.getElem_append_left hkA, captureNames_getElem]
    · rw [mem_slice_after _ k hk0]
      have hd : (k + 1).toNat ≤ (Fren.Core.captureNames next captured).length := by omega
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.drop_append_of_le_length hd]
      simp only [List.mem_append, not_or]
      have hf := hfresh (next + k.toNat) (by omega)
      simp only [Int.toNat_natCast] at hf
      refine ⟨?_, hf.1.1.1, hf.1.1.2, hf.1.2, hf.2⟩
      intro hmem
      obtain ⟨i, hi, heq⟩ := List.mem_drop_iff_getElem.mp hmem
      rw [captureNames_getElem] at heq
      have := captureSym_inj heq
      omega
  · rintro ⟨hni, hp⟩
    obtain ⟨⟨⟨hj0, hjl⟩, hjx⟩, hjb⟩ := hlast hp
    have hm : (if x ∈ inner then x else Fren.Core.captureRename next captured params x) = x := by
      simp [hni, Fren.Core.captureRename, hp]
    rw [hm, decide_eq_true_eq]
    rw [Fren.Seq.nth_of_lt (Fren.Seq.ofList params) j hj0 (by simpa using hjl)] at hjx
    rw [mem_slice_after params j hj0] at hjb
    have hpre : ((Fren.Core.captureNames next captured ++ values ++ around).length : Int) =
        (Fren.Core.captureNames next captured).length + values.length + around.length := by simp; omega
    refine ⟨⟨⟨by omega, by simp; omega⟩, ?_⟩, ?_⟩
    · rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
      simp only [Fren.Seq.toList_ofList]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      have key : ∀ (m : Nat) (hm : m < params.length), m = j.toNat → params[m] = x := by
        intro m hm e
        subst e
        exact hjx
      exact key _ _ (by simp; omega)
    · have h0 : 0 ≤ ((Fren.Core.captureNames next captured).length : Int) + values.length + around.length + j := by omega
      rw [mem_slice_after _ _ h0]
      have hd : (Fren.Core.captureNames next captured ++ values ++ around ++ params).length
          ≥ (((Fren.Core.captureNames next captured).length : Int) + values.length + around.length + j + 1).toNat := by
        simp; omega
      rw [List.drop_append_of_le_length hd]
      simp only [List.mem_append, not_or]
      refine ⟨?_, hni⟩
      rw [show (((Fren.Core.captureNames next captured).length : Int) + values.length + around.length + j + 1).toNat
          = (Fren.Core.captureNames next captured ++ values ++ around).length + (j + 1).toNat by simp; omega]
      rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
      exact hjb

end Fren.Impls
