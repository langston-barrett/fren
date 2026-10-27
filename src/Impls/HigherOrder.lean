-- keep-sorted start
import FrenCore.Closures
import Impls.Lang
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

def toWithin : Fren.Core.Within → lang.Within
  | .element => .Element
  | .argument => .Argument
  | .fnParameter => .FnParameter
  | .fnResult => .FnResult

-- For every place where a type is written and every way down to a function
-- type within it, as both front ends find it (`Core.fnTypeWithin`): the
-- code that they report (`Core.fnTypeCode?`).
impl function_type_place: lang::function_type_place for (site : Fren.Core.TypeSite) (w : List Fren.Core.Within) {
  site := toTypeSite site,
  within := Fren.Seq.ofList (w.map toWithin),
  accepted? := (Fren.Core.fnTypeCode? site w).isNone,
  code := (Fren.Core.fnTypeCode? site w).getD "",
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

/-! ## Capture, end to end

What `Core.captureFree` gives a closure's body, through `Core.STerm.free`
and `Core.STerm.renameFree`, which `Core.inlineCall` runs: each free symbol
of the renamed body is one of the closure's parameters, one of its capture
symbols, or not local, so that, with the capture symbols new
(`lang::closure_capture`), no binder of the higher-order body captures it. -/

open Fren.Core in
/-- Renaming keeps the names that a `let` binds. -/
theorem names_renameDefs (σ : String → Option String) : (bs : List STerm) →
    (STerm.renameDefs σ bs).filterMap bindName = bs.filterMap bindName
  | [] => by simp [STerm.renameDefs]
  | .list (.atom x :: rest) :: bs => by simp [STerm.renameDefs, bindName, names_renameDefs σ bs]
  | .list (.list l :: rest) :: bs => by simp [STerm.renameDefs, bindName, names_renameDefs σ bs]
  | .list [] :: bs => by simp [STerm.renameDefs, STerm.renameFree, STerm.renameL, bindName, names_renameDefs σ bs]
  | .atom a :: bs => by simp [STerm.renameDefs, STerm.renameFree, bindName, names_renameDefs σ bs]

open Fren.Core in
theorem bound_renameDefs (σ : String → Option String) (bs : List STerm) :
    STerm.bound (STerm.renameDefs σ bs) = STerm.bound bs := by
  funext s
  simp only [STerm.bound, names_renameDefs]

open Fren.Core in
mutual
/-- Each free symbol of a renamed term is a free symbol of the term,
renamed, where `σ` never names a binder form. -/
theorem free_renameFree (σ : String → Option String) (hσ : ∀ x y, σ x = some y → binderKw y = false) :
    (t : STerm) → ∀ s ∈ (t.renameFree σ).free, ∃ x ∈ t.free, s = (σ x).getD x
  | .atom a => by
    intro s hs
    simp only [STerm.renameFree, STerm.free, List.mem_singleton] at hs ⊢
    exact ⟨a, rfl, hs⟩
  | .list ts => by
    intro s hs
    simp only [STerm.renameFree, STerm.free] at hs ⊢
    exact freeL_renameL σ hσ ts s hs

theorem freeL_renameL (σ : String → Option String) (hσ : ∀ x y, σ x = some y → binderKw y = false) :
    (ts : List STerm) → ∀ s ∈ STerm.freeL (STerm.renameL σ ts), ∃ x ∈ STerm.freeL ts, s = (σ x).getD x
  | [.atom kw, .list bs, body] => by
    intro s hs
    by_cases hk : binderKw kw = true
    · have hb' : STerm.bound (if (kw == "let") = true then STerm.renameDefs σ bs else bs) = STerm.bound bs := by
        split
        · exact bound_renameDefs σ bs
        · rfl
      simp only [STerm.renameL, hk, if_true, STerm.freeL, hb', List.mem_append, List.mem_filter] at hs
      simp only [STerm.freeL, hk, if_true, List.mem_append, List.mem_filter]
      rcases hs with hs | ⟨hs, hn⟩
      · by_cases hl : (kw == "let") = true
        · simp only [hl, if_true] at hs ⊢
          obtain ⟨x, hx, rfl⟩ := freeDefs_renameDefs σ hσ bs s hs
          exact ⟨x, Or.inl hx, rfl⟩
        · simp [hl] at hs
      · have hσ' : ∀ x y, (if STerm.bound bs x then none else σ x) = some y → binderKw y = false := by
          intro x y h
          split at h
          · cases h
          · exact hσ x y h
        obtain ⟨x, hx, rfl⟩ := free_renameFree _ hσ' body _ hs
        by_cases hb : STerm.bound bs x = true
        · simp only [hb, if_true, Option.getD_none] at hn
          simp at hn
        · refine ⟨x, Or.inr ⟨hx, by simp [hb]⟩, by simp [hb]⟩
    · simp only [STerm.renameL, hk, Bool.false_eq_true, if_false] at hs
      have hk' : binderKw ((σ kw).getD kw) = false := by
        cases h : σ kw with
        | none => simpa [h] using hk
        | some y => simpa using hσ kw y h
      simp only [STerm.freeL, hk', Bool.false_eq_true, if_false, List.mem_cons, List.mem_append] at hs
      simp only [STerm.freeL, hk, Bool.false_eq_true, if_false, List.mem_cons, List.mem_append]
      rcases hs with hs | hs | hs
      · exact ⟨kw, Or.inl rfl, hs⟩
      · obtain ⟨x, hx, rfl⟩ := freeL_renameL σ hσ bs s hs
        exact ⟨x, Or.inr (Or.inl hx), rfl⟩
      · obtain ⟨x, hx, rfl⟩ := free_renameFree σ hσ body s hs
        exact ⟨x, Or.inr (Or.inr hx), rfl⟩
  | [] => by simp [STerm.renameL, STerm.freeL]
  | .list x :: ts => by
    intro s hs
    simp only [STerm.renameL, STerm.freeL, STerm.renameFree, List.mem_append] at hs
    simp only [STerm.freeL, List.mem_append]
    rcases hs with hs | hs
    · obtain ⟨y, hy, rfl⟩ := free_renameFree σ hσ (.list x) s (by simpa [STerm.renameFree] using hs)
      exact ⟨y, Or.inl hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := freeEach_renameEach σ hσ ts s hs
      exact ⟨y, Or.inr hy, rfl⟩
  | .atom a :: [] => by
    intro s hs
    simp only [STerm.renameL, STerm.renameEach, STerm.freeL, STerm.freeEach, STerm.renameFree, STerm.free,
      List.append_nil, List.mem_singleton] at hs ⊢
    exact ⟨a, rfl, hs⟩
  | .atom a :: [u] => by
    intro s hs
    rw [STerm.renameL, STerm.renameEach, STerm.renameEach, STerm.freeL, STerm.freeEach, STerm.freeEach] at hs
    rw [STerm.freeL, STerm.freeEach, STerm.freeEach]
    simp only [STerm.renameFree, STerm.free, List.append_nil, List.mem_append, List.mem_singleton] at hs ⊢
    rcases hs with hs | hs
    · exact ⟨a, Or.inl rfl, hs⟩
    · obtain ⟨y, hy, rfl⟩ := free_renameFree σ hσ u s hs
      exact ⟨y, Or.inr hy, rfl⟩
    all_goals (intro _ _ _ _ h2; simp at h2)
  | .atom a :: .atom b :: [body] => by
    intro s hs
    simp only [STerm.renameL, STerm.renameEach, STerm.freeL, STerm.freeEach, STerm.renameFree, STerm.free,
      List.append_nil, List.singleton_append, List.mem_cons] at hs ⊢
    rcases hs with hs | hs | hs
    · exact ⟨a, Or.inl rfl, hs⟩
    · exact ⟨b, Or.inr (Or.inl rfl), hs⟩
    · obtain ⟨y, hy, rfl⟩ := free_renameFree σ hσ body s hs
      exact ⟨y, Or.inr (Or.inr hy), rfl⟩
  | .atom a :: u :: v :: w :: rest => by
    intro s hs
    rw [STerm.renameL, STerm.freeL] at hs
    rw [STerm.freeL]
    simp only [STerm.renameFree, STerm.free, List.mem_append, List.mem_singleton] at hs ⊢
    rcases hs with hs | hs
    · exact ⟨a, Or.inl rfl, hs⟩
    · obtain ⟨y, hy, rfl⟩ := freeEach_renameEach σ hσ (u :: v :: w :: rest) s hs
      exact ⟨y, Or.inr hy, rfl⟩
    all_goals (intro _ _ _ _ h2; have := congrArg List.length h2; simp [STerm.renameEach] at this)

theorem freeEach_renameEach (σ : String → Option String) (hσ : ∀ x y, σ x = some y → binderKw y = false) :
    (ts : List STerm) → ∀ s ∈ STerm.freeEach (STerm.renameEach σ ts), ∃ x ∈ STerm.freeEach ts, s = (σ x).getD x
  | [] => by simp [STerm.renameEach, STerm.freeEach]
  | t :: ts => by
    intro s hs
    simp only [STerm.renameEach, STerm.freeEach, List.mem_append] at hs ⊢
    rcases hs with hs | hs
    · obtain ⟨x, hx, rfl⟩ := free_renameFree σ hσ t s hs
      exact ⟨x, Or.inl hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := freeEach_renameEach σ hσ ts s hs
      exact ⟨x, Or.inr hx, rfl⟩

theorem freeDefs_renameDefs (σ : String → Option String) (hσ : ∀ x y, σ x = some y → binderKw y = false) :
    (bs : List STerm) → ∀ s ∈ STerm.freeDefs (STerm.renameDefs σ bs), ∃ x ∈ STerm.freeDefs bs, s = (σ x).getD x
  | [] => by simp [STerm.renameDefs, STerm.freeDefs]
  | .list (x :: rest) :: bs => by
    intro s hs
    simp only [STerm.renameDefs, STerm.freeDefs, List.mem_append] at hs ⊢
    rcases hs with hs | hs
    · obtain ⟨y, hy, rfl⟩ := freeEach_renameEach σ hσ rest s hs
      exact ⟨y, Or.inl hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := freeDefs_renameDefs σ hσ bs s hs
      exact ⟨y, Or.inr hy, rfl⟩
  | .list [] :: bs => by
    intro s hs
    simp only [STerm.renameDefs, STerm.freeDefs, STerm.renameFree, STerm.renameL, STerm.free, STerm.freeL,
      List.nil_append] at hs ⊢
    exact freeDefs_renameDefs σ hσ bs s hs
  | .atom a :: bs => by
    intro s hs
    simp only [STerm.renameDefs, STerm.renameFree, STerm.freeDefs, STerm.free, List.mem_append,
      List.mem_singleton] at hs ⊢
    rcases hs with hs | hs
    · exact ⟨a, Or.inl rfl, hs⟩
    · obtain ⟨y, hy, rfl⟩ := freeDefs_renameDefs σ hσ bs s hs
      exact ⟨y, Or.inr hy, rfl⟩
end

open Fren.Core in
/-- No capture symbol starts a binder form. -/
theorem binderKw_captureSym (k : Nat) : binderKw (captureSym k) = false := by
  have h (w : String) (c : Char) (hw : w.toList.head? = some c) (hc : c ≠ '|') : captureSym k ≠ w := by
    intro e
    have := congrArg (fun s : String => s.toList.head?) e
    simp [captureSym, hw] at this
    exact hc this.symm
  simp only [binderKw, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨⟨⟨h "let" 'l' rfl (by decide), h "forall" 'f' rfl (by decide)⟩, h "exists" 'e' rfl (by decide)⟩,
    h "lambda" 'l' rfl (by decide)⟩

open Fren.Core in
-- The whole renaming of a closure's body, as `Core.inlineCall` runs it
-- (`Core.captureFree`): each free symbol of the renamed body is a parameter
-- of the closure, one of its capture symbols, or not local. With the
-- capture symbols new (`lang::closure_capture`'s `fresh`), no binder of the
-- higher-order body around the unfolded closure binds any of them.
theorem captureFree_free (t : STerm) (params : List String) (locals : String → Bool) (next : Nat) :
    ∀ s ∈ (captureFree t params locals next).1.free, s ∈ params
      ∨ s ∈ captureNames next (t.free.eraseDups.filter fun s => locals s && !params.contains s)
      ∨ locals s = false := by
  intro s hs
  let captured := t.free.eraseDups.filter fun s => locals s && !params.contains s
  have hcases : ∀ x, captureRename next captured params x = x ∨ ∃ k, captureRename next captured params x = captureSym k := by
    intro x
    unfold captureRename
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
  have hσ : ∀ x y, (let r := captureRename next captured params x; if r == x then none else some r) = some y →
      binderKw y = false := by
    intro x y h
    simp only at h
    split at h
    · cases h
    · rename_i hne
      cases h
      rcases hcases x with he | ⟨k, hk⟩
      · simp [he] at hne
      · rw [hk]
        exact binderKw_captureSym k
  obtain ⟨x, hx, rfl⟩ := free_renameFree _ hσ t s hs
  by_cases hp : x ∈ params
  · left
    simp [captureRename, hp]
  · cases hi : captured.idxOf? x with
    | some k =>
      right; left
      have hk := (List.idxOf?_eq_some_iff.mp hi).1
      have hr : captureRename next captured params x = captureSym (next + k) := by simp [captureRename, hp, hi]
      have hmem : captureSym (next + k) ∈ captureNames next captured := by
        simp only [captureNames, List.mem_map, List.mem_range]
        exact ⟨k, hk, rfl⟩
      by_cases he : captureSym (next + k) = x
      · simp only [hr, he, beq_self_eq_true, if_true, Option.getD_none]
        exact he ▸ hmem
      · simp only [hr, beq_iff_eq, he, if_false, Option.getD_some]
        exact hmem
    | none =>
      right; right
      have hr : captureRename next captured params x = x := by simp [captureRename, hp, hi]
      simp only [hr, beq_self_eq_true, if_true, Option.getD_none]
      have hnc : x ∉ captured := fun h => by
        have := List.idxOf?_eq_none_iff.mp hi
        exact this h
      cases hl : locals x
      · rfl
      · exfalso
        apply hnc
        simp only [captured, List.mem_filter, List.mem_eraseDups, Bool.and_eq_true, hl, true_and]
        exact ⟨hx, by simpa using hp⟩

/-! ## Obligations of closures -/

/-- `Core.siteHolds` is the obligation, or that some guard fails. -/
theorem siteHolds_eq (fs : List (Fren.Core.GuardedOperand × Bool)) (p : Bool) :
    Fren.Core.siteHolds fs p = (!(fs.all fun (o, c) => o.guard c !c) || p) := by
  induction fs with
  | nil => simp [Fren.Core.siteHolds, Fren.Core.siteGoal]
  | cons f fs ih =>
    obtain ⟨o, c⟩ := f
    simp only [Fren.Core.siteHolds, List.map_cons, Fren.Core.siteGoal] at ih ⊢
    rw [ih]
    cases h : o.guard c !c <;> simp [h]

theorem guard_holds_eq (o : Fren.Core.GuardedOperand) (c : Bool) :
    (if toGuardedOperand o = lang.GuardedOperand.WhenBody ∨ toGuardedOperand o = lang.GuardedOperand.ThenBranch ∨
        toGuardedOperand o = lang.GuardedOperand.AndRight ∨ toGuardedOperand o = lang.GuardedOperand.ArmGuard ∨
        toGuardedOperand o = lang.GuardedOperand.ArmBody then c else !c) = (o.guard c !c) := by
  cases o <;> simp [toGuardedOperand, Fren.Core.GuardedOperand.guard, Fren.Core.GuardedOperand.whenHolds]

-- For every application with at most three guards around it, the
-- obligation as both front ends ask it (`Core.siteGoal`, here over the
-- conditions' values).
impl closure_obligation: lang::closure_obligation for (fs : List (Fren.Core.GuardedOperand × Bool)) (p : Bool) {
  frames := Fren.Seq.ofList (fs.map fun (o, _) => toGuardedOperand o),
  conditions := Fren.Seq.ofList (fs.map (·.2)),
  at_args? := p,
  evaluated? := fs.all fun (o, c) => o.guard c !c,
  holds? := Fren.Core.siteHolds fs p,
} by
  intro fs p h
  simp only [fren_spec] at h ⊢
  have hl : fs.length ≤ 3 := by simp at h; omega
  rw [siteHolds_eq]
  match fs, hl with
  | [], _ => simp
  | [(o, c)], _ => simp [guard_holds_eq]
  | [(o, c), (o', c')], _ =>
    simp [guard_holds_eq]
    cases o.guard c !c <;> cases o'.guard c' !c' <;> simp
  | [(o, c), (o', c'), (o'', c'')], _ =>
    simp [guard_holds_eq, Bool.and_assoc]
    cases o.guard c !c <;> cases o'.guard c' !c' <;> cases o''.guard c'' !c'' <;> simp

end Fren.Impls
