-- keep-sorted start
import Reqs.Lang.ModulesAndInterfaces
import Reqs.Lang.Types
-- keep-sorted end
open Fren.Lang

#fren_md "Implementations.md"

-- The linked enumerations check the sequence model too: their lookups,
-- lengths and shared predicates agree, for every finite list and index.
namespace Reqs.Lang.Implementations
open Fren.Generated

private def linkedList : lang.ModuleItems → List lang.ModuleItem
  | .Nil => []
  | .Cons item rest => item :: linkedList rest

private theorem linked_nth (items : lang.ModuleItems) (i : Nat) :
    lang.linked_item_at items (i : Int) = (linkedList items).getD i lang.NO_ITEM := by
  induction items generalizing i with
  | Nil => simp [lang.linked_item_at, linkedList]
  | Cons item rest ih =>
    cases i with
    | zero => simp [lang.linked_item_at, linkedList]
    | succ i =>
      have hn : (i : Int) + 1 ≠ 0 := by omega
      simpa [lang.linked_item_at, linkedList, hn] using ih i

private theorem linked_negative (items : lang.ModuleItems) (i : Int) (hi : i < 0) :
    lang.linked_item_at items i = lang.NO_ITEM := by
  induction items generalizing i with
  | Nil => simp [lang.linked_item_at]
  | Cons item rest ih =>
    have h0 : i ≠ 0 := by omega
    simp only [lang.linked_item_at, h0, ↓reduceIte]
    exact ih (i - 1) (by omega)

private theorem lookup_agrees (items : lang.ModuleItems) (i : Int) :
    lang.item_at (Fren.Seq.ofList (linkedList items)) i = lang.linked_item_at items i := by
  by_cases hi : 0 ≤ i
  · have hc : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
    rw [← hc, linked_nth]
    simp only [lang.item_at, Fren.Seq.len, Fren.Seq.toList, Fren.Seq.ofList, Fren.Seq.nth]
    split
    · rename_i h
      have hb : i.toNat < (linkedList items).length := by omega
      have hm : max i 0 = i := by omega
      simp [List.getD, List.getElem?_eq_getElem hb, hm]
    · rename_i h
      have hb : (linkedList items).length ≤ i.toNat := by omega
      simp [List.getD, List.getElem?_eq_none hb]
  · rw [linked_negative items i (by omega)]
    simp [lang.item_at, hi, Fren.Seq.len]

private theorem length_agrees (items : lang.ModuleItems) :
    lang.item_count (Fren.Seq.ofList (linkedList items)) = lang.linked_item_count items := by
  induction items with
  | Nil =>
    simp [lang.item_count, lang.linked_item_count, linkedList, Fren.Seq.len,
      Fren.Seq.toList, Fren.Seq.ofList]
  | Cons item rest ih =>
    have ih' : ((linkedList rest).length : Int) = lang.linked_item_count rest := ih
    simp only [lang.item_count, lang.linked_item_count, linkedList, Fren.Seq.len,
      Fren.Seq.toList, Fren.Seq.ofList, List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

-- The original predicates and both executable enumerations receive the
-- same raw inputs for every linked module and every sentence.
private theorem representation_agrees (items : lang.ModuleItems) (n u : lang.ModuleSentence) :
    let m : lang.ModuleModel := ⟨Fren.Seq.ofList (linkedList items)⟩
    lang.sentence_of? m n = lang.sentence_of_from? n (lang.linked_item_at items) ∧
    lang.rests_case? m n u = lang.rests_case_from? n u (lang.linked_item_at items) ∧
    lang.caveat_source? m n = lang.caveat_source_from? n (lang.linked_item_at items) ∧
    lang.rests_on_caveat? m n =
      lang.rests_on_caveat_from? (lang.linked_item_count items) n (lang.linked_item_at items) := by
  dsimp only
  have hget : (fun i => lang.item_of ⟨Fren.Seq.ofList (linkedList items)⟩ i) = lang.linked_item_at items := by
    funext i
    exact lookup_agrees items i
  have hlen : ((linkedList items).length : Int) = lang.linked_item_count items := length_agrees items
  simp [lang.sentence_of?, lang.rests_case?, lang.caveat_source?, lang.rests_on_caveat?, hget, hlen]

end Reqs.Lang.Implementations
