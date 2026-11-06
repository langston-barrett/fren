-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- A segment, as both front ends give it to `Core.ownArgs` and `Core.ownIn`
(`lang::Segment`): the own type's name `G`, the type parameters' names `T0`,
`T1` and `T2`, another name `X`, and the markers. -/
def segString : lang.Segment → String
  | .Own => "G"
  | .Ident .P0 => "T0"
  | .Ident .P1 => "T1"
  | .Ident .P2 => "T2"
  | .Ident .Other => "X"
  | .ArgsOpen => Fren.Core.argsOpen
  | .ArgsSep => Fren.Core.argsSep
  | .ArgsClose => Fren.Core.argsClose
  | .SetOf => Fren.Core.setSeg
  | .SeqOf => Fren.Core.seqSeg
  | .RelOf => Fren.Core.relSeg
  | .RelSep => Fren.Core.relSep

/-- The names of the first `n` type parameters, as `Core.ownArgs` takes them. -/
def ownParams (n : Nat) : Array String := (["T0", "T1", "T2"].take n).toArray

/-- The own type with its first `n` type parameters, in order
(`lang::own_written`). -/
def ownWrittenList : Nat → List lang.Segment
  | 0 => [.Own]
  | 1 => [.Own, .ArgsOpen, .Ident .P0, .ArgsClose]
  | 2 => [.Own, .ArgsOpen, .Ident .P0, .ArgsSep, .Ident .P1, .ArgsClose]
  | _ => [.Own, .ArgsOpen, .Ident .P0, .ArgsSep, .Ident .P1, .ArgsSep, .Ident .P2, .ArgsClose]

/-- No segment is a pattern's, so `Core.withoutPatterns` keeps them all. -/
theorem segString_patterns (a : lang.Segment) :
    (!(segString a).startsWith Fren.Core.patSeg && !(segString a).startsWith Fren.Core.patOuterSeg) = true := by
  rcases a with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> decide +kernel

theorem withoutPatterns_segs (L : List lang.Segment) :
    Fren.Core.withoutPatterns (L.map segString).toArray = (L.map segString).toArray := by
  apply Array.toList_inj.1
  simp only [Fren.Core.withoutPatterns, Array.toList_filter]
  rw [List.filter_eq_self.2]
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
  exact segString_patterns b

/-- Distinct segments are distinct strings. -/
theorem segString_beq (a b : lang.Segment) : (segString a == segString b) = decide (a = b) := by
  rcases a with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    rcases b with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> decide

theorem map_segString_inj (l m : List lang.Segment) : (l.map segString = m.map segString) ↔ l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have := segString_beq a b
      simp only [List.map_cons, List.cons.injEq, ih]
      constructor
      · rintro ⟨h, rfl⟩; refine ⟨?_, rfl⟩; simpa [h] using this
      · rintro ⟨rfl, rfl⟩; simp

theorem asDeclared_eq (n : Fin 4) (h : (n : Nat) ≠ 0) :
    Fren.Core.argsOpen :: (ownParams n).toList.intersperse Fren.Core.argsSep ++ [Fren.Core.argsClose] =
      ((ownWrittenList n).drop 1).map segString := by
  obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | exact absurd rfl h | rfl

theorem beq_own (a : lang.Segment) : (segString a == "G") = decide (a = .Own) := segString_beq a .Own
theorem beq_argsOpen (a : lang.Segment) : (segString a == Fren.Core.argsOpen) = decide (a = .ArgsOpen) :=
  segString_beq a .ArgsOpen
theorem beq_setSeg (a : lang.Segment) : (segString a == Fren.Core.setSeg) = decide (a = .SetOf) :=
  segString_beq a .SetOf
theorem beq_seqSeg (a : lang.Segment) : (segString a == Fren.Core.seqSeg) = decide (a = .SeqOf) :=
  segString_beq a .SeqOf
theorem beq_relSeg (a : lang.Segment) : (segString a == Fren.Core.relSeg) = decide (a = .RelOf) :=
  segString_beq a .RelOf
theorem beq_relSep (a : lang.Segment) : (segString a == Fren.Core.relSep) = decide (a = .RelSep) :=
  segString_beq a .RelSep

theorem any_own (L : List lang.Segment) : ((L.map segString).any fun s => s == "G") = decide (.Own ∈ L) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih, beq_own, eq_comm]

theorem beq_map (l m : List lang.Segment) : (l.map segString == m.map segString) = decide (l = m) := by
  rw [Bool.eq_iff_iff]; simp [map_segString_inj]

theorem beq_map_cons (b : lang.Segment) (l m : List lang.Segment) :
    (segString b :: l.map segString == m.map segString) = decide (b :: l = m) := by
  rw [← List.map_cons]; exact beq_map _ _

theorem beq_map_tail (b : lang.Segment) (l m : List lang.Segment) :
    (segString b :: l.map segString == (m.map segString).tail) = decide (b :: l = m.tail) := by
  rw [← List.map_tail]; exact beq_map_cons _ _ _

theorem isEmpty_map_tail (m : List lang.Segment) : (m.map segString).tail.isEmpty = decide (m.tail = []) := by
  cases m with
  | nil => rfl
  | cons a m => cases m <;> rfl

theorem any_eq_own (l : List lang.Segment) : (l.any fun x => decide (x = .Own)) = decide (.Own ∈ l) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, eq_comm]

theorem own_eq (x : lang.Segment) : (lang.Segment.Own = x) ↔ (x = .Own) := eq_comm

theorem ownParams_empty (n : Fin 4) : (ownParams n = #[]) ↔ (n : Nat) = 0 := by
  obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | simp [ownParams]

/-- Whether segments are the own type, with type arguments or without. -/
def wholeB (L : List lang.Segment) : Bool :=
  decide (L.head? = some .Own) && (decide (L.length = 1) || decide (L[1]? = some .ArgsOpen))

/-- Whether segments are a set's, sequence's or relation's. -/
def elemHead (L : List lang.Segment) : Bool :=
  decide (L.head? = some .SetOf) || decide (L.head? = some .SeqOf) || decide (L.head? = some .RelOf)

/-- What `Core.ownArgs` computes from segments, over the segments. -/
theorem ownArgs_eq (L : List lang.Segment) (n : Fin 4) :
    Fren.Core.ownArgs (L.map segString).toArray "G" (ownParams n) =
      (wholeB L, (if (n : Nat) = 0 then decide (L.length = 1) else decide (L.drop 1 = (ownWrittenList n).drop 1)),
        !elemHead L && decide (.Own ∈ (if wholeB L then L.drop 1 else L))) := by
  simp only [Fren.Core.ownArgs, withoutPatterns_segs]
  by_cases h0 : (n : Nat) = 0
  · rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
    all_goals simp [wholeB, elemHead, beq_own, beq_argsOpen, beq_setSeg, beq_seqSeg, beq_relSeg, h0,
      ownParams, List.take_of_length_le]
    all_goals try split
    all_goals simp_all [any_eq_own, own_eq, beq_own, Function.comp_def]
  · rw [asDeclared_eq n h0]
    rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
    all_goals simp [wholeB, elemHead, beq_own, beq_argsOpen, beq_setSeg, beq_seqSeg, beq_relSeg, h0, ownParams_empty,
      List.take_of_length_le, beq_map_tail, isEmpty_map_tail]
    all_goals try split
    all_goals simp_all [any_eq_own, own_eq, beq_own, Function.comp_def]

/-- Whether a segment is a marker of an element type. -/
def isMarker (x : lang.Segment) : Bool :=
  decide (x = .SetOf) || decide (x = .SeqOf) || decide (x = .RelOf) || decide (x = .RelSep)

theorem filter_markers (L : List lang.Segment) :
    (L.map segString).filter (fun s => s != Fren.Core.setSeg && s != Fren.Core.relSeg && s != Fren.Core.relSep &&
      s != Fren.Core.seqSeg) = (L.filter fun x => !isMarker x).map segString := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, bne, beq_setSeg, beq_relSeg, beq_relSep, beq_seqSeg, isMarker]
  cases x <;> simp

/-- What `Core.ownIn` computes from segments, over the segments. -/
theorem ownIn_eq (L : List lang.Segment) :
    Fren.Core.ownIn (L.map segString).toArray "G" =
      (decide (L = [.Own]), decide ((((.SetOf ∈ L ∨ .SeqOf ∈ L) ∨ .RelOf ∈ L) ∨ .RelSep ∈ L) ∧ .Own ∈ L)) := by
  simp only [Fren.Core.ownIn, withoutPatterns_segs]
  simp [filter_markers]
  have ho (a : lang.Segment) : (!isMarker a && segString a == "G") = decide (a = .Own) := by
    rcases a with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> decide
  constructor
  · rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rcases a with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> decide
    · have h1 := List.length_filter_le (fun x => !isMarker x) rest
      simp only [List.length_cons, List.filter_cons]
      split <;> split <;> simp <;> omega
  · simp only [ho, any_eq_own]
    rw [Bool.eq_iff_iff]
    simp only [isMarker, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨x, hx, ((h | h) | h) | h⟩, h'⟩ <;> subst h <;> simp_all
    · rintro ⟨((h | h) | h) | h, h'⟩ <;> exact ⟨⟨_, h, by simp⟩, h'⟩

theorem nth_zero_cons (a : lang.Segment) (l : List lang.Segment) : (Seq.ofList (a :: l)).nth 0 = a := by
  rw [Seq.nth_of_lt _ _ (by decide) (by simp)]; rfl

theorem nth_one_cons (a b : lang.Segment) (l : List lang.Segment) : (Seq.ofList (a :: b :: l)).nth 1 = b := by
  rw [Seq.nth_of_lt _ _ (by decide) (by simp; omega)]; rfl

theorem own_elem_spec (L : List lang.Segment) :
    (Seq.ofList L ≠ ∅ ∧ (Seq.ofList L).nth 0 ∈ ({.SetOf, .SeqOf, .RelOf} : Fren.FinSet lang.Segment))
      ↔ elemHead L = true := by
  rcases L with _ | ⟨a, rest⟩ <;> simp [elemHead, Seq.ext_iff, or_assoc]

theorem recursivePlace_accepted (d e : Bool) :
    Fren.Core.typeParamPlaceAccepted (Fren.Core.recursivePlace d e) = (!e && d) := by
  cases d <;> cases e <;> rfl

theorem own_whole_spec (L : List lang.Segment) :
    ((Seq.ofList L ≠ ∅ ∧ (Seq.ofList L).nth 0 = .Own) ∧ ((Seq.ofList L).len = 1 ∨ (Seq.ofList L).nth 1 = .ArgsOpen))
      ↔ wholeB L = true := by
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [wholeB, Seq.ext_iff, nth_zero_cons, nth_one_cons] <;> omega

theorem own_written_spec (n : Fin 4) :
    (if ((n : Nat) : Int) = 0 then Seq.unit lang.Segment.Own
      else if ((n : Nat) : Int) = 1 then
        Seq.unit lang.Segment.Own ++ (Seq.unit lang.Segment.ArgsOpen ++
          (Seq.unit (lang.Segment.Ident lang.Arg.P0) ++ Seq.unit lang.Segment.ArgsClose))
      else if ((n : Nat) : Int) = 2 then
        Seq.unit lang.Segment.Own ++ (Seq.unit lang.Segment.ArgsOpen ++ (Seq.unit (lang.Segment.Ident lang.Arg.P0) ++
          (Seq.unit lang.Segment.ArgsSep ++ (Seq.unit (lang.Segment.Ident lang.Arg.P1) ++
            Seq.unit lang.Segment.ArgsClose))))
      else
        Seq.unit lang.Segment.Own ++ (Seq.unit lang.Segment.ArgsOpen ++ (Seq.unit (lang.Segment.Ident lang.Arg.P0) ++
          (Seq.unit lang.Segment.ArgsSep ++ (Seq.unit (lang.Segment.Ident lang.Arg.P1) ++
            (Seq.unit lang.Segment.ArgsSep ++ (Seq.unit (lang.Segment.Ident lang.Arg.P2) ++
              Seq.unit lang.Segment.ArgsClose)))))))
      = Seq.ofList (ownWrittenList n) := by
  obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | rfl

theorem own_slice_spec (L : List lang.Segment) (c : Prop) [Decidable c] :
    (Seq.ofList L).slice (if c then 1 else 0) (Seq.ofList L).len = Seq.ofList (if c then L.drop 1 else L) := by
  unfold Seq.slice
  split <;> rename_i h <;> split <;> simp_all [Seq.ext_iff]
  all_goals first | exact List.take_of_length_le (by simp) | (rcases L with _ | ⟨_, _ | _⟩ <;> simp_all <;> omega)

theorem own_decl_eq (L : List lang.Segment) (n : Fin 4) (h : wholeB L = true) :
    (if n = 0 then decide (L.length = 1) else decide (L.tail = (ownWrittenList n).tail)) =
      decide (L = ownWrittenList n) := by
  rcases L with _ | ⟨a, rest⟩
  · simp [wholeB] at h
  · have ha : a = .Own := by simp [wholeB] at h; exact h.1
    subst ha
    obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | simp [ownWrittenList]

-- For every declaration with at most three type parameters and every
-- written type, as segments: what both front ends read from a payload's or
-- field's type (`Core.ownArgs`, `Core.ownIn`), and the check of a recursive
-- payload that both make with it (`Core.recursivePlace`).
impl own_type: lang::own_type for (n : Fin 4) (segs : List lang.Segment) {
  params := (n : Nat),
  segs := Fren.Seq.ofList segs,
  own? := (Fren.Core.ownArgs (segs.map segString).toArray "G" (ownParams n)).1,
  as_declared? := (Fren.Core.ownArgs (segs.map segString).toArray "G" (ownParams n)).1 &&
    (Fren.Core.ownArgs (segs.map segString).toArray "G" (ownParams n)).2.1,
  nested? := (Fren.Core.ownArgs (segs.map segString).toArray "G" (ownParams n)).2.2,
  bare? := (Fren.Core.ownIn (segs.map segString).toArray "G").1,
  in_element? := (Fren.Core.ownIn (segs.map segString).toArray "G").2,
  accepted? := let (own, declared, nested) := Fren.Core.ownArgs (segs.map segString).toArray "G" (ownParams n)
    !(own || nested) || Fren.Core.typeParamPlaceAccepted (Fren.Core.recursivePlace declared nested),
} by
  intro n segs _
  simp only [fren_spec, ownArgs_eq, ownIn_eq, own_whole_spec, own_written_spec, own_slice_spec, own_elem_spec]
  have h3 : ((n : Nat) : Int) ≤ 3 := by omega
  cases hw : wholeB segs
  · simp [Seq.ext_iff, recursivePlace_accepted]
    by_cases ho : lang.Segment.Own ∈ segs <;> cases elemHead segs <;> simp [ho]
  · simp [h3, Seq.ext_iff, own_decl_eq segs n hw, recursivePlace_accepted]
    intro
    cases elemHead segs <;> simp

end Fren.Impls
