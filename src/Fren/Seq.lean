-- keep-sorted start
import FrenCore.Str
-- keep-sorted end

/-!
# Finite sequences

`Fren.Seq α`, the Lean type of Fren's `Seq<T>`: a list, wrapped so that the
SMT translation has a head symbol to match. Positions are `Int`s, as in
Fren, and each operation is total, with SMT-LIB's `seq.*` values at the
edges, which are those of its `str.*` operations: the methods that strings
share have the same values here as in `Fren.Str` on a string's characters,
which `src/FrenTest/Seqs.lean` checks.

Each operation has a `simp` lemma that states it by `List` functions, so
that implementations over lists are proved by `simp`.
-/

namespace Fren

/-- A finite sequence: a wrapper around `List`, not reducible, so that the
SMT translation has a head symbol to match. -/
def Seq (α : Type u) : Type u := List α

namespace Seq

variable {α : Type u}

/-- The sequence of the elements of `l`, in order. -/
def ofList (l : List α) : Seq α := l

/-- The list of the elements of `q`, in order. -/
def toList (q : Seq α) : List α := q

@[simp] theorem toList_ofList (l : List α) : toList (ofList l) = l := rfl
@[simp] theorem ofList_toList (q : Seq α) : ofList (toList q) = q := rfl

/-- Two sequences with the same elements in the same order are equal. -/
theorem ext {q r : Seq α} (h : q.toList = r.toList) : q = r := h

theorem ext_iff {q r : Seq α} : q = r ↔ q.toList = r.toList := Iff.rfl

instance : EmptyCollection (Seq α) := ⟨ofList []⟩
instance : Inhabited (Seq α) := ⟨∅⟩
instance : Append (Seq α) := ⟨fun q r => ofList (q.toList ++ r.toList)⟩
instance : Membership α (Seq α) := ⟨fun q x => x ∈ q.toList⟩

instance [DecidableEq α] (x : α) (q : Seq α) : Decidable (x ∈ q) :=
  inferInstanceAs (Decidable (x ∈ q.toList))

instance [DecidableEq α] : DecidableEq (Seq α) := inferInstanceAs (DecidableEq (List α))

instance [Repr α] : Repr (Seq α) := ⟨fun q n => reprPrec q.toList n⟩

@[simp] theorem toList_empty : toList (∅ : Seq α) = [] := rfl
@[simp] theorem toList_default : toList (default : Seq α) = [] := rfl
@[simp] theorem toList_append (q r : Seq α) : (q ++ r).toList = q.toList ++ r.toList := rfl
@[simp] theorem mem_iff {x : α} {q : Seq α} : x ∈ q ↔ x ∈ q.toList := Iff.rfl

/-- The sequence whose only element is `x`. -/
def unit (x : α) : Seq α := ofList [x]

@[simp] theorem toList_unit (x : α) : (unit x).toList = [x] := rfl

/-- `q.len`: SMT-LIB's `seq.len`. -/
def len (q : Seq α) : Int := q.toList.length

@[simp] theorem len_eq (q : Seq α) : len q = q.toList.length := rfl

/-- `q.nth(i)`: SMT-LIB's `seq.nth`; `default` unless `0 ≤ i < len q`. -/
def nth [Inhabited α] (q : Seq α) (i : Int) : α :=
  if h : 0 ≤ i ∧ i < q.toList.length then q.toList[i.toNat]'(by omega) else default

@[simp] theorem nth_of_lt [Inhabited α] (q : Seq α) (i : Int) (h₀ : 0 ≤ i) (h₁ : i < q.toList.length) :
    nth q i = q.toList[i.toNat]'(by omega) := by
  simp [nth, h₀, h₁]

theorem nth_eq_default [Inhabited α] (q : Seq α) (i : Int) (h : ¬(0 ≤ i ∧ i < q.toList.length)) :
    nth q i = default := by
  simp [nth, h]

/-- `q.slice(i, n)`: SMT-LIB's `seq.extract`; empty unless `0 ≤ i < len q`
and `0 < n`. -/
def slice (q : Seq α) (i n : Int) : Seq α :=
  if 0 ≤ i ∧ i < q.toList.length ∧ 0 < n then ofList ((q.toList.drop i.toNat).take n.toNat) else ∅

/-- `q.at(i)`: SMT-LIB's `seq.at`, which is `seq.extract q i 1`. -/
def «at» (q : Seq α) (i : Int) : Seq α := slice q i 1

/-- `q.index_of(t, i)`: SMT-LIB's `seq.indexof`; `-1` unless `0 ≤ i ≤ len q`
and `t` occurs at or after `i`, and `i` if `t` is empty. -/
def indexOf [DecidableEq α] (q t : Seq α) (i : Int) : Int :=
  if 0 ≤ i ∧ i ≤ q.toList.length then
    match (List.range (q.toList.length + 1 - i.toNat)).find? fun k =>
        t.toList.isPrefixOf (q.toList.drop (i.toNat + k)) with
    | some k => i + k
    | none => -1
  else -1

/-- `q.starts_with?(p)`: SMT-LIB's `seq.prefixof p q`. -/
def startsWith [DecidableEq α] (q p : Seq α) : Bool := p.toList.isPrefixOf q.toList

/-- `q.ends_with?(p)`: SMT-LIB's `seq.suffixof p q`. -/
def endsWith [DecidableEq α] (q p : Seq α) : Bool := p.toList.isSuffixOf q.toList

/-- `q.contains?(t)`: SMT-LIB's `seq.contains q t`, whether `t` is a
contiguous part of `q`; every sequence contains the empty one. -/
def contains [DecidableEq α] (q t : Seq α) : Bool :=
  (List.range (q.toList.length + 1)).any fun i => t.toList.isPrefixOf (q.toList.drop i)

/-- `q.replace(a, b)`: SMT-LIB's `seq.replace`: the first occurrence only,
and `b ++ q` if `a` is empty. -/
def replace [DecidableEq α] (q a b : Seq α) : Seq α :=
  if a.toList.isEmpty then b ++ q else
    let j := indexOf q a 0
    if j < 0 then q else
      ofList (q.toList.take j.toNat ++ b.toList ++ q.toList.drop (j.toNat + a.toList.length))

/-- `q.update(i, x)`: SMT-LIB's `seq.update q i (seq.unit x)`; `q` itself
unless `0 ≤ i < len q`. -/
def update (q : Seq α) (i : Int) (x : α) : Seq α :=
  if 0 ≤ i ∧ i < q.toList.length then ofList (q.toList.set i.toNat x) else q

/-- `q.rev`: SMT-LIB's `seq.rev`, the elements in reverse order. -/
def rev (q : Seq α) : Seq α := ofList q.toList.reverse

@[simp] theorem toList_rev (q : Seq α) : (rev q).toList = q.toList.reverse := rfl

@[simp] theorem toList_update_of_lt (q : Seq α) (i : Int) (x : α) (h₀ : 0 ≤ i)
    (h₁ : i < q.toList.length) : (update q i x).toList = q.toList.set i.toNat x := by
  simp [update, h₀, h₁]

theorem update_eq_self (q : Seq α) (i : Int) (x : α) (h : ¬(0 ≤ i ∧ i < q.toList.length)) :
    update q i x = q := by
  simp [update, h]

@[simp] theorem len_update (q : Seq α) (i : Int) (x : α) : len (update q i x) = len q := by
  unfold update; split <;> simp

@[simp] theorem len_rev (q : Seq α) : len (rev q) = len q := by simp

@[simp] theorem startsWith_iff [DecidableEq α] (q p : Seq α) :
    startsWith q p = true ↔ p.toList <+: q.toList :=
  List.isPrefixOf_iff_prefix

@[simp] theorem endsWith_iff [DecidableEq α] (q p : Seq α) :
    endsWith q p = true ↔ p.toList <:+ q.toList :=
  List.isSuffixOf_iff_suffix

/-! The methods that strings share agree with `Fren.Str` on a string's characters. -/

@[simp] theorem len_ofList_string (s : String) : len (ofList s.toList) = Fren.Str.len s := by
  simp [Fren.Str.len, String.length_toList]

theorem startsWith_string (s p : String) :
    startsWith (ofList s.toList) (ofList p.toList) = Fren.Str.startsWith s p := rfl

theorem endsWith_string (s p : String) :
    endsWith (ofList s.toList) (ofList p.toList) = Fren.Str.endsWith s p := rfl

theorem contains_string (s t : String) :
    contains (ofList s.toList) (ofList t.toList) = Fren.Str.contains s t := by
  simp [contains, Fren.Str.contains, String.length_toList]

theorem slice_string (s : String) (i n : Int) :
    (slice (ofList s.toList) i n).toList = (Fren.Str.slice s i n).toList := by
  unfold slice Fren.Str.slice; simp only [toList_ofList, String.length_toList]; split <;> simp_all

theorem at_string (s : String) (i : Int) :
    («at» (ofList s.toList) i).toList = (Fren.Str.at s i).toList := slice_string s i 1

theorem indexOf_string (s t : String) (i : Int) :
    indexOf (ofList s.toList) (ofList t.toList) i = Fren.Str.indexOf s t i := by
  unfold indexOf Fren.Str.indexOf; simp only [toList_ofList, String.length_toList]; rfl

end Seq

end Fren
