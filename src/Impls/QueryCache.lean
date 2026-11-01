-- keep-sorted start
import FrenCli.QueryStore
import Std.Data.String.ToNat
-- keep-sorted end

/-! # The keys and entries of the query cache

A query's key holds its observations' names exactly when none has a
numeric component (`cli::query_key`), and `FrenCli.decodeEntry?` inverts
`FrenCli.encodeEntry?`: the key, the answer and the model read back as
they were written, whatever characters they hold (`cli::query_entry`). -/

namespace Fren.Impls.QueryCache

open FrenCli
open Fren.Core (Outcome)

/-! ## Escaping -/

theorem escapeChar_other {c : Char} (h₁ : c ≠ '\\') (h₂ : c ≠ '\n') : escapeChar c = [c] := by
  unfold escapeChar; split <;> simp_all

theorem unescapeChars_cons_other {c : Char} (h : c ≠ '\\') (acc l : List Char) :
    unescapeChars acc (c :: l) = unescapeChars (c :: acc) l := by
  cases l with
  | nil => unfold unescapeChars; split <;> simp_all [unescapeChars]
  | cons d l => conv => lhs; unfold unescapeChars
                split <;> simp_all

theorem unescapeChars_escape : (acc l : List Char) → unescapeChars acc (l.flatMap escapeChar) = acc.reverse ++ l
  | acc, [] => by simp [unescapeChars]
  | acc, c :: l => by
    have ih := fun acc => unescapeChars_escape acc l
    by_cases h₁ : c = '\\'
    · subst h₁; simp [escapeChar, unescapeChars, ih]
    · by_cases h₂ : c = '\n'
      · subst h₂; simp [escapeChar, unescapeChars, ih]
      · rw [List.flatMap_cons, escapeChar_other h₁ h₂, List.singleton_append, unescapeChars_cons_other h₁, ih]
        simp

theorem newline_not_mem_escape (l : List Char) : '\n' ∉ l.flatMap escapeChar := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro c _
  unfold escapeChar
  split <;> simp_all [eq_comm]

@[simp] theorem unescapeLine_escapeLine (s : String) : unescapeLine (escapeLine s) = s := by
  simp [unescapeLine, escapeLine, unescapeChars_escape]

theorem newline_not_mem_escapeLine (s : String) : '\n' ∉ (escapeLine s).toList := by
  simpa [escapeLine] using newline_not_mem_escape s.toList

/-! ## Prefixes, numbers and lines -/

theorem afterPrefix_go : (p s : List Char) → afterPrefix?.go p (p ++ s) = some (String.ofList s)
  | [], _ => rfl
  | c :: p, s => by simp [afterPrefix?.go, afterPrefix_go p s]

@[simp] theorem afterPrefix_append (p s : String) : afterPrefix? p (p ++ s) = some s := by
  simp [afterPrefix?, afterPrefix_go]

@[simp] theorem toNat_toString (n : Nat) : (toString n).toNat? = some n :=
  Nat.toNat?_repr n

@[simp] theorem toString_string (s : String) : toString s = s := rfl

theorem newline_not_mem_toString (n : Nat) : '\n' ∉ (toString n).toList := by
  intro h
  have : Char.isDigit '\n' := by
    simp only [toString, Nat.toList_repr] at h
    exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) h
  simp at this

theorem splitOn_lines : (ls : List (List Char)) → (∀ l ∈ ls, '\n' ∉ l) →
    (ls.flatMap (· ++ ['\n'])).splitOn '\n' = ls ++ [[]]
  | [], _ => rfl
  | l :: ls, h => by
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append,
      List.splitOn_append_cons_of_forall_mem_beq_eq_false
        (fun x m => by simp only [beq_eq_false_iff_ne]; rintro rfl; exact h l (by simp) m) _ (by simp),
      splitOn_lines ls (fun l' m => h l' (by simp [m]))]
    rfl

theorem toList_joinLines (ls : List String) :
    (joinLines ls).toList = (ls.map String.toList).flatMap (· ++ ['\n']) := by
  simp [joinLines, String.toList_join, List.flatMap_map]

theorem textLines_joinLines (ls : List String) (h : ∀ l ∈ ls, '\n' ∉ l.toList) :
    textLines (joinLines ls) = ls ++ [""] := by
  rw [textLines, toList_joinLines, splitOn_lines _ (by simpa using h)]
  simp [List.map_map, Function.comp_def]

/-! ## Names and keys -/

theorem textParts_eq_some {ps : List NamePart} {ts : List String} :
    textParts? ps = some ts ↔ ps = ts.map .str := by
  induction ps generalizing ts with
  | nil => cases ts <;> simp [textParts?]
  | cons p ps ih =>
    cases p with
    | num => cases ts <;> simp [textParts?]
    | str s =>
      cases ts with
      | nil => simp [textParts?]
      | cons t ts => simp only [textParts?, Option.map_eq_some_iff, ih, List.map_cons, List.cons.injEq,
          NamePart.str.injEq]; constructor
                     · rintro ⟨_, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
                     · rintro ⟨rfl, rfl⟩; exact ⟨_, rfl, rfl, rfl⟩

theorem namePartsOf_foldl (ps : List String) (n : Lean.Name) :
    namePartsOf (ps.foldl Lean.Name.mkStr n) = namePartsOf n ++ ps.map .str := by
  induction ps generalizing n with
  | nil => simp
  | cons p ps ih => simp [ih, namePartsOf, Lean.Name.mkStr]

theorem namePartsOf_nameOfParts (ps : List String) : namePartsOf (nameOfParts ps) = ps.map .str := by
  simp [nameOfParts, namePartsOf_foldl, namePartsOf]

theorem namePartsOf_inj : {a b : Lean.Name} → namePartsOf a = namePartsOf b → a = b
  | .anonymous, .anonymous, _ => rfl
  | .anonymous, .str _ _, h | .anonymous, .num _ _, h => by simp [namePartsOf] at h
  | .str _ _, .anonymous, h | .num _ _, .anonymous, h => by simp [namePartsOf] at h
  | .str p s, .str q t, h | .num p s, .num q t, h | .str p s, .num q t, h | .num p s, .str q t, h => by
    simp only [namePartsOf] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    simp at h₂
    all_goals simp_all [namePartsOf_inj h₁]

theorem nameOfParts_nameParts {n : Lean.Name} {ps : List String} (h : nameParts? n = some ps) :
    nameOfParts ps = n := by
  simp only [nameParts?, textParts_eq_some] at h
  exact namePartsOf_inj (by rw [namePartsOf_nameOfParts, h])

theorem partsOfLines_partsLines (ps rest : List String) :
    partsOfLines? (partsLines ps ++ rest) = some (ps, rest) := by
  simp [partsLines, partsOfLines?, List.map_map, Function.comp_def, guard]

theorem nameOfLines_nameLines {n : Lean.Name} {ls : List String} (h : nameLines? n = some ls) (rest : List String) :
    nameOfLines? (ls ++ rest) = some (n, rest) := by
  simp only [nameLines?, Option.map_eq_some_iff] at h
  obtain ⟨ps, hps, rfl⟩ := h
  simp [nameOfLines?, partsOfLines_partsLines, nameOfParts_nameParts hps]

theorem keyObservation_read (o : KeyObservation) (rest : List String) :
    KeyObservation.read? (o.lines ++ rest) = some (o, rest) := by
  rcases o with ⟨name, formula, _ | g⟩ <;>
    simp [KeyObservation.lines, KeyObservation.read?, partsOfLines_partsLines, List.append_assoc]

theorem readObservations_lines (os : List KeyObservation) (rest : List String) :
    readObservations? os.length (os.flatMap (·.lines) ++ rest) = some (os, rest) := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [readObservations?, List.append_assoc, keyObservation_read, ih]

theorem cacheKey_read (k : CacheKey) (rest : List String) :
    CacheKey.read? (k.lineList ++ rest) = some (k, rest) := by
  simp [CacheKey.lineList, CacheKey.read?, readObservations_lines]

theorem mapM_eq_some_map {f : α → Option β} : {l : List α} → {m : List β} →
    l.mapM f = some m ↔ l.map f = m.map some
  | [], [] => by simp
  | [], _ :: _ => by simp
  | a :: l, [] => by simp [List.mapM_cons, Option.bind_eq_some_iff]
  | a :: l, b :: m => by
    simp [List.mapM_cons, Option.bind_eq_some_iff, ← mapM_eq_some_map (l := l) (m := m)]

theorem mapM_eq_some_iff {f : α → Option β} {l : List α} {m : List β} :
    l.mapM f = some m ↔
      (l.length = m.length ∧ ∀ n (h₁ : n < l.length) (h₂ : n < m.length), f l[n] = some m[n]) := by
  rw [mapM_eq_some_map, List.ext_getElem_iff]
  simp

theorem mapM_some_mem {f : α → Option β} {l : List α} {m : List β} (h : l.mapM f = some m) :
    ∀ a ∈ l, ∃ b, f a = some b := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨hlen, h⟩ := mapM_eq_some_iff.mp h
  exact ⟨_, h n hn (hlen ▸ hn)⟩

theorem mapM_eq_none_iff {f : α → Option β} : {l : List α} → l.mapM f = none ↔ ∃ a ∈ l, f a = none
  | [] => by simp
  | a :: l => by
    have ih := @mapM_eq_none_iff _ _ f l
    simp only [List.mapM_cons, List.mem_cons, exists_eq_or_imp]
    cases ha : f a <;> cases hl : l.mapM f <;> simp_all

theorem textParts_isSome {ps : List NamePart} :
    (textParts? ps).isSome ↔ ∀ p ∈ ps, ∃ s, p = .str s := by
  induction ps with
  | nil => simp [textParts?]
  | cons p ps ih => cases p <;> simp [textParts?, ih]

theorem ofParts_eq_some {name : List NamePart} {formula : String} {guard? : Option (List NamePart)}
    {o : KeyObservation} :
    KeyObservation.ofParts? name formula guard? = some o ↔
      name = o.name.map .str ∧ o.formula = formula ∧ match guard?, o.guard? with
        | none, none => True
        | some g, some h => g = h.map .str
        | _, _ => False := by
  rcases o with ⟨oname, oformula, oguard⟩
  cases guard? <;> cases oguard <;>
    simp [KeyObservation.ofParts?, Option.bind_eq_some_iff, textParts_eq_some] <;> grind

theorem ofParts_isSome {name : List NamePart} {formula : String} {guard? : Option (List NamePart)} :
    (KeyObservation.ofParts? name formula guard?).isSome ↔
      (textParts? name).isSome ∧ ∀ g, guard? = some g → (textParts? g).isSome := by
  cases guard? <;> simp only [KeyObservation.ofParts?] <;>
    cases textParts? name <;> simp <;> cases textParts? _ <;> simp

/-! ## Entries -/

/-- Lines without a line break. -/
def NoBreaks (ls : List String) : Prop := ∀ l ∈ ls, '\n' ∉ l.toList

theorem noBreaks_append {a b : List String} (ha : NoBreaks a) (hb : NoBreaks b) : NoBreaks (a ++ b) := by
  intro l h
  rcases List.mem_append.mp h with h | h
  · exact ha l h
  · exact hb l h

theorem noBreaks_cons {s : String} {b : List String} (hs : '\n' ∉ s.toList) (hb : NoBreaks b) :
    NoBreaks (s :: b) := by
  intro l h
  rcases List.mem_cons.mp h with rfl | h
  · exact hs
  · exact hb l h

theorem noBreaks_nil : NoBreaks [] := by intro l h; simp at h

theorem noBreaks_partsLines (ps : List String) : NoBreaks (partsLines ps) := by
  simp only [partsLines]
  refine noBreaks_cons (newline_not_mem_toString _) ?_
  intro l h; obtain ⟨p, _, rfl⟩ := List.mem_map.mp h; exact newline_not_mem_escapeLine _

theorem noBreaks_observation (o : KeyObservation) : NoBreaks o.lines := by
  rcases o with ⟨name, formula, _ | g⟩ <;> simp only [KeyObservation.lines] <;>
    refine noBreaks_append (noBreaks_append (noBreaks_partsLines _)
      (noBreaks_cons (newline_not_mem_escapeLine _) noBreaks_nil)) ?_
  · exact noBreaks_cons (by decide) noBreaks_nil
  · exact noBreaks_cons (by decide) (noBreaks_partsLines _)

theorem newline_not_mem_append {a b : String} (ha : '\n' ∉ a.toList) (hb : '\n' ∉ b.toList) :
    '\n' ∉ (a ++ b).toList := by
  simp only [String.toList_append, List.mem_append, not_or]; exact ⟨ha, hb⟩

theorem noBreaks_lineList (k : CacheKey) : NoBreaks k.lineList := by
  simp only [CacheKey.lineList]
  refine noBreaks_append ?_ ?_
  · refine noBreaks_cons ?_ (noBreaks_cons ?_ (noBreaks_cons (newline_not_mem_escapeLine _)
      (noBreaks_cons (newline_not_mem_toString _) noBreaks_nil)))
    · exact newline_not_mem_append (by decide) (newline_not_mem_toString _)
    · exact newline_not_mem_append (by decide) (newline_not_mem_escapeLine _)
  · intro l h
    obtain ⟨o, _, h⟩ := List.mem_flatMap.mp h
    exact noBreaks_observation o l h

theorem bindingLines_eq {b : Lean.Name × String} {ls : List String} (h : bindingLines? b = some ls) :
    ∃ ps, nameParts? b.1 = some ps ∧ ls = partsLines ps ++ [escapeLine b.2] := by
  simp only [bindingLines?, nameLines?, Option.map_map, Option.map_eq_some_iff, Function.comp_def] at h
  obtain ⟨ps, hps, rfl⟩ := h
  exact ⟨ps, hps, rfl⟩

theorem noBreaks_model : {bs : List (Lean.Name × String)} → {lss : List (List String)} →
    bs.mapM bindingLines? = some lss → NoBreaks lss.flatten
  | [], lss, h => by simp at h; subst h; exact noBreaks_nil
  | b :: bs, lss, h => by
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨ls, hb, lss', hrest, rfl⟩ := h
    obtain ⟨ps, _, rfl⟩ := bindingLines_eq hb
    rw [List.flatten_cons]
    exact noBreaks_append (noBreaks_append (noBreaks_partsLines _)
      (noBreaks_cons (newline_not_mem_escapeLine _) noBreaks_nil)) (noBreaks_model hrest)

theorem modelOfLinesFuel_succ (f : Nat) {ls : List String} (hne : ls ≠ []) :
    modelOfLinesFuel? (f + 1) ls = (do
      let (n, rest) ← nameOfLines? ls
      let v :: rest := rest | none
      return (n, unescapeLine v) :: (← modelOfLinesFuel? f rest)) := by
  cases ls with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem modelOfLinesFuel_flatten : (bs : List (Lean.Name × String)) → (lss : List (List String)) →
    bs.mapM bindingLines? = some lss → (fuel : Nat) → lss.flatten.length ≤ fuel →
    modelOfLinesFuel? fuel lss.flatten = some bs
  | [], lss, h, fuel, _ => by
    simp at h; subst h; cases fuel <;> rfl
  | b :: bs, lss, h, fuel, hf => by
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨ls, hb, lss', hrest, rfl⟩ := h
    obtain ⟨ps, hps, rfl⟩ := bindingLines_eq hb
    have hn : nameLines? b.1 = some (partsLines ps) := by simp [nameLines?, hps]
    rw [List.flatten_cons, List.append_assoc, List.singleton_append] at hf ⊢
    cases fuel with
    | zero => simp [partsLines] at hf
    | succ f =>
      rw [modelOfLinesFuel_succ f (by simp [partsLines]), nameOfLines_nameLines hn]
      simp only [List.length_append, List.length_cons] at hf
      simp [modelOfLinesFuel_flatten bs lss' hrest f (by simp [partsLines] at hf ⊢; omega)]

/-- What an entry of the answer `o`, with whether it has a model, reads
back as: `unsat` keeps no model, and `sat` keeps one only if it has one. -/
def readBack : Outcome String → Bool → Outcome String × Bool
  | .unsat, _ => (.unsat, true)
  | .sat _, false => (.sat #[], false)
  | .sat m, true => (.sat m, true)
  | .unknown r, h => (.unknown r, h)

theorem decode_joinLines (k : CacheKey) (body : List String) (hb : NoBreaks body) :
    decodeEntry? (joinLines (k.lineList ++ body)) = (match body ++ [""] with
      | ["unsat", ""] => some (k, .unsat, true)
      | ["sat", ""] => some (k, .sat #[], false)
      | "sat model" :: rest => (modelOfLines? rest.dropLast).bind fun m => some (k, .sat m, true)
      | _ => none) := by
  rw [decodeEntry?, textLines_joinLines _ (noBreaks_append (noBreaks_lineList k) hb), List.append_assoc,
    cacheKey_read]
  split <;> simp_all

/-- `decodeEntry?` inverts `encodeEntry?`. -/
theorem decode_encode {k : CacheKey} {o : Outcome String} {h : Bool} {text : String}
    (he : encodeEntry? k o h = some text) : decodeEntry? text = some (k, readBack o h) := by
  simp only [encodeEntry?, Option.map_eq_some_iff] at he
  obtain ⟨L, hL, rfl⟩ := he
  cases o with
  | unsat =>
    simp [entryLines?] at hL; subst hL
    rw [decode_joinLines _ _ (noBreaks_cons (by decide) noBreaks_nil)]; rfl
  | unknown r => simp [entryLines?] at hL
  | sat m =>
    cases h with
    | false =>
      simp [entryLines?] at hL; subst hL
      rw [decode_joinLines _ _ (noBreaks_cons (by decide) noBreaks_nil)]; rfl
    | true =>
      simp [entryLines?, Option.bind_eq_some_iff] at hL
      obtain ⟨lss, hm, rfl⟩ := hL
      rw [decode_joinLines _ _ (noBreaks_cons (by decide) (noBreaks_model hm))]
      simp only [List.cons_append, List.dropLast_concat, modelOfLines?,
        modelOfLinesFuel_flatten _ _ hm _ (Nat.le_refl _)]
      simp [readBack]

end Fren.Impls.QueryCache
