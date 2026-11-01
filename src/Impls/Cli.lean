-- keep-sorted start
import FrenCli.Color
import FrenCli.Exit
import FrenCli.QueryStore
import FrenCli.SeqElems
import Impls.QueryCache
import Impls.View
import Reqs.Cli
-- keep-sorted end
open Fren.Lang

/-! # The binary's exit code (`Reqs/Cli`) -/

namespace Fren.Impls

open Fren.Core (Severity worst)

impl exit_code: cli::exit for (ran : Bool) (s : Option Severity) {
  ran? := ran,
  worst := toLevel s,
  code := (FrenCli.exitCode ran s).toNat,
} by
  intro ran s _
  cases ran <;> rcases s with _ | _ | _ | _ <;> decide

-- The binary's exit code follows the convention its commands share.
impl exit_status_code: cli::exit_status for (ran : Bool) (s : Option Severity) {
  ran? := ran,
  code := (FrenCli.exitCode ran s).toNat,
} by
  intro ran s _
  cases ran <;> rcases s with _ | _ | _ | _ <;> decide

def toColorChoice : FrenCli.ColorChoice → cli.ColorChoice
  | .auto => .Auto
  | .always => .Always
  | .never => .Never

impl color: cli::color for (c : FrenCli.ColorChoice) (tty noColor dumb : Bool) {
  choice := toColorChoice c,
  tty? := tty,
  no_color? := noColor,
  dumb? := dumb,
  colored? := FrenCli.useColor c tty noColor dumb,
} by
  intro c tty noColor dumb _
  cases c <;> cases tty <;> cases noColor <;> cases dumb <;> decide

instance : LawfulBEq Severity where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

/-- The levels of the severities `ss`, as the spec sees a run. -/
def levels (ss : Array Severity) : Fren.FinSet view.Severity := Fren.FinSet.ofArray (ss.map (toLevel ∘ some))

/-- A level is present exactly when a severity of it is. -/
theorem mem_levels (ss : Array Severity) (s : Severity) : toLevel (some s) ∈ levels ss ↔ s ∈ ss := by
  simp only [levels, Fren.FinSet.mem_ofArray, Array.mem_map, Function.comp]
  constructor
  · rintro ⟨t, ht, e⟩
    have : t = s := by cases t <;> cases s <;> simp_all [toLevel]
    exact this ▸ ht
  · exact fun h => ⟨s, h, rfl⟩

theorem silent_not_mem (ss : Array Severity) : view.Severity.Silent ∉ levels ss := by
  simp only [levels, Fren.FinSet.mem_ofArray, Array.mem_map, Function.comp, not_exists, not_and]
  intro t _; cases t <;> simp [toLevel]

-- Over arrays, so `decide` does not apply: a proof.
impl worst_of: cli::worst_severity for (ss : Array Severity) {
  present := levels ss,
  worst := toLevel (worst ss),
} by
  intro ss _
  have he := mem_levels ss .error
  have hw := mem_levels ss .warning
  simp only [toLevel] at he hw
  have ae (s : Severity) : (ss.any fun x => x == s) = true ↔ s ∈ ss := by simp [Array.mem_iff_getElem]
  have an (s : Severity) (h : s ∉ ss) : (ss.any fun x => x == s) = false := by
    simpa using mt (ae s).mp h
  by_cases e : view.Severity.Error ∈ levels ss
  · simp [fren_spec, e, worst, (ae _).mpr (he.mp e), toLevel]
  · by_cases w : view.Severity.Warning ∈ levels ss
    · simp [fren_spec, e, w, worst, an _ (mt he.mpr e), (ae _).mpr (hw.mp w), toLevel]
    · simp [fren_spec, e, w, worst, an _ (mt he.mpr e), an _ (mt hw.mpr w), toLevel]

-- A whole run, from the impls of its instances: the instances' variables
-- are given by the code, and their obligations by the theorems above.
impl run: cli::run for (ran : Bool) (ss : Array Severity) {
  ran? := ran,
  present := levels ss,
  code := (FrenCli.exitCode ran (worst ss)).toNat,
} by
  intro ran ss _
  exact ⟨_, toLevel (worst ss), ran, _, _, rfl,
    ⟨rfl, trivial, worst_of ss trivial⟩, ⟨⟨rfl, rfl⟩, trivial, exit_code ran (worst ss) trivial⟩⟩

def toLogic (s : String) : cli.Logic :=
  if s == "ALL" then .All else if s == "HO_ALL" then .HigherOrder else if s == "UFDTLIA" then .Quantified
  else .QuantifierFree

/-- The theories that a spec using strings, sets and sequences needs. -/
def theories (strings sets seqs : Bool) : Fren.FinSet cli.Theory :=
  (if strings then {.Strings} else ∅) ∪ (if sets then {.Sets} else ∅) ∪ (if seqs then {.Sequences} else ∅)

-- With the logic and options that the `fren` command sets.
-- The `fren` command gives sequences the options of strings and of sets.
impl logic: cli::logic for (k : Fren.Core.CheckKind) (strings sets seqs proj q : Bool) {
  kind := toCheckKind k,
  theories := theories strings sets seqs,
  projection? := proj,
  quantified? := q,
  logic := toLogic (Fren.Core.logic k (strings || sets || seqs) proj q),
  strings_exp? := ["strings-exp", "re-inter-mode", "re-elim"].all fun o =>
    (Fren.Core.solverOptions (strings || seqs) (sets || seqs)).any (·.1 == o),
  sets_exp? := (Fren.Core.solverOptions (strings || seqs) (sets || seqs)).any (·.1 == "sets-exp"),
  last_call? := (Fren.Core.quantifierOptions (Fren.Core.logic k (strings || sets || seqs) proj q)).contains
    ("inst-when", "last-call"),
}

-- `fren check` asks a query in the logic of its check, given whether the
-- script it would ask has a quantifier (`Fren.Core.hasQuantifier`). This
-- binds the decision only: that `runQuery` asks it of each script is backed
-- by the ui tests, not proved.
impl query_logic: cli::query_logic for (k : Fren.Core.CheckKind) (ext proj q quantifies : Bool) {
  logic := toLogic (Fren.Core.logic k ext proj q),
  quantifies? := quantifies,
  asked? := Fren.Core.queryAsked (Fren.Core.logic k ext proj q) quantifies,
  internal? := !Fren.Core.queryAsked (Fren.Core.logic k ext proj q) quantifies,
}

/-- An observation of a key, as the spec sees it. -/
def toObservation (o : FrenCli.KeyObservation) : cli.Observation :=
  { name := o.name, formula := o.formula, guard := o.guard? }

/-- A key of the query cache, as the spec sees it. -/
def toCacheKey (k : FrenCli.CacheKey) : cli.Key :=
  { script := k.script, observations := k.observations.map toObservation, solver := k.solver, version := k.version }

theorem toObservation_inj {a b : FrenCli.KeyObservation} (h : toObservation a = toObservation b) : a = b := by
  cases a; cases b
  simp only [toObservation] at h
  injection h with h1 h2 h3
  subst h1 h2 h3; rfl

theorem map_toObservation_inj : {as bs : List FrenCli.KeyObservation} →
    as.map toObservation = bs.map toObservation → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [toObservation_inj h.1, map_toObservation_inj h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- A component of a name, as the spec sees it. -/
def toNamePart : FrenCli.NamePart → cli.NamePart
  | .str s => .Text s
  | .num n => .Number n

/-- The components of a name, as the spec sees them. -/
def toNameParts (n : Lean.Name) : Fren.Seq cli.NamePart :=
  Fren.Seq.ofList ((FrenCli.namePartsOf n).map toNamePart)

/-- An observation of a query's model, as the spec sees it. -/
def toObserved (o : FrenCli.ModelObservation) : cli.Observed :=
  { name := toNameParts o.key, formula := o.formula, guard := o.guard?.map toNameParts }

theorem nth_map_text (ts : List String) (j : Int) (h : 0 ≤ j ∧ j < ts.length) :
    (Fren.Seq.ofList (ts.map (toNamePart ∘ FrenCli.NamePart.str))).nth j = .Text (ts[j.toNat]'(by omega)) := by
  rw [Fren.Seq.nth_of_lt _ _ h.1 (by simpa using h.2)]
  simp [toNamePart]

theorem holds_of {o : FrenCli.ModelObservation} {ko : FrenCli.KeyObservation}
    (h : FrenCli.KeyObservation.of? o = some ko) : cli.«holds?» (toObserved o) (toObservation ko) = true := by
  rcases o with ⟨key, formula, guard?⟩
  rcases ko with ⟨kname, kformula, kguard?⟩
  simp only [FrenCli.KeyObservation.of?, QueryCache.ofParts_eq_some] at h
  obtain ⟨hname, rfl, hguard⟩ := h
  cases guard? <;> cases kguard? <;> simp at hguard <;>
    simp_all +contextual [fren_spec, toObserved, toObservation, toNameParts, Fren.Seq.toList, nth_map_text]
  all_goals rfl

theorem observed_text_of {o : FrenCli.ModelObservation} :
    cli.«observed_text?» (toObserved o) = true ↔ (FrenCli.KeyObservation.of? o).isSome := by
  rcases o with ⟨key, formula, _ | g⟩ <;>
    simp [fren_spec, toObserved, FrenCli.KeyObservation.of?, QueryCache.ofParts_isSome] <;>
    simp only [toNameParts, Fren.Seq.toList_ofList, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, QueryCache.textParts_isSome]
  · exact forall₂_congr fun a _ => by cases a <;> simp [toNamePart]
  · exact and_congr (forall₂_congr fun a _ => by cases a <;> simp [toNamePart])
      (forall₂_congr fun a _ => by cases a <;> simp [toNamePart])

-- A query's key (`FrenCli.QueryStore.key?`), from its script and the
-- observations of its model, as the check names them.
impl query_key: cli::query_key for (script : String) (os : List FrenCli.ModelObservation) (solver : String) {
  script := script,
  observed := Fren.Seq.ofList (os.map toObserved),
  observations := Fren.Seq.ofList
    ((((FrenCli.CacheKey.ofObservations? script os solver).map (·.observations)).getD []).map toObservation),
  solver := solver,
  version := FrenCli.queryCacheVersion,
  «kept?» := (FrenCli.CacheKey.ofObservations? script os solver).isSome,
  «spelled?» := (FrenCli.CacheKey.ofObservations? script os solver).isSome,
  key := toCacheKey ((FrenCli.CacheKey.ofObservations? script os solver).getD (FrenCli.CacheKey.of script [] solver)),
} by
  intro script os solver _
  have hof : FrenCli.CacheKey.ofObservations? script os solver =
      (os.mapM FrenCli.KeyObservation.of?).map (FrenCli.CacheKey.of script · solver) := by
    simp only [FrenCli.CacheKey.ofObservations?]
    cases os.mapM FrenCli.KeyObservation.of? <;> rfl
  simp only [fren_spec, hof, decide_eq_true_eq, Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map,
    Fren.Seq.len_eq, List.length_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rcases hm : os.mapM FrenCli.KeyObservation.of? with _ | kos
  · obtain ⟨o, ho, hno⟩ := QueryCache.mapM_eq_none_iff.mp hm
    have hne : os.length ≠ 0 := by intro h; simp [List.length_eq_zero_iff.mp h] at ho
    have ht := (not_congr (observed_text_of (o := o))).mpr (by simp [hno])
    refine ⟨by simp [toCacheKey, FrenCli.CacheKey.of, Fren.Seq.ofList], ?_, ?_⟩
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro hall
      have := hall o ho
      apply ht
      simp only [fren_spec, decide_eq_true_eq, Fren.Seq.mem_iff] at this ⊢
      exact this
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro h
      exact hne (by simpa using h.1.symm)
  · obtain ⟨hlen, hidx⟩ := QueryCache.mapM_eq_some_iff.mp hm
    refine ⟨by simp [toCacheKey, FrenCli.CacheKey.of, Fren.Seq.ofList], ?_, ?_⟩
    · simp only [Option.map_some, Option.isSome_some, true_iff]
      intro a ha
      obtain ⟨ko, hko⟩ := QueryCache.mapM_some_mem hm a ha
      have := (observed_text_of (o := a)).mpr (by simp [hko])
      simpa only [fren_spec, decide_eq_true_eq, Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map, Fren.Seq.len_eq,
        List.length_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using this
    · simp only [Option.map_some, Option.isSome_some, Option.getD_some, true_iff]
      refine ⟨by simp [FrenCli.CacheKey.of, hlen], fun i h₀ hi => ?_⟩
      have hn : i.toNat < os.length := by omega
      have e₁ : (Fren.Seq.ofList (os.map toObserved)).nth i = toObserved os[i.toNat] := by
        rw [Fren.Seq.nth_of_lt _ _ h₀ (by simpa using hi)]; simp
      have e₂ : (Fren.Seq.ofList ((FrenCli.CacheKey.of script kos solver).observations.map toObservation)).nth i =
          toObservation (kos[i.toNat]'(by omega)) := by
        rw [Fren.Seq.nth_of_lt _ _ h₀ (by simp [FrenCli.CacheKey.of]; omega)]; simp [FrenCli.CacheKey.of]
      have H : cli.«holds?» ((Fren.Seq.ofList (os.map toObserved)).nth i)
          ((Fren.Seq.ofList ((FrenCli.CacheKey.of script kos solver).observations.map toObservation)).nth i) =
            true := by
        rw [e₁, e₂]; exact holds_of (hidx i.toNat hn (by omega))
      simp only [fren_spec, decide_eq_true_eq, Fren.Seq.len_eq, and_imp] at H
      exact H

/-- An answer, as the spec sees it. -/
def toCachedAnswer : FrenCli.CachedAnswer → cli.Answer
  | .unsat => .Unsat
  | .sat false => .Sat
  | .sat true => .SatWithModel
  | .unknown => .Unknown

/-- A binding of a model, as the spec sees it. -/
def toModelBinding (b : Lean.Name × String) : cli.Binding :=
  { name := toNameParts b.1, value := b.2 }

/-- An entry of the key `k`, the answer `o` and whether it has a model, as
the spec sees it: only a `sat` answer with a model has one. -/
def toEntry (k : FrenCli.CacheKey) (o : Fren.Core.Outcome String) (h : Bool) : cli.Entry :=
  { key := toCacheKey k, answer := toCachedAnswer (FrenCli.CachedAnswer.of o h),
    model := match o, h with
      | .sat m, true => Fren.Seq.ofList (m.toList.map toModelBinding)
      | _, _ => Fren.Seq.ofList [] }

theorem toEntry_readBack (k : FrenCli.CacheKey) (o : Fren.Core.Outcome String) (h : Bool) :
    toEntry k (QueryCache.readBack o h).1 (QueryCache.readBack o h).2 = toEntry k o h := by
  cases o <;> cases h <;> rfl

-- Which entries `--query-cache` writes (`FrenCli.encodeEntry?`), and what
-- it reads them back as (`FrenCli.decodeEntry?`).
impl query_entry: cli::query_entry for (k : FrenCli.CacheKey) (o : Fren.Core.Outcome String) (h : Bool) {
  written := toEntry k o h,
  «text?» := (FrenCli.encodeEntry? k o h).isSome,
  read := ((FrenCli.encodeEntry? k o h).bind FrenCli.decodeEntry?).map fun (k, o, h) => toEntry k o h,
} by
  intro k o h _
  simp only [fren_spec]
  refine ⟨?_, ?_⟩
  · rcases he : FrenCli.encodeEntry? k o h with _ | text
    · rfl
    · simp [QueryCache.decode_encode he, toEntry_readBack]
  · cases o with
    | unsat => cases h <;> simp [FrenCli.encodeEntry?, FrenCli.entryLines?, toEntry, FrenCli.CachedAnswer.of,
        toCachedAnswer, Fren.Seq.toList, Fren.Seq.ofList, Fren.Seq.mem_iff]
    | unknown r => simp [FrenCli.encodeEntry?, FrenCli.entryLines?, toEntry, FrenCli.CachedAnswer.of, toCachedAnswer]
    | sat m =>
      cases h
      · simp [FrenCli.encodeEntry?, FrenCli.entryLines?, toEntry, FrenCli.CachedAnswer.of, toCachedAnswer,
          Fren.Seq.toList, Fren.Seq.ofList, Fren.Seq.mem_iff]
      · simp [FrenCli.encodeEntry?, FrenCli.entryLines?, toEntry, FrenCli.CachedAnswer.of, toCachedAnswer]
        have hb : ∀ (o : Option (List (List String))), (o.bind (Option.map FrenCli.joinLines ∘
            fun lines => some (k.lineList ++ "sat model" :: lines.flatten))).isSome = o.isSome := by
          intro o; cases o <;> rfl
        have key : ∀ x : Lean.Name,
            (FrenCli.nameParts? x).isSome ↔ ∀ p ∈ (toNameParts x).toList, ∃ s, p = cli.NamePart.Text s := by
          intro x
          simp only [FrenCli.nameParts?, QueryCache.textParts_isSome, toNameParts, Fren.Seq.toList_ofList,
            List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          exact forall₂_congr fun a _ => by cases a <;> simp [toNamePart]
        rw [hb]
        constructor
        · intro hs b x v hxv hb p hp
          subst hb
          obtain ⟨lss, hl⟩ := Option.isSome_iff_exists.mp hs
          obtain ⟨ls, hls⟩ := QueryCache.mapM_some_mem hl (x, v) (by simpa using hxv)
          obtain ⟨ps, hps, _⟩ := QueryCache.bindingLines_eq hls
          obtain ⟨s, rfl⟩ := (key x).mp (by simp [hps]) p hp
          rfl
        · intro hall
          rw [Option.isSome_iff_ne_none, Ne, QueryCache.mapM_eq_none_iff]
          rintro ⟨⟨x, v⟩, hxv, hnone⟩
          have hx : (FrenCli.nameParts? x).isSome := (key x).mpr fun p hp => by
            have := hall _ x v (by simpa using hxv) rfl p hp
            cases p <;> simp_all
          simp [FrenCli.bindingLines?, FrenCli.nameLines?] at hnone
          simp [hnone] at hx

-- When an entry of `--query-cache` answers a query (`FrenCli.lookupEntry?`).
impl query_cache_hit: cli::query_cache for (asked stored : FrenCli.CacheKey) (found wantModel : Bool)
    (a : FrenCli.CachedAnswer) {
  asked := toCacheKey asked,
  want_model? := wantModel,
  found? := found,
  stored := toCacheKey stored,
  answer := toCachedAnswer a,
  hit? := FrenCli.cacheHit found asked stored a wantModel,
} by
  intro asked stored found wantModel a _
  have key : toCacheKey stored = toCacheKey asked ↔ asked = stored := by
    constructor
    · intro h
      cases asked; cases stored
      simp only [toCacheKey] at h
      injection h with h1 h2 h3 h4
      have : _ := Int.ofNat.inj h4
      subst h1 h3 this
      rw [map_toObservation_inj h2]
    · intro h; rw [h]
  rcases a with _ | (_ | _) | _ <;> cases found <;> cases wantModel <;>
    simp_all [fren_spec, FrenCli.cacheHit, FrenCli.CachedAnswer.answers, toCachedAnswer]

-- Which answers `--query-cache` keeps (`FrenCli.QueryStore.record`).
impl kept_answer: cli::kept_answer for (a : FrenCli.CachedAnswer) {
  answer := toCachedAnswer a,
  kept? := a.stored,
} by
  intro a _
  rcases a with _ | (_ | _) | _ <;> decide

-- When a fresh answer contradicts one of `--verify-query-cache`'s
-- (`FrenCli.QueryStore.record`).
impl contradicts: cli::contradicts for (fresh kept : FrenCli.CachedAnswer) (same : Bool) {
  fresh := toCachedAnswer fresh,
  kept := toCachedAnswer kept,
  same_model? := same,
  contradiction? := FrenCli.contradicts fresh kept same,
} by
  intro fresh kept same _
  rcases fresh with _ | (_ | _) | _ <;> rcases kept with _ | (_ | _) | _ <;> cases same <;> decide

end Fren.Impls

namespace Fren.Impls
impl substitution_scope: cli::substitution_scope for (bound mentioned : Bool) {
  name := { bound_here? := bound, mentioned_in_replacement? := mentioned },
  replace? := (FrenCli.SeqElems.substitutionScope bound mentioned).1,
  rename? := (FrenCli.SeqElems.substitutionScope bound mentioned).2,
} by
  intro bound mentioned _
  cases bound <;> cases mentioned <;> simp [fren_spec, FrenCli.SeqElems.substitutionScope]
end Fren.Impls
