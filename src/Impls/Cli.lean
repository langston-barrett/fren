-- keep-sorted start
import FrenCli.Color
import FrenCli.Exit
import FrenCli.QueryStore
import FrenCli.SeqElems
import FrenCore.Symbols
import Impls.QueryCache
import Impls.View
import Reqs.Cli
import Std.Data.String.ToNat
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

namespace Fren.Impls

/-- A model goal, its heads as `cli::goal_introduction` names them, read as
the front ends read theirs (`Fren.Core.GoalHead`): past its last head,
the rest is `Other`. -/
def modelGoalHead : List cli.GoalHead → Id (Fren.Core.GoalHead Unit (List cli.GoalHead))
  | .Universal :: rest => pure (.universal () rest)
  | .Premise :: rest => pure (.premise [] rest)
  | .Definition :: rest => pure (.definition rest)
  | _ => pure .other

def toGoalHead : cli.GoalHead → Fren.Core.GoalHead Unit Unit
  | .Universal => .universal () ()
  | .Premise => .premise () ()
  | .Definition => .definition ()
  | .Other => .other

def toIntroducedUnit : Fren.Core.Introduced Unit Unit → cli.Introduced
  | .constant _ => .Constant
  | .hypothesis _ => .Hypothesis
  | .substituted => .Substituted

instance : Fren.Finite cli.GoalHead := ⟨[.Universal, .Premise, .Definition, .Other], by intro x; cases x <;> simp⟩

impl head_introduction: cli::head_introduction for (h : cli.GoalHead) {
  head := h,
  introduced := ((toGoalHead h).introduced?).map (toIntroducedUnit ·.1),
}

/-- Whether `h` can be introduced (`cli::introduced_as`). -/
def introducible : cli.GoalHead → Bool
  | .Other => false
  | _ => true

theorem introducible_iff (h : cli.GoalHead) :
    (match h with
      | cli.GoalHead.Universal => some cli.Introduced.Constant
      | cli.GoalHead.Premise => some cli.Introduced.Hypothesis
      | cli.GoalHead.Definition => some cli.Introduced.Substituted
      | cli.GoalHead.Other => none) ≠ none ↔ introducible h = true := by
  cases h <;> simp [introducible]

/-- `introduceGoal` introduces the heads in front that can be, with the
fuel for all of them. -/
theorem introducedCount_eq (hs : List cli.GoalHead) (fuel : Nat) (hf : hs.length ≤ fuel) :
    (Fren.Core.introduceGoal modelGoalHead hs fuel).run.steps.length = (hs.takeWhile introducible).length := by
  induction hs generalizing fuel with
  | nil => cases fuel <;> simp [Fren.Core.introduceGoal, modelGoalHead, Fren.Core.GoalHead.introduced?]
  | cons h t ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have e := ih f (by simp at hf; omega)
      cases h <;> simp_all [Fren.Core.introduceGoal, modelGoalHead, Fren.Core.GoalHead.introduced?, introducible,
        List.takeWhile]

/-- `n` is within the heads in front that `p` holds of. -/
theorem lt_takeWhile {α : Type} (p : α → Bool) (hs : List α) (n : Nat) :
    n < (hs.takeWhile p).length ↔ ∃ hn : n < hs.length, ∀ k (hk : k ≤ n), p (hs[k]'(by omega)) = true := by
  induction hs generalizing n with
  | nil => simp
  | cons h t ih =>
    by_cases ph : p h
    · cases n with
      | zero =>
        simp only [List.takeWhile, ph, List.length_cons]
        refine ⟨fun _ => ⟨by simp, fun k hk => ?_⟩, fun _ => by omega⟩
        obtain rfl : k = 0 := by omega
        simpa using ph
      | succ m =>
        simp only [List.takeWhile, ph, List.length_cons, Nat.add_lt_add_iff_right, ih]
        constructor
        · rintro ⟨hm, hk⟩
          refine ⟨by omega, fun k hk' => ?_⟩
          cases k with
          | zero => simpa using ph
          | succ k => simpa using hk k (by omega)
        · rintro ⟨hm, hk⟩
          exact ⟨by omega, fun k hk' => by simpa using hk (k + 1) (by omega)⟩
    · simp only [List.takeWhile, ph, List.length_nil, Nat.not_lt_zero, false_iff]
      rintro ⟨_, hk⟩
      simpa [ph] using hk 0 (by omega)

/-- How many of the heads `hs` `Fren.Core.introduceGoal` introduces. -/
def introducedCount (hs : List cli.GoalHead) : Nat :=
  (Fren.Core.introduceGoal modelGoalHead hs).run.steps.length

impl goal_introduction: cli::goal_introduction for (hs : List cli.GoalHead) (i : Int) {
  heads := Fren.Seq.ofList hs,
  i := i,
  introduced? := decide (0 ≤ i ∧ i < introducedCount hs),
} by
  intro hs i h
  simp only [fren_spec] at h ⊢
  have hl : hs.length ≤ Fren.Core.goalIntroductionLimit := by
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList] at h
    simp only [Fren.Core.goalIntroductionLimit]; omega
  simp only [introducedCount, introducedCount_eq hs _ hl, decide_eq_true_iff]
  constructor
  · rintro ⟨h0, hi⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    obtain ⟨hn, hk⟩ := (lt_takeWhile introducible hs n).mp (by omega)
    refine ⟨⟨h0, by simpa using hn⟩, fun j ⟨hj0, hji⟩ => ?_⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    rw [Fren.Seq.nth_of_lt _ _ hj0 (by simp; omega)]
    exact (introducible_iff _).mpr (by simpa using hk k (by omega))
  · rintro ⟨⟨h0, hi⟩, hj⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨h0, ?_⟩
    have : n < (hs.takeWhile introducible).length := by
      refine (lt_takeWhile introducible hs n).mpr ⟨by simpa using hi, fun k hk => ?_⟩
      have := hj k ⟨by omega, by omega⟩
      rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp at hi ⊢; omega)] at this
      simpa using (introducible_iff _).mp this
    omega

/-- Whether the query has the symbol `s`, when it has the bound name `x`
if `b`, and the candidates `x#goal{j}` of `ks`. -/
def takenOf (b : Bool) (ks : List Nat) (s : String) : Bool :=
  (b && s == "x") || ks.any fun j => Fren.Core.goalCandidate "x" j == s

/-- The candidates are distinct. -/
theorem goalCandidate_inj {base : String} {j k : Nat}
    (h : Fren.Core.goalCandidate base j = Fren.Core.goalCandidate base k) : j = k := by
  simp only [Fren.Core.goalCandidate, String.append_right_inj] at h
  exact Nat.repr_injective h

/-- No candidate is the bound name itself. -/
theorem goalCandidate_ne (k : Nat) : Fren.Core.goalCandidate "x" k ≠ "x" := by
  intro h
  have := congrArg String.length h
  simp only [Fren.Core.goalCandidate, String.length_append] at this
  rw [show "x".length = 1 from rfl, show "#goal".length = 5 from rfl] at this
  omega

theorem takenOf_candidate (b : Bool) (ks : List Nat) (j : Nat) :
    takenOf b ks (Fren.Core.goalCandidate "x" j) = ks.contains j := by
  have e : ∀ i, (Fren.Core.goalCandidate "x" i == Fren.Core.goalCandidate "x" j) = (i == j) := by
    intro i
    by_cases hij : i = j
    · simp [hij]
    · have : Fren.Core.goalCandidate "x" i ≠ Fren.Core.goalCandidate "x" j := fun h => hij (goalCandidate_inj h)
      exact (beq_eq_false_iff_ne.mpr this).trans (beq_eq_false_iff_ne.mpr hij).symm
  have hn : (Fren.Core.goalCandidate "x" j == "x") = false := by simp [goalCandidate_ne]
  simp only [takenOf, hn, Bool.and_false, Bool.false_or, e]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

/-- `firstFree` finds the first number from `start` that `free` holds of,
if one is within reach. -/
theorem firstFree_spec (free : Nat → Bool) (start fuel : Nat) (j : Nat) (hj : start ≤ j) (hjf : j < start + fuel)
    (fj : free j = true) :
    let r := Fren.Core.firstFree free start fuel
    free r = true ∧ start ≤ r ∧ ∀ i, start ≤ i → i < r → free i = false := by
  induction fuel generalizing start with
  | zero => omega
  | succ f ih =>
    simp only [Fren.Core.firstFree]
    by_cases fs : free start = true
    · rw [if_pos fs]
      exact ⟨fs, Nat.le_refl _, fun i hi hr => by omega⟩
    · rw [if_neg fs]
      have hj' : start + 1 ≤ j := by
        rcases Nat.lt_or_eq_of_le hj with h | h
        · exact h
        · subst h; simp [fs] at fj
      obtain ⟨a, b', c⟩ := ih (start + 1) hj' (by omega)
      refine ⟨a, by omega, fun i hi hr => ?_⟩
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact c i h hr
      · subst h; simpa using fs

/-- Nodup numbers all in `ks` are no more than `ks`. -/
theorem nodup_length_le (l ks : List Nat) (hl : l.Nodup) (hs : ∀ j ∈ l, j ∈ ks) : l.length ≤ ks.length := by
  induction l generalizing ks with
  | nil => simp
  | cons a t ih =>
    have ha : a ∈ ks := hs a (by simp)
    have hn := List.nodup_cons.mp hl
    have := ih (ks.erase a) hn.2 fun j hj =>
      (List.mem_erase_of_ne (fun e => hn.1 (by rw [← e]; exact hj))).mpr (hs j (by simp [hj]))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < ks.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- Of `0, ..., ks.length`, one is not in `ks`. -/
theorem exists_free (ks : List Nat) : ∃ j, j < ks.length + 1 ∧ j ∉ ks := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ j ∈ List.range (ks.length + 1), j ∈ ks := fun j hj =>
    Classical.byContradiction fun hj' => hne ⟨j, List.mem_range.mp hj, hj'⟩
  have := nodup_length_le _ ks List.nodup_range hall
  simp at this
  omega

impl goal_constant_name: cli::goal_constant_name for (b : Bool) (ks : List Nat) (k : Nat) {
  base_taken? := b,
  taken := Fren.FinSet.ofList (ks.map Int.ofNat),
  k := k,
  kept? := Fren.Core.goalConstantName (takenOf b ks) "x" (ks.length + 1) == "x",
  chosen? := Fren.Core.goalConstantName (takenOf b ks) "x" (ks.length + 1) == Fren.Core.goalCandidate "x" k,
} by
  intro b ks k _
  simp only [fren_spec]
  have hx : takenOf b ks "x" = b := by
    cases b <;> simp [takenOf, goalCandidate_ne]
  have memk : ∀ j : Nat, ((j : Int) ∈ Fren.FinSet.ofList (ks.map Int.ofNat)) ↔ j ∈ ks := by
    intro j
    simp only [Fren.FinSet.mem_ofList, List.mem_map]
    exact ⟨fun ⟨a, ha, e⟩ => (Int.ofNat.inj e) ▸ ha, fun h => ⟨j, h, rfl⟩⟩
  cases b with
  | false =>
    simp only [Fren.Core.goalConstantName, hx, Bool.not_false, if_true]
    simp [(goalCandidate_ne k).symm]
  | true =>
    simp only [Fren.Core.goalConstantName, hx, Bool.not_true, Bool.false_eq_true, if_false]
    simp only [takenOf_candidate]
    obtain ⟨j, hj, hjk⟩ := exists_free ks
    obtain ⟨fr, -, least⟩ := firstFree_spec (fun i => !ks.contains i) 0 (ks.length + 1) j (Nat.zero_le _)
      (by omega) (by simpa using hjk)
    generalize Fren.Core.firstFree (fun i => !ks.contains i) 0 (ks.length + 1) = r at fr least
    refine ⟨by simp [goalCandidate_ne], ?_⟩
    have ceq : (Fren.Core.goalCandidate "x" r == Fren.Core.goalCandidate "x" k) = true ↔ r = k := by
      constructor
      · intro e; exact goalCandidate_inj (by simpa using e)
      · intro e; simp [e]
    rw [ceq, memk]
    simp only [Bool.not_eq_true'] at fr least
    have fr : r ∉ ks := by simpa using fr
    constructor
    · rintro rfl
      refine ⟨⟨trivial, fr⟩, fun i ⟨hi0, hik⟩ => ?_⟩
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
      rw [memk]
      have := least n (Nat.zero_le _) (by omega)
      simpa using this
    · rintro ⟨⟨-, hk⟩, hlt⟩
      rcases Nat.lt_trichotomy r k with h | h | h
      · have := hlt r ⟨by omega, by omega⟩
        rw [memk] at this; exact absurd this fr
      · exact h
      · have := least k (Nat.zero_le _) h
        simp at this; exact absurd this hk

/-! ## The symbols of a query (`cli::query_symbols`) -/

namespace QuerySymbols

/-- A string that does not contain `"#"`, as Fren's `contains?` reads it,
has no `#`. -/
theorem not_mem_of_contains {s : String} (h : Fren.Str.contains s "#" = false) : '#' ∉ s.toList := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have : Fren.Str.contains s "#" = true := by
    simp only [Fren.Str.contains, List.any_eq_true, List.mem_range]
    refine ⟨i, by rw [← String.length_toList]; omega, ?_⟩
    rw [List.drop_eq_getElem_cons hi, he]
    rfl
  simp_all

/-- What precedes the first `#` and what follows it. -/
theorem hash_split : ∀ {x y s t : List Char}, '#' ∉ x → '#' ∉ y → x ++ '#' :: s = y ++ '#' :: t → x = y ∧ s = t
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: _, _, _, _, hy, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hy
  | c :: _, [], _, _, hx, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hx
  | a :: x, b :: y, s, t, hx, hy, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := hash_split (x := x) (y := y) (fun m => hx (List.mem_cons_of_mem _ m))
      (fun m => hy (List.mem_cons_of_mem _ m)) h
    exact ⟨by rw [this.1], this.2⟩

/-- A number's text is its decimal digits, which are not empty and are
all digits. -/
theorem digits (k : Nat) : (toString k).toList = Nat.toDigits 10 k := Nat.toList_repr

theorem digit_of_mem {k : Nat} {c : Char} (h : c ∈ (toString k).toList) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) (digits k ▸ h)

theorem digits_ne_nil (k : Nat) : (toString k).toList ≠ [] := digits k ▸ Nat.toDigits_ne_nil

theorem digits_inj {j k : Nat} (h : (toString j).toList = (toString k).toList) : j = k :=
  Nat.repr_injective (String.toList_inj.mp h)

/-- The symbol of each kind, as a list: its name, then, but for a
variable's, `#` and what tells the kinds apart. -/
def tail : Fren.Core.QuerySymbol → Option (List Char)
  | .name x => if Fren.Core.theorySymbols.contains x then some [] else none
  | .copy _ => some ['\'']
  | .bound _ k => some (toString k).toList
  | .closure _ n => some ("closure".toList ++ (toString n).toList)

theorem text_toList (a : Fren.Core.QuerySymbol) :
    a.text.toList = a.base.toList ++ (match tail a with | some t => '#' :: t | none => []) := by
  cases a with
  | name x =>
    simp only [Fren.Core.QuerySymbol.text, Fren.Core.QuerySymbol.base, Fren.Core.smtName, tail]
    split <;> simp [String.toList_append]
  | copy x => simp [Fren.Core.QuerySymbol.text, Fren.Core.QuerySymbol.base, Fren.Core.copySymbol, tail, String.toList_append]
  | bound x k => simp [Fren.Core.QuerySymbol.text, Fren.Core.QuerySymbol.base, Fren.Core.boundSymbol, tail, String.toList_append]
  | closure x n =>
    simp [Fren.Core.QuerySymbol.text, Fren.Core.QuerySymbol.base, Fren.Core.closureSymbol, tail, String.toList_append]

theorem digit_head {k : Nat} {c : Char} {t : List Char} (h : (toString k).toList = c :: t) : c.isDigit = true :=
  digit_of_mem (h ▸ List.mem_cons_self)

/-- Symbols of one name with the same tail are of the same thing. -/
theorem tail_inj {a b : Fren.Core.QuerySymbol} (hx : a.base = b.base) (ht : tail a = tail b) : a = b := by
  cases a <;> cases b <;> simp only [Fren.Core.QuerySymbol.base] at hx <;> subst hx <;>
    simp only [tail] at ht
  all_goals first
    | rfl
    | (split at ht <;> simp at ht)
    | (split at ht <;> simp at ht <;> exact absurd ht.symm (digits_ne_nil _))
    | (simp only [Option.some.injEq] at ht
       first
        | exact absurd (digit_head ht.symm) (by decide)
        | exact absurd (digit_head ht) (by decide)
        | exact congrArg _ (digits_inj ht)
        | exact congrArg _ (digits_inj (List.append_cancel_left ht))
        | (simp at ht; done))

/-- Two symbols of names without `#` are the same only if they are of the
same thing. -/
theorem text_inj {a b : Fren.Core.QuerySymbol} (ha : '#' ∉ a.base.toList) (hb : '#' ∉ b.base.toList)
    (h : a.text = b.text) : a = b := by
  have h := congrArg String.toList h
  rw [text_toList, text_toList] at h
  apply tail_inj _ _
  all_goals cases hta : tail a <;> cases htb : tail b <;> simp only [hta, htb, List.append_nil] at h
  · exact String.toList_inj.mp h
  · exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) ha
  · exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) hb
  · exact String.toList_inj.mp (hash_split ha hb h).1
  · rfl
  · exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) ha
  · exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) hb
  · rw [(hash_split ha hb h).2]

end QuerySymbols

/-- A symbol as the Req has it: whether a theory has a variable's name,
and numbers in decimal. -/
def toReqSymbol : Fren.Core.QuerySymbol → cli.QuerySymbol
  | .name x => .Name x (Fren.Core.theorySymbols.contains x)
  | .copy x => .Copy x
  | .bound x k => .Bound x (toString k)
  | .closure x n => .Closure x (toString n)

theorem toReqSymbol_inj {a b : Fren.Core.QuerySymbol} (h : toReqSymbol a = toReqSymbol b) : a = b := by
  cases a <;> cases b <;> simp only [toReqSymbol, reduceCtorEq, cli.QuerySymbol.Name.injEq,
    cli.QuerySymbol.Copy.injEq, cli.QuerySymbol.Bound.injEq, cli.QuerySymbol.Closure.injEq] at h
  all_goals first
    | exact congrArg _ h.1
    | (obtain ⟨rfl, h⟩ := h; exact congrArg _ (Nat.repr_injective h))
    | (rw [h])

theorem not_mem_of_not_contains {s : String} (h : ¬Fren.Str.contains s (Fren.Str.lit "#") = true) : '#' ∉ s.toList :=
  QuerySymbols.not_mem_of_contains (by simpa using h)

impl query_symbols: cli::query_symbols for (a b : Fren.Core.QuerySymbol) {
  a := toReqSymbol a,
  b := toReqSymbol b,
  symbol_a := a.text,
  symbol_b := b.text,
  same? := a.text == b.text,
} by
  intro a b _
  simp only [fren_spec]
  refine ⟨⟨?_, ?_⟩, beq_iff_eq⟩
  · cases a <;> simp [toReqSymbol, Fren.Core.QuerySymbol.text, Fren.Core.smtName, Fren.Core.copySymbol,
      Fren.Core.boundSymbol, Fren.Core.closureSymbol, Fren.Str.lit, String.append_assoc]
  · cases b <;> simp [toReqSymbol, Fren.Core.QuerySymbol.text, Fren.Core.smtName, Fren.Core.copySymbol,
      Fren.Core.boundSymbol, Fren.Core.closureSymbol, Fren.Str.lit, String.append_assoc]

/-- What the Req's `apart` says, which its checker proves from `forms` and
`rule`: of names without `#`, symbols are the same only if they are of
the same thing. -/
theorem query_symbols_apart {a b : Fren.Core.QuerySymbol} (ha : '#' ∉ a.base.toList) (hb : '#' ∉ b.base.toList) :
    a.text = b.text ↔ toReqSymbol a = toReqSymbol b :=
  ⟨fun e => congrArg _ (QuerySymbols.text_inj ha hb e), fun e => by rw [toReqSymbol_inj e]⟩

end Fren.Impls
