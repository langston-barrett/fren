-- keep-sorted start
import FrenCli.Color
import FrenCli.Exit
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
}

end Fren.Impls
