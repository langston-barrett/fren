-- keep-sorted start
import FrenCli.MutateOutcome
import FrenCli.MutateSelect
import Impls.Check
import Impls.Cli
import Reqs.Mutate
-- keep-sorted end
open Fren.Lang

/-!
# What becomes of a mutant (`Reqs/Mutate`)

The decisions in `FrenCli.MutateOutcome` and `FrenCli.MutateSelect`
implement the comps of `mutate`. Each obligation over `Bool` is proved by
`decide`, given the variables of `mutate::exit`'s instance, and each over
`Nat` by `simp`.
-/

namespace Fren.Impls

open FrenCli.Mutate (Outcome Tally killsCheck outcome missed exitCode rechecks both)

def toMutantOutcome : Outcome → mutate.Outcome
  | .killed => .Killed
  | .survived => .Survived
  | .equivalent => .Equivalent
  | .unviable => .Unviable

impl mutant_kill: mutate::kill for (b a : Fren.Core.Verdict) {
  before := toVerdict b,
  after := toVerdict a,
  kills? := killsCheck b a,
} by
  intro b a _
  cases b <;> cases a <;> decide

impl mutant_outcome: mutate::outcome for (v k e : Bool) {
  viable? := v,
  killed? := k,
  equivalent? := e,
  outcome := toMutantOutcome (outcome v k e),
} by
  intro v k e _
  cases v <;> cases k <;> cases e <;> decide

impl mutant_missed: mutate::missed for (s t : Bool) {
  by_solver? := s,
  by_testing? := t,
  missed? := missed s t,
} by
  intro s t _
  cases s <;> cases t <;> decide

/-- The most severe level that `exitCode` gives `cli::exit`. -/
def mutateWorst (s i : Bool) : Option Fren.Core.Severity := if i then some .error else if s then some .warning else none

-- The instance's variables are given by the code.
impl mutate_exit: mutate::exit for (r s i : Bool) {
  ran? := r,
  survived? := s,
  internal? := i,
  code := (exitCode r s i).toNat,
} by
  intro r s i _
  refine ⟨toLevel (mutateWorst s i), r, toLevel (mutateWorst s i), (FrenCli.exitCode r (mutateWorst s i)).toNat, ?_, ?_, ?_⟩ <;>
    cases r <;> cases s <;> cases i <;> decide

/-- Adding a mutant's outcome to the counts so far. -/
def countedAfter (o : Outcome) (k s e u : Nat) : Tally :=
  ({ killed := k, survived := s, equivalent := e, unviable := u } : Tally).add o

impl mutant_count: mutate::count for (o : Outcome) (k s e u : Nat) {
  outcome := toMutantOutcome o,
  killed := k,
  survived := s,
  equivalent := e,
  unviable := u,
  killed_after := (countedAfter o k s e u).killed,
  survived_after := (countedAfter o k s e u).survived,
  equivalent_after := (countedAfter o k s e u).equivalent,
  unviable_after := (countedAfter o k s e u).unviable,
} by
  intro o k s e u _
  cases o <;> simp [fren_spec, countedAfter, Tally.add, toMutantOutcome]

/-- The rate of `k` killed and `s` surviving, of which there is at least
one, is a percentage, and 100 exactly when none survives. -/
theorem rate_bounds (k s : Nat) (pos : 0 < k + s) :
    100 * k / (k + s) ≤ 100 ∧ (100 * k / (k + s) = 100 ↔ s = 0) := by
  refine ⟨Nat.div_le_of_le_mul (by omega), fun hr => ?_, fun hs => ?_⟩
  · have := (Nat.le_div_iff_mul_le pos).mp (Nat.le_of_eq hr.symm)
    omega
  · subst hs
    exact Nat.mul_div_cancel 100 (by omega)

impl kill_rate: mutate::rate for (k s : Nat) {
  killed := k,
  survived := s,
  rated? := ({ killed := k, survived := s } : Tally).rate?.isSome,
  rate := (({ killed := k, survived := s } : Tally).rate?).getD 0,
} by
  intro k s _
  by_cases h : k + s = 0
  · have : k = 0 ∧ s = 0 := by omega
    obtain ⟨rfl, rfl⟩ := this
    simp [fren_spec, Tally.rate?]
  · obtain ⟨le, full⟩ := rate_bounds k s (by omega)
    have hk : ¬(k = 0 ∧ s = 0) := by omega
    have hz : k = 0 → 100 * k / (k + s) = 0 := by intro h0; subst h0; simp
    obtain ⟨f1, f2⟩ := full
    generalize hq : 100 * k / (k + s) = q at le f1 f2 hz
    simp [fren_spec, Tally.rate?, hk, hq]
    omega

/-- An answer to whether parts are equivalent, as `both` combines them. -/
def toAnswer : Option Bool → mutate.Answer
  | some true => .Equal
  | some false => .Differs
  | none => .Unknown

impl skip_unchanged: mutate::skip for (fp fp' : String) (b a : Fren.Core.Verdict) {
  changed? := fp != fp',
  before := toVerdict b,
  after := toVerdict a,
  run? := rechecks fp fp',
} by
  intro fp fp' b a _
  refine ⟨toVerdict b, toVerdict a, killsCheck b a, by simp [fren_spec, rechecks], ?_⟩
  -- The instance reads only the verdicts.
  generalize (fp != fp') = c
  generalize rechecks fp fp' = r
  cases b <;> cases a <;> cases c <;> cases r <;> decide

impl equivalence_parts: mutate::combine for (a b : Option Bool) {
  a := toAnswer a,
  b := toAnswer b,
  both := toAnswer (both a b),
} by
  intro a b _
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> decide

impl mutant_selection: mutate::selection for (c n t s h : Bool) {
  of_comp? := c,
  named? := n,
  touched? := t,
  sampled? := s,
  sharded? := h,
  selected? := FrenCli.Mutate.chosen c n t s h,
} by
  intro c n t s h _
  cases c <;> cases n <;> cases t <;> cases s <;> cases h <;> decide

-- Over `Nat`, so `decide` does not apply.
impl patch_touches: mutate::touches for (f l n : Nat) {
  first := f,
  last := l,
  line := n,
  touched? := FrenCli.Mutate.touchesLine f l n,
} by
  intro f l n _
  simp [fren_spec, FrenCli.Mutate.touchesLine]

impl mutant_sample: mutate::sample for (r s : Nat) {
  rank := r,
  size := s,
  taken? := FrenCli.Mutate.takes r s,
} by
  intro r s _
  simp [fren_spec, FrenCli.Mutate.takes]

-- The remainder is the code's: that of the identifier's hash.
impl mutant_shard: mutate::shard for (h k n : Nat) {
  remainder := h % n,
  k := k,
  taken? := FrenCli.Mutate.inShard h k n,
} by
  intro h k n _
  simp [fren_spec, FrenCli.Mutate.inShard]

end Fren.Impls
