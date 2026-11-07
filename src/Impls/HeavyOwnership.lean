-- keep-sorted start
import Fren.Impl
import Heavy.Ownership
import Reqs.Testing
-- keep-sorted end
open Fren.Lang

/-! The Std-only ownership kernel, bound to the existing heavy requirements.
These proofs establish conformance of the decoded Lean functions, not their
use by Fren's CLI or hosted front end. Each output is inventoried outside
those runtimes in `test/impl_paths.txt`. Python's concrete lock, wire decoding
and procfs tests remain in `Impls.Trace`. -/

namespace Fren.Impls.HeavyOwnership

open Heavy.Ownership

def owner (o : Owner) : testing.MemoryOwner := ⟨o.job, o.sequence⟩

def monitor (m : Monitor) : testing.MonitorIdentity := ⟨m.pid, m.start, m.space⟩

def report (r : Report) : testing.MemoryReport :=
  ⟨owner r.owner, r.rss, r.updated, r.monitor.map monitor⟩

def memoryLease (r : Lease) : testing.MemoryLease :=
  ⟨r.report.map report, r.statusJob, r.observed.map monitor, r.legacyRss⟩

def timeSpan : TimeSpan → testing.TimeSpan
  | .finite e => .Finite e
  | .positiveInfinity => .PositiveInfinity
  | .negativeInfinity => .NegativeInfinity
  | .notANumber => .NotANumber

impl time_conversion: testing::heavy_time_conversion for (span : TimeSpan) (ttl : Nat) {
  span := timeSpan span,
  ttl := ttl,
  elapsed_updated := elapsedTimestamp span,
  remaining_deadline := remainingDeadline span,
  fresh? := freshReport ⟨⟨"", 1⟩, 0, elapsedTimestamp span, none⟩ 0 ttl,
  timed_out? := (Heavy.Ownership.registry false 0 (remainingDeadline span) false false).timedOut,
} by
  intro span ttl _
  cases span <;>
    simp [fren_spec, timeSpan, elapsedTimestamp, remainingDeadline, freshReport,
      Heavy.Ownership.registry]

/-- Normalization preserves all integral freshness inputs, not just fixtures. -/
theorem integral_freshness (r : Report) (now : Int) (ttl : Nat) :
    freshReport { r with updated := elapsedTimestamp (.finite (now - r.updated)) } 0 ttl =
      freshReport r now ttl := by
  simp [freshReport, elapsedTimestamp]

/-- Normalization also preserves the original integral registry contract. -/
theorem integral_registry (available : Bool) (now deadline : Int) (held requested : Bool) :
    Heavy.Ownership.registry available 0 (remainingDeadline (.finite (deadline - now))) held requested =
      Heavy.Ownership.registry available now deadline held requested := by
  have hge : (0 ≥ deadline - now) ↔ now ≥ deadline := by omega
  simp [Heavy.Ownership.registry, remainingDeadline, hge]

impl registry: testing::heavy_registry
    for (available : Bool) (now deadline : Int) (held requested : Bool) {
  available? := available,
  now := now,
  deadline := deadline,
  held? := held,
  requested? := requested,
  acquired? := (Heavy.Ownership.registry available now deadline held requested).acquired,
  retry? := (Heavy.Ownership.registry available now deadline held requested).retry,
  timed_out? := (Heavy.Ownership.registry available now deadline held requested).timedOut,
  deferred? := (Heavy.Ownership.registry available now deadline held requested).deferred,
} by
  intro available now deadline held requested _
  simp [fren_spec, Heavy.Ownership.registry]

theorem valid_eq (r : Report) : testing.valid_report? (report r) = validReport r := by
  rfl

theorem fresh_eq (r : Report) (now : Int) (ttl : Nat) :
    testing.fresh_report? (report r) now ttl = freshReport r now ttl := by
  simp [testing.fresh_report?, report, freshReport]

theorem monitor_eq (a b : Monitor) : monitor a = monitor b ↔ a = b := by
  cases a; cases b; simp [monitor]

theorem report_owner_eq (r : Option Report) (job : String) (m : Option Monitor)
    (now : Int) (ttl : Nat) :
    testing.report_owner? (r.map report) job (m.map monitor) now ttl =
      reportOwner r job m now ttl := by
  cases r with
  | none => rfl
  | some r =>
    cases m with
    | none =>
      simp [testing.report_owner?, reportOwner, testing.valid_report?, validReport,
        testing.fresh_report?, freshReport, report, owner, Prelude.Option.some.x0,
        Bool.and_assoc]
    | some m =>
      cases hm : r.monitor <;>
        simp [testing.report_owner?, reportOwner, testing.valid_report?, validReport,
          report, owner, hm, monitor_eq, Prelude.Option.some.x0, Bool.and_assoc]

impl report_owner: testing::heavy_report_owner
    for (r : Option Report) (job : String) (m : Option Monitor) (now : Int) (ttl : Nat) {
  report := r.map report,
  status_job := job,
  observed := m.map monitor,
  now := now,
  ttl := ttl,
  compatible? := reportOwner r job m now ttl,
} by
  intro r job m now ttl _
  refine ⟨?_, trivial⟩
  change reportOwner r job m now ttl = testing.report_owner? (r.map report) job (m.map monitor) now ttl
  exact (report_owner_eq r job m now ttl).symm

theorem legacy_reservation_eq (cap : Nat) (rss : Option Int) :
    testing.legacy_reservation cap rss = legacyReservation cap rss := by
  cases rss <;> simp [testing.legacy_reservation, legacyReservation, Int.max_def]
  all_goals split <;> omega

theorem legacy_memory_eq (rss : Option Int) :
    testing.legacy_memory rss = legacyMemory rss := by
  cases rss <;> simp [testing.legacy_memory, legacyMemory, Int.max_def]
  split <;> split <;> omega

theorem admission_eq (cap : Nat) (r : Option Report) (now : Int) (ttl : Nat) :
    testing.admission_memory cap (r.map report) now ttl = admissionMemory cap r now ttl := by
  cases r <;>
    simp [testing.admission_memory, admissionMemory, testing.valid_report?, validReport,
      testing.fresh_report?, freshReport, report, owner, testing.legacy_reservation,
      legacyReservation, Int.max_def]
  all_goals split <;> omega

theorem eviction_eq (r : Option Report) :
    testing.eviction_memory (r.map report) = evictionMemory r := by
  cases r <;> simp [testing.eviction_memory, evictionMemory, testing.valid_report?, validReport,
    report, owner]

impl lease: testing::heavy_lease
    for (cap : Nat) (locked : Bool) (row : Lease) (now : Int) (ttl : Nat) {
  cap := cap,
  locked? := locked,
  lease := memoryLease row,
  now := now,
  ttl := ttl,
  live? := (Heavy.Ownership.lease cap locked row now ttl).live,
  admission := (Heavy.Ownership.lease cap locked row now ttl).admission,
  eviction := (Heavy.Ownership.lease cap locked row now ttl).eviction,
} by
  intro cap locked row now ttl _
  refine ⟨row.report.map report, row.statusJob, row.observed.map monitor, now, ttl,
    reportOwner row.report row.statusJob row.observed now ttl, ?_⟩
  have ho := (report_owner_eq row.report row.statusJob row.observed now ttl).symm
  have ha := (admission_eq cap row.report now ttl).symm
  have he := (eviction_eq row.report).symm
  have hl := (legacy_reservation_eq cap row.legacyRss).symm
  have hm := (legacy_memory_eq row.legacyRss).symm
  simp only [fren_spec, memoryLease] at ⊢ ho ha he hl hm
  rw [← ha, ← he, ← hl, ← hm, ← ho]
  cases locked
  · simp [Heavy.Ownership.lease]
  · by_cases h : reportOwner row.report row.statusJob row.observed now ttl = true <;>
      simp [Heavy.Ownership.lease, h]

def victimRow (r : VictimRow) : testing.VictimRow :=
  ⟨r.job, r.order, r.rss, r.legacyRss⟩

def victimRows : List VictimRow → testing.VictimRows
  | [] => .Nil
  | r :: rs => .Cons (victimRow r) (victimRows rs)

theorem victim_owner_eq (r : VictimRow) :
    testing.victim_owner (victimRow r) = (victimOwner r).map owner := by
  cases r with
  | mk job order rss legacy =>
    cases job <;> cases order <;> cases rss <;>
      simp [testing.victim_owner, victimRow, victimOwner, owner]

theorem newest_owner_eq (a b : Option Owner) :
    testing.newest_owner (a.map owner) (b.map owner) = (newestOwner a b).map owner := by
  cases a <;> cases b <;> simp [testing.newest_owner, newestOwner, owner]
  split <;> rfl

/-- Equal orders keep the first owner, regardless of their identities. -/
theorem newest_tie (a b : Owner) (h : a.sequence = b.sequence) :
    newestOwner (some a) (some b) = some a := by
  simp [newestOwner, h]

theorem victim_summary_eq (rows : List VictimRow) :
    (rows.foldr (fun row (total, latest) =>
      let o := victimOwner row
      let measured := if o.isSome then row.rss.getD 0 else 0
      (measured + legacyMemory row.legacyRss + total, newestOwner o latest)) (0, none)).1 =
        testing.victim_total (victimRows rows) ∧
    (rows.foldr (fun row (total, latest) =>
      let o := victimOwner row
      let measured := if o.isSome then row.rss.getD 0 else 0
      (measured + legacyMemory row.legacyRss + total, newestOwner o latest)) (0, none)).2.map owner =
        testing.victim_latest (victimRows rows) := by
  induction rows with
  | nil => simp [victimRows, testing.victim_total, testing.victim_latest]
  | cons r rs ih =>
    have ho := victim_owner_eq r
    have hl := legacy_memory_eq r.legacyRss
    have hn := newest_owner_eq (victimOwner r) ((rs.foldr (fun row (total, latest) =>
      let o := victimOwner row
      let measured := if o.isSome then row.rss.getD 0 else 0
      (measured + legacyMemory row.legacyRss + total, newestOwner o latest)) (0, none)).2)
    cases h : victimOwner r <;> cases hr : r.rss <;>
      simp_all [victimRows, testing.victim_total, testing.victim_latest, victimRow,
        victimOwner]

impl observed_victim: testing::heavy_observed_victim
    for (cap : Nat) (rows : List VictimRow) {
  cap := cap,
  rows := victimRows rows,
  total := (memoryVictim cap rows).1,
  selected := (memoryVictim cap rows).2.map owner,
} by
  intro cap rows _
  have h := victim_summary_eq rows
  simp only [fren_spec, memoryVictim]
  split <;> simp_all <;> omega

end Fren.Impls.HeavyOwnership
