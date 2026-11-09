-- keep-sorted start
import Fren.Impl
import Heavy.Budget
import Heavy.CompilerForecast
import Heavy.Ownership
import Heavy.Process
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

def memoryLeases : List Lease → testing.MemoryLeases
  | [] => .Nil
  | r :: rs => .Cons (memoryLease r) (memoryLeases rs)

theorem observed_admission_eq (cap : Nat) (rows : List Lease) (now : Int) (ttl : Nat) :
    testing.observed_admission cap (memoryLeases rows) now ttl =
      rows.foldr (fun row total =>
        (if reportOwner row.report row.statusJob row.observed now ttl then
          admissionMemory cap row.report now ttl else legacyMemory row.legacyRss) + total) 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [testing.observed_admission, memoryLeases, memoryLease, List.foldr_cons]
    rw [report_owner_eq, admission_eq, legacy_memory_eq, ih]

set_option linter.unusedSimpArgs false in
theorem unknown_legacy_eq (rows : List Lease) (now : Int) (ttl : Nat) :
    testing.unknown_legacy? (memoryLeases rows) now ttl =
      rows.any (fun row => !reportOwner row.report row.statusJob row.observed now ttl &&
        match row.legacyRss with | none => true | some rss => decide (rss < 0)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [testing.unknown_legacy?, memoryLeases, memoryLease, List.any_cons]
    rw [report_owner_eq, ih]
    cases howner : reportOwner r.report r.statusJob r.observed now ttl <;>
      cases hany : rs.any (fun row => !reportOwner row.report row.statusJob row.observed now ttl &&
        match row.legacyRss with | none => true | some rss => decide (rss < 0)) <;>
      cases r.legacyRss <;> simp only [howner, hany, Bool.false_eq_true, Bool.true_eq_false,
        Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or,
        Bool.or_false, Bool.or_true, decide_true, decide_false, not_false_eq_true, not_true_eq_false,
        false_and, true_and, false_or, true_or] <;> simp

impl admission_total: testing::heavy_admission_total
    for (cap : Nat) (rows : List Lease) (now : Int) (ttl : Nat) {
  cap := cap,
  leases := memoryLeases rows,
  now := now,
  ttl := ttl,
  total := admissionTotal cap rows now ttl,
} by
  intro cap rows now ttl _
  simp [fren_spec, testing.admission_total, admissionTotal, observed_admission_eq,
    unknown_legacy_eq, legacyReservation, Int.max_def]
  rfl

/-- A concrete mixed regression, independent of Fren's recursive solver. -/
theorem mixed_legacy_57 :
    admissionTotal 100 [⟨none, "", none, some 7⟩, ⟨none, "", none, none⟩,
      ⟨none, "", none, none⟩] 0 10 = 57 := by
  decide

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

def groupProbe : GroupProbe → testing.GroupProbe
  | .missing => .Missing
  | .present => .Present
  | .denied => .Denied

impl group_gone: testing::heavy_group_gone
    for (subreaper leader : Bool) (wait : GroupWait) (probe : GroupProbe) {
  subreaper? := subreaper,
  leader_reaped? := leader,
  group_wait_pending? := wait == .pending,
  probe := groupProbe probe,
  gone? := groupGone subreaper leader wait probe,
} by
  intro subreaper leader wait probe _
  cases subreaper <;> cases leader <;> cases wait <;> cases probe <;>
    simp [fren_spec, groupGone, groupProbe] <;> decide

def cleanupCause : CleanupCause → testing.CleanupCause
  | .memorySample => .MemorySample
  | .externalSignal => .ExternalSignal
  | .setupFailure => .SetupFailure
  | .accountingFailure => .AccountingFailure

theorem victim_selected_eq (cap : Nat) (rows : List VictimRow) :
    (memoryVictim cap rows).2.map owner =
      (if testing.victim_total (victimRows rows) > cap then
        testing.victim_latest (victimRows rows) else none) := by
  have h := victim_summary_eq rows
  simp only [memoryVictim]
  rw [← h.1, ← h.2]
  split <;> simp

set_option maxRecDepth 4096 in
impl cleanup_trigger: testing::heavy_cleanup_trigger
    for (cause : CleanupCause) (cap ownRss : Nat) (ownJob : Option String)
        (rows : List VictimRow) {
  cause := cleanupCause cause,
  cap := cap,
  own_rss := ownRss,
  own_job := ownJob,
  rows := victimRows rows,
  cleanup? := cleanupTrigger cause cap ownRss ownJob rows,
} by
  intro cause cap ownRss ownJob rows _
  have hv := victim_selected_eq cap rows
  cases hs : (memoryVictim cap rows).2 with
  | none =>
    simp only [hs, Option.map_none] at hv
    cases cause <;> cases ownJob <;>
      simp [fren_spec, cleanupCause, cleanupTrigger, hs, ← hv]
  | some selected =>
    simp only [hs, Option.map_some] at hv
    cases cause <;> cases ownJob with
    | none => simp [fren_spec, cleanupCause, cleanupTrigger, hs, ← hv, owner]
    | some job =>
      by_cases eq : selected.job = job <;>
        simp [fren_spec, cleanupCause, cleanupTrigger, hs, ← hv, owner, eq]

impl signal_attempt: testing::heavy_signal_attempt
    for (subreaper leader : Bool) (wait : GroupWait) (probe : GroupProbe) {
  subreaper? := subreaper,
  leader_reaped? := leader,
  group_wait_pending? := wait == .pending,
  probe := groupProbe probe,
  attempt? := signalAttempt subreaper leader wait probe,
} by
  intro subreaper leader wait probe _
  cases subreaper <;> cases leader <;> cases wait <;> cases probe <;>
    simp [fren_spec, signalAttempt, groupGone, groupProbe] <;> decide

end Fren.Impls.HeavyOwnership

namespace Fren.Impls.HeavyOwnership

-- These are the actual functions called by the standalone compiler launcher.
impl process_result: testing::heavy_process_result
    for (launchError execError waitError status : Nat) {
  launch_error := launchError,
  exec_error := execError,
  wait_error := waitError,
  status := status,
  result := let r := Heavy.Process.result launchError execError waitError status
    ⟨r.kind, r.detail, r.shellCode⟩,
} by
  intro launchError execError waitError status _
  have hz : ((status : Int) % 128 = 0) ↔ status % 128 = 0 := by omega
  have hs : ((status : Int) % 128 < 127) ↔ status % 128 < 127 := by omega
  by_cases hl : 0 < launchError <;> by_cases hw : 0 < waitError <;>
    by_cases he : 0 < execError <;> by_cases h0 : status % 128 = 0 <;>
    by_cases h1 : status % 128 < 127 <;>
    simp [fren_spec, Heavy.Process.result, testing.process_result, hl, hw, he, h0, h1, hz, hs]

impl process_elapsed: testing::heavy_process_elapsed for (clockError start finish : Nat) {
  clock_error := clockError,
  start := start,
  finish := finish,
  elapsed := (Heavy.Process.elapsed clockError start finish).map Int.ofNat,
} by
  intro clockError start finish _
  by_cases h : clockError = 0 ∧ finish ≥ start
  · have hsub : ((finish - start : Nat) : Int) = (finish : Int) - (start : Int) := by omega
    simp [fren_spec, Heavy.Process.elapsed, h, hsub]
  · simp [fren_spec, Heavy.Process.elapsed, h]

impl process_usage: testing::heavy_process_usage
    for (launchError execError waitError status user system rss : Nat) {
  launch_error := launchError,
  exec_error := execError,
  wait_error := waitError,
  status := status,
  user := user,
  system := system,
  rss := rss,
  cpu := (Heavy.Process.usage launchError execError waitError status user system rss).map (fun p => (p.1 : Int)),
  peak := (Heavy.Process.usage launchError execError waitError status user system rss).map (fun p => (p.2 : Int)),
} by
  intro launchError execError waitError status user system rss _
  have hs : ((status : Int) % 128 < 127) ↔ status % 128 < 127 := by omega
  simp [fren_spec, Heavy.Process.usage, hs, and_assoc]

impl process_request_excess: testing::heavy_process_request_excess
    for (requested observed : Option Nat) {
  requested := requested.map Int.ofNat,
  observed := observed.map Int.ofNat,
  excess := (Heavy.Process.requestExcess requested observed).map Int.ofNat,
} by
  intro requested observed _
  cases requested with
  | none => simp [fren_spec, Heavy.Process.requestExcess]
  | some request =>
    cases observed with
    | none => simp [fren_spec, Heavy.Process.requestExcess]
    | some peak =>
      by_cases hz : request = 0
      · simp [fren_spec, Heavy.Process.requestExcess, hz]
      · by_cases hp : peak > request
        · have hsub : ((peak - request : Nat) : Int) = (peak : Int) - request := by omega
          simp [fren_spec, Heavy.Process.requestExcess, hz, hp, hsub]
        · have hsub : peak - request = 0 := Nat.sub_eq_zero_of_le (by omega)
          simp [fren_spec, Heavy.Process.requestExcess, hz, hp, hsub]

impl compiler_cpu_limit: testing::heavy_compiler_cpu_limit for (seconds : Nat) (gated query : Bool) {
  seconds := seconds, gated? := gated, query? := query,
  limit := (Heavy.Process.compilerCpuLimit seconds gated query).map Int.ofNat,
} by
  intro seconds gated query _
  cases query <;> simp only [fren_spec, Heavy.Process.compilerCpuLimit] <;>
    split <;> split <;> simp_all <;> omega

impl compiler_wall_limit: testing::heavy_compiler_wall_limit for (milliseconds : Nat) (gated query : Bool) {
  milliseconds := milliseconds, gated? := gated, query? := query,
  limit := (Heavy.Process.compilerWallLimit milliseconds gated query).map Int.ofNat,
} by
  intro milliseconds gated query _
  cases query <;> simp only [fren_spec, Heavy.Process.compilerWallLimit, Heavy.Process.compilerCpuLimit] <;>
    split <;> split <;> simp_all <;> omega

impl wall_signal_mask: testing::heavy_wall_signal_mask for (error usr1 usr2 : Nat) {
  error := error, usr1 := usr1, usr2 := usr2,
  safe? := Heavy.Process.wallSignalMaskSafe error usr1 usr2,
} by
  intro error usr1 usr2 _
  simp [fren_spec, Heavy.Process.wallSignalMaskSafe]

impl wall_message: testing::heavy_wall_message for (bytes expected cause : Nat) {
  bytes := bytes, expected := expected, cause := cause,
  valid? := Heavy.Process.wallMessageValid bytes expected cause,
} by
  intro bytes expected cause _
  simp [fren_spec, Heavy.Process.wallMessageValid] <;> omega

impl compiler_cpu_observation: testing::heavy_compiler_cpu_observation
    for (seconds bytes first readError eof waitError : Nat) {
  seconds := seconds, bytes := bytes, first := first, read_error := readError,
  eof := eof, wait_error := waitError,
  applied := (Heavy.Process.appliedCompilerCpu seconds bytes first readError eof waitError).map Int.ofNat,
} by
  intro seconds bytes first readError eof waitError _
  simp [fren_spec, Heavy.Process.appliedCompilerCpu]
  split <;> split <;> simp_all <;> omega

impl process_fingerprint: testing::heavy_process_fingerprint for (mode bytes : Nat) {
  mode := mode,
  bytes := bytes,
  read? := Heavy.Process.fingerprintAllowed mode bytes,
} by
  intro mode bytes _
  have hm : (((mode : Int) / 4096) % 16 = 8) ↔ mode / 4096 % 16 = 8 := by omega
  have hb : ((bytes : Int) ≤ 67108864) ↔ bytes ≤ 67108864 := by omega
  simp [fren_spec, Heavy.Process.fingerprintAllowed, hm, hb]

def arguments : List String → testing.ProcessArguments
  | [] => .Nil
  | a :: rest => .Cons a (arguments rest)

def metadata (m : Heavy.Process.Metadata) : testing.ProcessMetadata :=
  ⟨m.kind, m.source, m.olean, m.ilean, m.c, m.bc, m.setup⟩

theorem empty_metadata_eq (kind : String) :
    metadata (Heavy.Process.emptyMetadata kind) = testing.process_empty_metadata kind := by rfl

theorem set_metadata_eq (m : Heavy.Process.Metadata) (flag value : String) :
    metadata (Heavy.Process.setMetadata m flag value) =
      testing.process_set_metadata (metadata m) flag value := by
  simp [metadata, Heavy.Process.setMetadata, testing.process_set_metadata]

theorem finish_metadata_eq (m : Heavy.Process.Metadata) :
    (Heavy.Process.finishMetadata m).map metadata = testing.process_finish_metadata (metadata m) := by
  cases m with
  | mk kind source o i c b setup =>
    cases source <;> by_cases h : kind = "stdin" <;>
      simp [metadata, Heavy.Process.finishMetadata, testing.process_finish_metadata, h]

theorem value_flag_eq (arg : String) : testing.process_value_flag? arg = Heavy.Process.valueFlag arg := by
  simp [testing.process_value_flag?, Heavy.Process.valueFlag]

theorem query_flag_eq (arg : String) : testing.process_query_flag? arg = Heavy.Process.queryFlag arg := by
  simp [testing.process_query_flag?, Heavy.Process.queryFlag]

theorem plain_flag_eq (arg : String) : testing.process_plain_flag? arg = Heavy.Process.plainFlag arg := by
  simp [testing.process_plain_flag?, Heavy.Process.plainFlag]

theorem metadata_source (m : Heavy.Process.Metadata) : (metadata m).source = m.source := rfl

set_option linter.unusedSimpArgs false in
theorem metadata_loop_eq (args : List String) (m : Heavy.Process.Metadata) :
    (Heavy.Process.metadataLoop args m).map metadata =
      testing.process_metadata_loop (arguments args) (metadata m) := by
  induction args, m using Heavy.Process.metadataLoop.induct with
  | case1 m =>
    simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case2 arg m hv =>
    simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case3 arg m hv value tail ih =>
    simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case4 arg rest m hv hq =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case5 rest m hv hq ih =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case6 m file tail hs ho hv hq hi =>
    simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case7 m file tail hs ho hv hq hi =>
    simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case8 rest m hn hv hq hi =>
    cases rest <;> cases hs : m.source <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case9 arg rest m hv hq hi hr hp ih =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case10 arg rest m hv hq hi hr hp ho =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case11 arg rest m hv hq hi hr hp ho value hs =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]
  | case12 arg rest m hv hq hi hr hp ho hs ih =>
    cases rest <;> simp_all [Heavy.Process.metadataLoop, arguments, testing.process_metadata_loop,
      value_flag_eq, query_flag_eq, plain_flag_eq, Heavy.Process.valueFlag,
      Heavy.Process.queryFlag, Heavy.Process.plainFlag, Heavy.Process.optionLike,
      Fren.Str.startsWith, Fren.Str.lit, ← empty_metadata_eq,
      ← set_metadata_eq, ← finish_metadata_eq, metadata_source]

impl process_arguments: testing::heavy_process_arguments for (args : List String) {
  args := arguments args,
  parsed := (Heavy.Process.parseMetadata args).map metadata,
} by
  intro args _
  simpa [fren_spec, Heavy.Process.parseMetadata, empty_metadata_eq] using
    metadata_loop_eq args (Heavy.Process.emptyMetadata "file")

impl process_metadata_reuse: testing::heavy_process_metadata_reuse
    for (currentPath : String) (currentFingerprint : Option String)
        (preparedPath preparedFingerprint version githash : String)
        (observedChecksum storedChecksum : Nat) {
  current_path := currentPath,
  current_fingerprint := currentFingerprint,
  prepared_path := preparedPath,
  prepared_fingerprint := preparedFingerprint,
  version := version,
  githash := githash,
  observed_checksum := observedChecksum,
  stored_checksum := storedChecksum,
  reuse? := Heavy.Process.reuseMetadata currentPath currentFingerprint
    preparedPath preparedFingerprint version githash observedChecksum storedChecksum,
} by
  intro currentPath currentFingerprint preparedPath preparedFingerprint version githash
    observedChecksum storedChecksum _
  simp [fren_spec, Heavy.Process.reuseMetadata, Fren.Str.lit, and_assoc]

impl process_identity: testing::heavy_process_identity
    for (source toolchain inputClosure : Option String) {
  source := source,
  toolchain := toolchain,
  input_closure := inputClosure,
  complete? := Heavy.Process.identityComplete source toolchain inputClosure,
} by
  intro source toolchain inputClosure _
  cases source <;> cases toolchain <;> cases inputClosure <;>
    simp [fren_spec, Heavy.Process.identityComplete, Heavy.Process.identityPart,
      testing.identity_part?]

end Fren.Impls.HeavyOwnership

namespace Fren.Impls.HeavyOwnership

impl compile_budget: testing::heavy_compile_budget
    for (allowance parent held demand ticket oldest : Int) {
  allowance := allowance,
  parent := parent,
  held := held,
  demand := demand,
  ticket := ticket,
  oldest := oldest,
  decision := Heavy.Budget.decision allowance parent held demand ticket oldest,
} by
  intro allowance parent held demand ticket oldest _
  simp [fren_spec, Heavy.Budget.decision, or_assoc]

impl compile_row: testing::heavy_compile_row
    for (locked : Bool) (state ticket : Int) (row : Heavy.Ownership.Lease) {
  locked? := locked,
  state := state,
  ticket := ticket,
  lease := memoryLease row,
  charge := Heavy.Budget.charge locked state ticket row,
} by
  intro locked state ticket row _
  cases locked <;> cases hr : row.report <;> cases hm : row.observed <;>
    simp [fren_spec, Heavy.Budget.charge, memoryLease, hr, hm, report, owner, monitor,
      Heavy.Ownership.reportOwner, Heavy.Ownership.validReport, Bool.and_assoc,
      and_assoc, Str.lit]
  rename_i r m
  cases r.monitor with
  | none => simp
  | some other =>
    cases other
    cases m
    simp

impl compile_deadline: testing::heavy_compile_deadline for (clockError now limit : Int) {
  clock_error := clockError,
  now := now,
  deadline := limit,
  decision := Heavy.Budget.deadline clockError now limit,
} by
  intro clockError now limit _
  simp [fren_spec, Heavy.Budget.deadline, or_assoc]

impl compile_lifecycle: testing::heavy_compile_lifecycle
    for (actionError handler flags autoReapBit previousWaitError waitError observed expected reaped : Int) {
  action_error := actionError,
  handler := handler,
  flags := flags,
  auto_reap_bit := autoReapBit,
  previous_wait_error := previousWaitError,
  wait_error := waitError,
  observed := observed,
  expected := expected,
  reaped := reaped,
  waitable? := Heavy.Budget.waitable actionError handler flags autoReapBit,
  signal? := Heavy.Budget.groupSignal actionError handler flags autoReapBit previousWaitError waitError observed expected reaped,
} by
  intro actionError handler flags autoReapBit previousWaitError waitError observed expected reaped _
  simp [fren_spec, Heavy.Budget.waitable, Heavy.Budget.groupSignal, and_assoc, Bool.and_assoc]

impl compile_source_identity: testing::heavy_compile_source_identity
    for (canonical fingerprint : Option String) {
  canonical := canonical,
  fingerprint := fingerprint,
  source := (Heavy.Budget.sourceIdentity canonical fingerprint).1,
  digest := (Heavy.Budget.sourceIdentity canonical fingerprint).2,
} by
  intro canonical fingerprint _
  cases canonical <;> simp [fren_spec, Heavy.Budget.sourceIdentity]

end Fren.Impls.HeavyOwnership

namespace Fren.Impls.HeavyOwnership

open Heavy.CompilerForecast

def compilerContext (c : Context) : testing.CompilerContext :=
  ⟨c.source, c.cwd, c.sourceFingerprint, c.compiler, c.compilerFingerprint,
    c.version, c.githash, arguments c.args, c.setup, c.setupFingerprint⟩

theorem arguments_injective : Function.Injective arguments := by
  intro a b h
  induction a generalizing b with
  | nil => cases b <;> simp [arguments] at h ⊢
  | cons a as ih =>
    cases b with
    | nil => simp [arguments] at h
    | cons b bs =>
      simp only [arguments] at h
      injection h with hab ht
      cases hab
      exact congrArg (List.cons a) (ih ht)

theorem compilerContext_injective : Function.Injective compilerContext := by
  intro a b h
  cases a; cases b
  simp only [compilerContext] at h
  injection h with hs hc hf hp ht hv hg ha hu hz
  have ha := arguments_injective ha
  cases hs; cases hc; cases hf; cases hp; cases ht
  cases hv; cases hg; cases ha; cases hu; cases hz
  rfl

impl compiler_sample: testing::heavy_compiler_sample
    for (r : Record) (c : Context) (boot : String) (cutoff now : Nat) {
  observed := compilerContext r.context,
  current := compilerContext c,
  source_after := r.sourceAfter,
  boot := r.boot,
  current_boot := boot,
  schema := r.schema,
  family := r.family,
  kind := r.kind,
  launch_error := r.launchError,
  exec_error := r.execError,
  wait_error := r.waitError,
  clock_error := r.clockError,
  status := r.status,
  pid := r.pid,
  gate_error := r.gateError.map Int.ofNat,
  child_present := r.childPresent,
  wrapper_code := r.wrapperCode.map Int.ofNat,
  start := r.start,
  finish := r.finish,
  cutoff := cutoff,
  now := now,
  rss := r.rss,
  measured_rss := r.measuredRss,
  usable? := sample r c boot cutoff now,
} by
  intro r c boot cutoff now _
  have hc : compilerContext r.context = compilerContext c ↔ r.context = c :=
    compilerContext_injective.eq_iff
  have hs2 : ((r.schema : Int) = 2) ↔ r.schema = 2 := by omega
  have hs3 : ((r.schema : Int) = 3) ↔ r.schema = 3 := by omega
  cases hg : r.gateError <;> cases hw : r.wrapperCode <;>
    by_cases h2 : r.schema = 2 <;>
    simp [fren_spec, sample, ← hc, compilerContext, hg, hw, h2, hs2, hs3, and_assoc]

impl compiler_padding: testing::heavy_compiler_padding
    for (peak : Option Int) (padding : Nat) {
  peak := peak,
  padding := padding,
  request := Heavy.CompilerForecast.padded peak padding,
} by
  intro peak padding _
  cases peak <;> simp [fren_spec, Heavy.CompilerForecast.padded]

theorem forecast_fit (allowance parent demand : Int) (positive : 0 < demand) :
    Heavy.Budget.decision allowance parent 0 demand 1 1 = 1 ↔
      0 ≤ parent ∧ parent ≤ allowance ∧ demand ≤ allowance - parent := by
  unfold Heavy.Budget.decision
  split
  · omega
  · split
    · omega
    · split <;> omega

impl compiler_request: testing::heavy_compiler_request
    for (peak : Option Int) (padding : Nat) (allowance parent : Int) {
  peak := peak,
  padding := padding,
  allowance := allowance,
  parent := parent,
  request := Heavy.CompilerForecast.forSession peak padding allowance parent,
} by
  intro peak padding allowance parent _
  cases peak with
  | none => simp [fren_spec, Heavy.CompilerForecast.forSession, Heavy.CompilerForecast.padded]
  | some p =>
    by_cases hp : 0 < p
    · by_cases hz : 0 < padding
      · by_cases hl : p + (padding : Int) ≤ 1125899906842624
        · have hd : 0 < p + (padding : Int) := by omega
          simp [fren_spec, Heavy.CompilerForecast.forSession, Heavy.CompilerForecast.padded,
            hp, hz, hl, forecast_fit allowance parent _ hd, and_assoc]
        · simp [fren_spec, Heavy.CompilerForecast.forSession, Heavy.CompilerForecast.padded, hp, hz, hl]
      · simp [fren_spec, Heavy.CompilerForecast.forSession, Heavy.CompilerForecast.padded, hp, hz]
    · simp [fren_spec, Heavy.CompilerForecast.forSession, Heavy.CompilerForecast.padded, hp]

end Fren.Impls.HeavyOwnership
