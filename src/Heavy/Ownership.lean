import Std

/-! Pure decisions for the existing slot-owner protocol. Report decoding,
flock/procfs observations and all syscalls remain adapter responsibilities.
This module depends only on Std, never on Fren or its requirements. -/

namespace Heavy.Ownership

/-- Numeric results after the adapter's arithmetic. Finite ticks and TTL
share a positive scale; infinities and NaN must not discard report identity.
This type does not encode an approval or claim to implement IEEE arithmetic. -/
inductive TimeSpan where
  | finite (ticks : Int)
  | positiveInfinity
  | negativeInfinity
  | notANumber
  deriving Repr

/-- A relative timestamp at now = 0. All non-finite elapsed values fail
Python's bounded freshness comparison; the future timestamp 1 represents
that outcome without discarding the report's owner or RSS. -/
def elapsedTimestamp : TimeSpan → Int
  | .finite e => -e
  | _ => 1

/-- A relative deadline at now = 0. Python's `remaining <= 0` is false
for NaN and positive infinity, and true for negative infinity. -/
def remainingDeadline : TimeSpan → Int
  | .finite r => r
  | .negativeInfinity => -1
  | _ => 1

structure RegistryDecision where
  acquired : Bool
  retry : Bool
  timedOut : Bool
  deferred : Bool
  deriving Repr, BEq

/-- One nonblocking attempt. Availability is the flock result; the deadline
is fixed by the adapter once per acquisition, not once per retry. -/
def registry (available : Bool) (now deadline : Int) (held requested : Bool) : RegistryDecision :=
  ⟨available, !available && decide (now < deadline),
    !available && decide (now ≥ deadline), held && requested⟩

structure Owner where
  job : String
  sequence : Int
  deriving Repr, DecidableEq

/-- All three fields identify a monitor. A numeric PID alone is never an
identity, and a PID from diagnostic slot text is never an observation. -/
structure Monitor where
  pid : Int
  start : Int
  space : String
  deriving Repr, DecidableEq

/-- A decoded protocol-v3 report. Timestamps and TTL share an integral unit.
The Python boundary uses `elapsedTimestamp` at now = 0 after computing its
rounded elapsed value. Malformed wire records are decoded as `none`. -/
structure Report where
  owner : Owner
  rss : Int
  updated : Int
  monitor : Option Monitor
  deriving Repr

structure Lease where
  report : Option Report
  statusJob : String
  observed : Option Monitor
  legacyRss : Option Int
  deriving Repr

def validReport (r : Report) : Bool := decide (r.rss ≥ 0 ∧ r.owner.sequence > 0)

/-- Both endpoints are fresh; future-dated reports are not. -/
def freshReport (r : Report) (now : Int) (ttl : Nat) : Bool :=
  decide (0 ≤ now - r.updated ∧ now - r.updated ≤ ttl)

/-- A visible kernel owner must match even when the report is fresh.
Without one, only freshness can distinguish inherited status from ownership.
A verified owner stays compatible when its report becomes stale. -/
def reportOwner (report : Option Report) (statusJob : String) (observed : Option Monitor)
    (now : Int) (ttl : Nat) : Bool :=
  match report with
  | none => false
  | some r => validReport r && decide (statusJob = r.owner.job) &&
      match observed with
      | some m => decide (r.monitor = some m)
      | none => freshReport r now ttl

/-- The existing shared legacy forecast. The isolated-lease view below may
use it only for the sole unknown holder; it is not additive over holders. -/
def legacyReservation (cap : Nat) (observed : Option Int) : Int :=
  match observed with
  | some rss => if rss ≥ 0 then rss else max 1 (((cap : Int) + 1) / 2)
  | none => max 1 (((cap : Int) + 1) / 2)

def legacyMemory (observed : Option Int) : Int :=
  match observed with
  | some rss => max rss 0
  | none => 0

def admissionMemory (cap : Nat) (report : Option Report) (now : Int) (ttl : Nat) : Int :=
  match report with
  | some r => if validReport r then (if freshReport r now ttl then r.rss else cap)
      else legacyReservation cap none
  | none => legacyReservation cap none

def evictionMemory (report : Option Report) : Int :=
  match report with
  | some r => if validReport r then r.rss else 0
  | none => 0

structure LeaseDecision where
  live : Bool
  admission : Int
  eviction : Int
  deriving Repr, BEq

/-- No held lock means no charge, even if its metadata survives. These are
one lease's charges, not admission policy or a choice of eviction victim. -/
def lease (cap : Nat) (locked : Bool) (row : Lease) (now : Int) (ttl : Nat) : LeaseDecision :=
  if !locked then ⟨false, 0, 0⟩
  else if reportOwner row.report row.statusJob row.observed now ttl then
    ⟨true, admissionMemory cap row.report now ttl, evictionMemory row.report⟩
  else ⟨true, legacyReservation cap row.legacyRss, legacyMemory row.legacyRss⟩

/-- A held-job row before the victim eligibility check. Ownership is
established by the adapter; no PID is used as an identity here. -/
structure VictimRow where
  job : Option String
  order : Option Int
  rss : Option Int
  legacyRss : Option Int
  deriving Repr

def victimOwner (row : VictimRow) : Option Owner :=
  match row.job, row.order, row.rss with
  | some job, some order, some rss =>
    if order > 0 ∧ rss ≥ 0 then some ⟨job, order⟩ else none
  | _, _, _ => none

def newestOwner (first second : Option Owner) : Option Owner :=
  match first, second with
  | none, _ => second
  | _, none => first
  | some a, some b => if b.sequence > a.sequence then second else first

/-- Observed pressure and the first newest eligible owner, only above cap.
Legacy readings contribute independently; forecasts do not. -/
def memoryVictim (cap : Nat) (rows : List VictimRow) : Int × Option Owner :=
  let (total, latest) := rows.foldr (fun row (total, latest) =>
    let owner := victimOwner row
    let measured := if owner.isSome then row.rss.getD 0 else 0
    (measured + legacyMemory row.legacyRss + total, newestOwner owner latest)) (0, none)
  (total, if total > cap then latest else none)

/-- Observations from wait4 and killpg, after any PID 1 cleanup. They do not
claim that the probe or waits are atomic with subsequent OS activity. -/
inductive GroupProbe where
  | missing | present | denied
  deriving Repr, BEq

inductive GroupWait where
  | pending | exhausted
  deriving Repr, BEq

def groupGone (subreaper leaderReaped : Bool) (wait : GroupWait) (probe : GroupProbe) : Bool :=
  leaderReaped && (!subreaper || wait == .exhausted) && probe == .missing

end Heavy.Ownership
