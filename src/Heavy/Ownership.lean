import Std

/-! Pure decisions for the existing slot-owner protocol. Report decoding,
flock/procfs observations and all syscalls remain adapter responsibilities.
This module depends only on Std, never on Fren or its requirements. -/

namespace Heavy.Ownership

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

/-- A decoded protocol-v3 report. Timestamps and TTL share an integral
monotonic unit. Malformed wire records are decoded as `none` by the adapter. -/
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

end Heavy.Ownership
