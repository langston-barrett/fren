import Heavy.Budget
import Heavy.Process
import Heavy.CompilerForecast

/-! Raw protocol adapter for the single-use session, shared with its tests.
Malformed input has no zero-demand or launch-anyway path. -/
namespace BudgetAdapter
open Heavy.Ownership Heavy.Budget

def words (s : String) : List String := (s.splitOn " ").filter (· != "")

def identity (s : String) : Option Monitor := do
  let [pid, start, space] := words s | none
  return ⟨← pid.toInt?, ← start.toInt?, space⟩

def row (s : String) : Option (Int × Int × Lease) := do
  let [stored, observed] := s.splitOn "\t" | none
  let ticket :: state :: demand :: pid :: start :: space :: [] := words stored | none
  let ticket ← ticket.toInt?
  let demand ← demand.toInt?
  let monitor ← identity s!"{pid} {start} {space}"
  let observed := identity observed
  return (ticket, ← state.toInt?, ⟨some ⟨⟨"compiler", ticket⟩, demand, 0, some monitor⟩,
    "compiler", observed, none⟩)

/-- The FFI holds the registry throughout this call and subsequent publication.
Raw row states are 0 waiting and 1 running. No row ages out. -/
def snapshot (raw : Array String) : Array UInt64 := Id.run do
  let some header := raw[0]? | return #[2, 0]
  let [a, p, t, d] := words header | return #[2, 0]
  let some a := a.toInt? | return #[2, 0]
  let some p := p.toInt? | return #[2, 0]
  let some t := t.toInt? | return #[2, 0]
  let some d := d.toInt? | return #[2, 0]
  let mut total := 0
  let mut oldest := t
  let mut own := false
  let mut seen : List Int := []
  for line in raw.toList.drop 1 do
    let some (ticket, state, lease) := row line | return #[2, 0]
    if seen.contains ticket then return #[2, 0]
    seen := ticket :: seen
    let some charged := charge true state ticket lease | return #[2, 0]
    if ticket == t then
      if state != 0 || (lease.report.map (·.rss)) != some d then return #[2, 0]
      own := true
    total := total + charged
    if total > 2^50 then return #[2, 0]
    if state == 0 then oldest := min oldest ticket
  if !own then return #[2, 0]
  return #[(decision a p total d t oldest).toNat.toUInt64, total.toNat.toUInt64]

/-- Actual FFI control observations, with no supplied freshness/owner verdict.
Tag 0: clock errno, now ns, fixed deadline ns. Tag 1: sigaction errno, raw
handler, sa_flags, SA_NOCLDWAIT, prior/current wait errno, si_pid, child PID,
last reap PID. The C caller requires exact output lengths and values. -/
def control (raw : Array UInt64) : Array UInt64 :=
  match raw.toList.map (fun n => (n.toNat : Int)) with
  | [0, error, now, limit] => #[(deadline error now limit).toNat.toUInt64]
  | [3, bytes, expected, cause] =>
    #[if Heavy.Process.wallMessageValid bytes.toNat expected.toNat cause.toNat then 1 else 0]
  | [2, error, usr1, usr2] =>
    #[if Heavy.Process.wallSignalMaskSafe error.toNat usr1.toNat usr2.toNat then 1 else 0]
  | [1, error, handler, flags, bit, previous, errorWait, observed, expected, reaped] =>
    #[if waitable error handler flags bit then 1 else 0,
      if groupSignal error handler flags bit previous errorWait observed expected reaped then 1 else 0]
  | _ => #[2]

/-- Selection compares the actual encoded observations, never a supplied verdict. -/
def cohortDemand (expected : String) (observed : Option String) (demand : Nat) :
    Option (Nat × String) :=
  if observed == some expected then some (demand, "explicit-cohort-request") else none

theorem cohort_mismatch (expected : String) (observed : Option String) (demand : Nat)
    (h : observed ≠ some expected) : cohortDemand expected observed demand = none := by
  simp [cohortDemand, h]

/-- Explicit source-bound requests are fixtures/configuration, not forecasts.
The noncryptographic fingerprint is a mismatch check, never input closure.
All absent/unsupported/mismatched inputs use a caller-specified positive
fallback. Duplicate or malformed entries fail configuration entirely. -/
def request (manifest : String) (source fingerprint : Option String) (fallback : Nat) (cohort : Option String := none) :
    Option (Nat × String) := do
  if fallback == 0 then none else do
    let mut selected := none
    let mut seen : List String := []
    for line in manifest.splitOn "\n" do
      if line == "" then continue
      let (path, digest, identity, demandText) ← match line.splitOn "\t" with
        | [path, digest, demand] => some (path, digest, none, demand)
        | [path, digest, "cohort-v1", identity, demand] =>
          if identity == "" || identity.utf8ByteSize > 65536 then none
          else some (path, digest, some identity, demand)
        | _ => none
      let demand ← demandText.toNat?
      if path == "" || digest == "" || demand == 0 || demand > 2^50 || seen.contains path then none
      else do
        seen := path :: seen
        if source == some path && fingerprint == some digest then
          match identity with
          | none => selected := some (demand, "explicit-source-request")
          | some expected => selected := cohortDemand expected cohort demand
    return match selected with
      | some pair => pair
      | none => (fallback, "explicit-unknown-fallback")

end BudgetAdapter
