import Std

/-! Bounded historical memory forecasts. This kernel depends only on Std;
requirements and log decoding depend on it, never the reverse. -/

namespace Heavy.Forecast

/-- Complete command keys cannot collide with legacy kind-only keys. -/
def predictionKey (command : Option String) (kind : String) : Bool × String :=
  match command with
  | some c => (true, c)
  | none => (false, kind)

/-- An observation's forecast fields. Decoders use `none` for missing or
malformed fields; a missing log event defaults to `some "job"`. Times
and the cutoff share one integral unit. -/
structure Observation (Key : Type) where
  event : Option String := some "job"
  key : Option Key := none
  ended : Option Int := none
  peak : Option Int := none
  /-- The record shows that the job did not exit with status 0. A record
  with no status, as old logs have, is not known to have failed. -/
  failed : Bool := false
  deriving Repr

/-- Completion time and measured peak, ordered newest first. -/
abbrev Peaks := List (Int × Int)

/-- Failed jobs remain usable as lower bounds; eligibility depends on these
fields alone. -/
def eligible [DecidableEq Key] (o : Observation Key) (key : Key) (cutoff now : Int) : Bool :=
  decide (o.event = some "job" ∧ o.key = some key) &&
    match o.ended, o.peak with
    | some t, some p => decide (cutoff ≤ t ∧ t ≤ now ∧ p > 0)
    | _, _ => false

/-- At most `n` entries of a descending history. -/
def take (n : Nat) : Peaks → Peaks
  | [] => []
  | (t, p) :: rest => if n = 0 then [] else (t, p) :: take (n - 1) rest

/-- Insert into a bounded descending history, with peak as the tie breaker.
This has the same selection as Python's bounded `(ended, peak)` min-heap. -/
def insert (t p : Int) (n : Nat) : Peaks → Peaks
  | [] => if n = 0 then [] else [(t, p)]
  | (u, q) :: rest => if n = 0 then []
      else if t > u ∨ (t = u ∧ p ≥ q) then (t, p) :: take (n - 1) ((u, q) :: rest)
      else (u, q) :: insert t p (n - 1) rest

/-- Select by completion time rather than log order, including both cutoff
endpoints. Retain at most `n` entries throughout the traversal. -/
def recent [DecidableEq Key] (history : List (Observation Key)) (key : Key)
    (cutoff now : Int) (n : Nat) : Peaks :=
  match history with
  | [] => []
  | o :: rest =>
    let ps := recent rest key cutoff now n
    match o.ended, o.peak with
    | some t, some p => if eligible o key cutoff now then insert t p n ps else ps
    | _, _ => ps

/-- An empty usable history is unknown, never zero. -/
def maximum : Peaks → Option Int
  | [] => none
  | (_, p) :: rest => match maximum rest with
    | none => some p
    | some q => some (max p q)

/-- Whether some eligible job is not known to have failed. A failed job's
peak shows only how far it got: a test that fails before it starts its
compiler says nothing about the memory a full run needs. -/
def finished [DecidableEq Key] (history : List (Observation Key)) (key : Key)
    (cutoff now : Int) : Bool :=
  match history with
  | [] => false
  | o :: rest => (eligible o key cutoff now && !o.failed) || finished rest key cutoff now

/-- The latest eligible job not known to have failed, selected as `recent`
selects: none, or that one job. -/
def latestFinished [DecidableEq Key] (history : List (Observation Key)) (key : Key)
    (cutoff now : Int) : Peaks :=
  match history with
  | [] => []
  | o :: rest =>
    let ps := latestFinished rest key cutoff now
    match o.ended, o.peak with
    | some t, some p => if eligible o key cutoff now && !o.failed then insert t p 1 ps else ps
    | _, _ => ps

/-- A forecast is never below the floor, when there is one. -/
def raise (prediction floor : Option Int) : Option Int :=
  match prediction, floor with
  | none, _ => none
  | some m, none => some m
  | some m, some f => some (max m f)

/-- The forecast from a selection `ps` and the latest finished job `ok`.
Without a finished job in the window the peaks are lower bounds only, so the
forecast is unknown and uses no jobs. With one, the forecast is never below
the latest finished job's peak, however many later failures fill the
selection; failed jobs' peaks can only raise it. -/
def forecast (seen : Bool) (ok ps : Peaks) : Option Int × Nat :=
  if seen then (raise (maximum ps) (maximum ok), ps.length) else (none, 0)

/-- The frozen forecast and its sample count. Limits and keys are caller
policy; the legacy scheduler uses 20 samples of one job kind in seven days. -/
def predict [DecidableEq Key] (history : List (Observation Key)) (key : Key)
    (cutoff now : Int) (n : Nat) : Option Int × Nat :=
  forecast (finished history key cutoff now) (latestFinished history key cutoff now)
    (recent history key cutoff now n)

end Heavy.Forecast
