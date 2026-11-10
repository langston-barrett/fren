import Std

/-! Pure decisions for whole-job admission: the start rule besides the slot
lock, the priority class of a job, its CPU share, and whose turn it is among
the waiting jobs. Reading the waiter registry, the load, the clock and the
cgroup files, and every syscall, remain adapter responsibilities. This
module depends only on Std, never on Fren or its requirements. -/

namespace Heavy.Admission

/-- Admission besides the slot lock. `rss` is the charged memory of the
running jobs, `none` when the registry gave no total; memory is never
waived. A load limit binds only until `grace`, and a missing load reading
lets the job start. `waited` and `grace` share one unit, and so do `limit`
and `load`: the adapter scales both exactly to integers. -/
def canStart (rss : Option Int) (cap waited grace : Int) (limit load : Option Int) : Bool :=
  (match rss with
    | some used => decide (5 * used ≤ 3 * cap)
    | none => false) &&
  (match limit with
    | none => true
    | some bound => decide (waited ≥ grace) ||
      (match load with
        | none => true
        | some reading => decide (reading < bound)))

/-- Why a job runs, most urgent first. The order of constructors is the
order of admission. -/
inductive Class where
  | mainRepair | criticalPath | mergeBlocking | editLoop | exploratory
  deriving Repr, BEq, DecidableEq

/-- The class a caller's label names. A missing or unknown label is
exploratory, so that a misspelt label never jumps the queue. -/
def classOf (label : Option String) : Class :=
  if label = some "main-repair" then .mainRepair
  else if label = some "critical-path" then .criticalPath
  else if label = some "merge-blocking" then .mergeBlocking
  else if label = some "edit-loop" then .editLoop
  else .exploratory

def Class.label : Class → String
  | .mainRepair => "main-repair"
  | .criticalPath => "critical-path"
  | .mergeBlocking => "merge-blocking"
  | .editLoop => "edit-loop"
  | .exploratory => "exploratory"

def Class.rank : Class → Int
  | .mainRepair => 0
  | .criticalPath => 1
  | .mergeBlocking => 2
  | .editLoop => 3
  | .exploratory => 4

/-- The niceness heavy gives the job's processes. Never negative: heavy
runs unprivileged. -/
def Class.nice : Class → Int
  | .mainRepair => 0
  | .criticalPath => 2
  | .mergeBlocking => 4
  | .editLoop => 7
  | .exploratory => 10

/-- The cgroup v2 `cpu.weight` of a job's own cgroup; the kernel's default
is 100 and its range 1 to 10000. -/
def Class.weight : Class → Int
  | .mainRepair => 250
  | .criticalPath => 160
  | .mergeBlocking => 100
  | .editLoop => 50
  | .exploratory => 25

/-- The weight to write, if any. The cgroup's weight is the job's to set
only when heavy may write it and no process outside the job shares the
cgroup; `outsiders` counts those. -/
def weightToWrite (label : Option String) (writable : Bool) (outsiders : Nat) : Option Int :=
  if writable ∧ outsiders = 0 then some (classOf label).weight else none

/-- One waiting job, as it published itself. Times are on one machine-wide
monotonic clock, in one unit. `slots`, `cap` and `limit` are the settings
it waits under, which may differ between callers. -/
structure Waiter where
  sequence : Int
  label : Option String
  enqueued : Int
  updated : Int
  slots : Int
  cap : Int
  limit : Option Int
  deriving Repr

/-- The virtual deadline that orders the queue: each class step costs
`step` of waiting. A waiter's key never changes, so every later arrival of
any class eventually sorts behind it. -/
def key (w : Waiter) (step : Int) : Int :=
  (classOf w.label).rank * step + w.enqueued

/-- Strict queue order: the key, then the enqueue sequence. -/
def before (a b : Waiter) (step : Int) : Bool :=
  key a step < key b step || (decide (key a step = key b step) && a.sequence < b.sequence)

/-- Whether `w` could take slot `slot` now: it still heartbeats, the slot is
one of its slots, and the start rule holds under its own settings. A waiter
that cannot start holds nobody back. -/
def contends (w : Waiter) (slot : Int) (rss : Option Int) (load : Option Int)
    (now ttl grace : Int) : Bool :=
  decide (0 ≤ now - w.updated ∧ now - w.updated ≤ ttl) && decide (slot < w.slots) &&
    canStart rss w.cap (now - w.enqueued) grace w.limit load

/-- The number of other waiters that go first. -/
def ahead (own : Waiter) (others : List Waiter) (slot : Int) (rss : Option Int)
    (load : Option Int) (now ttl grace step : Int) : Int :=
  match others with
  | [] => 0
  | w :: rest =>
    (if contends w slot rss load now ttl grace && before w own step then 1 else 0) +
      ahead own rest slot rss load now ttl grace step

/-- A waiter may claim the slot when nobody goes first. -/
def turn (own : Waiter) (others : List Waiter) (slot : Int) (rss : Option Int)
    (load : Option Int) (now ttl grace step : Int) : Bool :=
  ahead own others slot rss load now ttl grace step == 0

theorem ahead_nonneg (own : Waiter) (others : List Waiter) (slot : Int) (rss : Option Int)
    (load : Option Int) (now ttl grace step : Int) :
    0 ≤ ahead own others slot rss load now ttl grace step := by
  induction others with
  | nil => simp [ahead]
  | cons w rest ih => simp only [ahead]; split <;> omega

/-- The order is irreflexive and asymmetric: two waiters never each yield
to the other. -/
theorem before_asymm (a b : Waiter) (step : Int) : before a b step = true → before b a step = false := by
  intro h
  have h' : key a step < key b step ∨ (key a step = key b step ∧ a.sequence < b.sequence) := by
    simpa [before] using h
  have goal : ¬ (key b step < key a step ∨ (key b step = key a step ∧ b.sequence < a.sequence)) := by
    omega
  cases hb : before b a step
  · rfl
  · exact absurd (by simpa [before] using hb) goal

/-- No starvation: a waiter that has queued for more than four class steps
precedes every newcomer, whatever their classes. -/
theorem aged_first (a b : Waiter) (step : Int) (hstep : 0 ≤ step)
    (h : a.enqueued + 4 * step < b.enqueued) : before a b step = true := by
  have ha : (classOf a.label).rank * step ≤ 4 * step := by
    cases (classOf a.label) <;> simp [Class.rank] <;> omega
  have hb : 0 ≤ (classOf b.label).rank * step := by
    cases (classOf b.label) <;> simp [Class.rank] <;> omega
  simp only [before, key, Bool.or_eq_true, decide_eq_true_eq]
  left; omega

end Heavy.Admission
