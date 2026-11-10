-- keep-sorted start
import Fren.Impl
import Heavy.Admission
import Reqs.Testing
-- keep-sorted end
open Fren.Lang

/-! The Std-only admission kernel, bound to heavy's admission requirements.
These proofs establish conformance of the Lean functions, not their use by
the Python scheduler, which `scripts/heavy_admission_test.py` compares with
them. Each output is inventoried in `test/impl_paths.txt`. -/

namespace Fren.Impls.HeavyAdmission

open Heavy.Admission

def priority : Class → testing.PriorityClass
  | .mainRepair => .MainRepair
  | .criticalPath => .CriticalPath
  | .mergeBlocking => .MergeBlocking
  | .editLoop => .EditLoop
  | .exploratory => .Exploratory

def waiter (w : Waiter) : testing.Waiter :=
  ⟨w.sequence, w.label, w.enqueued, w.updated, w.slots, w.cap, w.limit⟩

def waiters : List Waiter → testing.Waiters
  | [] => .Nil
  | w :: ws => .Cons (waiter w) (waiters ws)

theorem start_eq (rss : Option Int) (cap waited grace : Int) (limit load : Option Int) :
    testing.start_allowed? rss cap waited grace limit load =
      canStart rss cap waited grace limit load := by
  cases rss <;> cases limit <;> cases load <;>
    simp [testing.start_allowed?, canStart, Prelude.Option.some.x0]

impl start: testing::heavy_start
    for (rss : Option Int) (cap waited grace : Int) (limit load : Option Int) {
  rss := rss,
  cap := cap,
  waited := waited,
  grace := grace,
  limit := limit,
  load := load,
  start? := canStart rss cap waited grace limit load,
} by
  intro rss cap waited grace limit load _
  show _ ↔ _
  rw [start_eq]

theorem class_eq (label : Option String) :
    testing.priority_class label = priority (classOf label) := by
  simp only [testing.priority_class, classOf]
  repeat' split
  all_goals rfl

theorem rank_eq (c : Class) : testing.priority_rank (priority c) = c.rank := by
  cases c <;> rfl

theorem nice_eq (c : Class) : testing.priority_nice (priority c) = c.nice := by
  cases c <;> rfl

theorem weight_eq (c : Class) : testing.priority_weight (priority c) = c.weight := by
  cases c <;> rfl

impl priority_class: testing::heavy_priority_class for (label : Option String) {
  label := label,
  priority := priority (classOf label),
  rank := (classOf label).rank,
} by
  intro label _
  simp [fren_spec, class_eq, rank_eq]

impl cpu_weight: testing::heavy_cpu_weight
    for (label : Option String) (writable : Bool) (outsiders : Nat) (other : Option String) {
  label := label,
  writable? := writable,
  outsiders := outsiders,
  other := other,
  nice := (classOf label).nice,
  weight := weightToWrite label writable outsiders,
} by
  intro label writable outsiders other _
  simp [fren_spec, class_eq, nice_eq, weight_eq, weightToWrite]

theorem key_eq (w : Waiter) (step : Int) : testing.queue_key (waiter w) step = key w step := by
  simp only [testing.queue_key, waiter, key, class_eq]
  cases classOf w.label <;> simp [priority, Class.rank] <;> omega

theorem before_eq (a b : Waiter) (step : Int) :
    testing.queue_before? (waiter a) (waiter b) step = before a b step := by
  simp only [testing.queue_before?, key_eq, before]
  simp [waiter]

impl queue_order: testing::heavy_queue_order for (first second : Waiter) (step : Nat) {
  first := waiter first,
  second := waiter second,
  step := step,
  before? := before first second step,
} by
  intro first second step _
  show _ ↔ _
  rw [before_eq]

theorem contends_eq (w : Waiter) (slot : Int) (rss : Option Int) (load : Option Int)
    (now ttl grace : Int) :
    testing.queue_contends? (waiter w) slot rss load now ttl grace =
      contends w slot rss load now ttl grace := by
  have h := start_eq rss w.cap (now - w.enqueued) grace w.limit load
  simp only [testing.queue_contends?, contends]
  simp [waiter, h]

theorem ahead_eq (own : Waiter) (others : List Waiter) (slot : Int) (rss : Option Int)
    (load : Option Int) (now ttl grace step : Int) :
    testing.queue_ahead (waiter own) (waiters others) slot rss load now ttl grace step =
      ahead own others slot rss load now ttl grace step := by
  induction others with
  | nil => simp [waiters, testing.queue_ahead, ahead]
  | cons w rest ih =>
    simp only [waiters, testing.queue_ahead, ahead, ih, contends_eq, before_eq]
    simp

impl queue_turn: testing::heavy_queue_turn
    for (own : Waiter) (others : List Waiter) (slot : Int) (rss : Option Int)
        (load : Option Int) (now : Int) (ttl grace step : Nat) {
  own := waiter own,
  others := waiters others,
  slot := slot,
  rss := rss,
  load := load,
  now := now,
  ttl := ttl,
  grace := grace,
  step := step,
  ahead := ahead own others slot rss load now ttl grace step,
  turn? := turn own others slot rss load now ttl grace step,
} by
  intro own others slot rss load now ttl grace step _
  simp [fren_spec, ahead_eq, turn]

end Fren.Impls.HeavyAdmission
