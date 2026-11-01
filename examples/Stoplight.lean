-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# A pedestrian crossing in Lean

A controller built from one `step` function, which an `impl` proves meets
the spec's `stoplight::step`, and the monitor `watch` beside it, which an
`impl` proves meets `stoplight::watch`. The spec checks one step at a time,
and a fixed-length chain of them; the theorems here say what it can't,
about every sequence of events from the start: every state reached is
valid; a press while nobody walks is served within `MIN_GREEN + YELLOW`
ticks, whatever is pressed meanwhile; every walk starts after `MIN_GREEN`
ticks of green; and the phases shown are a run of the abstract machine
`stoplight::cycle`, through every intermediate phase. Each follows from a
lemma that serves any step function: for an invariant, for a property of
every step, for a ranking function, and for a simulation.
-/

open Fren.Lang

-- The spec, in its module `stoplight`.
#fren_md "stoplight.fren"

#fren_check

namespace Stoplight

open stoplight

/-- One step of the controller. -/
def step (s : State) : Event → State
  | .Press => { s with waiting? := decide (s.people = .DontWalk) }
  | .Tick =>
    if s.timer > 1 then { s with timer := s.timer - 1 }
    else match s.cars with
      | .Green => if s.waiting? then { s with cars := .Yellow, timer := YELLOW } else s
      | .Yellow => { cars := .Red, people := .Walk, waiting? := false, timer := WALK }
      | .Red => { s with cars := .Green, people := .DontWalk, timer := MIN_GREEN }

-- `step` is the spec's procedure, resolved from the spec's module, `stoplight`.
impl step_meets: step for (s : State) (e : Event) {
  now := s, event := e, next := Stoplight.step s e
} by
  intro s e h
  obtain ⟨cars, people, waiting, timer⟩ := s
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.step, ht, if_true, if_false] <;>
    simp_all [fren_spec] <;> omega

/-! ## Lemmas for any step function -/

section Generic

variable {σ α ε : Type} (step : σ → ε → σ)

/-- An invariant that every step keeps holds after any sequence of events. -/
theorem foldl_invariant (inv : σ → Prop) (keeps : ∀ s e, inv s → inv (step s e)) :
    ∀ (es : List ε) (s : σ), inv s → inv (es.foldl step s)
  | [], _, h => h
  | e :: es, s, h => foldl_invariant inv keeps es (step s e) (keeps s e h)

/-- A property of each step from a state with the invariant holds of every
step of every sequence of events: of the step by `e` after `es`. -/
theorem foldl_every_step (inv : σ → Prop) (keeps : ∀ s e, inv s → inv (step s e))
    (p : σ → ε → σ → Prop) (each : ∀ s e, inv s → p s e (step s e)) (s : σ) (h : inv s) (es : List ε) (e : ε) :
    p (es.foldl step s) e ((es ++ [e]).foldl step s) := by
  rw [List.foldl_append]
  exact each _ e (foldl_invariant step inv keeps es s h)

/-- A ranking function: from a state with `p`, each step either reaches
`goal` or keeps `p`, and each step that `tick` holds of lowers `rank` by one
or more, while the others never raise it. Then `goal` comes within `rank s`
ticks, at the end of some prefix of the events, whatever the others are. -/
theorem foldl_reaches (p goal : σ → Prop) (rank : σ → Int) (tick : ε → Bool)
    (positive : ∀ s, p s → 0 < rank s)
    (moves : ∀ s e, p s → goal (step s e) ∨
      (p (step s e) ∧ rank (step s e) ≤ rank s - (if tick e then 1 else 0))) :
    ∀ (es : List ε) (s : σ), p s → rank s ≤ es.countP tick →
      ∃ n ≤ es.length, goal ((es.take n).foldl step s)
  | [], s, h, hr => by have := positive s h; simp at hr; omega
  | e :: es, s, h, hr => by
    rcases moves s e h with hg | ⟨hp, hle⟩
    · exact ⟨1, by simp, by simpa using hg⟩
    · have hc : rank (step s e) ≤ es.countP tick := by
        rw [List.countP_cons] at hr; split at hle <;> simp_all <;> omega
      obtain ⟨n, hn, hg⟩ := foldl_reaches p goal rank tick positive moves es (step s e) hp hc
      exact ⟨n + 1, by simp; omega, by simpa using hg⟩

/-- `IsRun r as es`: the abstract states `as` follow one another by `r`,
under the events `es`, one step for each. -/
inductive IsRun (r : α → ε → α → Prop) : List α → List ε → Prop
  | last (a : α) : IsRun r [a] []
  | step {a b : α} {as : List α} {e : ε} {es : List ε} :
    r a e b → IsRun r (b :: as) es → IsRun r (a :: b :: as) (e :: es)

/-- Where each step from a state with the invariant `inv` is a step of `r`
on the states' images under `abs`, the images of all the states that a
sequence of events passes through are a run of `r`. -/
theorem scanl_simulates (inv : σ → Prop) (keeps : ∀ s e, inv s → inv (step s e))
    (abs : σ → α) (r : α → ε → α → Prop) (sim : ∀ s e, inv s → r (abs s) e (abs (step s e))) :
    ∀ (es : List ε) (s : σ), inv s → IsRun r ((es.scanl step s).map abs) es
  | [], s, _ => by simpa using IsRun.last (abs s)
  | e :: es, s, h => by
    have ih := scanl_simulates inv keeps abs r sim es (step s e) (keeps s e h)
    cases es with
    | nil => simpa using IsRun.step (sim s e h) (IsRun.last _)
    | cons e' es' => simp only [List.scanl_cons, List.map_cons] at ih ⊢; exact IsRun.step (sim s e h) ih

end Generic

/-! ## The controller -/

/-- The spec's invariant, the subset type `Lights`, as `stoplight::step`
assumes it of its state; the event and the rest do not matter. -/
def Valid (s : State) : Prop := stoplight.step.assumes s .Tick s false

/-- A step keeps the invariant: the guarantees of `stoplight::step` start
with the invariant of its result. -/
theorem step_valid (s : State) (e : Event) (h : Valid s) : Valid (step s e) := by
  obtain ⟨_, _, ⟨hinv, _⟩⟩ := step_meets s e h
  exact hinv

theorem start_valid : Valid START := by simp [Valid, fren_spec]

/-- Every state reachable from `START` is valid. -/
theorem reachable_valid (es : List Event) : Valid (es.foldl step START) :=
  foldl_invariant step Valid step_valid es START start_valid

/-! ### A press is served in time -/

/-- Someone is waiting, and nobody walks. -/
def Waiting (s : State) : Prop := Valid s ∧ s.waiting? = true ∧ s.people = .DontWalk

/-- The step of `stoplight::prompt`: the wait is positive, and each step
either brings the walk or keeps someone waiting, a press with the same wait
and a tick with one less. -/
theorem step_prompt (s : State) (e : Event) (h : Waiting s) :
    0 < wait s ∧ ((step s e).people = .Walk ∨
      (Waiting (step s e) ∧ wait (step s e) ≤ wait s - (if e = .Tick then 1 else 0))) := by
  obtain ⟨hv, hw, hp⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨cars, people, waiting, timer⟩ := s
    simp only [Valid, fren_spec, decide_eq_true_eq] at hv
    cases cars <;> simp [wait] at hv hp ⊢ <;> first | omega | simp_all
  · by_cases hpw : (step s e).people = .Walk
    · exact .inl hpw
    · refine .inr ⟨⟨step_valid s e hv, ?_⟩, ?_⟩ <;>
      obtain ⟨cars, people, waiting, timer⟩ := s <;>
      cases e <;> cases cars <;> cases people <;> cases waiting <;>
        by_cases ht : 1 < timer <;> simp only [Stoplight.step, ht, if_true, if_false] at hpw ⊢ <;>
        simp_all [Valid, fren_spec, wait] <;> omega

/-- A press while nobody walks, at any state reachable from `START`, is
served within `MIN_GREEN + YELLOW` ticks, whatever is pressed meanwhile:
the walk comes at the end of some prefix of any later events with that
many ticks. -/
theorem press_served (before after : List Event) (h : (before.foldl step START).people = .DontWalk)
    (enough : MIN_GREEN + YELLOW ≤ after.countP (· = .Tick)) :
    ∃ n ≤ after.length, ((after.take n).foldl step (step (before.foldl step START) .Press)).people = .Walk := by
  have hv := step_valid _ .Press (reachable_valid before)
  have hw : Waiting (step (before.foldl step START) .Press) := by
    refine ⟨hv, ?_, ?_⟩ <;> simp [Stoplight.step, h]
  have bound : wait (step (before.foldl step START) .Press) ≤ MIN_GREEN + YELLOW := by
    obtain ⟨⟨_, _, ht⟩, -, hp⟩ := hw
    revert ht hp
    generalize step (before.foldl step START) .Press = s
    obtain ⟨cars, people, waiting, timer⟩ := s
    cases cars <;> simp_all [fren_spec, wait] <;> omega
  refine foldl_reaches step Waiting (·.people = .Walk) wait (· = .Tick)
    (fun s h => (step_prompt s .Tick h).1) (fun s e h => ?_) after _ hw (by omega)
  rcases (step_prompt s e h).2 with hg | ⟨hp, hle⟩
  · exact .inl hg
  · exact .inr ⟨hp, by cases e <;> simp_all⟩

/-! ## The monitor -/

/-- One step of the monitor: the controller's step, and the ticks of green
since the last walk. -/
def watch (w : Watch) (e : Event) : Watch :=
  { lights := step w.lights e
    green_ticks :=
      if (step w.lights e).people = .Walk then 0
      else if e = .Tick ∧ w.lights.cars = .Green then w.green_ticks + 1
      else w.green_ticks }

-- `watch` is the spec's procedure, its call of `step` the Lean `step`.
impl watch_meets: watch for (w : Watch) (e : Event) {
  now := w, event := e, next := Stoplight.watch w e
} by
  intro w e h
  obtain ⟨l, hd, he⟩ := step_meets w.lights e h.1.1
  refine ⟨w.lights, e, step w.lights e, l, ?_, ⟨rfl, rfl⟩, hd, h.1.1, he⟩
  have hl := he.1
  clear hd he
  obtain ⟨⟨cars, people, waiting, timer⟩, ticks⟩ := w
  simp only [fren_spec, decide_eq_true_eq] at h hl ⊢
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.watch, Stoplight.step, ht, if_true, if_false] at hl ⊢ <;>
    simp_all <;> omega

/-- The spec's invariant `Watched`, as `stoplight::watch` assumes it. -/
def Watched (w : Watch) : Prop := stoplight.watch.assumes w .Tick w w.lights .Tick w.lights false

theorem watch_watched (w : Watch) (e : Event) (h : Watched w) : Watched (watch w e) := by
  obtain ⟨_, _, _, _, ⟨hinv, _⟩, _⟩ := watch_meets w e h
  exact hinv

theorem watch_start_watched : Watched WATCH_START := by simp [Watched, fren_spec]

/-- The step of `stoplight::green_between_walks`. -/
theorem step_enough_green (w : Watch) (e : Event) (h : Watched w)
    (starts : w.lights.people = .DontWalk ∧ (watch w e).lights.people = .Walk) :
    MIN_GREEN ≤ w.green_ticks := by
  obtain ⟨⟨cars, people, waiting, timer⟩, ticks⟩ := w
  simp only [Watched, fren_spec, decide_eq_true_eq] at h
  revert starts h
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.watch, Stoplight.step, ht, if_true, if_false] <;>
    simp_all <;> omega

/-- In every sequence of events from `WATCH_START`, each walk starts only
after `MIN_GREEN` ticks of green since the last one, or since the start. -/
theorem green_between_walks (es : List Event) (e : Event)
    (starts : (es.foldl watch WATCH_START).lights.people = .DontWalk ∧
      ((es ++ [e]).foldl watch WATCH_START).lights.people = .Walk) :
    MIN_GREEN ≤ (es.foldl watch WATCH_START).green_ticks :=
  foldl_every_step watch Watched watch_watched
    (fun w _ w' => w.lights.people = .DontWalk ∧ w'.lights.people = .Walk → MIN_GREEN ≤ w.green_ticks)
    (fun w e h => step_enough_green w e h) WATCH_START watch_start_watched es e starts

/-- The monitor's controller is the controller: it sees the same states. -/
theorem watch_lights (es : List Event) (w : Watch) : (es.foldl watch w).lights = es.foldl step w.lights := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih => exact ih (watch w e)

/-! ## The abstract machine -/

/-- Each step is a step of the abstract machine on the phases. -/
theorem step_cycles (s : State) (e : Event) (h : Valid s) :
    stoplight.cycle.ensures (phase s) e (phase (step s e)) := by
  obtain ⟨cars, people, waiting, timer⟩ := s
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.step, ht, if_true, if_false] <;>
    simp_all [fren_spec, phase]

/-- The phases of all the states that a sequence of events from `START`
passes through, the first and the last included, are a run of the
abstract machine. -/
theorem reachable_cycles (es : List Event) :
    IsRun stoplight.cycle.ensures ((es.scanl step START).map phase) es :=
  scanl_simulates step Valid step_valid phase _ step_cycles es START start_valid

end Stoplight
