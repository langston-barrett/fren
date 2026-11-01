-- keep-sorted start
import FrenCli.Verdicts
import Impls.Check
import Reqs.Eval
-- keep-sorted end
open Fren.Lang

/-!
# The evaluator's decisions (`Reqs/Eval`)

The decisions in `FrenCli.Verdicts` implement the comps of `eval`: for
whatever the search and the evaluator found, the status, verdict, exit code
or confirmation is as required. Each obligation is proved by `decide`, or,
over a number of tests, by cases on whether there were any.
-/

namespace Fren.Impls

open Fren.Core (CheckKind Verdict)
open FrenCli.Eval (Status Confirmation Unreached UnreachedWarning statusOf evalExit reached counted triggerUnknown unreachedOf unreachedWarning testVerdict
  confirmation confirmedVerdict)

def toStatus : Status → eval.Status
  | .Inadmissible => .Inadmissible
  | .Violates => .Violates
  | .Meets => .Meets

instance : Fren.Finite Status := ⟨[.Inadmissible, .Violates, .Meets], by intro x; cases x <;> simp⟩

impl status_of: eval::status for (a i r : Bool) {
  assumes? := a,
  insts? := i,
  guarantees? := r,
  status := toStatus (statusOf a i r),
} by
  intro a i r _
  cases a <;> cases i <;> cases r <;> decide

/-- A status as `eval::eval_exit` sees it: an unknown one is not `Meets`. -/
def toStatus? : Option Status → eval.Status
  | some s => toStatus s
  | none => .Violates

impl eval_exit_code: eval::eval_exit for (ran complete : Bool) (s : Option Status) (ef : Bool) {
  ran? := ran,
  complete? := complete,
  status := toStatus? s,
  expect_false? := ef,
  code := (evalExit ran complete s ef).toNat,
} by
  intro ran complete s ef _
  cases ran <;> cases complete <;> cases ef <;> rcases s with _ | _ | _ | _ <;> decide

impl reaches_check: eval::reaches for (f h : Bool) (t v : Option Bool) {
  found? := f,
  has_trigger? := h,
  trigger := t,
  value := v,
  reached? := reached f h t v,
  counted? := counted f h t,
  trigger_unknown? := triggerUnknown f h t,
} by
  intro f h t v _
  cases f <;> cases h <;> rcases t with _ | _ | _ <;> rcases v with _ | _ | _ <;> decide

def toUnreached : Unreached → eval.Unreached
  | .Reached => .Reached
  | .Untested => .Untested
  | .Untriggered => .Untriggered
  | .Valueless => .Valueless
  | .TriggerValueless => .TriggerValueless

def toUnreachedWarning : UnreachedWarning → eval.UnreachedWarning
  | .Silent => .Silent
  | .Untriggered => .Untriggered
  | .Valueless => .Valueless
  | .TriggerValueless => .TriggerValueless

instance : Fren.Finite Unreached := ⟨[.Reached, .Untested, .Untriggered, .Valueless, .TriggerValueless], by intro x; cases x <;> simp⟩

-- Over the numbers of tests: only which are zero matters.
impl unreached_of: eval::unreached for (f t u d : Nat) {
  found := f,
  triggered := t,
  unknown := u,
  decided := d,
  why := toUnreached (unreachedOf f t u d),
} by
  intro f t u d h
  simp only [fren_spec, unreachedOf] at *
  by_cases hd : d > 0 <;> by_cases hf : f = 0 <;> by_cases ht : t = 0 <;> by_cases hu : u < t <;>
    simp_all [toUnreached] <;> omega

-- From the impl of its call: only why no test reached the check matters.
impl unreached_warning_of: eval::unreached_warning for (f t u d v : Nat) (un c : Bool) {
  found := f,
  triggered := t,
  unknown := u,
  decided := d,
  valued := v,
  untested? := un,
  assumption? := c,
  shown := toUnreachedWarning (unreachedWarning f t u d v un c),
} by
  intro f t u d v un c h
  have hu := unreached_of f t u d h.1
  simp only [fren_spec] at *
  refine ⟨f, t, u, d, toUnreached (unreachedOf f t u d), ?_, ⟨rfl, rfl, rfl, rfl⟩, h.1, hu⟩
  simp only [unreachedWarning]
  by_cases hv : v = 0 <;>
    cases unreachedOf f t u d <;> cases un <;> cases c <;> simp_all [toUnreached, toUnreachedWarning]

-- Over the number of tests, so `decide` does not apply: only whether
-- there were any matters.
impl test_verdict_of: eval::test_verdict for (k : CheckKind) (refuted : Bool) (n : Nat) (x : Bool) {
  kind := toCheckKind k,
  refuted? := refuted,
  n_tests := n,
  exhausted? := x,
  verdict := toVerdict (testVerdict k refuted n x),
} by
  intro k refuted n x _
  rcases n with _ | n
  · cases k <;> cases refuted <;> cases x <;> decide
  · have : n + 1 > 0 := Nat.succ_pos n
    cases k <;> cases refuted <;> cases x <;> simp_all [fren_spec, testVerdict, toVerdict, toCheckKind] <;> first | omega | decide

def toConfirmation : Confirmation → eval.Confirmation
  | .Confirmed => .Confirmed
  | .Refuted => .Refuted
  | .Undecided => .Undecided

instance : Fren.Finite Confirmation := ⟨[.Confirmed, .Refuted, .Undecided], by intro x; cases x <;> simp⟩

impl confirm_model: eval::confirm for (h g a : Bool) {
  hyp_false? := h,
  goal_true? := g,
  all_known? := a,
  result := toConfirmation (confirmation h g a),
} by
  intro h g a _
  cases h <;> cases g <;> cases a <;> decide

impl confirmed: eval::confirmed_verdict for (v : Verdict) (c : Confirmation) {
  solver := toVerdict v,
  result := toConfirmation c,
  verdict := toVerdict (confirmedVerdict v c),
} by
  intro v c _
  cases v <;> cases c <;> decide

/-! ## Backjumping

The search's conflict sets are `Nat`s, bit `j` for the variable at
position `j` (`FrenCli.Eval.conflictOf`). -/

open FrenCli.Eval (conflictOf resumesAt)

/-- The set of the positions of `cs` that are `true`. -/
def bitsOf : List Bool → Nat
  | [] => 0
  | b :: cs => b.toNat + 2 * bitsOf cs

theorem bitsOf_eq_zero (cs : List Bool) : bitsOf cs = 0 ↔ true ∉ cs := by
  induction cs with
  | nil => simp [bitsOf]
  | cons b cs ih =>
    cases b
    · simp [bitsOf]; rw [← ih]; omega
    · simp [bitsOf]

theorem testBit_bitsOf (cs : List Bool) (n : Nat) : (bitsOf cs).testBit n = cs.getD n false := by
  induction cs generalizing n with
  | nil => simp [bitsOf]
  | cons b cs ih =>
    cases n with
    | zero => cases b <;> simp [bitsOf, Nat.testBit_zero] <;> omega
    | succ n =>
      rw [Nat.testBit_succ]
      have : (b.toNat + 2 * bitsOf cs) / 2 = bitsOf cs := by cases b <;> simp <;> omega
      simp only [bitsOf, this, ih]
      simp

theorem bitsOf_lt (cs : List Bool) (n : Nat) : bitsOf cs < 2 ^ (n + 1) ↔ true ∉ cs.drop (n + 1) := by
  induction cs generalizing n with
  | nil => simp [bitsOf]; exact Nat.pow_pos (by omega)
  | cons b cs ih =>
    cases n with
    | zero =>
      have := bitsOf_eq_zero cs
      cases b <;> simp [bitsOf] <;> rw [← this] <;> omega
    | succ n =>
      have h := ih n
      have : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
      rw [List.drop_succ_cons, ← h, this]
      cases b <;> simp [bitsOf] <;> omega

/-- A slice from just after `n` to the end is the rest of the list. -/
theorem slice_rest (cs : List Bool) (n : Nat) (h : n < cs.length) :
    ((Fren.Seq.ofList cs).slice ((n : Int) + 1) (cs.length : Int)).toList = cs.drop (n + 1) := by
  unfold Fren.Seq.slice
  by_cases h' : n + 1 < cs.length
  · rw [if_pos (by simp; omega)]
    simp
    exact List.take_of_length_le (by simp)
  · rw [if_neg (by simp; omega)]
    simp [List.drop_eq_nil_of_le (by omega : cs.length ≤ n + 1)]

theorem testBit_foldl_or (e : Nat) (rs : List Nat) (n : Nat) :
    (rs.foldl (· ||| ·) e).testBit n = (e.testBit n || rs.any (·.testBit n)) := by
  induction rs generalizing e with
  | nil => simp
  | cons r rs ih => simp [ih, Nat.testBit_or, Bool.or_assoc]

/-- The set of `j` alone if `b`, else the empty set. -/
def bitIf (j : Nat) (b : Bool) : Nat := if b then 2 ^ j else 0

theorem testBit_bitIf (j : Nat) (b : Bool) : (bitIf j b).testBit j = b := by
  cases b <;> simp [bitIf, Nat.testBit_two_pow_self]

theorem member_conflictOf (i j : Nat) (e : Bool) (rs : List Bool) :
    (conflictOf i (bitIf j e) (rs.map (bitIf j))).testBit j = (decide (j < i) && (e || true ∈ rs)) := by
  have : rs.any ((fun x => x.testBit j) ∘ bitIf j) = decide (true ∈ rs) := by
    induction rs with
    | nil => simp
    | cons r rs ih => cases r <;> simp_all [testBit_bitIf]
  simp [conflictOf, Nat.testBit_mod_two_pow, testBit_foldl_or, testBit_bitIf, this]

-- For every position of the variable and of an earlier one, over whether
-- each rejection reads the earlier one.
impl conflict_of: eval::conflict for (i : Nat) (j : Int) (e : Bool) (rs : List Bool) {
  position := i,
  earlier := j,
  equated? := e,
  rejections := Fren.Seq.ofList rs,
  member? := decide (0 ≤ j) && (conflictOf i (bitIf j.toNat e) (rs.map (bitIf j.toNat))).testBit j.toNat,
} by
  intro i j e rs _
  simp [fren_spec, member_conflictOf]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, by omega⟩, h2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨h0, by omega, h2⟩

-- At every position, over every conflict set: the search resumes at the
-- last member, as `resumesAt` decides from the bits.
impl backjump_at: eval::backjump for (cs : List Bool) (k : Int) {
  conflict := Fren.Seq.ofList cs,
  k := k,
  resumes? := decide (0 ≤ k) && resumesAt (bitsOf cs) k.toNat,
} by
  intro cs k _
  simp [fren_spec]
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp only [Int.toNat_natCast, resumesAt, testBit_bitsOf, Bool.and_eq_true, decide_eq_true_eq, bitsOf_lt]
    by_cases hn : n < cs.length
    · rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hn), slice_rest cs n hn]
      simp [hn, List.getD_eq_getElem?_getD]
    · have : cs.getD n false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : cs.length ≤ n)]
      simp only [this]
      constructor
      · intro h
        simp at h
      · rintro ⟨⟨_, _⟩, _⟩
        omega
  · simp [hk]

trusted eval::sound: "a counterexample from testing is a behaviour that the evaluator found to meet the component and to falsify the check, so it is genuine if the evaluator is right; `fren check` passes such a check only on an `Unsat` answer, which comes with no model to confirm, so this rests on the solver and Fren's translation being sound on `Unsat`, which is trusted, not checked"

end Fren.Impls
