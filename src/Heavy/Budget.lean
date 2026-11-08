import Heavy.Ownership

/-! KiB reservation decisions for a single owned compiler session. These
functions do not prove locking, process identity or physical memory bounds. -/
namespace Heavy.Budget
open Heavy.Ownership

/-- A held but unknown row is an error, including after its monitor dies.
An unlocked row's stale or partially written metadata is irrelevant. -/
def charge (locked : Bool) (state ticket : Int) (row : Lease) : Option Int :=
  if !locked then some 0
  else match row.report, row.observed with
    | some r, some m =>
      if (state = 0 ∨ state = 1) ∧ ticket > 0 ∧ r.owner.sequence = ticket ∧
          r.rss > 0 ∧ m.pid > 0 ∧ m.start > 0 ∧ m.space ≠ "" ∧
          reportOwner row.report row.statusJob row.observed 0 0 then
        some (if state = 1 then r.rss else 0) else none
    | _, _ => none

/-- 0 wait, 1 admit, 2 malformed accounting, 3 intrinsically oversized.
Parent headroom is subtracted once; held excludes the waiting request. -/
def decision (allowance parent held demand ticket oldest : Int) : Int :=
  if allowance < 0 ∨ parent < 0 ∨ parent > allowance ∨ held < 0 ∨
      demand ≤ 0 ∨ ticket ≤ 0 ∨ oldest ≤ 0 then 2
  else if demand > allowance - parent then 3
  else if ticket = oldest ∧ held + demand ≤ allowance - parent then 1
  else 0

/-- Raw monotonic samples at actual lock/grant boundaries. Equality expires;
no promise is made about preemption after a successful sample. -/
def deadline (clockError now limit : Int) : Int :=
  if clockError ≠ 0 ∨ now < 0 ∨ limit < 0 then 2
  else if now < limit then 0 else 1

/-- Narrow Linux policy: only SIG_DFL without SA_NOCLDWAIT is supported.
`autoReapBit` is the actual OS bit constant (only 2 is supported); the
adapter supplies sa_flags. A different ABI fails closed. -/
def waitable (actionError handler flags autoReapBit : Int) : Bool :=
  decide (actionError = 0 ∧ handler = 0 ∧ flags ≥ 0 ∧ autoReapBit = 2 ∧
    flags / 2 % 2 = 0)

/-- Raw waitid si_pid (zero means pending), last waitpid result, and errors.
An earlier loss/error cannot be erased by a later successful observation. -/
def groupSignal (actionError handler flags autoReapBit previousWaitError waitError
    observed expected reaped : Int) : Bool :=
  waitable actionError handler flags autoReapBit &&
    decide (previousWaitError = 0 ∧ waitError = 0 ∧ expected > 0 ∧
      (observed = 0 ∨ observed = expected) ∧ reaped = 0)

/-- Only a completed, registry-locked snapshot can instantiate this bound. -/
theorem admitted_bound (a p h d t o : Int) (admitted : decision a p h d t o = 1) :
    0 ≤ p ∧ 0 ≤ h ∧ 0 < d ∧ p + h + d ≤ a := by
  unfold decision at admitted
  split at admitted <;> try contradiction
  split at admitted <;> try contradiction
  split at admitted <;> omega

end Heavy.Budget
