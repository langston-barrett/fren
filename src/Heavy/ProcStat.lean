import Std

/-! What one `/proc/<pid>/stat` sample shows. Reading and splitting the file
remain adapter responsibilities. This module depends only on Std, never on
Fren or its requirements. -/

namespace Heavy.ProcStat

inductive Sample where
  /-- The process is gone, as if its stat file no longer existed. -/
  | vanished
  /-- The sample is not a usable reading of a process. -/
  | rejected
  /-- A live process or a zombie, with its counters. -/
  | process
  deriving Repr, BEq, DecidableEq

/-- State X is a process that was reaped and that the kernel is releasing.
It has no parent, group or session left (0, -1, -1), so the state decides
before any counter is judged. A zombie (state Z) is a process until it is
reaped, and keeps its final counters. -/
def sample (state : String) (pid parent group session user system start pages : Int) : Sample :=
  if state = "X" then .vanished
  else if pid ≤ 0 ∨ parent < 0 ∨ group < 0 ∨ session < 0 ∨ user < 0 ∨ system < 0 ∨
      start < 0 ∨ pages < 0 then .rejected
  else .process

end Heavy.ProcStat
