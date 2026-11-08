import BudgetAdapter

open Heavy.Budget Heavy.Ownership

def check (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)

def main : IO Unit := do
  for allowance in [-1, 0, 9, 10] do
    for parent in [-1, 0, 1, 11] do
      for held in [-1, 0, 2, 7, 9] do
        for demand in [-1, 0, 2, 7, 10] do
          let r := decision allowance parent held demand 2 2
          check (r != 1 || (0 ≤ parent && 0 ≤ held && 0 < demand && parent + held + demand ≤ allowance)) "raw budget bound"
  check (decision 10 1 7 2 2 2 == 1) "unequal fit"
  check (decision 10 1 7 7 2 2 == 0) "no fit"
  check (decision 10 1 0 10 2 2 == 3) "oversize"
  check (decision 10 11 0 1 2 2 == 2) "headroom underflow"
  check (decision 10 1 0 2 2 1 == 0) "FIFO"
  let m : Monitor := ⟨10, 50, "boot:namespace"⟩
  let r : Report := ⟨⟨"compiler", 1⟩, 7, -999999, some m⟩
  let row : Lease := ⟨some r, "compiler", some m, none⟩
  check (charge true 1 1 row == some 7) "raw stale holder retains reservation"
  check (charge true 1 1 {row with observed := some {m with start := 51}} == none) "PID reuse"
  check (charge true 1 1 {row with observed := none} == none) "unknown cannot be zero"
  check (charge false 1 1 {row with report := none} == some 0) "unlocked metadata"
  check ((BudgetAdapter.request "" none none 9) == some (9, "explicit-unknown-fallback")) "missing request fallback"
  check ((BudgetAdapter.request "source\tfp\t2\n" (some "source") (some "fp") 9) == some (2, "explicit-source-request")) "source request"
  check ((BudgetAdapter.request "source\tfp\t2\n" (some "source") (some "changed") 9) == some (9, "explicit-unknown-fallback")) "mismatch fallback"
  for bad in ["source\tfp\t0\n", "source\tfp\t-1\n", "source\tfp\t2\nsource\tfp\t3\n", "partial"] do
    check ((BudgetAdapter.request bad none none 9).isNone) "malformed request"
  for raw in [#[], #["10 1 1 0"], #["10 11 1 2"], #["10 1 1 2", "partial"]] do
    check ((BudgetAdapter.snapshot raw)[0]! == 2) "malformed snapshot"
  for error in [0, 5] do
    for now in [-1, 0, 9, 10, 11] do
      check (deadline error now 10 == (if error != 0 || now < 0 then 2 else if now < 10 then 0 else 1)) "raw deadline"
  for handler in [0, 1, 42] do
    for flags in [0, 2, 4, 6] do
      check (waitable 0 handler flags 2 == (handler == 0 && flags / 2 % 2 == 0)) "raw disposition"
  check (groupSignal 0 0 0 2 0 0 0 10 0) "pending anchor"
  check (groupSignal 0 0 0 2 0 0 10 10 0) "unreaped exited anchor"
  for previous in [0, 10] do
    for error in [0, 4, 10] do
      for observed in [0, 10, 11] do
        for reaped in [0, 10] do
          check (groupSignal 0 0 0 2 previous error observed 10 reaped ==
            (previous == 0 && error == 0 && (observed == 0 || observed == 10) && reaped == 0)) "raw wait lifecycle"
  check (!groupSignal 0 1 0 2 0 0 0 10 0) "ignored disposition"
  check (!groupSignal 0 0 2 2 0 0 0 10 0) "automatic reap"
  check (!groupSignal 5 0 0 2 0 0 0 10 0) "sigaction error"
  check (!groupSignal 0 0 0 2 0 0 0 0 0) "no child"
  check (!waitable 0 0 0 4) "unsupported signal ABI"
  check (BudgetAdapter.control #[0, 0, 10, 10] == #[1]) "deadline callback contract"
  check (BudgetAdapter.control #[1, 0, 0, 0, 2, 10, 0, 10, 10, 0] == #[1, 0]) "lifecycle callback contract"
  for canonical in [none, some "/source"] do
    for fingerprint in [none, some "observed"] do
      let observed := sourceIdentity canonical fingerprint
      check (observed == (canonical, if canonical.isSome then fingerprint else none)) "source identity normalization"
      if canonical.isNone then
        check (BudgetAdapter.request "/source\tobserved\t2\n" observed.1 observed.2 9 ==
          some (9, "explicit-unknown-fallback")) "canonicalization failure reaches positive fallback"
  IO.println "budget raw inputs passed"
