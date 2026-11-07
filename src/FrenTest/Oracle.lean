-- keep-sorted start
import FrenCore.Str
-- keep-sorted end

/-! # Guards against vacuous test oracles (`testing::oracle_count`,
`testing::oracle_output`, `testing::oracle_tool`)

These return failures, rather than a Boolean that a caller could discard
while reporting its other failures. `Impls.Testing` proves their verdicts.
-/

namespace FrenTest.Oracle

/-- Keep every prior failure and require a positive floor of observations. -/
def finish (name : String) (compared floor : Nat) (failures : Array String) : Array String :=
  if floor == 0 || compared < floor then
    failures.push (if floor == 0 then s!"{name}: observation floor must be positive"
      else s!"{name}: only {compared} observations, need at least {floor}")
  else failures

/-- A tool must write something and must not report an internal error,
even alongside otherwise usable output. -/
def outputFailures (out : String) : Array String :=
  if out == "" || out.contains "internal error" then
    #["oracle: empty output or internal error"]
  else #[]

/-- A subprocess must succeed as well as supply usable output. -/
def toolFailures (out err : String) (exit : Nat) : Array String :=
  let failures := if err.contains "internal error" then
    (outputFailures out).push "oracle: internal error on stderr" else outputFailures out
  if exit != 0 then failures.push s!"oracle: tool exited {exit}"
  else failures

theorem finish_isEmpty (name : String) (compared floor : Nat) (failures : Array String) :
    (finish name compared floor failures).isEmpty =
      (failures.isEmpty && decide (0 < floor) && decide (floor ≤ compared)) := by
  simp only [finish]
  split <;> simp_all <;> omega

end FrenTest.Oracle
