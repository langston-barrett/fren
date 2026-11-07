import Heavy.Ownership
import Lean

/-! Test-only transport of decoded observations. It supplies no precomputed
ownership, freshness, charge or registry decision to the kernel. -/

open Lean Heavy.Ownership

def monitor (j : Json) : Except String Monitor := do
  return ⟨← j.getObjValAs? Int "pid", ← j.getObjValAs? Int "start",
    ← j.getObjValAs? String "namespace"⟩

def optionalField (j : Json) (key : String) (decode : Json → Except String α) : Except String (Option α) := do
  match ← j.getObjVal? key with
  | .null => return none
  | x => return some (← decode x)

def report (j : Json) : Except String Report := do
  return ⟨⟨← j.getObjValAs? String "job_id", ← j.getObjValAs? Int "order"⟩,
    ← j.getObjValAs? Int "rss_kb", ← j.getObjValAs? Int "updated_monotonic",
    ← optionalField j "monitor" monitor⟩

def check (j : Json) : Except String Json := do
  let now ← j.getObjValAs? Int "now"
  if (← j.getObjValAs? String "kind") == "registry" then
    let r := registry (← j.getObjValAs? Bool "available") now
      (← j.getObjValAs? Int "deadline") (← j.getObjValAs? Bool "held")
      (← j.getObjValAs? Bool "requested")
    return .arr #[toJson r.acquired, toJson r.retry, toJson r.timedOut, toJson r.deferred]
  let row : Lease := ⟨← optionalField j "report" report,
    ← j.getObjValAs? String "status_job", ← optionalField j "observed" monitor,
    ← j.getObjValAs? (Option Int) "legacy_rss"⟩
  let ttl ← j.getObjValAs? Nat "ttl"
  let r := lease (← j.getObjValAs? Nat "cap") (← j.getObjValAs? Bool "locked") row now ttl
  return .arr #[toJson (reportOwner row.report row.statusJob row.observed now ttl),
    toJson r.live, toJson r.admission, toJson r.eviction]

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← IO.ofExcept (Json.parse line >>= check)
    output.putStrLn result.compress
