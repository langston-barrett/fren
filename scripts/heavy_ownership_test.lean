import Heavy.Ownership
import Lean

/-! Test-only transport of decoded observations. It supplies no precomputed
ownership, freshness, charge or registry decision to the kernel. Each row
has one elapsed span, unlike the Python producer's two clock samples. -/

open Lean Heavy.Ownership

def monitor (j : Json) : Except String Monitor := do
  return ⟨← j.getObjValAs? Int "pid", ← j.getObjValAs? Int "start",
    ← j.getObjValAs? String "namespace"⟩

def optionalField (j : Json) (key : String) (decode : Json → Except String α) : Except String (Option α) := do
  match ← j.getObjVal? key with
  | .null => return none
  | x => return some (← decode x)

def timeSpan (j : Json) : Except String TimeSpan := do
  match ← j.getObjValAs? String "kind" with
  | "finite" => return .finite (← j.getObjValAs? Int "ticks")
  | "positiveInfinity" => return .positiveInfinity
  | "negativeInfinity" => return .negativeInfinity
  | "notANumber" => return .notANumber
  | _ => throw "unknown numeric span"

def report (span : TimeSpan) (j : Json) : Except String Report := do
  return ⟨⟨← j.getObjValAs? String "job_id", ← j.getObjValAs? Int "order"⟩,
    ← j.getObjValAs? Int "rss_kb", elapsedTimestamp span,
    ← optionalField j "monitor" monitor⟩

def victimRow (j : Json) : Except String VictimRow := do
  return ⟨← j.getObjValAs? (Option String) "job_id",
    ← j.getObjValAs? (Option Int) "order", ← j.getObjValAs? (Option Int) "rss_kb",
    ← j.getObjValAs? (Option Int) "legacy_rss_kb"⟩

def check (j : Json) : Except String Json := do
  if (← j.getObjValAs? String "kind") == "cleanup" then
    let cause ← match ← j.getObjValAs? String "cause" with
      | "memory" => pure CleanupCause.memorySample
      | "signal" => pure CleanupCause.externalSignal
      | "setup" => pure CleanupCause.setupFailure
      | "accounting" => pure CleanupCause.accountingFailure
      | _ => throw "unknown cleanup cause"
    let rows ← (← j.getObjValAs? (Array Json) "rows").toList.mapM victimRow
    return toJson (cleanupTrigger cause (← j.getObjValAs? Nat "cap")
      (← j.getObjValAs? Nat "rss") (← j.getObjValAs? (Option String) "own") rows)
  if (← j.getObjValAs? String "kind") == "group" then
    let wait ← match ← j.getObjValAs? String "wait" with
      | "pending" => pure GroupWait.pending
      | "exhausted" => pure GroupWait.exhausted
      | _ => throw "unknown wait observation"
    let probe ← match ← j.getObjValAs? String "probe" with
      | "missing" => pure GroupProbe.missing
      | "present" => pure GroupProbe.present
      | "denied" => pure GroupProbe.denied
      | _ => throw "unknown group probe"
    let subreaper ← j.getObjValAs? Bool "subreaper"
    let leader ← j.getObjValAs? Bool "leader"
    if (← j.getObjValAs? Bool "attempt") then
      return toJson (signalAttempt subreaper leader wait probe)
    return toJson (groupGone subreaper leader wait probe)
  if (← j.getObjValAs? String "kind") == "victim" then
    let rows ← (← j.getObjValAs? (Array Json) "rows").toList.mapM victimRow
    let (total, selected) := memoryVictim (← j.getObjValAs? Nat "cap") rows
    return .arr #[toJson total, toJson (selected.map (·.job))]
  if (← j.getObjValAs? String "kind") == "aggregate" then
    let ttl ← j.getObjValAs? Nat "ttl"
    let mut rows := []
    for item in (← j.getObjValAs? (Array Json) "rows") do
      if ← item.getObjValAs? Bool "locked" then
        let span ← item.getObjVal? "span" >>= timeSpan
        rows := rows ++ [⟨← optionalField item "report" (report span),
          ← item.getObjValAs? String "status_job", ← optionalField item "observed" monitor,
          ← item.getObjValAs? (Option Int) "legacy_rss"⟩]
    return toJson (admissionTotal (← j.getObjValAs? Nat "cap") rows 0 ttl)
  let span ← j.getObjVal? "span" >>= timeSpan
  let now : Int := 0
  if (← j.getObjValAs? String "kind") == "registry" then
    let r := registry (← j.getObjValAs? Bool "available") now
      (remainingDeadline span) (← j.getObjValAs? Bool "held")
      (← j.getObjValAs? Bool "requested")
    return .arr #[toJson r.acquired, toJson r.retry, toJson r.timedOut, toJson r.deferred]
  let ttl ← j.getObjValAs? Nat "ttl"
  if (← j.getObjValAs? String "kind") == "conversion" then
    let r : Report := ⟨⟨"", 1⟩, 0, elapsedTimestamp span, none⟩
    return .arr #[toJson (elapsedTimestamp span), toJson (remainingDeadline span),
      toJson (freshReport r 0 ttl),
      toJson (registry false 0 (remainingDeadline span) false false).timedOut]
  let row : Lease := ⟨← optionalField j "report" (report span),
    ← j.getObjValAs? String "status_job", ← optionalField j "observed" monitor,
    ← j.getObjValAs? (Option Int) "legacy_rss"⟩
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
