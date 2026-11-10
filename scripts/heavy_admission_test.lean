import Heavy.Admission
import Lean

/-! Test-only transport of admission inputs. It supplies no precomputed
start, class, order or turn decision to the kernel: times, memory and load
arrive as the integers the Python scheduler read. -/

open Lean Heavy.Admission

def waiter (j : Json) : Except String Waiter := do
  return ⟨← j.getObjValAs? Int "sequence", ← j.getObjValAs? (Option String) "label",
    ← j.getObjValAs? Int "enqueued", ← j.getObjValAs? Int "updated",
    ← j.getObjValAs? Int "slots", ← j.getObjValAs? Int "cap",
    ← j.getObjValAs? (Option Int) "limit"⟩

def check (j : Json) : Except String Json := do
  match ← j.getObjValAs? String "kind" with
  | "start" =>
    return toJson (canStart (← j.getObjValAs? (Option Int) "rss") (← j.getObjValAs? Int "cap")
      (← j.getObjValAs? Int "waited") (← j.getObjValAs? Int "grace")
      (← j.getObjValAs? (Option Int) "limit") (← j.getObjValAs? (Option Int) "load"))
  | "class" =>
    let label ← j.getObjValAs? (Option String) "label"
    let c := classOf label
    return Json.mkObj [("label", c.label), ("rank", toJson c.rank), ("nice", toJson c.nice),
      ("weight", toJson (weightToWrite label (← j.getObjValAs? Bool "writable")
        (← j.getObjValAs? Nat "outsiders")))]
  | "turn" =>
    let own ← waiter (← j.getObjVal? "own")
    let others ← (← j.getObjValAs? (Array Json) "others").toList.mapM waiter
    let slot ← j.getObjValAs? Int "slot"
    let rss ← j.getObjValAs? (Option Int) "rss"
    let load ← j.getObjValAs? (Option Int) "load"
    let now ← j.getObjValAs? Int "now"
    let ttl ← j.getObjValAs? Int "ttl"
    let grace ← j.getObjValAs? Int "grace"
    let step ← j.getObjValAs? Int "step"
    return Json.mkObj [
      ("before", toJson (others.map (before · own step))),
      ("contends", toJson (others.map (contends · slot rss load now ttl grace))),
      ("ahead", toJson (ahead own others slot rss load now ttl grace step)),
      ("turn", toJson (turn own others slot rss load now ttl grace step))]
  | _ => throw "unknown kind"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← IO.ofExcept (Json.parse line >>= check)
    output.putStrLn result.compress
