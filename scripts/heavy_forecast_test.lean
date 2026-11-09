import Heavy.Forecast
import Lean

/-! Test-only JSON transport for the pure kernel. Python supplies decoded
fields with exact integral timestamps; this is not a scheduler entry point. -/

open Lean Heavy.Forecast

-- Real completion rows: broad labels must not hide a command's last peak.
#guard predictionKey (some "lake test") "heavy" ==
  predictionKey (some "lake test") "another-label"
#guard predictionKey (some "lake test") "heavy" !=
  predictionKey (some "lake build fren-dev") "heavy"
#guard predictionKey none "lake test" != predictionKey (some "lake test") "heavy"
#guard predictionKey (some "bash -c 'lake test'") "heavy" !=
  predictionKey (some "bash -c 'lake build fren-dev'") "heavy"
#guard predict
  [{key := some (predictionKey (some "lake test") "heavy"), ended := some 1,
    peak := some 17911340}]
  (predictionKey (some "lake test") "heavy") 0 2 20 == (some 17911340, 1)
#guard predict
  [{key := some (predictionKey (some "/home/ubuntu/coord/out/fd-soft-overlap/phases/001-author-d29e0ab6-83f7-4138-914d-b7f457b0fac3/overlap-controls.sh") "test"), ended := some 1,
    peak := some 13566436}]
  (predictionKey (some "/home/ubuntu/coord/out/fd-soft-overlap/phases/001-author-d29e0ab6-83f7-4138-914d-b7f457b0fac3/overlap-controls.sh") "test") 0 2 20 == (some 13566436, 1)

-- Future module/input keys need no changes to the kernel.
#guard predict
  [{ key := some ("Module", "fingerprint"), ended := some 10, peak := some 7 },
   { key := some ("Module", "other-input"), ended := some 10, peak := some 999 }]
  ("Module", "fingerprint") 0 10 20 == (some 7, 1)

def observation (j : Json) : Observation String :=
  { event := (j.getObjValAs? String "event").toOption
    key := (j.getObjValAs? String "key").toOption
    ended := (j.getObjValAs? Int "ended").toOption
    peak := (j.getObjValAs? Int "peak").toOption }

def forecast (j : Json) : Except String Json := do
  let rows ← j.getObjValAs? (Array Json) "history"
  let key ← j.getObjValAs? String "key"
  let cutoff ← j.getObjValAs? Int "cutoff"
  let now ← j.getObjValAs? Int "now"
  let n ← j.getObjValAs? Nat "n"
  let (peak, jobs) := predict (rows.toList.map observation) key cutoff now n
  return toJson (peak, jobs)

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← IO.ofExcept (Json.parse line >>= forecast)
    output.putStrLn result.compress
