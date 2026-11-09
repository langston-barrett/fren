import Lean.Data.Json.Parser
import Heavy.CompilerForecast

namespace CompilerAdvice
open Lean Heavy.CompilerForecast

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def str (j : Json) (k : String) : Except String String := field j k >>= Json.getStr?
def nat (j : Json) (k : String) : Except String Nat := field j k >>= Json.getNat?
def strings (j : Json) : Except String (List String) := do
  return (← (← j.getArr?).mapM Json.getStr?).toList

/-- Missing optional identities remain absent; wrong types are errors. -/
def optional (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) := do
  match j.getObjVal? k with
  | .error _ => return none
  | .ok .null => return none
  | .ok v => return some (← f v)

/-- Nullable schema fields must still be present; absence is not a null. -/
def nullable (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) := do
  let value ← field j k
  if value.isNull then return none else return some (← f value)

def decode (j : Json) : Except String Record := do
  let schema ← nat j "schema"
  if schema != 2 && schema != 3 then throw "unsupported observation schema"
  let context : Context := {
    source := ← str j "source", cwd := ← str j "cwd"
    sourceFingerprint := ← str j "source_before", compiler := ← str j "real_compiler"
    compilerFingerprint := ← str j "compiler_fingerprint", version := ← str j "compiler_version"
    githash := ← str j "compiler_githash", args := ← strings (← field j "args")
    setup := ← nullable j "setup" Json.getStr?
    setupFingerprint := ← nullable j "setup_fingerprint" Json.getStr? }
  let gateError ← if schema == 3 then do pure (some (← nat j "gate_errno")) else pure none
  let childPresent ← if schema == 3 then do pure (some (← (← field j "child_present").getBool?)) else pure none
  let wrapperCode ← if schema == 3 then do pure (some (← nat j "wrapper_code")) else pure none
  return {
    context, schema, sourceAfter := ← str j "source_after"
    boot := ← optional j "boot_id" Json.getStr?, family := ← str j "family", kind := ← str j "input_kind"
    launchError := ← nat j "launch_errno", execError := ← nat j "exec_errno"
    waitError := ← nat j "wait_errno", clockError := ← nat j "clock_errno"
    status := ← nat j "raw_wait_status", pid := ← nat j "child_pid"
    gateError, childPresent, wrapperCode
    start := ← nat j "start_monotonic_ns", finish := ← nat j "end_monotonic_ns"
    rss := ← nat j "peak_rss_kib", measuredRss := ← nat j "measured_peak_rss_kib" }

end CompilerAdvice
