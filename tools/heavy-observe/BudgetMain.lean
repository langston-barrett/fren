import BudgetAdapter

@[extern "heavy_observe_read_regular"]
opaque readManifest (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

@[extern "heavy_budget_session"]
opaque session (path config requests exe : @& String) (args : @& Array String)
    (control : @& (Array UInt64 → Array UInt64)) : IO (Array UInt64)

/-- Development invocation: new absolute session directory, KiB allowance,
parent headroom, unknown fallback, wait milliseconds, manifest, --, command.
The command must remain in the owned process group (the tested Lake path). -/
def main (args : List String) : IO UInt32 := do
  try
    let path :: a :: p :: f :: w :: manifest :: "--" :: exe :: rest := args
      | throw (IO.userError "expected DIR ALLOWANCE_KIB PARENT_KIB FALLBACK_KIB WAIT_MS MANIFEST -- /absolute/command args...")
    unless (System.FilePath.mk path).isAbsolute && (System.FilePath.mk exe).isAbsolute do
      throw (IO.userError "session and command paths must be absolute")
    let some allowance := a.toNat? | throw (IO.userError "invalid allowance")
    let some parent := p.toNat? | throw (IO.userError "invalid headroom")
    let some fallback := f.toNat? | throw (IO.userError "invalid fallback")
    let some wait := w.toNat? | throw (IO.userError "invalid deadline")
    unless allowance ≤ 2^50 && parent ≤ allowance && fallback > 0 && fallback ≤ 2^50 &&
        wait > 0 && wait ≤ 600000 do throw (IO.userError "unsupported budget configuration")
    let some bytes ← readManifest manifest Heavy.Process.fingerprintAllowed
      | throw (IO.userError "unreadable request manifest")
    let some requests := String.fromUTF8? bytes | throw (IO.userError "invalid request manifest")
    if (BudgetAdapter.request requests none none fallback).isNone then
      throw (IO.userError "malformed request manifest")
    let raw ← session path s!"{allowance} {parent} {fallback} {wait}\n" requests exe rest.toArray BudgetAdapter.control
    if raw.size != 3 then throw (IO.userError "invalid session result")
    if raw[0]! != 0 || raw[2]! != 0 then
      IO.eprintln s!"heavy-budget: control errno={raw[0]!}; cleanup errno={raw[2]!}; command wait status={raw[1]!}"
      return 125
    let r := Heavy.Process.result 0 0 0 raw[1]!.toNat
    return r.shellCode.toUInt32
  catch e =>
    IO.eprintln s!"heavy-budget: {e}"
    return 125
