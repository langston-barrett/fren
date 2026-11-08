import Heavy.Process

open Heavy.Process

-- Exhaustive raw 16-bit wait-status transport, compared to Python's OS macros.
@[extern "heavy_observe_read_regular"]
opaque readRegular (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

-- The direct reader mode tests the same FFI implementation and eligibility
-- function used at every runtime fingerprint call site.
def main (args : List String) : IO Unit := do
  if args.head? == some "--read" then
    let bytes ← readRegular args[1]! fingerprintAllowed
    IO.println (bytes.map (fun b => s!"some:{hash b}") |>.getD "none")
    return
  for status in List.range 65536 do
    let r := result 0 0 0 status
    IO.println s!"{status} {r.kind} {r.detail} {r.shellCode}"
  unless result 5 2 9 0 == ⟨3, 5, 125⟩ do throw (IO.userError "launch precedence")
  unless result 0 2 9 0 == ⟨3, 9, 125⟩ do throw (IO.userError "wait precedence")
  unless result 0 2 0 0 == ⟨2, 2, 127⟩ do throw (IO.userError "exec error")
  unless elapsed 0 10 17 == some 7 do throw (IO.userError "elapsed")
  unless elapsed 0 17 10 == none do throw (IO.userError "reversed clock")
  unless elapsed 5 10 17 == none do throw (IO.userError "clock failure")
  unless usage 0 0 0 15 7 8 99 == some (15, 99) do throw (IO.userError "signal usage")
  unless usage 0 2 0 0 7 8 99 == none do throw (IO.userError "exec usage")
  unless usage 0 0 5 0 7 8 99 == none do throw (IO.userError "wait usage")
  unless usage 0 0 0 127 7 8 99 == none do throw (IO.userError "nontermination usage")
  for mode in [0, 4096, 8192, 16384, 32768, 33188, 49152] do
    for bytes in [0, 67108864, 67108865] do
      unless fingerprintAllowed mode bytes == ((mode == 32768 || mode == 33188) && bytes ≤ 67108864) do
        throw (IO.userError "fingerprint raw mode/size")
  unless (parseMetadata ["--run", "Main.lean", "-o", "data", "Other.lean"]).map (·.source) == some (some "Main.lean") do
    throw (IO.userError "run metadata")
  unless (parseMetadata ["Main.lean", "-o", "old", "-o", "new"]).map (·.olean) == some (some "new") do
    throw (IO.userError "last setting")
  unless (parseMetadata ["--stdin", "Label.lean"]).map (·.source) == some none do
    throw (IO.userError "stdin disk source")
  unless parseMetadata ["--olean=out.lean"] == none do throw (IO.userError "unsupported metadata")
  for source in [none, some "", some "source"] do
    for toolchain in [none, some "", some "compiler"] do
      for closure in [none, some "", some "closure"] do
        let expected := source == some "source" && toolchain == some "compiler" && closure == some "closure"
        unless identityComplete source toolchain closure == expected do
          throw (IO.userError "identity parts")
