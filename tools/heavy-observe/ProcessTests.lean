import Heavy.Process
import Heavy.ModuleMemory

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
  let selected := "/source/FrenBase/Identity.lean"
  for (args, expected) in [([selected], true), (["-o", "--run", selected], true),
      (["--run", selected], false), (["--stdin", selected], false),
      (["--version", selected], false), ([selected, "--unsupported"], true),
      (["--setup", "--stdin", selected], true), (["-o"], true)] do
    unless Heavy.ModuleMemory.directFile args == expected do
      throw (IO.userError "raw direct compilation selection")
  for bytes in [0, 1, Heavy.ModuleMemory.defaultBytes, 2^50, 2^50+1] do
    unless Heavy.ModuleMemory.limit "/source" selected "file" bytes ==
        (if bytes == 0 || bytes > 2^50 then none else some bytes) do
      throw (IO.userError "selected memory configuration")
    for legacy in ["/source/FrenTestMain.lean", "/source/Impls/Lint.lean",
                   "/source/FrenBaseOther.lean", "/other/FrenBase/Identity.lean"] do
      unless Heavy.ModuleMemory.limit "/source" legacy "file" bytes == some 0 do
        throw (IO.userError "legacy memory configuration")
    for kind in ["query", "stdin"] do
      unless Heavy.ModuleMemory.limit "/source" selected kind bytes == some 0 do
        throw (IO.userError "query/stdin memory configuration")
  unless Heavy.ModuleMemory.limit "/source" selected "unknown" 1 == none do
    throw (IO.userError "ambiguous selected memory configuration")
  unless Heavy.ModuleMemory.applied 0 100 100 0 7 7 9 9 [0, 200, 80] == some (100, 80) do
    throw (IO.userError "raw applied/effective memory")
  for raw in [[1,100,100,0,7,7,9,9], [0,100,101,0,7,7,9,9],
              [0,100,100,1,7,7,9,9], [0,100,100,0,7,8,9,9],
              [0,100,100,0,7,7,9,10], [0,100,100,0,0,0,9,9]] do
    unless Heavy.ModuleMemory.applied raw[0]! raw[1]! raw[2]! raw[3]!
        raw[4]! raw[5]! raw[6]! raw[7]! [] == none do
      throw (IO.userError "raw memory acknowledgement rejection")
  for status in List.range 65536 do
    let r := result 0 0 0 status
    IO.println s!"{status} {r.kind} {r.detail} {r.shellCode}"
  unless result 5 2 9 0 == ⟨3, 5, 125⟩ do throw (IO.userError "launch precedence")
  unless result 0 2 9 0 == ⟨3, 9, 125⟩ do throw (IO.userError "wait precedence")
  unless result 0 2 0 0 == ⟨2, 2, 127⟩ do throw (IO.userError "exec error")
  unless elapsed 0 10 17 == some 7 do throw (IO.userError "elapsed")
  unless elapsed 0 17 10 == none do throw (IO.userError "reversed clock")
  unless elapsed 5 10 17 == none do throw (IO.userError "clock failure")
  unless requestExcess (some 10) (some 15) == some 5 &&
      requestExcess (some 10) (some 10) == some 0 &&
      requestExcess (some 10) (some 9) == some 0 &&
      requestExcess (some 0) (some 15) == none &&
      requestExcess none (some 15) == none &&
      requestExcess (some 10) none == none do
    throw (IO.userError "request excess")
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
