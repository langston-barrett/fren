import FrenTest.FuzzFrontends

/-!
# `lake exe fren_fuzz_frontends`

The fuzzer's entry point. The fuzzer itself is `FrenTest.FuzzFrontends`,
in a library, so that `lake test` can import it to check its fixed corpus
(`FrenTest.FuzzFrontends.corpus`).
-/

unsafe def main (args : List String) : IO UInt32 := FrenTest.FuzzFrontends.main args
