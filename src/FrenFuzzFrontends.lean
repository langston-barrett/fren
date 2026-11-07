-- keep-sorted start
import FrenTest.ExpansionFuzz
import FrenTest.FuzzFrontends.Main
-- keep-sorted end

/-!
# `lake exe fren_fuzz_frontends`

The fuzzer's entry point. The fuzzer itself is `FrenTest.FuzzFrontends`,
in a library, so that `lake test` can import it to check its fixed corpus
(`FrenTest.FuzzFrontends.corpus`).

`--copying COUNT` checks an independent stream of copying constructs,
including refinement locals. Short workers keep the hosted environments
of a long run from accumulating, as the ordinary fuzzer's workers do.
-/

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--copying", count] =>
    let some count := count.toNat? | IO.eprintln "expected --copying COUNT"; return 2
    let mut start := 0
    while start < count do
      let size := min 25 (count - start)
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := #["--copying-worker", toString size, toString start] }
      let code ← child.wait
      if code != 0 then return code
      start := start + size
      if start % 250 == 0 then IO.eprintln s!"copying corpus: {start}/{count}"
    IO.println s!"copying corpus: all {count} specs agree"
    return 0
  | ["--copying-worker", count, start] =>
    let some count := count.toNat? | return 2
    let some start := start.toNat? | return 2
    let failures ← FrenTest.ExpansionFuzz.run count start
    for failure in failures do IO.eprintln failure
    return if failures.isEmpty then 0 else 1
  | _ => FrenTest.FuzzFrontends.main args
