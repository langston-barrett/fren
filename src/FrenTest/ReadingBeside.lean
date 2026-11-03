-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-! A test of what `FrenCli.elaborateReading` rests on: the elaborator's
type arguments of each file's applications of generic functions
(`State.callTargs`), as they are once that file is elaborated, are those
of the whole spec, as far as lowering the file reads them. Lowering a file
looks up only the type arguments of the file being lowered
(`Eval.elaboratedArgs`), so they agree if the elaborator records a file's
only while it elaborates that file, and changes none of them later. -/

namespace FrenTest.ReadingBeside

open FrenCli

/-- The type arguments of file `file`'s applications, by where each
starts, in order. -/
def ofFile (callTargs : Std.HashMap (Nat × Nat) (Array Fren.Core.Ty)) (file : Nat) : Array (Nat × Array Fren.Core.Ty) :=
  (callTargs.fold (init := #[]) fun acc (f, start) targs => if f == file then acc.push (start, targs) else acc)
    |>.qsort (·.1 < ·.1)

/-- For the files `files`, whose contents are `srcs`, the files whose
applications' type arguments, as they are after each, differ from those of
the whole spec, each with a failure, and how many files have any. -/
def disagreements (files srcs : Array String) : IO (Array String × Nat) := do
  let (_, states, final) ← elaborateSourcesBefore files srcs #[]
  let mut failures := #[]
  let mut withAny := 0
  for path in files, k in [0:files.size] do
    let after := ofFile (states[k + 1]?.getD {}).callTargs k
    let whole := ofFile final.callTargs k
    if !whole.isEmpty then withAny := withAny + 1
    unless after.size == whole.size && (after.zip whole).all fun (a, b) => a.1 == b.1 && a.2 == b.2 do
      failures := failures.push
        s!"{path}: the type arguments of its applications after it ({after.size}) differ from those of the whole spec ({whole.size})"
  if let some d := final.diags.find? (·.severity == .error) then
    failures := failures.push s!"{files[d.file]?.getD "?"}: a static error: {d.msg.headline}"
  return (failures, withAny)

/-- Two files, each of which applies a generic function of the first, at
several instances, so that both files have type arguments. -/
def generics : Array (String × String) := #[
  ("lib.fren", "pub mod lib

pub fn first<T>(a: T, b: T): T := if a = b then b else a

pub fn wrap<T>(x: T): Option<T> := Option::Some(x)

pub fn both?(n: Int, b?) := first(n, n) = n and first(b?, b?) = b?
"),
  ("client.fren", "mod client
use lib::{first, wrap}

proc uses(n: Int, b?): (det y: Int) {
    out y := first(n, 0)
    expect w: wrap(b?) = Option::Some(b?) and wrap(y) != Option::None
}
")]

/-- The type arguments agree for `generics`, where both files have some,
and for the files `own`, Fren's own requirements, where more than one
file has some. -/
def agree (own : Array String) : IO (Array String) := do
  let (failures, withAny) ← disagreements (generics.map (·.1)) (generics.map (·.2))
  let failures := if withAny == 2 then failures else
    failures.push s!"in the two files of `generics`, {withAny} have type arguments, not both"
  let srcs ← own.mapM fun (path : String) => IO.FS.readFile path
  let (failures', withAny) ← disagreements own srcs
  let failures' := if withAny ≥ 2 then failures' else
    failures'.push s!"in Fren's own requirements, {withAny} files have type arguments, which tests little"
  return failures ++ failures'

end FrenTest.ReadingBeside
