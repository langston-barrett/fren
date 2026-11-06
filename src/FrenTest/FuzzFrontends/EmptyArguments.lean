-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- `[]` and `{}` as methods' arguments, which take their element types
from their receivers (`Reqs/Lang/Expressions`): in one procedure, over
two to four sequences of `Int`, `Bool`, `String`, `Option<Int>` or `E` if
the spec has it, of sequences of them and of sets of them, each read
alone and then all of them in one expectation, so that the same `[]` is
typed against several element types in one check, as the hosted front
end's cache of the types of terms must not confuse (`typeOf`). A check
may fail, but nothing here is a static error. -/
def emptyArguments (sc : WScope) : R String := do
  let tys := #[("Int", "1"), ("Bool", "true"), ("String", "\"a\""), ("Option<Int>", "Option::Some(1)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0")] else #[])
  let mut params := #[]
  let mut atoms := #[]
  for k in [0:(← below 3) + 2] do
    let (t, v) ← pick tys
    let q := s!"ea{k}"
    let (ty, atom) ← match ← below 3 with
      | 0 => do
        let i ← below 2
        let a ← pick #[s!"{q}.starts_with?([])", s!"{q}.ends_with?([])", s!"{q}.contains?([])",
          s!"{q}.index_of([], {i}) >= 0", s!"{q}.replace([], [{v}]).len > {i}", s!"[] = {q}"]
        pure (s!"Seq<{t}>", a)
      | 1 => do
        let a ← pick #[s!"{q}.contains?([[]])", s!"{q}.starts_with?([[]])", s!"{q}.update(0, []) = {q}",
          s!"{q}.update(1, [{v}]).len = {q}.len", s!"{q}.ends_with?([[], [{v}]])"]
        pure (s!"Seq<Seq<{t}>>", a)
      | _ => do
        let a ← pick #[s!"{q}.update(0, \{}) = {q}", s!"{q}.update(1, \{}).len = {q}.len", s!"{q}.contains?([\{}])",
          s!"{q}.starts_with?([\{{v}}, \{}])"]
        pure (s!"Seq<Set<{t}>>", a)
    params := params.push s!"{q}: {ty}"
    atoms := atoms.push atom
  let body := String.join (atoms.toList.zipIdx.map fun (a, k) => s!"    expect xa{k}: {a}\n")
  return s!"pub proc empty_args({", ".intercalate params.toList}) \{\n{body}    expect xa_all: {" and ".intercalate atoms.toList}\n}\n"

end FrenTest.FuzzFrontends.Wide
