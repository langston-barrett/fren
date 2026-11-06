-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Preconditions in each form that a clause about the inputs takes
(`lang::precondition_word`): `require` in a procedure's block, labelled,
with a `where` clause, as a labelled `and` block, as an unlabelled one and
under a leading `when`, in a function's block, labelled or as an unlabelled
`and` block, alone, under a leading `when` or `let` or before a `where`, a
generic function's and a trait method's; and the
`assume` of a global expectation that calls the procedure, where the
preconditions hold. Its checks pass, and nothing here is a static error.
The procedure is checked by the solver: a global expectation over one
checked by random testing is a difference of its own (only the `fren`
command says what rests on it, `F0663`).
It is appended to specs of the corpus, so it is written from a grammar of
its own. -/
def requireForms : R String := do
  let low ← pick #["-3", "-1", "0"]
  let mut body := s!"    require n0: x > {low}\n"
  if ← chance 50 then body := body ++ "    require n1: y >= x - k where k := 2\n"
  if ← chance 50 then body := body ++ s!"    require n2: and \{ a: x > {low} - 1, b: y > -9 }\n"
  if ← chance 50 then body := body ++ "    require and { c: x != 3, d: b? or y > 0 }\n"
  if ← chance 50 then body := body ++ "    require when b?, and { e: y > 0 }\n"
  body := body ++ "    out r := x\n    ensure q: r = x\n"
  let mut out := s!"pub proc pw_proc(x: Int, y: Int, b?): (det r: Int) \{\n{body}}\n"
  if ← chance 60 then
    out := out ++ s!"\npub fn pw_fn(x: Int): (r: Int) \{\n    require p: x > {low}\n    out r := x + 1\n    ensure s: r > {low}\n}\n"
  if ← chance 50 then
    out := out ++ "\npub fn pw_generic<T>(q: Seq<T>, d: T): (r: T) {\n    require first: q != [] and q[0] = d\n    out r := d\n}\n"
  if ← chance 40 then
    out := out ++ "\npub trait PwTrait {\n    fn pw_method(s: Self, x: Int): (r: Int) {\n        require p: x > 0\n        ensure q: r >= 0\n    }\n}\n"
  if ← chance 60 then
    out := out ++ "\nexpect pw_global(x: Int, y: Int) {\n    assume big: x > 5 and y > x\n    call c := pw_proc(x, y, true)\n" ++
      "    expect e: c.r = x\n}\n"
  -- After every earlier draw, so that what the seed gave before stays: a
  -- function's preconditions without a label, a Boolean block, alone,
  -- under a leading `when` or `let`, or before a `where`, and an
  -- application that meets them.
  if ← chance 50 then
    let pre ← pick #[s!"require and \{ p: x > {low} }", s!"require when x > 0, and \{ p: x > {low} }",
      s!"require and \{ p: x > {low}, q: x > {low} - 1 }", s!"require and \{ p: x > k } where k := {low}",
      s!"require let m := {low} in and \{ p: x > m }"]
    out := out ++ s!"\npub fn pw_bare(x: Int): (r: Int) \{\n    {pre}\n    out r := x + 1\n}\n" ++
      "\nproc pw_bare_use(x: Int): (y: Int) {\n    require big: x > 5\n    ensure e: y = pw_bare(x)\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
