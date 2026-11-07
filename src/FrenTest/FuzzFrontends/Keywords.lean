-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A spec for `--keywords`: one block, a procedure's, a function's, a
trait method's or a global expectation's, with one clause written with the
other block's keyword (`assume` in a procedure's or a function's, `require`
in a global expectation's), alone or among parts that the block rejects,
before or after it: a modifier or a second result of a function's, an
`out` of another name or of the result again, `refines`, a claim, a call
or an `exists` in a function's block, a dotted name, a foreign operator,
or a clause without a label that is not a Boolean block; or, no error, one
that is, with a `where` or under a `let`.
No part is an error of Lean's grammar, which Lean would report instead
of any error of the block's: a `det` claim, or an evidence setting before
the `}`. Its static errors are on purpose, so it is a mode of its own, which
`lake test`'s corpus does not check; both front ends must report the same
first error of the block (`lang::block_errors`). `genKeywordsItem` now
and then writes an item of another kind before it, `genKeywordsGrammar`
puts an error of Lean's grammar in its item, and `genKeywordsTail` writes
the item after it. -/
def genKeywords : R String := do
  let block ← below 4
  let global := block == 3
  let wrong := if global then "require" else "assume"
  let clause ← match ← below 5 with
    | 0 => pure s!"{wrong} a: x > 0"
    | 1 => pure s!"{wrong} a: x > k where k := 1"
    | 2 => pure s!"{wrong} a: and \{ b: x > 0, c: x < 9 }"
    | 3 => pure s!"{wrong} and \{ b: x > 0 }"
    | _ => pure s!"{wrong} when x > 0, and \{ b: x < 9 }"
  -- Parts that the block rejects, or that are errors of their own syntax.
  let fnParts := #["out s := x", "out r := x\nout r := x", "refines c spec(x)", "expect e: x > 0",
    "cover g: x > 0", "call w := cb(x)", "exists z: Int", "det let z: Int := x", "ensure q: r == 1",
    "set_option fren.evidence \"random\" in", "let d.e: Int := x"]
  let procParts := #["out z := x", "ensure q: y == 1", "let d.e: Int := x",
    "set_option fren.evidence \"random\" in", "set_option fren.foo \"x\" in"]
  let globalParts := #["ensure q: x > 0", "out y := x", "expect q: x == 1", "let d.e: Int := x",
    "set_option fren.evidence \"random\" in"]
  let pool := if block == 3 then globalParts else if block == 0 then procParts else fnParts
  let mut before := #[]
  for _ in [0:← below 3] do before := before.push (← pick pool)
  -- After the clause, no evidence setting, which Lean's grammar would
  -- reject before the `}` and so before any check of the block.
  let mut after := #[]
  for _ in [0:← below 2] do
    let part ← pick pool
    unless part.startsWith "set_option" do after := after.push part
  -- A function's results: one, or with a modifier, a second, or a dotted
  -- name, the first's own error.
  let result ← match ← below 6 with
    | 0 => pure "det r: Int"
    | 1 => pure "r: Int, s: Int"
    | 2 => pure "r.a: Int, s: Int"
    | 3 => pure "set_option fren.evidence \"random\" in r: Int"
    | _ => pure "r: Int"
  -- Drawn after every other draw, so that a spec that has none is the one
  -- that the seed gave before: now and then, a clause without a label that
  -- is not a Boolean block, an error of its own syntax
  -- (`lang::clause_errors`), somewhere before the clause, with the block's
  -- keyword or the other's, under a leading `when` or with a `where`; or
  -- one that is a Boolean block with a `where` or under a `let`, no error.
  if ← chance 50 then
    let bareParts := if global then #["expect x > 0", "assume x > 0", "require x > 0", "ensure x > 0",
        "expect when x > 0, x < 9", "assume x > k where k := 1", "assume and { u: x > k } where k := 1"]
      else if block == 0 then #["ensure y = x", "require x > 0", "assume x > 0", "expect when x > 0, y = x",
        "ensure y = k where k := x", "require let m := 1 in and { u: x > m }"]
      else #["require x > 0", "assume x > 0", "ensure r = x", "require when x > 0, x < 9", "expect x > 0",
        "require and { u: x > k } where k := 1"]
    let bare ← pick bareParts
    let at_ ← below (before.size + 1)
    before := before.insertIdxIfInBounds at_ bare
  let members := before ++ #[clause] ++ after
  -- Each line of each member, at the indentation `ind`.
  let bodyAt (ind : String) := String.join (members.toList.flatMap fun m =>
    (m.splitOn "\n").map (ind ++ · ++ "\n"))
  let body := bodyAt "    "
  let decls := "pub proc cb(x: Int): (v: Int) { ensure e: v = x }\n" ++
    "pub proc spec(x: Int): (v: Int) { ensure e: v = x }\n"
  return decls ++ match block with
    | 0 => s!"\npub proc kw(x: Int): (y: Int) \{\n{body}    ensure r: y = x\n}\n"
    | 1 => s!"\npub fn kw(x: Int): ({result}) \{\n{body}}\n"
    | 2 => s!"\npub trait KwTrait \{\n    fn kw(s: Self, x: Int): ({result}) \{\n{bodyAt "        "}    }\n}\n"
    | _ => s!"\nexpect kw(x: Int) \{\n    call c := cb(x)\n{body}    expect z: c.v = x\n}\n"

/-- The item after `genKeywords`' block (`--keywords`), with messages of
its own, which neither front end may lose to the block's keyword error
(`lang::item_error`): now and then, a procedure with a name that
nothing declares (`F0201`), one with an unused parameter, one whose
expectation fails (`F0603`), or an application that may not meet a
function's precondition (`F0629`). It is drawn from a generator of its own
(`Mode.spec`), so that the block before it is the one that the seed gave
before. -/
def genKeywordsTail (block : String) : R String := do
  if !(← chance 75) then return ""
  -- An item that names the block's own, a procedure's or a function's,
  -- which its keyword error breaks.
  let names := if (block.splitOn "\npub proc kw(").length > 1 then
      #["\nproc kw_after(x: Int): (y: Int) {\n    call c := kw(x)\n    ensure r: y = c.y\n}\n"]
    else if (block.splitOn "\npub fn kw(").length > 1 then
      #["\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = kw(x)\n}\n"]
    else #[]
  pick (#["\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = x + missing\n}\n",
    "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = 1\n}\n",
    "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = x\n    expect e: y > 0\n}\n",
    "\nfn kw_pre(x: Int): (r: Int) {\n    require p: x > 0\n    out r := x\n}\n" ++
      "\nproc kw_after(x: Int): (y: Int) {\n    ensure r: y = kw_pre(x)\n}\n"] ++ names)

/-- An item of each kind that can hold clauses, with a clause written with
the other block's keyword in one of its members (`--keywords`,
`lang::item_error`): a procedure, a function, a global expectation, a
trait's method, procedure or expectation (a procedure being a member that
the trait does not take), a trait inside a trait, and a procedure under a
`set_option ... in`. The clause is labelled, a Boolean block without a
label, or under a leading `when`. It is drawn from a generator of its own
(`Mode.spec`), and goes before `genKeywords`' block. -/
def genKeywordsItem : R String := do
  if !(← chance 60) then return ""
  let kind ← below 8
  let global := kind == 2 || kind == 5
  let wrong := if global then "require" else "assume"
  let form ← pick #[s!"{wrong} ka: x > 0", s!"{wrong} and \{ ka: x > 0 }", s!"{wrong} when x > 0, and \{ kb: x < 9 }"]
  -- Each line of the item's member, at the indentation `ind`.
  let at_ (ind : String) := ind ++ form ++ "\n"
  return match kind with
    | 0 => s!"\npub proc kx(x: Int): (y: Int) \{\n{at_ "    "}    ensure r: y = x\n}\n"
    | 1 => s!"\npub fn kx(x: Int): (r: Int) \{\n{at_ "    "}    out r := x\n}\n"
    | 2 => s!"\nexpect kx(x: Int) \{\n{at_ "    "}    expect e: x >= 0\n}\n"
    | 3 => s!"\npub trait KxTrait \{\n    fn kx(s: Self, x: Int): (r: Int) \{\n{at_ "        "}        out r := x\n    }\n}\n"
    | 4 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    proc kx(x: Int): (y: Int) \{\n{at_ "        "}" ++
        "        ensure r: y = x\n    }\n}\n"
    | 5 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    expect kx(s: Self, x: Int) \{\n{at_ "        "}" ++
        "        expect e: kc(s) = kc(s)\n    }\n}\n"
    | 6 => s!"\npub trait KxTrait \{\n    fn kc(Self): Int\n    trait KxInner \{\n        fn kx(s: Self, x: Int): (r: Int) \{\n" ++
        s!"{at_ "            "}            out r := x\n        }\n    }\n}\n"
    | _ => s!"\nset_option fren.lint.unused_variables \"allow\" in\npub proc kx(x: Int): (y: Int) \{\n{at_ "    "}" ++
        "    ensure r: y = x\n}\n"

/-- An error of Lean's grammar later in `genKeywords`' item (`--keywords`),
which both front ends must report instead of any error of a clause's
keyword (`lang::item_error`): now and then, a member on a line of its own
before the block's `}`, or a clause written with the other block's keyword
whose Boolean block spans lines, with the grammar error inside. It is
drawn from a generator of its own (`Mode.spec`). `block` is the spec that
`genKeywords` gave. -/
def genKeywordsGrammar (block : String) : R String := do
  if !(← chance 30) then return block
  let global := (block.splitOn "\nexpect kw(").length > 1
  let trait := block.endsWith "    }\n}\n"
  let ind := if trait then "        " else "    "
  let wrong := if global then "require" else "assume"
  let lines ← pick #[s!"{ind}expect zz: x +\n",
    s!"{ind}{wrong} zz: and \{\n{ind}    zb: x +\n{ind}}\n",
    s!"{ind}{wrong} zz: and \{\n{ind}    zb: x > 0,\n{ind}    zc: x < (1\n{ind}}\n"]
  -- Before the `}` that closes the block: a method's, before the trait's.
  let close := if trait then "    }\n}\n" else "}\n"
  return (block.dropEnd close.length).toString ++ lines ++ close

end FrenTest.FuzzFrontends.Wide
