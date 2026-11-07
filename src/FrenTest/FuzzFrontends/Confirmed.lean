-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A spec of what the confirmation of models evaluates (`--confirm`,
`Reqs/Models#known-values`): `div` and `mod` by a literal, positive or
negative; an index in an argument that a function's body never reads,
which leaves the application unknown out of range
(`model::known_application`); tables that may take no
row, or whose last row is a condition or `true`; `match`es over an integer
and over enumerations, exhaustive or not, by or-patterns and over one
variant, with binders read in a body or a guard, and in a function's body;
`match`es of several scrutinees and tables over one, a binder as the
whole arm, an or-pattern with a `_` alternative, `let` and `is`;
and the rules that know more than `lang::eval`: a count with an argument
that may be unknown, spelled out too, through a function and against a
constant, and an `if`, a `match` and a table whose condition or scrutinee
may be, with branches, arms or rows equal or not. A mode of its own, so
that the specs of the other modes' seeds are as they were. No value of an
abstract type or of a type parameter, which the Lean-hosted front end does
not evaluate. Appended cases put tables, guarded matches and indexes in
unused arguments, across scalar, collection and datatype arguments,
through generic applications, nesting and local definitions. -/
def genConfirmed : R String := do
  let k : R String := do return toString (← below 4)
  let divisor : R String := pick #["2", "3", "-2", "(-3)"]
  let int : R String := do
    match ← below 12 with
    | 0 => return s!"(a {← pick #["div", "mod"]} {← divisor})"
    | 1 => return s!"(b {← pick #["div", "mod"]} {← divisor})"
    | 2 => return s!"cf_ind({← pick #["a", "b"]})"
    | 3 => return s!"(a {← pick #["div", "mod"]} {← divisor} + b)"
    | 4 => return "CF_ONE"
    | 5 => return s!"(if q != [] then q[0] else {← pick #["a", "b"]})"
    | 6 => return "(a + b)"
    -- A table that may take no row, whose value there is unspecified: by
    -- its conditions, since one over a range that leaves out values is a
    -- static error (F0317), which would stop the spec's checks.
    | 7 => return s!"table \{ a > {← k} => 1, b > {← k} => 2 }"
    | 8 => return s!"table \{ q != [] => q[0], a = {← k} => {← pick #["a", "b", "2"]} }"
    -- An `if` whose condition may be unknown, an index out of range.
    | 9 => return s!"(if q[{← k}] > {← k} then {← pick #["a", "b", "1"]} else {← pick #["a", "b", "1"]})"
    -- A `match` that may take no arm, by its guards.
    | 10 => return s!"match a \{ n if n > {← k} => 1, n if n < {← k} => b }"
    | _ => pick #["a", "b"]
  let op : R String := pick #["=", "!=", "<", "<=", ">", ">="]
  let bool : R String := do
    match ← below 31 with
    | 0 => return s!"a {← pick #["=", "!="]} b"
    | 1 | 2 => return s!"{← int} {← op} {← int}"
    -- Keep these original forms and draws; guarded unused arguments are
    -- appended below, after all the existing draws.
    | 3 => return s!"(q != [] and (q[0] {← op} {← int} or q[{← k}] = {← k}))"
    | 4 => return s!"(when {← k} < q.len, q[{← k}] {← op} {← int})"
    | 5 => return s!"(cf_ign?(q[{← k}]) or a {← op} {← k})"
    | 6 => return s!"(cf_ign?(a + b) or a {← op} {← k})"
    -- A count with an argument that may be unknown, which the others may decide.
    | 7 => return s!"{← pick #["at_most_one?", "exactly_one?"]}({← pick #["true", "false", "a > 1"]}, " ++
        s!"{← pick #["true", "false", "b > 1"]}, q[{← k}] = {← k})"
    -- An `if` whose condition may be unknown, with branches equal or not.
    | 8 =>
      let t ← pick #["a > 1", "true", "b = a"]
      return s!"(if q[{← k}] = {← k} then {t} else {← if ← chance 50 then pure t else pick #["a > 1", "false"]})"
    -- A `match` and a table whose scrutinee or condition may be unknown,
    -- with arms or rows equal or not.
    | 9 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match q[{← k}] \{ {← k} => {t}, _ => {u} })"
    | 10 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table \{ q[{← k}] = {← k} => {t}, _ => {u} }"
    -- A count spelled out, with a condition that may be unknown.
    | 11 =>
      return s!"((if q[{← k}] = {← k} then 1 else 0) + {← pick #["0", "1", "2", "(if a > 1 then 1 else 0)"]} " ++
        s!"{← pick #["<=", "="]} 1)"
    -- Through a function, and against a constant.
    | 12 => return s!"(cf_ind(q[{← k}]) + {← pick #["0", "1", "2"]} {← pick #["<=", "="]} 1)"
    | 13 =>
      return s!"((if q[{← k}] = {← k} then 1 else 0) + {← pick #["0", "1", "CF_ONE"]} {← pick #["<=", "="]} CF_ONE)"
    -- A `match` on a value of an enumeration that may be unknown: its arms
    -- exhaustive or not, by an or-pattern, with binders read in a body or a
    -- guard, and over an enumeration of one variant.
    | 14 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}] \{ Ce::P({← pick #["_", "n"]}) => {t}, Ce::Q => {u} })"
    | 15 =>
      let t ← pick #["a > 1", "true"]
      return s!"(match s[{← k}] \{ Ce::P(n) => n > {← k} or {t}, Ce::Q => {t} })"
    | 16 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}] \{ Ce::P(n) if n > {← k} => {t}, _ => {u} })"
    | 17 => return s!"(match s[{← k}] \{ Ce::P(_) | Ce::Q => {← pick #["a > 1", "true", "b = a"]} })"
    | 18 => return s!"(match o[{← k}] \{ Co::A({← pick #["_", "n"]}) => {← pick #["a > 1", "true", "b = a"]} })"
    -- In a function's body.
    | 19 => return s!"cf_pick?(s, a)"
    -- A table whose last row is a condition, or `true`.
    | 20 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table \{ q[{← k}] = {← k} => {t}, {← pick #["true", "a > 1"]} => {u} }"
    -- A `match` of several scrutinees, one of which may be unknown, which
    -- each pattern tests on its own (`model::arm_test_of`), with `_`s.
    | 21 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match q[{← k}], a \{ {← k}, _ => {t}, _, _ => {u} })"
    | 22 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match a, q[{← k}] \{ {← k}, _ => {t}, _, {← pick #["_", "n"]} => {u} })"
    | 23 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"(match s[{← k}], (a > 1) \{ Ce::P(_), _ => {t}, Ce::Q, true => {u}, Ce::Q, false => {t} })"
    -- A table over a scrutinee that may be unknown.
    | 24 =>
      let t ← pick #["a > 1", "true", "b = a"]
      let u ← if ← chance 50 then pure t else pick #["a > 1", "false"]
      return s!"table (q[{← k}]) \{ {← k} => {t}, _ => {u} }"
    -- A binder of a scrutinee that may be unknown, as the whole arm.
    | 25 => return s!"(match q[{← k}] \{ n => {← pick #["n > 1 or a > 1", "a > 1", "n = n"]} })"
    -- An or-pattern with a `_` alternative, which tests nothing.
    | 26 =>
      let t ← pick #["a > 1", "true", "b = a"]
      -- The alternative's literal is none of the first arm's (`k`), which
      -- would leave it unreachable, a static error (F0318).
      return s!"(match q[{← k}] \{ {← k} => {t}, {← pick #["4", "5"]} | _ => {← pick #["a > 1", "false", "true"]} })"
    -- A `let`, whose definition the body reads or not.
    | 27 => return s!"(let z := {← pick #["q[1]", "a + 1"]} in {← pick #["z > 1", "a > 1"]})"
    -- A pattern test of a scrutinee that may be unknown.
    | 28 => return s!"(q[{← k}] is {← k} or a {← op} {← k})"
    -- A count spelled out with a negated literal, and as `1 >= sum`.
    | 29 =>
      let sum := s!"(if q[{← k}] = {← k} then 1 else 0) + {← pick #["-0", "0", "1", "-(-1)", "(if a > 1 then 1 else 0)"]}"
      let rel ← pick #["<=", "="]
      return if ← chance 50 then s!"(1 >= {sum})" else s!"({sum} {rel} 1)"
    | _ => return s!"(if a = b then a {← op} {← k} else b {← op} {← k})"
  let mut out := "mod fz\n\n" ++
    "pub fn cf_ign?(a: Int) := false\n" ++
    "pub enum Ce { P(Int), Q }\npub enum Co { A(Int) }\npub const CF_ONE: Int := 1\n" ++
    "pub fn cf_ind(n: Int): Int := if n = 0 then 1 else 0\n" ++
    "pub fn cf_pick?(s: Seq<Ce>, a: Int) := match s[1] { Ce::P(_) => a > 1, Ce::Q => a > 1 }\n"
  for i in [0:(← below 3) + 1] do
    let mut body := s!"    out r := {← int}\n"
    for j in [0:← below 2] do body := body ++ s!"    require ca{j}: {← bool}\n"
    for j in [0:(← below 3) + 1] do body := body ++ s!"    expect cx{j}: {← bool}\n"
    if ← chance 50 then body := body ++ s!"    cover cg0: {← bool}\n"
    let enumerated ← chance 30
    -- The sequences of enumerations only where the body reads them, and then
    -- not enumerated: the Lean-hosted front end does not count the scrutinee
    -- of a complete `match` among a check's variables (#493).
    let ce := if (body.splitOn "s[").length > 1 || (body.splitOn "cf_pick?(s").length > 1 then ", s: Seq<Ce>" else ""
    let co := if (body.splitOn "o[").length > 1 then ", o: Seq<Co>" else ""
    let enumerated := if enumerated && ce.isEmpty && co.isEmpty then
      "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n" else ""
    out := out ++ s!"\n{enumerated}pub proc cfm{i}(a: Int, b: Int, q: Seq<Int>{ce}{co}): (r: Int) \{\n{body}}\n"
  -- Binders of a scrutinee that may be unknown, each read where the arm
  -- binds it: in its body, its guard or both, for a binder as a column of a
  -- `match` of several scrutinees, as the whole arm, and in a variant's
  -- payload. Drawn after every other draw, so that each earlier seed's spec
  -- only grows (`Reqs/dev/Testing`, front-end corpus).
  let binderBool : R String := do
    let u ← pick #["a > 1", "false", "true"]
    let t ← pick #["a > 1", "true", "b = a"]
    let (g?, body) ← match ← below 3 with
      | 0 => pure (none, s!"n > {← k} or {t}")
      | 1 => pure (some s!"n > {← k}", t)
      | _ => pure (some s!"n > {← k}", s!"n < {← k} or {t}")
    let guard := (g?.map (s!" if " ++ ·)).getD ""
    -- After a binder's arm without a guard, which matches whatever is left,
    -- no arm, which would be unreachable (F0318), a static error.
    let rest (r : String) := if g?.isSome then s!", {r} => {u}" else ""
    match ← below 5 with
    | 0 => return s!"(match a, q[{← k}] \{ {← k}, _ => {u}, _, n{guard} => {body}{rest "_, _"} })"
    | 1 => return s!"(match q[{← k}], a \{ n, {← k}{guard} => {body}, _, _ => {u} })"
    | 2 => return s!"(match q[{← k}] \{ n{guard} => {body}{rest "_"} })"
    | 3 => return s!"(match s[{← k}] \{ Ce::P(n){guard} => {body}, _ => {u} })"
    | _ => return s!"(match o[{← k}] \{ Co::A(n){guard} => {body}{rest "_"} })"
  let mut binders := ""
  for j in [0:(← below 3) + 1] do binders := binders ++ s!"    expect cb{j}: {← binderBool}\n"
  out := out ++ s!"\npub proc cfb(a: Int, b: Int, q: Seq<Int>, s: Seq<Ce>, o: Seq<Co>): (r: Int) \{\n    out r := a\n{binders}}\n"
  -- Source questions survive unused arguments, through generic functions,
  -- nested applications and local definitions. Append after every draw
  -- above so that existing seeds keep their original specs as a prefix.
  let (ty, value) ← pick #[
    ("Int", "0"), ("Nat", "0"), ("Bool", "false"), ("String", "\"\""),
    ("Set<Int>", "{}"), ("Rel<Bool, Bool>", "{}"), ("Seq<Int>", "[]"),
    ("Option<Int>", "Option::None"), ("Ce", "Ce::Q"),
    ("CfArgNew", "CfArgNew(0)"), ("CfArgRecord", "CfArgRecord { value := 0 }")]
  let valueName := if ty == "Bool" then "cf_arg_value?" else "cf_arg_value"
  let valueCall := valueName ++ "(0)"
  let savedName := if ty == "Bool" then "saved?" else "saved"
  out := out ++ "\npub struct CfArgNew(Int)\npub struct CfArgRecord { value: Int }\n" ++
    s!"pub fn {valueName}(unused: Int): {ty} := {value}\n" ++
    "pub fn cf_arg_ignore?<T>(value: T) := true\n" ++
    "pub fn cf_arg_identity<T>(value: T): T := value\n"
  let mut arguments := ""
  for j in [0:3] do
    let source ← match j with
      | 0 => pure s!"table \{ enabled? => {valueCall} }"
      | 1 => pure s!"match option \{ Option::Some(n) if n > 0 => {valueCall}, Option::None => {valueCall} }"
      | _ => pure s!"[{valueCall}][k]"
    let argument ← match ← below 3 with
      | 0 => pure source
      | 1 => pure s!"cf_arg_identity({source})"
      | _ => pure s!"(let {savedName}: {ty} := {source} in {savedName})"
    let test := s!"cf_arg_ignore?({argument}) {← pick #["=", "!=", "iff"]} enabled?"
    arguments := arguments ++ s!"    expect arg{j}: when k {← op} {← k}, {test}\n"
  let evidence ← pick #["enumerated", "solver"]
  out := out ++ s!"\nset_option fren.enumeration.size 2 in\nset_option fren.evidence \"{evidence}\" in\n" ++
    s!"pub proc cf_args(k: Int, enabled?, option: Option<Int>) \{\n{arguments}}\n"
  return out

end FrenTest.FuzzFrontends.Wide
