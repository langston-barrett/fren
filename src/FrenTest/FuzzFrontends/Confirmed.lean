-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Non-flat values of a sort, appended by `genHostedConfirmed` after all its
older draws. Generic containers carry a function's type parameter in
fields and payloads; explicit abstract type arguments are forbidden.
A newtype cannot itself contain a sort (`Reqs/Lang/Generics`), so it
occurs beside one in a relation's pair. Each legal shape is used
directly, through a definition, in comparisons and as an argument to
a function, including a higher-order one. Quantifiers and structural
recursions also read the sort through generic definitions. No static
error is deliberate here: it would stop the older checks too. Record
inputs are equated for the pre-existing reconstruction difference #871:
https://github.com/langston-barrett/fren/issues/871. Its independent-record
reproduction is tracked there, outside this error-free appended group. -/
def confirmedSorts : R String := do
  let op : R String := pick #["=", "!=", "<", "<=", ">", ">="]
  -- General sequence comparisons and alternating quantifiers can be
  -- outside the decidable core. They still test confirmation when the
  -- solver finds a model; the lint must not stop the spec's checks.
  let out := "\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub struct CfBox<A> { value: A }\npub struct CfTag(Int)\n" ++
    "pub enum CfWrap<A> { Empty, One(A), Two(A, Int) }\n" ++
    "pub enum CfList<A> { Nil, Cons(A, CfList<A>) }\n" ++
    "pub fn cf_id<A>(x: A): A := x\n" ++
    "pub fn cf_sort_lab<A>(x: A): Int := 3\n" ++
    "pub fn cf_apply<A>(f: fn(A) -> Int, x: A): Int := 0\n" ++
    "pub proc cf_copy(x: CfN): (v: CfN) { out v := x }\n" ++
    "pub fn cf_exists?<A>(x: A) := exists (y: A), y != x\n" ++
    "pub fn cf_forall?<A>(x: A) := forall (y: A), y = x\n" ++
    "pub fn cf_len<A>(l: CfList<A>): Int := match l { CfList::Nil => 0, CfList::Cons(_, r) => 1 + cf_len(r) }\n" ++
    "pub fn cf_has?<A>(l: CfList<A>, x: A) := match l { CfList::Nil => false, CfList::Cons(y, r) => y = x or cf_has?(r, x) }\n"
  -- One or two layers, each wrapping the preceding type. Datatypes are
  -- declared above; nesting is in their arguments and in parameters.
  let mut ty := "SORT"
  let mut abstractTy := "SORT"
  for _ in [0:(← below 2) + 1] do
    ty ← pick #[s!"Seq<{ty}>", s!"Set<{ty}>", s!"Rel<{ty}, Int>", s!"Rel<CfTag, {ty}>",
      s!"Option<{ty}>", s!"CfBox<{ty}>", s!"CfWrap<{ty}>", s!"CfList<{ty}>"]
    abstractTy ← pick #[s!"Seq<{abstractTy}>", s!"Set<{abstractTy}>", s!"Rel<{abstractTy}, Int>", s!"Rel<CfTag, {abstractTy}>"]
  let comparison (x y : String) : R String := do
    match ← below 5 with
    | 0 => return s!"{x} {← pick #["=", "!="]} {y}"
    | 1 => return s!"cf_same({x}, {y}) {← op} {← below 3}"
    | 2 => return s!"{← pick #[s!"cf_ig({x})", s!"cf_sort_lab({x})", s!"cf_apply(cf_sort_lab, {x})"]} {← op} {← below 4}"
    | 3 => return s!"(if {x} = {y} then a else b) {← op} {← below 3}"
    | _ => return s!"cf_same(cf_id({x}), {y}) {← op} {← below 3}"
  let atom ← comparison "x" "y"
  let defined ← comparison "z" "cf_id(y)"
  let join ← pick #["and", "or"]
  let mut shapes := s!"pub proc cf_shape_copy(x: {abstractTy.replace "SORT" "CfN"}): (v: {abstractTy.replace "SORT" "CfN"}) \{ out v := x }\n"
  for generic in [false, true] do
    let shape := if generic then ty.replace "SORT" "T" else abstractTy.replace "SORT" "CfN"
    let name := if generic then "cf_shape_generic" else "cf_shape_abstract"
    let head := if generic then s!"pub fn {name}<T>" else s!"pub proc {name}"
    let call := if generic then "" else "    call c := cf_shape_copy(y)\n"
    -- Keep the draws and record shapes, but defer independent record
    -- values: lean-smt can omit their payloads from its sort domain (#871).
    let record := generic && (ty.splitOn "CfBox<").length > 1
    let alias := if record then "    require same_record: x = y\n" else ""
    let called ← comparison "z" "c.v"
    let post := if generic then
      s!"    ensure e: {name}(x, y, a, b) > 0 {join} {defined}\n"
      else s!"    expect e: a > 0 {join} {called}\n"
    shapes := shapes ++ s!"\n{head}(x: {shape}, y: {shape}, a: Int, b: Int): (r: Int) \{\n" ++
      s!"    let z: {shape} := cf_id(x)\n{call}{alias}" ++
      s!"    require pinned: a = -1 {join} ({atom} {join} {defined})\n    out r := a\n{post}}\n"
  -- Quantify both directly and through a definition. A second quantifier
  -- may be nested, and the integer may decide a surrounding connective.
  let quantifier (t : String) : R String := do
    let exists_ ← chance 50
    let body := if exists_ then "y != x" else "y = x"
    let direct := if exists_ then s!"(exists (y: {t}), {body})" else s!"(forall (y: {t}), {body})"
    let helper := if exists_ then "cf_exists?(x)" else "cf_forall?(x)"
    match ← below 6 with
    | 0 => return direct
    | 1 => return helper
    | 2 => return s!"(forall (z: {t}), (exists (y: {t}), y != z) or z = x)"
    | 3 => return s!"({direct} {← pick #["and", "or"]} {helper})"
    | 4 => return s!"(forall (unused: {t}), a = -1)"
    | _ => return s!"(exists (unused: {t}), a = -1)"
  let qa ← quantifier "CfN"
  let qg ← quantifier "T"
  let beside (q : String) : R String := do
    let connective ← pick #["and", "or"]
    return if ← chance 50 then s!"{q} {connective} a = -1" else s!"a = -1 {connective} {q}"
  let quantified := s!"\npub proc cf_quantified(x: CfN, a: Int) \{\n    require pinned: {← beside qa}\n    expect e: a > 0\n}\n" ++
    s!"\npub fn cf_quantified_generic<T>(x: T, a: Int): (r: Int) \{\n    require pinned: {← beside qg}\n    out r := a\n    ensure e: cf_quantified_generic(x, a) > 0\n}\n"
  -- Unknown `let` and call values, with no equality to force a model
  -- value. The recursive case also leaves `x` free beside a known list.
  let recursive ← chance 50
  let recAtom := if recursive then "cf_len(l) = 2" else "cf_has?(l, x)"
  let mut definitions := ""
  for generic in [false, true] do
    let t := if generic then "T" else "CfN"
    let name := if generic then "cf_defined_generic" else "cf_defined_abstract"
    let head := if generic then s!"pub fn {name}<T>" else s!"pub proc {name}"
    let call := if generic then "" else "    call c := cf_copy(z)\n"
    let post := if generic then s!"    ensure e: {name}(x, l, a) > 0\n" else "    expect e: a > 0 and cf_ig(c.v) = 0\n"
    let listParam := if generic then s!", l: CfList<{t}>" else ""
    let recAtom := if generic then s!" and {recAtom}" else ""
    definitions := definitions ++ s!"\n{head}(x: {t}{listParam}, a: Int): (r: Int) \{\n" ++
      s!"    let z: {t} := cf_id(x)\n{call}" ++
      s!"    require pinned: a = -1{recAtom} and cf_ig(z) = 0 and cf_apply(cf_sort_lab, x) = 0\n    out r := a\n{post}}\n"
  -- A pair of related checks per seed keeps workers' memory bounded
  -- (#650); fresh seeds cover each family, and the ui pins regressions.
  return out ++ (← pick #[shapes, quantified, definitions])

/-- The prefix of a spec of what confirmation evaluates (`--confirm`,
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
may be, with branches, arms or rows equal or not. `genConfirmedBase`
continues with hosted-sort cases, while `genConfirmedArguments` continues
with main's ignored-argument cases, at this same draw boundary. -/
def genConfirmedPrefix : R String := do
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
    -- An index in an argument that a body never reads only where nothing
    -- guards it: the `fren` command gives such an index no definedness goal
    -- (#493).
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
  return out

/-- The original confirmation prefix, then its hosted-sort cases.
The shared prefix makes both independently appended streams reproducible. -/
def genConfirmedBase : R String := do
  let mut out ← genConfirmedPrefix
  let k : R String := do return toString (← below 4)
  let op : R String := pick #["=", "!=", "<", "<=", ">", ">="]
  -- Values of an abstract type and of a generic function's type parameter,
  -- which the model gives as its sort's values or leaves free: compared,
  -- given to a function, a generic one too, which compares them in its
  -- body or never reads them, deciding an `if`, and in a sequence, beside
  -- an integer that may decide the formula. Drawn after every other draw,
  -- as the binders are.
  let atAbstract (x y q : String) (generic : Bool) : R String := do
    let lab := if generic then s!"cf_ig({x})" else s!"cf_lab({x})"
    let atom ← match ← below 8 with
      | 0 => pure s!"{x} {← pick #["=", "!="]} {y}"
      | 1 => pure s!"cf_same({x}, {y}) = {← pick #["0", "1"]}"
      | 2 => pure s!"{lab} {← op} {← k}"
      | 3 => pure s!"(if {x} = {y} then a else b) {← op} {← k}"
      | 4 => pure s!"(if {x} = {y} then a > 1 else b > 1)"
      | 5 => pure s!"{q}.len {← op} {← k}"
      | 6 => pure s!"(when {q} != [], {q}[0] {← pick #["=", "!="]} {x})"
      | _ => pure s!"cf_ig({y}) = 0"
    match ← below 3 with
    | 0 => return atom
    | 1 => return s!"({atom} {← pick #["and", "or"]} a {← op} {← k})"
    | _ => return s!"(a {← op} {← k} {← pick #["and", "or"]} {atom})"
  out := out ++ "\npub type CfN\npub fn cf_lab(n: CfN): Int := 3\npub fn cf_ig<U>(x: U): Int := 0\n" ++
    "pub fn cf_same<T>(x: T, y: T): Int := if x = y then 1 else 0\n"
  let mut abstracts := ""
  for j in [0:(← below 2) + 1] do abstracts := abstracts ++ s!"    require cn{j}: {← atAbstract "n" "m" "p" false}\n"
  for j in [0:(← below 2) + 1] do abstracts := abstracts ++ s!"    expect cy{j}: {← atAbstract "n" "m" "p" false}\n"
  out := out ++ s!"\npub proc cfa(a: Int, b: Int, n: CfN, m: CfN, p: Seq<CfN>): (r: Int) \{\n    out r := a\n{abstracts}}\n"
  let mut generics := ""
  for j in [0:(← below 2) + 1] do generics := generics ++ s!"    require gn{j}: {← atAbstract "x" "y" "p" true}\n"
  for j in [0:(← below 2) + 1] do
    generics := generics ++ s!"    ensure gy{j}: cfg(x, y, p, a, b) {← op} {← k} {← pick #["and", "or"]} {← atAbstract "x" "y" "p" true}\n"
  out := out ++ s!"\npub fn cfg<T>(x: T, y: T, p: Seq<T>, a: Int, b: Int): (r: Int) \{\n{generics}    out r := a\n}\n"
  return out

/-- Quantifiers with evaluation domains, unused binders in compiled
conditionals and Boolean locals, and unbounded sort quantifiers beside
a recursion without type parameters. Drawn after all existing
confirmation groups, so earlier seeds keep their complete prefix. -/
private def confirmedDomainBase : R String := do
  if ← chance 20 then
    let quantifier ← pick #["forall", "exists"]
    let ty ← pick #["Int", "T"]
    let q := s!"{quantifier} (unused: {ty}), a = -1"
    let condition ← pick #[q, s!"({q}) and a < 0", s!"({q}) or a = -1"]
    let body ← pick #[s!"if ({condition}) then 1 else 0", s!"let b? := ({condition}) in if b? then 1 else 0"]
    let generic := ty == "T"
    let header := if generic then "pub fn cf_unused<T>(x: T, a: Int): Int := " else "pub fn cf_unused(a: Int): Int := "
    let parameters := if generic then "x: CfN, a: Int" else "a: Int"
    let arguments := if generic then "x, a" else "a"
    return "\n" ++ header ++ body ++ s!"\npub proc cf_unused_check({parameters}) \{\n" ++
      s!"    require pinned: a = -1 and cf_unused({arguments}) = 1\n    expect e: a > 0\n}\n"
  let declarations := "\npub enum CfIntList { Nil, Cons(Int, CfIntList) }\n" ++
    "pub fn cf_int_len(l: CfIntList): Int := match l { CfIntList::Nil => 0, CfIntList::Cons(_, r) => 1 + cf_int_len(r) }\n" ++
    "pub fn cf_witness?<A>(x: A) := exists (y: A), y = x\n"
  let generic ← chance 50
  let t := if generic then "T" else "CfN"
  let name := if generic then "cf_domain_generic" else "cf_domain_abstract"
  let head := if generic then s!"pub fn {name}<T>" else s!"pub proc {name}"
  if ← chance 40 then
    let q ← pick #[s!"(exists (y: {t}), y = x)", s!"(forall (y: {t}), y = x)", "cf_witness?(x)",
      s!"(forall (y: {t}), when y in q, exists (z: {t}), z = y)",
      s!"(forall (y: {t}), when y in q, forall (z: {t}), z = y)"]
    let body ← pick #[q, s!"({q} or a = -1)", s!"(a = -1 or {q})"]
    let integer := if ← chance 50 then "    require integer: a = -1\n" else ""
    let post := if generic then s!"    ensure e: {name}(x, l, q, a) > 0\n" else "    expect e: a > 0\n"
    return declarations ++ s!"{head}(x: {t}, l: CfIntList, q: Seq<{t}>, a: Int): (r: Int) \{\n" ++
      s!"    require members: q = [x]\n{integer}    require pinned: cf_int_len(l) = 0 and {body}\n    out r := a\n{post}}\n"
  let seq ← chance 50
  let collection := if seq then "Seq" else "Set"
  let members := if seq then "[x]" else "{x}"
  let all ← chance 50
  let binder ← pick #["y", "y z"]
  let equality := if binder == "y" then "y = x" else "y = z"
  let guard := if binder == "y" then "y in q" else "y in q and z in q"
  let q (ty : String) := if all then s!"forall ({binder}: {ty}), when {guard}, {equality} and a = -1"
    else s!"exists ({binder}: {ty}), {guard} and {equality} and a = -1"
  let helper := s!"pub fn cf_bounded?<A>(x: A, q: {collection}<A>, a: Int) := {q "A"}\n"
  let quantified ← pick #[q t, "cf_bounded?(x, q, a)"]
  let post := if generic then s!"    ensure e: {name}(x, q, a) > 0\n" else "    expect e: a > 0\n"
  return declarations ++ helper ++ s!"{head}(x: {t}, q: {collection}<{t}>, a: Int): (r: Int) \{\n" ++
    s!"    require members: q = {members}\n    require pinned: {quantified}\n    out r := a\n{post}}\n"

/-- Complete Boolean matches whose scrutinees are guarded quantifiers.
Each spec has existential/universal and empty/nonempty domains; types,
collections, nested quantifiers and unfolded definitions vary by seed.
Independent record inputs retain the #871 limitation documented above. -/
private def confirmedDomainMatches : R String := do
  let mut out := ""
  for j in [0:4] do
    let (t, generic) ← pick #[("Int", false), ("Nat", false), ("Bool", false), ("CfN", false),
      ("CfTag", false), ("T", true), ("Seq<T>", true), ("Set<T>", true), ("Rel<T, T>", true),
      ("CfBox<T>", true), ("CfWrap<T>", true)]
    let collection ← pick #["Seq", "Set"]
    -- Nat is not a collection element type (F0338); its domains are
    -- integer ranges. Boolean binders keep their required question marks.
    let range := t == "Nat"
    let aggregate := ["Seq<T>", "Set<T>", "Rel<T, T>", "CfBox<T>", "CfWrap<T>"].contains t
    let paramTy := if aggregate then "T" else t
    let xName := if paramTy == "Bool" then "x?" else "x"
    -- Construct nested values from a directly returned sort value. The
    -- pin's missing independent payload values stay in the #871 repro.
    let item := if t == "Seq<T>" then "[x]" else if t == "Set<T>" then "{x}"
      else if t == "Rel<T, T>" then "{(x, x)}" else if t == "CfBox<T>" then "CfBox { value := x }"
      else if t == "CfWrap<T>" then "CfWrap::One(x)" else xName
    let primitive := ["Int", "Nat", "Bool", "CfTag"].contains t
    let universal := j % 2 == 1
    let empty := j < 2
    let nested ← if j < 2 then pure "forall" else pick #["plain", "exists", "forall", "nested"]
    let boundName (a name : String) := if a == "Bool" then name ++ "?" else name
    let body (a item domain : String) := Id.run do
      let y := boundName a "y"
      let z := boundName a "z"
      let innerTy := if primitive then "CfN" else a
      let innerZ := boundName innerTy "z"
      let w := boundName innerTy "w"
      let equal := if primitive then s!"{innerZ} = {innerZ}" else s!"{innerZ} = {y}"
      let guard := if range then s!"{z} < n" else s!"{z} in {domain}"
      return match nested with
        | "plain" => s!"{y} = {item}"
        | "exists" => s!"exists ({innerZ}: {innerTy}), {equal}"
        | "nested" => s!"forall ({z}: {a}), when {guard}, exists ({w}: {innerTy}), {if primitive then w else z} = {w}"
        | _ => s!"forall ({innerZ}: {innerTy}), {equal}"
    let quantified (a item domain : String) := Id.run do
      let y := boundName a "y"
      let guard := if range then s!"{y} < n" else s!"{y} in {domain}"
      return if universal then s!"forall ({y}: {a}), when {guard}, ({body a item domain})"
        else s!"exists ({y}: {a}), {guard} and ({body a item domain})"
    let helper := s!"cf_match_scrutinee_{j}?"
    let indirect ← chance 50
    let readsItem := nested == "plain"
    if indirect then
      let itemParam := if readsItem then (if range then "x: Nat, " else "x: A, ") else ""
      out := out ++ (if range then s!"\npub fn {helper}({itemParam}n: Nat) := {quantified "Nat" "x" "n"}\n"
        else s!"\npub fn {helper}<A>({itemParam}q: {collection}<A>) := {quantified "A" "x" "q"}\n")
    let literal := if collection == "Seq" then (if empty then "[]" else s!"[{item}]")
      else if empty then "{}" else "{" ++ item ++ "}"
    let domain := if aggregate then "mq" else "q"
    let helperArgs := (if readsItem then item ++ ", " else "") ++ (if range then "n" else domain)
    let scrutinee := if indirect then s!"{helper}({helperArgs})" else quantified t item domain
    let name := s!"cf_match_domain_{j}"
    let head := if generic then s!"pub fn {name}<T>" else s!"pub proc {name}"
    let members := if range then s!"    require members: n = {if empty then 0 else 1}\n"
      else if aggregate then s!"    let mq: {collection}<{t}> := {literal}\n"
      else s!"    require members: q = {literal}\n"
    let other ← pick #["a = -1", "true", "false"]
    let onTrue := if universal then "a = -1" else other
    let onFalse := if universal then other else "a = -1"
    let firstTrue ← if j < 2 then pure (!universal) else chance 50
    let arms := if firstTrue then s!"true => {onTrue}, false => {onFalse}"
      else s!"false => {onFalse}, true => {onTrue}"
    let domainParam := if range then ", n: Nat" else if aggregate then "" else s!", q: {collection}<{t}>"
    let post := if generic then "    ensure e: r > 0\n" else "    expect e: a > 0\n"
    out := out ++ s!"\n{head}({xName}: {paramTy}{domainParam}, a: Int): (r: Int) \{\n" ++
      members ++ s!"    require pinned: match ({scrutinee}) \{ {arms} }\n" ++
      s!"    out r := a\n{post}}\n"
  return out

/-- Retain the original domain group's entire stream. The opt-in match
composition tail draws only after it, so old specs and cuts are unchanged. -/
def confirmedDomains (withMatches := false) : R String := do
  let base ← confirmedDomainBase
  if withMatches then return base ++ (← confirmedDomainMatches)
  return base

/-- The original confirmation spec followed by the non-flat sort and
quantifier-domain groups.
`Mode.cuts` keeps the prefix so that the corpus rejects a static error
in the appended group even if both front ends report it alike. -/
def genHostedConfirmed (withMatches := false) : R String := do
  let base ← genConfirmedBase
  let sorts ← confirmedSorts
  return base ++ sorts ++ (← confirmedDomains withMatches)

-- A body index also creates a quantified definedness goal without an
-- index of its own, which retains the pre-existing native limit #493:
-- see test/known/493-quantified-index-count.fren. Keep that separate from
-- these partial quantifier/count compositions; do not hide its diagnostic.
/-- Counts of empty and inhabited guarded quantifiers whose bodies contain
unbounded quantifiers. Both quantifiers must compose with the count itself, not
only with a separately evaluated Boolean. Draw after the earlier tail. -/
def confirmedCountDomains : R String := do
  let mut out := "\npub enum CfCountBit { Off, On }\npub ordered struct CfCountOrd(Int)\n"
  for j in [0:4] do
    let universal := j % 2 == 0
    let empty := j < 2
    let range ← chance 25
    let (ty, item, generic) ← if range then pick #[("Nat", "0", false), ("Int", "0", false),
      ("CfCountOrd", "CfCountOrd(0)", false)] else pick #[
      ("Bool", "true", false), ("Int", "0", false), ("String", "\"\"", false),
      ("CfN", "x", false), ("CfTag", "x", false),
      ("CfCountBit", "CfCountBit::On", false), ("Ce", "Ce::Q", false),
      ("T", "x", true), ("Result<T, Bool>", "Result::Ok(x)", true),
      ("Seq<T>", "[x]", true), ("Set<T>", "{x}", true),
      ("Rel<T, T>", "{(x, x)}", true), ("CfBox<T>", "CfBox { value := x }", true),
      ("CfWrap<T>", "CfWrap::One(x)", true)]
    let collection ← pick #["Seq", "Set"]
    let nested ← chance 50
    let nestedAll ← chance 50
    let direct ← chance 50
    let quantified (a domain : String) := Id.run do
      let y := if a == "Bool" then "y?" else "y"
      let z := if a == "Bool" then "z?" else "z"
      let guard (v : String) := if !range then s!"{v} in {domain}"
        else if ty == "Nat" then s!"{v} < {domain}"
        else s!"{if ty == "CfCountOrd" then "CfCountOrd(0)" else "0"} <= {v} and {v} < {domain}"
      let body := if !nested then s!"cf_count_all?({y})"
        else if nestedAll then s!"(forall ({z}: {a}), when {guard z}, cf_count_all?({z}))"
        else s!"(exists ({z}: {a}), {guard z} and cf_count_all?({z}))"
      return if universal then s!"(forall ({y}: {a}), when {guard y}, {body})"
        else s!"(exists ({y}: {a}), {guard y} and ({body}))"
    let helper := s!"cf_count_domain_q_{j}?"
    if !direct then
      out := out ++ (if range then
        s!"\npub fn {helper}(n: {ty}) := {quantified ty "n"}\n"
        else s!"\npub fn {helper}<A>(members: {collection}<A>) := {quantified "A" "members"}\n")
    let bound := if empty then "0" else "1"
    let domain := if !range then "members" else if ty == "CfCountOrd" then s!"CfCountOrd({bound})" else bound
    let q := if direct then quantified ty domain else s!"{helper}({domain})"
    let condition := if empty && !universal then s!"(not {q})" else q
    let k := if empty then "1" else "2"
    let sum := s!"((if {condition} then 1 else 0) + {k})"
    let extra := if empty then "false" else "true"
    let count ← pick #[s!"{sum} = 1", s!"1 = {sum}", s!"{sum} <= 1", s!"1 >= {sum}",
      s!"exactly_one?({condition}, true, {extra})", s!"at_most_one?({condition}, true, {extra})"]
    let pinned ← pick #[s!"a = 1 or (({count}) and unknowns[5] = 0)",
      s!"if {count} then unknowns[5] = 0 else a = 1",
      s!"a = 1 or ((not cf_count_accept?({count})) and unknowns[5] = 0)"]
    let literal := if collection == "Seq" then (if empty then "[]" else s!"[{item}]")
      else if empty then "{}" else "{" ++ item ++ "}"
    let members := if range then "" else s!"    let members: {collection}<{ty}> := {literal}\n"
    let head := if generic then s!"pub fn cf_count_guarded_{j}<T>" else s!"pub proc cf_count_guarded_{j}"
    let parameter := if generic then "x: T, " else if item == "x" then s!"x: {ty}, " else ""
    out := out ++ s!"\n{head}({parameter}unknowns: Seq<Int>, a: Int): (r: Int) \{\n" ++
      members ++ s!"    require pinned: {pinned}\n    out r := a\n" ++
      (if generic then "    ensure e: r = 3\n" else "    expect e: a = 3\n") ++ "}\n"
  return out

/-- Quantifiers inside count conditions, followed by Boolean, conditional
and strict-argument compositions. Draw only after the old confirmation
stream, in an opt-in mode, so every existing spec stays unchanged. -/
def genConfirmedCounts : R String := do
  let mut out ← genHostedConfirmed false
  out := out ++ "\npub fn cf_count_all?<A>(x: A) := forall (y: A), y = x\n" ++
    "pub fn cf_count_accept?<A>(x: A) := true\n"
  for j in [0:4] do
    let (ty, item, generic) ← pick #[("Bool", "true", false), ("Int", "0", false),
      ("Nat", "x", false), ("String", "\"\"", false), ("CfN", "x", false), ("CfTag", "x", false),
      ("T", "x", true), ("Seq<T>", "[x]", true), ("Set<T>", "{x}", true),
      ("Rel<T, T>", "{(x, x)}", true), ("CfBox<T>", "CfBox { value := x }", true),
      ("CfWrap<T>", "CfWrap::One(x)", true)]
    let direct ← chance 50
    let nested ← chance 50
    let y := if ty == "Bool" then "y?" else "y"
    let z := if ty == "Bool" then "z?" else "z"
    let body := if nested then s!"exists ({z}: {ty}), {z} = {item}" else s!"{y} = {item}"
    let q := if direct then s!"(forall ({y}: {ty}), {body})" else s!"cf_count_all?({item})"
    let sum := s!"((if {q} then 1 else 0) + 2)"
    let count ← pick #[s!"{sum} = 1", s!"1 = {sum}", s!"{sum} <= 1", s!"1 >= {sum}",
      s!"exactly_one?(true, {q}, true)", s!"at_most_one?({q}, true, true)"]
    let settled := if j == 3 then s!"not at_most_one?({q}, false, false)" else count
    let settled ← pick #[settled, s!"(exists (w: Int), w in [0] and ({settled}))",
      s!"(forall (w: Int), when w in [0], ({settled}))"]
    let pinned ← pick #[s!"a = 1 or (({settled}) and unknowns[5] = 0)",
      s!"if {settled} then unknowns[5] = 0 else a = 1",
      s!"a = 1 or ((not cf_count_accept?({settled})) and unknowns[5] = 0)"]
    let head := if generic then s!"pub fn cf_count_{j}<T>" else s!"pub proc cf_count_{j}"
    let parameter := if generic then "x: T, " else if item == "x" then s!"x: {ty}, " else ""
    out := out ++ s!"\n{head}({parameter}unknowns: Seq<Int>, a: Int): (r: Int) \{\n" ++
      s!"    require pinned: {pinned}\n    out r := a\n" ++
      (if generic then "    ensure e: r = 3\n" else "    expect e: a = 3\n") ++ "}\n"
  -- Ambiguous counts keep their unknown value, also through their reversed
  -- spellings. The unbounded generic domain does not supply a finite list.
  let unknown ← pick #["(if cf_count_all?(x) then 1 else 0) = 1",
    "1 = (if cf_count_all?(x) then 1 else 0)",
    "(if cf_count_all?(x) then 1 else 0) + 1 <= 1",
    "1 >= (if cf_count_all?(x) then 1 else 0) + 1"]
  out := out ++ "\npub fn cf_count_unknown<T>(x: T, a: Int): (r: Int) {\n" ++
    s!"    require pinned: a = 1 or ({unknown})\n" ++
    "    out r := a\n    ensure e: r = 3\n}\n"
  return out ++ (← confirmedCountDomains)

/-- Main's #940 stream, with its Nat index annotation corrected in the
argument regression mode. `genConfirmed` replays the original spelling. -/
def genConfirmedArguments (widenNatIndex := true) : R String := do
  let mut out ← genConfirmedPrefix
  let k : R String := do return toString (← below 4)
  let op : R String := pick #["=", "!=", "<", "<=", ">", ">="]
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
    -- Sequence elements widen Nat to Int. A local binding must use the
    -- index's type, not the Nat result of the function in its literal.
    let savedTy := if widenNatIndex && j == 2 && ty == "Nat" then "Int" else ty
    let argument ← match ← below 3 with
      | 0 => pure source
      | 1 => pure s!"cf_arg_identity({source})"
      | _ => pure s!"(let {savedName}: {savedTy} := {source} in {savedName})"
    let test := s!"cf_arg_ignore?({argument}) {← pick #["=", "!=", "iff"]} enabled?"
    arguments := arguments ++ s!"    expect arg{j}: when k {← op} {← k}, {test}\n"
  let evidence ← pick #["enumerated", "solver"]
  out := out ++ s!"\nset_option fren.enumeration.size 2 in\nset_option fren.evidence \"{evidence}\" in\n" ++
    s!"pub proc cf_args(k: Int, enabled?, option: Option<Int>) \{\n{arguments}}\n"
  return out

/-- Main's entire original `--confirm` stream, then the hosted additions.
Replay the hosted generator from the saved seed state so its existing
cases also keep their draws; append only what follows the shared prefix.
The argument mode keeps the corrected Nat annotation regression without
rewriting main's old seeds. -/
def genConfirmed : R String := do
  let rng ← get
  let original ← genConfirmedArguments false
  let shared := Id.run (genConfirmedPrefix.run' rng)
  let hosted := Id.run ((genHostedConfirmed false).run' rng)
  return original ++ (hosted.drop shared.length).toString

end FrenTest.FuzzFrontends.Wide
