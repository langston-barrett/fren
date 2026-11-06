-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A random procedure in the decidable core of strings. -/
def stringCore : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\n"
  let lits := #["\"\"", "\"a\"", "\"ab\"", "\"b\"", "\"F0\"", "\"x?\""]
  let pats := #["r\"[a-z]*\"", "r\"a+b?\"", "r\".*[A-Z].*\"", "r\"[^_]*\"", "r\"(ab|ba){1,2}\"", "r\"F0[1-7][0-9]\""]
  for k in [0:1] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      let seed ← below 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let v := pick #["s", "t"] 1
      let l := pick lits 2
      let i := toString ((seed / 13) % 4)
      atoms := atoms.push <| pick #[
        s!"{v}.starts_with?({l})", s!"{v}.ends_with?({l})", s!"{v}.contains?({l})",
        s!"{v}.matches?({pick pats 3})", s!"{v}.len <= {i}", s!"{v}.len + 1 >= {i}", s!"{v} = {l}", "s = t",
        "s != t", s!"s.len + t.len = {i}", s!"({v} ++ {l}).len > {i}", s!"{v}.at({i}) = {l}",
        s!"{v}.slice(0, {i}) != {l}", s!"{v} < {l}"] 5
    out := out ++ s!"proc c{k}(s: String, t: String): (p?) \{\n    \
      require a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect e: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- A random procedure in the decidable core of sets:
Boolean algebra with cardinality. -/
def setCore : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\nenum E { A, B, C }\n\n"
  let sets := #["s", "t", "(s union t)", "(s inter t)", "(s minus t)", "{1, 2}", "(t minus t)"]
  for k in [0:1] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      let seed ← below 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick sets 1
      let b := pick sets 2
      let i := toString ((seed / 13) % 4)
      atoms := atoms.push <| pick #[
        s!"x in {a}", s!"{a} subset {b}", s!"{a} = {b}", s!"{a} != {b}", s!"{a}.card <= {i}",
        s!"{a}.card + {b}.card >= {i}", s!"e in es", "es = {E::A, E::B}", s!"es.card = {i}", "x in s and not x in t",
        "s = {}"] 5
    out := out ++ s!"proc c{k}(s: Set<Int>, t: Set<Int>, x: Int, es: Set<E>, e: E): (p?) \{\n    \
      require a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Relations over finite types, which are in the decidable core: the
relational operators, with the set operators, but not `card`, which the core
does not combine with them. -/
def relationCore : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\nenum E { A, B, C }\n\n"
  let rels := #["r", "q", "(r union q)", "(r inter q)", "(r minus q)", "(r join q)", "r.inverse", "r.closure",
    "{(E::A, E::B), (E::B, E::C)}", "(q join r.closure)"]
  let sets := #["s", "r.domain", "r.range", "r.image(s)", "q.image({E::A})", "{E::B}", "r.closure.image(s)"]
  for k in [0:1] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      let seed ← below 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick rels 1
      let b := pick rels 2
      let u := pick sets 3
      atoms := atoms.push <| pick #[
        s!"(x, y) in {a}", s!"{a} subset {b}", s!"{a} = {b}", s!"x in {u}", s!"{u} subset s", s!"{u} != {b}.domain",
        s!"(x, x) in {a}", "r = {}", s!"{a} != \{}"] 5
    out := out ++ s!"proc c{k}(r: Rel<E, E>, q: Rel<E, E>, s: Set<E>, x: E, y: E): (p?) \{\n    \
      require a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Sequences in the decidable core: indexing, `len`, `update`, equality,
and operations with a literal operand. -/
def sequenceCore : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n\n"
  let seqs := #["q", "r", "[1, 2]", "q.update(0, x)", "r.update(i, 2)", "[x]", "[0, x, 1]"]
  for k in [0:1] do
    let mut atoms : Array String := #[]
    for _ in [0:3] do
      let seed ← below 2147483648
      let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
      let a := pick seqs 1
      let b := pick seqs 2
      let j := toString ((seed / 13) % 3)
      atoms := atoms.push <| pick #[
        s!"{a} = {b}", s!"{a} != {b}", s!"{a}.len <= {j}", s!"x in [1, {j}]", s!"q.starts_with?([{j}])",
        s!"q.ends_with?([x, {j}])", s!"(q.len > {j} and q[{j}] = x)", s!"(0 <= i and i < r.len and r[i] > {j})",
        s!"{a}.len + {b}.len >= {j}"] 5
    out := out ++ s!"proc c{k}(q: Seq<Int>, r: Seq<Int>, x: Int, i: Int): (p?) \{\n    \
      require a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r1: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
      expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Procedures whose output invariants apply an opaque recursion under
realizability's quantifier, or whose outputs are replaced by definitions.
Drawn after the older core generators so their existing specs stay
unchanged up to this addition. -/
def outputInvariantCore : R String := do
  let carriers := #[
    ("Int", "@", "0", false), ("Nat", "@", "0", false),
    ("Bool", "(if @ then 1 else 0)", "false", false),
    ("Mode", "(if @ = Mode::A then 0 else 1)", "Mode::A", false),
    ("Carrier", "@.value", "Carrier { value := 0 }", false),
    ("WrappedInt", "@.0", "WrappedInt(0)", false),
    ("Payload", "(match @ { Payload::A(k) => k, Payload::B => 0 })", "Payload::B", false),
    ("Atom", "0", "token(true)", false),
    ("String", "@.len", "\"\"", true),
    ("Set<Int>", "@.card", "{}", true),
    ("Rel<Int, Int>", "@.card", "{}", true),
    ("Seq<Int>", "@.len", "[]", true),
    ("L", "(match @ { L::Nil => 0, L::Cons(k, _) => k })", "L::Nil", true)]
  let (ty, value, witness, unbounded) ← pick carriers
  let name := if ty == "Bool" then "n?" else "n"
  let alias := if ty == "Bool" then "v?" else "v"
  let field := if ty == "Bool" then "value?" else "value"
  let bound := (← below 3) + 1
  let mut out := "mod output_invariants\n\nset_option fren.lint.unused_variables \"allow\"\n\n" ++
    "pub enum Mode { A, B }\npub struct Carrier { value: Int }\npub struct WrappedInt(Int)\n" ++
    "pub type Atom\npub fn token(Bool): Atom\n" ++
    "pub enum Payload { A(Int), B }\npub enum L { Nil, Cons(Int, L) }\n" ++
    "pub fn total(l: L): (r: Int) {\n" ++
    "    out r := match l { L::Nil => 0, L::Cons(n, rest) => n.abs + total(rest) }\n" ++
    "    ensure nonnegative: r >= 0\n    ensure empty: when l = L::Nil, r = 0\n}\n" ++
    "pub fn generic_total<T>(a: T, l: L): (r: Int) {\n" ++
    "    out r := match l { L::Nil => 0, L::Cons(n, rest) => n.abs + generic_total(a, rest) }\n" ++
    "    ensure nonnegative: r >= 0\n    ensure empty: when l = L::Nil, r = 0\n}\n" ++
    "pub fn fixed<T>(unused: T): L := L::Nil\n"
  let appAt (name : String) := if ty == "Atom" then s!"generic_total({name}, L::Cons(0, L::Nil))"
    else s!"total(L::Cons({value.replace "@" name}, L::Nil))"
  let direct := appAt name
  out := out ++ s!"pub fn observe<T>(unused: T, {name}: {ty}): Int := {appAt alias} where {alias} := {name}\n"
  let app ← pick #[direct, s!"observe(true, {name})", s!"(let {alias} := {name} in {appAt alias})",
    s!"total(fixed({name}))"]
  let comparison ← pick #[s!"{app} >= {bound}", s!"{bound} <= {app}", s!"{app} > {bound - 1}",
    s!"{app} = {bound}", s!"{app} != -1"]
  out := out ++ s!"pub type Refined = {name}: {ty} where invariant: ({comparison}) or {name} = {witness}\n" ++
    "pub type Alias := Refined\n"
  -- Abstract types can be procedure variables, never fields or payloads.
  if ty != "Atom" then
    out := out ++ s!"pub struct Box \{ {field}: Alias }\npub struct Wrapped(Alias)\n" ++
      "pub enum Choice { V(Alias) }\npub struct Outer { inner: Box }\n"
  let shapes := if ty == "Atom" then #[("Refined", "y"), ("Alias", "y")] else
    #[ ("Refined", "y"), ("Alias", "y"), ("Box", s!"y.{field}"),
       ("Wrapped", "y.0"), ("Choice", "(match y { Choice::V(v) => v })"), ("Outer", s!"y.inner.{field}") ]
  let (result, read) ← pick shapes
  let output := if ty == "Bool" && (result == "Refined" || result == "Alias") then "y?" else "y"
  let read := if ty == "Bool" then
      if read == "y" then output else read.replace "Choice::V(v) => v" "Choice::V(v?) => v?"
    else read
  -- Unbounded outputs, including through data, must be defined (F0313,
  -- `lang::variable_type`); the solver never quantifies over them.
  if unbounded || (← chance 30) then
    let input := if output == "y?" then "x?" else "x"
    out := out ++ s!"proc generated({input}: {result}): ({output}: {result}) \{ out {output} := {input} }\n"
  else
    let input := if ty == "Bool" then "x?" else "x"
    let op ← pick (if ty == "Int" || ty == "Nat" then #["=", "!=", ">=", ">", "<=", "<"] else #["=", "!="])
    out := out ++ s!"proc generated({input}: {ty}): ({output}: {result}) \{ ensure g: {read} {op} {input} }\n"
  return out

/-- Opt-outs inherited through bodies, values and chains of contracts.
The suffix draws after the original decidable corpus, preserving every
existing spec's prefix. Types, nesting, definitions and comparisons vary;
only the source quantifiers need an opt-out. -/
def inheritedCore : R String := do
  let bound := (← below 4) + 1
  let (ty, left, right) ← pick #[
    ("Int", "n", "n + 1"), ("Bool", "true", "false"),
    ("String", "\"a\"", "\"b\""), ("Set<Int>", "{n}", "{}"),
    ("Seq<Int>", "[n]", "[]"), ("Rel<Int, Int>", "{(n, n)}", "{}"),
    ("Option<Int>", "Option::Some(n)", "Option::None")]
  let suffix := if ty == "Bool" then "?" else ""
  let mut out := "\nmod core_dependencies\n\n" ++
    "set_option fren.lint.undecidable \"allow\" in\n" ++
    s!"pub fn all?(n: Int) := forall (i: Int), when 0 <= i < n, i >= {bound}\n" ++
    "pub fn wrapped?(n: Int) := all?(n)\n" ++
    "pub fn generic<T>(x: T, y: T, n: Int): T := if wrapped?(n) then x else y\n" ++
    "pub fn apply?(f: fn(Int) -> Bool, n: Int) := f(n)\n" ++
    "pub const FLAG: Bool := all?(3)\n"
  let body ← pick #[s!"if all?(n) then {left} else {right}",
    s!"generic({left}, {right}, n)",
    s!"if apply?(wrapped?, n) then {left} else {right}",
    s!"if FLAG then {left} else {right}"]
  out := out ++ s!"pub fn chosen{suffix}(n: Int): {ty} := {body}\n"
  let mut value := s!"chosen{suffix}(n)"
  for _ in [0:← below 3] do
    value := s!"generic({value}, {right}, n)"
  let compare ← pick #["=", "!="]
  let y := if ty == "Bool" then "y?" else "y"
  out := out ++ s!"pub proc body(n: Int): ({y}: {ty}) \{\n    out {y} := {value}\n    expect same: {y} {compare} {left}\n}\n"
  let result ← pick #["Int", "Nat"]
  out := out ++ "pub fn index(Int): Nat\n" ++
    "set_option fren.lint.undecidable \"allow\" in\n" ++
    s!"pub fn first(n: Int): (r: {result}) \{\n    ensure bound: forall (i: Int), when 0 <= i < n, r >= index(i)\n}\n" ++
    s!"pub fn second(n: Int): (r: {result}) \{ ensure value: r = first(n) }\n" ++
    s!"pub fn third<T>(x: T, n: Int): (r: {result}) \{ ensure value: r = second(n) }\n" ++
    s!"expect contract(n: Int) \{ expect bound: third(n, n) >= {bound} }\n" ++
    s!"pub proc cover_contract(n: Int) \{ cover low: third(n, n) < {bound} }\n"
  return out

/-- Random procedures in each theory's decidable core, followed by output
invariant and inherited-core cases. A mode of its own keeps every older
mode's seed unchanged. -/
def genDecidable : R String := do
  let out := "mod strings\n\n" ++ (← stringCore) ++ "mod sets\n\n" ++ (← setCore) ++
    "mod relations\n\n" ++ (← relationCore) ++ "mod sequences\n\n" ++ (← sequenceCore)
  let out := out ++ (← outputInvariantCore)
  return out ++ (← inheritedCore)

end FrenTest.FuzzFrontends.Wide
