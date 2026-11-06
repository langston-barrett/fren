-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Private procedures that only claim (`lint::proc_without_outputs`), and
functions whose contract clauses mention their own names, another
function's, a constant's, or nothing (`lint::contract_mentions_nothing`).

Each procedure has members of every kind that a global expectation's block
accepts, and now and then one that it does not: a result, a guarantee, an
`exists` or a `det` `let`. A later call, refinement or claim names some of
them. No member has an evidence setting: only `fren check` runs random
testing, so the two front ends would report such a member's checks
differently. -/
def claimProcs : R String := do
  -- The lint is allowed by default, so warn of it from here on.
  let mut out := "set_option fren.lint.proc_without_outputs \"warn\"\npub const ZK: Int := 3\npub fn zg(Int): Int\npub proc zb(x: Int): (y?) { ensure r: y? iff x > ZK }\n"
  let mut procs : Array (String × Nat × Bool) := #[]
  for k in [0:(← below 3) + 1] do
    let nIn ← below 3
    let ins := (List.range nIn).map (s!"zx{·}")
    let int (d : Nat) : R String := do
      let a ← if ins.isEmpty || (← chance 30) then pure (toString (← below 5)) else pick ins.toArray
      if d > 0 && (← chance 40) then return s!"{a} + {← below 3}"
      return a
    let mut body := ""
    let mut results := ""
    if !ins.isEmpty && (← chance 40) then body := body ++ s!"    require za: {← int 1} >= 0\n"
    let hasLet ← chance 40
    if hasLet then body := body ++ s!"    {if ← chance 15 then "det " else ""}let zl: Int := {← int 1}\n"
    let hasCall ← chance 40
    if hasCall then body := body ++ s!"    call zw := zb({← int 1})\n"
    -- A refinement cannot name a procedure with an `exists`.
    let kind ← below 8
    match kind with
    | 0 =>
      results := s!": (zo: Int)"
      body := body ++ s!"    out zo := {← int 1}\n"
    | 1 => body := body ++ s!"    ensure zq: {← int 1} > zg({← int 0})\n"
    | 2 => body := body ++ "    exists zv?\n    expect zu: zv? or not zv?\n"
    | _ => pure ()
    let atom : R String := do
      match ← below 4 with
      | 0 => if hasLet then return s!"zl > {← int 0}" else return s!"{← int 1} > 0"
      | 1 => if hasCall then return "zw.y?" else return s!"{← int 0} < ZK"
      | 2 => return s!"zg({← int 0}) >= {← int 1}"
      | _ => return s!"{← int 1} != {← int 0}"
    -- No evidence setting: only `fren check` tests an expectation set to
    -- random testing, so the front ends would differ in its result. The ui
    -- test `lints/procedures.fren` has one.
    body := body ++ s!"    expect ze: {← atom} or {← atom}\n"
    if ← chance 40 then body := body ++ s!"    cover zc: {← atom}\n"
    let params := ", ".intercalate (ins.map (s!"{·}: Int"))
    out := out ++ s!"proc zp{k}({params}){results} \{\n{body}}\n"
    procs := procs.push (s!"zp{k}", nIn, kind != 2)
  -- A later item that names one of them, now and then.
  if ← chance 50 then
    let (p, nIn, refinable) ← pick procs
    let args := ", ".intercalate ((List.range nIn).map fun _ => "zy")
    match ← below 3 with
    | 0 => out := out ++ s!"pub proc zcaller(zy: Int): (zr: Int) \{\n    call zc := {p}({args})\n    out zr := zy\n}\n"
    | 1 => if refinable then out := out ++ s!"expect zrefines(zy: Int) \{\n    call zc := {p}({args})\n    refines zc {p}({args})\n}\n"
    | _ => out := out ++ s!"trusted {p}: \"a claim\"\n"
  -- Contract clauses, each mentioning its own, another's, or nothing.
  for k in [0:(← below 2) + 1] do
    let clause : R String := do
      match ← below 7 with
      | 0 => return "zn > 0"
      | 1 => return "zr >= zn"
      | 2 => return s!"zg({← below 3}) > 0"
      | 3 => return "ZK > 0"
      | 4 => return "zh > ZK"
      | 5 => return s!"zf{k}(zn) = zr"
      | _ => return "true"
    let pre ← clause
    let pre := if pre.startsWith "zr" || pre.startsWith s!"zf{k}" then "zn > ZK" else pre
    out := out ++ s!"pub fn zf{k}(zn: Int): (zr: Int) \{\n    let zh: Int := zg(1)\n    require zpre: {pre}\n" ++
      s!"    ensure zpost: {← clause}\n}\n"
  -- Drawn after the above, so that a spec the group wrote before keeps it:
  -- clauses that read a field of a parameter, of a sequence or a record,
  -- that mention only the value, that are a labelled conjunction, or a
  -- quantifier over another function; and a higher-order function's
  -- precondition, which reads or applies its function parameter. A
  -- procedure's `out` member always defines a result, which the block
  -- rejects anyway, so the results above stand for it.
  out := out ++ "pub struct Zs { za: Int }\n"
  let fieldClause (post : Bool) : R String := do
    match ← below (if post then 7 else 5) with
    | 0 => return "zq.len > 1"
    | 1 => return "zs.za > ZK"
    | 2 => return s!"zg({← below 3}) > zs.za"
    | 3 => return "and { zl1: zq.len > 1, zl2: zg(0) > 0 }"
    | 4 => return "forall (zb?: Bool), zg(if zb? then 1 else 0) > 0"
    | 5 => return "zr > 0"
    | _ => return "and { zl1: zr > ZK, zl2: zg(1) > 0 }"
  out := out ++ s!"pub fn zfs(zq: Seq<Int>, zs: Zs): (zr: Int) \{\n    require zpre: {← fieldClause false}\n" ++
    s!"    ensure zpost: {← fieldClause true}\n}\n"
  let hoClause ← pick #["zk(0) > ZK", "zk(zn) >= zn", "zn > 0", "zg(0) > 0", "and { zl1: zk(1) > 0, zl2: zg(1) > 0 }"]
  out := out ++ s!"pub fn zho(zk: fn(Int) -> Int, zn: Int): (zr: Int) \{\n    require zpre: {hoClause}\n    out zr := zk(zn)\n}\n"
  -- Drawn after the above too: procedures whose members are unlabelled
  -- Boolean blocks, of each kind, which are members of their keywords'
  -- kinds, so that a guarantee among them keeps the lint quiet.
  for k in [0:(← below 2) + 1] do
    let mut body := ""
    if ← chance 50 then body := body ++ "    require and { zua: zx > 0, zub: zx < 9 }\n"
    if ← chance 30 then body := body ++ "    ensure and { zuc: zx + 1 > zx, zud: zx - 1 < zx }\n"
    body := body ++ s!"    expect and \{ zue: zx >= {← below 3}, zuf: zg(zx) != zx }\n"
    out := out ++ s!"proc zu{k}(zx: Int) \{\n{body}}\n"
  -- And last, a clause about two other functions, whose note lists both,
  -- in an order that both front ends must agree on.
  if ← chance 60 then
    let two ← pick #["zg(0) > zg2(1)", "zg2(0) > 0 or zg(1) > ZK", "zg2(zg(0)) > 0"]
    out := out ++ s!"pub fn zg2(Int): Int\npub fn zf2(zn: Int): (zr: Int) \{\n    ensure zgrows: zr >= zn\n" ++
      s!"    ensure ztwo: {two}\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
