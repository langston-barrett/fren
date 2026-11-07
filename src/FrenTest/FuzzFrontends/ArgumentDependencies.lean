-- keep-sorted start
import Lean
-- keep-sorted end

namespace FrenTest.FuzzFrontends

/-- Ordinary values ignore unused operands; source questions still enter
them. A separate stream keeps every existing generated spec unchanged. -/
def argumentDependencySpec (seed : Nat) : String :=
  let types := #["Bool", "Int", "Nat", "String", "Seq<Int>", "Set<Int>",
    "Rel<Bool, Bool>", "Option<Int>", "ArgEnum", "ArgNew", "ArgRecord", "Abstract"]
  let ty := types[seed % types.size]!
  let name := if ty == "Bool" then "unknown?" else "unknown"
  let generic := if ty == "Bool" then "generic?" else "generic"
  let saved := if ty == "Bool" then "saved?" else "saved"
  let direct := s!"{name}(b?)"
  let source := match seed / types.size % 6 with
    | 0 => direct
    | 1 => s!"{generic}(b?)"
    | 2 => s!"(let {saved}: {ty} := {direct} in {saved})"
    | 3 => s!"(if b? then {name}(true) else {name}(false))"
    | 4 => s!"table \{ b? => {name}(true), _ => {name}(false) }"
    | _ => s!"match b? \{ true => {name}(true), false => {name}(false) }"
  -- Opaque functions returning relations of finite members are outside
  -- the decidable core. Exercise this argument type with defined values;
  -- keep the source-theory guard, rather than generate invalid specs.
  let functions := if ty == "Rel<Bool, Bool>" then
    "pub fn unknown(flag?): Rel<Bool, Bool> := if flag? then {} else {(false, false)}\n" ++
    "pub fn generic<T>(value: T): Rel<Bool, Bool> := {}\n"
  else s!"pub fn {name}(Bool): {ty}\npub fn {generic}<T>(T): {ty}\n"
  "mod fz_argument_dependencies\nset_option fren.evidence \"enumerated\"\n" ++
    "set_option fren.lint.unused_variables \"allow\"\n" ++
    "set_option fren.lint.assertions_on_constants \"allow\"\n" ++
    "pub enum ArgEnum { A, B }\npub struct ArgNew(Int)\n" ++
    "pub struct ArgRecord { value: Int }\npub type Abstract\n" ++
    functions ++
    "pub fn ignored?<T>(value: T) := true\npub fn identity<T>(value: T): T := value\n" ++
    s!"pub proc plain(b?) \{ expect e: ignored?({source}) }\n" ++
    s!"pub proc nested(b?) \{ expect e: ignored?(identity({source})) }\n" ++
    s!"pub proc defined(b?): (det result?) \{ out result? := ignored?({source})\n    expect e: result? }\n"

end FrenTest.FuzzFrontends
