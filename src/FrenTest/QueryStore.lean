-- keep-sorted start
import FrenCli.QueryStore
-- keep-sorted end

/-! An entry of the query cache reads back as it was written
(`Reqs/Cli#query-cache`): its key, its answer and its model, whatever
characters their names and values hold. -/

namespace FrenTest.QueryStore

open FrenCli

/-- Whether `encodeEntry?` then `decodeEntry?` gives back `k`, `o` and
`hasModel`. -/
def roundTrips (k : CacheKey) (o : Fren.Core.Outcome String) (hasModel : Bool) : Bool :=
  match encodeEntry? k o hasModel >>= decodeEntry? with
  | some (k', o', hasModel') =>
    k' == k && hasModel' == hasModel && match o, o' with
      | .unsat, .unsat => true
      | .sat m, .sat m' => sameModel m m'
      | _, _ => false
  | none => false

def key : CacheKey :=
  { script := "(assert (= |x\\/y| \"a\\nb\"))\n; observe g: true when h\n\\", solver := "1.3.2\\/\n", version := 1,
    observations := [{ name := ["#g", "a\nb"], formula := "(> x 0)\n\\", guard? := none },
      { name := [], formula := "", guard? := some ["", "\\n"] }, { name := ["v"], formula := "unguarded", guard? := some [] }] }

def awkward : Array (Lean.Name × String) :=
  #[(.mkSimple "\\/x", "\\/"), (.mkStr (.mkSimple "a\nb") "\\", "1\n2\\n"), (.anonymous, ""), (.mkSimple "", "\\\\/"),
    (.mkSimple "#member_observation_0_0_guard", "true")]

#guard roundTrips key .unsat true
#guard roundTrips key (.sat #[]) false
#guard roundTrips key (.sat #[]) true
#guard roundTrips key (.sat awkward) true
#guard roundTrips { key with script := "" } (.sat awkward) true
-- `unknown` is never written.
#guard (encodeEntry? key (.unknown "timeout") false).isNone
-- A name with a numeric component is never written.
#guard (encodeEntry? key (.sat #[(.mkNum .anonymous 3, "1")]) true).isNone
-- A different key reads back as itself, so a hash shared by two keys is a miss.
#guard (decodeEntry? ((encodeEntry? key .unsat true).get!)).map (·.1 != { key with version := 2 }) == some true

-- A key holds its observations, so keys that differ only in them, or in
-- whether one is guarded, read back as different keys.
#guard (decodeEntry? ((encodeEntry? key .unsat true).get!)).map (·.1 != { key with observations := [] }) == some true
#guard (decodeEntry? ((encodeEntry? { key with observations := [{ name := ["v"], formula := "f", guard? := none }] } .unsat true).get!)).map
  (·.1 != { key with observations := [{ name := ["v"], formula := "f", guard? := some [] }] }) == some true

/-! Generated entries, over strings of the characters that the encoding
treats specially, read back as they were written
(`cli::query_entry`). -/

-- fren-covers: cli::query_entry

/-- A pseudo-random number generator, a step of a linear congruential
generator. -/
def step (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A string of up to 5 characters, from the state `s`, and the next
state. -/
def genString (s : Nat) : String × Nat := Id.run do
  let alphabet := #['\\', '\n', 'n', '/', ' ', '0', ':', '|', '"', 'é']
  let mut s := step s
  let len := s / 7 % 6
  let mut out := ""
  for _ in [0:len] do
    s := step s
    out := out.push alphabet[s / 11 % alphabet.size]!
  return (out, s)

/-- Up to 3 strings from `s`, and the next state. -/
def genStrings (s : Nat) : List String × Nat := Id.run do
  let mut s := step s
  let mut out := []
  for _ in [0:s / 13 % 4] do
    let (x, s') := genString s
    out := out ++ [x]
    s := s'
  return (out, s)

/-- A key, an answer and whether it has a model, from the seed `seed`. -/
def genEntry (seed : Nat) : CacheKey × Fren.Core.Outcome String × Bool := Id.run do
  let (script, s) := genString (step seed)
  let (solver, s) := genString s
  let mut s := s
  let mut observations := []
  for _ in [0:s / 17 % 3] do
    let (name, s₁) := genStrings s
    let (formula, s₂) := genString s₁
    let (guard, s₃) := genStrings s₂
    observations := observations ++ [{ name, formula, guard? := if s₃ / 19 % 2 == 0 then none else some guard }]
    s := step s₃
  let key : CacheKey := { script, solver, version := s / 23 % 4, observations }
  let mut model := #[]
  for _ in [0:s / 29 % 3] do
    let (name, s₁) := genStrings s
    let (value, s₂) := genString s₁
    model := model.push (nameOfParts name, value)
    s := s₂
  return match s / 31 % 3 with
    | 0 => (key, .unsat, true)
    | 1 => (key, .sat #[], false)
    | _ => (key, .sat model, true)

#guard (List.range 2000).all fun i => let (k, o, m) := genEntry i; roundTrips k o m

end FrenTest.QueryStore
