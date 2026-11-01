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

def key : CacheKey := { script := "(assert (= |x\\/y| \"a\\nb\"))\n; observe g: true when h\n\\", solver := "1.3.2\\/", version := 1 }

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

end FrenTest.QueryStore
