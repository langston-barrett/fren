-- keep-sorted start
import FrenCli.Confirm
-- keep-sorted end

/-!
The evaluator's goals of the precondition and postcondition checks
(`Reqs/Eval#confirming-models`), with which `fren check` confirms the
solver's models: each application of a function with preconditions has
its question at the function's name, guarded as an index is, and a
defined function's postconditions are constraints of its body's comp.
Each has a value in a behaviour, so a model that contradicts it is
refuted.
-/

open FrenCli FrenCli.Eval

def contractSrc : String := "fn nth(q: Seq<Int>, i: Int): (r: Int) {
    assume in_range: 0 <= i < q.len
    out r := q[i]
    ensure same: r = q[i]
}

proc c(
    q: Seq<Int>,
): (y: Int) {
    ensure r: when q != [], y = nth(q, 0)
}
"

def contractSpec : Spec := (specOf #[("t.fren", contractSrc.toList.toArray)]).toOption.getD default

/-- The value of `e` where `q` is `vals`, and `y` and `i` are 0. -/
def valueAt (e : Ex) (vals : Array Int) : Option Val :=
  e.eval {} fun n =>
    if n == `q then some (.seq (vals.map .int)) else if n == `y || n == `i then some (.int 0) else none

-- The application's question, at the position of `nth` in `r`, under the
-- guard `q != []`: decided both where it holds and where the guard fails.
#guard
  match (contractSpec.comp? `c).bind (·.constraints.find? (·.name == `r)) with
  | some r => match r.e.tableGoals with
    | #[(pos, .precondition f p, g)] =>
      pos == (contractSrc.splitOn "nth(q, 0)")[0]!.utf8ByteSize && f == `nth && p == `in_range
        && valueAt g #[] == some (.bool true) && valueAt g #[5] == some (.bool true)
    | _ => false
  | none => false

-- The body's comp has the precondition and the postcondition as
-- constraints, which have values: a model where the postcondition is
-- false is refuted.
#guard
  match contractSpec.bodies.find? (·.body?.map (·.1) == some `nth) with
  | some b =>
    let pre := b.constraints.find? (·.name == `nth.in_range)
    let post := b.constraints.find? (·.name == `nth.same)
    (pre.map (valueAt ·.e #[]) == some (some (.bool false)))
      && (post.map (valueAt ·.e #[7]) == some (some (.bool true)))
  | none => false
