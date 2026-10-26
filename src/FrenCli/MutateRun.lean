-- keep-sorted start
import FrenCli.Mutate
import FrenCli.MutateOutcome
import FrenCli.MutateSelect
import FrenCli.Quick
import FrenCli.Smt
-- keep-sorted end

/-!
# Running mutants

What `fren mutate` (`FrenCli.mutate`) decides about each mutant, from the
results of its checks (`Reqs/Mutate`): whether it is killed, whether the
solver shows it equivalent to the original, and how it is reported.

A mutant's checks are those of the components whose formulas it changes:
the checks of any other component read the same formulas, so give the
same results.
-/

namespace FrenCli.Mutate

open Lean (Name)
open Fren.Core (CheckResult Msg Verdict)

/-- How mutants are checked (`--by`). -/
inductive By where
  | solver
  | testing
  | both
  deriving BEq, Inhabited

def By.ofName? : String → Option By
  | "solver" => some .solver
  | "testing" => some .testing
  | "both" => some .both
  | _ => none

def By.solves (b : By) : Bool := b != .testing
def By.tests (b : By) : Bool := b != .solver

/-- A component, global expectation, refinement, or body of a function or
value of a constant with tables, with the checks that `fren check` runs on
it. -/
structure Todo where
  comp : CComp
  global : Bool
  kinds : Array Fren.Core.CheckKind
  refinement : Bool
  body : Bool := false

/-- What `fren check` checks in the spec `st`, in order. -/
def todo (st : State) : Array Todo :=
  st.comps.map (⟨·, false, Fren.Core.CheckedItem.component.kinds, false, false⟩)
    ++ st.globals.map (⟨·, true, Fren.Core.CheckedItem.global.kinds, false, false⟩)
    ++ st.refinements.map (⟨·, false, Fren.Core.CheckKind.all.filter Fren.Core.refinementRuns, true, false⟩)
    -- An uninterpreted function's contract has its value as an output.
    ++ st.bodies.map fun b =>
      ⟨b, false, (if b.vars.any (·.role == .output) then Fren.Core.CheckedItem.contract else .body).kinds, false, true⟩

/-- The key of its results. -/
def Todo.key (t : Todo) : String :=
  if t.body then s!"body {t.comp.path}::{t.comp.bodyOf?.getD .anonymous}"
  else if t.global then s!"expect {t.comp.path}::{(t.comp.props[0]?.map (·.name)).getD .anonymous}"
  else if t.refinement then s!"refine {t.comp.path}" else s!"comp {t.comp.path}"

/-- The results of a component, each with the key of its check. The
definedness checks of a constraint are one check, which passes when every
index in it is in range: an index is named only by its position, which a
mutant that adds or drops an index changes. So are its completeness
checks, its disjointness checks and its reachability checks, which a
mutant that drops a row renumbers. -/
def keyed (rs : Array CheckResult) : Array (String × CheckResult) := Id.run do
  let key (r : CheckResult) := s!"{repr r.kind}|{r.prop?}|{r.target?}"
  let mut out : Array (String × CheckResult) := #[]
  for r in rs do
    let k := key r
    unless r.kind == .definedness || r.kind == .completeness || r.kind == .disjointness || r.kind == .precondition
        || r.kind == .reachability do
      out := out.push (k, r)
      continue
    match out.findIdx? (·.1 == k) with
    | none => out := out.push (k, { r with index? := none, site? := none, rows? := none, goal? := none })
    | some i =>
      -- A failure decides, then an inconclusive result.
      let v := match out[i]!.2.verdict, r.verdict with
        | .fail, _ | _, .fail => Verdict.fail
        | .inconclusive, _ | _, .inconclusive => .inconclusive
        | _, _ => .pass
      out := out.set! i (k, { out[i]!.2 with verdict := v })
  return out

/-- The checks of `after` that kill the mutant, against the results
`before` of the original, both keyed. -/
def killers (before after : Array (String × CheckResult)) : Array (String × CheckResult) :=
  after.filter fun (k, r) => before.any fun (k', b) => k == k' && killsCheck b.verdict r.verdict

/-- Whether some check that passes on the original is inconclusive in
`after`. -/
def inconclusive (before after : Array (String × CheckResult)) : Bool :=
  after.any fun (k, r) => r.verdict == .inconclusive && before.any fun (k', b) => k == k' && b.verdict == .pass

def PropKind.name : PropKind → String
  | .assume => "assume"
  | .ensure => "ensure"
  | .expect => "expect"
  | .cover => "cover"

/-- The formulas of `c` that its checks read, labelled. -/
def formulas (c : CComp) : Array (String × String) :=
  c.props.map (fun p => (s!"{PropKind.name p.kind} {p.name}", p.smt))
    ++ c.props.filterMap (fun p => p.trigger?.map (s!"trigger {p.name}", ·))
    ++ c.defs.map (fun (d, e) => (s!"def {d}", e))
    ++ c.insts.flatMap (fun i => #[(s!"bindings {i.name}", i.bindings), (s!"behaviour {i.name}", i.behaviour)]
      ++ i.assumes.map fun (n, a) => (s!"assume {i.name} {n}", a))
    -- The indexes of an item together, as the definedness check of the
    -- item, so that a mutant that adds or drops one still compares.
    ++ (c.indexes.map (·.1)).toList.eraseDups.toArray.map (fun n =>
      (s!"indexes {n}", conj (c.indexes.filter (·.1 == n) |>.map (·.2.2.2.1))))
    -- And the questions about its tables.
    ++ (c.tables.map (·.1)).toList.eraseDups.toArray.map fun n =>
      (s!"tables {n}", conj (c.tables.filter (·.1 == n) |>.map (·.2.2.2.2)))

/-- Everything that `c`'s checks read, with the spec's `prelude`: a mutant
that leaves it alone leaves their results alone. It leaves out the logic
and options, which the whole spec sets (`cli::logic`): a mutant that drops
the only set literal, say, can narrow them, yet `c`'s queries mean the
same in either, since a wider logic only admits more of SMT-LIB, so the
original's results still hold. -/
def fingerprint (prelude : String) (c : CComp) : String :=
  let vars := c.vars.map fun v => s!"{v.name} {repr v.role} {v.isPub} {v.isDet} {v.ty.show}"
  "\n".intercalate ([prelude] ++ vars.toList ++ (formulas c).toList.map fun (l, f) => s!"{l}: {f}")

/-- Whether the solver shows that the formulas of each pair are equal for
all values of `vars` and every interpretation: `some false` if some pair
can differ, `none` if it cannot tell. `prelude` is `st`'s, indexed. -/
def equal (st : State) (prelude : Prelude) (vars : Array CVar) (pairs : Array (String × String)) (timeout : Nat)
    (cache : QueryCache) : IO (Option Bool) := do
  if pairs.isEmpty then return some true
  let strings := st.usesStrings || st.usesSeqs
  let sets := st.usesSets || st.usesSeqs
  let options := String.join ((Fren.Core.solverOptions strings sets).map fun (o, v) => s!"(set-option :{o} {v})\n")
  let goal := conj (pairs.map fun (a, b) => s!"(= {a} {b})")
  match ← runQuery (Fren.Core.logic .expect (strings || sets) st.usesProjection st.quantified) options prelude vars { timeoutSecs := timeout } none #[] goal false cache with
  | .unsat => return some true
  | .sat _ => return some false
  | .unknown _ => return none

/-- The time limit, in seconds, of each query that asks whether a mutant
is equivalent: the answer only refines the report, so it is kept short. -/
def equivalenceTimeout : Nat := 1

/-- Whether the solver shows that the spec `st'` of a mutant means what the
original `st` means (`Reqs/Mutate#equivalent-mutants`): each defined function, and each
formula of each component, global expectation and refinement, is equivalent to the
original's. `prelude` is `st`'s, indexed, and `cache` holds the answers to
the queries asked before. -/
def equivalent (st : State) (prelude : Prelude) (st' : State) (timeout : Nat) (cache : QueryCache) : IO (Option Bool) := do
  -- Mutants change only expressions, so the declarations are the same.
  if { st with defs := #[] }.prelude != { st' with defs := #[] }.prelude || st.defs.size != st'.defs.size then return none
  let mut result := some true
  for (name, ps, _, body) in st.defs, (name', ps', _, body') in st'.defs do
    if body == body' then continue
    if name != name' || ps.map (·.1) != ps'.map (·.1) then return none
    let vars := ps.map fun (x, t) => { name := x, role := .input, isPub := false, ty := t, span := default : CVar }
    -- The original, applied to the parameters, and the mutant's body.
    let applied := if ps.isEmpty then itemSym name else s!"({itemSym name} {" ".intercalate (ps.toList.map (quote ·.1.toString))})"
    result := both result (← equal st prelude vars #[(applied, body')] timeout cache)
    if result == some false then return result
  let ts := todo st
  for t' in todo st' do
    let c' := t'.comp
    let some t := ts.find? (·.key == t'.key) | return none
    let c := t.comp
    -- An item's indexes are missing where it has none, such as after a
    -- mutant drops its last one: they are then all in range, `true`.
    let isIndexes (l : String) := l.startsWith "indexes "
    let (is, fs) := (formulas c).partition (isIndexes ·.1)
    let (is', fs') := (formulas c').partition (isIndexes ·.1)
    if fs.map (·.1) != fs'.map (·.1) then return none
    let lookup (xs : Array (String × String)) (l : String) := ((xs.find? (·.1 == l)).map (·.2)).getD "true"
    let labels := ((is ++ is').map (·.1)).toList.eraseDups
    let pairs := ((fs.zip fs').map fun ((_, a), (_, b)) => (a, b))
      ++ labels.toArray.map (fun l => (lookup is l, lookup is' l))
    let pairs := pairs.filter fun (a, b) => a != b
    result := both result (← equal st prelude c.vars pairs timeout cache)
    if result == some false then return result
  return result

/-- The mutants to run (`Reqs/Mutate#selecting-mutants`): those of the
component `comp?`, if any; those named by `ids`, if any; and those that
`touched` keeps, such as those of the items that a patch touches. Of
those, `sample?` of them, if given, chosen by `seed`; and of those, the
shard `k` of `n`, if `shard?` is `(k, n)`. A mutant is sampled, and
sharded, by its identifier alone, so a larger sample contains a smaller
one, and the shards of a selection partition it. -/
def select (all : Array Mutant) (comp? : Option Name) (ids : Array String) (sample? : Option Nat) (seed : Nat)
    (touched : Mutant → Bool := fun _ => true) (shard? : Option (Nat × Nat) := none) : Array Mutant :=
  let ofComp (m : Mutant) := comp?.all (m.comp? == some ·)
  let named (m : Mutant) := ids.isEmpty || ids.contains m.id
  let ms := all.filter fun m => ofComp m && named m && touched m
  let sampled : Std.HashSet String := match sample? with
    | none => .ofArray (ms.map (·.id))
    | some n =>
      let rank (m : Mutant) := fnv1a s!"{seed}\x00{m.id}"
      let ranked := ms.qsort fun a b => rank a < rank b
      .ofArray ((ranked.zipIdx.filter fun (_, i) => takes i n).map (·.1.id))
  let sharded (m : Mutant) := shard?.all fun (k, n) => inShard (fnv1a m.id).toNat k n
  all.filter fun m => chosen (ofComp m) (named m) (touched m) (sampled.contains m.id) (sharded m)

/-- What a mutant changes, such as `` `<` to `<=` ``. -/
def Mutant.change (m : Mutant) : String :=
  if m.after.isEmpty then s!"`{normalize m.before}` removed" else s!"`{normalize m.before}` changed to `{normalize m.after}`"

def survivedMsg (m : Mutant) (mayBeEquivalent inconclusive : Bool) : Msg :=
  { code? := some "F0613", headline := s!"no check rejects this change to `{Fren.Core.showComp m.item}`"
    label? := some m.change
    notes := #[s!"note: the mutant is `{m.id}`"]
      ++ (if inconclusive then #["note: some check that passes on the spec is inconclusive on the mutant"] else #[])
      ++ (if mayBeEquivalent then #["note: the solver could not tell whether the mutant means what the spec means"] else #[])
      ++ (if m.comp?.isNone then
          #[s!"note: the expectations that read `{Fren.Core.showComp m.item}` change with it, and cannot reject the change alone"] else #[])
      ++ #["help: add an expectation or a cover goal that the change breaks, or say what the spec means more exactly"]
    fixes := #[{ msg := "the mutant", replacement := m.after }] }

def missedMsg (m : Mutant) (tests : Nat) : Msg :=
  { code? := some "F0614", headline := s!"testing does not reject this change to `{Fren.Core.showComp m.item}`, which the checks do"
    label? := some m.change
    notes := #[s!"note: the mutant is `{m.id}`", s!"note: none of {tests} tests per component found a behaviour that tells it apart"]
    fixes := #[{ msg := "the mutant", replacement := m.after }] }

def plural (n : Nat) (w : String) : String := s!"{n} {w}{if n == 1 then "" else "s"}"

/-- A line of the report: `what`'s mutants and kill rate. -/
def Tally.line (t : Tally) (what : String) (testing : Bool) : String :=
  let rate := match t.rate? with | some r => s!" ({r}%)" | none => ""
  let rest := (if t.equivalent > 0 then [s!"{t.equivalent} equivalent"] else [])
    ++ (if t.unviable > 0 then [s!"{t.unviable} unviable"] else [])
    ++ (if testing && t.missed > 0 then [s!"{t.missed} missed by testing"] else [])
  s!"{what}: {t.killed} of {plural (t.killed + t.survived) "mutant"} killed{rate}" ++ String.join (rest.map (", " ++ ·))

end FrenCli.Mutate
