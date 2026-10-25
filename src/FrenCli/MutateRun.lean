-- keep-sorted start
import FrenCli.Mutate
import FrenCli.MutateOutcome
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
open Fren.Core (CheckResult Msg)

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

/-- A component, global expectation or refinement, with the checks that
`fren check` runs on it. -/
structure Todo where
  comp : CComp
  global : Bool
  kinds : Array Fren.Core.CheckKind
  refinement : Bool

/-- What `fren check` checks in the spec `st`, in order. -/
def todo (st : State) : Array Todo :=
  st.comps.map (⟨·, false, Fren.Core.kindsFor false, false⟩) ++ st.globals.map (⟨·, true, Fren.Core.kindsFor true, false⟩)
    ++ st.refinements.map (⟨·, false, Fren.Core.CheckKind.all.filter Fren.Core.refinementRuns, true⟩)

/-- The key of its results. -/
def Todo.key (t : Todo) : String :=
  if t.global then s!"expect {t.comp.path}::{(t.comp.props[0]?.map (·.name)).getD .anonymous}"
  else if t.refinement then s!"refine {t.comp.path}" else s!"comp {t.comp.path}"

/-- A definedness check names its index by its position in the
constraint, which a mutant that drops an earlier index changes. So the
index is named by its text instead, `chars` being the text of `c`'s file,
and how many indexes of the same text come before it in the constraint. -/
def indexKey (chars : Array Char) (c : CComp) (r : CheckResult) : String := Id.run do
  let some k := r.index? | return ""
  let some n := r.prop? | return toString k
  let here := c.indexes.filter (·.1 == n) |>.map fun (_, _, sp, _) => idText (String.ofList (chars.extract sp.start sp.stop).toList)
  let some t := here[k]? | return toString k
  return s!"{t}#{((here.extract 0 k).filter (· == t)).size}"

/-- The results of `c`, in the file `chars`, each with the key of its
check. -/
def keyed (chars : Array Char) (c : CComp) (rs : Array CheckResult) : Array (String × CheckResult) :=
  rs.map fun r => (s!"{repr r.kind}|{r.prop?}|{r.target?}|{indexKey chars c r}", r)

/-- Whether some check of `after` kills the mutant, against the results
`before` of the original, both keyed. -/
def kills (before after : Array (String × CheckResult)) : Bool :=
  after.any fun (k, r) => before.any fun (k', b) => k == k' && killsCheck b.verdict r.verdict

/-- Whether some check that passes on the original is inconclusive in
`after`. -/
def inconclusive (before after : Array (String × CheckResult)) : Bool :=
  after.any fun (k, r) => r.verdict == .inconclusive && before.any fun (k', b) => k == k' && b.verdict == .pass

def PropKind.name : PropKind → String
  | .assume => "assume"
  | .req => "req"
  | .expect => "expect"

/-- The formulas of `c` that its checks read, labelled. -/
def formulas (c : CComp) : Array (String × String) :=
  c.props.map (fun p => (s!"{PropKind.name p.kind} {p.name}", p.smt))
    ++ c.props.filterMap (fun p => p.trigger?.map (s!"trigger {p.name}", ·))
    ++ c.defs.map (fun (d, e) => (s!"def {d}", e))
    ++ c.insts.flatMap (fun i => #[(s!"bindings {i.name}", i.bindings), (s!"behaviour {i.name}", i.behaviour)]
      ++ i.assumes.map fun (n, a) => (s!"assume {i.name} {n}", a))
    ++ c.indexes.mapIdx (fun k (n, _, _, goal) => (s!"index {k} {n}", goal))

/-- Everything that `c`'s checks read, with the spec's `prelude`: a mutant
that leaves it alone leaves their results alone. -/
def fingerprint (prelude : String) (c : CComp) : String :=
  let vars := c.vars.map fun v => s!"{v.name} {repr v.role} {v.isPub} {v.isDet} {v.ty.show}"
  "\n".intercalate ([prelude] ++ vars.toList ++ (formulas c).toList.map fun (l, f) => s!"{l}: {f}")

/-- Combines the answers to whether parts are equivalent: `some false` if
some part differs, `none` if some part is unknown, else `some true`. -/
def both (a b : Option Bool) : Option Bool :=
  if a == some false || b == some false then some false else if a.isNone || b.isNone then none else some true

/-- Whether the solver shows that the formulas of each pair are equal for
all values of `vars` and every interpretation: `some false` if some pair
can differ, `none` if it cannot tell. -/
def equal (st : State) (vars : Array CVar) (pairs : Array (String × String)) (timeout : Nat) : IO (Option Bool) := do
  if pairs.isEmpty then return some true
  let strings := st.usesStrings || st.usesSeqs
  let sets := st.usesSets || st.usesSeqs
  let options := String.join ((Fren.Core.solverOptions strings sets).map fun (o, v) => s!"(set-option :{o} {v})\n")
  let goal := conj (pairs.map fun (a, b) => s!"(= {a} {b})")
  match ← runQuery (Fren.Core.logic .expect (strings || sets) st.usesProjection) (options ++ st.prelude) vars timeout none #[] goal false with
  | .unsat => return some true
  | .sat _ => return some false
  | .unknown _ => return none

/-- The time limit, in seconds, of each query that asks whether a mutant
is equivalent: the answer only refines the report, so it is kept short. -/
def equivalenceTimeout : Nat := 1

/-- Whether the solver shows that the spec `st'` of a mutant means what the
original `st` means (`Reqs/Mutate#equivalent-mutants`): each defined function, and each
formula of each component, global expectation and refinement, is equivalent to the
original's. -/
def equivalent (st st' : State) (timeout : Nat) : IO (Option Bool) := do
  -- Mutants change only expressions, so the declarations are the same.
  if { st with defs := #[] }.prelude != { st' with defs := #[] }.prelude || st.defs.size != st'.defs.size then return none
  let mut result := some true
  for (name, ps, _, body) in st.defs, (name', ps', _, body') in st'.defs do
    if body == body' then continue
    if name != name' || ps.map (·.1) != ps'.map (·.1) then return none
    let vars := ps.map fun (x, t) => { name := x, role := .input, isPub := false, ty := t, span := default : CVar }
    -- The original, applied to the parameters, and the mutant's body.
    let applied := if ps.isEmpty then itemSym name else s!"({itemSym name} {" ".intercalate (ps.toList.map (quote ·.1.toString))})"
    result := both result (← equal st vars #[(applied, body')] timeout)
    if result == some false then return result
  let ts := todo st
  for t' in todo st' do
    let c' := t'.comp
    let some t := ts.find? (·.key == t'.key) | return none
    let c := t.comp
    let fs := formulas c
    let fs' := formulas c'
    if fs.map (·.1) != fs'.map (·.1) then return none
    let pairs := (fs.zip fs').filterMap fun ((_, a), (_, b)) => if a == b then none else some (a, b)
    result := both result (← equal st c.vars pairs timeout)
    if result == some false then return result
  return result

/-- The mutants to run (`Reqs/Mutate#selecting-mutants`): those of the component `comp?`,
if any; those named by `ids`, if any; and of those, `sample?` of them, if
given, chosen by `seed`. A mutant is sampled by its identifier alone, so a
larger sample contains a smaller one. -/
def select (all : Array Mutant) (comp? : Option Name) (ids : Array String) (sample? : Option Nat) (seed : Nat) : Array Mutant :=
  let ms := all.filter fun m => comp?.all (m.comp? == some ·) && (ids.isEmpty || ids.contains m.id)
  match sample? with
  | none => ms
  | some n =>
    let rank (m : Mutant) := fnv1a s!"{seed}\x00{m.id}"
    let chosen := (ms.qsort fun a b => rank a < rank b).extract 0 n |>.map (·.id)
    ms.filter (chosen.contains ·.id)

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
      ++ #["help: add an expectation that the change breaks, or say what the spec means more exactly"]
    fixes := #[{ msg := "the mutant", replacement := m.after }] }

def missedMsg (m : Mutant) (tests : Nat) : Msg :=
  { code? := some "F0614", headline := s!"testing does not reject this change to `{Fren.Core.showComp m.item}`, which the checks do"
    label? := some m.change
    notes := #[s!"note: the mutant is `{m.id}`", s!"note: none of {tests} tests per component found a behaviour that tells it apart"]
    fixes := #[{ msg := "the mutant", replacement := m.after }] }

/-- The mutants of a component, or of a constant or function, by
outcome. -/
structure Tally where
  killed : Nat := 0
  survived : Nat := 0
  equivalent : Nat := 0
  unviable : Nat := 0
  /-- Killed by the solver but not by testing. -/
  missed : Nat := 0

def Tally.add (t : Tally) : Outcome → Tally
  | .killed => { t with killed := t.killed + 1 }
  | .survived => { t with survived := t.survived + 1 }
  | .equivalent => { t with equivalent := t.equivalent + 1 }
  | .unviable => { t with unviable := t.unviable + 1 }

def Tally.merge (a b : Tally) : Tally :=
  { killed := a.killed + b.killed, survived := a.survived + b.survived, equivalent := a.equivalent + b.equivalent
    unviable := a.unviable + b.unviable, missed := a.missed + b.missed }

/-- The share of the mutants that could be killed that were
(`Reqs/Mutate#output`), as a whole percentage, rounded down; `none` if none
could be. -/
def Tally.rate? (t : Tally) : Option Nat :=
  let n := t.killed + t.survived
  if n == 0 then none else some (100 * t.killed / n)

def plural (n : Nat) (w : String) : String := s!"{n} {w}{if n == 1 then "" else "s"}"

/-- A line of the report: `what`'s mutants and kill rate. -/
def Tally.line (t : Tally) (what : String) (testing : Bool) : String :=
  let rate := match t.rate? with | some r => s!" ({r}%)" | none => ""
  let rest := (if t.equivalent > 0 then [s!"{t.equivalent} equivalent"] else [])
    ++ (if t.unviable > 0 then [s!"{t.unviable} unviable"] else [])
    ++ (if testing && t.missed > 0 then [s!"{t.missed} missed by testing"] else [])
  s!"{what}: {t.killed} of {plural (t.killed + t.survived) "mutant"} killed{rate}" ++ String.join (rest.map (", " ++ ·))

end FrenCli.Mutate
