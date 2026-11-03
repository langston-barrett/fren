-- keep-sorted start
import FrenCli.Elab
import FrenCore.Obligations
-- keep-sorted end

/-! The questions of `Fren.Core.questionsOf` are the queries that the checks
ask (`Reqs/Cli#obligations`). A backend that answers every query
`unknown` has every check ask its first queries and nothing after them,
with no cores to minimize and no models to read, and every question that
an answer could skip, such as redundancy's after its consistency, asked:
so the queries that `checkCompLawful` asks of it are exactly the
questions, in order, for items with every part that a question reads. And
the canonical form of a script (`Fren.Core.canonical`) does not depend on
the order of its commands, its options or its definitions. -/

namespace FrenTest.Obligations

open Lean Fren.Core

/-- Each query, as its hypotheses' names and formulas and its goal. -/
abbrev Asked := Array (Array (Name × String) × String)

private def backend : Backend (StateM Asked) String String where
  query hyps goal _ := do
    modify (·.push (hyps, goal))
    return .unknown "not asked"
  falseF := "false"
  notF f := s!"(not {f})"
  conj fs := s!"(and {" ".intercalate fs.toList})"
  existsOutputs f := pure s!"(exists outputs {f})"
  pin _ _ := pure none
  pinVariant _ _ := pure none
  render _ v := pure v
  prime f := s!"(prime {f})"
  samePrimed n := s!"(same {n})"
  subst ds f := s!"(subst {ds.size} {f})"

private def call : Inst String :=
  { name := `i, comp := `q, bindings := "bind", behaviour := "behave", assumes := #[(`qa, "qa"), (`qb, "qb")] }

private def site (prop : Name) (k : Nat) (place : IndexPlace) (goal : String) : IndexSite String :=
  { prop, k, place, goal }

/-- An item with every part that a question reads. -/
private def full : Comp String :=
  { path := `p
    vars := #[{ name := `x, role := .input, isPub := true }, { name := `y, role := .output, isPub := true, isDet := true }]
    assumes := #[(`a, "a"), (`b, "b")]
    reqs := #[(`r, "r"), (`s, "s")]
    expects := #[(`e, "e")]
    covers := #[(`g, "g")]
    insts := #[call]
    triggers := #[(`r, "tr")]
    defs := #[(`y, "(= y d)", "d")]
    indexes := #[site `r 0 .prop "in_range", site `a 0 .assume "in_range_a", site `i 0 (.binding 0) "in_range_i"]
    tables := #[{ site := site `s 0 .prop "complete", goal := .completeness .table },
                { site := site `s 1 .prop "disjoint", goal := .disjointness .table 0 1 },
                { site := site `s 2 .prop "pre", goal := .precondition `f `pre },
                { site := site `s 3 .prop "reach", goal := .reachability .match 0 }]
    posts := #[(`post, "post")]
    laws := #[(`law, "law")]
    lawsOf := `T }

private def questionsAsked (c : Comp String) (kinds : Array CheckKind := CheckKind.all) : Bool × Nat :=
  let (_, asked) := (checkCompLawful (fun _ => backend) c kinds).run #[]
  let (qs, _) := (questionsOf (fun _ => backend) c kinds).run #[]
  (asked == qs.map (fun q => (q.hyps, q.goal)), qs.size)

/-- A fixed carrier, whose realizability asks one question. -/
private def carrier : Comp String :=
  { path := `c, vars := #[{ name := `y, role := .output, isPub := true }], assumes := #[], reqs := #[(`r, "r")]
    expects := #[], triggers := #[], inhabitation := true }

#guard questionsAsked full == (true, 23)
-- Without laws, no question of the item's vacuity under them.
#guard questionsAsked { full with laws := #[] } == (true, 22)
#guard questionsAsked carrier #[.realizable] == (true, 1)
-- Without assumptions, there is no question of their consistency.
#guard questionsAsked { full with assumes := #[], defs := #[], indexes := #[] } #[.redundancy] == (true, 3)
#guard questionsAsked { full with reqs := #[] } == (true, 20)

/-! The canonical form of a script. -/

private def script (lines : List String) : String := "\n".intercalate lines ++ "\n"

-- The options, the solver's commands and the comments go; a definition is
-- unfolded and goes; declarations and sentences are sorted, each once; the
-- goal is the last assertion's negation.
#guard canonical (script ["(set-logic ALL)", "(set-option :produce-models true)", "(define-fun |::f| ((|x| Int)) Int (* 2 |x|))",
    "(declare-const |n| Int)", "(declare-const |m| Int)", "(assert (> |n| 0)) ; a", "(assert (> |n| 0)) ; again",
    "(assert (= |m| (|::f| |n|))) ; r", "(assert (not (> |m| 1)))", "(check-sat)", "(reset)"]) false ==
  { signature := #["(declare-const m Int)", "(declare-const n Int)"], sentences := #["(= m (* 2 n))", "(> n 0)"], goal := "(> m 1)" }
-- So two scripts that differ only in those have the same canonical form.
#guard canonical (script ["(declare-const m Int)", "(assert (= m (* 2 n)))", "(declare-const n Int)", "(assert (> n 0))",
    "(assert (not (> m 1)))"]) false ==
  canonical (script ["(set-logic QF_UFDTLIA)", "(define-fun |::f| ((|x| Int)) Int (* 2 |x|))", "(declare-const |n| Int)",
    "(declare-const |m| Int)", "(assert (> |n| 0)) ; a", "(assert (= |m| (|::f| |n|))) ; r", "(assert (not (> |m| 1)))"]) false
-- A question of consistency has the goal `false`, which a front end may
-- leave out, and the sentences `true` and `(not false)` go.
#guard canonical (script ["(declare-const n Int)", "(assert (> n 0))", "(assert (not false))"]) true ==
  canonical (script ["(declare-const n Int)", "(assert (> n 0))"]) true
-- A goal that is a negation stays the goal, though its double negation
-- is written as what it negates.
#guard (canonical (script ["(declare-const n Int)", "(assert (> n 0))", "(assert (not (not (> n 1))))"]) false).goal ==
  "(not (> n 1))"
-- A constant that nothing mentions free goes, even if a binder names it.
#guard (canonical (script ["(declare-const m Int)", "(declare-const n Int)",
    "(assert (not (exists ((m Int)) (= m n))))"]) false).signature == #["(declare-const n Int)"]
-- A definition's parameters are substituted, but not under a binder that
-- rebinds them.
#guard (canonical (script ["(define-fun f ((x Int)) Bool (and (> x 0) (forall ((x Int)) (> x 1))))",
    "(assert (not (f n)))"]) false).goal == "(and (> n 0) (forall ((x Int)) (> x 1)))"

/-! The canonical names of symbols are those of `fren check`'s queries,
without their `|`s. -/

private def unquoted (s : String) : String := ((s.drop 1).dropEnd 1).toString

#guard (ItemSymbol.datatype `m.E).text == unquoted (FrenCli.dataSortSym `m.E)
#guard (ItemSymbol.variant `m.E `A).text == unquoted (FrenCli.ctorSym `m.E `A)
#guard (ItemSymbol.payload `m.E `A 1).text == unquoted (FrenCli.payloadSym `m.E `A 1)
#guard (ItemSymbol.record `m.P).text == unquoted (FrenCli.recordCtorSym `m.P)
#guard (ItemSymbol.field `m.P `a).text == unquoted (FrenCli.fieldSym `m.P `a)
#guard (ItemSymbol.item `m.f).text == unquoted (FrenCli.itemSym `m.f)

end FrenTest.Obligations
