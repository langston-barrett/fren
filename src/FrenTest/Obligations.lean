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
-- Each kind alone, so that a check whose first query changes fails here
-- whichever kinds are selected.
#guard CheckKind.all.all fun k => (questionsAsked full #[k]).1
#guard CheckKind.all.all fun k => (questionsAsked { full with laws := #[] } #[k]).1
-- Realizability, and every other kind, of an item without assumptions,
-- whose question of their consistency has an empty context.
#guard questionsAsked { full with assumes := #[] } == (true, 21)
#guard ((questionsOf (fun _ => backend) { full with assumes := #[] } #[.realizable]).run #[]).1.any fun q =>
  q.part == "assumptions" && q.hyps.isEmpty && q.consistency

/-- The evidence and script of the obligation of `c` under the laws, with
the call `i` set to testing, as `obligationsOf` gives them, and the
solver's, with the hypotheses and goal of the query of `untested`'s vacuity
under the laws, which `checkCompLawful` asks of it. -/
private def lawsWithTestedCall (c : Comp String) (untested : Comp String) : Option String × Option String :=
  let tested : Tested := { insts := #[`i] }
  let text (hyps : Array (Name × String)) (goal : String) : String := s!"{hyps} {goal}"
  let ((os : Array Obligation), _) :=
    (obligationsOf (fun _ => backend) (fun _ hyps goal => pure (text hyps goal)) c #[.vacuity] tested {}).run #[]
  let (_, asked) := (checkCompLawful (fun _ => backend) untested #[.vacuity]).run #[]
  ((os.find? (·.part == "laws")).map fun o => s!"{o.evidence} {o.script}",
    asked.back?.map fun (hyps, goal) => s!"solver {text hyps goal}")

-- A call set to testing has its assumptions cleared (`Comp.untested`), and
-- the question under the laws, which the solver is asked, has the context
-- that it is asked with, not the item's.
#guard let (dumped, asked) := lawsWithTestedCall full (full.untested { insts := #[`i] } #[.vacuity]).1
  dumped.isSome && dumped == asked
#guard (lawsWithTestedCall full full).1 != (lawsWithTestedCall full full).2

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

-- A definition is unfolded without capture: the bound name that would
-- capture its argument's free name is renamed apart.
#guard (canonical (script ["(define-fun f ((y Int)) Bool (forall ((x Int)) (> x y)))", "(assert (not (f x)))"]) false).goal ==
  "(forall ((x#s0 Int)) (> x#s0 x))"
-- At its use, a definition without parameters is not a bound name's, and
-- a binder that would capture a free name of its body is renamed apart.
#guard (canonical (script ["(define-fun d () Int x)", "(assert (not (forall ((x Int)) (> x d))))"]) false).goal ==
  "(forall ((x#s0 Int)) (> x#s0 x))"
#guard (canonical (script ["(define-fun d () Int 3)", "(assert (not (forall ((d Int)) (> d 0))))"]) false).goal ==
  "(forall ((d Int)) (> d 0))"
#guard (canonical (script ["(define-fun f ((y Int)) Bool (> y n))", "(assert (not (forall ((n Int)) (f n))))"]) false).goal ==
  "(forall ((n#s0 Int)) (> n#s0 n))"
-- A definition's parameter, and a recursive definition's, is its own,
-- not an earlier definition's of the same name.
#guard (canonical (script ["(define-fun y () Int 7)", "(define-fun f ((y Int)) Int (+ y 1))",
    "(assert (not (> (f 2) 0)))"]) false).goal == "(> (+ 2 1) 0)"
#guard (canonical (script ["(define-fun y () Int 7)", "(define-fun-rec g ((y Int)) Int (g y))",
    "(assert (not (> (g 2) 0)))"]) false).signature == #["(define-fun-rec g ((y Int)) Int (g y))"]
#guard (canonical (script ["(define-fun T () Int 7)", "(declare-datatypes ((L 1)) ((par (T) ((nil) (cons (hd T) (tl (L T)))))))",
    "(declare-const l (L Int))", "(assert (not (= l (as nil (L Int)))))"]) false).signature ==
  #["(declare-const l (L Int))", "(declare-datatypes ((L 1)) ((par (T) ((nil) (cons (hd T) (tl (L T)))))))"]
-- A `match` case binds its pattern's variables: unfolding a definition
-- into a case, and substituting an argument into one, rename a variable
-- that would capture, and a constant that only a pattern names is not used.
#guard (canonical (script ["(define-fun d () Int x)", "(declare-const l L)",
    "(assert (not (= 0 (match l ((nil 0) ((cons x r) (+ x d)))))))"]) false).goal ==
  "(= 0 (match l ((nil 0) ((cons x#s0 r) (+ x#s0 x)))))"
#guard (canonical (script ["(define-fun f ((y Int)) Int (match l ((nil y) ((cons x r) (+ x y)))))",
    "(assert (not (> (f x) 0)))"]) false).goal == "(> (match l ((nil x) ((cons x#s0 r) (+ x#s0 x)))) 0)"
-- And so does one whose scrutinee is an application.
#guard (canonical (script ["(define-fun d () Int x)", "(declare-fun g (Int) L)",
    "(assert (not (= 0 (match (g 1) ((nil 0) ((cons x r) (+ x d)))))))"]) false).goal ==
  "(= 0 (match (g 1) ((nil 0) ((cons x#s0 r) (+ x#s0 x)))))"
#guard (canonical (script ["(declare-const x Int)", "(declare-const l L)",
    "(assert (not (= 0 (match l ((nil 0) ((cons x r) x))))))"]) false).signature == #["(declare-const l L)"]
-- Lean's `✝` and `«»` go, but not where two names would be one.
#guard (canonical (script ["(declare-const x✝ Int)", "(assert (not (> x✝ 0)))"]) false).goal == "(> x 0)"
#guard (canonical (script ["(declare-const x✝ Int)", "(declare-const x Int)", "(assert (not (> x✝ x)))"]) false).goal ==
  "(> x✝ x)"
#guard (canonical (script ["(declare-const «x» Int)", "(declare-const x Int)", "(assert (not (> «x» x)))"]) false).goal ==
  "(> «x» x)"
-- Quantifiers are merged only where no name would be bound twice.
#guard (canonical (script ["(assert (not (forall ((x Int)) (forall ((x Int)) (> x 0)))))"]) false).goal ==
  "(forall ((x Int)) (forall ((x Int)) (> x 0)))"
#guard (canonical (script ["(assert (not (forall ((x Int)) (forall ((y Int)) (> x y)))))"]) false).goal ==
  "(forall ((x Int) (y Int)) (> x y))"

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
