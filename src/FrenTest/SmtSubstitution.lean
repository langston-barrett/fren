-- keep-sorted start
import FrenCli.SeqElems
-- keep-sorted end

/-! Scope regressions for the SMT representation, including forms that
Fren's surface syntax does not expose directly. UI tests exercise both frontends. -/
-- fren-covers: cli::substitution_scope
open FrenCli.SeqElems

private def checkSubst (input : String) (replacements : Array (String × String))
    (expected : String) : IO Unit := do
  let result := (parse input).subst (replacements.map fun (k, v) => (k, parse v))
  unless result == parse expected do
    throw <| IO.userError s!"substitution produced {result}; expected {expected}"

#eval do
  checkSubst "(forall ((x Int)) (= x b))" #[("b", "x")]
    "(forall ((|fren.subst.0| Int)) (= |fren.subst.0| x))"
  checkSubst "(exists ((x Int)) (= x b))" #[("b", "x")]
    "(exists ((|fren.subst.0| Int)) (= |fren.subst.0| x))"
  checkSubst "(lambda ((x Int)) (+ x b))" #[("b", "x")]
    "(lambda ((|fren.subst.0| Int)) (+ |fren.subst.0| x))"
  checkSubst "(fren.forall#2 ((x Int)) (= x b))" #[("b", "x")]
    "(fren.forall#2 ((|fren.subst.0| Int)) (= |fren.subst.0| x))"
  checkSubst "(let ((x b) (y x)) (+ x b y))" #[("b", "x"), ("x", "z")]
    "(let ((|fren.subst.0| x) (y z)) (+ |fren.subst.0| x y))"
  checkSubst "(forall ((x Int)) (and (= x b) (exists ((x Int)) (= x b))))"
    #[("b", "x")]
    "(forall ((|fren.subst.0| Int)) (and (= |fren.subst.0| x) (exists ((|fren.subst.0| Int)) (= |fren.subst.0| x))))"
  checkSubst "(forall ((x Int)) (= x b))" #[("x", "b")]
    "(forall ((x Int)) (= x b))"
  checkSubst "(forall ((x Int) (y Int)) (= x b y |fren.subst.0|))"
    #[("b", "(+ x y |fren.subst.1|)")]
    "(forall ((|fren.subst.2| Int) (|fren.subst.3| Int)) (= |fren.subst.2| (+ x y |fren.subst.1|) |fren.subst.3| |fren.subst.0|))"
