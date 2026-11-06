-- keep-sorted start
import FrenCore.GroundMatching
-- keep-sorted end

-- fren-covers: lang::ground_match_step, lang::ground_parameter_step, lang::ground_extension_step
-- fren-covers: lang::ground_normalization, lang::ground_shape_step, lang::ground_subject_step
-- fren-covers: lang::ground_selection_step, lang::ground_variables_step, lang::ground_join_step
-- fren-covers: lang::ground_listed_step, lang::ground_sentence_lists_step, lang::ground_rule_step
-- fren-covers: lang::ground_preparation_step, lang::ground_instance_list_step, lang::ground_instances_step

namespace FrenTest.GroundMatching

open Fren.Core Fren.Core.GroundMatching

private def app (f : Lean.Name) (xs : List TheoryTerm) : TheoryTerm :=
  xs.foldl TheoryTerm.app (.item f)
private def x : TheoryTerm := .variable `x
private def y : TheoryTerm := .variable `y
private def a : TheoryTerm := .query `a
private def b : TheoryTerm := .query `b
private def ctx : Context := {
  items := [`g, `f, `p]
  typeOf := fun _ => some .int
}
private def rule (vs : List (Lean.Name × Ty)) (claims : List TheoryTerm)
    (calls : List TheoryTerm := []) (domain : TheoryTerm := .literal "true") : Rule :=
  { sentence := { role := .axiom, variables := vs, domain, calls, claims } }

-- Syntax, type arguments, repeated variables and argument order matter.
#guard matchTerm [(`x, .int)] ctx.typeOf (app `f [x, x]) (app `f [a, a]) == some [(`x, a)]
#guard matchTerm [(`x, .int)] ctx.typeOf (app `f [x, x]) (app `f [a, b]) == none
#guard matchTerm [(`x, .bool)] ctx.typeOf x a == none
#guard matchTerm [(`x, .int)] (fun _ => none) x a == none
#guard matchTerm [] ctx.typeOf (.literal "Int:1") (.literal "Nat:1") == none
#guard matchTerm [(`x, .int)] ctx.typeOf (app `f [x, .sort .int]) (app `f [a, .sort .nat]) == none
#guard matchTerm [(`x, .int)] ctx.typeOf (app `f [x, b]) (app `f [b, a]) == none
#guard matchTerm [(`x, .int)] ctx.typeOf x (.bound 0) == none
#guard matchTerm [(`x, .int)] ctx.typeOf (.all .int x) (.all .int (.bound 0)) == none
#guard matchTerm [(`x, .int)] ctx.typeOf (.all .int (.bound 0)) (.all .int (.bound 0)) == some []

private def swap := rule [(`x, .int), (`y, .int)] [app `f [x, y], app `f [y, x]]
#guard matchApplications ctx swap { applications := [app `f [a, b]] } == []
#guard (matchApplications ctx swap { applications := [app `f [a, b], app `f [b, a]] }).length == 2
#guard (instances ctx swap { applications := [app `f [a, b]] }).isEmpty
#guard (instances ctx swap { applications := [app `f [a, b], app `f [b, a]] }).length == 2

-- A compound anchor binds its proper subterms, including nested apps.
private def nested := rule [(`x, .int)] [app `f [app `f [x]], app `f [x]]
#guard nested.anchors ctx.items == [app `f [app `f [x]]]
#guard matchApplications ctx nested { applications := [app `f [app `f [a]]] } == [[(`x, a)]]

-- All calls match together, with their output arguments, using the same
-- substitution as the anchors. A function term is never a call witness.
private def withCall := rule [(`x, .int)] [app `f [x]] [app `p [x, b]]
#guard (instances ctx withCall { applications := [app `f [a], app `p [a, b]] }).isEmpty
#guard (instances ctx withCall { applications := [app `f [a]], calls := [app `p [b, b]] }).map (·.claims) ==
  [[app `f [b]]]
#guard (instances ctx withCall { applications := [app `f [a]], calls := [app `p [a, b]] }).length == 1

-- Here the function is the subject, so both its anchor and the call must
-- agree; neither a second call nor a different output is interchangeable.
private def callCtx := { ctx with items := [`g, `p, `f] }
#guard (instances callCtx withCall { applications := [app `f [a]], calls := [app `p [b, b]] }).isEmpty
#guard (instances callCtx withCall { applications := [app `f [a]], calls := [app `p [a, a]] }).isEmpty
#guard (instances callCtx withCall { applications := [app `f [a]], calls := [app `p [a, b]] }).length == 1
private def twoCalls := rule [(`x, .int)] [app `f [x]] [app `p [x, a], app `p [x, b]]
#guard (instances callCtx twoCalls { applications := [app `f [a]], calls := [app `p [a, a]] }).isEmpty
#guard (instances callCtx twoCalls { applications := [app `f [a]], calls := [app `p [a, a], app `p [a, b]] }).length == 1
private def callOutput := rule [(`x, .int), (`y, .int)] [app `f [y]] [app `p [x, y]]
#guard (instances callCtx callOutput { applications := [app `f [b]], calls := [app `p [a, b]] }).map (·.calls) ==
  [[app `p [a, b]]]
#guard (instances callCtx callOutput { applications := [app `f [b]], calls := [app `p [a, a]] }).isEmpty
private def nestedCall := rule [(`x, .int)] [app `g [x]] [app `p [app `f [x], b]]
#guard (instances callCtx nestedCall { calls := [app `p [app `f [a], b]] }).map (·.claims) ==
  [[app `g [a]]]

-- Query binders are excluded, free query locals are ground. Outside-only
-- unlisted variables remain quantified in the whole returned sentence.
private def outside := rule [(`x, .int), (`localOutside, .int)]
  [app `f [x], .variable `localOutside]
#guard (instances ctx outside { applications := [app `f [.bound 0]] }).isEmpty
#guard (instances ctx outside { applications := [.all .int (app `f [.bound 0])] }).isEmpty
#guard (instances ctx outside { applications := [.ex .int (app `f [.bound 0])] }).isEmpty
#guard (instances ctx outside { applications := [.all .int (app `f [a])] }).length == 1
#guard ((instances ctx outside { applications := [app `f [a]] }).map (·.variables)) ==
  [[(`localOutside, .int)]]
private def unbound := rule [(`x, .int), (`y, .int)] [app `f [x], app `g [y]]
#guard !unbound.instantiable ctx
#guard (instances ctx unbound { applications := [app `f [a]] }).isEmpty

private def boolCtx : Context := { ctx with
  typeOf := fun t => if t == .literal "true" || t == .literal "false" then some .bool else some .int
  listed := fun ty => if ty == .bool then some [.literal "true", .literal "false"] else none }
private def listed := rule [(`x, .int), (`flag, .bool), (`unused, .bool)]
  [app `f [x], .variable `flag]
#guard (instances boolCtx listed { applications := [app `f [a]] }).length == 2
#guard ((instances boolCtx listed { applications := [app `f [a]] }).map (·.variables)) ==
  [[(`unused, .bool)], [(`unused, .bool)]]
#guard (instances { boolCtx with listed := fun _ => some [] } listed
  { applications := [app `f [a]] }).isEmpty
private def badBoolCtx : Context := { boolCtx with
  listed := fun ty => if ty == .bool then some [.literal "true", .bound 0, .literal "Int:1"] else none }
#guard (instances badBoolCtx listed { applications := [app `f [a]] }).length == 1

-- Subjectless facts contribute once, retaining outside quantifiers.
#guard (instances ctx (rule [(`x, .int)] [x]) {}).length == 1
#guard (instances ctx (rule [] [app `f [a]]) {}).isEmpty

-- Aliases expand transitively in their own scope; applied item heads and
-- literal operators remain opaque. The matcher normalizes patterns and terms.
private def defs : List (TheoryTerm × TheoryTerm) :=
  [(.query `localOut, .query `localWhere), (.query `localWhere, .query `localLet), (.query `localLet, .item `CONST), (.item `CONST, a)]
#guard same defs (.query `localOut) a
#guard same [(.query `x, .query `x), (.query `x, a)] (.query `x) a
#guard !same [(.query `x, a), (.query `y, .query `x)] (.query `y) (.query `x)
#guard !same [(.item `f, a)] (app `f [b]) a
#guard !same [] (app `plus [a, .literal "0"]) a
#guard normalize (definitions defs) (.query `missing) == .query `missing
#guard (instances { ctx with definitions := defs } (rule [(`x, .int)] [app `f [x]])
  { applications := [app `f [.query `localOut], app `f [a]] }).length == 1

#guard (instances { ctx with definitions := defs } (rule [] [app `f [.query `localOut]])
  { applications := [app `f [a]] }).map (·.claims) ==
  [[app `f [a]]]
#guard normalize [(.bound 0, a), (.literal "1", b)] (.bound 0) == .bound 0
#guard normalize [(.bound 0, a), (.literal "1", b)] (.literal "1") == .literal "1"
#guard (matchApplications ctx swap { applications := [app `f [a, b], app `f [b, a], app `f [a, b]] }).length == 2

-- The spine retains argument and type-argument order, and suppresses
-- curried prefixes while visiting applications in arguments and builtins.
#guard applications ctx.items (app `f [a, b]) == [app `f [a, b]]
#guard applications ctx.items (app `f [app `g [a], b]) == [app `f [app `g [a], b], app `g [a]]
#guard applications ctx.items (.app (.literal "not") (app `f [a])) == [app `f [a]]
#guard (rule [(`x, .int)] [app `g [app `f [x]]]).subject ctx.items == some `f
#guard subjectApps none [app `f [a], .app (.query `higher) a] == []
#guard (rule [(`x, .int)] [.all .int (app `f [x])]).instantiable ctx

-- A closed application under an inner quantifier still supplies an
-- anchor; one depending on that quantifier's variable does not.
private def inner := rule [(`x, .int)] [.all .int (app `f [.bound 0]), app `f [x]]
#guard inner.anchors ctx.items == [app `f [x]]
#guard (instances ctx inner { applications := [app `f [a]] }).map (·.claims) ==
  [[.all .int (app `f [.bound 0]), app `f [a]]]
#guard (instances ctx (rule [] [.all .int (app `f [.bound 0])])
  { applications := [.all .int (app `f [.bound 0])] }).length == 1

-- Ground query locals cannot become sentence holes on a later occurrence.
private def capture := rule [(`x, .int), (`y, .int)]
  [app `f [x, y], .all .int (.app (.app (.literal "equal") x) (.bound 0))]
#guard (instances ctx capture { applications := [app `f [.query `y, b]] }).map (·.claims) ==
  [[app `f [.query `y, b], .all .int (.app (.app (.literal "equal") (.query `y)) (.bound 0))]]
#guard matchApplications { ctx with definitions := [(.query `alias, x)] }
  (rule [(`x, .int)] [app `f [.query `alias]]) { applications := [app `f [a]] } == [[(`x, a)]]

-- Listed values are normalized in the same environment as the query.
private def aliasBoolCtx : Context := { boolCtx with
  definitions := [(.query `yes, .literal "true")]
  listed := fun ty => if ty == .bool then some [.query `yes] else none }
#guard (instances aliasBoolCtx listed { applications := [app `f [a]] }).map (·.claims) ==
  [[app `f [a], .literal "true"]]

-- Call witnesses use the same alias environment as the function anchors.
#guard (instances { callCtx with definitions := defs } withCall
  { applications := [app `f [a]], calls := [app `p [.query `localOut, b]] }).map (·.calls) ==
  [[app `p [a, b]]]

-- The domain and the relations of calls are part of the whole returned
-- sentence. An unlisted parameter used only in the domain stays quantified.
private def bounded := rule [(`x, .int), (`n, .int)] [app `f [x]] [app `p [x, b]]
  (.app (.literal "positive") (.variable `n))
#guard (instances callCtx bounded { applications := [app `f [a]], calls := [app `p [a, b]] }).map
    (fun s => (s.variables, s.domain, s.calls, s.claims)) ==
  [([(`n, .int)], .app (.literal "positive") (.variable `n), [app `p [a, b]], [app `f [a]])]

end FrenTest.GroundMatching
