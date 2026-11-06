-- keep-sorted start
import FrenCore.Check.Types
import FrenCore.SeqElems
import FrenCore.Str
-- keep-sorted end

/-!
# Solver logics, symbols and options

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type}

/-- The SMT-LIB logic of a check's queries (`cli::logic`): realizability
quantifies, over outputs, and so does every query of a spec with an
unbounded quantifier, or with a refinement claim whose abstraction has
calls, over whose variables the claim quantifies (`quantified`); a spec
that uses strings or sets (`extended`) needs `ALL`, and a query that
projects a relation over a type that is not finite (`projection`),
`HO_ALL` (`queryLogic`). -/
def logic (kind : CheckKind) (extended : Bool := false) (projection : Bool := false) (quantified : Bool := false) :
    String :=
  if extended then (if projection then "HO_ALL" else "ALL") else match kind with
    | .realizable => "UFDTLIA"
    | _ => if quantified then "UFDTLIA" else "QF_UFDTLIA"

/-- The logic in which `fren check` asks a query of a check in `logic`:
`HO_ALL` only if the query's script projects a relation (`projects`), and
otherwise `ALL`, as `logic` gives it without a projection
(`cli::logic`). The Lean-hosted front end does the same, by `force-logic`
(`Reqs/Cli#solver-queries`). cvc5's higher-order extension, which
`HO_ALL` turns on, slows every query that it is set for. -/
def queryLogic (logic : String) (projects : Bool) : String :=
  if logic == "HO_ALL" && !projects then "ALL" else logic

/-- Lowering a check's logic by whether its query's script projects a
relation (`projects`) gives the logic of that check with `projects` as its
projection, over every kind, extension and quantification: the logic that
`cli::logic` binds, with `projection?` read per query. -/
theorem queryLogic_logic (k : CheckKind) (e q projects : Bool) :
    queryLogic (logic k e true q) projects = logic k e projects q := by
  cases k <;> cases e <;> cases q <;> cases projects <;> decide

/-- A check whose spec projects no relation keeps its logic, whatever its
script says. -/
theorem queryLogic_unprojected (k : CheckKind) (e q projects : Bool) :
    queryLogic (logic k e false q) projects = logic k e false q := by
  cases k <;> cases e <;> cases q <;> cases projects <;> decide

/-- Whether the SMT-LIB text `f` projects a relation, which only a query in
higher-order logic may (`queryLogic`). A string literal that spells it makes
the query higher-order, which costs time, never an answer. -/
def projectsRelation (f : String) : Bool := occursIn "rel.project" f

#guard projectsRelation "((_ rel.project 0) |r|)"
#guard !projectsRelation "(rel.join |r| |s|)"

/-- Whether `fren check` asks a query in the logic `logic`, given whether
the script it would ask has a `forall` or `exists` (`quantifies`): never a quantified one
in a quantifier-free logic, which is an internal error instead
(`cli::query_logic`). -/
def queryAsked (logic : String) (quantifies : Bool) : Bool :=
  !(logic.startsWith "QF_" && quantifies)

/-- Whether the SMT-LIB text `f` has a quantifier, `forall` or `exists`
(`cli::query_logic`). It reads the text as Fren prints it, a binder list
right after the quantifier, one space apart, as `(forall ((x Int)) ...)`;
a symbol that spells `forall` is quoted, as `|forall|`, and is not one. A
match in a comment, as a hypothesis's name, or in a string literal counts
too, which errs toward not asking the query: a false positive is an
internal `Unknown`, never a wrong answer. -/
def hasQuantifier (f : String) : Bool :=
  ["(forall (", "(exists ("].any (occursIn · f)

#guard hasQuantifier "(forall ((x Int)) x)"
#guard hasQuantifier "(exists ((x Int)) x)"
#guard hasQuantifier "(define-fun f ((y Int)) Bool (forall ((x Int)) (> (g x) y)))"
#guard !hasQuantifier "(and a b)"
#guard !hasQuantifier "(and |forall| |exists|)"
#guard !hasQuantifier "(define-fun f ((y Int)) Bool (> y 0))"

/-- Why a query with a quantifier, which `cli::logic` put in a
quantifier-free logic, is not asked (`cli::query_logic`). -/
def quantifiedQueryReason (logic : String) : String :=
  s!"internal error: a query with a quantifier would be asked in the quantifier-free logic `{logic}`; \
    please report it"

/-- The symbols of cvc5's theories, under `HO_ALL`, that a Fren name can
spell: cvc5 rejects a declaration of any of them, quoted or not, as
shadowing a theory function symbol. Found by declaring each identifier of
cvc5's libraries as a constant. -/
def theorySymbols : Std.HashSet String := .ofList [
  "abs", "and", "arccos", "arccot", "arccsc", "arcsec", "arcsin", "arctan", "bag", "bag.all",
  "bag.card", "bag.choose", "bag.count", "bag.difference_remove", "bag.difference_subtract",
  "bag.filter", "bag.fold", "bag.inter_min", "bag.map", "bag.member", "bag.partition", "bag.setof",
  "bag.some", "bag.subbag", "bag.union_disjoint", "bag.union_max", "bv2nat", "bvadd", "bvand",
  "bvashr", "bvcomp", "bvite", "bvlshr", "bvmul", "bvnand", "bvneg", "bvnego", "bvnor", "bvnot",
  "bvor", "bvredand", "bvredor", "bvsaddo", "bvsdiv", "bvsdivo", "bvsge", "bvsgt", "bvshl",
  "bvsle", "bvslt", "bvsmod", "bvsmulo", "bvsrem", "bvssubo", "bvsub", "bvuaddo", "bvudiv",
  "bvuge", "bvugt", "bvule", "bvult", "bvumulo", "bvurem", "bvusubo", "bvxnor", "bvxor", "concat",
  "cos", "cot", "csc", "distinct", "div", "div_total", "eqrange", "exists", "exp", "ff.add",
  "ff.bitsum", "ff.mul", "ff.neg", "forall", "fp", "fp.abs", "fp.add", "fp.div", "fp.eq", "fp.fma",
  "fp.geq", "fp.gt", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isNormal", "fp.isPositive",
  "fp.isSubnormal", "fp.isZero", "fp.leq", "fp.lt", "fp.max", "fp.min", "fp.mul", "fp.neg",
  "fp.rem", "fp.roundToIntegral", "fp.sqrt", "fp.sub", "fp.to_real", "int.log2", "int.pow2",
  "is_int", "ite", "lambda", "mod", "mod_total", "not", "nullable.is_null", "nullable.is_some",
  "nullable.lift", "nullable.some", "nullable.val", "or", "piand", "pto", "re.comp", "re.diff",
  "re.inter", "re.opt", "re.range", "re.union", "rel.aggr", "rel.group", "rel.iden", "rel.join",
  "rel.join_image", "rel.product", "rel.project", "rel.table_join", "rel.tclosure",
  "rel.transpose", "sbv_to_int", "sec", "select", "sep", "seq.at", "seq.contains", "seq.extract",
  "seq.indexof", "seq.len", "seq.nth", "seq.prefixof", "seq.replace", "seq.replace_all", "seq.rev",
  "seq.suffixof", "seq.unit", "seq.update", "set.all", "set.card", "set.choose", "set.complement",
  "set.comprehension", "set.filter", "set.fold", "set.insert", "set.inter", "set.is_empty",
  "set.is_singleton", "set.map", "set.member", "set.minus", "set.singleton", "set.some",
  "set.subset", "set.union", "sin", "sqrt", "store", "str.at", "str.contains", "str.from_code",
  "str.from_int", "str.in_re", "str.indexof", "str.indexof_re", "str.is_digit", "str.len",
  "str.prefixof", "str.replace", "str.replace_all", "str.replace_re", "str.replace_re_all",
  "str.rev", "str.substr", "str.suffixof", "str.to_code", "str.to_int", "str.to_lower",
  "str.to_re", "str.to_upper", "str.update", "table.aggr", "table.group", "table.join",
  "table.product", "table.project", "tan", "to_int", "to_real", "tuple", "tuple.project",
  "ubv_to_int", "wand", "xor"
]

/-- The name that the solver knows the name `s` by, in both front ends
(`Reqs/Cli#solver-queries`): `s`, or with a `#` after it if it is a
theory's symbol (`theorySymbols`), since no Fren name contains `#`. -/
def smtName (s : String) : String := if theorySymbols.contains s then s!"{s}#" else s

/-- The cvc5 options for a spec that uses strings and sets (`cli::logic`):
`strings-exp` for the extended string functions, `re-inter-mode` to
decide intersections of patterns, `re-elim` to rewrite a match that needs
no automaton, such as `x[0-9]{2}.*`, as string functions, and `sets-exp`
to count the members of a set of a finite type. -/
def solverOptions (strings sets : Bool) : List (String × String) :=
  (if strings then [("strings-exp", "true"), ("re-inter-mode", "all"), ("re-elim", "on")] else [])
    ++ (if sets then [("sets-exp", "true")] else [])

/-- The cvc5 option for a query in a logic with quantifiers, every logic
of `logic` but `QF_UFDTLIA` (`cli::logic`): `inst-when` `last-call`, so
that cvc5 instantiates quantifiers only once the rest of the query is
satisfied, not also while it searches it. Its default instantiates, by
E-matching, at each step of that search too, and can go on making
instances that each bring new terms to match: a query that assumes the
contract of `lang::resolve` for two scopes of one name took 1.4 to 2 s
to find a model so, and 0.1 to 0.2 s with the option (#520). -/
def quantifierOptions (logic : String) : List (String × String) :=
  if logic == "QF_UFDTLIA" then [] else [("inst-when", "last-call")]

/-- The cvc5 option for a query with a quantifier over a collection's
elements, which a subset type within an element type brings
(`Reqs/Cli#solver-queries`): `fmf-bound`, with which cvc5 finds models of
quantifiers that membership bounds.

A procedure, global expectation or refinement whose queries have an
unbounded quantifier with a bound name that has a domain sets it too
(`Reqs/Lang/Quantifiers#guards`): cvc5 then finds models of quantifiers
bounded by membership and by integer ranges. For it, the domain is that of
the guard's shape alone (`lang::guard_domain`), whatever the bound name's
type: no field read from a bound name is the name, and only a name declared
`Nat` has naturals for values. `lang::range_domain` says only which ranges
the evaluators enumerate. -/
def boundedOptions : List (String × String) := [("fmf-bound", "true")]


/-- The cvc5 option for the contract of a generic function without a body,
checked once at its type parameters' sorts
(`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`):
`finite-model-find`, with which cvc5 finds the small domains, such as one
of a single value, on which the contract may fail, rather than giving up. -/
def finiteModelOptions : List (String × String) := [("finite-model-find", "true")]

end Fren.Core
