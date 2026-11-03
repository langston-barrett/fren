# Structural recursion

A first-order [defined function](Items.md#defined-functions), [generic](GenericFunctions.md)
or not, may apply itself in its own body, as a
*structural recursion* over a recursive enumeration: one of its
parameters, the *decreasing* one, is the same in every application, and
there each argument is a binder that a [`match`](Expressions.md#matches)
arm bound from a payload of that parameter, directly or nested. Each
application is then to a value smaller than the parameter's, so every
application has a value:

```text
pub enum Tree { Leaf(Int), Node(Tree, Tree) }

pub fn leaves(t: Tree): Int := match t {
    Tree::Leaf(_) => 1,
    Tree::Node(l, r) => leaves(l) + leaves(r),
}
```

A binder is bound from a payload of a parameter `p` when it is a binder of
a `match` arm's pattern on `p`, within a variant's payload, as `l` and `r`
are above, however deeply the pattern nests; when it is such a binder of a
`match` on a binder already bound from a payload of `p`; or when it is a
binder of the whole of such a binder, as `m` in `match l { m => ... }`. A
binder of a pattern test (`is`), a `let`'s or a `where`'s name is not,
whatever its value. The other arguments of an application are any
expressions.

The decreasing parameter is the first, in order, at which every
application's argument is bound from a payload of that parameter, so a
function with several parameters of the recursive enumeration recurses on
the first that works for all of its applications. There is no other
recursion: an application whose arguments decrease at no parameter that
all the others decrease at, an application within a
[closure](HigherOrder.md#closures), or the function's name given for a
function parameter, is an error (`F0447`), at the first application by
which every parameter has failed, saying why its argument is not a payload
of the parameter there: the parameter itself, another name, or another
expression. A higher-order function is never recursive (`F0331`), and
mutual recursion cannot be written, since a function is not in scope in the
bodies of the functions declared before it. `lang::self_application` states
which functions may apply themselves: whether a function is generic does
not matter, since the structural rule does not look at the types of the
payloads that the recursion decreases on (see [Generic
recursion](#generic-recursion)). Both front ends call
`Core.selfApplicable`, which is bound to it with an `impl`. A structural
recursion is accepted, with the meaning, encodings and decidability below
([Meaning](#meaning), [Solver encoding](#solver-encoding)); `F0448`, which
reported it as not yet supported, is retired.

```fren
pub mod lang

pub proc self_application(
    generic?,          -- the function has type parameters
    higher_order?,     -- the function has a function parameter
): (det may_recurse?) {
    ensure rule: may_recurse? iff not higher_order?

    expect generic: when generic? and not higher_order?, may_recurse?
}
```

`lang::structural_recursion` states this, over the function's uses of
itself in its body, in the order they are read (below), each with where its
arguments come from:

```fren
-- Where a recursive application's argument at one position comes from,
-- relative to the function's parameter at that position: a binder bound
-- from a payload of it, the parameter itself, another name, or another
-- expression.
pub enum RecArg { Payload, Itself, Name, Expr }

-- How the function is used in its own body: applied, applied within a
-- closure, or given for a function parameter without being applied.
pub enum RecForm { Applied, InClosure, Passed }

-- A use of the function: its form, and an application's arguments, in order.
pub struct RecUse { form: RecForm, args: Seq<RecArg> }

-- Not recursive; a structural recursion, decreasing at the parameter at a
-- position; or not one, at a use, reporting the argument at a position.
pub enum Recursion { NotRecursive, Structural(Int), NotStructural(Int, Int) }

-- Whether the use `u` is an application whose argument at position `i` is
-- bound from a payload of the parameter there.
pub fn decreases_at?(u: RecUse, i: Int) :=
    u.form = RecForm::Applied and 0 <= i < u.args.len and u.args[i] = RecArg::Payload

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc structural_recursion(
    n_params: Int,         -- the function's number of parameters
    uses: Seq<RecUse>,     -- its uses of itself in its body, in order
): (det verdict: Recursion) {
    use self::Recursion::{NotRecursive, NotStructural, Structural}
    assume params: n_params >= 1

    ensure none: when uses = [], verdict = NotRecursive
    -- The first position at which every use decreases.
    ensure structural: forall (i: Int), when 0 <= i < n_params and uses != []
        and (forall (k: Int), when 0 <= k < uses.len, decreases_at?(uses[k], i))
        and (forall (h: Int), when 0 <= h < i, exists (k: Int), 0 <= k < uses.len and not decreases_at?(uses[k], h)),
        verdict = Structural(i)
    -- Otherwise the first use by which every position has failed, and the
    -- first position that fails first there.
    ensure not_structural: forall (k: Int) (i: Int), when 0 <= k < uses.len and 0 <= i < n_params
        and not decreases_at?(uses[k], i)
        and (forall (j: Int), when 0 <= j < k, decreases_at?(uses[j], i))
        and (forall (h: Int), when 0 <= h < n_params, exists (j: Int), 0 <= j <= k and not decreases_at?(uses[j], h))
        and (forall (h: Int), when 0 <= h < i, exists (j: Int), 0 <= j < k and not decreases_at?(uses[j], h)),
        verdict = NotStructural(k, i)
}
```

Both front ends read the body into these uses as they elaborate it: a use
when they reach the function's name, before its arguments, so an
application within another's arguments comes after it. That is the order
they are written but where an operand does not synthesize its type, and
the other operand is elaborated first, as in `[match f(l) { _ => [] },
[f(l)]].len`, where the second `f(l)` is read first; both front ends read
in the same order. Each use is read once, at its place: an expression that
is elaborated again, such as a `match`'s scrutinee where a closure refers
to an arm's binder, is not another use.

## Meaning

A structural recursion denotes the least fixed point of its equations,
which the structural rule makes total: each application is to a value
smaller than the parameter's, so there is exactly one function that meets
them (the recursive enumeration is the initial algebra of its base
functor). Evaluation and generated Lean definitions use these equations; checks
use the finite Hoare abstraction described below:

- **Evaluation** (testing, quickcheck, and confirming a model) applies
  the definition, which terminates.
- **Lean** gets a genuine structural recursion (`def` with a Lean `match`
  on the decreasing parameter), which Lean accepts as it is, with its
  equation lemmas and functional induction ([Generated](Generated.md)).
  A `match` that a recursive application is under must therefore be one
  that the generator makes a Lean `match` of (`Reqs/Generated#matches`).

`lang::recursive_match` states which `match`es are an error (`F0449`): one
on a parameter, or on a binder bound from a payload of one, of an
enumeration, with a recursive application under its arms (in a guard or a
body), where some arm has a guard, or its pattern has a literal, a range, or an or-pattern
other than at its top, which would make it a chain of `if`s. Both front
ends report it, for a structural recursion, at the first such arm of the
first such `match`, before any other report of the recursion. A
`match` on another value, such as an `Int` payload, is unrestricted, as
its arms bind nothing that the recursion decreases on.

```fren
-- What a `match`'s scrutinee is, relative to the function's parameters.
pub enum MatchedOn { Parameter, Payload, Other }

-- What a pattern has within it, as Lean's `match` sees it
-- (`generated::Head`), with an or-pattern at its top its alternatives.
pub enum PatPart { Wildcard, Binder, Variant, Literal, OrPattern }

-- A `match` in a defined function's body.
pub struct RecMatch {
    on: MatchedOn,
    enumeration?,              -- whether its scrutinee is an enumeration
    arms: Seq<Set<PatPart>>,   -- each arm's pattern's parts
    guarded?,                 -- some arm has a guard
    recursion_under?,          -- whether a recursive application is in an arm
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc recursive_match(m: RecMatch): (det rejected?) {
    ensure rule: rejected? = (m.on != MatchedOn::Other and m.enumeration? and m.recursion_under?
        and (m.guarded? or (exists (k: Int), 0 <= k < m.arms.len
        and (PatPart::Literal in m.arms[k] or PatPart::OrPattern in m.arms[k]))))
}
```

## Solver encoding

Hoare induction is the only interpretation of recursion in checks. Every
application of a structural recursion is opaque: an uninterpreted function
application, including applications on constant arguments. The
invariants of its parameters' subset types and its preconditions are
obligations, just as for an
uninterpreted function with a contract. Its postconditions are ground
facts, under the application's guards and preconditions, and so is its
result type's constraint, as for an uninterpreted function: that a `Nat`
is at least 0, and the invariants of a subset type, or of the subset type
that an alias names. No recursive
SMT definition, quantified recursion axiom, or evaluation on constant
arguments is used.

Each application also brings one step of its defining equations. For an
arm `C(xs) => body`, the equation is `t is C(xs) => f(t) = body`, with
selectors substituted for `xs`. Arm guards are extra conditions and earlier
arms take precedence, exactly as in `match`. Applications introduced by
this unfolding bring postconditions only, never another unfolding. Thus a
query has finitely many ground equations. This holds in every context,
including a function's own contract check.

The following structured policy is shared by both front ends. `Written`
means an application in the query; `Reflected` means one
introduced by the one-step defining equation. Applications found while
expanding a contract inherit the originating application’s origin, including
through further contracts. A work queue visits each application, guards and
origin once; a contract expansion also stops when it revisits an application
on its ancestry path. Before scanning, the CLI expands the nonrecursive
definitions and contract clauses that apply, directly or through others, a
recursive or uninterpreted function, or a selector whose payload brings a
fact, and leaves the rest to the solver as definitions: they hold no
application to find, and expanding each where it is applied can make a
query hundreds of times larger. Either way, a definition's [quantifiers
over elements](ElementQuantifiers.md#expansion) are expanded where it is
applied, as in a spec without recursion. This is the CLI’s finite
collection policy, shared by hosted checks and recursive contract proofs.
Facts are conditional on the application's own guards, and postconditions
also on its preconditions. The result type's constraint, where the
function's declared result type has one, comes with the postconditions,
wherever they do: so in the function's own body too, where it is an
induction hypothesis at each recursive application, beside the
postconditions ([Contracts](#contracts)). For example, of `keep` below,
the obligation that the body is a `Pos` follows, at `keep(p, rest)`, from
that application's being one:

```text
pub type Pos = n: Int where positive: n >= 1

pub fn keep(p: Pos, l: L): Pos := match l {
    L::Nil => p,
    L::Cons(_, rest) => keep(p, rest),
}
```

An application's `bound?` is decided with its postconditions, where the
work queue finds it: both front ends decide the result type's fact from
`constrained_result?` alone, for the applications that bring
postconditions.

```fren
pub enum RecApplication { Written, Reflected }
pub struct RecFacts { result_type?, posts?, equation? }

pub proc recursive_facts(
    origin: RecApplication,
    bound?,                  -- the application mentions a quantifier-bound variable
    constrained_result?,     -- the function's declared result type has a constraint
): (det facts: RecFacts) {
    ensure result_type: facts.result_type? iff constrained_result? and not bound?
    ensure posts: facts.posts? iff not bound?
    ensure equation: facts.equation? iff not bound? and origin = RecApplication::Written

    -- The result type is a hypothesis wherever the postconditions are.
    expect with_posts: when constrained_result?, facts.result_type? = facts.posts?
}
```

Both front ends decide the result type's fact with
`Fren.Core.recursiveResultFact`, and the others with
`Fren.Core.recursiveFacts`.

The work queue finds an application once on each path to it: within the
formulas of the query, and through the facts and equations that bring it.
Each path has its own guards, and a fact of the application holds where
they do. A query asserts each fact once, where it is first found, under the
disjunction of the guards of its weakest paths, and with no guard where one
of them has none. A path is weaker than another when its guards are among
the other's, as they are of a path through the facts of an application that
another fact mentions too, which only adds guards to the first: then the
fact under the other's guards follows from it under its own. So the query
is equivalent to one with the fact under every path's guards.
`lang::merged_facts` states which paths each fact is asserted under, over
the paths on which the queue finds it, by position. Its first two conjuncts
make the query equivalent: where some guards hold, the query asserts each
fact found on a path whose guards hold, by the second, and no other, by the
first. Images over `Int` are outside the [decidable core](Decidability.md),
so the procedure opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub proc merged_facts(
    found: Rel<Int, Int>,        -- each fact that the queue finds, with each path on which it finds it
    guards: Rel<Int, Int>,       -- each path, with its guards
    asserted: Rel<Int, Int>,     -- each fact that the query asserts, with each path under whose guards it does
    assertions: Rel<Int, Int>,   -- each of the query's assertions of these facts, by position, with its fact
): (det merged?) {
    ensure rule: merged? iff (asserted subset found
        and (forall (f: Int) (p: Int), when (f, p) in found,
        exists (q: Int), (f, q) in asserted and guards.image({q}) subset guards.image({p}))
        and (forall (f: Int) (p: Int) (q: Int), when (f, p) in asserted and (f, q) in asserted and p != q,
        not guards.image({q}) subset guards.image({p}))
        -- Each fact once.
        and (forall (a: Int) (b: Int) (f: Int), when (a, f) in assertions and (b, f) in assertions, a = b)
        and assertions.range = found.domain)
}
```

An application is ground when its arguments mention no variable bound by
an enclosing quantifier. Both front ends collect its one-step equations
and postconditions as top-level facts wherever it appears, including beneath
quantifiers. An application mentioning a quantifier-bound variable brings
no top-level facts. Guards mentioning such variables are not exported either;
ground facts retain only guards independent of those variables. No fact may
refer to a variable outside its binder. If the remaining facts cannot prove
a check and evaluation does not confirm its model, both front ends report
Inconclusive with the same `F0450` diagnostic.

## Contracts

A recursive function's contract is checked once against its body by
Hoare's rule. At actual recursive applications in that body all of the
function's postconditions, and its result type's constraint, may be
assumed simultaneously, guarded by the application's conditions. No
hypotheses are added at arbitrary payloads: only the applications
actually made bring facts. Structural recursion
makes the induction sound, because each such application decreases.
The other arguments are those at the application, not necessarily the
original parameters. The invariants of the parameters' subset types and
the preconditions remain obligations there, including constrained input domains.

If any postcondition fails, each other postcondition that passed is
Inconclusive: its induction may depend on the failing postcondition. The
same dependency rule applies when another postcondition is Inconclusive: its
hypotheses have not been established, so a dependent success is not a proof.

```fren
pub enum RecPost { Passed, Failed, Inconclusive }

pub proc recursive_post_result(result: RecPost, another_unproved?): (det reported: RecPost) {
    ensure rule: reported = (if result = RecPost::Passed and another_unproved?
        then RecPost::Inconclusive else result)
}
```

Lean still receives a real structural recursive definition. Each
postcondition receives a theorem proved by induction on the decreasing
parameter. For nested payload calls the definition's generated structural
induction principle supplies hypotheses at those calls as well. The equations for one
step and each case's facts are given to the solver as guarded formulas,
without splitting independent applications into constructor combinations. This includes equations at
self-applications. After adding those equations, applications in their bodies
receive contracts only. Self-applications introduced there use induction
hypotheses at smaller descendants, including descendants deeper than the
immediate children. A caller assumes another function's contract whether or
not that contract was proved; an unproved contract is reported at its declaration,
as for uninterpreted functions. Hosted theorems use established unconditional
contract theorems where available and otherwise take the dependency's contract
as an explicit hypothesis. This includes dependencies with conditional theorems;
no axiom is introduced. An internal proof-generation failure cannot suppress
or alter the checker’s verdicts and diagnostics.
No equation is added for an application merely because reflection introduced it.
Recursive applications use the induction hypotheses. As for
other hosted checks, solver steps use `trust := true`; no goal may be
left unproved. Constructor matches with guards must preserve structural
recursion, or be rejected by both front ends with `F0449`.

## Generic recursion

A generic function that is a structural recursion, as

```text
pub enum List<T> { Nil, Cons(T, List<T>) }

pub fn len<T>(l: List<T>): Int := match l {
    List::Nil => 0,
    List::Cons(_, r) => 1 + len(r),
}
```

is one at every instance. An application at an instance applies the
instance (`lang::applied_instance`): the generic definition with each type
parameter replaced by its type argument, every part of it at once, as for
any [generic function](GenericFunctions.md#meaning), and its applications
of itself, which are at its own type parameters, recurse at that same
instance, since instantiating its own type parameters gives the instance's
type arguments. So `len<Int>` is the structural recursion whose body is
`len`'s with `Int` for `T`, which applies `len<Int>`; and a recursion that
applies another generic recursion at its own type parameter, as `total<T>`
applies `len<T>`, applies `len<Int>` at `total<Int>`. A self-application
is at the function's own type parameters: within its body the function has
its declared type, with its type parameters as the abstract types that they
are there, so each argument is checked against its parameter's declared
type, and one of another instance's type is a type mismatch (`F0304`), as
`f(m, Option::Some(x))` in `fn f<T>(n: N, x: T): Int` is. So there is no
polymorphic recursion, and an instance's body applies only itself and
instances of the functions declared before it.

Its checks are as for any structural recursion, at its type parameters'
sorts and at each instance:

- Its contract is checked once, at the sorts, by Hoare's rule
  ([Contracts](#contracts)), so it holds at every instance, as a generic
  function's contract does (see [Generic
  functions](GenericFunctions.md#meaning)).
- Each instance that a query applies is an opaque function of its own: the
  `fren` command declares one `declare-fun` for each, named as an instance
  of a defined generic function is, as `|::len<Int>|`, and the Lean-hosted
  front end gives each its own local, from the solver form, which takes the
  type arguments and their `Inhabited` instances first. Each of its
  applications brings its postconditions and its declared result type's
  constraint, at the instance, and, if written, one step of the instance's
  body, as above ([Solver encoding](#solver-encoding)).
- Evaluation, testing and enumeration apply the instance's definition.
- A counterexample of the check at the sorts is confirmed by evaluation as
  any other is ([Counterexamples and completeness](#counterexamples-and-completeness)),
  at the model's values of each type parameter's sort: the `fren` command
  evaluates with them as abstract values, as `T#0`, and the Lean-hosted
  front end puts each sort at the type that lean-smt reads it as, a `Fin
  n`, or `Nat` where the model gives no value of it. A model may give
  values of a type parameter's sort, as `t = Term::Var(V#0)`: both front
  ends read them, and once evaluation confirms the counterexample the check
  fails, with that counterexample.
- Where the declared result type is a type parameter, an instance's result
  brings no fact of its type argument's, not even a data type's whose
  payload has a subset type: the type parameter has none, so a subset
  type's invariant reaches such an instance's result only through its
  postconditions. Both front ends decide from the declared result type. A
  declared result type that is not a type parameter brings its constraint
  as for any recursion, as `keep_generic<T>(p: Pos, x: T, l: L): Pos` does
  in `test/ui/checks/recursion_subset_result.fren`, beside `rep<T>(x: T, l:
  L): T` at an enumeration with a `Pos` payload, which brings none.
  With `fn rep<T>(n: N, x: T): T` and `d: Pos`, `rep(n, d) >= 1` holds but is
  Inconclusive (`F0450`). That is sound but incomplete, and particular to a
  recursion: a generic function that is not recursive is unfolded, so its
  result's invariant follows from its body.

Termination of what the checks collect does not change: an instance's facts
apply only itself and the instances of earlier functions, so each round of
`check::fact_applications` and each work queue of the one-step equations
ends as without generics. The hosted front end does not yet generate a
Lean theorem for a generic recursion's contract, as it does for other
recursions ([Contracts](#contracts)): the theorem would be at the type
parameters' placeholders, not at every type.

## Counterexamples and completeness

An opaque function may take any value its contract permits. Before a
check applying a recursive function reports a counterexample, evaluation
of the real recursive definitions on the model's inputs must confirm the
failure. A failure confirmed by evaluation is reported normally. A model
that evaluation does not confirm, because it refutes it or cannot evaluate
it, makes the check Inconclusive (`F0450`): it fails under the contracts
of the named recursive functions, which may be too weak, and the message
says only that evaluation did not confirm it, not which. Both front ends
use this rule and diagnostic.

The formulas whose recursive applications a query reflects, with their
one-step equations, are its own, the facts that its variables' types
bring, and the facts of the applications that it has, transitively
(`check::fact_applications`): of `fn one(l: L): (r: Int) { ensure e: r =
total(L::Cons(1, l)) }`, a query that mentions `one(l)` has the one-step
equation of `total(L::Cons(1, l))` too, so that `one(l) >= 1` follows where
`total`'s body adds the absolute values of the list's elements; and of
`type Big = l: L where invariant: total(l) >= 5`, a query over `x: Big`
has the one-step equations of `total(x)`, so that `x is L::Nil` cannot
hold.

A model is confirmed against the query's own hypotheses and goal: where
they apply a recursive function, evaluation of the real definitions on the
model must confirm it. Where a fact of the applications that the query has
applies a recursive function, a model is never confirmed, and the check is
Inconclusive (`F0450`), as it is where evaluation refutes the model. That
is a conservative choice: the model gives the values of those facts'
applications too, at which evaluation of the real definitions could
confirm it, but none does yet. So of `fn first(l: L): (r: Int) { ensure e:
r = total(L::Cons(1, L::Cons(2, L::Cons(3, l)))) }`, `cover low: first(l)
< 6` is not met by a model that only the opaque `total` allows; but `cover
big: one(l) > 100`, which `l = [200]` meets, is Inconclusive too. Both
front ends take the formulas they reflect from
`Fren.Core.recursionFormulas`, from the same three kinds, and decide with
`Fren.Core.recursiveCounterexample`, where `applies_recursive?` is whether
the query's own hypotheses or goal apply a recursive function, as the
solver has them, and `facts_recursive?` whether a formula of
`facts.image(brought)` does.

A model is not yet confirmed against the facts of the query's variables'
types, though they are reflected. That is a known gap, not the rule meant:
a check can rest on a model that only an opaque recursive function allows,
as the assumptions `x = 0` of `x: BigI`, where `type BigI = n: Int where
invariant: total(L::Cons(n, L::Nil)) >= 5 or n = 5`, which no `BigI`
meets, pass as consistent, and `cover small: x = L::Cons(1, L::Cons(1,
L::Cons(1, L::Nil)))` of `x: Big` is met. Confirming against those facts
needs a model that evaluation does not refute wherever a real one exists,
or the verdict would depend on which model each front end's solver gives:
the values of the recursive applications that a refuted model leaves open,
as `total(L::Nil)` above, added as facts, and the query asked again (#634).
The binary already confirms a model against the type of a call's output,
which is part of the call's hypothesis there, and the Lean front end does
not: there, too, the front ends agree only where the solver's model is a
real one (#634).

`lang::counterexample_confirmed` states the same over the query's own
formulas, each as the solver has it: whether it applies a recursive
function, once the definitions it applies are unfolded, and what
evaluation of the real definitions gives it at the model. A formula
applies a recursive function where the solver's formula does, whether or
not evaluation can read it: the goal of a subset type's obligation, which
evaluation has no formula of, applies one where the value checked against
the subset type does, as `keep(p, rest)` above. So a model that evaluation
refutes, or cannot evaluate, is never a failure where a formula applies a
recursive function; `counterexample_confirmed_refines` confirms that this
refines `recursive_counterexample`. Both front ends decide with
`Fren.Core.counterexampleReported`.

```fren
set_option fren.lint.undecidable "allow" in
pub proc recursion_formulas(
    variables: Set<Int>,         -- the facts that the query's variables' types bring, by position
    written: Set<Int>,           -- the query's own hypotheses, by position
    facts: Rel<Int, Int>,        -- each application, with the formulas of its facts
    brought: Set<Int>,           -- the applications whose facts the query has (`check::fact_applications`)
): (det reflected: Set<Int>) {
    out reflected := variables union facts.image(brought) union written
}

pub proc recursive_counterexample(applies_recursive?, evaluation_confirms?, facts_recursive?):
    (det report_counterexample?) {
        ensure rule: report_counterexample? iff (not facts_recursive? and (not applies_recursive? or evaluation_confirms?))
    }

-- What evaluation of the real definitions gives a formula at the solver's
-- model: true, false, or nothing, where it cannot evaluate it.
pub enum Evaluated { Holds, Fails, Unevaluated }

-- A formula of a query, as the solver has it: whether it applies a
-- recursive function, and what evaluation gives it at the model.
pub struct ModelFormula { recursive?, value: Evaluated }

-- Whether a formula of `hyps`, or `goal`, applies a recursive function.
set_option fren.lint.undecidable "allow" in
pub fn applies_recursive?(hyps: Seq<ModelFormula>, goal: ModelFormula) :=
    goal.recursive? or (exists (k: Int), 0 <= k < hyps.len and hyps[k].recursive?)

-- Whether evaluation confirms the model: every hypothesis holds and the
-- goal fails.
set_option fren.lint.undecidable "allow" in
pub fn evaluation_confirms?(hyps: Seq<ModelFormula>, goal: ModelFormula) :=
    goal.value = Evaluated::Fails and (forall (k: Int), when 0 <= k < hyps.len, hyps[k].value = Evaluated::Holds)

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc counterexample_confirmed(
    hyps: Seq<ModelFormula>,     -- the query's own hypotheses
    goal: ModelFormula,          -- its goal, which a counterexample makes false
    facts_recursive?,            -- a fact of the applications that the query has applies a recursive function
): (det report_counterexample?) {
    use self::Evaluated::{Fails, Holds, Unevaluated}
    ensure rule: report_counterexample? iff (not facts_recursive?
        and (not applies_recursive?(hyps, goal) or evaluation_confirms?(hyps, goal)))

    -- A model that evaluation refutes is never a failure.
    expect refuted: when applies_recursive?(hyps, goal)
        and (goal.value = Holds or (exists (k: Int), 0 <= k < hyps.len and hyps[k].value = Fails)),
        not report_counterexample?
    -- Nor one that it cannot evaluate.
    expect unevaluated: when goal.recursive? and goal.value = Unevaluated, not report_counterexample?
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect counterexample_confirmed_refines(
    hyps: Seq<lang::ModelFormula>,
    goal: lang::ModelFormula,
    facts_recursive?,
) {
    use lang
    call concrete := counterexample_confirmed(hyps, goal, facts_recursive?)
    refines concrete recursive_counterexample(
        lang::applies_recursive?(hyps, goal),
        lang::evaluation_confirms?(hyps, goal),
        facts_recursive?,
    )
}
```

Checks are complete modulo recursive functions being opaque. A fact that
follows from the body beyond one step, but not from the contract, need not
be provable. Strengthen the function's contract to make such a fact
available. Recursion itself never raises `undecidable`: its applications,
ground facts and finite one-step equations add only uninterpreted
functions to quantifier-free queries.

```fren
#fren_check self_application
#fren_check structural_recursion
#fren_check recursive_match
#fren_check recursive_facts
#fren_check merged_facts
#fren_check recursive_post_result
#fren_check recursion_formulas
#fren_check recursive_counterexample
#fren_check counterexample_confirmed
#fren_check counterexample_confirmed_refines
```
