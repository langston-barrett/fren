# Structural recursion

A first-order [defined function](Items.md#defined-functions) that is not
[generic](GenericFunctions.md) may apply itself in its own body, as a
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
expression. A generic or higher-order function is never recursive
(`F0331`), and mutual recursion cannot be written, since a function is not
in scope in the bodies of the functions declared before it. A structural
recursion is accepted, with the meaning, encodings and decidability below
([Meaning](#meaning), [Solver encoding](#solver-encoding)); `F0448`, which
reported it as not yet supported, is retired.

`lang::structural_recursion` states this, over the function's uses of
itself in its body, in the order they are read (below), each with where its
arguments come from:

```fren
pub mod lang

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
facts, under the application's guards and preconditions. No recursive
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
also on its preconditions.

```fren
pub enum RecApplication { Written, Reflected }
pub struct RecFacts { posts?, equation? }
pub proc recursive_facts(origin: RecApplication, bound?): (det facts: RecFacts) {
    ensure posts: facts.posts? iff not bound?
    ensure equation: facts.equation? iff not bound? and origin = RecApplication::Written
}
```

An application is ground when its arguments mention no variable bound by
an enclosing quantifier. Both front ends collect its one-step equations
and postconditions as top-level facts wherever it appears, including beneath
quantifiers. An application mentioning a quantifier-bound variable brings
no top-level facts. Guards mentioning such variables are not exported either;
ground facts retain only guards independent of those variables. No fact may
refer to a variable outside its binder. If the remaining facts cannot prove
a check and evaluation refutes its model, both front ends report Inconclusive
with the same `F0450` diagnostic.

## Contracts

A recursive function's contract is checked once against its body by
Hoare's rule. At actual recursive applications in that body all of the
function's postconditions may be assumed simultaneously, guarded by the
application's conditions. No hypotheses are added at arbitrary payloads:
only the applications actually made bring facts. Structural recursion
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

```fren
pub proc recursive_counterexample(applies_recursive?, evaluation_confirms?):
    (det report_counterexample?) {
        ensure rule: report_counterexample? iff (not applies_recursive? or evaluation_confirms?)
    }
```

Checks are complete modulo recursive functions being opaque. A fact that
follows from the body beyond one step, but not from the contract, need not
be provable. Strengthen the function's contract to make such a fact
available. Recursion itself never raises `undecidable`: its applications,
ground facts and finite one-step equations add only uninterpreted
functions to quantifier-free queries.

```fren
#fren_check structural_recursion
#fren_check recursive_match
#fren_check recursive_facts
#fren_check recursive_post_result
#fren_check recursive_counterexample
```
