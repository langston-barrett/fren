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
itself in its body, in the order they are written, each with where its
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
set_option fren.evidence "tested" in
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
application within another's arguments comes after it.

## Meaning

A structural recursion denotes the least fixed point of its equations,
which the structural rule makes total: each application is to a value
smaller than the parameter's, so there is exactly one function that meets
them (the recursive enumeration is the initial algebra of its base
functor). There is no other meaning for the solver, the evaluator and
Lean to agree on:

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
body), where some arm's pattern has a literal, a range, or an or-pattern
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
    recursion_under?,          -- whether a recursive application is in an arm
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc recursive_match(m: RecMatch): (det rejected?) {
    ensure rule: rejected? = (m.on != MatchedOn::Other and m.enumeration? and m.recursion_under?
        and (exists (k: Int), 0 <= k < m.arms.len
        and (PatPart::Literal in m.arms[k] or PatPart::OrPattern in m.arms[k])))
}
```

## Kinds

A *recursive payload* is a binder bound from a payload of the decreasing
parameter, as above. Each of its occurrences in the body is either the
decreasing argument of a recursive application, or any other occurrence:
matched on, compared, given to another function, or returned. A
structural recursion is a *catamorphism* when every occurrence of every
recursive payload is the decreasing argument of a recursive application:
its arms use the recursive results, never the subterms themselves, as
`leaves` above does. Any other structural recursion is a *paramorphism*:

```text
-- A paramorphism: the arm tests the subterm `l` itself.
pub fn left_leaves(t: Tree): Int := match t {
    Tree::Leaf(_) => 0,
    Tree::Node(l, r) => (if l is Tree::Leaf(_) then 1 else 0) + left_leaves(l) + left_leaves(r),
}
```

The kind is decided syntactically, by both front ends, while they read
the body into its uses (`lang::structural_recursion`): each occurrence of
a recursive payload is recorded with whether it is a recursive
application's decreasing argument.

## Solver encoding

What a query knows of a defined function depends on its kind:

| Kind | Encoding | On symbolic arguments |
|---|---|---|
| Not recursive | its body, unfolded at each application, as today | exact |
| Catamorphism | an SMT-LIB `define-fun-rec` of its body | exact; decided when sufficiently surjective |
| Paramorphism | uninterpreted, with one-step unfolding where the constructor is known | opaque |

- **Catamorphism: `define-fun-rec`.** Both front ends give the solver the
  function's body as a recursive definition, with each recursive
  application an application of the defined symbol, and do not unfold it
  themselves. The structural rule makes the definition admissible, so the
  axiom is consistent (Reynolds et al., IJCAR 2016). A query that applies
  one sets cvc5's `fmf-fun`, without which cvc5 answers `unknown` where it
  has a model. For a sufficiently surjective catamorphism into the
  decidable core, such as a size into `Nat`, or the elements as a set or a
  multiset, the fragment is decidable (Suter, Dotta and Kuncak, POPL
  2010), by unfolding (Suter, Köksal and Kuncak, SAS 2011).
- **Paramorphism: uninterpreted, plus one-step unfolding.** The function
  is an uninterpreted function. Wherever the query applies it to an
  argument whose constructor is known, its one-layer equation is added,
  with the recursive applications left as applications: from a `match`
  arm's `t = Tree::Node(l, r)`, `left_leaves(t) = (if l is Tree::Leaf(_)
  then 1 else 0) + left_leaves(l) + left_leaves(r)`. The constructor is
  known at a ground value, where the equations are added down to the
  leaves, and at a `match` arm on the argument, where they are added once.
  The equations are ground and quantifier-free, so the query stays
  decidable; it is sound and incomplete on symbolic arguments.

A model is a counterexample only if it is genuine (`Reqs/Check`). Under
`define-fun-rec`, every model gives a catamorphism its real value. Under
one-step unfolding, a model may give a paramorphism a value at a symbolic
argument that it never takes; so a `sat` answer to a query that applies a
paramorphism to an argument whose constructor is not known is confirmed by
evaluating the formula at the model's values, with the real definitions:
false there, the counterexample is genuine; true there, or not
evaluable (an abstract type, an uninterpreted function), the result is
`Inconclusive`, and the message says that the paramorphism's value was
not pinned down.

`lang::recursive_encoding` states this, over the function's occurrences
of its parameters and of the binders bound from their payloads, which both
front ends record as they read the body, each once, by where it is
written: a recursive payload as a recursive application's argument at its
own position; a parameter as a `match`'s scrutinee; and any other, which
is a recursive payload of the parameter's type otherwise used, a parameter
otherwise used, or a `match` on a parameter or a recursive payload whose
pattern has a variant's pattern within a payload. That last is
conservative: a pattern within a payload of another enumeration, such as
`Option`, makes a paramorphism too, which is encoded soundly, only not
decided on symbolic arguments.

```fren
-- An occurrence of a parameter, or of a binder bound from a payload of one:
-- as a recursive application's argument, as a `match`'s scrutinee, or any
-- other.
pub enum Occurrence { Recursed, Matched, Other }

-- An occurrence, of the parameter at `pos` or of a payload of it.
pub struct PayloadOcc { pos: Int, occ: Occurrence }

-- How the solver knows a defined function.
pub enum Encoding { Unfolded, DefineFunRec, Opaque }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc recursive_encoding(
    recursion: Recursion,          -- `lang::structural_recursion`'s verdict
    occurrences: Seq<PayloadOcc>,  -- in the order they are written
): (det encoding: Encoding) {
    ensure unfolded: when not (recursion is Recursion::Structural(_)), encoding = Encoding::Unfolded
    -- A catamorphism: nothing at the decreasing parameter is other.
    ensure catamorphism: when recursion is Recursion::Structural(i)
        and (forall (k: Int), when 0 <= k < occurrences.len and occurrences[k].pos = i,
        occurrences[k].occ != Occurrence::Other),
        encoding = Encoding::DefineFunRec
    ensure paramorphism: when recursion is Recursion::Structural(i)
        and (exists (k: Int), 0 <= k < occurrences.len and occurrences[k].pos = i
        and occurrences[k].occ = Occurrence::Other),
        encoding = Encoding::Opaque
}
```

Until structural recursion is accepted, `F0448`'s message names the kind.

## Decidability

The decidable core ([Decidability](Decidability.md)) holds, of the defined
functions:

- non-recursive ones, which are unfolded;
- sufficiently surjective catamorphisms into the decidable core, through
  `define-fun-rec`;
- a paramorphism applied to a ground argument, which unfolds completely.

In each case every model gives the function its real value. The
`undecidable` lint reports every other application of a recursive
function: a paramorphism's on an argument that is not ground, and a
catamorphism's that is not sufficiently surjective or whose result is
outside the core, at the application. Allowing it keeps the checks sound:
a reported counterexample is still confirmed against the real definition,
or the result is `Inconclusive`.

A future version brings a paramorphism into the core through its
contract: when its contract is `det` (#366), checked by realizability, by
determinism, and against the body by Hoare's rule, with recursive
applications bringing the function's own postconditions as the induction
hypothesis, and in a fragment that cvc5 decides, the postconditions as
ground facts at each application pin down its value. Until then, the
`undecidable` lint reports it as above.

### Measured: cvc5 on `define-fun-rec`

cvc5 1.3.2 on small queries over `Tree { Leaf, Node(Tree, Int, Tree) }`,
each stopped at 30 seconds, with the options that Fren sets for sets
(`sets-exp`):

| Query | Without `fmf-fun` | With `fmf-fun` |
|---|---|---|
| `elems(t) = {}` and `t != Leaf` | unsat | unsat |
| `t = Node(u, 5, Leaf)` and `size(t) != 1 + size(u)` | unsat | unsat |
| `size(t) = 3`, `size(u) = 3`, `t != u` | unknown (right model) | sat, with a model |
| `elems(t) = {1, 2}` | unknown (right model) | sat, with a model |
| `size(t) = size(u) + 1` and `elems(t) = elems(u)` | unknown (right model) | sat, with a model |
| `size(t) = 0` and `t != Leaf`, `size` into `Int` | timeout | timeout |
| the same, with `forall x, size(x) >= 0` asserted | unsat | timeout |
| a paramorphism, at a ground tree | unsat | unsat |
| a paramorphism, `= 2` on a symbolic tree | unknown (right model) | sat, with a model |

So `fmf-fun` is needed for models, a count into `Int` is not sufficiently
surjective (its non-negativity needs induction), and the quantified fact
that would supply it is lost under `fmf-fun`. How a catamorphism into `Nat`
gets its non-negativity without losing `fmf-fun` is open; until then its
queries that need it are `Inconclusive`. Where cvc5 answers
`unknown` or runs out of time, the result is `Inconclusive`, never a wrong
answer.

The Lean-hosted front end checks this chapter's procedures by name, since
no `#fren_check` of its Lean file comes after it:

```fren
#fren_check structural_recursion
#fren_check recursive_encoding
#fren_check recursive_match
```
