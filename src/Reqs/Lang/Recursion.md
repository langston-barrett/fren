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
the body.

`lang::recursive_kind` states this, over the function's occurrences of
its parameters and of the binders bound from their payloads, which both
front ends record as they read the body, each once, by where it is
written: a recursive payload as a recursive application's argument at its
own position; a parameter as a `match`'s scrutinee; and any other, which
is a recursive payload of the parameter's type otherwise used, a parameter
otherwise used, or a `match` on a parameter or a recursive payload whose
pattern has a variant's pattern within a payload. That last is
conservative: a pattern within a payload of another enumeration, such as
`Option`, makes a paramorphism too, which is checked as soundly, only not
in the decidable core.

```fren
-- An occurrence of a parameter, or of a binder bound from a payload of one:
-- as a recursive application's argument, as a `match`'s scrutinee, or any
-- other.
pub enum Occurrence { Recursed, Matched, Other }

-- An occurrence, of the parameter at `pos` or of a payload of it.
pub struct PayloadOcc { pos: Int, occ: Occurrence }

-- What kind of recursion a defined function is.
pub enum RecKind { NotRecursive, Catamorphism, Paramorphism }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc recursive_kind(
    recursion: Recursion,          -- `lang::structural_recursion`'s verdict
    occurrences: Seq<PayloadOcc>,  -- in the order they are read
): (det rec_kind: RecKind) {
    ensure not_recursive: when not (recursion is Recursion::Structural(_)), rec_kind = RecKind::NotRecursive
    -- A catamorphism: nothing at the decreasing parameter is other.
    ensure catamorphism: when recursion is Recursion::Structural(i)
        and (forall (k: Int), when 0 <= k < occurrences.len and occurrences[k].pos = i,
        occurrences[k].occ != Occurrence::Other),
        rec_kind = RecKind::Catamorphism
    ensure paramorphism: when recursion is Recursion::Structural(i)
        and (exists (k: Int), 0 <= k < occurrences.len and occurrences[k].pos = i
        and occurrences[k].occ = Occurrence::Other),
        rec_kind = RecKind::Paramorphism
}
```

## Solver encoding

Every structural recursion, of either kind,
is given to the solver as an SMT-LIB recursive definition,
`define-fun-rec`, of its body, with each recursive application an
application of the defined symbol; neither front end unfolds it itself.
The structural rule makes the definition admissible, so the axiom is
consistent (Reynolds et al., IJCAR 2016), and every model gives the
function its real value at every argument: a counterexample is genuine.
A defined function that is not recursive is unfolded at each application,
as before, and so is each that a recursive definition's body applies.

- A query whose formulas apply a structural recursion, directly or through
  another's definition, sets cvc5's `fmf-fun`, without which cvc5 answers
  `unknown` where it has a model (see the measurements below). Both front
  ends set it right after `fmf-bound`.
- The binary writes the definition from its body as it writes a defined
  function's `define-fun`. The Lean-hosted front end gives lean-smt the
  solver's own copy of the definition (`DefinedInfo.recursive`), a Lean
  structural recursion over the placeholders themselves, as a `let` with
  an equational definition, from which lean-smt writes `define-fun-rec`;
  its Lean `match`es become the testers and selectors of the datatype, as
  the binary's do.

Where cvc5 answers `unknown` or runs out of time, which it may for a
recursion outside the core, the result is `Inconclusive`, never a wrong
answer.

The design on #279 encodes a paramorphism instead as an uninterpreted
function with its one-layer equation where its argument's constructor is
known, confirming each model against the real definition. That encoding
is not implemented: `define-fun-rec` is as sound, its models are genuine
without confirming them, and on the measured paramorphisms cvc5 behaves
as on the catamorphisms. Which applications are decided is the
`undecidable` lint's, below, not the encoding's.

## Decidability

The decidable core ([Decidability](Decidability.md#recursion)) holds, of
the defined functions:

- the non-recursive ones, which are unfolded;
- a catamorphism into `Bool` or a set, on any arguments: both are
  sufficiently surjective (Suter, Dotta and Kuncak, POPL 2010), decided
  by unfolding (Suter, Köksal and Kuncak, SAS 2011);
- a catamorphism *onto* its result type, on any arguments: one that an arm
  of a `match` on a parameter, without a guard, gives one of its pattern's
  payloads of the result's type, as `Expr::Val(n) => n` does. Every value
  of the type is then in its range, so no constraint on its range, such
  as a size's being at least 0, is left for the solver to derive by
  induction, which is what kept a size out of the core; cvc5 answers such
  queries, sat with models and unsat, by unfolding (measured below);
- any structural recursion, on constant arguments, which unfolds
  completely.

The `undecidable` lint reports every other application of a structural
recursion, at the application (`Construct::Recursion`). A catamorphism
into `Int` or `Nat` that is not onto it, such as a size, is not in the core: cvc5 does not
derive that a size is never negative, which needs induction, and the
quantified fact that would supply it is lost under `fmf-fun` (below).

```fren
-- Whether the applications of a function of kind `rec_kind`, whose result is
-- a `Bool` or a set (`bool_or_set?`), or which is onto its result type
-- (`onto?`), are decided on arguments that vary.
set_option fren.evidence "tested" in
pub proc recursive_decided(rec_kind: RecKind, bool_or_set?, onto?): (det decided?) {
    ensure rule: decided? = (rec_kind = RecKind::NotRecursive
        or (rec_kind = RecKind::Catamorphism and (bool_or_set? or onto?)))
}
```

A function's own value in its own contract, as `r` in `ensure
keeps_value: eval(r) = eval(e)`, is not reported: the postcondition check
reads it by induction, below.

## Contracts

A structural recursion's postconditions are checked by structural
induction on its decreasing parameter, with Hoare's rule for recursive
procedures (1971): the check of each postcondition assumes, besides the
preconditions, its *induction hypotheses*: the postcondition itself at
each payload of the parameter that is of the parameter's own type, with
the other parameters as they are, where the parameter is that payload's
variant and the payload meets the preconditions. For `fold` below, they
are that where `e` is `Expr::Add(a, b)`, `eval(fold(a)) = eval(a)` and
`eval(fold(b)) = eval(b)`:

```text
pub fn fold(e: Expr): (r: Expr) {
    out r := match e { ... }
    ensure keeps_value: eval(r) = eval(e)
}
```

- **Sound.** Under its variant, each payload is a value smaller than the
  parameter, so the hypotheses are those of an induction on the
  parameter's structure: a postcondition whose check passes holds for
  every argument. Each check assumes its own postcondition's hypotheses
  alone, so that it passes by its own induction, whatever the others are.
- **Genuine counterexamples.** The function is a recursive definition for
  the solver, so every model gives it its real value at every argument:
  a model of the check is an argument at which the postcondition is
  false. Where the hypotheses are too weak for the step, the solver does
  not find a model of a true postcondition; it answers `unknown`, and the
  check is `Inconclusive`. There are no lemmas or hints: a stronger
  postcondition is a stronger spec, or the proof is Lean's.
- **Lean.** The generated Lean definition is a structural recursion, so
  the same induction proves the postcondition there (`examples/Arith.lean`
  proves `fold`'s). The generated Lean does not yet state or prove a
  function's postconditions itself.

`lang::induction_hypotheses` states whether there is a hypothesis at a
value of a variant's payload, over the variants of the decreasing
parameter's enumeration, each with whether each value of its payload is
of the enumeration itself:

```fren
-- A value of a variant's payload: of the enumeration itself, or another type.
pub enum Slot { Own, Other }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc induction_hypotheses(
    variants: Seq<Seq<Slot>>,  -- each variant's payload, in order
    variant: Int,              -- a variant, by its position
    slot: Int,                 -- a value of its payload, by its position
): (det hypothesis?) {
    ensure rule: hypothesis? = (0 <= variant < variants.len and 0 <= slot < variants[variant].len
        and variants[variant][slot] = Slot::Own)
}
```

Callers see a structural recursion through its recursive definition, as
before; its postconditions are not yet added at its applications as
facts.

A future version brings more into the core through contracts: a
paramorphism whose contract is `det` (#366), checked by realizability, by
determinism, and by the induction above, and in a fragment that cvc5
decides, has its value pinned down by the postconditions as ground facts
at each application.

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
| `eval(e) = 5`, `e` not a `Val` (an `eval` onto `Int`) | | sat, with a model |
| `eval(Add(e, Val(0))) != eval(e)` | | unsat |
| `eval(e) > 100` and `eval` of its left operand `< 0` | | sat, with a model |
| `fold`'s induction step for `keeps_value` | | unsat |
| the same for `eval(r) = eval(e) + 1` | | sat: `e = Val(0)` |

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
#fren_check recursive_kind
#fren_check recursive_decided
#fren_check recursive_match
#fren_check induction_hypotheses
```
