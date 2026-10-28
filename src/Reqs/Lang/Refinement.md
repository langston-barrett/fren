# Refinement

A refinement claim is written inside a global expectation block:

```
expect example(x: Int) {
    call c := implementation(x)
    refines c specification(x)
}
```

The block supplies explicit parameters and assumptions. The call establishes
its implementation's preconditions; `refines` checks the specification's
guarantees using the call's public results in declaration order. Arguments
and results may widen from `Nat` to `Int`. Specification assumptions are
not added implicitly, private `let` values are computed, and private
`exists` values are rejected. See [Refinement in expectation blocks](#refinement-in-expectation-blocks)
for the current decision models and hosted proof rules.

## Legacy migration model

The following models describe the removed top-level refinement syntax for
migration and the historical `Impls.Refine` decisions. Their name-based
interfaces and explicit bindings do not describe normal `refines` syntax.

```fren
pub mod refinement
```

## The interface

`a` and `c` are related through `a`'s variables. By default, each is
read as the variable of `c` of the same name: each parameter of `a` must be
a parameter of `c`, and each output of `a` a result of `c`, of the same
type, or one that [widens](Types.md#natural-numbers) in the direction its
values flow. An output of `c` is read where `a`'s type is expected, so
`c`'s type must widen to `a`'s: a `Nat` output of `c` serves for an `Int`
of `a`. An input of `a` is given to `c`, so `a`'s type must widen to
`c`'s: an `Int` input of `c` serves for a `Nat` of `a`, but a `Nat` input
of `c` does not serve for an `Int` of `a`, since `c` need not accept the
inputs below 0 that `a` does. The input then has `a`'s type, and the
output `c`'s, for what a `Nat` brings. Types are compared without their
[patterns](Types.md#pattern-types), as anywhere, and their constraints
follow the values too: the refinement assumes what `a`'s inputs' pattern
types bring, checks what `c`'s inputs' bring as `c`'s call
assumptions, and checks what `a`'s outputs' bring as it checks `a`'s
guarantees. An `exists` or `let` variable of `a` must be a result of `c` too: `a`'s
guarantees may mention it, and the refinement can read it only from
`c`'s results, since an `exists` or `let` variable says nothing about how `c`
computes it. `c` may have more inputs and outputs than `a`. An input of
`c` that no variable of `a` reads, by name or through a binding (see
[Bindings](#bindings)), is unconstrained by `a`'s assumptions, so an
assumption of `c` about such an input makes the refinement fail unless it
holds, given `a`'s assumptions, whatever that input is (see [The
obligation](#the-obligation)). An input that a binding reads is
constrained through it: with `x := y - 1`, `a`'s assumption `x > 0` says
`y - 1 > 0`, so `c` may assume `y > 1`. `a`'s calls are `a`'s own,
and stay hidden. A variable of `a` that `c` does not have
with the right role and type is an error (`F0412`). `refinement::interface`
states the rule for one variable of `a` that the refinement does not bind
(see [Bindings](#bindings)):

```fren
pub proc interface(
    input?,              -- the variable is an input of `a`, rather than an output
    in_concrete?,        -- `c` has a variable of the same name
    concrete_input?,     -- that variable is an input of `c`
    concrete_pub?,       -- that variable is a result of `c`
    a_widens?,           -- its type in `a` widens to its type in `c` (`lang::widening`)
    c_widens?,           -- its type in `c` widens to its type in `a`
): (det accepted?) {
    ensure rule: accepted? iff (in_concrete? and (if input? then a_widens? else c_widens?)
        and (if input? then concrete_input? else not concrete_input? and concrete_pub?))

    expect hidden_outputs: when not input? and not concrete_pub?, not accepted?
    -- An input flows from `a` to `c`, and an output from `c` to `a`.
    expect inputs_from_abstract: when input? and accepted?, a_widens?
    expect outputs_from_concrete: when not input? and accepted?, c_widens?
}
```

## Bindings

Where the names differ, or `a` is more abstract than `c`, a refinement
can bind variables of `a`. The bindings are written in braces after `a`,
as `x := e`, separated by commas:

```
refine fmt_exit_status: fmt::exit refines cli::exit_status { ran? := all_parsed? }
```

Each binding `x := e` gives the variable `x` of `a` as the expression `e`
over `c`'s variables, in place of `c`'s variable named `x`. `x` alone means
`x := x`. Since `e` is an expression, not just a name, a binding can be an
abstraction function, as in `{ forbidden? := level = Forbid }`. `e` must
have the type of `x` in `a`, as a call's argument must have the type of
its parameter. It is written at the refinement, so other names in it resolve
as they do there.

A refinement may bind any variable of `a`, input or output, each at most
once, and nothing else: a name that is not a variable of `a` (`F0413`), or
one bound twice (`F0414`), is an error. Unlike a call, it need not
bind every variable: the others are read by name, as in [The
interface](#the-interface). `refinement::binding` states the rule for one
name, given whether it is a variable of `a` and how many times the
refinement binds it:

```fren
pub proc binding(
    variable?,           -- the name is a variable of `a`
    n: Nat,              -- bindings of this name in the refinement
): (det accepted?) {
    ensure rule: accepted? iff (n = 0 or (variable? and n = 1))

    expect bound_once: when accepted?, n <= 1
}
```

A binding sees `c` from outside, as `a`'s variable would. Only `c`'s own
variables are in scope in it: the variables of `c`'s calls, such as
`inner.y`, are not, and neither are its calls' names, so `inner.y`
is a dotted name whose root is not in scope (`F0111`), as anywhere else.
Of `c`'s own variables, a binding may mention the parameters and
results, and no `exists` or `let` variable. A binding of an input of `a` may mention
`c`'s inputs only, since `a`'s inputs are chosen by the environment, before `c` chooses
its outputs, and `a`'s assumptions, which mention them, constrain the
environment. A result of `c` with a definition is an output here, whatever its
definition mentions. A mention that breaks this rule is an error
(`F0415`). `refinement::mention` states it, for one variable of `c`
mentioned in a binding:

```fren
pub proc mention(
    input?,              -- the binding binds an input of `a`
    concrete_input?,     -- the variable mentioned is an input of `c`, rather than an output
    concrete_pub?,       -- it is a result of `c`
): (det allowed?) {
    ensure rule: allowed? iff (concrete_input? or (not input? and concrete_pub?))

    expect inputs_see_inputs: when input? and allowed?, concrete_input?
    expect private_hidden: when not concrete_input? and not concrete_pub?, not allowed?
}
```

A binding is part of the refinement, which is checked as a procedure (see
[The obligation](#the-obligation)), so the [decidable
core](Decidability.md#relations) is a procedure's: if the refinement
applies a relational operator, in a binding or through `c` or `a`, then a
`card` of anything but a constant in a binding is outside the core, and
so are `c` and `a` if they count.

The indexes of a binding are checked for
[definedness](../Check.md#definedness) where it is read. An input's
binding is checked under all of `a`'s assumptions, with the bindings
substituted into them, and nothing else: not the call of `c`, nor any
other hypothesis. An assumption on another binding can guard an index:
with `n := q.len` and `assume pos: n > 0` in `a`, `x := q[0]` is defined.
Without one, an input's binding is guarded within its own expression, as
in `if q != [] then q[0] else 0`. An output's binding is
checked under the hypotheses of the obligation's second part below: `a`'s
assumptions, the call of `c`, and `a`'s calls.

## The obligation

In the notation of [Procedures](Procedures.md#meaning), with `i` the
inputs of `c`, `y` the variables of `c`'s calls, `o` its outputs, `w`
the variables of `a`'s calls, and each variable of `a` read as its
binding, over `i` and `o`, or else as `c`'s variable of the same name,
`c` refines `a` when, for all `i`:

  A_a(i) → A_c(i)

and for all `i`, `y`, `o`, `w`:

  A_a(i) ∧ I_c(i, y) ∧ R_c(i, y, o) ∧ D_c(i, y, o) ∧ I_a(i, w) → R_a(i, w, o) ∧ D_a(i, w, o)

Fren checks this as it checks a procedure: the refinement is a procedure
whose parameters are `c`'s, whose assumptions are `a`'s, with a call of
`c` named as `c` is, and `a`'s calls, and whose expectations are `a`'s
guarantees and `a`'s definitions. Throughout,
`a`'s variables are replaced by their bindings, or their names, with
`c`'s outputs read from the call of `c`. `a`'s calls are hypotheses there, as
`I_a` is above: their assumptions are `a`'s own obligations, checked in
`a`. The first part of the obligation is then
the [call assumption](../Check.md#call-assumptions) check of the
call of `c`, and the second part its [expectation
checks](../Check.md#expectations). A failure is reported as for those
checks, with a counterexample, at the refinement. `refinement::checks` gives
which checks run on a refinement: those that check the obligation, and the
[definedness](../Check.md#definedness), [completeness](../Check.md#completeness),
[disjointness](../Check.md#disjointness) and
[preconditions](../Check.md#preconditions) of what it reads. Not
[reachability](../Check.md#reachability): the bindings may narrow the
abstract procedure's inputs, so that an arm or a row of one of its
`match`es or tables is never taken under them, which says nothing about
how it is written, and the abstract procedure's own checks ask it:

```fren
use check::Kind

pub proc checks(kind: Kind): (det runs?) {
    use check::Kind::{
        Completeness,
        Definedness,
        Disjointness,
        Expectation,
        InstanceAssumption,
        Precondition,
    }

    ensure rule: runs? iff kind in {InstanceAssumption, Expectation, Definedness, Completeness, Disjointness, Precondition}
}
```

A refinement has no guarantees of its own, so the other checks would
only repeat those of `a` and `c`.

## Evidence

By default the solver decides the obligation. `set_option fren.evidence
"tested" in` before the refinement has it tested instead (see [Checking by
testing](../Check.md#checking-by-testing)). Where a precise procedure,
whose [unbounded quantifiers](Quantifiers.md#unbounded-quantifiers) put it
outside the decidable core, cannot be proved of the code, as
[Quantifiers](Quantifiers.md#unbounded-quantifiers) prefers, this is how
it is related to a bounded one in the core: the tests evaluate the precise procedure's quantifiers on the
behaviours of the refinement, as long as each has a
[domain](Quantifiers.md#guards). A quantifier without one cannot be
tested, which is an error (`F0639`).

In Lean, `by` and tactics prove it instead: Fren generates the obligation
as a proposition, `r`, named as every item's declarations are (see
[Names](../Generated.md#names)), and the tactics must prove it. Then no check of the refinement is asked of the solver, and a
proof that does not succeed is an error. The `fren` command does not run
Lean, so `by` is a static error there, like any construct that needs Lean
(see [The `fren` command](../Cli.md#agreement-with-lean)).

A refinement is not a procedure: it has no evidence in the sense of
[Traceability](../Trace.md), and does not change the evidence of `a` or `c`.


## Refinement in expectation blocks

The replacement syntax is `refines c a(args)` inside a global expectation
block. It claims the guarantees of `a`, with its inputs taken from `args`
and its results taken positionally from call `c`. Result names need not
agree. The arguments use ordinary argument typing. Values widen from
`Nat` to `Int`, never in the opposite direction. An abstract `let` is
computed from its definition and is not a result to match. An abstract
`exists` is rejected: the author must make it a result. No assumption
of `a` is introduced by this claim. The enclosing block's assumptions
must discharge the ordinary preconditions of `call c := ...`.

The following decision uses ordered result types and an actual position,
so arity and widening are specified independently of names. The decision
is for a queried result slot; every slot must pass. `existentials` records
uncomputed private outputs, which never contribute a public result slot.
The same directional type rule checks arguments flowing into parameters.

```fren
pub enum RefineValueType { Natural, Integer, Boolean, Text }

pub proc positional_refinement(
    actual: Seq<RefineValueType>,
    required: Seq<RefineValueType>,
    position: Int,
    existentials: Set<String>,
): (det arity?, det slot?, det accepted?) {
    out arity? := actual.len = required.len
    out slot? := 0 <= position < actual.len and position < required.len and (actual[position] = required[position] or (actual[position] = RefineValueType::Natural and required[position] = RefineValueType::Integer))
    out accepted? := arity? and slot? and existentials = {}
    expect no_narrowing: when 0 <= position < actual.len and position < required.len
        and actual[position] = RefineValueType::Integer and required[position] = RefineValueType::Natural, not slot?
    expect existential_rejected: when existentials != {}, not accepted?
    expect length_mismatch: when actual.len != required.len, not accepted?
}
```

`block_refinement` specifies the claim over actual sets of valuations.
In particular, the specification's precondition does not filter the
block's domain. A counterexample outside that precondition still refutes
the claim. The separate call check establishes the implementation's
preconditions from the block's assumptions and earlier calls.

```fren
pub type RefineWorld

pub proc block_refinement(
    block_domain: Set<RefineWorld>,
    implementation: Set<RefineWorld>,
    specification_domain: Set<RefineWorld>,
    guarantees: Set<RefineWorld>,
    witness: RefineWorld,
): (det holds?) {
    ensure validity: holds? iff block_domain inter implementation subset guarantees
    expect outside_precondition: when witness in block_domain and witness in implementation
        and not witness in specification_domain and not witness in guarantees, not holds?
    expect full_domain: when guarantees = {}, holds? iff block_domain inter implementation = {}
}

pub proc refinement_computed_local(
    definition_value: Int,
    concrete_private_value: Int,
): (det abstract_local: Int) {
    out abstract_local := definition_value
    expect evaluated: abstract_local = definition_value
    cover not_matched: abstract_local != concrete_private_value
}
```

A hosted `by` proof proves the same claim, universally over the block's
parameters and call variables, under the block's assumptions, earlier
calls and computed definitions. A failed proof, an unresolved goal, or
`sorry` does not establish it. A specification's own calls share the
interpretation of the block and contribute their meanings as hypotheses;
its private call variables are universally quantified in the claim.

`fren fix` migrates a removed top-level item by making its shared inputs
parameters, copying the specification's assumptions with definition-site
name resolution, calling the implementation, and passing the former
input bindings as argument expressions. When the old item associates
results by name in a different order, or binds an output expression, its
claims must be written as ordinary inner expectations rather than silently
changing that mapping to positional matching. `--check` does not write;
a statically invalid replacement leaves all original files unchanged.


Result type predicates are part of the claim even when there is no
explicit `ensure`. Migration must retain them when a result is mapped by
an old binding, as well as when it is matched positionally. A typed local
assignment can carry that obligation in an expanded migration; it checks
the type rather than assuming it.

```fren
pub proc refinement_result_domain(
    required_values: Set<Int>,
    guarantee_values: Set<Int>,
    candidate: Int,
): (det accepted?) {
    ensure both: accepted? iff candidate in required_values inter guarantee_values
    expect type_cannot_disappear: when not candidate in required_values and candidate in guarantee_values, not accepted?
    expect guarantee_still_needed: when candidate in required_values and not candidate in guarantee_values, not accepted?
    cover only_type_fails: not candidate in required_values and candidate in guarantee_values
}
```


Testing can enumerate a call variable determined by an unconditional
equality using a singleton domain. It must retain the equality and the
variable's type predicate. This is exact, not a random choice: if the
forced value is outside the declared domain there is no admitted world.
The equivalence below models an arbitrary continuation as a set of values:

```fren
pub proc refinement_singleton_domain(
    domain: Set<Int>,
    forced: Int,
    continuation: Set<Int>,
): (det full?, det singleton?) {
    ensure full_enumeration: full? iff domain inter {forced} subset continuation
    ensure singleton_enumeration: singleton? iff (when forced in domain, forced in continuation)
    expect exact: full? iff singleton?
    expect outside_type: when not forced in domain, full? and singleton?
}
```

#fren_check
