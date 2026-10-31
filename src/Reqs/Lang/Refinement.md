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
pub mod refinement

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

pub proc refinement_computed_local(definition_value: Int, concrete_private_value: Int): (
    det abstract_local: Int,
) {
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

Result type predicates are part of the claim even when there is no
explicit `ensure`. Positional result matching retains these predicates.
A typed local assignment can carry that obligation in an expanded claim; it checks
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
pub proc refinement_singleton_domain(domain: Set<Int>, forced: Int, continuation: Set<Int>): (
    det full?,
    det singleton?,
) {
    ensure full_enumeration: full? iff domain inter {forced} subset continuation
    ensure singleton_enumeration: singleton? iff (when forced in domain, forced in continuation)
    expect exact: full? iff singleton?
    expect outside_type: when not forced in domain, full? and singleton?
}
```

#fren_check
