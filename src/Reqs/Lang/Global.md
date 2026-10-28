# Global expectations

A procedure's [expectation](Procedures.md#members) is a claim about each of
its behaviours separately. A global expectation is a claim about procedures
as a whole: it can relate several behaviours of one procedure, or behaviours
of different procedures. It is written like a procedure, with parameters
and a block, and relates the procedures by [calling](Calls.md) them:

```
expectation := "expect" IDENT"(" [variable ("," variable)* [","]] ")" "{" member* "}"
             | "expect" IDENT ":" top
```

`expect n(x: T, ...) { ... }` claims that for all values of its
parameters, and all behaviours of the procedures it calls, its
assumptions imply each of its expectations. Its parameters are
quantified, as a procedure's inputs are: they may have any type, unbounded
ones included, and each is shown in a counterexample. Its block has the
members that a claim needs, and no others:

- `assume n: e` restricts the parameters, as a procedure's assumption
  does;
- `call w := p(...)` relates the procedure `p`, whose variables it reads
  as `w.x`, as a procedure's call does;
- `expect n: e` is a claim, and `cover n: e` a scenario that must be
  possible, as in a procedure;
- `let x: T := e` names an expression, and `use` imports names for the
  block, as in a procedure.

A global expectation constrains nothing, so it has no results, and no
`exists` or `ensure` member, nor an `out` member, which defines a result;
and nothing is determined by it, so no member is `det`. Each of these is
an error (`F0417`). It is an item, named like a procedure, but it is not
one: nothing can call it, and a call of it is an error, as a call of any
item that is not a procedure is. Its parameters, calls, constraints and
`let` variables share one namespace, as a procedure's do, and may
[shadow](Procedures.md#shadowing) the constants, functions and variants
of its module, written with `!`. Each procedure it calls must be declared,
and visible, before it.

```fren
pub mod lang
```

`lang::block_member` states which members a global expectation's block
accepts, and a result in its signature, which it does not:

```fren
pub enum BlockMember { Result, Exists, Let, Define, Assume, Ensure, Expect, Cover, Call, Use }

pub proc block_member(
    member: BlockMember,
    det?,                -- written with `det`
): (det accepted?) {
    use self::BlockMember::{Assume, Call, Cover, Define, Ensure, Exists, Expect, Let, Result, Use}

    ensure rule: accepted? iff (not det? and member in {Let, Assume, Expect, Cover, Call, Use})

    expect claims: when member in {Expect, Cover} and not det?, accepted?
    expect constrains_nothing: when member in {Result, Exists, Define, Ensure}, not accepted?
    expect determines_nothing: when det?, not accepted?
}
```

## The short form

`expect n: e`, without parameters or a block, is a claim about
[constants](Items.md#constants), such as `expect sane: MIN_TEMP <
MAX_TEMP`. It means what `expect n() { expect n: e }` means, and is
checked so, but it is reported by its own name, `n`, as a constraint of
its module is. `e` may end with a [`where` clause](Let.md), and may be a
[quantifier](Quantifiers.md#global-expectations) over values: `expect n:
forall (m: Method), E` claims `E` of every value `m` of `Method`.

## Example

`band` classifies a temperature (see [Calls](Calls.md#example)):

```
pub proc band(temp: Int, target: Int): (too_cold?, too_hot?) {
    ensure cold: too_cold? iff temp < target - 2
    ensure hot: too_hot? iff temp > target + 2
}

expect colder_is_cold(temp1: Int, temp2: Int, target: Int) {
    assume sorted: temp1 <= temp2

    call a := band(temp1, target)
    call b := band(temp2, target)

    expect colder: when b.too_cold?, a.too_cold?
}
```

`colder_is_cold` says that `band` is monotone: for the same target, a lower
temperature is at least as cold. It relates two behaviours of `band`, so it
cannot be an expectation of `band` itself. The calls share the parameter
`target`, so the claim is about two behaviours with the same target, and
the assumption says which temperatures it is about.

A global expectation can also say that two procedures agree. If
`fast_band` is meant to classify temperatures as `band` does:

```
expect same_band(temp: Int, target: Int) {
    call f := fast_band(temp, target)
    call b := band(temp, target)

    expect same: (f.too_cold? iff b.too_cold?) and (f.too_hot? iff b.too_hot?)
}
```

## Meaning

A global expectation means what its expectations mean in a procedure with
its parameters as inputs, its assumptions, its calls and its definitions,
and no outputs or guarantees (see [Procedures](Procedures.md#meaning)). With
`i` its parameters, `y` its calls' variables, `A(i)` its assumptions and
`I(i, y)` its calls' constraints, each expectation `E` holds if

  ∀ i y. A(i) ∧ I(i, y) ⇒ E(i, y)

with its definitions substituted. The assumptions of each call's
procedure are obligations on the call's arguments, as in any procedure,
which the global expectation's assumptions must discharge: the [call
check](../Check.md#call-assumptions) confirms that they do. So a global
expectation states its domain: the inputs it is about are those that its
assumptions admit, and each call is one that its procedure accepts.

All the calls share one [interpretation](Procedures.md#interpretations)
of the spec's abstract types and functions, and the global expectation
must hold under every interpretation. Its parameters are universally
quantified at the top of each query, as a procedure's inputs are, so no
bound on their types is needed.

A global expectation constrains nothing. It is not a procedure, and has no
[evidence](../Trace.md). The [checks](../Check.md#global-expectations)
confirm it: they are a procedure's, but for those of what it does not
have. Its assumptions must be satisfiable, as a procedure's must, or every
expectation would hold vacuously: the realizability check reports
contradictory ones (`F0602`).

## Checks as sets of behaviours

The following requirements model complete valuations, rather than flags
for individual pieces of syntax. `GlobalWorld` identifies a valuation of
the parameters, all call variables, and one shared interpretation. Sets
of these worlds describe the meanings of assumptions, calls and claims.
An expectation is validity over the admitted worlds; a cover is existence
within them. Call preconditions are obligations, never extra hypotheses.

```fren
pub type GlobalWorld

pub proc global_checks(
    assumptions: Set<GlobalWorld>,
    calls: Set<GlobalWorld>,
    earlier_calls: Set<GlobalWorld>,
    preconditions: Set<GlobalWorld>,
    claim: Set<GlobalWorld>,
    scenario: Set<GlobalWorld>,
): (det expectation?, det call_valid?, det inhabited?, det covered?) {
    let admitted: Set<GlobalWorld> := assumptions inter calls
    ensure expectation: expectation? iff admitted subset claim
    ensure obligation: call_valid? iff assumptions inter earlier_calls subset preconditions
    ensure nonvacuous: inhabited? iff admitted != {}
    ensure cover: covered? iff admitted inter scenario != {}

    expect universal: when admitted subset claim, expectation?
    expect missing_precondition: when not assumptions inter earlier_calls subset preconditions, not call_valid?
    expect no_call_filter: when assumptions = {} or calls = {}, not inhabited?
    expect impossible_scenario: when admitted inter scenario = {}, not covered?
    expect witness: when scenario = admitted and admitted != {}, covered?
}
```

Parameters range over their entire declared types. No enumeration size
limit applies to a block's parameters. Two calls receive the same input
exactly when their argument expressions give that value; outputs of an
earlier call may supply arguments to a later one. These executable claims
use unbounded integers, shared arguments, and an output passed onwards:

```fren
pub proc global_successor(x: Int): (det y: Int) {
    ensure successor: y = x + 1
}

expect global_composition(x: Int) {
    call first := global_successor(x)
    call again := global_successor(x)
    call next := global_successor(first.y)
    expect shared_argument: first.y = again.y
    expect composition: next.y = x + 2
    cover possible: next.y = 2
}
```

## Migration

The removed behaviour-binder form is accepted only as input to `fren
fix`. A behaviour binder contributes a fresh parameter for each input of
its procedure, in declaration order, and a call with those arguments.
Each value binder contributes a parameter. Each callee assumption is
copied with its inputs substituted, including definitions used by the
assumption. Names and types retain their original resolution. The old
body, including any `where`, becomes the inner expectation. Generated
names must avoid the original names, including locally bound names.
Guards equating inputs remain guards; migration does not merge inputs.
`--check` prints the change without writing, and `--ignore` excludes a
file. An unsuccessful migration writes no partial change.

The parameter types of one migrated binder are an ordered sequence,
not a set: a behaviour contributes its procedure's input types in order,
even when several inputs have the same type. A value contributes just
its own type. A procedure with no inputs still contributes one call.

```fren
pub enum GlobalBinderKind { Behaviour, Value }

pub proc global_migration_shape(
    binder_kind: GlobalBinderKind,
    input_types: Seq<String>,
    value_type: String,
): (det parameter_types: Seq<String>, det calls: Int) {
    out parameter_types := if binder_kind = GlobalBinderKind::Behaviour then input_types else [value_type]
    out calls := if binder_kind = GlobalBinderKind::Behaviour then 1 else 0
    expect behaviour_order: when binder_kind = GlobalBinderKind::Behaviour, parameter_types = input_types
    expect value_parameter: when binder_kind = GlobalBinderKind::Value, parameter_types = [value_type] and calls = 0
    expect zero_inputs: when binder_kind = GlobalBinderKind::Behaviour and input_types = [], parameter_types = [] and calls = 1
}

pub proc global_migration_name(
    reserved: Set<String>,    -- original declarations and locally bound names
    allocated: Set<String>,   -- names already allocated by this migration
    candidate: String,
): (det available?) {
    ensure fresh: available? iff not candidate in reserved union allocated
    expect original_name: when candidate in reserved, not available?
    expect generated_name: when candidate in allocated, not available?
    expect unused_name: when not candidate in reserved and not candidate in allocated, available?
}
```

`global_migration_meaning` states why copying the assumptions preserves
the old domain. Worlds that obey the old binders' assumptions and calls
are precisely those admitted by the migrated block:

```fren
pub proc global_migration_meaning(
    old_assumptions: Set<GlobalWorld>,
    calls: Set<GlobalWorld>,
    claim: Set<GlobalWorld>,
): (det old_worlds: Set<GlobalWorld>, det new_worlds: Set<GlobalWorld>, det same?) {
    out old_worlds := old_assumptions inter calls
    out new_worlds := old_assumptions inter calls
    ensure meaning: same? iff (old_worlds subset claim iff new_worlds subset claim)
    expect domains: old_worlds = new_worlds
    expect preserved: same?
}
```
