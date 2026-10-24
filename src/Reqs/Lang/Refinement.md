# Refinement

```
refinement := "refine" IDENT ":" path "refines" path ["by" TACTICS]
```

`refine r: c refines a` states that the component `c` *refines* the
component `a`: `c` accepts every input that `a` accepts, and on those
inputs every behaviour of `c` meets `a`'s requirements. So whatever `a`
guarantees, `c` guarantees too, and every expectation that follows from
`a`'s assumptions and requirements holds of `c`'s behaviours as well.

Refinement is a way to gain confidence in a spec where parts of it are hard
for the solver (see [Decidability](Decidability.md#in-practice)): `a` can
be a simpler component that the solver decides, whose expectations are
checked, and `c` the precise one. Whether `c` refines `a` is itself
checked, by the solver, by [testing](../Check.md#checking-by-testing), or,
in Lean, by a proof.

```fren
pub mod refinement
```

## The interface

`a` and `c` are related through `a`'s variables: each input of `a` must be
an input of `c`, and each output of `a` a public output of `c`, of the same
type. `c` may have more inputs and outputs than `a`; an input of `c` that
`a` does not have is unconstrained by `a`'s assumptions. `a`'s instances
are `a`'s own, and stay hidden. A variable of `a` that `c` does not have
with the right role and type is an error (`F0412`). `refinement::interface`
states the rule for one variable of `a`:

```fren
pub comp interface {
    in input?            -- the variable is an input of `a`, rather than an output
    in in_concrete?      -- `c` has a variable of the same name
    in concrete_input?   -- that variable is an input of `c`
    in concrete_pub?     -- that variable is public in `c`
    in same_type?        -- it has the same type as in `a`
    pub det out accepted?

    req rule: accepted? iff (in_concrete? and same_type?
        and (if input? then concrete_input? else not concrete_input? and concrete_pub?))

    expect hidden_outputs: when not input? and not concrete_pub?, not accepted?
}
```

## The obligation

In the notation of [Components](Components.md#meaning), with `i` the
inputs of `c`, `y` the variables of `c`'s instances, `o` its outputs, `w`
the variables of `a`'s instances, and `a`'s outputs read as `c`'s outputs
of the same names, `c` refines `a` when, for all `i`:

  A_a(i) → A_c(i)

and for all `i`, `y`, `o`, `w`:

  A_a(i) ∧ I_c(i, y) ∧ R_c(i, y, o) ∧ D_c(i, y, o) ∧ I_a(i, w) → R_a(i, w, o) ∧ D_a(i, w, o)

Fren checks this as it checks a component: the refinement is a component
whose inputs are `c`'s, whose assumptions are `a`'s, with an instance of
`c` named as `c` is, and `a`'s instances, and whose expectations are `a`'s
requirements and the definitions of `a`'s defined outputs, over the
outputs of the instance of `c`. The first part of the obligation is then
the [instance assumption](../Check.md#instance-assumptions) check of the
instance of `c`, and the second part its [expectation
checks](../Check.md#expectations). A failure is reported as for those
checks, with a counterexample, at the refinement. `refinement::checks` gives
which checks run on a refinement: those that check the obligation, and the
[definedness](../Check.md#definedness) of what it reads:

```fren
use check::Kind

pub comp checks {
    use check::Kind::{Definedness, Expectation, InstanceAssumption}
    in kind: Kind
    pub det out runs?

    req rule: runs? iff kind in {InstanceAssumption, Expectation, Definedness}
}
```

A refinement has no requirements of its own, so the other checks would
only repeat those of `a` and `c`.

## Evidence

By default the solver decides the obligation. `set_option fren.evidence
"tested" in` before the refinement has it tested instead (see [Checking by
testing](../Check.md#checking-by-testing)).

In Lean, `by` and tactics prove it instead: Fren generates the obligation
as a proposition, `r`, in the module's namespace, and the tactics must
prove it. Then no check of the refinement is asked of the solver, and a
proof that does not succeed is an error. The `fren` command does not run
Lean, so `by` is a static error there, like any construct that needs Lean
(see [The `fren` command](../Cli.md#agreement-with-lean)).

A refinement is not a component: it has no evidence in the sense of
[Traceability](../Trace.md), and does not change the evidence of `a` or `c`.

#fren_check
