# Implementations

An implementation states, in Lean, that Lean code meets a component, and
proves it.

```
implementation := "impl" IDENT ":" path ["for" binder+]
                  "{" [map ("," map)* [","]] "}" ["by" TACTICS]
binder         := "(" IDENT+ ":" TERM ")"
map            := IDENT ":=" TERM
```

Implementations exist only in Lean; the [`fren` command](Cli.md) rejects
them.

## Example

For the `thermostat` of the [Language overview](Lang/Overview.md), with this
Lean function:

```lean
def choose_mode (t g : Int) : climate.Mode :=
  if t < g - 2 then .Heat else if t > g + 2 then .Cool else .Off
```

this implementation states that `choose_mode` meets `thermostat`, and proves
it:

```lean
impl choose_mode_thermostat: climate::thermostat for (t g : Int) {
  temp := t, target := g, mode := choose_mode t g
} by
  intro t g _
  by_cases h1 : t < g - 2 <;> by_cases h2 : g + 2 < t <;>
    simp [fren_spec, choose_mode, h1, h2] <;> omega
```

It adds the theorem

```lean
choose_mode_thermostat : ∀ (t g : Int),
  climate.thermostat.assumes t g (choose_mode t g) →
  climate.thermostat.ensures t g (choose_mode t g)
```

## Meaning

`impl n: c for (x : T) ... { v := e, ... }` interprets each variable `v` of
the component `c` as the Lean term `e`. The binders after `for` must be
explicit binders, and are universally quantified. The component path is
resolved, and its visibility checked, from the current Fren module. The name
`n` is a Lean declaration name, in the current Lean namespace.

An implementation must give a term for each input and each public output of
the component, of its [Lean type](Generated.md), and for nothing else.
Private outputs and the variables of the component's instances are internal
to it, so the implementation need not compute them.

The implementation's *obligation* is a theorem named `n`, stated with the
component's [generated definitions](Generated.md):

```
∀ binders, c.assumes ι⃗ v⃗ d⃗ → ∃ h⃗, c.defs ι⃗ v⃗ h⃗ ∧ c.ensures ι⃗ v⃗ h⃗ ∧ c.inst.w₁ ι⃗ v⃗ h⃗ ∧ … ∧ c.inst.wₖ ι⃗ v⃗ h⃗
```

`c.defs` is there only when `c` has [defined
outputs](Lang/Components.md#defined-outputs). A public defined output is
given a term like any public output, and the obligation proves it equal
to the definition; a private one is among `h⃗`, and its witness is its
definition.

where `ι⃗` are the [interpretations](#interpretations) of the abstract
types and functions that `c` uses, if any, `v⃗` are the given terms, `h⃗` are the private outputs and instance
variables, and `d⃗` are `default` values for them, which the assumptions
never mention. When there are no private outputs or instances, as in the
example, the obligation is `∀ binders, c.assumes v⃗ → c.ensures v⃗`. So an
implementation meets the component for every input that the component's
assumptions allow. Expectations and [cover
goals](Lang/Components.md#cover-goals) are not part of the obligation.

`impls::mapping` states which variables must be given terms. `Role` is the
classification from [Instances](Lang/Instances.md#instance-variables):

```fren
pub mod impls

use check::{Outcome, Verdict}
use check::Outcome::{Sat, Unknown, Unsat}
use check::Verdict::{Fail, Inconclusive, Pass}
use inst::Role
use inst::Role::{Input, Output}

pub comp mapping {
    in role: Role
    in is_pub?
    in n: Nat            -- terms given for this variable
    pub out accepted?

    ensure rule: accepted? iff n = (if role = Input or (role = Output and is_pub?) then 1 else 0)

    expect private_not_mapped: when role = Output and not is_pub? and accepted?, n = 0
    expect inputs_mapped: when role = Input and accepted?, n = 1
}
```

An implementation of a component that uses abstract types or functions
must come after an interpretation of each. `impls::interpreted` states
this:

```fren
pub type ItemName

pub comp interpreted {
    in used: Set(ItemName)           -- abstract types and functions the component uses
    in interpreted: Set(ItemName)    -- those interpreted earlier, in the file and its imports
    pub det out accepted?

    ensure rule: accepted? iff used subset interpreted

    expect concrete_specs: when used = {}, accepted?
}
```

## Interpretations

```
interpretation := "interp" path ":=" TERM ["by" TACTICS]
```

An interpretation gives the Lean meaning of an [abstract
type](Lang/Types.md#abstract-types) or a [function](Lang/Items.md#functions),
which a spec leaves open (see
[Interpretations](Lang/Components.md#interpretations)). For example, for

```
type Name
fn ends_in_q?(Name)
```

these interpretations say that a `Name` is a Lean name, and what it is for
one to end in `?`:

```lean
interp Name := Lean.Name
interp ends_in_q? := fun n => n.toString.endsWith "?"
```

`interp p := t` interprets `p` as the Lean term `t`. The path `p` is
resolved, and its visibility checked, from the current Fren module, and
must name an abstract type or an uninterpreted function: a defined
function's body already gives its meaning. For an abstract type, `t` must be
a type with an `Inhabited` instance, since an abstract type has at least
one value. For a function, `t` must have the function's Lean type, with
each abstract type replaced by its interpretation, so the abstract types in
a function's parameters and result must be interpreted before it. The
interpretation adds the reducible definition `q := t`, where `q` is the
Lean name of `p`, in `Fren.Generated` under the current Lean namespace
(see [Names](Generated.md#names)).

Each abstract type and function is interpreted at most once, in a Lean file
and the files it imports, so every implementation uses the same meaning.
An interpretation is not checked against the spec, which states nothing
about a function beyond its type, including a [pattern
type](Lang/Types.md#pattern-types) of its result, and its
[postconditions](Lang/Items.md#contracts): it says what the spec's author
means by the function, and is reviewed as part of the spec. Every
application is assumed to meet both, so they are proved of its
interpretation, as one statement: `interp p := t`, for a function with
postconditions or whose result type brings a constraint, adds the theorem
`q.ensures`, that for all values of the parameters, `t` at them matches
the result type, whatever the parameters' types, since an application's
constraint holds wherever it is written, and, where they meet the
preconditions, meets each postcondition, where the abstract types and
functions that the contract and the result type use are their
interpretations. It is proved by the tactics after `by`, if there are
any, and otherwise by `decide` or, failing that, by the solver, as an
[implementation](#proof) is, in which case it is an axiom. An
interpretation whose statement is not proved is an error, and adds
nothing, so the function can be interpreted again; a proof that uses
`sorry` proves nothing. So with `fn size(Int): Int is 0..=255`, `interp
size := fun _ => 300` is rejected, and no implementation can rely on it.
An interpretation is what makes an
implementation a claim about the code: the implementation of a component
that applies `ends_in_q?` is proved against the interpretation, not
against what the code computes. `impls::interpretation` decides whether an
interpretation is accepted:

```fren
pub enum Interpreted { AbstractType, Function, Other }

pub comp interpretation {
    in what: Interpreted       -- what the path names; a defined function is `Other`
    in earlier: Nat            -- interpretations of it in the file and its imports
    in typed?                  -- the term has the required type, and an `Inhabited` instance for a type
    in types_interpreted?      -- for a function: each abstract type in its signature is interpreted
    pub det out accepted?

    ensure rule: accepted? iff (what != Interpreted::Other and earlier = 0 and typed?
        and (what != Interpreted::Function or types_interpreted?))

    expect once: when earlier > 0, not accepted?
    expect only_open_items: when what = Interpreted::Other, not accepted?
}
```

`impls::interpretation_contract` states how an
interpretation of a function proves its postconditions and its result
type's constraint, from whether it has any, its written proof, if any, and the answers of `decide` and the
solver, which are asked in turn only when the earlier ones prove nothing:

```fren
pub enum ContractProof { NotNeeded, Theorem, Axiom, Unproved }

pub comp interpretation_contract {
    use self::ContractProof::{Axiom, NotNeeded, Theorem, Unproved}
    in obligated?        -- the function has postconditions, or its result type brings a constraint
    in written?          -- the interpretation has tactics after `by`
    in written_ok?       -- they elaborate without an error
    in uses_sorry?       -- the proof they give uses `sorry`
    in decide_q: Outcome  -- `Unsat` if `decide` proves the statement, `Sat` if it evaluates it to false
    in smt_q: Outcome    -- can the solver prove the statement?
    pub det out proof: ContractProof
    pub det out recorded?    -- the interpretation, and its theorem, are added
    pub det out error?       -- an error is reported

    ensure rule: proof = table {
        | not obligated? => NotNeeded,
        | obligated? and written? => if written_ok? and not uses_sorry? then Theorem else Unproved,
        | obligated? and not written? and decide_q = Unsat => Theorem,
        | obligated? and not written? and decide_q = Sat => Unproved,
        | obligated? and not written? and decide_q = Unknown => if smt_q = Unsat then Axiom else Unproved,
    }
    ensure records: recorded? iff proof != Unproved
    ensure reports: error? iff proof = Unproved

    expect sorry_proves_nothing: when obligated? and written? and uses_sorry?, not recorded? and error?
    expect failure_records_nothing: when error?, not recorded?
}
```

`impls::interpretation_at` states what an interpretation without a
written proof must meet, over the domain of [contract
realizability](Check.md#contracts-of-uninterpreted-functions): the
interpretation gives each argument a value, `at_a0` and `at_a1`, and is
recorded exactly when, at each argument that meets the preconditions, its
value meets the postconditions, which `decide` decides on so small a
domain. Its implementation decides the statement over the domain and
proves with the real decision. It refines
`impls::interpretation_contract`:

```fren
use check::{Argument, Point, Value}

pub comp interpretation_at {
    in pres: Set(Argument)   -- the arguments that meet the preconditions
    in posts: Set(Point)     -- the arguments and values that meet the postconditions
    in at_a0: Value          -- the interpretation's value at `A0`
    in at_a1: Value          -- at `A1`
    pub det out recorded?

    ensure rule: recorded? iff ((when Argument::A0 in pres, Point { arg := Argument::A0, value := at_a0 } in posts)
        and (when Argument::A1 in pres, Point { arg := Argument::A1, value := at_a1 } in posts))

    expect unconstrained: when pres = {}, recorded?
}

refine interpretation_detail: interpretation_at refines interpretation_contract {
    obligated? := true,
    written? := false,
    written_ok? := false,
    uses_sorry? := false,
    decide_q := if (when Argument::A0 in pres, Point { arg := Argument::A0, value := at_a0 } in posts)
        and (when Argument::A1 in pres, Point { arg := Argument::A1, value := at_a1 } in posts) then Unsat else Sat,
    smt_q := Unknown,
    proof := if recorded? then ContractProof::Theorem else ContractProof::Unproved,
    error? := not recorded?,
}
```

## Proof

The obligation is proved in one of three ways:

1. By the tactics after `by`, if there are any. In a proof, `simp
   [fren_spec]` unfolds the component's definitions.
2. Otherwise by `decide`, evaluated by Lean's kernel. This applies when
   every binder's type has a `Fren.Finite` instance (see [Generated Lean
   declarations](Generated.md)). If `decide` finds that the obligation is
   false, the implementation fails, and Fren reports values of the binders
   that falsify it, and which guarantees they falsify.
3. Otherwise by the solver, with Fren's generated definitions unfolded and
   the implementation's definitions left uninterpreted. A proof by the
   solver adds the theorem as an axiom, which `#print axioms` shows. Since
   the solver does not see the implementation's definitions, its models may
   be spurious, so it never refutes an implementation: if it does not prove
   the obligation, the implementation is inconclusive, and Fren warns and
   asks for a written proof.

`impls::obligation` gives the verdict, from whether a proof is written and
accepted, and the outcomes of `decide` and the solver:

```fren
pub comp obligation {
    in written?          -- a proof is written with `by`
    in written_ok?       -- Lean accepts it
    in decide_q: Outcome  -- `Unsat`: `decide` proves it; `Sat`: it evaluates to false; `Unknown`: it does not apply
    in smt_q: Outcome    -- the solver, asked only if `decide_q` is `Unknown`
    pub out verdict: Verdict
    pub out names_failures?  -- report a counterexample and the guarantees it falsifies
    pub out axiom?         -- the statement is added as an axiom, on the solver's word

    ensure written_proof: when written?, verdict = (if written_ok? then Pass else Fail)
    ensure decided: unless written?, when decide_q != Unknown, verdict = (if decide_q = Unsat then Pass else Fail)
    ensure solver: unless written?, when decide_q = Unknown, verdict = (if smt_q = Unsat then Pass else Inconclusive)
    ensure failures: names_failures? iff (not written? and decide_q = Sat)
    ensure by_solver: axiom? iff (not written? and decide_q = Unknown and smt_q = Unsat)

    expect fails_only_by_proof: when verdict = Fail, written? or decide_q = Sat
    expect kernel_unless_axiom: when verdict = Pass and not axiom?, written? or decide_q = Unsat
}
```

## Vacuous implementations

The obligation assumes the component's assumptions, of the terms given to
the inputs. If no values of the binders satisfy them, the obligation holds
whatever the code computes, and says nothing about it. This can happen
because of the terms, such as `temp := 1000` when an assumption bounds
`temp`, or because of an interpretation: with `interp arity := fun _ =>
-1`, no name satisfies `assume nonneg: arity(n) >= 0`. The checks hold
under every interpretation, so they cannot see this; it depends on the one
the implementation uses.

So once an implementation passes, Fren asks whether some values of the
binders satisfy the assumptions. If every binder's type has a `Fren.Finite`
instance, and there are at most 4096 combinations of their values, Fren
tries each. Otherwise it asks the solver to prove that none do, with
Fren's generated definitions and the interpretations unfolded, and the
implementation's definitions left uninterpreted. Whatever the solver
assumes of those definitions, a proof holds of them too, so only a proof
counts. If none do, the theorem is still added, since it is true, but Fren
warns, and the implementation is not [evidence](Trace.md) for its
component. `impls::vacuity` states this:

```fren
pub comp vacuity {
    in added?            -- the theorem or axiom is added (`statement`)
    in finite?           -- the binders' values are tried, as above
    in found?            -- trying them finds values that satisfy the assumptions
    in smt_q: Outcome    -- the solver, asked only if not `finite?`, on "no values satisfy them"
    pub det out vacuous?     -- warn that the implementation holds vacuously
    pub det out evidence?    -- the implementation is evidence for its component

    ensure vacuous: vacuous? iff (added? and (if finite? then not found? else smt_q = Unsat))
    ensure evidence: evidence? iff (added? and not vacuous?)

    expect witnessed: when added? and finite? and found?, evidence?
    expect only_proofs_warn: when vacuous? and not finite?, smt_q = Unsat
}
```

## Using the theorem

A passing implementation's theorem, or axiom, is added to the environment,
so Lean code can rely on it. In particular, it can be used to prove an
implementation of a component that instantiates the component. A failing
or inconclusive implementation adds nothing.

`impls::statement` states this:

```fren
pub comp statement {
    in written?
    in written_ok?
    in decide_q: Outcome
    in smt_q: Outcome
    pub out added?       -- the theorem or axiom is added to the environment

    inst o: obligation { written?, written_ok?, decide_q, smt_q }

    ensure added_iff_pass: added? iff o.verdict = Pass

    expect solver_passes_are_axioms: when added? and not written? and decide_q = Unknown, o.axiom?
}
```

A passing implementation is also evidence for its component: see
[Traceability](Trace.md).

```fren
#fren_check
```
