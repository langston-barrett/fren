# Natural numbers

This lint of the `style` group finds an `Int` that a constraint makes a
`Nat`.

```fren
pub mod lint
```

## Integers kept at least 0

A [`Nat`](../../Lang/Types.md#natural-numbers) input brings the assumption
that it is at least 0 with its type, and a `Nat` output, public or
private, the guarantee (see [Natural
numbers](../../Lang/Components.md#natural-numbers)). `manual_nat` fires on
an input of a component declared an `Int`, one of whose assumptions has
the conjunct `x >= 0` or `0 <= x`, and on an output declared an `Int`, not
a defined one, one of whose guarantees has one. A *conjunct* is an
operand of the constraint's `and`s, outside parentheses but the
constraint's own, as written: `x` is the variable's name, and `0` the
literal, and the conjunct may be in parentheses. A bound under `when` or
`or`, or in an expectation or a cover goal, says nothing of every value
the variable takes, and is left as it is. The lint fires once for each
variable, at its first bound, in the order of the constraints.

The message suggests a fix, which `fren fix` does not make: declare the
variable a `Nat`, and remove its first bound from its constraint, or the
constraint if nothing else is left of it. It changes the component's
interface, which an instance or a refinement in another file may rely
on, as below, so it is the writer's to make. Of a component,
a bound is in an assumption only for an input, which an assumption alone
may mention, and in a guarantee for an output, so the `Nat` brings what
it removes. Within the component, the fix keeps what the spec means, and the guards: a
conjunct after the bound was guarded by it, and is by the `Nat`'s
constraint instead, which every query of the component has among its
hypotheses (see [Checks](../../Check.md)). Each expression keeps its type
but those that the variable's widening makes `Nat`s, and a `Nat` is
accepted wherever an `Int` is, so the component stays well typed. Its
interface changes, though, and an `Int` is never narrowed: an instance
must then bind the variable to a `Nat`, and a refinement that reads it by
name must read it as a `Nat` input or give it as a `Nat` output. A spec
whose instance binds it to an `Int`, such as `n - k` where an assumption
of the instance's component makes that at least 0, relies on the
assumption, which the [instance check](../../Check.md#instance-assumptions)
confirms, and cannot have the `Nat` instead. So the lint does not fire on
a variable that an instance in the same file binds to an `Int`, nor on
one that a refinement in it binds to an `Int`, reads by name as an `Int`
input of the abstract component, for the concrete one's input, or reads
by name from an `Int` output of the concrete component, for the abstract
one's output. It waits for the end
of the file to know. An instance or a refinement in another file is not
seen, which is why `fren fix` leaves the fix to the writer, and the
message says that an instance must then give a `Nat`. It is
`warn` by default, as most such inputs are counts or positions, which
are `Nat`s, and nothing but the variable's uses decides that. Clippy has
no lint like it. `lint::manual_nat` states when it fires, and
`lint::nat_kept` when a refinement that reads a variable by name keeps it an `Int`:

```fren
pub comp manual_nat {
    in input?            -- the variable is an input, rather than an output
    in defined?          -- it is a defined output
    in int?              -- it is declared an `Int`
    in assumption?       -- the constraint is an assumption, rather than a guarantee
    in bound?            -- the constraint has the conjunct `x >= 0` or `0 <= x`
    pub det out fires?

    ensure rule: fires? iff (int? and not defined? and bound? and (input? iff assumption?))

    expect inputs_assume: when fires? and input?, assumption?
}

pub comp nat_kept {
    in input?            -- the variable is an input, rather than an output
    in abstract_int?     -- the abstract component's variable of the name is an `Int`
    in concrete_int?     -- the concrete component's is
    pub det out kept?    -- the refinement keeps one of them an `Int`
    pub det out concrete?  -- that one is the concrete component's, rather than the abstract one's

    ensure rule: kept? iff (abstract_int? and concrete_int?)
    ensure which: concrete? iff input?
}
```

The [refinements](../../Lang/Refinement.md) below check the fix of an input,
each way, and of an output, one way: components as written, as fixed, and
a refinement between them, so that the solver checks that they agree for
every value of the inputs. A refinement whose abstract input is an `Int`
binds it to the concrete `Nat`, which widens. The other way for an
output would read the written `Int` as a `Nat`, which no binding can, so
there [`lang::nat_variable`](../../Lang/Components.md#natural-numbers)
states what a `Nat` output brings instead:

```fren
set_option fren.lint.manual_nat "allow" in
pub comp manual_nat_input_written {
    in n: Int
    in k: Int
    pub out m: Int

    assume counts: n >= 0 and k < n

    ensure r: m = n - k
}

pub comp manual_nat_input_fixed {
    in n: Nat
    in k: Int
    pub out m: Int

    assume counts: k < n

    ensure r: m = n - k
}

refine manual_nat_input_sound: manual_nat_input_fixed refines manual_nat_input_written { n }
refine manual_nat_input_complete: manual_nat_input_written refines manual_nat_input_fixed

set_option fren.lint.manual_nat "allow" in
set_option fren.lint.chainable_comparison "allow" in
pub comp manual_nat_output_written {
    in n: Nat
    pub out m: Int

    ensure r: m >= 0 and m <= n
}

pub comp manual_nat_output_fixed {
    in n: Nat
    pub out m: Nat

    ensure r: m <= n
}

refine manual_nat_output_sound: manual_nat_output_fixed refines manual_nat_output_written
```
