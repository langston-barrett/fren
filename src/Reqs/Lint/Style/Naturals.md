# Natural numbers

This lint of the `style` group finds an `Int` that a constraint makes a
`Nat`.

```fren
pub mod lint
```

## Integers kept at least 0

A [`Nat`](../../Lang/Types.md#natural-numbers) input brings the assumption
that it is at least 0 with its type, and a `Nat` output, a result or an
`exists` or `let` variable, the guarantee (see [Natural
numbers](../../Lang/Procedures.md#natural-numbers)). `manual_nat` fires on
an input of a procedure declared an `Int`, one of whose assumptions has
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
constraint if nothing else is left of it. It changes the procedure's
interface, which a call or a refinement in another file may rely
on, as below, so it is the writer's to make. Of a procedure,
a bound is in an assumption only for an input, which an assumption alone
may mention, and in a guarantee for an output, so the `Nat` brings what
it removes. Within the procedure, the fix keeps what the spec means, and the guards: a
conjunct after the bound was guarded by it, and is by the `Nat`'s
constraint instead, which every query of the procedure has among its
hypotheses (see [Checks](../../Check.md)). Each expression keeps its type
but those that the variable's widening makes `Nat`s, and a `Nat` is
accepted wherever an `Int` is, so the procedure stays well typed. Its
interface changes, though, and an `Int` is never narrowed: a call
must then give the variable a `Nat` argument, and a refinement that reads it by
name must read it as a `Nat` input or give it as a `Nat` output. A spec
whose call gives it an `Int`, such as `n - k` where an assumption
of the called procedure makes that at least 0, relies on the
assumption, which the [call check](../../Check.md#call-assumptions)
confirms, and cannot have the `Nat` instead. So the lint does not fire on
a variable that a call in the same file gives an `Int`, nor on
one that a refinement in it binds to an `Int`, reads by name as an `Int`
input of the abstract procedure, for the concrete one's input, or reads
by name from an `Int` output of the concrete procedure, for the abstract
one's output. It waits for the end
of the file to know. A call or a refinement in another file is not
seen, which is why `fren fix` leaves the fix to the writer, and the
message says that a call must then give a `Nat`. It is
`warn` by default, as most such inputs are counts or positions, which
are `Nat`s, and nothing but the variable's uses decides that. Clippy has
no lint like it.

`lint::manual_nat` states where it fires for one variable, over the
conjuncts of the procedure's assumptions and guarantees, in order, and
the types that the file's calls, refinements and `impl`s give the
variable. `bounds?` says that a conjunct is a bound of the variable that
the `Nat` would bring: the variable is declared an `Int`, the conjunct
says that it is at least `0`, as its written operands show, and it is an
assumption of an input or a guarantee of an output that is not defined.
The lint is reported at the first bound, unless the file gives the
variable an `Int`. `k` is any position, so the guarantee `first` holds of
every position, and together the guarantees make `position` the least
bound. Over sequences of records the solver is incomplete, so the
procedure's checks are by testing:

```fren
pub enum NatRole { Input, Output, DefinedOutput }

pub enum BoundOp { AtLeast, AtMost, OtherOp }  -- `>=`, `<=`, or another comparison

pub struct NatVariable { name: String, role: NatRole, int? }

-- A conjunct: whether its constraint is an assumption, its comparison, and its operands' written forms.
pub struct NatConjunct { assumption?, op: BoundOp, left: String, right: String }

pub enum Given { Integer, Natural }  -- `Int` or `Nat`

pub fn bounds?(v: NatVariable, c: NatConjunct) := v.int?
    and (match c.op { BoundOp::AtLeast => c.left = v.name and c.right = "0",
    BoundOp::AtMost => c.left = "0" and c.right = v.name, BoundOp::OtherOp => false })
    and (match v.role { NatRole::Input => c.assumption?, NatRole::Output => not c.assumption?,
    NatRole::DefinedOutput => false })

set_option fren.evidence "random" in
set_option fren.lint.undecidable "allow" in
pub proc manual_nat(
    var: NatVariable,
    conjuncts: Seq<NatConjunct>,    -- the conjuncts of the assumptions and guarantees, in order
    uses: Seq<Given>,    -- the types that the file's calls, refinements and `impl`s give it
    k: Int,              -- any position in `conjuncts`
): (
    position: Int,         -- of the bound it is reported at, or -1 where it does not fire
) {
    ensure kept: when Given::Integer in uses, position = -1
    ensure found: when position != -1, 0 <= position < conjuncts.len and bounds?(var, conjuncts[position])
    ensure first: unless Given::Integer in uses,
        when 0 <= k < conjuncts.len and bounds?(var, conjuncts[k]), 0 <= position <= k
}
```

The [refinements](../../Lang/Refinement.md) below check the fix of an input,
each way, and of an output, one way: procedures as written, as fixed, and
a refinement between them, so that the solver checks that they agree for
every value of the inputs. A refinement whose abstract input is an `Int`
binds it to the concrete `Nat`, which widens. The other way for an
output would read the written `Int` as a `Nat`, which no binding can, so
there [`lang::nat_variable`](../../Lang/Procedures.md#natural-numbers)
states what a `Nat` output brings instead:

```fren
set_option fren.lint.manual_nat "allow" in
pub proc manual_nat_input_written(n: Int, k: Int): (m: Int) {
    assume counts: n >= 0 and k < n

    ensure r: m = n - k
}

pub proc manual_nat_input_fixed(n: Nat, k: Int): (m: Int) {
    assume counts: k < n

    ensure r: m = n - k
}

expect manual_nat_input_sound(n: Nat, k: Int) {
    assume spec_counts: (n) >= 0 and (k) < (n)
    call concrete := manual_nat_input_fixed(n, k)
    refines concrete manual_nat_input_written(n, k)
}
expect manual_nat_input_complete(n: Nat, k: Int) {
    assume spec_counts: (k) < (n)
    call concrete := manual_nat_input_written(n, k)
    refines concrete manual_nat_input_fixed(n, k)
}

set_option fren.lint.manual_nat "allow" in
set_option fren.lint.chainable_comparison "allow" in
pub proc manual_nat_output_written(n: Nat): (m: Int) {
    ensure r: m >= 0 and m <= n
}

pub proc manual_nat_output_fixed(n: Nat): (m: Nat) {
    ensure r: m <= n
}

expect manual_nat_output_sound(n: Nat) {
    call concrete := manual_nat_output_fixed(n)
    refines concrete manual_nat_output_written(n)
}
```
