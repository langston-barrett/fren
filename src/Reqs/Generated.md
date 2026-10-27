# Generated Lean declarations

In Lean, each enumeration, record, defined function, constant, component and
global expectation becomes ordinary Lean declarations,
so that Lean code can use a spec. An item at the Fren path `a::b::c` gets
the Lean name `Fren.Generated.a.b.c`, prefixed by the current Lean
namespace, and Lean code names it `a.b.c` (see [Names](#names)). Below,
`p` stands for that name.

## Names

The declarations generated for an item are in a namespace of their own,
`Fren.Generated`, under the current Lean namespace: the item at the path
`a::b::c`, declared where the current Lean namespace is `N`, gets the
Lean name `N.Fren.Generated.a.b.c`, and every other declaration generated
for it, such as a variant's constructor or a component's guarantee, a name
under that one. Lean declares nothing else in `Fren.Generated`, so no
item's Lean name is one of Lean's own: `enum Option` at the root module is
`Fren.Generated.Option`, apart from Lean's `Option`, and both front ends
accept it, as they accept `struct List`. Messages, notes and witnesses
name an item by its Fren path, never by its Lean name, so the two front
ends' messages agree.

`generated::lean_name` states the name over the components of names, which
are strings: those of the current Lean namespace, and the segments of the
item's path, which is the full path from the root module. Its rules join
sequences, which is outside the [decidable
core](Lang/Decidability.md#sequences), so they opt out:

```fren
pub mod generated

-- The namespace, under the current Lean namespace, of every generated declaration.
pub const NAMESPACE: Seq<String> := ["Fren", "Generated"]

set_option fren.lint.undecidable "allow" in
pub comp lean_name {
    in current: Seq<String>      -- the current Lean namespace's components, [] at the root
    in path: Seq<String>         -- the item's path's segments

    assume item: path != []
    pub out name: Seq<String> := current ++ NAMESPACE ++ path

    expect length: name.len = current.len + 2 + path.len
    expect starts_in_namespace: name.starts_with?(current ++ NAMESPACE)
    expect ends_in_path: name.ends_with?(path)
    expect root_option: when current = [] and path = ["Option"], name = ["Fren", "Generated", "Option"]
    expect never_leans: when current = [] and path = ["Option"], name != ["Option"]
    expect in_module: when current = [] and path = ["check", "Verdict"], name = ["Fren", "Generated", "check", "Verdict"]
    expect in_lean_namespace: when current = ["FrenTest", "Ui"] and path = ["Mode"],
        name = ["FrenTest", "Ui", "Fren", "Generated", "Mode"]
}

set_option fren.lint.undecidable "allow" in
expect distinct_paths: forall (a b: lean_name),
    when a.current = b.current and a.path != b.path, a.name != b.name
```

`generated::distinct_paths` claims that two items never share a Lean name:
in one Lean namespace, distinct paths have distinct names.

Wherever `Fren.Lang` is open, so is `Fren.Generated`, under the current
Lean namespace: `open Fren.Lang` opens it too, and so does each Fren
command, if it is not yet open. So Lean code names an item's declarations
by its path, `a.b.c`, such as `climate.Mode.Heat` or `simp [fren_spec,
size]`, and `Fren.Generated.a.b.c` names them anywhere. Where an item's
name is also the name of one of Lean's declarations, as `Option` at the
root module is, the name alone is ambiguous in Lean code where both are
visible: `Fren.Generated.Option` names the item's, and `_root_.Option`
Lean's. The generated declarations name each other by their full Lean
names, so they are never ambiguous. Lean's `#print` and `#check` show a
declaration's full Lean name, `Fren.Generated.a.b.c`.

## Enumerations

An enumeration becomes `inductive p`, with one constructor for each
variant, deriving `DecidableEq`, `Repr` and `Inhabited`. For example,
`climate::Mode` becomes `climate.Mode`, with constructors
`climate.Mode.Off`, `climate.Mode.Heat` and `climate.Mode.Cool`.

A variant with a payload becomes a constructor with one explicit
parameter for each value of its payload, of the Lean type of the
payload's type (see [Components](#components)): `enum Shape { Circle(Int),
Empty }` gives `Shape.Circle : Int → Shape`. A recursive enumeration
becomes a recursive inductive type. The `k`th value of a payload, counted
from 0, is the constructor's parameter `xk`, and is read by the selector
`p.V.xk`, such as `Shape.Circle.x0 : Shape → Int`, which gives `default`
for any other variant. A [`match`](Lang/Expressions.md#matches) becomes
`if`s that test the scrutinee against each arm's pattern, rather than
Lean's own `match`, whose rules for exhaustiveness differ from Fren's: a
variant by comparing the value with the variant built from its own payload,
and then its payload's patterns on the values the selectors read; a literal
by equality; a range by comparisons with its bounds, a constant's by its
value; an or-pattern by the disjunction of its alternatives' tests. Binders
read their values with the selectors. An arm with a guard tests its guard
too, in the same `if`, `if T and C then x else ...`, so that where its
guard fails, the chain falls through to the arms after it, as Fren's
`match` does: Lean's `match` has no guards in term mode. Where no arm is
taken, a `match` whose arms without guards are not exhaustive is
`Fren.Seq.nth ∅ 0`, as a table is below. A [`let`](Lang/Let.md) becomes
Lean's `have`, one for each definition, and so does a `where` clause,
around the expression it follows. A [table](Lang/Expressions.md#tables) becomes `if`s over its rows'
conditions, in order: `table { a => x, b => y, _ => z }` is `if a then x
else if b then y else z`. Without a `_` row, where no row holds, the table
is the index out of range that the solver sees, `Fren.Seq.nth ∅ 0` of the
empty sequence of its type, which is `default`: `table { a => x, b => y }`
is `if a then x else if b then y else Fren.Seq.nth ∅ 0`. That is one
interpretation of the solver's unspecified value of the type, the same for
every such table, as `default` is of an index out of range, so every check
that passes, and every `impl` that the solver proves, holds of the
generated definitions. The checks of a table or a `match` generate
nothing: a table's
completeness is the theorem that the disjunction of its conditions follows
from its guard, the disjointness of two rows that the conjunction of
their conditions, where they are defined, is false under it, and the
reachability of a row or an arm that its own test and the failure of the
tests before it can hold together under it, theorems about its patterns
and guards, which a proof about the generated definitions can state.

Each enumeration whose variants have no payloads also has an instance
`p.instFinite` of `Fren.Finite`, a class whose instances list every value
of a type.

## Generic types

A [generic type](Lang/Generics.md) becomes an inductive type or structure,
as above, with one explicit parameter of type `Type` for each type
parameter, of the same name, and named as any other item's declarations
are (see [Names](#names)): `enum Option<T> { None, Some(T) }` becomes
`inductive Option (T : Type)`, which at the root module is
`Fren.Generated.Option`, apart from Lean's `Option`, with `Option.Some :
{T : Type} → T → Option T`. Deriving `DecidableEq`, `Repr` and `Inhabited` asks the same of
the arguments, which every Fren type has. Its instances are applications,
as `Option Int`, and a construction gives its inferred arguments
explicitly, as `@Option.None Int`, so that Lean infers nothing that Fren
does not. A generic record's constructor is `p.mk!`, rather than
`p.«{}»` (see [Records](#records)), which no field is named, since no
field's name has a `!`: lean-smt qualifies a constructor of a parametric
datatype by its sort, as `(as C (Pair Int Bool))`, where cvc5 finds the
constructor only by a symbol that needs no `|`s. A selector takes the parameters as implicit arguments, with an
`Inhabited` instance of each, for its `default`: `Option.Some.x0 :
{T : Type} → [Inhabited T] → Option T → T`. The solver is given the
inductive type as a parametric datatype (see [Generic
types](Lang/Generics.md#meaning)).

## Records

A record becomes `structure p`, with one field of the same name for each
of its fields, in order, deriving `DecidableEq`, `Repr` and `Inhabited`.
For example, `struct Point { x: Int, y: Int }` becomes `Point`, with
fields `Point.x : Point → Int` and `Point.y`, so that `p.x` in Lean is
`p.x` in Fren. A field whose name ends in `?` keeps it. The constructor
is `p.«{}»`, rather than `p.mk`, which could be a field: a record literal
`Point { x := 1, y := 2 }` becomes `Point.«{}» 1 2`. A [record
update](Lang/Expressions.md#record-updates) `{ q with x := 1 }` becomes
`Point.«{}» 1 (Point.y q)`, which is what Lean's own `{ q with x := 1 }`
means. An updated value that is not a name, and that some field is read
from, is bound once with `let`, so that nested updates grow linearly:
`{ f(q) with x := 1 }` becomes `let r := f q; Point.«{}» 1 (Point.y r)`.

## Newtypes

A [newtype](Lang/Items.md#newtypes) becomes `structure p`, with one field,
`p.«0»`, of the Lean type of its underlying type, and the constructor
`p.mk`, deriving `DecidableEq`, `Repr` and `Inhabited`. For example,
`struct Ms(Int)` becomes `Ms`, with `Ms.mk : Int → Ms` and `Ms.«0» : Ms →
Int`, so that `Ms(5)` is `Ms.mk 5` and `x.0` is `x.«0»`. Since `Ms` is a
structure of its own, Lean too keeps an `Ms` apart from an `Int` and from
other newtypes. A newtype's operators are those of its field: `a < b`,
for an ordered newtype, is `a.«0» < b.«0»`, and `a + b` is `Ms.mk (a.«0» +
b.«0»)`. An [ordered record](Lang/Items.md#ordered-declarations)'s `a <
b` is unfolded, lexicographically, into its fields' comparisons, as `a.x <
b.x ∨ (a.x = b.x ∧ a.y < b.y)`, so that Lean needs no order of its own on
the structure. The solver is
given the structure as a datatype of one constructor, whose values are
those of its field, so the checks have the results that they have in the
`fren` command, where it is its underlying type.

## Abstract types and uninterpreted functions

An [abstract type](Lang/Types.md#abstract-types) or
[uninterpreted function](Lang/Items.md#uninterpreted-functions) generates nothing: its Lean meaning is
given by an [interpretation](Impl.md#interpretations), which may come
later, so the definitions that use it take it as a parameter (see
[Components](#components)). An interpretation generates the definition `p`,
and, for a function with postconditions or whose result type brings a
constraint, the theorem `p.ensures` (see [Contracts](#contracts) and
[Interpretations](Impl.md#interpretations)).

## Defined functions

A [defined function](Lang/Items.md#defined-functions) becomes `def p`, with
one explicit parameter for each of its parameters, of the same name and of
its Lean type, as for variables below, and its body as its value. For
example, `fn double(n: Int): Int := 2 * n` becomes `double : Int → Int`.
Like a component's definitions, it first takes a parameter for each
abstract type it uses: those that its parameter and result types, and its
body, mention.

## Generic functions

A [generic function](Lang/GenericFunctions.md) becomes `def p`, as any
defined function does, whose type parameters are among the abstract types
it uses: each is an explicit parameter of type `Type`, named as the type
parameter, followed by an instance-implicit `Inhabited` instance of it, as
an abstract type's is, after the abstract types declared before the
function. For example, `fn unwrap_or<T>(o: Option<T>, d: T): T := ...`
becomes `unwrap_or : (T : Type) → [Inhabited T] → Option T → T → T`. An
application gives its inferred type arguments explicitly, with their
instances, as `unwrap_or Int x 0`, so that Lean infers nothing that Fren
does not, and the solver sees the body at that instance.

A generic function without a body, as `fn pick<T>(T, T): T`, generates
nothing, as any [uninterpreted function](#abstract-types-and-uninterpreted-functions):
its Lean meaning is a constant whose type takes the type parameters first,
each with its `Inhabited` instance, `pick : (T : Type) → [Inhabited T] → T
→ T → T`, which a component that applies it takes as a parameter, and an
[interpretation](Impl.md#interpretations) gives. An application gives its
type arguments explicitly, as `pick Int x y`, and the solver sees each
instance as an unknown function of its own
(`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).

## Contracts

Each clause `n` of a function's [contract](Lang/Items.md#contracts)
becomes `def p.n : Prop`, with one explicit parameter for each of the
function's parameters, as for a defined function, and the clause as its
value. Like a component's definitions, it first takes a parameter for
each abstract type and function it uses: those that the function's
parameter and result types, and the clause, mention, the function itself
among them if the clause applies it. The checks state a precondition's
obligation at an application, and a postcondition's claim, with these
definitions: the obligation is `p.n` applied to the arguments, and the
claim is that `p.n` holds for all values of the parameters for which each
precondition does. The [postcondition check](Check.md#postconditions) is
trusted from the solver, as every check is, so a defined function's
postconditions are not Lean theorems; an uninterpreted function's are,
of its [interpretation](Impl.md#interpretations): a theorem, or an axiom
where the solver proved them.

## Constants

A constant becomes `def p : T`, where `T` is the Lean type of its type, as
for variables below. For example, `climate::MAX_TARGET` becomes
`climate.MAX_TARGET : Int`. Fren uses the constant's value directly, so
this definition is only for Lean code that uses the spec.

## Components

A component becomes a family of definitions, each a proposition over the
component's variables:

| Definition | Meaning |
|---|---|
| `p.assume.n`, `p.ensure.n`, `p.expect.n`, `p.cover.n` | the assumption, guarantee, expectation or cover goal `n` |
| `p.inst.w` | the instance `w`: its bindings, and the [meaning](Lang/Components.md#meaning) of the instantiated component |
| `p.assumes` | the conjunction of the assumptions |
| `p.ensures` | the conjunction of the guarantees |
| `p.def.d` | the definition of the [defined output](Lang/Components.md#defined-outputs) `d`, as the proposition `d = e` |
| `p.defs` | the conjunction of the definitions |
| `p.out.d` | when the definition of `d` mentions only inputs: its value, as a function of the inputs |

In the assumptions, each defined output is replaced by its definition, so
`p.assumes` never depends on the outputs' parameters. `p.out.d` takes the
parameters for abstract types and functions, as below, and then only the
component's inputs, in order. For example, with `in a: Int` and `out
double: Int := 2 * a`, `p.out.double : Int → Int`, which an implementation
can use as the term for `double`.

The parameters of every definition are the component's variables, in the
order of their declarations, followed by the variables of each instance in
order: those of the instantiated component, including its own instances',
named `w.x`. A variable of type `Bool`, `Int`, `Nat`, `String`, an
enumeration `E` or a record `R`, a newtype among them, has the Lean type
`Bool`, `Int`, `Nat`, `String`, or the inductive or structure for `E` or
`R`, and a `Nat` that
is widened to an `Int` is Lean's `↑n`. A [pattern
type](Lang/Types.md#pattern-types) has its base type's Lean type, and a
type alias that of the type it names, and a field or payload of type `Nat`
is Lean's `Nat`. What pattern types bring is part of the definitions: `p.assumes` starts
with the constraints of the inputs whose types bring one (see
[Components](Lang/Components.md#pattern-types)), in order, and `p.ensures`
with those of the outputs that are not defined, before the assumptions
and guarantees that the spec writes, so that an implementation's
obligation assumes them and proves them. A variable of type `Set<T>` has the
Lean type `Fren.FinSet T'`, where `T'` is that of `T`: a list up to having
the same members, with `∈`, `∪`, `∩`, `\`, `⊆`, `∅`, `{a, b}` and
`Fren.FinSet.card`, each with a `simp` lemma stating it by membership. A
variable of type `Rel<A, B>` has the Lean type `Fren.FinSet (A' × B')`, and
`r join q`, `r.inverse`, `r.closure`, `r.image(s)`, `r.domain` and
`r.range` are `Fren.FinSet.join r q`, `Fren.FinSet.inverse r`, and so on,
each with a `simp` lemma stating it by membership, except `closure`, whose
lemma `Fren.FinSet.mem_closure` states it by `Relation.TransGen`. Where the
type it ranges over is finite, `r.domain` is the image of `r.inverse` under
the set of every value of `B`, and `r.range` the image of `r` under every
value of `A`. A variable of type `Seq<T>` has the Lean type `Fren.Seq T'`,
a wrapper around `List T'`; `[]`, `[a, b]`, `q ++ r` and `x in q` are `∅`,
`Fren.Seq.unit a ++ Fren.Seq.unit b`, `++` and `∈`, `q[i]` is
`Fren.Seq.nth q i`, which is `default` out of range, and each method is the
definition of `Fren.Seq` of its name, with a `simp` lemma that states it by
`List` functions. `default` is one interpretation of an out-of-range
index, so every check that passes holds of it. An abstract type's value
out of range needs an `Inhabited` instance, so a generated definition that
indexes a sequence of an abstract type `T` takes one, `[Inhabited T]`,
after `T`, which an implementation gives from its interpretation of `T`. A
string method is a definition of
`Fren.Str`, over `Int` positions, such as `Fren.Str.len : String → Int`,
whose `@[simp]` lemmas relate it to Lean's `String` functions. `a div k`
and `a mod k` are `a / k` and `a % k` on `Int`, which are Lean's
Euclidean `Int.ediv` and `Int.emod`, by the divisor's value as a numeral:
for a negative divisor `-k`, `a div -k` is `-(a / k)` and `a mod -k` is
`a % k`, which the Euclidean laws make the same, so that the solver always
divides by a numeral, as its linear logics require. The methods of `Int` are conditionals: `x.abs` is
`if x < 0 then -x else x`, `x.min(y)` is `if x ≤ y then x else y`, and
`x.max(y)` is `if x ≥ y then x else y`. A
[chained comparison](Lang/Expressions.md#chained-comparisons), which Lean
does not have, is the conjunction of its comparisons: `a < b <= c` is
`a < b ∧ b ≤ c`, with the same term for `b` in both. A [cardinality
operator](Lang/Expressions.md#cardinality) is the sum of a conditional for
each argument, compared with 1: `exactly_one?(a?, b?)` is `((if a? = true
then 1 else 0) + if b? = true then 1 else 0) = 1`, of type `Int`, and
`at_most_one?` compares with `≤`, with no definition of its own for the
solver to unfold. A [quantifier](Lang/Quantifiers.md) over listed types is
its expansion: `forall (m: Method), m != x` is
`Method.Len ≠ x ∧ Method.Card ≠ x` for `enum Method { Len, Card }`, the body
at each value in the order of [its instances](Lang/Quantifiers.md#meaning),
conjoined by `∧`, or by `∨` for `exists`, with nothing left of the
quantifier: no `∀`, `∃` or `Fintype`. The `∧`s and `∨`s form a balanced
tree, `(a ∧ b) ∧ (c ∧ d)`, so that an expansion of 256 instances is 8 deep,
not 256. Within a [`let` or `where`](Lang/Let.md), an expansion that mentions its
names is a function of them, applied to the locals of their `have`s. An
[unbounded quantifier](Lang/Quantifiers.md#unbounded-quantifiers) is a
`Prop`, Lean's `∀` or `∃` over the Lean type of each bound name of a
type that is not listed, named `x'k` as the solver knows it, with
its bound names of listed types expanded within it: `forall (i: Int),
when 0 <= i < q.len, q[i] > 0` is `∀ (i'0 : Int), 0 ≤ i'0 ∧ i'0 < Fren.Seq.len q →
Fren.Seq.nth q i'0 > 0`. A pattern type's constraint, and a `Nat`'s, are
part of the bound name's type, as `∀ (n'0 : Nat)`, or a hypothesis before
the body for `∀`, and a conjunct for `∃`. Its body has no `have`: the
names of `let`s and `where`s within it are substituted. Where a `Bool`
is needed of it, as the value of a `Bool` variable or function, the
condition of an `if`, or a member of a set, it is decided by
`Classical.propDecidable`, since it has no other `Decidable` instance, as
equality on an abstract type has none; that is why the definitions that
need one are not computable. The checks and implementations read the
propositions, which need no `Decidable` instance.

A component *uses* the abstract types and uninterpreted functions that its
variables' types, its constraints and its bindings mention, those that its
instances' components and the defined functions it applies use, and the
parameter and result types of the functions it uses. Before its variables, every definition of the component takes one
explicit parameter for each abstract type and function it uses, in the
order of their declarations: `(T : Type)` for an abstract type `T`, and for
a function, a Lean function from its parameter types to its result type,
where each abstract type is the parameter for it. A variable of an
abstract type has the parameter for it as its Lean type. For example, with

```
type Name
fn ends_in_q?(Name)

comp c { in n: Name pub out q? ensure r: q? iff ends_in_q?(n) }
```

`c.ensures` has type `(Name : Type) → (Name → Bool) → Name → Bool → Prop`.

For example, `climate.thermostat.ensures` has type `Int → Int → climate.Mode →
Prop`, for `temp`, `target` and `mode`.

## Cover goals

A [cover goal](Lang/Components.md#cover-goals) `n` of a component claims
that some behaviour meets the component and satisfies `p.cover.n`. When
`#fren_check` finds a witness of it, and the component uses no abstract
types or functions, it adds the theorem

```
p.cover.n.met : ∃ x₁ … xₖ, M x⃗ ∧ p.cover.n x⃗
```

where `x⃗` are the parameters of the component's definitions, as above,
and `M` is what an implementation's obligation assumes and proves of
them: `p.defs` (if there are defined outputs), `p.assumes`, `p.ensures` and
`p.inst.w` for each instance `w`. Its proof gives the witness's values
for `x⃗`, and `decide` proves the rest, in Lean's kernel. A variable
whose value the model leaves out is given `default`. If a value cannot be
written as a Lean term, or `decide` does not prove the statement, no
theorem is added, and the goal still passes, on the solver's word, as the
other checks do. A component that uses abstract types or functions gets no
theorem: the check finds a witness under *some* interpretation, which an
`∃` over the variables alone cannot state.

## Global expectations

A global expectation becomes `def p : Prop`: for all values of the
binders' variables, if the [meaning](Lang/Global.md#meaning) of each
binder's component holds, then so does the body. Each binder's variables
are named `w.x`. Like a component's definitions, it first takes a
parameter for each abstract type and function it uses: those that its
body mentions and that its binders' components use.

## Proofs

The definitions are reducible, so that `decide` and type-class instances see
through them. They are also in the simp set `fren_spec`, so `simp
[fren_spec]` unfolds them. Where `Fren.Lang` is open, `decide` also decides
`∀` and `∃` over `Bool`, enumerations, and any type with a `Fren.Finite`
instance.

These declarations need only `import Fren.Spec` (see [Lean
embedding](Lean.md#libraries)).
