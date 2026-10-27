# Global expectations

A procedure's [expectation](Procedures.md#members) is a claim about each of
its behaviours separately. A global expectation is a claim about procedures
as a whole: it can relate several behaviours of one procedure, or behaviours
of different procedures.

```
expectation := "expect" IDENT ":" ["forall" binder+ ","] top
binder      := "(" DECL+ ":" type ")"
```

`expect n: forall (a b: c) (d: e), E` claims that `E` holds for any two
behaviours `a` and `b` of the procedure `c` and any behaviour `d` of `e`.
Each name a binder introduces stands for a behaviour of its procedure, with
its own inputs, chosen freely: the binders share no variables, and nothing
gives their inputs. Within `E`, `a.x` refers to the variable `x` of `a`, as
for a [call](Calls.md#call-variables), so only the procedure's
parameters and results can be mentioned: `inst::mention` applies, with
`E` as a guarantee.

`E` may end with a [`where` clause](Let.md), whose definitions may
mention the binders: `forall (a b: c), a.x <= b.x where ...`.

A binder whose type is a path that names a procedure ranges over its
behaviours; any other binder ranges over the values of its type, as a
[quantifier's](Quantifiers.md#global-expectations) does, and one `forall`
may have both: `expect n: forall (a: c) (m: Method), E` claims that `E`
holds for every behaviour `a` of `c` and every value `m` of `Method`. The
binders over values are a quantifier around `E`, with any `where` clause,
whatever their order among the others, and follow its rules: their types
must be finite, they have at most 256 instances, and they are named and
scoped as a quantifier's bound names. Being a quantifier, they leave the
expectation without a [trigger](Procedures.md#triggers). The rest of this
chapter is about the binders over behaviours.

Without `forall`, or with binders over values alone, the expectation
mentions no variables, and is a claim about [constants](Items.md#constants),
such as `expect sane: MIN_TEMP < MAX_TEMP`.

The names a global expectation introduces are distinct from each other, and
are named like calls. Like a call's, a binder's name may
[shadow](Procedures.md#shadowing) a constant, a function or a variant of
the module, written with `!`, as in `forall (RATE!: c)`: in `E`, `RATE.x`
is then the binder's variable, not a field of the constant. Its own name
is an item in the current module, so it is distinct from the module's
other items, but nothing can refer to it. Each procedure a binder names
must be declared, and visible, before the global expectation. A binder's
path that names neither a procedure nor a type is an error.

## Example

`band` classifies a temperature (see [Calls](Calls.md#example)):

```
pub proc band(temp: Int, target: Int): (too_cold?, too_hot?) {
  ensure cold: too_cold? iff temp < target - 2
  ensure hot: too_hot? iff temp > target + 2
}

expect colder_is_cold: forall (a b: band),
  when a.target = b.target and a.temp <= b.temp and b.too_cold?, a.too_cold?
```

`colder_is_cold` says that `band` is monotone: for the same target, a lower
temperature is at least as cold. It relates two behaviours of `band`, so it
cannot be an expectation of `band` itself. Since the binders share no
inputs, the condition says which pairs of behaviours the claim is about.

A global expectation can also say that two procedures agree. If
`fast_band` is meant to classify temperatures as `band` does:

```
expect same_band: forall (f: fast_band) (b: band),
  when f.temp = b.temp and f.target = b.target,
  (f.too_cold? iff b.too_cold?) and (f.too_hot? iff b.too_hot?)
```

## Meaning

Let `M_c(y)` be the [meaning](Procedures.md#meaning) of a procedure `c`
over its variables `y`: the conjunction of its assumptions, its
guarantees, and the constraints of its calls. A global expectation
with binders `w_1: c_1`, ..., `w_n: c_n` and body `E` holds if

  ∀ y_1 ... y_n. M_c_1(y_1) ∧ ... ∧ M_c_n(y_n) ⇒ E(y_1, ..., y_n)

All the binders share one [interpretation](Procedures.md#interpretations)
of the spec's abstract types and functions, and the global expectation
must hold under every interpretation: so `forall (a b: c), when a.x =
b.x, f(a.x) = f(b.x)` holds for any function `f`.
Every variable of a binder is universally quantified, so the body may
apply functions to binders' outputs as well as their inputs.

Each binder's assumptions are among the hypotheses, not obligations: a
behaviour of a procedure is one in which its assumptions hold. So unlike a
call's, a binder's inputs need satisfy nothing, and there is no
[call check](../Check.md#call-assumptions) for them.

A global expectation constrains nothing. It is not a procedure, and has no
[evidence](../Trace.md). The [checks](../Check.md#global-expectations)
confirm it.
