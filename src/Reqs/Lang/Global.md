# Global expectations

A component's [expectation](Components.md#members) is a claim about each of
its behaviours separately. A global expectation is a claim about components
as a whole: it can relate several behaviours of one component, or behaviours
of different components.

```
expectation := "expect" IDENT ":" ["forall" binder+ ","] expr
binder      := "(" DECL+ ":" path ")"
```

`expect n: forall (a b: c) (d: e), E` claims that `E` holds for any two
behaviours `a` and `b` of the component `c` and any behaviour `d` of `e`.
Each name a binder introduces stands for a behaviour of its component, with
its own inputs, chosen freely: the binders share no variables, and nothing
binds their inputs. Within `E`, `a.x` refers to the variable `x` of `a`, as
for an [instance](Instances.md#instance-variables), so only the component's
inputs and public outputs can be mentioned: `inst::mention` applies, with
`E` as a requirement.

Without `forall`, the expectation mentions no variables, and is a claim
about [constants](Items.md#constants), such as `expect sane: MIN_TEMP <
MAX_TEMP`.

The names a global expectation introduces are distinct from each other, and
are named like instances. Like an instance's, a binder's name may
[shadow](Components.md#shadowing) a constant, a function or a variant of
the module, written with `!`, as in `forall (RATE!: c)`: in `E`, `RATE.x`
is then the binder's variable, not a field of the constant. Its own name is an item in the current module, so
it is distinct from the module's other items, but nothing can refer to it.
Each component a binder names must be declared, and visible, before the
global expectation.

## Example

`band` classifies a temperature (see [Instances](Instances.md#example)):

```
pub comp band {
  in temp: Int
  in target: Int
  pub out too_cold?
  pub out too_hot?

  req cold: too_cold? iff temp < target - 2
  req hot: too_hot? iff temp > target + 2
}

expect colder_is_cold: forall (a b: band),
  when a.target = b.target and a.temp <= b.temp and b.too_cold?, a.too_cold?
```

`colder_is_cold` says that `band` is monotone: for the same target, a lower
temperature is at least as cold. It relates two behaviours of `band`, so it
cannot be an expectation of `band` itself. Since the binders share no
inputs, the condition says which pairs of behaviours the claim is about.

A global expectation can also say that two components agree. If
`fast_band` is meant to classify temperatures as `band` does:

```
expect same_band: forall (f: fast_band) (b: band),
  when f.temp = b.temp and f.target = b.target,
  (f.too_cold? iff b.too_cold?) and (f.too_hot? iff b.too_hot?)
```

## Meaning

Let `M_c(y)` be the [meaning](Components.md#meaning) of a component `c`
over its variables `y`: the conjunction of its assumptions, its
requirements, and the constraints of its instances. A global expectation
with binders `w_1: c_1`, ..., `w_n: c_n` and body `E` holds if

  ∀ y_1 ... y_n. M_c_1(y_1) ∧ ... ∧ M_c_n(y_n) ⇒ E(y_1, ..., y_n)

All the binders share one [interpretation](Components.md#interpretations)
of the spec's abstract types and functions, and the global expectation
must hold under every interpretation: so `forall (a b: c), when a.x =
b.x, f(a.x) = f(b.x)` holds for any function `f`.
Every variable of a binder is universally quantified, so the body may
apply functions to binders' outputs as well as their inputs.

Each binder's assumptions are among the hypotheses, not obligations: a
behaviour of a component is one in which its assumptions hold. So unlike an
instance's, a binder's inputs need satisfy nothing, and there is no
[instance check](../Check.md#instance-assumptions) for them.

A global expectation constrains nothing. It is not a component, and has no
[evidence](../Trace.md). The [checks](../Check.md#global-expectations)
confirm it.
