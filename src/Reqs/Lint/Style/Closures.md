# Closures

## Closures that only apply a function

`redundant_closure` fires on a [closure](../../Lang/HigherOrder.md#arguments)
given for a function parameter, whose body, without parentheses, applies a
function to the closure's parameters, in order, each once, written as its
name alone, with nothing else: `|x, y| add(x, y)`. The name of a function
`g` given for a function parameter means the closure `|x1, ..., xn| g(x1,
..., xn)`, so the fix writes `add` in place of the closure, which keeps
the meaning. The function is a defined function that is neither generic
nor higher-order, or a function parameter of the enclosing higher-order
function; an uninterpreted function cannot be given by its name
(`F0436`), and a generic function's name gives its type arguments from its
own types, where the closure's body may fix them otherwise. The
function's parameters' and result's types are the function type's, with
none a [subset type](../../Lang/SubsetTypes.md) and no `Nat` where the
function type has an `Int`: otherwise the closure widens, or brings an
obligation, which the name would not. It is Clippy's `redundant_closure`,
also in `style`, `warn`. It is reported at the closure.

`lint::redundant_closure` states when it fires, from the closure's body as
an application and its arguments:

```fren
pub mod lint

-- An argument of the application that is a closure's body, as
-- `redundant_closure` reads it: the closure's parameter at a position,
-- written as its name alone, or any other expression.
pub enum ClosureArg { Param(Int), Other }

-- What a closure's body applies: a defined function that is neither
-- generic nor higher-order, the enclosing function's function parameter,
-- or anything else.
pub enum Callee { Defined, FnParameter, Other }

set_option fren.lint.undecidable "allow" in
pub proc redundant_closure(
    n_params: Int,           -- the closure's parameters
    applies?,                -- its body, without parentheses, applies a function
    callee: Callee,          -- what it applies
    args: Seq<ClosureArg>,   -- the application's arguments, in order
    exact?,                  -- the function's parameters' and result's types are the function type's, none a subset type
): (det fires?) {
    ensure rule: fires? iff (applies? and callee != Callee::Other and exact? and args.len = n_params
        and (forall (k: Int), when 0 <= k < args.len, args[k] = ClosureArg::Param(k)))
}
```

The refinements below check the fix on one example, of one parameter and
of two:

```fren
pub fn apply_twice(f: fn(Int) -> Int, x: Int): Int := f(f(x))

pub fn apply_both(g: fn(Int, Int) -> Int, x: Int): Int := g(x, x)

pub fn bump(n: Int): Int := n + 1

pub fn plus(a: Int, b: Int): Int := a + b

set_option fren.lint.redundant_closure "allow" in
pub proc redundant_closure_written(k: Int): (det v: Int, det w: Int) {
    out v := apply_twice(|y| bump(y), k)
    out w := apply_both(|p, q| plus(p, q), k)
}

pub proc redundant_closure_fixed(k: Int): (det v: Int, det w: Int) {
    out v := apply_twice(bump, k)
    out w := apply_both(plus, k)
}

expect redundant_closure_sound(k: Int) {
    call concrete := redundant_closure_fixed(k)
    refines concrete redundant_closure_written(k)
}
expect redundant_closure_complete(k: Int) {
    call concrete := redundant_closure_written(k)
    refines concrete redundant_closure_fixed(k)
}
```
