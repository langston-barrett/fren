# Structural recursion

A first-order [defined function](Items.md#defined-functions) that is not
[generic](GenericFunctions.md) may apply itself in its own body, as a
*structural recursion* over a recursive enumeration: one of its
parameters, the *decreasing* one, is the same in every application, and
there each argument is a binder that a [`match`](Expressions.md#matches)
arm bound from a payload of that parameter, directly or nested. Each
application is then to a value smaller than the parameter's, so every
application has a value:

```text
pub enum Tree { Leaf(Int), Node(Tree, Tree) }

pub fn leaves(t: Tree): Int := match t {
    Tree::Leaf(_) => 1,
    Tree::Node(l, r) => leaves(l) + leaves(r),
}
```

A binder is bound from a payload of a parameter `p` when it is a binder of
a `match` arm's pattern on `p`, within a variant's payload, as `l` and `r`
are above, however deeply the pattern nests; when it is such a binder of a
`match` on a binder already bound from a payload of `p`; or when it is a
binder of the whole of such a binder, as `m` in `match l { m => ... }`. A
binder of a pattern test (`is`), a `let`'s or a `where`'s name is not,
whatever its value. The other arguments of an application are any
expressions.

The decreasing parameter is the first, in order, at which every
application's argument is bound from a payload of that parameter, so a
function with several parameters of the recursive enumeration recurses on
the first that works for all of its applications. There is no other
recursion: an application whose arguments decrease at no parameter that
all the others decrease at, an application within a
[closure](HigherOrder.md#closures), or the function's name given for a
function parameter, is an error (`F0447`), at the first application by
which every parameter has failed, saying why its argument is not a payload
of the parameter there: the parameter itself, another name, or another
expression. A generic or higher-order function is never recursive
(`F0331`), and mutual recursion cannot be written, since a function is not
in scope in the bodies of the functions declared before it. For now, a
structural recursion is recognized and then reported as not yet supported
(`F0448`).

`lang::structural_recursion` states this, over the function's uses of
itself in its body, in the order they are written, each with where its
arguments come from:

```fren
-- Where a recursive application's argument at one position comes from,
-- relative to the function's parameter at that position: a binder bound
-- from a payload of it, the parameter itself, another name, or another
-- expression.
pub enum RecArg { Payload, Itself, Name, Expr }

-- How the function is used in its own body: applied, applied within a
-- closure, or given for a function parameter without being applied.
pub enum RecForm { Applied, InClosure, Passed }

-- A use of the function: its form, and an application's arguments, in order.
pub struct RecUse { form: RecForm, args: Seq<RecArg> }

-- Not recursive; a structural recursion, decreasing at the parameter at a
-- position; or not one, at a use, reporting the argument at a position.
pub enum Recursion { NotRecursive, Structural(Int), NotStructural(Int, Int) }

-- Whether the use `u` is an application whose argument at position `i` is
-- bound from a payload of the parameter there.
pub fn decreases_at?(u: RecUse, i: Int) :=
    u.form = RecForm::Applied and 0 <= i < u.args.len and u.args[i] = RecArg::Payload

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc structural_recursion(
    n_params: Int,         -- the function's number of parameters
    uses: Seq<RecUse>,     -- its uses of itself in its body, in order
): (det verdict: Recursion) {
    use self::Recursion::{NotRecursive, NotStructural, Structural}
    assume params: n_params >= 1

    ensure none: when uses = [], verdict = NotRecursive
    -- The first position at which every use decreases.
    ensure structural: forall (i: Int), when 0 <= i < n_params and uses != []
        and (forall (k: Int), when 0 <= k < uses.len, decreases_at?(uses[k], i))
        and (forall (h: Int), when 0 <= h < i, exists (k: Int), 0 <= k < uses.len and not decreases_at?(uses[k], h)),
        verdict = Structural(i)
    -- Otherwise the first use by which every position has failed, and the
    -- first position that fails first there.
    ensure not_structural: forall (k: Int) (i: Int), when 0 <= k < uses.len and 0 <= i < n_params
        and not decreases_at?(uses[k], i)
        and (forall (j: Int), when 0 <= j < k, decreases_at?(uses[j], i))
        and (forall (h: Int), when 0 <= h < n_params, exists (j: Int), 0 <= j <= k and not decreases_at?(uses[j], h))
        and (forall (h: Int), when 0 <= h < i, exists (j: Int), 0 <= j < k and not decreases_at?(uses[j], h)),
        verdict = NotStructural(k, i)
}
```

Both front ends read the body into these uses as they elaborate it: a use
when they reach the function's name, before its arguments, so an
application within another's arguments comes after it.

The Lean-hosted front end checks this chapter's procedure by name, since
no `#fren_check` of its Lean file comes after it:

```fren
#fren_check structural_recursion
```
