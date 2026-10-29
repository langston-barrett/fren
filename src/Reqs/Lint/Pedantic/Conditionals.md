# Conditionals

This lint of the `pedantic` group looks at the branches of a conditional.

```fren
pub mod lint
```

## Branches sharing code

`branches_sharing_code`, `allow` by default, fires on `if C then A op X
else B op X`, where `op` is one binary operator in both branches and `X`
is written the same in both, and on its mirror, `if C then X op A else X
op B`. The fix moves `X` out of the `if`: `(if C then A else B) op X`, or
`X op (if C then A else B)`. The `if` is in parentheses, as
`lang::operand` requires of a conditional operand, and the whole is in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes); `A`
and `B` keep the parentheses they are written with. If both operands of
the branches are written the same, so are the branches, which
[`same_branches`](../Suspicious/Expressions.md#branches-written-the-same)
reports, and this lint does not fire. Nor does it fire where the fix would
be outside the arithmetic that Fren accepts. For `*`, that is where
[`lang::linear_product`](../../Lang/Expressions.md#linear-arithmetic) rejects
the product of the `if` it moves out with `X`: where `X` mentions a
variable or an uninterpreted function, and so does the `if`, which
mentions what `C`, `A` and `B` do (see
[Mentions](../../Lang/Expressions.md#mentions)): `if a? then 3 * x
else 2 * x` would become `(if a? then 3 else 2) * x`, a product of two
operands that mention variables, but `if a? then x * 2 else y * 2` becomes
`(if a? then x else y) * 2`. For `div` and `mod`, it is where `X` is on
the left, since the `if` would be the divisor, which must be a literal or
a constant (see [Division and remainder](../../Lang/Expressions.md#division-and-remainder)): `if a? then
x div 2 else y div 2` becomes `(if a? then x else y) div 2`, but `if a?
then x div 2 else x div 3` is left as it is. Its Clippy counterpart,
of the same name, is in `nursery`.

The fix keeps the meaning: an operator's value depends only on the values
of its operands, and the `if` picks the value of `A` or of `B` as before.
The two copies of `X`, written the same, have the same value, by
[`written_same`](../Meaning.md#expressions-as-written), so one copy outside the
`if` has the value of whichever was evaluated. It keeps the guards. `X` is
guarded by `C` in one branch and by `not C` in the other, so it is
evaluated wherever the conditional is; in the fix it is evaluated there
too. Under `and` and `or`, an `X` on the right is also guarded by the left
operand, `A` under `C` and `B` under `not C`, and in the fix by `if C then
A else B`, which holds exactly where one of those does. `A` and `B` keep
their guards, `C` and `not C`, and under `and` and `or`, with `X` on the
left, `X` as well. Where a pattern test in the conditional binds names, it
does not fire: the branches see different binders (see
[`lang::test_scope`](../../Lang/Expressions.md#pattern-tests)), so in `if r is
Reply::Value(v!) then 1 + v else 2 + v` the two `v`s are the payload and
the variable `v`, and moving one out of the `if` would change which is
meant. `lint::branches_sharing_code` states when it fires, from the
branches' operators, as written, and operands as
[written](../Meaning.md#expressions-as-written) in their scopes, and what the
operands mention:

```fren
-- The operator of the branches, as Fren's arithmetic restricts it: `*`,
-- `div` and `mod`, or another.
pub enum SharedOp { Times, Div, Mod, OtherOp }

pub fn shared_op(op: lang::Id): SharedOp := match op {
    "*" => SharedOp::Times,
    "div" => SharedOp::Div,
    "mod" => SharedOp::Mod,
    _ => SharedOp::OtherOp,
}

pub proc branches_sharing_code(
    binders: Set<lang::Id>,                -- the binders of the pattern tests in the conditional
    then_op: lang::Id,                     -- the operator of the `then` branch, as written, or `""` for none
    else_op: lang::Id,                     -- the `else` branch's
    then_left: Scoped,                     -- the operands of the `then` branch, as written in their scopes
    then_right: Scoped,
    else_left: Scoped,                     -- the operands of the `else` branch
    else_right: Scoped,
    condition_mentioned: Set<lang::Mention>,    -- what `C` mentions
    a_mentioned: Set<lang::Mention>,       -- what `A` mentions
    b_mentioned: Set<lang::Mention>,       -- what `B` mentions
    shared_mentioned: Set<lang::Mention>,    -- what `X` mentions
): (
    det op: SharedOp,
    det same_op?,
    det shared_left?,
    det shared_right?,
    det moved_mentioned: Set<lang::Mention>,
    det fires?,
) {
    use self::SharedOp::{Div, Mod, OtherOp, Times}
    out op := shared_op(then_op)
    out same_op? := then_op = else_op and then_op != ""
    out shared_left? := then_left = else_left
    out shared_right? := then_right = else_right
    -- What the `if` that the fix moves out, `if C then A else B`, mentions.
    out moved_mentioned :=
        lang::mentioned_by(lang::ExprKind::Compound, condition_mentioned union a_mentioned union b_mentioned)

    -- The product the fix would write, for `*`.
    call product := lang::linear_product(moved_mentioned, shared_mentioned)

    ensure rule: fires? iff (binders = {} and same_op? and shared_left? != shared_right? and not match op {
        Times => not product.accepted?,
        Div | Mod => shared_left?,
        OtherOp => false,
    })

    expect same_branches: when shared_left? and shared_right?, not fires?
    expect linear: when fires? and op = Times, moved_mentioned = {} or shared_mentioned = {}
    -- Never across binders, and the fix writes one binary operator, whose
    -- divisor is never the `if`.
    expect no_binders: when fires?, binders = {}
    expect one_operator: when fires?, then_op = else_op and then_op != ""
    expect no_divisor: when fires? and op in {Div, Mod}, not shared_left?

    cover other: fires? and op = OtherOp
    cover divided: fires? and op = Div
}
```

Where it fires, the two copies of `X` have the same value in one
environment:

```fren
expect branches_sharing_value(
    b_binders: Set<lang::Id>,
    b_then_op: lang::Id,
    b_else_op: lang::Id,
    b_then_left: Scoped,
    b_then_right: Scoped,
    b_else_left: Scoped,
    b_else_right: Scoped,
    b_condition_mentioned: Set<lang::Mention>,
    b_a_mentioned: Set<lang::Mention>,
    b_b_mentioned: Set<lang::Mention>,
    b_shared_mentioned: Set<lang::Mention>,
    i: lang::Interp,
    env: lang::Env,
) {
    call b := branches_sharing_code(b_binders, b_then_op, b_else_op, b_then_left, b_then_right, b_else_left, b_else_right, b_condition_mentioned, b_a_mentioned, b_b_mentioned, b_shared_mentioned)
    expect branches_sharing_value: when b.fires?,
        lang::eval(i, env, written(if b.shared_left? then b.then_left else b.then_right))
        = lang::eval(i, env, written(if b.shared_left? then b.else_left else b.else_right))
}
```

The refinements check both forms, on integers, with `-`, which is not
commutative, and on `Bool`s, with `and` and `or`, whose operands are
guarded:

```fren
set_option fren.lint.branches_sharing_code "allow" in
pub proc branches_sharing_code_written(c?, a: Int, b: Int, x: Int, p?, q?, y?): (
    det right: Int,
    det left: Int,
    det right_and?,
    det left_or?,
) {
    out right := if c? then a - x else b - x
    out left := if c? then x - a else x - b
    out right_and? := if c? then p? and y? else q? and y?
    out left_or? := if c? then y? or p? else y? or q?
}

pub proc branches_sharing_code_fixed(c?, a: Int, b: Int, x: Int, p?, q?, y?): (
    det right: Int,
    det left: Int,
    det right_and?,
    det left_or?,
) {
    out right := (if c? then a else b) - x
    out left := x - (if c? then a else b)
    out right_and? := (if c? then p? else q?) and y?
    out left_or? := y? or (if c? then p? else q?)
}

expect branches_sharing_code_sound(c?, a: Int, b: Int, x: Int, p?, q?, y?) {
    call concrete := branches_sharing_code_fixed(c?, a, b, x, p?, q?, y?)
    refines concrete branches_sharing_code_written(c?, a, b, x, p?, q?, y?)
}
expect branches_sharing_code_complete(c?, a: Int, b: Int, x: Int, p?, q?, y?) {
    call concrete := branches_sharing_code_written(c?, a, b, x, p?, q?, y?)
    refines concrete branches_sharing_code_fixed(c?, a, b, x, p?, q?, y?)
}
```
