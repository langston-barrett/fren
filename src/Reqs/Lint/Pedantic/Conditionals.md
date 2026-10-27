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
branches' root layers and operands as
[written](../Meaning.md#expressions-as-written) in their scopes, and what the
operands mention:

```fren
-- The operator of the branches, as Fren's arithmetic restricts it: `*`,
-- `div` and `mod`, or another.
pub enum SharedOp { Times, Div, Mod, OtherOp }

pub fn shared_op(head: lang::Head): SharedOp := match lang::operator(head) {
    "*" => SharedOp::Times,
    "div" => SharedOp::Div,
    "mod" => SharedOp::Mod,
    _ => SharedOp::OtherOp,
}

pub comp branches_sharing_code {
    use self::SharedOp::{Div, Mod, OtherOp, Times}
    in binders: Set(lang::Id)              -- the binders of the pattern tests in the conditional
    in then_head: lang::Head               -- the head of the `then` branch's root layer
    in else_head: lang::Head               -- the `else` branch's
    in then_left: Scoped                   -- the operands of the `then` branch, as written in their scopes
    in then_right: Scoped
    in else_left: Scoped                   -- the operands of the `else` branch
    in else_right: Scoped
    in condition_mentioned: Set(lang::Mention)  -- what `C` mentions
    in a_mentioned: Set(lang::Mention)     -- what `A` mentions
    in b_mentioned: Set(lang::Mention)     -- what `B` mentions
    in shared_mentioned: Set(lang::Mention)  -- what `X` mentions
    pub det out op: SharedOp := shared_op(then_head)
    pub det out same_op? := then_head = else_head and lang::operator(then_head) != ""
    pub det out shared_left? := then_left = else_left
    pub det out shared_right? := then_right = else_right
    -- What the `if` that the fix moves out, `if C then A else B`, mentions.
    pub det out moved_mentioned: Set(lang::Mention) :=
        lang::mentioned_by(lang::Head::Op("if", ""), condition_mentioned union a_mentioned union b_mentioned)
    pub det out fires?

    -- The product the fix would write, for `*`.
    inst product: lang::linear_product { a_mentioned := moved_mentioned, b_mentioned := shared_mentioned }

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
    expect one_operator: when fires?, then_head = else_head and lang::operator(then_head) != ""
    expect no_divisor: when fires? and op in {Div, Mod}, not shared_left?

    cover other: fires? and op = OtherOp
    cover divided: fires? and op = Div
}
```

Where it fires, the two copies of `X` have the same value in one
environment. Here `p` and `q` are their root layers:

```fren
expect branches_sharing_value: forall (b: branches_sharing_code) (p q: lang::node),
    when b.fires? and p.env = q.env
    and p.head = written_head(if b.shared_left? then b.then_left else b.then_right)
    and p.values = written_values(p.env, if b.shared_left? then b.then_left else b.then_right)
    and q.head = written_head(if b.shared_left? then b.else_left else b.else_right)
    and q.values = written_values(q.env, if b.shared_left? then b.else_left else b.else_right),
    p.value = q.value
```

The refinements check both forms, on integers, with `-`, which is not
commutative, and on `Bool`s, with `and` and `or`, whose operands are
guarded:

```fren
set_option fren.lint.branches_sharing_code "allow" in
pub comp branches_sharing_code_written {
    in c?
    in a: Int
    in b: Int
    in x: Int
    in p?
    in q?
    in y?
    pub det out right: Int := if c? then a - x else b - x
    pub det out left: Int := if c? then x - a else x - b
    pub det out right_and? := if c? then p? and y? else q? and y?
    pub det out left_or? := if c? then y? or p? else y? or q?
}

pub comp branches_sharing_code_fixed {
    in c?
    in a: Int
    in b: Int
    in x: Int
    in p?
    in q?
    in y?
    pub det out right: Int := (if c? then a else b) - x
    pub det out left: Int := x - (if c? then a else b)
    pub det out right_and? := (if c? then p? else q?) and y?
    pub det out left_or? := y? or (if c? then p? else q?)
}

refine branches_sharing_code_sound: branches_sharing_code_fixed refines branches_sharing_code_written
refine branches_sharing_code_complete: branches_sharing_code_written refines branches_sharing_code_fixed
```
