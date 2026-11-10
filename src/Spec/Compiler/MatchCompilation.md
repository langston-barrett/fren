# Match compilation

This chapter covers compilation of pattern matches.

## Arm selection

Lowering builds a chain of guards over the arms in written order and takes the
last arm as the fallback, so that it needs no guard of its own. For a
constructor that has an arm, the chain runs the first arm written for it,
which is the arm that
[`select`](../Language/Patterns.md#r-patterns.matching.select) names. For a
constructor that has no arm, the chain runs its fallback, where `select`
names none, so the two agree only on a match whose arms
[cover](../Language/Patterns.md#r-patterns.coverage.covered) the constructor.
`select` in turn is the selection of the dynamic semantics when
[no arm is repeated](../Language/Patterns.md#r-patterns.matching.dynamics),
and can differ from it for a constructor that has a repeated arm.

r[match.lowering.selection] spec::lowering::lowering_selection::agrees
For an [admitted](../Language/Patterns.md#r-patterns.coverage.admitted)
match and a constructor of its scrutinee's enumeration, the arm that the
lowered guard chain runs is the arm `select` names. The claim is made for no
other match and no other constructor. `lowering_pick` stands for the arm
that the chain runs and has no interpretation yet, so the procedure's result
says where the two agree, and that it is `true` for every such match and
constructor is the open claim.

```fren
pub mod spec::lowering

use spec::names::{ArmF, Ctx, ItemId, ItemKind, Symb, Ty, entry, symb_ok?}
use spec::patterns::{match_admitted?, select}
use spec::surface::Snoc
use spec::types::Typing

pub fn lowering_pick(Snoc<ArmF<Typing>>, ItemId): Option<ArmF<Typing>>

set_option fren.evidence "random" in
pub proc lowering_selection(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty,
    owner: ItemId,
    constructor: ItemId,
): (holds?) {
    ensure agrees: when holds? and symb_ok?(symb) and match_admitted?(symb, ctx, scrutinee, arms, ty)
        and scrutinee.ty = Ty::Nominal(owner)
        and entry(symb, constructor) = Option::Some(ItemKind::Constructor(owner)),
        lowering_pick(arms, constructor) = select(arms, constructor)
}

trusted lowering_selection: "open: the lowered guard chain, whose last arm is the fallback, is not yet related to select on admitted matches; lowering shares no extracted selection function with the evaluator"
```
