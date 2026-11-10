# Match compilation

This chapter covers compilation of pattern matches.

## Arm selection

Lowering builds a chain of guards over the arms in written order and takes the
last arm as the fallback, so that it needs no guard of its own. The match then
runs the arm that [`select`](../Language/Patterns.md#r-patterns.matching.select)
names for every constructor of an admitted match.

r[match.lowering.selection] spec::lowering::lowering_selection::agrees
The arm that the lowered guard chain runs for a constructor is the arm
`select` names for it.

```fren
pub mod spec::lowering

use spec::names::{ArmF, ItemId}
use spec::surface::Snoc
use spec::types::Typing
use spec::patterns::select

pub fn lowering_pick(Snoc<ArmF<Typing>>, ItemId): Option<ArmF<Typing>>

set_option fren.evidence "random" in
pub proc lowering_selection(arms: Snoc<ArmF<Typing>>, constructor: ItemId): (holds?) {
    ensure output: holds?
    ensure agrees: lowering_pick(arms, constructor) = select(arms, constructor)
}

trusted lowering_selection: "open: the lowered guard chain, whose last arm is the fallback, is not yet related to select; lowering shares no extracted selection function with the evaluator"
```
