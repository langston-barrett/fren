# Record updates

## Needless updates

`needless_update` fires on a [record update](../../Lang/Expressions.md#record-updates)
`{ r with ... }` that gives every field of `r`'s record: it reads nothing
from `r`, so it has the value of the record literal of the same fields.
This is Clippy's `needless_update`, which is in its `complexity` group.
There is no fix, as in Clippy. The literal names the record, which the
fix would have to write by a path that resolves where the update is, and
it would no longer mention `r`, which the update does (see
[Mentions](../../Lang/Expressions.md#mentions)), nor have the indexes
within `r` checked for [definedness](../../Check.md#definedness). The
message suggests the literal, or leaving out the fields that should keep
`r`'s values. `lint::needless_update` states when it fires:

```fren
pub mod lint

pub comp needless_update {
    in n_fields: Nat   -- the fields of `r`'s record
    in n_given: Nat    -- the fields the update gives, each at most once

    assume within: n_given <= n_fields
    pub det out fires?

    ensure rule: fires? iff n_given = n_fields
}
```

What the message says, that the update is the literal of the same
fields, is checked by refinement, each way:

```fren
set_option fren.lint.needless_update "allow" in
pub comp needless_update_written {
    in t: Triple
    in n: Int
    pub det out u: Triple := { t with a := n, b := 1, c := n + 1 }
}

set_option fren.lint.unused_variables "allow" in
pub comp needless_update_fixed {
    in t: Triple
    in n: Int
    pub det out u: Triple := Triple { a := n, b := 1, c := n + 1 }
}

refine needless_update_sound: needless_update_fixed refines needless_update_written
refine needless_update_complete: needless_update_written refines needless_update_fixed
```
