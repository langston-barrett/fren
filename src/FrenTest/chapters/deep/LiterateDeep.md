# A nested chapter in a subdirectory of its reader

It declares an item, reads a chapter through `..`, and then checks its own
item, that chapter's, and an imported one.

```fren
pub comp deep_gate {
    in a?
    pub out b?

    ensure same: b? iff a?
    expect never: when a?, not b?
}

#fren_md "../LiterateShared.md"

#fren_check deep_gate
#fren_check shared_gate
#fren_check dep::dep_gate
```
