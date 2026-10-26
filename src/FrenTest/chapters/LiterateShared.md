# A chapter reached through `..`

```fren
pub comp shared_gate {
    in a?
    pub out b?

    ensure same: b? iff a?
    expect never: when a?, not b?
}
```
