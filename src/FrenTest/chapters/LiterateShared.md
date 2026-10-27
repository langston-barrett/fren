# A chapter reached through `..`

```fren
pub proc shared_gate(a?): (b?) {
    ensure same: b? iff a?
    expect never: when a?, not b?
}
```
