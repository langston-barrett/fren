# A chapter that another chapter reads

It declares an item of its own, and checks it, the outer chapter's item and
the Lean file's.

```fren
pub proc inner_gate(a?): (b?) {
    ensure same: b? iff a?
    expect never: when a?, not b?
}

#fren_check
```
