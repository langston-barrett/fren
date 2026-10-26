# A chapter that reads another

Its item is declared before the chapter it reads, which checks it.

```fren
mod outer

pub comp outer_gate {
    in a?
    pub out b?

    ensure same: b? iff a?
    expect never: when a?, not b?
}

#fren_md "LiterateInner.md"
```
