# A Markdown spec

Prose is ignored, and so are other code blocks:

```lean
def notFren := 1
```

```fren
mod lit

pub proc gate(a?): (b?) {
    ensure same: b? iff a?

    expect never: when a?, not b?
}

#fren_check
```
