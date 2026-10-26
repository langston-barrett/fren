# A Markdown spec

Prose is ignored, and so are other code blocks:

```lean
def notFren := 1
```

```fren
mod lit

pub comp gate {
    in a?
    pub out b?

    ensure same: b? iff a?
```

Blocks are concatenated, so an item can span them.

```fren
    expect never: when a?, not b?
}

#fren_check
```
