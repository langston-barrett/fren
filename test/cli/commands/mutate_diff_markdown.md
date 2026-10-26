# A Markdown spec

Prose before the code, which the patch's line numbers count.

```fren
mod m

pub comp c {
    in x: Int
    pub out y?

    ensure r: y? iff x > 1
}
```

More prose, between the blocks.

```fren
pub comp d {
    in x: Int
    pub out y?

    ensure r: y? iff x < 9
}
```
