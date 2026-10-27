# A Markdown spec

Prose before the code, which the patch's line numbers count.

```fren
mod m

pub proc c(x: Int): (y?) {
    ensure r: y? iff x > 1
}
```

More prose, between the blocks.

```fren
pub proc d(x: Int): (y?) {
    ensure r: y? iff x < 9
}
```
