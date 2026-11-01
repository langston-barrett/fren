# Blocks that look like Fren

Inline code at the start of a line, such as
```` ```fren ```` here, is not a fence, so the block after it is read.

```fren
pub proc read_after_inline(a?): (b?) {
    ensure same: b? iff a?
}
```

A block whose info string is `fren,ignore` is prose, which is an error:

```fren,ignore
pub proc ignored(a?): (b?) {
    ensure same: b? iff a?
}
```
