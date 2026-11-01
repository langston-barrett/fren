# Blocks that look like Fren

Inline code at the start of a line, such as
```` ```fren ```` here, is not a fence, so the block after it is read. Its
expectation fails, but the error below stops the checks, in both front ends,
before the `#fren_check` runs.

```fren
pub proc read_after_inline(a?): (b?) {
    ensure same: b? iff a?

    expect wrong: b? iff not a?
}

#fren_check
```

A block whose info string is `fren,ignore` is prose, which is an error:

```fren,ignore
pub proc ignored(a?): (b?) {
    ensure same: b? iff a?
}
```
