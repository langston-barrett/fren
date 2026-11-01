# A block that is never closed

The block below is still open at the end of the file, so it extends to the
end.

```fren
pub proc unclosed(a?): (b?) {
    ensure same: b? iff a?
}
