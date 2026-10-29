# The first of two chapters

Its items are checked by the second chapter, whose text is different, so a
message about them must be placed by this chapter's text.

```fren
mod chapters

pub proc gate(a?): (b?) {
    ensure same: b? iff a?
    expect never: when a?, not b?
}

set_option fren.lint.assertions_on_constants "allow" in
expect arithmetic: 1 + 1 = 3

set_option fren.evidence "tested" in
pub proc by_testing(a?): (b?) {
    ensure same: b? iff a?
}
```

A refinement that fails, which the second chapter checks too:

```fren
pub proc precise(x: Int): (y: Int) {
    ensure r: y = x + 1
}

pub proc lower(x: Int): (y: Int) {
    ensure below: x != 0 or y < x
}

expect fails(x: Int) {
    call concrete := precise(x)
    refines concrete lower(x)
}
```
