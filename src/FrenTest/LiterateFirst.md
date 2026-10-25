# The first of two chapters

Its items are checked by the second chapter, whose text is different, so a
message about them must be placed by this chapter's text.

```fren
mod chapters

pub comp gate {
    in a?
    pub out b?

    req same: b? iff a?
    expect never: when a?, not b?
}

expect arithmetic: 1 + 1 = 3

set_option fren.evidence "tested" in
pub comp by_testing {
    in a?
    pub out b?

    req same: b? iff a?
}
```
