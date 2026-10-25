# The first of two chapters

Its item is checked by the second chapter, whose text is different, so a
message about it must be placed by this chapter's text.

```fren
mod chapters

pub comp gate {
    in a?
    pub out b?

    req same: b? iff a?
    expect never: when a?, not b?
}
```
