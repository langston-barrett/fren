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

set_option fren.lint.assertions_on_constants "allow" in
expect arithmetic: 1 + 1 = 3

set_option fren.evidence "tested" in
pub comp by_testing {
    in a?
    pub out b?

    req same: b? iff a?
}
```

A refinement that fails, which the second chapter checks too:

```fren
pub comp precise {
    in x: Int
    pub out y: Int

    req r: y = x + 1
}

pub comp lower {
    in x: Int
    pub out y: Int

    req below: y < x
}

refine fails: precise refines lower
```
