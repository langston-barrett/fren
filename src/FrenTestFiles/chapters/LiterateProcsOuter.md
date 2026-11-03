# A chapter whose procedure only a later item calls

```fren
proc md_claim(x: Int) { expect e: x + 1 > x }
```

It reads another chapter before the call:

```fren
#fren_md "LiterateProcsInner.md"

pub proc md_caller(x: Int): (y: Int) {
    call c := md_claim(x)
    out y := x
}
```
