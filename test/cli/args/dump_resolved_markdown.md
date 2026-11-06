# A literate surface

Prose is blanked before offsets are measured.

```fren
-- λ
pub fn identity(x: Int): Int := x
```

Prose between blocks is blanked too.

```fren
pub proc caller(x: Int): (det y: Int) { out y := identity(x) }
```
