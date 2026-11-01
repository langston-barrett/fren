# A spec outside the decidable core

Counting with a relational operator, where `undecidable` is denied, as by
default: cvc5 may abort on it, so it must never reach the solver.

```fren
mod undecidable_md

proc mixed(r: Rel<Int, Int>): (y?) { ensure q: y? iff r.range.card = 1 }
```
