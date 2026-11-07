# A checked example

This small example shows how a rule can state a property precisely in Fren.
The accompanying Lean wrapper binds a Lean function to the procedure and
proves that it meets the rule.

**Dynamic semantics**

r[spec-language-example.double] spec::language_example::double
Doubling an integer gives its sum with itself.

```fren
pub mod spec
pub mod spec::language_example

pub proc double(n: Int): (result: Int) {
    ensure sum: result = n + n
}
```
